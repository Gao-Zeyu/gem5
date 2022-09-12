#include "cpu/pred/decoupled_bpred.hh"

#include "base/output.hh"
#include "base/debug_helper.hh"
#include "cpu/pred/stream_common.hh"
#include "debug/DecoupleBPVerbose.hh"
#include "sim/core.hh"

namespace gem5
{
namespace branch_prediction
{

DecoupledBPU::DecoupledBPU(const DecoupledBPUParams &p)
    : BPredUnit(p), fetchTargetQueue(p.ftq_size), historyBits(p.maxHistLen), streamTAGE(p.stream_tage)
{
    assert(streamTAGE);

    // TODO: remove this
    fetchStreamQueueSize = 64;
    s0PC = 0x80000000;
    s0StreamStartPC = s0PC;

    s0History.resize(historyBits, 0);
    fetchTargetQueue.setName(name());

    commitHistory.resize(historyBits, 0);
    squashing = true;

    registerExitCallback([this]() {
        auto out_handle = simout.create("topMisPredicts.txt", false, true);
        *out_handle->stream() << "streamStart" << " " << "control pc" << " " << "count" << std::endl;
        std::vector<std::pair<Addr, MispredictEntry>> topMisPredPC;
        for (auto &it : topMispredicts) {
            topMisPredPC.push_back(it);
        }
        std::sort(topMisPredPC.begin(), topMisPredPC.end(), [](const std::pair<Addr, MispredictEntry> &a, const std::pair<Addr, MispredictEntry> &b) {
            return a.second.count > b.second.count;
        });
        for (auto& it : topMisPredPC) {
            *out_handle->stream() << std::hex << it.second.streamStart << " " << it.second.controlAddr << " " << std::dec << it.second.count << std::endl;
        }
        simout.close(out_handle);
    });
}

void
DecoupledBPU::useStreamRAS()
{
    if (s0UbtbPred.endIsCall) {
        DPRINTF(DecoupleBPRAS,
                "%lu, push stream RAS for call, addr: %lx, size: %d\n", fsqId,
                s0UbtbPred.controlAddr + s0UbtbPred.controlSize,
                streamRAS.size());
        streamRAS.push(s0UbtbPred.controlAddr + s0UbtbPred.controlSize);
        dumpRAS();
    } else if (s0UbtbPred.endIsRet && !streamRAS.empty()) {
        DPRINTF(DecoupleBPRAS,
                "%lu, pop stream RAS for ret, nextStream: %lx, control addr: "
                "%#lx, control size: %#lx, RAS size: %d\n",
                fsqId, streamRAS.top(), s0UbtbPred.controlAddr,
                s0UbtbPred.controlSize, streamRAS.size());
        s0UbtbPred.nextStream = streamRAS.top();
        streamRAS.pop();
        dumpRAS();
    }
}

void
DecoupledBPU::tick()
{
    if (!squashing) {
        DPRINTF(DecoupleBP, "DecoupledBPU::tick()\n");
        s0UbtbPred = streamTAGE->getStream();
        tryEnqFetchTarget();
        tryEnqFetchStream();

    } else {
        DPRINTF(DecoupleBP, "Squashing, skip this cycle\n");
    }
    lastCyclePredicted = false;

    streamTAGE->tickStart();
    if (!streamQueueFull()) {
        if (s0StreamStartPC == ObservingPC) {
            DPRINTFV(true, "Predicting stream %#lx, id: %lu\n", s0StreamStartPC, fsqId);
        }
        streamTAGE->putPCHistory(s0PC, s0StreamStartPC, s0History);
        lastCyclePredicted = true;
    }
    
    squashing = false;
}

bool
DecoupledBPU::trySupplyFetchWithTarget()
{
    return fetchTargetQueue.trySupplyFetchWithTarget();
}


std::pair<bool, bool>
DecoupledBPU::decoupledPredict(const StaticInstPtr &inst,
                               const InstSeqNum &seqNum, PCStateBase &pc,
                               ThreadID tid)
{
    std::unique_ptr<PCStateBase> target(pc.clone());

    DPRINTF(DecoupleBP, "looking up pc %#lx\n", pc.instAddr());
    auto target_avail = fetchTargetQueue.fetchTargetAvailable();

    DPRINTF(DecoupleBP, "Supplying fetch with target ID %lu\n",
            fetchTargetQueue.getSupplyingTargetId());

    if (!target_avail) {
        DPRINTF(DecoupleBP,
                "No ftq entry to fetch, return dummy prediction\n");
        // todo pass these with reference
        // TODO: do we need to update PC if not taken?
        return std::make_pair(false, true);
    }

    const auto &target_to_fetch = fetchTargetQueue.getTarget();
    // found corresponding entry
    auto start = target_to_fetch.startPC;
    auto end = target_to_fetch.endPC;
    auto taken_pc = target_to_fetch.takenPC;
    DPRINTF(DecoupleBP, "Responsing fetch with");
    printFetchTarget(target_to_fetch, "");

    // supplying ftq entry might be taken before pc
    // because it might just be updated last cycle
    // but last cycle ftq tells fetch that this is a miss stream
    assert(pc.instAddr() < end && pc.instAddr() >= start);
    bool taken = pc.instAddr() == taken_pc && target_to_fetch.taken;

    bool run_out_of_this_entry = false;

    if (taken) {
        auto &rtarget = target->as<GenericISA::PCStateWithNext>();
        rtarget.pc(target_to_fetch.target);
        // TODO: how about compressed?
        rtarget.npc(target_to_fetch.target + 4);
        rtarget.uReset();
        DPRINTF(DecoupleBP,
                "Predicted pc: %#lx, upc: %#lx, npc(meaningless): %#lx\n",
                target->instAddr(), rtarget.upc(), rtarget.npc());
        set(pc, *target);
        run_out_of_this_entry = true;
    } else {
        inst->advancePC(*target);
        if (target->instAddr() >= end) {
            run_out_of_this_entry = true;
        }
    }
    DPRINTF(DecoupleBP, "Predict it %staken to %#lx\n", taken ? "" : "not ",
            target->instAddr());

    if (run_out_of_this_entry) {
        // dequeue the entry
        DPRINTF(DecoupleBP, "running out of ftq entry %lu\n",
                fetchTargetQueue.getSupplyingTargetId());
        fetchTargetQueue.finishCurrentFetchTarget();
    }

    return std::make_pair(taken, run_out_of_this_entry);
}

void
DecoupledBPU::controlSquash(unsigned target_id, unsigned stream_id,
                            const PCStateBase &control_pc,
                            const PCStateBase &corr_target,
                            const StaticInstPtr &static_inst,
                            unsigned control_inst_size, bool actually_taken,
                            const InstSeqNum &seq, ThreadID tid)
{
    bool is_conditional = static_inst->isCondCtrl();
    bool is_indirect = static_inst->isIndirectCtrl();
    bool is_call = static_inst->isCall() && !static_inst->isNonSpeculative();
    bool is_return = static_inst->isReturn() && !static_inst->isNonSpeculative();
    EndType end_type = END_TYPE_NONE;

    if (is_conditional) {
        ++stats.condIncorrect;
    }
    if (is_indirect) {
        ++stats.indirectMispredicted;
    }
    if (is_return) {
        ++stats.RASIncorrect;
        end_type = END_TYPE_RET;
    }
    if (is_call) {
        end_type = END_TYPE_CALL;
    }

    squashing = true;

    s0PC = corr_target.instAddr();
    s0StreamStartPC = s0PC;

    DPRINTF(DecoupleBP || debugFlagOn,
            "Control squash: ftq_id=%lu, fsq_id=%lu,"
            " control_pc=%#lx, corr_target=%#lx, is_conditional=%u, "
            "is_indirect=%u, actually_taken=%u, branch seq: %lu\n",
            target_id, stream_id, control_pc.instAddr(),
            corr_target.instAddr(), is_conditional, is_indirect,
            actually_taken, seq);

    dumpFsq("Before control squash");
    // check sanity
    auto squashing_stream_it = fetchStreamQueue.find(stream_id);
    assert(squashing_stream_it != fetchStreamQueue.end());
    auto &stream = squashing_stream_it->second;

    DPRINTF(DecoupleBP || debugFlagOn, "stream start=%#lx\n", stream.streamStart);


    auto pc = stream.streamStart;
    if (pc == ObservingPC) {
        debugFlagOn = true;
    }

    FetchTargetId ftq_demand_stream_id;

    // restore ras
    DPRINTFV(this->debugFlagOn || ::gem5::debug::DecoupleBPRAS,
             "dump ras before control squash\n");
    dumpRAS();
    for (auto iter = --(fetchStreamQueue.end());iter != squashing_stream_it;--iter) {
        auto restore = iter->second;
        if (restore.isCall) {
            DPRINTF(DecoupleBPRAS, "erase call in control squash, fsqid: %lu\n", iter->first);
            streamRAS.pop();
        } else if (restore.isReturn) {
            DPRINTF(DecoupleBPRAS, "restore return in control squash, fsqid: %lu\n", iter->first);
            streamRAS.push(restore.getTakenTarget());
        }
    }
    if (stream.isCall) {
        DPRINTF(DecoupleBPRAS, "erase call in control squash, fsqid: %lu\n", squashing_stream_it->first);
        streamRAS.pop();
    } else if (stream.isReturn) {
        DPRINTF(DecoupleBPRAS, "restore return in control squash, fsqid: %lu\n", squashing_stream_it->first);
        streamRAS.push(stream.getTakenTarget());
    }
    stream.resolved = true;
    stream.exeEnded = true;
    stream.exeBranchPC = control_pc.instAddr();
    stream.exeTarget = corr_target.instAddr();
    stream.exeEndPC = stream.exeBranchPC + control_inst_size;

    if (actually_taken) {
        stream.exeTaken = true;
        // stream.exeBranchType = 0;
        stream.isCall = is_call;
        stream.isReturn = is_return;
        DPRINTF(DecoupleBP || debugFlagOn,
                "Mark stream %lu is call: %u, is return: %u\n", stream_id,
                is_call, is_return);

        if (stream.isCall) {
            DPRINTF(DecoupleBPRAS, "use ras for call in control squash, fsqid: %lu\n, push addr: %lx", squashing_stream_it->first, stream.exeEndPC);
            streamRAS.push(stream.exeEndPC);
        } else if (stream.isReturn & !streamRAS.empty()) {
            DPRINTF(DecoupleBPRAS, "use ras for return in control squash, fsqid: %lu\n", squashing_stream_it->first);
            streamRAS.pop();
        }

        streamTAGE->update(
            computeLastChunkStart(control_pc.instAddr(), stream.streamStart),
            stream.streamStart, control_pc.instAddr(), corr_target.instAddr(),
            control_inst_size, actually_taken, stream.history, end_type);

        // clear younger fsq entries
        auto erase_it = fetchStreamQueue.upper_bound(stream_id);
        while (erase_it != fetchStreamQueue.end()) {
            DPRINTF(DecoupleBP, "erasing entry %lu\n", erase_it->first);
            printStream(erase_it->second);
            fetchStreamQueue.erase(erase_it++);
        }

        boost::to_string(s0History, buf1);
        boost::to_string(stream.history, buf2);
        DPRINTFV(this->debugFlagOn || ::gem5::debug::DecoupleBP,
                 "Recover history %s\nto %s\n", buf1.c_str(), buf2.c_str());
        s0History = stream.history;
        auto hashed_path =
            computePathHash(control_pc.instAddr(), corr_target.instAddr());
        histShiftIn(hashed_path, s0History);
        boost::to_string(s0History, buf1);
        DPRINTFV(this->debugFlagOn || ::gem5::debug::DecoupleBP,
                 "Shift in history %s\n", buf1.c_str());

        DPRINTFV(
            this->debugFlagOn || ::gem5::debug::DecoupleBP,
            "a %s flow was redirected by taken branch, "
            "predicted: %#lx->%#lx, correct: %#lx->%#lx, new fsq entry is:\n",
            stream.predEnded ? "pred-longer" : "miss", stream.predBranchPC,
            stream.predTarget, control_pc.instAddr(), corr_target.instAddr());
        
        printStream(stream);

    } else {

        streamTAGE->update(
            computeLastChunkStart(control_pc.instAddr(), stream.streamStart),
            stream.streamStart, control_pc.instAddr(), corr_target.instAddr(),
            control_inst_size, actually_taken, stream.history, end_type);

        // clear younger fsq entries
        auto erase_it = fetchStreamQueue.upper_bound(stream_id);
        while (erase_it != fetchStreamQueue.end()) {
            DPRINTF(DecoupleBP, "erasing entry %lu\n", erase_it->first);
            printStream(erase_it->second);
            fetchStreamQueue.erase(erase_it++);
        }

        boost::to_string(s0History, buf1);
        boost::to_string(stream.history, buf2);
        DPRINTFV(this->debugFlagOn || ::gem5::debug::DecoupleBP,
                 "Recover history %s\nto %s\n", buf1.c_str(), buf2.c_str());
        s0History = stream.history;

        DPRINTFV(
            this->debugFlagOn || ::gem5::debug::DecoupleBP,
            "a taken flow was redirected by NOT taken branch,"
            "predicted: %#lx->%#lx, correct: %#lx->%#lx, new fsq entry is:\n",
            stream.predBranchPC, stream.predTarget, control_pc.instAddr(),
            corr_target.instAddr());
        printStream(stream);
    }

    if (stream.getEnded()) {
        // inc stream id because current stream ends
        ftq_demand_stream_id = stream_id + 1;
        fsqId = stream_id + 1;
    } else {
        // keep stream id because still in the same stream
        ftq_demand_stream_id = stream_id;
        fsqId = stream_id;
    }

    dumpFsq("After control squash");

    DPRINTF(DecoupleBPRAS, "dump ras after control squash\n");
    dumpRAS();

    s0UbtbPred.valid = false;

    fetchTargetQueue.squash(target_id + 1, ftq_demand_stream_id,
                            corr_target.instAddr());

    fetchTargetQueue.dump("After control squash");

    DPRINTFV(this->debugFlagOn || ::gem5::debug::DecoupleBP,
            "After squash, FSQ head Id=%lu, demand stream Id=%lu, Fetch "
            "demanded target Id=%lu\n",
            fsqId, fetchTargetQueue.getEnqState().streamId,
            fetchTargetQueue.getSupplyingTargetId());

    historyManager.squash(stream_id, actually_taken, control_pc.instAddr(),
                          corr_target.instAddr());
    checkHistory(s0History);
    debugFlagOn = false;
}

void
DecoupledBPU::nonControlSquash(unsigned target_id, unsigned stream_id,
                               const PCStateBase &inst_pc,
                               const InstSeqNum seq, ThreadID tid)
{
    DPRINTFV(this->debugFlagOn || ::gem5::debug::DecoupleBP,
            "non control squash: target id: %lu, stream id: %lu, inst_pc: %x, "
            "seq: %lu\n",
            target_id, stream_id, inst_pc.instAddr(), seq);
    squashing = true;

    dumpFsq("before non-control squash");

    // make sure the stream is in FSQ
    auto it = fetchStreamQueue.find(stream_id);
    assert(it != fetchStreamQueue.end());

    auto start = it->second.streamStart;
    auto end_pc = it->second.getEndPC();
    auto next_stream_start = it->second.getNextStreamStart();

    auto ftq_demand_stream_id = stream_id;

    DPRINTFV(this->debugFlagOn || ::gem5::debug::DecoupleBP,
             "non control squash: start: %x, end: %x, target: %x\n", start,
             end_pc, next_stream_start);

    if (end_pc) {
        if (start <= inst_pc.instAddr() && inst_pc.instAddr() < end_pc) {
            // this pc is in the stream
        } else if (inst_pc.instAddr() == next_stream_start) {
            // this pc is in the next stream!
            DPRINTF(DecoupleBP,
                    "Redirected PC is the target of the stream, "
                    "indicating that the stream is ended, switch to next "
                    "stream\n");
            ++it;
            ftq_demand_stream_id = stream_id + 1;
        } else {
            ++it;
            // find the containing stream
            DPRINTF(DecoupleBP,
                    "Redirected PC is not following stream, find it\n");
            while (it != fetchStreamQueue.end()) {
                if (it->second.streamStart <= inst_pc.instAddr() &&
                    inst_pc.instAddr() < it->second.getEndPC()) {
                    DPRINTF(DecoupleBP, "Found it in stream %lu\n", it->first);
                    ftq_demand_stream_id = it->first;
                    break;
                }
                ++it;
            }
            assert(it != fetchStreamQueue.end());
        }
    }


    auto &stream = it->second;
    // Fetching from the original predicted fsq entry, since this is not a
    // mispredict. We allocate a new target id to avoid alias
    auto pc = inst_pc.instAddr();
    fetchTargetQueue.squash(target_id + 1, ftq_demand_stream_id, pc);

    // we should set s0PC to be the predTarget of the fsq entry
    // in case that the stream is the newest entry in fsq,
    // That's because, if an inst of this stream had been squashed due to a
    // mispredict, and then a non-control squash was made on an inst oldder
    // than this inst, the s0PC would be set incorrectly by the previous
    // squash

    next_stream_start = stream.getNextStreamStart();
    // stream ptr might have been updated, so we need to update next stream start

    if (++it == fetchStreamQueue.end() && stream.getEnded()) {
        s0PC = next_stream_start;
        s0StreamStartPC = s0PC;
        fsqId = (--it)->first + 1;
    }

    if (pc == ObservingPC) dumpFsq("after non-control squash");
    DPRINTFV(this->debugFlagOn || ::gem5::debug::DecoupleBP,
            "After squash, FSQ head Id=%lu, s0pc=%#lx, demand stream Id=%lu, "
            "Fetch demanded target Id=%lu\n",
            fsqId, s0PC, fetchTargetQueue.getEnqState().streamId,
            fetchTargetQueue.getSupplyingTargetId());
}

void
DecoupledBPU::trapSquash(unsigned target_id, unsigned stream_id,
                         Addr last_committed_pc, const PCStateBase &inst_pc,
                         ThreadID tid)
{
    DPRINTF(DecoupleBP || debugFlagOn,
            "Trap squash: target id: %lu, stream id: %lu, inst_pc: %#lx\n",
            target_id, stream_id, inst_pc.instAddr());
    squashing = true;

    auto pc = inst_pc.instAddr();

    if (pc == ObservingPC) dumpFsq("before trap squash");

    auto it = fetchStreamQueue.find(stream_id);
    assert(it != fetchStreamQueue.end());
    auto &stream = it->second;

    // restore ras
    DPRINTF(DecoupleBPRAS, "dump ras before trap squash\n");
    dumpRAS();
    for (auto iter = --(fetchStreamQueue.end());iter != it;--iter) {
        auto restore = iter->second;
        if (restore.isCall) {
            DPRINTF(DecoupleBPRAS, "erase call in trap squash, fsqid: %lu\n", iter->first);
            streamRAS.pop();
        } else if (restore.isReturn) {
            DPRINTF(DecoupleBPRAS, "erase return in trap squash, fsqid: %lu\n", iter->first);
            streamRAS.push(restore.predTarget);
        }
    }
    if (stream.isCall) {
        DPRINTF(DecoupleBPRAS, "erase call in trap squash, fsqid: %lu\n", it->first);
        streamRAS.pop();
    } else if (stream.isReturn) {
        DPRINTF(DecoupleBPRAS, "erase return in trap squash, fsqid: %lu\n", it->first);
        streamRAS.push(stream.predTarget);
    }

    stream.exeEnded = true;
    stream.exeBranchPC = last_committed_pc;
    // stream.exeBranchType = 1;
    stream.exeTarget = inst_pc.instAddr();
    stream.exeEndPC = stream.exeBranchPC + 4;


    // For trap squash, we expect them to always incorrectly predict
    // Because correct prediction will cause strange behaviors
    streamTAGE->update(
        computeLastChunkStart(stream.getControlPC(), stream.streamStart),
        stream.streamStart, stream.getControlPC(), stream.getFallThruPC(), 4, false,
        stream.history, END_TYPE_NONE);

    historyManager.squash(stream_id, true, last_committed_pc, inst_pc.instAddr());

    boost::to_string(s0History, buf1);
    boost::to_string(stream.history, buf2);
    DPRINTF(DecoupleBP, "Recover history %s\nto %s\n", buf1.c_str(),
            buf2.c_str());
    s0History = stream.history;
    auto hashed_path =
        computePathHash(last_committed_pc, inst_pc.instAddr());
    histShiftIn(hashed_path, s0History);
    boost::to_string(s0History, buf1);
    DPRINTF(DecoupleBP, "Shift in history %s\n", buf1.c_str());

    checkHistory(s0History);

    auto erase_it = fetchStreamQueue.upper_bound(stream_id);
    while (erase_it != fetchStreamQueue.end()) {
        DPRINTF(DecoupleBP, "erasing entry %lu\n", erase_it->first);
        printStream(erase_it->second);
        fetchStreamQueue.erase(erase_it++);
    }

    // inc stream id because current stream is disturbed
    auto ftq_demand_stream_id = stream_id + 1;
    // todo update stream head id here
    fsqId = stream_id + 1;

    fetchTargetQueue.squash(target_id + 1, ftq_demand_stream_id,
                            inst_pc.instAddr());

    s0PC = inst_pc.instAddr();
    s0StreamStartPC = s0PC;

    DPRINTF(DecoupleBP,
            "After trap squash, FSQ head Id=%lu, s0pc=%#lx, demand stream "
            "Id=%lu, Fetch demanded target Id=%lu\n",
            fsqId, s0PC, fetchTargetQueue.getEnqState().streamId,
            fetchTargetQueue.getSupplyingTargetId());

    // restore ras
    DPRINTF(DecoupleBPRAS, "dump ras after trap squash\n");
    dumpRAS();
}

void DecoupledBPU::update(unsigned stream_id, ThreadID tid)
{
    // aka, commit stream
    // commit controls in local prediction history buffer to committedSeq
    // mark all committed control instructions as correct
    // do not need to dequeue when empty
    if (fetchStreamQueue.empty())
        return;
    auto it = fetchStreamQueue.begin();
    while (it != fetchStreamQueue.end() && stream_id >= it->first) {

        // dequeue
        DPRINTF(DecoupleBP, "dequeueing stream id: %lu, entry below:\n",
                it->first);
        bool miss_predicted =
            it->second.predBranchPC != it->second.exeBranchPC ||
            it->second.predTarget != it->second.exeTarget;
        DPRINTF(DecoupleBP,
                "Commit stream start %#lx, which is %s predicted, "
                "final br addr: %#lx, final target: %#lx, pred br addr: %#lx, "
                "pred target: %#lx\n",
                it->second.streamStart, miss_predicted ? "miss" : "correctly",
                it->second.exeBranchPC, it->second.exeTarget,
                it->second.predBranchPC, it->second.predTarget);

        if (!miss_predicted) {
            // TODO: do ubtb update here
            streamTAGE->commit(
                it->second.streamStart, it->second.exeBranchPC,
                it->second.exeTarget,
                it->second.history);
        } else {
            MispredictEntry entry(it->second.streamStart,
                                  it->second.exeBranchPC);

            auto find_it = topMispredicts.find(it->second.streamStart);
            if (find_it == topMispredicts.end()) {
                topMispredicts[it->second.streamStart] = entry;
            } else {
                find_it->second.count++;
            }
        }

        it = fetchStreamQueue.erase(it);
    }
    DPRINTF(DecoupleBP, "after commit stream, fetchStreamQueue size: %lu\n",
            fetchStreamQueue.size());
    printStream(it->second);

    historyManager.commit(stream_id);
}

void
DecoupledBPU::dumpFsq(const char *when)
{
    DPRINTF(DecoupleBPProbe, "dumping fsq entries %s...\n", when);
    for (auto it = fetchStreamQueue.begin(); it != fetchStreamQueue.end();
         it++) {
        DPRINTFR(DecoupleBPProbe, "StreamID %lu, ", it->first);
        printStream(it->second);
    }
}

void
DecoupledBPU::tryEnqFetchStream()
{
    if (s0StreamStartPC == ObservingPC) {
        debugFlagOn = true;
    }
    if (!lastCyclePredicted) {
        DPRINTF(DecoupleBP, "last cycle not predicted, cannot enq fsq");
        debugFlagOn = false;
        return;
    }
    if (!streamQueueFull()) {
        bool should_create_new_stream = false;
        if (!fetchStreamQueue.empty()) {
            // check last entry state
            auto &back = fetchStreamQueue.rbegin()->second;
            if (back.getEnded()) {
                should_create_new_stream = true;
                DPRINTF(DecoupleBP || debugFlagOn,
                        "FSQ: the latest stream has ended\n");
            }
        }
        if (fetchStreamQueue.empty()) {
            should_create_new_stream = true;
            DPRINTF(DecoupleBP || debugFlagOn,
                    "FSQ: is empty\n");
        }

        if (!should_create_new_stream) {
            DPRINTF(DecoupleBP || debugFlagOn,
                    "FSQ is not empty and the latest stream hasn't ended\n");
        }
        makeNewPrediction(should_create_new_stream);

        const auto &back = fetchStreamQueue.rbegin()->second;
        if (!back.getEnded()) {
            // streamMiss = true;
            DPRINTF(DecoupleBP || debugFlagOn, "s0PC update to %#lx\n", s0PC);
        } else {
            DPRINTF(DecoupleBP || debugFlagOn,
                    "stream %lu has ended, s0PC update to %#lx\n",
                    fetchStreamQueue.rend()->first, s0PC);
        }

    } else {
        DPRINTF(DecoupleBP || debugFlagOn, "FSQ is full: %lu\n",
                fetchStreamQueue.size());
    }
    DPRINTF(DecoupleBP || debugFlagOn, "fsqId=%lu\n", fsqId);
    debugFlagOn = false;
}

void
DecoupledBPU::setTakenEntryWithStream(const FetchStream &stream_entry, FtqEntry &ftq_entry)
{
    ftq_entry.taken = true;
    ftq_entry.takenPC = stream_entry.getControlPC();
    ftq_entry.endPC = stream_entry.getEndPC();
    ftq_entry.target = stream_entry.getTakenTarget();
}

void
DecoupledBPU::setNTEntryWithStream(FtqEntry &ftq_entry, Addr end_pc)
{
    ftq_entry.taken = false;
    ftq_entry.takenPC = 0;
    ftq_entry.target = 0;
    ftq_entry.endPC = end_pc;
}

void
DecoupledBPU::tryEnqFetchTarget()
{
    DPRINTF(DecoupleBP, "Try to enq fetch target\n");
    if (fetchTargetQueue.full()) {
        DPRINTF(DecoupleBP, "FTQ is full\n");
        return;
    }
    if (fetchStreamQueue.empty()) {
        // no stream that have not entered ftq
        DPRINTF(DecoupleBP, "No stream to enter ftq in fetchStreamQueue\n");
        return;
    }
    // ftq can accept new cache lines,
    // try to get cache lines from fetchStreamQueue
    // find current stream with ftqEnqfsqID in fetchStreamQueue
    auto &ftq_enq_state = fetchTargetQueue.getEnqState();
    auto it = fetchStreamQueue.find(ftq_enq_state.streamId);
    if (it == fetchStreamQueue.end()) {
        // desired stream not found in fsq
        DPRINTF(DecoupleBP, "FTQ enq desired Stream ID %u is not found\n",
                ftq_enq_state.streamId);
        return;
    }

    auto &stream_to_enq = it->second;
    Addr end = stream_to_enq.getEndPC();
    DPRINTF(DecoupleBP, "Serve enq PC: %#lx with stream %lu:\n",
            ftq_enq_state.pc, it->first);
    printStream(stream_to_enq);

    // We does let ftq to goes beyond fsq now
    assert(ftq_enq_state.pc <= end);

    // deal with an incompleted target entry
    if (fetchTargetQueue.lastEntryIncomplete()) {
        DPRINTF(DecoupleBP || debugFlagOn,
                "Try filling up incompleted ftq entry\n");
        fetchTargetQueue.dump("Before update last entry");
        auto &last = fetchTargetQueue.getLastInsertedEntry();
        bool used_up_stream = false;
        if (stream_to_enq.getTaken()) {
            DPRINTF(DecoupleBP || debugFlagOn,
                    "mark the last target as taken\n");
            setTakenEntryWithStream(stream_to_enq, last);
            ftq_enq_state.pc = last.target;
            used_up_stream = true;
        } else {
            // still a missing target, set endPC to the predicted end
            // decouplePredict is only allow to predicted untial this end
            Addr predicted_until = stream_to_enq.getEndPC();
            if (predicted_until > ftq_enq_state.pc) {
                last.endPC =
                    std::min(predicted_until,
                             alignToCacheLine(last.endPC + fetchTargetSize));
                ftq_enq_state.pc = last.endPC;
            } else {
                DPRINTF(
                    DecoupleBP || debugFlagOn,
                    "FSQ falls behind FTQ, cannot update last FTQ entry\n");
            }
            used_up_stream = stream_to_enq.getEnded() &&
                             ftq_enq_state.pc == stream_to_enq.getFallThruPC();
            DPRINTF(
                DecoupleBP || debugFlagOn,
                "the last target is still not taken, can predict to %#lx\n",
                ftq_enq_state.pc);
        }
        if (used_up_stream) {
            ftq_enq_state.streamId++;
        }
        DPRINTF(DecoupleBP || debugFlagOn,
                "After fill up last entry, Update ftqEnqPC to %#lx, "
                "FTQ demand stream ID to %lu\n",
                ftq_enq_state.pc, ftq_enq_state.streamId);
        printFetchTarget(last, "Updated in FTQ");
        fetchTargetQueue.dump("After update last entry");
        return;
    }
    // create a new target entry
    FtqEntry ftq_entry;
    ftq_entry.startPC = ftq_enq_state.pc;
    ftq_entry.fsqID = ftq_enq_state.streamId;

    Addr baddr = stream_to_enq.getControlPC();
    Addr line_end = alignToCacheLine(ftq_entry.startPC + fetchTargetSize);
    bool branch_in_line = baddr < line_end;
    bool end_in_line = end <= line_end;

    DPRINTF(DecoupleBP,
            "end in line: %d, branch in line: %d, stream ended: %d\n",
            end_in_line, branch_in_line, stream_to_enq.getEnded());

    bool used_up_stream = false;
    if (stream_to_enq.getTaken() && branch_in_line) {
        DPRINTF(DecoupleBP, "Enqueue FTQ with ended stream %lu\n",
                ftq_enq_state.streamId);
        printStream(stream_to_enq);

        setTakenEntryWithStream(stream_to_enq, ftq_entry);
        ftq_enq_state.pc = ftq_entry.target;
        used_up_stream = true;

    } else if (stream_to_enq.getEndPC() <= ftq_enq_state.pc) {
        DPRINTF(DecoupleBP || debugFlagOn,
                "FSQ falls behind FTQ, cannot update last FTQ entry\n");

        DPRINTF(DecoupleBP || debugFlagOn,
                "(Unchanged) Update ftqEnqPC = %#lx, FTQ demand stream ID = %lu\n",
                ftq_enq_state.pc, ftq_enq_state.streamId);
        return;
    } else {  // not taken:  A. missing or B. ended but not taken
        Addr predict_until;
        assert(!stream_to_enq.getEnded() ||
               (stream_to_enq.getEnded() && !stream_to_enq.getTaken())||
               (stream_to_enq.getTaken() && !branch_in_line));
        used_up_stream = stream_to_enq.getEnded() && end_in_line;
        if (end_in_line) {
            predict_until = end;
        } else {
            // Taken but br not in line
            // Or, miss and predicted_until goes beyond this cache line
            predict_until = line_end;
        }
        setNTEntryWithStream(ftq_entry, predict_until);
        ftq_enq_state.pc = predict_until;
        DPRINTF(DecoupleBP,
                "Enqueue FTQ with continuous stream %lu that can predicted "
                "until %#lx. Update ftqEnqPC to %#lx\n",
                ftq_enq_state.streamId, predict_until, ftq_enq_state.pc);
        printStream(stream_to_enq);
    }

    if (used_up_stream) {
        ftq_enq_state.streamId++;
    }
    DPRINTF(DecoupleBP,
            "Update ftqEnqPC to %#lx, FTQ demand stream ID to %lu\n",
            ftq_enq_state.pc, ftq_enq_state.streamId);

    fetchTargetQueue.enqueue(ftq_entry);

    assert(ftq_enq_state.streamId <= fsqId + 1);

    DPRINTF(DecoupleBP, "a%s stream, next enqueue target: %lu\n",
            stream_to_enq.getEnded() ? "n ended" : " miss", ftq_enq_state.nextEnqTargetId);
    printFetchTarget(ftq_entry, "Insert to FTQ");
    fetchTargetQueue.dump("After insert new entry");
}

Addr
DecoupledBPU::computePathHash(Addr br, Addr target)
{
    Addr ret = ((br >> 1) ^ (target >> 2)) & foldingTokenMask();
    return ret;
}

void
DecoupledBPU::histShiftIn(Addr hash, boost::dynamic_bitset<> &history)
{
    // boost::to_string(history, buf2);
    // DPRINTF(DecoupleBP, "Hist before shiftin: %s, hist len: %u, hash:
    // %#lx\n", buf.c_str(), history.size(), hash); DPRINTF(DecoupleBP, "Reach
    // x\n");
    history <<= 2;
    boost::dynamic_bitset<> temp_hash_bits(historyBits, hash);
    // boost::to_string(temp_hash_bits, buf2);
    // DPRINTF(DecoupleBP, "hash to shiftin: %s\n", buf.c_str());
    history ^= temp_hash_bits;
    // boost::to_string(history, buf2);
    // DPRINTF(DecoupleBP, "Hist after shiftin: %s\n", buf2.c_str());
}

void
DecoupledBPU::makeNewPrediction(bool create_new_stream)
{
    DPRINTF(DecoupleBP, "Try to make new prediction\n");
    FetchStream entry_new;
    // TODO: this may be wrong, need to check if we should use the last
    // s0PC
    auto back = fetchStreamQueue.rbegin();
    auto &entry = create_new_stream ? entry_new : back->second;
    entry.streamStart = s0StreamStartPC;
    if (s0StreamStartPC == ObservingPC) {
        debugFlagOn = true;
    }
    DPRINTF(DecoupleBP || debugFlagOn, "Make pred with %s, pred valid: %i, taken: %i\n",
             create_new_stream ? "new stream" : "last missing stream",
             s0UbtbPred.valid, !s0UbtbPred.endNotTaken);
    if (s0UbtbPred.valid && !s0UbtbPred.endNotTaken) {
        DPRINTF(DecoupleBP, "TAGE predicted target: %#lx\n", s0UbtbPred.nextStream);
        useStreamRAS();

        entry.predEnded = true;
        entry.predTaken = true;
        entry.predEndPC = s0UbtbPred.controlAddr + s0UbtbPred.controlSize;
        entry.predBranchPC = s0UbtbPred.controlAddr;
        entry.predTarget = s0UbtbPred.nextStream;
        entry.history = s0UbtbPred.history;
        entry.isCall = s0UbtbPred.endIsCall;
        entry.isReturn = s0UbtbPred.endIsRet;
        s0PC = s0UbtbPred.nextStream;
        s0StreamStartPC = s0PC;

        auto hashed_path =
            computePathHash(s0UbtbPred.controlAddr, s0UbtbPred.nextStream);
        boost::to_string(s0History, buf1);
        histShiftIn(hashed_path, s0History);
        boost::to_string(s0History, buf2);
        DPRINTF(DecoupleBP, "Update s0PC to %#lx\n", s0PC);
        DPRINTF(DecoupleBP, "Update s0History from %s to %s\n", buf1.c_str(),
                buf2.c_str());
        DPRINTF(DecoupleBP, "Hashed path: %#lx\n", hashed_path);

        if (create_new_stream) {
            historyManager.addSpeculativeHist(s0UbtbPred.controlAddr,
                                              s0UbtbPred.nextStream, fsqId, false);
        } else {
            historyManager.updateSpeculativeHist(s0UbtbPred.controlAddr,
                                                 s0UbtbPred.nextStream, fsqId);
        }

        DPRINTF(DecoupleBP,
                "Build stream %lu with Valid s0UbtbPred: %#lx-[%#lx, %#lx) "
                "--> %#lx, is call: %i, is return: %i\n",
                fsqId, entry.streamStart, entry.predBranchPC,
                entry.predEndPC, entry.predTarget, entry.isCall, entry.isReturn);
    } else {
        if (s0UbtbPred.valid && s0UbtbPred.endNotTaken) {
            // The prediction only tell us not taken until endPC
            // The generated stream cannot serve since endPC
            s0PC = s0UbtbPred.controlAddr + s0UbtbPred.controlSize;
            s0StreamStartPC = s0PC;
            entry.predEnded = true;
        } else {
            s0PC += streamChunkSize;
            entry.predEnded = false;
        }
        entry.predEndPC = s0PC;
        entry.history.resize(historyBits);
        DPRINTF(DecoupleBP, "entry hist size: %lu, ubtb hist size: %lu\n",
                entry.history.size(), s0UbtbPred.history.size());
        // when pred is invalid, history from s0UbtbPred is outdated
        // entry.history = s0History is right for back-to-back predictor
        // but not true for backing predictor taking multi-cycles to predict.
        entry.history = s0History; 

        if (create_new_stream) {
            // A missing history will not participate into history checking
            historyManager.addSpeculativeHist(0, 0, fsqId, true);
        }

        DPRINTF(DecoupleBP,
                "No valid prediction or pred fall thru, gen missing stream: %#lx -> ..."
                " is call: %i, is return: %i\n",
                s0PC, entry.isCall, entry.isReturn);
    }
    boost::to_string(entry.history, buf1);
    DPRINTF(DecoupleBP, "New prediction history: %s\n", buf1.c_str());

    if (create_new_stream) {
        entry.setDefaultResolve();
        auto [insert_it, inserted] = fetchStreamQueue.emplace(fsqId, entry);
        assert(inserted);

        dumpFsq("after insert new stream");
        DPRINTF(DecoupleBP, "Insert fetch stream %lu\n", fsqId);
    } else {
        DPRINTF(DecoupleBP, "Update fetch stream %lu\n", fsqId);
    }

    // only if the stream is predicted to be ended can we inc fsqID
    if (entry.getEnded()) {
        fsqId++;
        DPRINTF(DecoupleBP, "Inc fetch stream to %lu, because stream ends\n",
                fsqId);
    }
    printStream(entry);
    checkHistory(s0History);
    debugFlagOn = false;
}

void
DecoupledBPU::checkHistory(const boost::dynamic_bitset<> &history)
{
    unsigned ideal_size = 0;
    boost::dynamic_bitset<> ideal_hash_hist(historyBits, 0);
    for (const auto entry: historyManager.getSpeculativeHist()) {
        if (entry.miss) {
            continue;
        }
        ideal_size += 2;
        Addr signature = computePathHash(entry.pc, entry.target);
        DPRINTF(DecoupleBPVerbose, "%#lx->%#lx, signature: %#lx\n", entry.pc,
                entry.target, signature);
        ideal_hash_hist <<= 2;
        for (unsigned i = 0; i < historyTokenBits; i++) {
            ideal_hash_hist[i] ^= (signature >> i) & 1;
        }
    }
    unsigned comparable_size = std::min(ideal_size, historyBits);
    boost::dynamic_bitset<> sized_real_hist(history);
    ideal_hash_hist.resize(comparable_size);
    sized_real_hist.resize(comparable_size);

    boost::to_string(ideal_hash_hist, buf1);
    boost::to_string(sized_real_hist, buf2);
    DPRINTF(DecoupleBP,
            "Ideal size:\t%u, real history size:\t%u, comparable size:\t%u\n",
            ideal_size, historyBits, comparable_size);
    DPRINTF(DecoupleBP, "Ideal history:\t%s\nreal history:\t%s\n",
            buf1.c_str(), buf2.c_str());
    assert(ideal_hash_hist == sized_real_hist);
}

}  // namespace branch_prediction

}  // namespace gem5
