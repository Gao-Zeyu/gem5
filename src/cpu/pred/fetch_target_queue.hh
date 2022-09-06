#ifndef __CPU_PRED_FETCH_TARGET_QUEUE_HH__
#define __CPU_PRED_FETCH_TARGET_QUEUE_HH__

#include "cpu/pred/stream_struct.hh"
#include "sim/sim_object.hh"

namespace gem5
{

namespace branch_prediction
{

struct FetchTargetEnqState
{
    Addr pc;
    FetchStreamId streamId;
    FetchTargetId desireTargetId;
    FetchTargetEnqState() : pc(0), streamId(1), desireTargetId(0) {}
};

struct FetchTargetReadState
{
    bool valid;
    FetchTargetId targetId;
    FtqEntry entry;
};

class FetchTargetQueue
{
    // todo: move fetch target buffer here
    // 1. enqueue from fetch stream buffer
    // 2. supply fetch with fetch target head
    // 3. redirect fetch target head after squash
    using FTQ = std::map<FetchTargetId, FtqEntry>;
    using FTQIt = FTQ::iterator;
    FTQ ftq;
    unsigned ftqSize;
    FetchTargetId ftqId{0};  // this is a queue ptr for ftq itself

    // The supply/responsing fetch target state
    FetchTargetReadState supplyFetchTargetState;
    // The demanded fetch target ID to send to fetch
    FetchTargetId fetchDemandTargetId{0};

    FetchTargetEnqState fetchTargetEnqState;

    std::string _name;

  public:
    FetchTargetQueue(unsigned size);

    void squash(FetchTargetId new_enq_target_id,
                FetchStreamId new_enq_stream_id, Addr new_enq_pc);

    bool fetchTargetAvailable() const;

    FtqEntry &getTarget();

    FetchTargetEnqState &getEnqState() { return fetchTargetEnqState; }

    FetchTargetId getSupplyingTargetId()
    {
        return supplyFetchTargetState.targetId;
    }

    FetchStreamId getSupplyingStreamId()
    {
        return supplyFetchTargetState.entry.fsqID;
    }

    void finishCurrentFetchTarget();

    bool trySupplyFetchWithTarget();


    bool empty() const { return ftq.empty(); }

    unsigned size() const { return ftq.size(); }

    bool full() const { return ftq.size() >= ftqSize; }

    std::pair<bool, FTQIt> getDemandTargetIt();

    void enqueue(FtqEntry entry);

    void dump(const char *when);

    const std::string &name() const { return _name; }

    void setName(const std::string &parent) { _name = parent + ".ftq"; }

    bool validSupplyFetchTargetState() const;

    bool finishFetch(bool run_out_of_this_entry) {
        auto it = ftq.find(fetchDemandTargetId);
        if (run_out_of_this_entry && it != ftq.end()) {
            if (supplyFetchTargetState.entry.fsqID != it->second.fsqID) {
                return true;
            }
        }
        return false;
    }

    std::pair<FetchTargetId, FetchStreamId> nextSupplyTarget() {
        auto it = ftq.find(fetchDemandTargetId);
        if (it != ftq.end()) {
            return std::make_pair(it->first, it->second.fsqID);
        }
        return std::make_pair(getSupplyingTargetId(), getSupplyingStreamId());
    }
    
};

}
}

#endif  // __CPU_PRED_FETCH_TARGET_QUEUE_HH__
