/*
 * Copyright (c) 2001-2005 The Regents of The University of Michigan
 * Copyright (c) 2007 MIPS Technologies, Inc.
 * Copyright (c) 2020 Barkhausen Institut
 * Copyright (c) 2021 Huawei International
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met: redistributions of source code must retain the above copyright
 * notice, this list of conditions and the following disclaimer;
 * redistributions in binary form must reproduce the above copyright
 * notice, this list of conditions and the following disclaimer in the
 * documentation and/or other materials provided with the distribution;
 * neither the name of the copyright holders nor the names of its
 * contributors may be used to endorse or promote products derived from
 * this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 * A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 * OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

#include "arch/riscv/tlb.hh"

#include <string>
#include <vector>

#include "arch/riscv/faults.hh"
#include "arch/riscv/mmu.hh"
#include "arch/riscv/pagetable.hh"
#include "arch/riscv/pagetable_walker.hh"
#include "arch/riscv/pma_checker.hh"
#include "arch/riscv/pmp.hh"
#include "arch/riscv/pra_constants.hh"
#include "arch/riscv/utility.hh"
#include "base/inifile.hh"
#include "base/str.hh"
#include "base/trace.hh"
#include "cpu/thread_context.hh"
#include "debug/TLB.hh"
#include "debug/TLBGPre.hh"
#include "debug/TLBVerbose.hh"
#include "debug/TLBVerbose3.hh"
#include "debug/TLBVerbosel2.hh"
#include "debug/TLBtrace.hh"
#include "debug/autoNextline.hh"
#include "mem/page_table.hh"
#include "params/RiscvTLB.hh"
#include "sim/full_system.hh"
#include "sim/process.hh"
#include "sim/system.hh"

namespace gem5
{

using namespace RiscvISA;

///////////////////////////////////////////////////////////////////////
//
//  RISC-V TLB
//

static Addr
buildKey(Addr vpn, uint16_t asid)
{
    return (static_cast<Addr>(asid) << 48) | vpn;
}

TLB::TLB(const Params &p) :
    BaseTLB(p), is_dtlb(p.is_dtlb),is_L1tlb(p.is_L1tlb),isStage2(p.is_stage2),
    isTheSharedL2(p.is_the_sharedL2),size(p.size),sizeBack(32),
    l2TlbL1Size(p.l2tlb_l1_size),
    l2TlbL2Size(p.l2tlb_l2_size),l2TlbL3Size(p.l2tlb_l3_size),
    l2TlbSpSize(p.l2tlb_sp_size),
    regulationNum(p.regulation_num),
    tlb(size),lruSeq(0),hitInSp(false),
    hitPreEntry(0),hitPreNum(0),
    RemovePreUnused(0),AllPre(0),
    isOpenAutoNextLine(p.is_open_nextline),
    forwardPreSize(p.forward_pre_size),openForwardPre(p.open_forward_pre),
    openBackPre(p.open_back_pre),
    backPrePrecision(p.initial_back_pre_precision_value),
    forwardPrePrecision(p.initial_forward_pre_precision_value),
    allForwardPre(0),removeNoUseForwardPre(0),removeNoUseBackPre(0),
    usedBackPre(0),test_num(0),allUsed(0),forwardUsedPre(0),
    lastVaddr(0),lastPc(0), traceFlag(false),
    stats(this), pma(p.pma_checker),
    pmp(p.pmp),
    tlbL2L1(l2TlbL1Size *l2tlbLineSize),tlbL2L2(l2TlbL2Size *l2tlbLineSize),
    tlbL2L3(l2TlbL3Size *l2tlbLineSize),tlbL2Sp(l2TlbSpSize *l2tlbLineSize),
    forwardPre(forwardPreSize),backPre(32)
{

    if (is_L1tlb) {
        DPRINTF(TLBVerbose, "tlb11\n");
        for (size_t x = 0; x < size; x++) {
            tlb[x].trieHandle = nullptr;
            freeList.push_back(&tlb[x]);
        }
        walker = p.walker;
        walker->setTLB(this);
        DPRINTF(TLBVerbose, "tlb11 tlb_size %d size() %d\n", size, tlb.size());

    }
    if (isStage2 || isTheSharedL2) {
        DPRINTF(TLBVerbose, "tlbL2\n");
        for (size_t x_l2l1 = 0; x_l2l1 < l2TlbL1Size * l2tlbLineSize; x_l2l1++) {
            tlbL2L1[x_l2l1].trieHandle = nullptr;
            freeListL2L1.push_back(&tlbL2L1[x_l2l1]);
        }

        for (size_t x_l2l2 = 0; x_l2l2 < l2TlbL2Size * l2tlbLineSize; x_l2l2++) {
            tlbL2L2[x_l2l2].trieHandle = nullptr;
            freeListL2L2.push_back(&tlbL2L2[x_l2l2]);
        }
        for (size_t x_l2l3 = 0; x_l2l3 < l2TlbL3Size * l2tlbLineSize; x_l2l3++) {
            tlbL2L3[x_l2l3].trieHandle = nullptr;
            freeListL2L3.push_back(&tlbL2L3[x_l2l3]);
        }
        for (size_t x_l2sp = 0; x_l2sp < l2TlbSpSize * l2tlbLineSize; x_l2sp++) {
            tlbL2Sp[x_l2sp].trieHandle = nullptr;
            freeListL2sp.push_back(&tlbL2Sp[x_l2sp]);
        }
        for (size_t x_g = 0; x_g < forwardPreSize; x_g++) {
            forwardPre[x_g].trieHandle = nullptr;
            freeListForwardPre.push_back(&forwardPre[x_g]);
        }
        for (size_t x_f = 0; x_f < 32; x_f++) {
            backPre[x_f].trieHandle = nullptr;
            freeListBackPre.push_back(&backPre[x_f]);
        }
        DPRINTF(TLBVerbose, "l2l1.size() %d l2l2.size() %d l2l3.size() %d l2sp.size() %d\n", tlbL2L1.size(),
                tlbL2L2.size(), tlbL2L3.size(), tlbL2Sp.size());
        DPRINTF(TLBVerbose,
                "tlbl2 size l2tlb_l1_size %d l2tlb_l2_size %d l2tlb_l3_size "
                "%d l2tlb_sp_size %d\n",
                l2TlbL1Size, l2TlbL2Size, l2TlbL3Size, l2TlbSpSize);
    }
}

Walker *
TLB::getWalker()
{
    return walker;
}

void
TLB::evictLRU()
{
    // Find the entry with the lowest (and hence least recently updated)
    // sequence number.

    size_t lru = 0;
    for (size_t i = 1; i < size; i++) {
        if (tlb[i].lruSeq < tlb[lru].lruSeq)
            lru = i;
    }

    remove(lru);
}
void
TLB::evictForwardPre()
{
    size_t lru = 0;
    for (size_t i = 1; i < forwardPreSize; i++) {
        if (forwardPre[i].lruSeq < forwardPre[lru].lruSeq) {
            lru = i;
        }
    }
    removeForwardPre(lru);
}

void
TLB::evictBackPre()
{
    size_t lru = 0;
    for (size_t i = 1; i < sizeBack; i++) {
        if (backPre[i].lruSeq < backPre[lru].lruSeq) {
            lru = i;
        }
    }
    removeBackPre(lru);
}

void
TLB::l2TLBEvictLRU(int l2TLBlevel, Addr vaddr)
{
    size_t lru;
    size_t i;
    Addr l2_index;
    Addr l3_index;
    l2_index = (vaddr >> (PageShift + LEVEL_BITS + L2TLB_BLK_OFFSET)) & (L2TLB_L2_MASK);
    l3_index = (vaddr >> (PageShift + L2TLB_BLK_OFFSET)) & (L2TLB_L3_MASK);
    int l2_index_num = 0;
    int l3_index_num = 0;
    DPRINTF(TLB, "l2tlb_evictLRU tlb_l2l1_size %d\n", tlbL2L1.size());

    if (l2TLBlevel == L_L2L1) {
        lru =0;
        for (i = l2tlbLineSize;i< l2TlbL1Size*l2tlbLineSize;i=i+l2tlbLineSize){
            if (tlbL2L1[i].lruSeq < tlbL2L1[lru].lruSeq){
                lru = i;
            }
        }
        l2TLBRemove(lru, L_L2L1);
    }

    else if (l2TLBlevel == L_L2L2) {
        lru = 0;
        for (i = 0; i < l2TlbL2Size * l2tlbLineSize; i = i + l2tlbLineSize) {
            if ((tlbL2L2[i].index == l2_index) && (tlbL2L2[i].trieHandle != nullptr)) {
                DPRINTF(TLBVerbose, "vaddr %#x index %#x\n", tlbL2L2[i].vaddr, l2_index);
                if (l2_index_num == 0) {
                    lru = i;
                } else if (tlbL2L2[i].lruSeq < tlbL2L2[lru].lruSeq) {
                    lru = i;
                }
                l2_index_num++;
            }
        }
        if (l2_index_num == 2) {
            l2TLBRemove(lru, L_L2L2);
        }

        else if (l2_index_num > 2) {
            panic("wrong in l2l2 tlb l2_index_num %d\n",l2_index_num);
        }

    }

    else if (l2TLBlevel == L_L2L3) {
        lru = 0;
        for (i = 0; i < l2TlbL3Size * l2tlbLineSize; i = i + l2tlbLineSize) {
            if ((tlbL2L3[i].index == l3_index) && (tlbL2L3[i].trieHandle != nullptr)) {
                if (l3_index_num == 0) {
                    lru = i;
                } else if (tlbL2L3[i].lruSeq < tlbL2L3[lru].lruSeq) {
                    lru = i;
                }
                l3_index_num++;
            }
        }

        if (l3_index_num == 4){
            l2TLBRemove(lru, L_L2L3);
        }

        else if (l3_index_num > 4)
            panic("wrong in l2l3 tlb l3_index_num %d\n",l3_index_num);
    }

    else if ((l2TLBlevel == L_L2sp1) || (l2TLBlevel == L_L2sp2)) {
        lru =0;
        for (i = l2tlbLineSize; i < l2TlbSpSize * l2tlbLineSize; i = i + l2tlbLineSize) {
            if (tlbL2Sp[i].lruSeq < tlbL2Sp[lru].lruSeq) {
                lru = i;
            }
        }
        l2TLBRemove(lru, L_L2sp1);
    }
}

TlbEntry *
TLB::lookup(Addr vpn, uint16_t asid, BaseMMU::Mode mode, bool hidden,
            bool sign_used)
{
    TlbEntry *entry = trie.lookup(buildKey(vpn, asid));

    if (!hidden) {
        if (entry)
            entry->lruSeq = nextSeq();

        if (mode == BaseMMU::Write)
            stats.writeAccesses++;
        else
            stats.readAccesses++;

        if (!entry) {
            if (mode == BaseMMU::Write)
                stats.writeMisses++;
            else
                stats.readMisses++;
        }
        else {
            if (mode == BaseMMU::Write)
                stats.writeHits++;
            else
                stats.readHits++;
        }

        if (entry) {
            if (entry->isSquashed) {
                if (mode == BaseMMU::Write)
                    stats.writeHitsSquashed++;
                else
                    stats.readHitsSquashed++;
            }
        }

        DPRINTF(TLBVerbose, "lookup(vpn=%#x, asid=%#x): %s ppn %#x\n",
                vpn, asid, entry ? "hit" : "miss", entry ? entry->paddr : 0);
    }
    if (sign_used) {
        if (entry) {
            entry->used = true;
        }
    }

    return entry;
}
TlbEntry *
TLB::lookupForwardPre(Addr vpn, uint64_t asid, bool hidden)
{
    TlbEntry *entry = trieForwardPre.lookup(buildKey(vpn, asid));
    if (!hidden) {
        if (entry) {
            entry->lruSeq = nextSeq();
            entry->used = true;
        }
    }
    return entry;
}

TlbEntry *
TLB::lookupBackPre(Addr vpn, uint64_t asid, bool hidden)
{
    TlbEntry *entry = trieBackPre.lookup(buildKey(vpn, asid));
    if (!hidden) {
        if (entry) {
            entry->lruSeq = nextSeq();
            entry->used = true;
            stats.backHits++;
        }
    }
    return entry;
}

bool
TLB::autoOpenNextline()
{
    TLB *l2tlb;

    if (isStage2)
        l2tlb = this;
    else
        l2tlb = static_cast<TLB *>(nextLevel());

    int pre_num_c = l2tlb->AllPre;
    int removePreUnused_c = l2tlb->RemovePreUnused;

    bool auto_nextline;
    double precision =
        (double)((pre_num_c - removePreUnused_c) / (pre_num_c + 1));
    if (isOpenAutoNextLine) {
        if (removePreUnused_c > regulationNum) {
            if (precision < nextlinePrecision) {
                DPRINTF(autoNextline,
                        "pre_num %d removePreUnused %d precision %f\n",
                        pre_num_c, removePreUnused_c, precision);
                auto_nextline = false;
            }

            else
                auto_nextline = true;
        } else
            auto_nextline = true;
    } else
        auto_nextline = true;


    return auto_nextline;
}
void
TLB::updateL2TLBSeq(TlbEntryTrie *Trie_l2, Addr vpn, Addr step, uint16_t asid)
{
    for (int i = 0; i < l2tlbLineSize; i++) {
        TlbEntry *m_entry = (*Trie_l2).lookup(buildKey(vpn + step * i, asid));
        if (m_entry == nullptr) {
            DPRINTF(TLB, "l2sp1 vaddr basic %#x vaddr %#x \n", vpn, vpn + step * i);
            panic("l2 TLB link num is empty\n");
        }
        m_entry->lruSeq = nextSeq();
    }
}
TlbEntry *
TLB::lookupL2TLB(Addr vpn, uint16_t asid, BaseMMU::Mode mode, bool hidden, int f_level, bool sign_used)
{

    Addr f_vpnl2l1 = (vpn >> (PageShift + 2 * LEVEL_BITS)) << (PageShift + 2 * LEVEL_BITS);
    Addr f_vpnl2l2 = (vpn >> (PageShift + LEVEL_BITS)) << (PageShift + LEVEL_BITS);
    Addr vpnl2l1 = (vpn >> (PageShift + 2 * LEVEL_BITS + L2TLB_BLK_OFFSET))
                   << (PageShift + 2 * LEVEL_BITS + L2TLB_BLK_OFFSET);
    Addr vpnl2sp1 = vpnl2l1;
    Addr vpnl2l2 = (vpn >> (PageShift + LEVEL_BITS + L2TLB_BLK_OFFSET)) << (PageShift + LEVEL_BITS + L2TLB_BLK_OFFSET);
    Addr vpnl2sp2 = vpnl2l2;
    Addr vpnl2l3 = (vpn >> (PageShift + L2TLB_BLK_OFFSET)) << (PageShift + L2TLB_BLK_OFFSET);

    Addr step;
    int i;

    DPRINTF(TLB, "f_vpnl2l1 %#x f_vpnl2l2 %#x vpn %#x\n", f_vpnl2l1, f_vpnl2l2, vpn);


    TlbEntry *entry_l2 = nullptr;

    if (is_L1tlb && !isStage2)
        panic("wrong in tlb config\n");

    if (f_level == L_L2L1) {
        DPRINTF(TLB, "look up l2tlb in l2l1 key %#x\n", buildKey(f_vpnl2l1, asid));
        TlbEntry *entry_l2l1 = trieL2L1.lookup(buildKey(f_vpnl2l1, asid));
        entry_l2 = entry_l2l1;
        step = 0x1 << (PageShift + 2 * LEVEL_BITS);
        if ((!hidden) && (entry_l2l1))
            updateL2TLBSeq(&trieL2L1, vpnl2l1, step, asid);
    }
    if (f_level == L_L2L2) {
        DPRINTF(TLB, "look up l2tlb in l2l2\n");
        TlbEntry *entry_l2l2 = trieL2L2.lookup(buildKey(f_vpnl2l2, asid));
        entry_l2 = entry_l2l2;
        step = 0x1 << (PageShift + LEVEL_BITS);
        if ((!hidden) && (entry_l2l2))
            updateL2TLBSeq(&trieL2L2, vpnl2l2, step, asid);
    }
    if (f_level == L_L2L3) {
        DPRINTF(TLB, "look up l2tlb in l2l3\n");
        TlbEntry *entry_l2l3 = trieL2L3.lookup(buildKey(vpn, asid));
        entry_l2 = entry_l2l3;
        step = 0x1000;
        bool write_sign = false;
        if (entry_l2l3) {
            if (sign_used) {
                if (entry_l2l3->isPre && (!entry_l2l3->preSign)) {
                    write_sign = true;
                    stats.hitPreEntry++;
                    hitPreEntry++;
                }
                if (entry_l2l3->isPre) {
                    stats.hitPreNum++;
                    hitPreNum++;
                }
            }
            for (i = 0; i < l2tlbLineSize; i++) {
                TlbEntry *m_entry_l2l3 = trieL2L3.lookup(buildKey((vpnl2l3 + step * i), asid));
                if (m_entry_l2l3 == nullptr) {
                    DPRINTF(TLB, "l2l3 vaddr basic %#x vaddr %#x\n", vpnl2l3, vpnl2l3 + step * i);
                    panic("l2l3 TLB link num is empty\n");
                }
                if (!hidden)
                    m_entry_l2l3->lruSeq = nextSeq();
                if (write_sign)
                    m_entry_l2l3->preSign = true;
            }
            if (!hidden) {
                if (mode == BaseMMU::Write) {
                    stats.writeL2Tlbl3Hits++;
                } else {
                    stats.ReadL2Tlbl3Hits++;
                }
                if (entry_l2l3->isSquashed) {
                    if (mode == BaseMMU::Write) {
                        stats.writeL2l3TlbSquashedHits++;
                    } else {
                        stats.ReadL2l3TlbSquashedHits++;
                    }
                }
            }
        }
    }
    if (f_level == L_L2sp1) {
        DPRINTF(TLB, "look up l2tlb in l2sp1\n");
        TlbEntry *entry_l2sp1 = trieL2sp.lookup(buildKey(f_vpnl2l1, asid));
        entry_l2 = entry_l2sp1;
        step = 0x1 << (PageShift + 2 * LEVEL_BITS);
        if (entry_l2sp1) {
            if (entry_l2sp1->level == 1) {
                DPRINTF(TLB, "hit in sp but sp2 , return\n");
                return nullptr;
            }
            if (!hidden)
                updateL2TLBSeq(&trieL2sp, vpnl2sp1, step, asid);
        }
    }
    if (f_level == L_L2sp2) {
        DPRINTF(TLB, "look up l2tlb in l2sp2\n");
        TlbEntry *entry_l2sp2 = trieL2sp.lookup(buildKey(f_vpnl2l2, asid));
        entry_l2 = entry_l2sp2;
        step = 0x1 << (PageShift + LEVEL_BITS);
        if (entry_l2sp2) {
            if (entry_l2sp2->level == 2) {
                DPRINTF(TLB, "hit in sp but sp1 , return\n");
                return nullptr;
            }
            if (!hidden)
                updateL2TLBSeq(&trieL2sp, vpnl2sp2, step, asid);
        }
    }


    if (sign_used) {
        if (entry_l2)
            entry_l2->used = true;
    }

    return entry_l2;
}

TlbEntry *
TLB::insert(Addr vpn, const TlbEntry &entry,bool squashed_update)
{
    DPRINTF(TLBGPre, "insert(vpn=%#x, asid=%#x): ppn=%#x pte=%#x size=%#x\n",
            vpn, entry.asid, entry.paddr, entry.pte, entry.size());

    // If somebody beat us to it, just use that existing entry.
    TlbEntry *newEntry = lookup(vpn, entry.asid, BaseMMU::Read, true, false);
    if (squashed_update) {
        if (newEntry) {
            if (newEntry->isSquashed) {
                return newEntry;
            }
            // update isSquashed flag
            newEntry->isSquashed = entry.isSquashed;
            stats.squashedInsert++;

        } else {
            DPRINTF(TLBVerbosel2, "update isSquashed flag but no entry\n");
        }
        return newEntry;
    }
    if (newEntry) {
        // update PTE flags (maybe we set the dirty/writable flag)
        newEntry->pte = entry.pte;
        Addr newEntryAddr = buildKey(newEntry->vaddr,newEntry->asid);
        Addr vpnAddr = buildKey(entry.vaddr,entry.asid);
        if (newEntry->vaddr != vpn) {
            DPRINTF(TLBGPre, "tlb in newEntryAddr %#x vpnAddr %#x\n", newEntryAddr, vpnAddr);
            DPRINTF(TLBGPre, "l1 tlb insert(vpn=%#x, vpn2 %#x asid=%#x): ppn=%#x pte=%#x size=%#x\n", vpn, entry.vaddr,
                    entry.asid, entry.paddr, entry.pte, entry.size());
            DPRINTF(TLBGPre, "l1 newentry(vpn=%#x, vpn2 %#x asid=%#x): ppn=%#x pte=%#x size=%#x \n", vpn,
                    newEntry->vaddr, newEntry->asid, newEntry->paddr, newEntry->pte, newEntry->size());
            DPRINTF(TLBGPre, "l1 newEntry->vaddr %#x vpn %#x \n", newEntry->vaddr, vpn);
        }

        assert(newEntry->vaddr == vpn);
        return newEntry;
    }

    if (freeList.empty())
        evictLRU();

    newEntry = freeList.front();
    freeList.pop_front();

    Addr key = buildKey(vpn, entry.asid);
    *newEntry = entry;
    newEntry->lruSeq = nextSeq();
    newEntry->vaddr = vpn;
    newEntry->trieHandle =
    trie.insert(key, TlbEntryTrie::MaxBits - entry.logBytes, newEntry);
    DPRINTF(TLBVerbosel2, "trie insert key %#x logbytes %#x paddr %#x\n", key,
            entry.logBytes, newEntry->paddr);
    // stats all insert number
    stats.ALLInsert++;
    allUsed++;
    return newEntry;
}

TlbEntry *
TLB::insertForwardPre(Addr vpn, const TlbEntry &entry)
{
    TlbEntry *newEntry = lookupForwardPre(vpn, entry.asid, true);
    if (newEntry)
        return newEntry;
    if (freeListForwardPre.empty()) {
        evictForwardPre();
    }
    newEntry = freeListForwardPre.front();
    freeListForwardPre.pop_front();

    Addr key = buildKey(vpn, entry.asid);
    *newEntry = entry;
    newEntry->lruSeq = nextSeq();
    newEntry->vaddr = vpn;
    newEntry->used = false;
    newEntry->trieHandle = trieForwardPre.insert(key, TlbEntryTrie::MaxBits - entry.logBytes, newEntry);
    allForwardPre++;
    return newEntry;
}

TlbEntry *
TLB::insertBackPre(Addr vpn, const TlbEntry &entry)
{
    TlbEntry *newEntry = lookupBackPre(vpn, entry.asid, true);
    if (newEntry)
        return newEntry;
    if (freeListBackPre.empty()) {
        evictBackPre();
    }
    newEntry = freeListBackPre.front();
    freeListBackPre.pop_front();

    Addr key = buildKey(vpn, entry.asid);
    *newEntry = entry;
    newEntry->lruSeq = nextSeq();
    newEntry->vaddr = vpn;
    newEntry->used = false;
    newEntry->trieHandle = trieBackPre.insert(key, TlbEntryTrie::MaxBits - entry.logBytes, newEntry);
    return newEntry;
}

TlbEntry *
TLB::L2TLBInsertIn(Addr vpn, const TlbEntry &entry, int choose, EntryList *List, TlbEntryTrie *Trie_l2, int sign,
                   bool squashed_update)
{
    DPRINTF(TLB,
            "l2tlb insert(vpn=%#x, vpn2 %#x asid=%#x): ppn=%#x pte=%#x "
            "size=%#x level %d\n",
            vpn, entry.vaddr, entry.asid, entry.paddr, entry.pte, entry.size(),
            choose);
    TlbEntry *newEntry;
    Addr key;
    newEntry =
        lookupL2TLB(vpn, entry.asid, BaseMMU::Read, true, choose, false);
    Addr step = 0;
    if ((choose == L_L2L1) || (choose == L_L2sp1)) {
        step = 0x1 << 30;
    } else if ((choose == L_L2L2) || (choose == L_L2sp2)) {
        step = 0x1 << 21;
    } else if (choose == L_L2L3) {
        step = 0x1 << 12;
    }

    if (squashed_update) {
        if (newEntry) {
            if (newEntry->isSquashed) {
                return newEntry;
            }
            newEntry->isSquashed = true;
            stats.squashedInsertL2++;
            for (int i = 1; i < l2tlbLineSize; i++) {
                newEntry = lookupL2TLB(vpn + step * i, entry.asid, BaseMMU::Read, true, choose, false);
                stats.squashedInsertL2++;
                if (newEntry) {
                    newEntry->isSquashed = true;
                }
            }
        }
        return newEntry;
    }
    if (newEntry) {
        newEntry->pte = entry.pte;
        if (newEntry->vaddr != vpn) {
            Addr newEntryAddr = buildKey(newEntry->vaddr,newEntry->asid);
            Addr vpnAddr = buildKey(entry.vaddr,entry.asid);
            DPRINTF(TLBVerbosel2, "newEntryAddr %#x vpnAddr %#x\n", newEntryAddr, vpnAddr);
            DPRINTF(TLBVerbosel2,
                    "l2tlb insert(vpn=%#x, vpn2 %#x asid=%#x): ppn=%#x "
                    "pte=%#x size=%#x level %d\n",
                    vpn, entry.vaddr, entry.asid, entry.paddr, entry.pte, entry.size(), choose);
            DPRINTF(TLBVerbosel2,
                    "newentry(vpn=%#x, vpn2 %#x asid=%#x): ppn=%#x pte=%#x "
                    "size=%#x level %d\n",
                    vpn, newEntry->vaddr, newEntry->asid, newEntry->paddr, newEntry->pte, newEntry->size(), choose);
            DPRINTF(TLBVerbosel2, "newEntry->vaddr %#x vpn %#x choose %d\n", newEntry->vaddr, vpn, choose);
            assert(0);
        }
        return newEntry;
    }
    DPRINTF(TLB, "not hit in l2 tlb\n");
    if ((choose == L_L2L2 || choose == L_L2L3) && (sign == 0)) {
        DPRINTF(TLB, "choose %d sign %d\n", choose, sign);
        l2TLBEvictLRU(choose, vpn);
    } else {
        if ((*List).empty())
            l2TLBEvictLRU(choose, vpn);
    }

    newEntry = (*List).front();
    (*List).pop_front();


    key = buildKey(vpn, entry.asid);

    *newEntry = entry;
    newEntry->lruSeq = nextSeq();
    newEntry->vaddr = vpn;
    if (entry.paddr == 0) {
        DPRINTF(TLB, " l2tlb num is outside vaddr %#x paddr %#x \n",
                entry.vaddr, entry.paddr);
    }

    newEntry->trieHandle = (*Trie_l2).insert(
        key, TlbEntryTrie::MaxBits - entry.logBytes, newEntry);


    DPRINTF(TLB, "l2tlb trie insert key %#x logbytes %#x len %#x\n", key,
            entry.logBytes,TlbEntryTrie::MaxBits - entry.logBytes);
    stats.ALLInsertL2++;
    if (choose == L_L2L3)
        allUsed++;
    if (entry.isPre) {
        stats.AllPre++;
        AllPre++;
    }

    return newEntry;

}

TlbEntry *
TLB::L2TLBInsert(Addr vpn, const TlbEntry &entry, int level, int choose, int sign, bool squashed_update)
{
    TLB *l2tlb;
    if (isStage2)
        l2tlb = this;
    else
        l2tlb = static_cast<TLB *>(nextLevel());

    TlbEntry *newEntry = nullptr;
    DPRINTF(TLB, "choose %d vpn %#x entry->vaddr %#x\n", choose, vpn, entry.vaddr);
    if (choose == 1)
        newEntry =
            l2tlb->L2TLBInsertIn(vpn, entry, choose, &l2tlb->freeListL2L1, &l2tlb->trieL2L1, sign, squashed_update);
    else if (choose == 2)
        newEntry =
            l2tlb->L2TLBInsertIn(vpn, entry, choose, &l2tlb->freeListL2L2, &l2tlb->trieL2L2, sign, squashed_update);
    else if (choose == 3)
        newEntry =
            l2tlb->L2TLBInsertIn(vpn, entry, choose, &l2tlb->freeListL2L3, &l2tlb->trieL2L3, sign, squashed_update);
    else if (choose == 4)
        newEntry =
            l2tlb->L2TLBInsertIn(vpn, entry, choose, &l2tlb->freeListL2sp, &l2tlb->trieL2sp, sign, squashed_update);
    else if (choose == 5)
        newEntry =
            l2tlb->L2TLBInsertIn(vpn, entry, choose, &l2tlb->freeListL2sp, &l2tlb->trieL2sp, sign, squashed_update);

    if (!squashed_update) {
        assert(newEntry != nullptr);
    }


    return newEntry;
}


void
TLB::demapPage(Addr vpn, uint64_t asid)
{
    DPRINTF(TLBGPre, "flush(vpn=%#x, asid=%#x)\n", vpn, asid);
    asid &= 0xFFFF;

    size_t i;

    TLB *l2tlb;
    if (isStage2)
        l2tlb = this;
    else
        l2tlb = static_cast<TLB *>(nextLevel());

    if ((l2tlb == nullptr) && (!isStage2))
        assert(0);

    if (vpn == 0 && asid == 0) {
        flushAll();
        if (!isStage2) {
            l2tlb->flushAll();
        }

    }

    else {
        DPRINTF(TLB, "flush(vpn=%#x, asid=%#x)\n", vpn, asid);
        DPRINTF(TLB, "l1tlb flush(vpn=%#x, asid=%#x)\n", vpn, asid);
        if (vpn != 0 && asid != 0) {

            TlbEntry *newEntry = lookup(vpn, asid, BaseMMU::Read, true, false);
            if (newEntry)
                remove(newEntry - tlb.data());
            l2tlb->demapPageL2(vpn, asid);

        } else {
            for (i = 0; i < size; i++) {
                if (tlb[i].trieHandle) {
                    Addr mask = ~(tlb[i].size() - 1);
                    if ((vpn == 0 || (vpn & mask) == tlb[i].vaddr) &&
                        (asid == 0 || tlb[i].asid == asid))
                        remove(i);
                }
            }
            l2tlb->demapPageL2(vpn, asid);
        }
    }
}

void
TLB::demapPageL2(Addr vpn, uint64_t asid)
{
    asid &= 0xFFFF;
    std::vector<Addr> vpn_vec;
    std::vector<TlbEntry *> tlb_lists;
    vpn_vec.push_back(0);
    Addr vpnl2l1 = (vpn >> (PageShift + 2 * LEVEL_BITS + L2TLB_BLK_OFFSET))
                   << (PageShift + 2 * LEVEL_BITS + L2TLB_BLK_OFFSET);
    vpn_vec.push_back(vpnl2l1);
    tlb_lists.push_back(tlbL2L1.data());
    Addr vpnl2l2 = (vpn >> (PageShift + LEVEL_BITS + L2TLB_BLK_OFFSET)) << (PageShift + LEVEL_BITS + L2TLB_BLK_OFFSET);
    vpn_vec.push_back(vpnl2l2);
    tlb_lists.push_back(tlbL2L2.data());
    Addr vpnl2l3 = (vpn >> (PageShift + L2TLB_BLK_OFFSET)) << (PageShift + L2TLB_BLK_OFFSET);
    vpn_vec.push_back(vpnl2l3);
    tlb_lists.push_back(tlbL2L3.data());
    Addr vpnl2sp1 = (vpn >> (PageShift + 2 * LEVEL_BITS + L2TLB_BLK_OFFSET))
                    << (PageShift + 2 * LEVEL_BITS + L2TLB_BLK_OFFSET);
    vpn_vec.push_back(vpnl2sp1);
    tlb_lists.push_back(tlbL2Sp.data());
    Addr vpnl2sp2 = (vpn >> (PageShift + LEVEL_BITS + L2TLB_BLK_OFFSET))
                    << (PageShift + LEVEL_BITS + L2TLB_BLK_OFFSET);
    vpn_vec.push_back(vpnl2sp2);
    int i;

    DPRINTF(TLB, "l2 flush(vpn=%#x, asid=%#x)\n", vpn, asid);
    DPRINTF(TLBVerbose3, "l2tlb flush(vpn=%#x, asid=%#x)\n", vpn, asid);

    TlbEntry *l2_newEntry[6] = {nullptr, nullptr, nullptr, nullptr, nullptr, nullptr};
    for (int ii = 1; ii < 6; ii++) {
        l2_newEntry[ii] = lookupL2TLB(vpn_vec[ii], asid, BaseMMU::Read, true, ii, false);
    }


    if (vpn != 0 && asid != 0) {
        for (i = 1; i < 6; i++) {
            int tlb_i = 0;
            if (i - 1 > 3)
                tlb_i = 3;
            else
                tlb_i = i - 1;
            if (l2_newEntry[i]) {
                TlbEntry *m_newEntry = lookupL2TLB(vpn_vec[i], asid, BaseMMU::Read, true, i, false);
                assert(m_newEntry != nullptr);
                l2TLBRemove(m_newEntry - tlb_lists[tlb_i], i);
            }
        }
    } else {
        for (i = 0; i < l2TlbL1Size * l2tlbLineSize; i = i + l2tlbLineSize) {
            if (tlbL2L1[i].trieHandle) {
                Addr l2l1_mask = ~(tlbL2L1[i].size() - 1);
                if ((vpnl2l1 == 0 || (vpnl2l1 & l2l1_mask) == tlbL2L1[i].vaddr) &&
                    (asid == 0 || tlbL2L1[i].asid == asid)) {
                    l2TLBRemove(i, L_L2L1);
                }
            }
        }
        for (i = 0; i < l2TlbL2Size * l2tlbLineSize; i = i + l2tlbLineSize) {
            if (tlbL2L2[i].trieHandle) {
                Addr l2l2_mask = ~(tlbL2L2[i].size() - 1);
                if ((vpnl2l2 == 0 || (vpnl2l2 & l2l2_mask) == tlbL2L2[i].vaddr) &&
                    (asid == 0 || tlbL2L2[i].asid == asid)) {
                    l2TLBRemove(i, L_L2L2);
                    DPRINTF(TLBVerbose3, "l2l2 remove vaddr %#x vpn %#x vpnl2l3\n", tlbL2L2[i].vaddr, vpn, vpnl2l2);
                }
            }
        }
        for (i = 0; i < l2TlbL3Size * l2tlbLineSize; i = i + l2tlbLineSize) {
            if (tlbL2L3[i].trieHandle) {
                Addr l2l3_mask = ~(tlbL2L3[i].size() - 1);
                if ((vpnl2l3 == 0 || (vpnl2l3 & l2l3_mask) == tlbL2L3[i].vaddr) &&
                    (asid == 0 || tlbL2L3[i].asid == asid)) {
                    l2TLBRemove(i, L_L2L3);
                    DPRINTF(TLBVerbose3, "l2l3 remove vaddr %#x vpn %#x vpnl2l3\n", tlbL2L3[i].vaddr, vpn, vpnl2l3);
                }
            }
        }
        for (i = 0; i < l2TlbSpSize * l2tlbLineSize; i++) {
            Addr l2sp_mask = ~(tlbL2Sp[i].size() - 1);
            if (tlbL2Sp[i].trieHandle) {
                if ((vpnl2l1 == 0 || (vpnl2l1 & l2sp_mask) == tlbL2Sp[i].vaddr) &&
                    (asid == 0 || tlbL2Sp[i].asid == asid)) {
                    l2TLBRemove(i, L_L2sp1);
                }
            }
            if (tlbL2Sp[i].trieHandle) {
                if ((vpnl2l2 == 0 || (vpnl2l2 & l2sp_mask) == tlbL2Sp[i].vaddr) &&
                    (asid == 0 || tlbL2Sp[i].asid == asid)) {
                    l2TLBRemove(i, L_L2sp2);
                }
            }
        }
    }
}

void
TLB::flushAll()
{
    size_t i;
    if (is_L1tlb) {
        for (i = 0; i < size; i++) {
            if (tlb[i].trieHandle)
                remove(i);
        }
    }
    if (isStage2 || isTheSharedL2) {
        for (i = 0; i < l2TlbL1Size * l2tlbLineSize; i = i + l2tlbLineSize) {
            if (tlbL2L1[i].trieHandle)
                l2TLBRemove(i, L_L2L1);
        }
        for (i = 0; i < l2TlbL2Size * l2tlbLineSize; i = i + l2tlbLineSize) {
            if (tlbL2L2[i].trieHandle)
                l2TLBRemove(i, L_L2L2);
        }
        for (i = 0; i < l2TlbL3Size * l2tlbLineSize; i = i + l2tlbLineSize) {
            if (tlbL2L3[i].trieHandle)
                l2TLBRemove(i, L_L2L3);
        }
        for (i = 0; i < l2TlbSpSize * l2tlbLineSize; i = i + l2tlbLineSize) {
            if (tlbL2Sp[i].trieHandle)
                l2TLBRemove(i, L_L2sp1);
        }
    }
}

void
TLB::remove(size_t idx)
{
    assert(tlb[idx].trieHandle);
    if (tlb[idx].used) {
        stats.l1tlbUsedRemove++;
    } else {
        stats.l1tlbUnusedRemove++;
    }
    trie.remove(tlb[idx].trieHandle);
    tlb[idx].trieHandle = nullptr;
    freeList.push_back(&tlb[idx]);
    stats.l1tlbRemove++;
}

void
TLB::removeForwardPre(size_t idx)
{
    assert(forwardPre[idx].trieHandle);
    if (!forwardPre[idx].used) {
        removeNoUseForwardPre++;
        stats.removeNoUseForwardPre++;
    } else {
        forwardUsedPre++;
        stats.usedForwardPre++;
    }
    trieForwardPre.remove(forwardPre[idx].trieHandle);
    forwardPre[idx].trieHandle = nullptr;
    freeListForwardPre.push_back(&forwardPre[idx]);
}

void
TLB::removeBackPre(size_t idx)
{
    assert(backPre[idx].trieHandle);
    if (!backPre[idx].used) {
        removeNoUseBackPre++;
        stats.removeNoUseBackPre++;
    } else {
        usedBackPre++;
        stats.usedBackPre++;
    }
    trieBackPre.remove(backPre[idx].trieHandle);
    backPre[idx].trieHandle = nullptr;
    freeListBackPre.push_back(&backPre[idx]);
}
void
TLB::l2tlbRemoveIn(EntryList *List, TlbEntryTrie *Trie_l2, std::vector<TlbEntry> &tlb, size_t idx, int choose)
{
    DPRINTF(TLB, "remove tlb %d idx %d\n", choose, idx);
    DPRINTF(TLB, "remove tlb (vpn=%#x, asid=%#x): ppn=%#x pte=%#x size=%#x\n", tlb[idx].vaddr, tlb[idx].asid,
            tlb[idx].paddr, tlb[idx].pte, tlb[idx].size());
    assert(tlb[idx].trieHandle);
    (*Trie_l2).remove(tlb[idx].trieHandle);
    tlb[idx].trieHandle = nullptr;
    (*List).push_back(&tlb[idx]);
}

void
TLB::l2TLBRemove(size_t idx, int choose)
{
    int i;
    if (choose == L_L2L1) {
        stats.l2l1tlbRemove++;
        if (tlbL2L1[idx].used) {
            stats.l2l1tlbUsedRemove++;
        } else {
            stats.l2l1tlbUnusedRemove++;
        }

        for (i = 0; i < l2tlbLineSize; i++) {
            DPRINTF(TLB, "remove tlb_l2l1 idx %d idx+i %d\n", idx, idx + i);
            l2tlbRemoveIn(&freeListL2L1, &trieL2L1, tlbL2L1, idx + i, L_L2L1);
        }
    }
    if (choose == L_L2L2) {
        stats.l2l2tlbRemove++;
        if (tlbL2L2[idx].used) {
            stats.l2l2tlbUsedRemove++;
        } else {
            stats.l2l2tlbUnusedRemove++;
        }
        EntryList::iterator iterl2l2 = freeListL2L2.begin();
        for (i = 0; i < l2tlbLineSize; i++) {
            DPRINTF(TLB, "remove tlb_l2l2 idx %d idx+i %d\n", idx, idx + i);
            l2tlbRemoveIn(&freeListL2L2, &trieL2L2, tlbL2L2, idx + i, L_L2L2);
        }
    }
    if (choose == L_L2L3) {
        stats.l2l3tlbRemove++;
        if (tlbL2L3[idx].used) {
            stats.l2l3tlbUsedRemove++;
        } else {
            stats.l2l3tlbUnusedRemove++;
        }
        if (tlbL2L3[idx].isPre && !tlbL2L3[idx].preSign) {
            stats.RemovePreUnused++;
            RemovePreUnused++;
        }

        EntryList::iterator iterl2l3 = freeListL2L3.begin();
        for (i = 0; i < l2tlbLineSize; i++) {
            DPRINTF(TLB, "remove tlb_l2l3 idx %d idx+i %d\n", idx, idx + i);
            l2tlbRemoveIn(&freeListL2L3, &trieL2L3, tlbL2L3, idx + i, L_L2L3);
        }
    }
    if (choose == L_L2sp1 || choose == L_L2sp2) {
        stats.l2sptlbRemove++;
        if (tlbL2Sp[idx].used) {
            stats.l2sptlbUsedRemove++;
        } else {
            stats.l2sptlbUnusedRemove++;
        }
        for (i = 0; i < l2tlbLineSize; i++) {
            DPRINTF(TLB, "remove tlb_l2sp idx %d idx+i %d\n", idx, idx + i);
            l2tlbRemoveIn(&freeListL2sp, &trieL2sp, tlbL2Sp, idx + i, L_L2sp1);
        }
    }
}

Fault
TLB::checkPermissions(STATUS status, PrivilegeMode pmode, Addr vaddr,
                      BaseMMU::Mode mode, PTESv39 pte)
{
    Fault fault = NoFault;

    if (mode == BaseMMU::Read && !pte.r) {
        fault = createPagefault(vaddr, 0, mode, false);
    } else if (mode == BaseMMU::Write && !pte.w) {
        fault = createPagefault(vaddr, 0, mode, false);
    } else if (mode == BaseMMU::Execute && !pte.x) {
        fault = createPagefault(vaddr, 0, mode, false);
    }

    if (fault == NoFault) {
        if (pmode == PrivilegeMode::PRV_U && !pte.u) {
            fault = createPagefault(vaddr, 0, mode, false);
        } else if (pmode == PrivilegeMode::PRV_S && pte.u && (status.sum == 0)) {
            fault = createPagefault(vaddr, 0, mode, false);
        }
    }

    return fault;
}

Fault
TLB::createPagefault(Addr vaddr, Addr gPaddr,BaseMMU::Mode mode,bool G)
{
    ExceptionCode code;
    if (G) {
        if (mode == BaseMMU::Read)
            code = ExceptionCode::LOADG_PAGE;
        else if (mode == BaseMMU::Write)
            code = ExceptionCode::STOREG_PAGE;
        else
            code = ExceptionCode::INSTG_PAGE;

    } else {
        if (mode == BaseMMU::Read)
            code = ExceptionCode::LOAD_PAGE;
        else if (mode == BaseMMU::Write)
            code = ExceptionCode::STORE_PAGE;
        else
            code = ExceptionCode::INST_PAGE;
    }

    DPRINTF(TLB, "Create page fault #%i on %#lx\n", code, vaddr);
    return std::make_shared<AddressFault>(vaddr, gPaddr, code);
}

Addr
TLB::translateWithTLB(Addr vaddr, uint16_t asid, BaseMMU::Mode mode)
{
    TlbEntry *e = lookup(vaddr, asid, mode, false, false);
    DPRINTF(TLB, "translateWithTLB vaddr %#x \n", vaddr);
    assert(e != nullptr);
    DPRINTF(TLBGPre, "translateWithTLB vaddr %#x paddr %#x\n", vaddr,
            e->paddr << PageShift | (vaddr & mask(e->logBytes)));
    return (e->paddr << PageShift) | (vaddr & mask(e->logBytes));
}
Fault
TLB::L2TLBPagefault(Addr vaddr, BaseMMU::Mode mode, const RequestPtr &req, bool isPre, bool is_back_pre)
{
    if (req->isInstFetch()) {
        Addr page_l2_start = (vaddr >> 12) << 12;
        DPRINTF(TLBVerbosel2, "vaddr %#x,req_pc %#x,page_l2_start %#x\n",
                vaddr, req->getPC(), page_l2_start);
        if (req->getPC() < page_l2_start) {
            DPRINTF(TLBVerbosel2, "vaddr %#x,req_pc %#x,page_l2_start %#x\n",
                    vaddr, req->getPC(), page_l2_start);
            return createPagefault(page_l2_start, 0, mode, false);
        }
        return createPagefault(req->getPC(), 0, mode, false);
    } else {
        DPRINTF(TLBVerbosel2, "vaddr 2 %#x,req_pc %#x,get vaddr %#x\n", vaddr, req->getPC(), req->getVaddr());
        if (is_back_pre)
            return createPagefault(req->getBackPreVaddr(), 0, mode, false);
        else if (isPre)
            return createPagefault(req->getForwardPreVaddr(), 0, mode, false);
        else
            return createPagefault(req->getVaddr(), 0, mode, false);
    }
}

Fault
TLB::L2TLBCheck(PTESv39 pte, int level, STATUS status, PrivilegeMode pmode, Addr vaddr, BaseMMU::Mode mode,
                const RequestPtr &req, bool isPre, bool is_back_pre)
{
    Fault fault = NoFault;
    hitInSp = false;
    if (isPre) {
        DPRINTF(TLBGPre, "l2tlb_check paddr %#x vaddr %#x pte %#x\n", pte.ppn,
                vaddr, pte);
    }

    if (!pte.v || (!pte.r && pte.w)) {
        hitInSp = true;
        fault = L2TLBPagefault(vaddr, mode, req, isPre, is_back_pre);

    } else {
        if (pte.r || pte.x) {
            hitInSp = true;
            fault = checkPermissions(status, pmode, vaddr, mode, pte);
            if (fault == NoFault) {
                if (level >= 1 && pte.ppn0 != 0) {
                    fault = L2TLBPagefault(vaddr, mode, req, isPre, is_back_pre);
                } else if (level == 2 && pte.ppn1 != 0) {
                    fault = L2TLBPagefault(vaddr, mode, req, isPre, is_back_pre);
                }
            }

            if (fault == NoFault) {
                if (!pte.a) {
                    fault = L2TLBPagefault(vaddr, mode, req, isPre, is_back_pre);
                }
                if (!pte.d && mode == BaseMMU::Write) {
                    fault = L2TLBPagefault(vaddr, mode, req, isPre, is_back_pre);
                }
            }

        } else {
            level--;
            if (level < 0) {
                hitInSp = true;
                fault = L2TLBPagefault(vaddr, mode, req, isPre, is_back_pre);
            } else {
                hitInSp = false;
            }
        }
    }
    DPRINTF(TLB, "tlb check final\n");
    if (fault == NoFault)
        DPRINTF(TLB, "the result is nofault\n");
    else
        DPRINTF(TLB, "the result is fault for some reason\n");
    if (fault != NoFault)
    {
        DPRINTF(TLBVerbose3, "hit in l2 vaddr is %#x\n", vaddr);
    }
    return fault;
}
bool
TLB::checkPrePrecision(uint64_t &removeNoUsePre, uint64_t &usedPre)
{
    bool prePrecision = false;
    if ((removeNoUsePre + removeNoUsePre) > preHitOnHitLNum) {
        if ((((double)(removeNoUsePre + 1) / (removeNoUsePre + usedPre))) < preHitOnHitPrecision) {
            prePrecision = true;
        } else {
            prePrecision = false;
        }
        removeNoUsePre = 0;
        usedPre = 0;
    }
    return prePrecision;
}
void
TLB::sendPreHitOnHitRequest(TlbEntry *e_pre_1, TlbEntry *e_pre_2, const RequestPtr &req, Addr pre_block, uint16_t asid,
                            bool forward, int check_level, STATUS status, PrivilegeMode pmode, BaseMMU::Mode mode,
                            ThreadContext *tc, BaseMMU::Translation *translation)
{
    TlbEntry pre_entry;
    TlbEntry *e_pre;
    double pre_precision = 0;
    TLB *l2tlb;
    if (isStage2)
        l2tlb = this;
    else
        l2tlb = static_cast<TLB *>(nextLevel());
    assert(l2tlb != nullptr);
    pre_entry.vaddr = pre_block;
    pre_entry.asid = asid;
    pre_entry.logBytes = PageShift;
    pre_entry.used = false;
    if (forward) {
        req->setForwardPreVaddr(pre_block);
        l2tlb->insertForwardPre(pre_block, pre_entry);
        pre_precision = forwardPrePrecision;
    } else {
        req->setBackPreVaddr(pre_block);
        l2tlb->insertBackPre(pre_block, pre_entry);
        pre_precision = backPrePrecision;
    }

    if (e_pre_1)
        e_pre = e_pre_1;
    else
        e_pre = e_pre_2;
    Fault pre_fault = L2TLBCheck(e_pre->pte, check_level, status, pmode, pre_block, mode, req, forward, !forward);
    if ((pre_fault == NoFault) && (!hitInSp) && pre_precision) {
        DPRINTF(TLBGPre, "pre_vaddr %#x\n", pre_block);
        walker->start(e_pre->pte.ppn, tc, translation, req, mode, forward, !forward, check_level - 1, true,
                      e_pre->asid);
    }
}
std::pair<bool, Fault>
TLB::L2TLBSendRequest(Fault fault, TlbEntry *e_l2tlb, const RequestPtr &req, ThreadContext *tc,
                      BaseMMU::Translation *translation, BaseMMU::Mode mode, Addr vaddr, bool &delayed, int level)
{
    Addr paddr;
    if (hitInSp) {
        if (fault == NoFault) {
            paddr = e_l2tlb->paddr << PageShift | (vaddr & mask(e_l2tlb->logBytes));
            walker->doL2TLBHitSchedule(req, tc, translation, mode, paddr, *e_l2tlb);
            delayed = true;
            return std::make_pair(true, fault);
        }
    } else {
        fault = walker->start(e_l2tlb->pte.ppn, tc, translation, req, mode, false, false, level, true, e_l2tlb->asid);
        if (translation != nullptr || fault != NoFault) {
            delayed = true;
            return std::make_pair(true, fault);
        }
    }
    return std::make_pair(false, fault);
}


Fault
TLB::doTwoStageTranslate(const RequestPtr &req, ThreadContext *tc,
                 BaseMMU::Translation *translation, BaseMMU::Mode mode,
                 bool &delayed)
{
    Addr vaddr = Addr(sext<VADDR_BITS>(req->getVaddr()));
    SATP vsatp = tc->readMiscReg(MISCREG_VSATP);
    int virt = tc->readMiscReg(MISCREG_VIRMODE);
    STATUS status = tc->readMiscReg(MISCREG_STATUS);
    HSTATUS hstatus = tc->readMiscReg(MISCREG_HSTATUS);
    int two_stage_pmode = (int)getMemPriv(tc, mode);

    if (mode != BaseMMU::Execute) {
        if (status.mprv) {
            two_stage_pmode = status.mpp;
            virt = status.mpv && (two_stage_pmode != PrivilegeMode::PRV_M);
        }

        if (req->get_h_inst()) {
            virt = 1;
            two_stage_pmode = (PrivilegeMode)(RegVal)hstatus.spvp;
        }
    }
    if (virt != 0) {
        if (vsatp.mode == 0)
            assert(0);
    } else {
        assert(0);
    }
    req->setTwoStageState(true, virt, two_stage_pmode);
    Fault fault = walker->start(0, tc, translation, req, mode, false, false, 2, false, 0);
    if (translation != nullptr || fault != NoFault) {
        delayed = true;
        return fault;
    }
    return fault;
}
Fault
TLB::doTranslate(const RequestPtr &req, ThreadContext *tc,
                 BaseMMU::Translation *translation, BaseMMU::Mode mode,
                 bool &delayed)
{
    delayed = false;
    Addr vaddr = Addr(sext<VADDR_BITS>(req->getVaddr()));
    SATP satp = tc->readMiscReg(MISCREG_SATP);
    Addr vaddr_trace = (vaddr >> (PageShift + L2TLB_BLK_OFFSET)) << (PageShift + L2TLB_BLK_OFFSET);
    if (((vaddr_trace != lastVaddr) || (req->getPC() != lastPc)) &&
        is_dtlb) {
        traceFlag = true;
        lastVaddr = vaddr_trace;
        lastPc = req->getPC();
    } else {
        traceFlag = false;
    }

    TlbEntry *e[6] = {nullptr, nullptr, nullptr, nullptr, nullptr, nullptr};
    TlbEntry *forward_pre[6] = {nullptr, nullptr, nullptr, nullptr, nullptr, nullptr};
    TlbEntry *back_pre[6] = {nullptr, nullptr, nullptr, nullptr, nullptr, nullptr};
    e[0] = lookup(vaddr, satp.asid, mode, false, true);
    Addr paddr = 0;
    Fault fault = NoFault;
    Fault fault_return = NoFault;
    Fault forward_pre_fault;
    Fault back_pre_fault;
    STATUS status = tc->readMiscReg(MISCREG_STATUS);
    PrivilegeMode pmode = getMemPriv(tc, mode);

    TLB *l2tlb;
    if (isStage2)
        l2tlb = this;
    else
        l2tlb = static_cast<TLB *>(nextLevel());

    assert(l2tlb != nullptr);

    uint64_t remove_unused_forward_pre = l2tlb->removeNoUseForwardPre;
    uint64_t all_forward_pre_num = l2tlb->allForwardPre;
    uint64_t all_used_num = l2tlb->allUsed / l2tlbLineSize;
    uint64_t all_used_forward_pre_num = l2tlb->forwardUsedPre;
    auto precision = (double)(all_forward_pre_num - remove_unused_forward_pre) / (all_forward_pre_num + 1);

    auto recall = (double)all_used_forward_pre_num / (all_used_num + 1);
    RequestPtr pre_req = req;


    Addr forward_pre_vaddr = vaddr + (l2tlbLineSize << PageShift);
    Addr forward_pre_block = (forward_pre_vaddr >> (PageShift + L2TLB_BLK_OFFSET)) << (PageShift + L2TLB_BLK_OFFSET);
    Addr vaddr_block = (vaddr >> (PageShift + L2TLB_BLK_OFFSET)) << (PageShift + L2TLB_BLK_OFFSET);
    Addr back_pre_vaddr = vaddr - vaddr + (l2tlbLineSize << PageShift);
    Addr back_pre_block = (back_pre_vaddr >> (PageShift + L2TLB_BLK_OFFSET)) << (PageShift + L2TLB_BLK_OFFSET);

    l2tlb->lookupForwardPre(vaddr_block, satp.asid, false);
    TlbEntry *pre_forward = l2tlb->lookupForwardPre(forward_pre_block, satp.asid, true);

    l2tlb->lookupBackPre(vaddr_block, satp.asid, false);
    TlbEntry *pre_back = l2tlb->lookupBackPre(back_pre_block, satp.asid, true);
    backPrePrecision = checkPrePrecision(l2tlb->removeNoUseBackPre, l2tlb->usedBackPre);
    forwardPrePrecision = checkPrePrecision(l2tlb->removeNoUseForwardPre, l2tlb->forwardUsedPre);

    for (int i_e = 1; i_e < 6; i_e++) {
        if (!e[0])
            e[i_e] = l2tlb->lookupL2TLB(vaddr, satp.asid, mode, false, i_e, true);

        forward_pre[i_e] = l2tlb->lookupL2TLB(forward_pre_block, satp.asid, mode, true, i_e, true);
        back_pre[i_e] = l2tlb->lookupL2TLB(back_pre_block, satp.asid, mode, true, i_e, true);
    }
    bool return_flag = false;


    if (!e[0]) {  // look up l2tlb
        if (e[3]) {  // if hit in l3tlb
            DPRINTF(TLBVerbosel2, "hit in l2TLB l3\n");
            fault = L2TLBCheck(e[3]->pte, L2L3CheckLevel, status, pmode, vaddr, mode, req, false, false);
            if (hitInSp) {
                e[0] = e[3];
                if (fault == NoFault) {
                    paddr = e[0]->paddr << PageShift | (vaddr & mask(e[0]->logBytes));
                    DPRINTF(TLBVerbosel2, "vaddr %#x,paddr %#x,pc %#x\n", vaddr, paddr, req->getPC());
                    walker->doL2TLBHitSchedule(req, tc, translation, mode, paddr, *e[3]);
                    DPRINTF(TLBVerbosel2, "finish Schedule\n");
                    delayed = true;
                    if ((forward_pre_block != vaddr_block) && (!forward_pre[3]) && openForwardPre && (!pre_forward)) {
                        if (forward_pre[2] || forward_pre[5]) {
                            sendPreHitOnHitRequest(forward_pre[5], forward_pre[2], req, forward_pre_block, satp.asid,
                                                   true, L2L2CheckLevel, status, pmode, mode, tc, translation);
                        } else {
                            if (forward_pre[1] || forward_pre[4]) {
                                sendPreHitOnHitRequest(forward_pre[4], forward_pre[1], req, forward_pre_block,
                                                       satp.asid, true, L2L1CheckLevel, status, pmode, mode, tc,
                                                       translation);
                            }
                        }
                    }
                    if ((back_pre_block != vaddr_block) && (!back_pre[3]) && openBackPre && (!pre_back)) {
                        if (back_pre[2] || back_pre[5]) {
                            sendPreHitOnHitRequest(back_pre[5], back_pre[2], req, back_pre_block, satp.asid, false,
                                                   L2L2CheckLevel, status, pmode, mode, tc, translation);
                        }
                    }
                    if (traceFlag)
                        DPRINTF(TLBtrace, "tlb hit in vaddr %#x pc %#x\n", vaddr_trace, req->getPC());
                    return fault;
                }
            } else {
                panic("wrong in L2TLB\n");
            }

        } else if (e[5]) {  // hit in sp l2
            DPRINTF(TLBVerbosel2, "hit in l2 tlb l5\n");
            fault = L2TLBCheck(e[5]->pte, L2L2CheckLevel, status, pmode, vaddr, mode, req, false, false);
            if (hitInSp)
                e[0] = e[5];
            auto [return_flag, fault_return] =
                L2TLBSendRequest(fault, e[5], req, tc, translation, mode, vaddr, delayed, 0);
            if (return_flag)
                return fault_return;
        } else if (e[4]) {  // hit in sp l1
            DPRINTF(TLBVerbosel2, "hit in l2 tlb l4\n");
            fault = L2TLBCheck(e[4]->pte, L2L1CheckLevel, status, pmode, vaddr, mode, req, false, false);
            if (hitInSp)
                e[0] = e[4];
            auto [return_flag, fault_return] =
                L2TLBSendRequest(fault, e[4], req, tc, translation, mode, vaddr, delayed, 1);
            if (return_flag)
                return fault_return;
        } else if (e[2]) {
            DPRINTF(TLBVerbosel2, "hit in l2 tlb l2\n");
            fault = L2TLBCheck(e[2]->pte, L2L2CheckLevel, status, pmode, vaddr, mode, req, false, false);
            if (hitInSp)
                e[0] = e[2];
            auto [return_flag, fault_return] =
                L2TLBSendRequest(fault, e[2], req, tc, translation, mode, vaddr, delayed, 0);
            if (return_flag)
                return fault_return;
        } else if (e[1]) {
            DPRINTF(TLBVerbosel2, "hit in l2 tlb l1\n");
            fault = L2TLBCheck(e[1]->pte, L2L1CheckLevel, status, pmode, vaddr, mode, req, false, false);
            if (hitInSp)
                e[0] = e[1];
            auto [return_flag, fault_return] =
                L2TLBSendRequest(fault, e[1], req, tc, translation, mode, vaddr, delayed, 1);
            if (return_flag)
                return fault_return;
        } else {
            DPRINTF(TLB, "miss in l1 tlb + l2 tlb\n");
            DPRINTF(TLBGPre, "pre_req %d vaddr %#x req_vaddr %#x pc %#x\n", req->get_forward_pre_tlb(), vaddr,
                    req->getVaddr(), req->getPC());

            if (traceFlag)
                DPRINTF(TLBtrace, "tlb miss vaddr %#x pc %#x\n", vaddr_trace, req->getPC());
            fault = walker->start(0, tc, translation, req, mode, false, false, 2, false, 0);
            DPRINTF(TLB, "finish start\n");
            if (translation != nullptr || fault != NoFault) {
                // This gets ignored in atomic mode.
                delayed = true;
                return fault;
            }
            e[0] = lookup(vaddr, satp.asid, mode, false, true);
            assert(e[0] != nullptr);
        }
    }
    if (!e[0])
        e[0] = lookup(vaddr, satp.asid, mode, false, true);
    assert(e[0] != nullptr);

    status = tc->readMiscReg(MISCREG_STATUS);
    pmode = getMemPriv(tc, mode);
    if (mode == BaseMMU::Write && !e[0]->pte.d) {
        fault = createPagefault(vaddr, 0, mode, false);
    }

    if (fault == NoFault) {
        DPRINTF(TLB, "final checkpermission\n");
        DPRINTF(TLB, "translate(vpn=%#x, asid=%#x): %#x pc %#x mode %i pte.d %\n", vaddr, satp.asid, paddr,
                req->getPC(), mode, e[0]->pte.d);
        fault = checkPermissions(status, pmode, vaddr, mode, e[0]->pte);
    }


    if (fault != NoFault) {
        // if we want to write and it isn't writable, do a page table walk
        // again to update the dirty flag.
        //change update a/d not need to do a pagetable walker
        DPRINTF(TLB, "raise pf pc%#x vaddr %#x\n", req->getPC(), vaddr);
        DPRINTF(TLBVerbose3, "mode %i pte.d %d pte.w %d pte.r %d pte.x %d pte.u %d\n", mode, e[0]->pte.d, e[0]->pte.w,
                e[0]->pte.r, e[0]->pte.x, e[0]->pte.u);
        DPRINTF(TLBVerbose3, "paddr %#x ppn %#x\n", e[0]->paddr, e[0]->pte.ppn);
        if (traceFlag)
            DPRINTF(TLBtrace, "tlb hit in l1 but pf vaddr %#x,pc%#x\n", vaddr_trace, req->getPC());
        return fault;
    }
    assert(e[0] != nullptr);
    paddr = e[0]->paddr << PageShift | (vaddr & mask(e[0]->logBytes));

    DPRINTF(TLBVerbosel2, "translate(vpn=%#x, asid=%#x): %#x pc%#x\n", vaddr,
            satp.asid, paddr, req->getPC());
    req->setPaddr(paddr);

    if (e[0]) {
        // same block
        if (traceFlag)
            DPRINTF(TLBtrace, "tlb hit in l1 vaddr %#x,pc%#x\n", vaddr_trace,
                    req->getPC());
        if ((forward_pre_block != vaddr_block) && (!forward_pre[3]) && openForwardPre && (!pre_forward)) {
            if (forward_pre[2] || forward_pre[5]) {
                sendPreHitOnHitRequest(forward_pre[5], forward_pre[2], req, forward_pre_block, satp.asid, true,
                                       L2L2CheckLevel, status, pmode, mode, tc, translation);
            } else {
                if (forward_pre[4] || forward_pre[1]) {
                    sendPreHitOnHitRequest(forward_pre[4], forward_pre[1], req, forward_pre_block, satp.asid, true,
                                           L2L1CheckLevel, status, pmode, mode, tc, translation);
                }
            }
        }
        if ((back_pre_block != vaddr_block) && (!back_pre[3]) && openBackPre && (!pre_back)) {
            if (back_pre[2] || back_pre[5]) {
                sendPreHitOnHitRequest(back_pre[5], back_pre[2], req, back_pre_block, satp.asid, false, L2L2CheckLevel,
                                       status, pmode, mode, tc, translation);
            }
        }
    }

    return NoFault;
}

PrivilegeMode
TLB::getMemPriv(ThreadContext *tc, BaseMMU::Mode mode)
{
    STATUS status = (STATUS)tc->readMiscReg(MISCREG_STATUS);
    PrivilegeMode pmode = (PrivilegeMode)tc->readMiscReg(MISCREG_PRV);
    if (mode != BaseMMU::Execute && status.mprv == 1)
        pmode = (PrivilegeMode)(RegVal)status.mpp;
    return pmode;
}
bool
TLB::hasTwoStageTranslation(ThreadContext *tc, const RequestPtr &req, BaseMMU::Mode mode)
{
    STATUS status = (STATUS)tc->readMiscReg(MISCREG_STATUS);
    int v_mode = tc->readMiscReg(MISCREG_VIRMODE);
    return (req->get_h_inst()) || (status.mprv && status.mpv) || v_mode;
}

MMUMode
TLB::isaMMUCheck(ThreadContext *tc, Addr vaddr, BaseMMU::Mode mode)
{
    STATUS status = tc->readMiscReg(MISCREG_STATUS);
    PrivilegeMode pp = (PrivilegeMode)tc->readMiscReg(MISCREG_PRV);
    SATP satp = tc->readMiscReg(MISCREG_SATP);
    SATP vsatp = tc->readMiscReg(MISCREG_VSATP);
    int v_mode = tc->readMiscReg(MISCREG_VIRMODE);
    HGATP hgatp = tc->readMiscReg(MISCREG_HGATP);
    bool vm_enable = (status.mprv && (mode == BaseMMU::Execute) ? status.mpp : pp) < PRV_M &&
                     (satp.mode == 8 || (v_mode && (vsatp.mode == 8 || hgatp.mode == 8)));
    Addr vaMask = ((((Addr)1) << (63 - 38 + 1)) - 1);
    Addr vaMsbs = vaddr >> 38;
    bool vaMsbsOk = (vaMsbs == vaMask) || vaMsbs == 0 || !vm_enable;
    bool gpf = false;
    if ((v_mode == 1) && (vsatp.mode == 0)) {
        Addr maxgpa = ((((Addr)1) << (41)) - 1);
        if ((vaddr & ~maxgpa) == 0) {
            vaMsbsOk = 1;
        } else {
            gpf = true;
        }
    }
    if (!vaMsbsOk)
        assert(0);
    return MMU_DIRECT;
}

Fault
TLB::translate(const RequestPtr &req, ThreadContext *tc,
               BaseMMU::Translation *translation, BaseMMU::Mode mode,
               bool &delayed)
{
    delayed = false;

    if (FullSystem) {
        PrivilegeMode pmode = getMemPriv(tc, mode);
        SATP satp = tc->readMiscReg(MISCREG_SATP);
        SATP vsatp = tc->readMiscReg(MISCREG_VSATP);
        HGATP hgatp = tc->readMiscReg(MISCREG_HGATP);
        int v_mode = tc->readMiscReg(MISCREG_VIRMODE);
        bool two_stage_translation = false;

        if ((pmode == PrivilegeMode::PRV_M || satp.mode == AddrXlateMode::BARE))
            req->setFlags(Request::PHYSICAL);

        Fault fault;
        if (req->getFlags() & Request::PHYSICAL) {
            req->setTwoStageState(false, 0, 0);
            /**
             * we simply set the virtual address to physical address
             */
            req->setPaddr(req->getVaddr());
            fault = NoFault;
            assert(!req->get_h_inst());
        } else {
            two_stage_translation = hasTwoStageTranslation(tc, req, mode);
            if (two_stage_translation) {
                if (vsatp.mode != 8 && hgatp.mode != 8)
                    assert(0);
                fault = doTwoStageTranslate(req, tc, translation, mode, delayed);
            } else {
                req->setTwoStageState(false, 0, 0);
                fault = doTranslate(req, tc, translation, mode, delayed);
            }
        }

        // according to the RISC-V tests, negative physical addresses trigger
        // an illegal address exception.
        // TODO where is that written in the manual?
        if (!delayed && fault == NoFault && bits(req->getPaddr(), 63)) {
            ExceptionCode code;
            if (mode == BaseMMU::Read)
                code = ExceptionCode::LOAD_ACCESS;
            else if (mode == BaseMMU::Write) {
                code = ExceptionCode::STORE_ACCESS;
            }
            else
                code = ExceptionCode::INST_ACCESS;
            fault = std::make_shared<AddressFault>(req->getVaddr(), 0, code);
        }

        if (!delayed && fault == NoFault) {
            pma->check(req);

            // do pmp check if any checking condition is met.
            // mainFault will be NoFault if pmp checks are
            // passed, otherwise an address fault will be returned.
            fault = pmp->pmpCheck(req, mode, pmode, tc);
        }

        return fault;
    } else {
        // In the O3 CPU model, sometimes a memory access will be speculatively
        // executed along a branch that will end up not being taken where the
        // address is invalid.  In that case, return a fault rather than trying
        // to translate it (which will cause a panic).  Since RISC-V allows
        // unaligned memory accesses, this should only happen if the request's
        // length is long enough to wrap around from the end of the memory to
        // the start.
        assert(req->getSize() > 0);
        if (req->getVaddr() + req->getSize() - 1 < req->getVaddr())
            return std::make_shared<GenericPageTableFault>(req->getVaddr());

        Process * p = tc->getProcessPtr();

        Fault fault = p->pTable->translate(req);
        if (fault != NoFault)
            return fault;

        return NoFault;
    }
}

Fault
TLB::translateAtomic(const RequestPtr &req, ThreadContext *tc,
                     BaseMMU::Mode mode)
{
    bool delayed;
    return translate(req, tc, nullptr, mode, delayed);
}

void
TLB::translateTiming(const RequestPtr &req, ThreadContext *tc,
                     BaseMMU::Translation *translation, BaseMMU::Mode mode)
{
    bool delayed;
    assert(translation);
    Fault fault = translate(req, tc, translation, mode, delayed);
    if (!delayed){
        translation->finish(fault, req, tc, mode);
    }
    else
        translation->markDelayed();
}

Fault
TLB::translateFunctional(const RequestPtr &req, ThreadContext *tc,
                         BaseMMU::Mode mode)
{
    const Addr vaddr = req->getVaddr();
    Addr paddr = vaddr;

    if (FullSystem) {
        MMU *mmu = static_cast<MMU *>(tc->getMMUPtr());

        PrivilegeMode pmode = mmu->getMemPriv(tc, mode);
        SATP satp = tc->readMiscReg(MISCREG_SATP);
        if (pmode != PrivilegeMode::PRV_M &&
            satp.mode != AddrXlateMode::BARE) {
            Walker *walker = mmu->getDataWalker();
            unsigned logBytes;
            Fault fault = walker->startFunctional(
                    tc, paddr, logBytes, mode);
            if (fault != NoFault)
                return fault;

            Addr masked_addr = vaddr & mask(logBytes);
            paddr |= masked_addr;
        }
    }
    else {
        Process *process = tc->getProcessPtr();
        const auto *pte = process->pTable->lookup(vaddr);

        if (!pte && mode != BaseMMU::Execute) {
            // Check if we just need to grow the stack.
            if (process->fixupFault(vaddr)) {
                // If we did, lookup the entry for the new page.
                pte = process->pTable->lookup(vaddr);
            }
        }

        if (!pte)
            return std::make_shared<GenericPageTableFault>(req->getVaddr());

        paddr = pte->paddr | process->pTable->pageOffset(vaddr);
    }

    DPRINTF(TLB, "Translated (functional) %#x -> %#x.\n", vaddr, paddr);
    req->setPaddr(paddr);
    return NoFault;
}

Fault
TLB::finalizePhysical(const RequestPtr &req,
                      ThreadContext *tc, BaseMMU::Mode mode) const
{
    return NoFault;
}

void
TLB::serialize(CheckpointOut &cp) const
{
    // Only store the entries in use.
    printf("serialize\n");
    uint32_t _size = size - freeList.size();
    SERIALIZE_SCALAR(_size);
    SERIALIZE_SCALAR(lruSeq);

    uint32_t _count = 0;
    for (uint32_t x = 0; x < size; x++) {
        if (tlb[x].trieHandle != nullptr)
            tlb[x].serializeSection(cp, csprintf("Entry%d", _count++));
    }
}

void
TLB::unserialize(CheckpointIn &cp)
{
    // Do not allow to restore with a smaller tlb.
    printf("unserialize\n");
    uint32_t _size;
    UNSERIALIZE_SCALAR(_size);
    if (_size > size) {
        fatal("TLB size less than the one in checkpoint!");
    }

    UNSERIALIZE_SCALAR(lruSeq);

    for (uint32_t x = 0; x < _size; x++) {
        TlbEntry *newEntry = freeList.front();
        freeList.pop_front();

        newEntry->unserializeSection(cp, csprintf("Entry%d", x));
        Addr key = buildKey(newEntry->vaddr, newEntry->asid);
        newEntry->trieHandle = trie.insert(key,
            TlbEntryTrie::MaxBits - newEntry->logBytes, newEntry);
    }
}

TLB::TlbStats::TlbStats(statistics::Group *parent)
    : statistics::Group(parent),
      ADD_STAT(readHits, statistics::units::Count::get(), "read hits"),
      ADD_STAT(readMisses, statistics::units::Count::get(), "read misses"),
      ADD_STAT(readAccesses, statistics::units::Count::get(), "read accesses"),
      ADD_STAT(writeHits, statistics::units::Count::get(), "write hits"),
      ADD_STAT(writeMisses, statistics::units::Count::get(), "write misses"),
      ADD_STAT(writeAccesses, statistics::units::Count::get(),
               "write accesses"),
      ADD_STAT(readprefetchHits, statistics::units::Count::get(),
               "read prefetch Hits"),
      ADD_STAT(writeprefetchHits, statistics::units::Count::get(),
               "write prefetch Hits"),
      ADD_STAT(readprefetchAccesses, statistics::units::Count::get(),
               "read prefetch Accesses"),
      ADD_STAT(writeprefetchAccesses, statistics::units::Count::get(),
               "write prefetch Accesses"),
      ADD_STAT(readprefetchMisses, statistics::units::Count::get(),
               "read prefetch Misses"),
      ADD_STAT(writeprefetchMisses, statistics::units::Count::get(),
               "write prefetch Misses"),
      ADD_STAT(writeHitsSquashed, statistics::units::Count::get(),
               "write squashed hits"),
      ADD_STAT(readHitsSquashed, statistics::units::Count::get(),
               "read squashed hits"),
      ADD_STAT(squashedInsert, statistics::units::Count::get(),
               "number of squashed pte insert"),
      ADD_STAT(ALLInsert, statistics::units::Count::get(),
               "number of all pte insert"),
      ADD_STAT(backHits, statistics::units::Count::get(),
               "number of backHitst"),
      ADD_STAT(usedBackPre, statistics::units::Count::get(),
               "number of used back pre"),
      ADD_STAT(removeNoUseBackPre, statistics::units::Count::get(),
               "number of unused back pre"),
      ADD_STAT(usedForwardPre, statistics::units::Count::get(),
               "number of used forward pre"),
      ADD_STAT(removeNoUseForwardPre, statistics::units::Count::get(),
               "number of unused forward pre"),
      ADD_STAT(writeL2l3TlbMisses, statistics::units::Count::get(),
               "write misses in l2tlb"),
      ADD_STAT(ReadL2l3TlbMisses, statistics::units::Count::get(),
               "read misses in l2tlb"),
      ADD_STAT(writeL2Tlbl3Hits, statistics::units::Count::get(),
               "write hits in l2tlb"),
      ADD_STAT(ReadL2Tlbl3Hits, statistics::units::Count::get(),
               "read hits in l2tlb"),
      ADD_STAT(squashedInsertL2, statistics::units::Count::get(),
               "number of l2 squashe pte insert"),
      ADD_STAT(ALLInsertL2, statistics::units::Count::get(),
               "number of all l2 pte insert"),
      ADD_STAT(writeL2l3TlbSquashedHits, statistics::units::Count::get(),
               "l2 write squashed hits"),
      ADD_STAT(ReadL2l3TlbSquashedHits, statistics::units::Count::get(),
               "l2 read squashed hits"),
      ADD_STAT(l1tlbRemove, statistics::units::Count::get(),
               "l1tlb remove num"),
      ADD_STAT(l1tlbUsedRemove, statistics::units::Count::get(),
               "l1tlb used remove"),
      ADD_STAT(l1tlbUnusedRemove, statistics::units::Count::get(),
               "l1tlb unused remove"),
      ADD_STAT(l2l1tlbRemove, statistics::units::Count::get(),
               "l2l1tlb remove"),
      ADD_STAT(l2l1tlbUsedRemove, statistics::units::Count::get(),
               "l2l1tlb used remove"),
      ADD_STAT(l2l1tlbUnusedRemove, statistics::units::Count::get(),
               "l2l1tlb unused remove"),
      ADD_STAT(l2l2tlbRemove, statistics::units::Count::get(),
               "l2l2tlb remove"),
      ADD_STAT(l2l2tlbUsedRemove, statistics::units::Count::get(),
               "l2l2tlb used remove"),
      ADD_STAT(l2l2tlbUnusedRemove, statistics::units::Count::get(),
               "l2l2tlb unused remove"),
      ADD_STAT(l2l3tlbRemove, statistics::units::Count::get(),
               "l2l3tlb remove"),
      ADD_STAT(l2l3tlbUsedRemove, statistics::units::Count::get(),
               "l2l3tlb used remove"),
      ADD_STAT(l2l3tlbUnusedRemove, statistics::units::Count::get(),
               "l2l3tlb unused remove"),
      ADD_STAT(l2sptlbRemove, statistics::units::Count::get(),
               "l2sptlb remove"),
      ADD_STAT(l2sptlbUsedRemove, statistics::units::Count::get(),
               "l2sptlb used remove"),
      ADD_STAT(l2sptlbUnusedRemove, statistics::units::Count::get(),
               "l2sptlb unused remove"),
      ADD_STAT(hitPreEntry, statistics::units::Count::get(),
               "number of pre entry hit"),
      ADD_STAT(hitPreNum, statistics::units::Count::get(),
               "number of pre hit times"),
      ADD_STAT(RemovePreUnused, statistics::units::Count::get(),
               "remove unused pre number"),
      ADD_STAT(AllPre, statistics::units::Count::get(), "all pre num"),
      ADD_STAT(hits, statistics::units::Count::get(),
               "Total TLB (read and write) hits", readHits + writeHits),
      ADD_STAT(misses, statistics::units::Count::get(),
               "Total TLB (read and write) misses", readMisses + writeMisses),
      ADD_STAT(accesses, statistics::units::Count::get(),
               "Total TLB (read and write) accesses",
               readAccesses + writeAccesses)
{
}

Port *
TLB::getTableWalkerPort()
{
    return &walker->getPort("port");
}

} // namespace gem5
