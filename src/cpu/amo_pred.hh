#ifndef __CPU_AMO_PRED_HH__
#define __CPU_AMO_PRED_HH__

#include <string>
#include <vector>

#include <base/statistics.hh>
#include <base/types.hh>

namespace gem5
{

class AMOPred
{


private:
    struct EntryInfo
    {
        Addr branch_pc;
        Addr amo_paddr;
        Cycles last_used_cycle;
        int confidence; // max 4

        int decreaseConfidence() {
            if (confidence > 0) {
                confidence--;
            }
            return confidence;
        }
        int increaseConfidence() {
            if (confidence < 4) {
                confidence++;
            }
            return confidence;
        }
        bool isZeroConfidence() { return confidence == 0;}
        void updateCycle(Cycles cycle) {
            last_used_cycle = cycle;
        }
    };

    Addr latest_branch_pc;
    Cycles last_branch_cycle;
    std::vector<EntryInfo> relationship_table;

    int entry_num;
    // int timeout_threshold;

    // struct AMOPredStats : public statistics::Group
    // {
    //     AMOPredStats(statistics::Group *parent);
    //     // Reasons for exiting
    //     // statistics::Scalar entry_timeout;
    //     statistics::Scalar entry_replaced_lowconf;
    //     statistics::Scalar entry_replaced_lru;
    //     // Hits
    //     statistics::Scalar branch_hit;
    //     statistics::Scalar hit_correct_addr;
    //     statistics::Scalar hit_wrong_addr;
    //     // statistics::Scalar miss;
    // } stats;

public:
    std::string name;

    AMOPred() {}
    AMOPred(std::string name, int entry_num)
    : entry_num(entry_num), name(name) {
    }

    ~AMOPred() {}

    std::pair<bool, Addr> tryPredict(Addr pc, Cycles cycle) {
        latest_branch_pc = pc;
        // if branch in relationship_cache
        for (auto i = relationship_table.begin(); i != relationship_table.end(); i++) {
            if (i->branch_pc == pc) {
                i->last_used_cycle = cycle;
                // stats.branch_hit++;
                return std::make_pair(true, i->amo_paddr);
            }
        }
        latest_branch_pc = pc;
        return std::make_pair(false, 0);
    }

    void updateConfidence(Addr amo_paddr, Cycles cycle) {
        // find in relationship table who's amo_paddr is amo_paddr
        std::vector<EntryInfo>::iterator entry_with_zero_confidence = relationship_table.end();
        std::vector<EntryInfo>::iterator oldest_entry = relationship_table.end();
        Cycles oldest_entry_cycle = cycle;
        for (auto i = relationship_table.begin(); i != relationship_table.end(); i++) {
            if (i->amo_paddr == amo_paddr) {
                i->updateCycle(cycle);
                i->increaseConfidence();
                // stats.hit_correct_addr++;
                return;
            // } else if (i->latest_branch_pc == branch_pc) {
            //     // Hit with wrong addr
            //     if (i->decreaseCondifdence() == 0) {
            //         i->amo_paddr = amo_paddr;
            //     }
            //     stats.hit_wrong_addr++;
            }
            // TODO deal with one pc multiple paddr
            if (i->isZeroConfidence()) {
                entry_with_zero_confidence = i;
            }
            if (i->last_used_cycle < oldest_entry_cycle) {
                oldest_entry = i;
                oldest_entry_cycle = i->last_used_cycle;
            }
        }

        // Not found
        // First add entry if table not full
        if (relationship_table.size() < entry_num) {
            relationship_table.emplace_back(
                EntryInfo{latest_branch_pc, amo_paddr, cycle, 0}
            );
            return;
        }

        // Then try evict entry with 0 conficence
        if (entry_with_zero_confidence != relationship_table.end()) {
            relationship_table.erase(entry_with_zero_confidence);
            // stats.entry_replaced_lowconf++;
            relationship_table.emplace_back(
                EntryInfo{latest_branch_pc, amo_paddr, cycle, 0}
            );
            return;
        }
        // Lastly evict oldest entry
        assert(oldest_entry != relationship_table.end());
        relationship_table.erase(oldest_entry);
        // stats.entry_replaced_lru++;
        relationship_table.emplace_back(
            EntryInfo{latest_branch_pc, amo_paddr, cycle, 0}
        );
    }
};
}

#endif // __CPU_AMO_PRED_HH__
