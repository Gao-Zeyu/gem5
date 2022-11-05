/**
 * @file
 * Describes a fetch directed instruction prefetcher.
 */

#ifndef __MEM_CACHE_PREFETCH_FDIP_HH__
#define __MEM_CACHE_PREFETCH_FDIP_HH__

#include "mem/cache/prefetch/queued.hh"
#include "mem/packet.hh"

namespace gem5
{

struct FDIPParams;

GEM5_DEPRECATED_NAMESPACE(Prefetcher, prefetch);
namespace prefetch
{

class FDIP : public Queued
{
  public:
    struct StreamEntry
    {
        bool valid;
        Addr start;
        Addr end;
        FetchStreamId streamId;
    };
    FDIP(const FDIPParams &p);
    ~FDIP() = default;

    void calculatePrefetch(const PrefetchInfo &pfi,
                           std::vector<AddrPriority> &addresses) override;

    void getStreamId(FetchStreamId &streamId) override;

    void addStream(Addr stream_start_pc, Addr stream_end_pc,
                    FetchStreamId stream_id);

    void squash(FetchStreamId streamId);

    StreamEntry streamToPrefetch;
};

} // namespace prefetch
} // namespace gem5

#endif // __MEM_CACHE_PREFETCH_FDIP_HH__
