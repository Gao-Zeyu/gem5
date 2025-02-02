/*
 * Copyright (c) 2017-2018 ARM Limited
 * All rights reserved
 *
 * The license below extends only to copyright in the software and shall
 * not be construed as granting a license to any other intellectual
 * property including but not limited to intellectual property relating
 * to a hardware implementation of the functionality of the software
 * licensed hereunder.  You may use the software subject to the license
 * terms below provided that you ensure that this notice is replicated
 * unmodified and in its entirety in all distributions of the software,
 * modified or unmodified, in source code or in binary form.
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

#ifndef __CPU_UTILS_HH__
#define __CPU_UTILS_HH__

#include "base/types.hh"

namespace gem5
{

/**
 * Calculates the offset of a given address wrt aligned fixed-size blocks.
 * @param addr Input address.
 * @param block_size Block size in bytes.
 * @return Offset of the given address in bytes.
 */
inline Addr
addrBlockOffset(Addr addr, Addr block_size)
{
    return addr & (block_size - 1);
}

/**
 * Returns the address of the closest aligned fixed-size block to the given
 * address.
 * @param addr Input address.
 * @param block_size Block size in bytes.
 * @return Address of the closest aligned block.
 */
inline Addr
addrBlockAlign(Addr addr, Addr block_size)
{
    return addr & ~(block_size - 1);
}

/**
 * Returns true if the given memory access (address, size) needs to be
 * fragmented across aligned fixed-size blocks.
 * @param addr Address of the memory access.
 * @param size Size of the memory access.
 * @param block_size Block size in bytes.
 * @return True if the memory access needs to be fragmented.
 */
inline bool
transferNeedsBurst(Addr addr, unsigned int size, unsigned int block_size)
{
    return (addrBlockOffset(addr, block_size) + size) > block_size;
}

/**
 * Test if there is any active element in an enablement range.
 */
inline bool
isAnyActiveElement(const std::vector<bool>::const_iterator& it_start,
                   const std::vector<bool>::const_iterator& it_end)
{
    auto it_tmp = it_start;
    for (;it_tmp != it_end && !(*it_tmp); ++it_tmp);
    return (it_tmp != it_end);
}

inline std::string
goldenDiffStr(uint8_t *dut_ptr, uint8_t* golden_ptr, size_t size) {
    assert(size <= 8);
    uint64_t dut_value = 0;
    uint64_t golden_value = 0;
    memcpy(&dut_value, dut_ptr, size);
    memcpy(&golden_value, golden_ptr, size);
    std::stringstream ss;
    ss << std::hex << "Dut value: " << dut_value << " , golden value: " << golden_value << " ";
    return ss.str();
}

} // namespace gem5

#endif // __CPU_UTILS_HH__
