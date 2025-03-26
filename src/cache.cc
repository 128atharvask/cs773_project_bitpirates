#include "cache.h"
#include "set.h"
#include "ooo_cpu.h"
#include "uncore.h"

#include<vector>

#include<iterator>

uint64_t l2pf_access = 0;
uint8_t L2C_BYPASS_KNOB = 0;    //Neelu: Set to 1: Bypass Instructions 2: Bypass Data 3: Bypass All

//#define PUSH_PREFETCHES_FROM_L2_TO_L1	//Neelu: Adding to L1 PQ after filling prefetch in L2

//#define CHECK_DATA_HIT_ON_STLB_HIT	//Neelu: Adding to check where the corresponding data is present in case of an STLB hit

//#define STLB_HINT_TO_L2_PREF

//#define NOTIFY_L1D_OF_DTLB_EVICTION

#define PREF_CLASS_MASK 0xF00 //0x1E000	//Neelu: IPCP pref class
#define NUM_OF_STRIDE_BITS 8 //13	//Neelu: IPCP stride

//Neelu: For Ideal Spatial Prefetcher
#define IDEAL_SPATIAL_REGIONS 64
vector <uint64_t> regions_accessed, total_regions;                             //Neelu: regions accessed for ideal spatial prefetcher
#define LOG2_SPATIAL_REGION_SIZE 11                             //Neelu: For 2 KB region size

//Neelu: Not sending translation requests to STLB for L1D same page prefetch requests
//#define NO_TRANSLATION_PENALTY_FOR_PREFETCHES


ostream& operator<<(ostream& os, const PACKET &packet)
{
    return os << " cpu: " << packet.cpu << " instr_id: " << packet.instr_id << " Translated: " << +packet.translated << " address: " << hex << packet.address << " full_addr: " << packet.full_addr << dec << " full_virtual_address: " << hex << packet.full_virtual_address << " full_physical_address: " << packet.full_physical_address << dec << "Type: " << +packet.type << " event_cycle: " << packet.event_cycle <<  " current_core_cycle: " <<  current_core_cycle[packet.cpu] << endl;
};

void CACHE::handle_fill()
{
    // handle fill
    uint32_t fill_cpu = (MSHR.next_fill_index == MSHR_SIZE) ? NUM_CPUS : MSHR.entry[MSHR.next_fill_index].cpu;
    if (fill_cpu == NUM_CPUS)
        return;

    if (MSHR.next_fill_cycle <= current_core_cycle[fill_cpu]) {

#ifdef SANITY_CHECK
        if (MSHR.next_fill_index >= MSHR.SIZE)
            assert(0);
#endif

        uint32_t mshr_index = MSHR.next_fill_index;

        // Get candidate sets for PhantomCache
        uint64_t candidate_sets[8];
        uint32_t num_candidates = 0;
#ifdef PHANTOMCACHE
        num_candidates = get_candidate_sets(MSHR.entry[mshr_index].address, candidate_sets);
#endif

        // Find victim
        uint32_t set, way;
#ifdef PHANTOMCACHE
        // Try each candidate set until we find a victim
        for (uint32_t i = 0; i < num_candidates; i++) {
            set = candidate_sets[i];
            way = (this->*find_victim)(fill_cpu, MSHR.entry[mshr_index].instr_id, set, block[set], 
                                     MSHR.entry[mshr_index].ip, MSHR.entry[mshr_index].full_addr, 
                                     MSHR.entry[mshr_index].type);
            if (way != NUM_WAY)  // Found a victim
                break;
        }
#else
        set = get_set(MSHR.entry[mshr_index].address);
        way = (this->*find_victim)(fill_cpu, MSHR.entry[mshr_index].instr_id, set, block[set], 
                                 MSHR.entry[mshr_index].ip, MSHR.entry[mshr_index].full_addr, 
                                 MSHR.entry[mshr_index].type);
#endif

        // fill the cache line
        if (way != NUM_WAY) {
            fill_cache(set, way, &MSHR.entry[mshr_index]);
            MSHR.num_returned++;
            MSHR.entry[mshr_index].returned = COMPLETED;

            // ADD LATENCY
            if (MSHR.entry[mshr_index].event_cycle < current_core_cycle[fill_cpu])
                MSHR.entry[mshr_index].event_cycle = current_core_cycle[fill_cpu] + LATENCY;
            else
                MSHR.entry[mshr_index].event_cycle += LATENCY;

            update_fill_cycle();

            DP (if (warmup_complete[fill_cpu]) {
                    cout << "[" << NAME << "_MSHR] " <<  __func__ << " instr_id: " << MSHR.entry[mshr_index].instr_id;
                    cout << " address: " << hex << MSHR.entry[mshr_index].address;
                    cout << " full_addr: " << MSHR.entry[mshr_index].full_addr;
                    cout << " data: " << MSHR.entry[mshr_index].data << dec;
                    cout << " num_returned: " << MSHR.num_returned;
                    cout << " index: " << mshr_index << " occupancy: " << MSHR.occupancy;
                    cout << " event: " << MSHR.entry[mshr_index].event_cycle;
                    cout << " current: " << current_core_cycle[fill_cpu] << " next: " << MSHR.next_fill_cycle << endl; });
        }
    }
}

void CACHE::handle_writeback()
{

    if(WQ.occupancy == 0)
        return;

    multimap<uint64_t, uint32_t> writes_ready; //{cycle_time,index}

assert(cache_type != IS_L1I || cache_type != IS_STLB); //@Vishal: TLB should not generate write packets

if(cache_type == IS_L1D) //Get completed index in WQ, as it is non-fifo
{
    for (uint32_t wq_index=0; wq_index < WQ.SIZE; wq_index++)
        if(WQ.entry[wq_index].translated == COMPLETED && (WQ.entry[wq_index].event_cycle <= current_core_cycle[cpu])) 
            writes_ready.insert({WQ.entry[wq_index].event_cycle, wq_index});
}
auto writes_ready_it = writes_ready.begin();

if(cache_type == IS_L1D && writes_ready.size() == 0)
    return;

if(cache_type == IS_L1D)
    WQ.head = writes_ready_it->second; //@Vishal: L1 WQ is non fifo, so head variable is set to next index to be read	

    // handle write
    uint32_t writeback_cpu = WQ.entry[WQ.head].cpu;
if (writeback_cpu == NUM_CPUS)
    return;


    // handle the oldest entry
    if ((WQ.entry[WQ.head].event_cycle <= current_core_cycle[writeback_cpu]) && (WQ.occupancy > 0)) {
        int index = WQ.head;

        // access cache
        uint32_t set = get_set(WQ.entry[index].address);
        int way = check_hit(&WQ.entry[index]);

        //Neelu: For Ideal Critical IP Prefetcher
        /*if(cache_type == IS_L1D)
          {
        //Marking read as hit if critical ip flag is set.
        if(WQ.entry[index].critical_ip_flag)
        way = 0;
        }*/


        //Addition by Neelu: For Ideal Spatial Prefetcher
        /*	if(cache_type == IS_L1D)
            {
            int found_region = 0;
            assert(WQ.entry[index].address != 0);
            for(int temp_index = 0; temp_index < regions_accessed.size(); temp_index++)
            {
            if(regions_accessed[temp_index] == (WQ.entry[index].address >> LOG2_SPATIAL_REGION_SIZE))
            {
            found_region = 1;
            way = 0;
            break; 
            }
            }
            if(found_region == 0)
            {       
            total_regions.push_back(WQ.entry[index].address >> LOG2_SPATIAL_REGION_SIZE);
            unique_region_count = total_regions.size();
            regions_accessed.push_back(WQ.entry[index].address >> LOG2_SPATIAL_REGION_SIZE);
            if(regions_accessed.size() > IDEAL_SPATIAL_REGIONS)
            {
            regions_accessed.erase(regions_accessed.begin());       
            region_conflicts++;
            }

        //assert(way < 0);			

        }
        }*/

#ifdef PERFECT_L1D
        if(cache_type==IS_L1D)
            way = 0 ;	//Perfect L1D
#endif

#ifdef PERFECT_L2C_DATA
        if(cache_type == IS_L2C && (WQ.entry[index].type != PREFETCH_TRANSLATION) && (WQ.entry[index].instruction == 0) && (WQ.entry[index].type != LOAD_TRANSLATION) && (WQ.entry[index].type != PREFETCH_TRANSLATION) && (WQ.entry[index].type != TRANSLATION_FROM_L1D))
            way = 0;
#endif 

        if (way >= 0) { // writeback hit (or RFO hit for L1D)

            (this->*update_replacement_state)(writeback_cpu, set, way, block[set][way].full_addr, WQ.entry[index].ip, 0, WQ.entry[index].type, 1);

            // COLLECT STATS
            sim_hit[writeback_cpu][WQ.entry[index].type]++;
            sim_access[writeback_cpu][WQ.entry[index].type]++;

            // mark dirty
            block[set][way].dirty = 1;

            if (cache_type == IS_ITLB)
                WQ.entry[index].instruction_pa = block[set][way].data;
            else if (cache_type == IS_DTLB)
                WQ.entry[index].data_pa = block[set][way].data;

            WQ.entry[index].data = block[set][way].data;

            // check fill level
            if (WQ.entry[index].fill_level < fill_level) {
                if(fill_level == FILL_L2)
                {
                    if(WQ.entry[index].fill_l1i)
                    {
                        upper_level_icache[writeback_cpu]->return_data(&WQ.entry[index]);
                    }
                    if(WQ.entry[index].fill_l1d)
                    {
                        upper_level_dcache[writeback_cpu]->return_data(&WQ.entry[index]);
                    }
                }
                else
                {
                    if (WQ.entry[index].instruction)
                        upper_level_icache[writeback_cpu]->return_data(&WQ.entry[index]);
                    if (WQ.entry[index].is_data)
                        upper_level_dcache[writeback_cpu]->return_data(&WQ.entry[index]);
                }

            }

            HIT[WQ.entry[index].type]++;
            ACCESS[WQ.entry[index].type]++;

            // remove this entry from WQ
            WQ.remove_queue(&WQ.entry[index]);
        }
        else { // writeback miss (or RFO miss for L1D)

            DP ( if (warmup_complete[writeback_cpu]) {
                    cout << "[" << NAME << "] " << __func__ << " type: " << +WQ.entry[index].type << " miss";
                    cout << " instr_id: " << WQ.entry[index].instr_id << " address: " << hex << WQ.entry[index].address;
                    cout << " full_addr: " << WQ.entry[index].full_addr << dec;
                    cout << " cycle: " << WQ.entry[index].event_cycle << endl; });

            if (cache_type == IS_L1D) { // RFO miss

                // check mshr
                uint8_t miss_handled = 1;
                int mshr_index = check_nonfifo_queue(&MSHR, &WQ.entry[index],false); //@Vishal: Updated from check_mshr

                if(mshr_index == -2)
                {
                    // this is a data/instruction collision in the MSHR, so we have to wait before we can allocate this miss
                    miss_handled = 0;
                }

                if ((mshr_index == -1) && (MSHR.occupancy < MSHR_SIZE)) { // this is a new miss

                    assert(WQ.entry[index].full_physical_address != 0);
                    PACKET new_packet = WQ.entry[index];
                    //@Vishal: Send physical address to lower level and track physical address in MSHR  
                    new_packet.address = WQ.entry[index].full_physical_address >> LOG2_BLOCK_SIZE;
                    new_packet.full_addr = WQ.entry[index].full_physical_address; 


                    // add it to mshr (RFO miss)
                    add_nonfifo_queue(&MSHR, &new_packet); //@Vishal: Updated from add_mshr

                    // add it to the next level's read queue
                    //if (lower_level) // L1D always has a lower level cache
                    lower_level->add_rq(&new_packet);
                }
                else {
                    if ((mshr_index == -1) && (MSHR.occupancy == MSHR_SIZE)) { // not enough MSHR resource

                        // cannot handle miss request until one of MSHRs is available
                        miss_handled = 0;
                        STALL[WQ.entry[index].type]++;
                    }
                    else if (mshr_index != -1) { // already in-flight miss

                        // update fill_level
                        if (WQ.entry[index].fill_level < MSHR.entry[mshr_index].fill_level)
                            MSHR.entry[mshr_index].fill_level = WQ.entry[index].fill_level;

                        if((WQ.entry[index].fill_l1i) && (MSHR.entry[mshr_index].fill_l1i != 1))
                        {
                            MSHR.entry[mshr_index].fill_l1i = 1;
                        }
                        if((WQ.entry[index].fill_l1d) && (MSHR.entry[mshr_index].fill_l1d != 1))
                        {
                            MSHR.entry[mshr_index].fill_l1d = 1;
                        }

                        // update request
                        if (MSHR.entry[mshr_index].type == PREFETCH) {
                            uint8_t  prior_returned = MSHR.entry[mshr_index].returned;
                            uint64_t prior_event_cycle = MSHR.entry[mshr_index].event_cycle;

                            uint64_t prior_address = MSHR.entry[mshr_index].address;
                            uint64_t prior_full_addr = MSHR.entry[mshr_index].full_addr;
                            uint64_t prior_full_physical_address = MSHR.entry[mshr_index].full_physical_address;


                            MSHR.entry[mshr_index] = WQ.entry[index];


                            //@Vishal: L1 RQ has virtual address, but miss needs to track physical address, so prior addresses are kept
                            if(cache_type == IS_L1D)
                            {
                                MSHR.entry[mshr_index].address = prior_address;
                                MSHR.entry[mshr_index].full_addr = prior_full_addr;
                                MSHR.entry[mshr_index].full_physical_address = prior_full_physical_address;
                            }

                            // in case request is already returned, we should keep event_cycle and retunred variables
                            MSHR.entry[mshr_index].returned = prior_returned;
                            MSHR.entry[mshr_index].event_cycle = prior_event_cycle;
                        }

                        MSHR_MERGED[WQ.entry[index].type]++;

                        DP ( if (warmup_complete[writeback_cpu]) {
                                cout << "[" << NAME << "] " << __func__ << " mshr merged";
                                cout << " instr_id: " << WQ.entry[index].instr_id << " prior_id: " << MSHR.entry[mshr_index].instr_id; 
                                cout << " address: " << hex << WQ.entry[index].address;
                                cout << " full_addr: " << WQ.entry[index].full_addr << dec;
                                cout << " cycle: " << WQ.entry[index].event_cycle << endl; });
                    }
                    else { // WE SHOULD NOT REACH HERE
                        cerr << "[" << NAME << "] MSHR errors" << endl;
                        assert(0);
                    }
                }

                if (miss_handled) {

                    MISS[WQ.entry[index].type]++;
                    ACCESS[WQ.entry[index].type]++;

                    // remove this entry from WQ
                    WQ.remove_queue(&WQ.entry[index]);
                }

            }
            else {
                // find victim
                uint32_t set = get_set(WQ.entry[index].address), way;
                way = (this->*find_victim)(writeback_cpu, WQ.entry[index].instr_id, set, block[set], WQ.entry[index].ip, WQ.entry[index].full_addr, WQ.entry[index].type);

#ifdef LLC_BYPASS
                if ((cache_type == IS_LLC) && (way == LLC_WAY)) {
                    cerr << "LLC bypassing for writebacks is not allowed!" << endl;
                    assert(0);
                }
#endif

                uint8_t  do_fill = 1;

                // is this dirty?
                if (block[set][way].dirty) {

                    // check if the lower level WQ has enough room to keep this writeback request
                    if (lower_level) { 
                        if (lower_level->get_occupancy(2, block[set][way].address) == lower_level->get_size(2, block[set][way].address)) {

                            // lower level WQ is full, cannot replace this victim
                            do_fill = 0;
                            lower_level->increment_WQ_FULL(block[set][way].address);
                            STALL[WQ.entry[index].type]++;

                            DP ( if (warmup_complete[writeback_cpu] ) {
                                    cout << "[" << NAME << "] " << __func__ << "do_fill: " << +do_fill;
                                    cout << " lower level wq is full!" << " fill_addr: " << hex << WQ.entry[index].address;
                                    cout << " victim_addr: " << block[set][way].tag << dec << endl; });
                        }
                        else { 
                            PACKET writeback_packet;

                            writeback_packet.fill_level = fill_level << 1;
                            writeback_packet.cpu = writeback_cpu;
                            writeback_packet.address = block[set][way].address;
                            writeback_packet.full_addr = block[set][way].full_addr;
                            writeback_packet.data = block[set][way].data;
                            writeback_packet.instr_id = WQ.entry[index].instr_id;
                            writeback_packet.ip = 0;
                            writeback_packet.type = WRITEBACK;
                            writeback_packet.event_cycle = current_core_cycle[writeback_cpu];

                            lower_level->add_wq(&writeback_packet);
                        }
                    }
#ifdef SANITY_CHECK
                    else {
                        // sanity check
                        if (cache_type != IS_STLB)
                            assert(0);
                    }
#endif
                }

                if (do_fill) {
                    // update prefetcher
                    if (cache_type == IS_L1I)
                        l1i_prefetcher_cache_fill(writeback_cpu, ((WQ.entry[index].ip)>>LOG2_BLOCK_SIZE)<<LOG2_BLOCK_SIZE, set, way, 0, ((block[set][way].ip)>>LOG2_BLOCK_SIZE)<<LOG2_BLOCK_SIZE);
                    else if (cache_type == IS_L1D)
                    {
                        //Neelu: Sending virtual fill and evicted address to L1D prefetcher.
                        //l1d_prefetcher_cache_fill(WQ.entry[index].full_addr, set, way, 0, block[set][way].address<<LOG2_BLOCK_SIZE, WQ.entry[index].pf_metadata);

                        uint64_t v_fill_addr, v_evicted_addr;
                        //First, getting virtual address for the fill address 
                        auto ppage_check = inverse_table.find(WQ.entry[index].full_addr >> LOG2_PAGE_SIZE);
                        assert(ppage_check != inverse_table.end());
                        v_fill_addr = (ppage_check->second) << LOG2_PAGE_SIZE;
                        v_fill_addr |= (WQ.entry[index].full_addr & ((1 << LOG2_PAGE_SIZE)-1));

                        //Now getting virtual address for the evicted address
                        /*Neelu: Note that it is not always necessary that evicted address is a valid address and is present in the inverse table, hence (1) do not use the assert and (2) if it is not present, assign it to zero. */

                        ppage_check = inverse_table.find(block[set][way].address >> (LOG2_PAGE_SIZE - LOG2_BLOCK_SIZE));
                        if(ppage_check != inverse_table.end())
                        {
                            v_evicted_addr = (ppage_check->second) << LOG2_PAGE_SIZE;
                            v_evicted_addr |= ((block[set][way].address << LOG2_BLOCK_SIZE) & ((1 << LOG2_PAGE_SIZE)-1));
                        }
                        else
                            v_evicted_addr = 0;

                        l1d_prefetcher_cache_fill(v_fill_addr, WQ.entry[index].full_addr, set, way, 0, v_evicted_addr, block[set][way].address<<LOG2_BLOCK_SIZE, WQ.entry[index].pf_metadata);		      

                    }
                    else if (cache_type == IS_L2C)
                        WQ.entry[index].pf_metadata = l2c_prefetcher_cache_fill(WQ.entry[index].address<<LOG2_BLOCK_SIZE, set, way, 0,
                                block[set][way].address<<LOG2_BLOCK_SIZE, WQ.entry[index].pf_metadata);
                    if (cache_type == IS_LLC)
                    {
                        cpu = writeback_cpu;
                        WQ.entry[index].pf_metadata =llc_prefetcher_cache_fill(WQ.entry[index].address<<LOG2_BLOCK_SIZE, set, way, 0,
                                block[set][way].address<<LOG2_BLOCK_SIZE, WQ.entry[index].pf_metadata);
                        cpu = 0;
                    }

#ifdef NOTIFY_L1D_OF_DTLB_EVICTION
                    //Neelu: Sending DTLB eviction notice to L1D
                    if(cache_type == IS_DTLB)
                    {
                        ooo_cpu[writeback_cpu].L1D.l1d_prefetcher_notify_about_dtlb_eviction(WQ.entry[index].address<<LOG2_PAGE_SIZE, set, way, 0, block[set][way].address<<LOG2_PAGE_SIZE, WQ.entry[index].pf_metadata);
                    }
#endif

                    // update replacement policy
                    (this->*update_replacement_state)(writeback_cpu, set, way, WQ.entry[index].full_addr, WQ.entry[index].ip, block[set][way].full_addr, WQ.entry[index].type, 0);

                    // COLLECT STATS
                    sim_miss[writeback_cpu][WQ.entry[index].type]++;
                    sim_access[writeback_cpu][WQ.entry[index].type]++;

                    fill_cache(set, way, &WQ.entry[index]);

                    // mark dirty
                    block[set][way].dirty = 1; 

                    // check fill level
                    if (WQ.entry[index].fill_level < fill_level) {
                        if(fill_level == FILL_L2)
                        {
                            if(WQ.entry[index].fill_l1i)
                            {
                                upper_level_icache[writeback_cpu]->return_data(&WQ.entry[index]);
                            }
                            if(WQ.entry[index].fill_l1d)
                            {
                                upper_level_dcache[writeback_cpu]->return_data(&WQ.entry[index]);
                            }
                        }
                        else
                        {
                            if (WQ.entry[index].instruction)
                                upper_level_icache[writeback_cpu]->return_data(&WQ.entry[index]);
                            if (WQ.entry[index].is_data)
                                upper_level_dcache[writeback_cpu]->return_data(&WQ.entry[index]);
                        }

                    }

                    MISS[WQ.entry[index].type]++;
                    ACCESS[WQ.entry[index].type]++;

                    // remove this entry from WQ
                    WQ.remove_queue(&WQ.entry[index]);
                }
            }
        }
    }
}

//@Vishal: Translation coming from TLB to L1 cache
void CACHE::handle_processed()
{
    assert(cache_type == IS_L1I || cache_type == IS_L1D);

    CACHE &tlb = cache_type == IS_L1I ? ooo_cpu[cpu].ITLB : ooo_cpu[cpu].DTLB;

    //@Vishal: one translation is processed per cycle
    if(tlb.PROCESSED.occupancy != 0)
    {
        if((tlb.PROCESSED.entry[tlb.PROCESSED.head].event_cycle <= current_core_cycle[cpu]))
        {
            int index = tlb.PROCESSED.head;

            if(tlb.PROCESSED.entry[index].l1_rq_index != -1)
            {
                assert(tlb.PROCESSED.entry[index].l1_wq_index == -1 && tlb.PROCESSED.entry[index].l1_pq_index == -1); //Entry can't have write and prefetch index

                int rq_index = tlb.PROCESSED.entry[index].l1_rq_index;

                if((tlb.PROCESSED.entry[index].full_addr) >> LOG2_PAGE_SIZE == (RQ.entry[rq_index].full_addr) >> LOG2_PAGE_SIZE)
                {

                    DP ( if (warmup_complete[cpu] ) {	
                            cout << "["<<NAME << "_handle_processed] packet: " << RQ.entry[rq_index]; 
                            });

                    RQ.entry[rq_index].translated = COMPLETED;

                    if(tlb.cache_type == IS_ITLB)
                        RQ.entry[rq_index].full_physical_address = (tlb.PROCESSED.entry[index].instruction_pa << LOG2_PAGE_SIZE) | (RQ.entry[rq_index].full_addr & ((1 << LOG2_PAGE_SIZE) - 1));
                    else
                    {
                        //Neelu: Marking the corresponding LQ entry as translated. 
                        ooo_cpu[cpu].LQ.entry[RQ.entry[rq_index].lq_index].translated = COMPLETED;
                        ITERATE_SET(merged, RQ.entry[rq_index].lq_index_depend_on_me, ooo_cpu[cpu].LQ.SIZE) 
                        {
                            ooo_cpu[cpu].LQ.entry[merged].translated = COMPLETED;						
                        }


                        RQ.entry[rq_index].full_physical_address = (tlb.PROCESSED.entry[index].data_pa << LOG2_PAGE_SIZE) | (RQ.entry[rq_index].full_addr & ((1 << LOG2_PAGE_SIZE) - 1));
                    }

                    // ADD LATENCY
                    if (RQ.entry[rq_index].event_cycle < current_core_cycle[cpu])
                        RQ.entry[rq_index].event_cycle = current_core_cycle[cpu] + LATENCY;
                    else
                        RQ.entry[rq_index].event_cycle += LATENCY;
                }
            }
            else if(tlb.PROCESSED.entry[index].l1_wq_index != -1)
            {
                assert(tlb.PROCESSED.entry[index].l1_rq_index == -1 && tlb.PROCESSED.entry[index].l1_pq_index == -1); //Entry can't have read and prefetch index

                int wq_index = tlb.PROCESSED.entry[index].l1_wq_index;
                if((tlb.PROCESSED.entry[index].full_addr) >> LOG2_PAGE_SIZE == (WQ.entry[wq_index].full_addr) >> LOG2_PAGE_SIZE)
                {

                    WQ.entry[wq_index].translated = COMPLETED;

                    if(tlb.cache_type == IS_ITLB)
                        WQ.entry[wq_index].full_physical_address = (tlb.PROCESSED.entry[index].instruction_pa << LOG2_PAGE_SIZE) | (WQ.entry[wq_index].full_addr & ((1 << LOG2_PAGE_SIZE) - 1));
                    else
                        WQ.entry[wq_index].full_physical_address = (tlb.PROCESSED.entry[index].data_pa << LOG2_PAGE_SIZE) | (WQ.entry[wq_index].full_addr & ((1 << LOG2_PAGE_SIZE) - 1));


                    // ADD LATENCY
                    if (WQ.entry[wq_index].event_cycle < current_core_cycle[cpu])
                        WQ.entry[wq_index].event_cycle = current_core_cycle[cpu] + LATENCY;
                    else
                        WQ.entry[wq_index].event_cycle += LATENCY;

                    DP ( if (warmup_complete[cpu] ) {
                            cout << "["<<NAME << "_handle_processed] packet: " << WQ.entry[wq_index];
                            });
                }
            }
            //Neelu: Checking for l1_pq_index as well as L1I prefetching is turned on and the corresponding translation requests are sent to ITLB.
            else if(tlb.PROCESSED.entry[index].l1_pq_index != -1)
            {
                //Neelu: This should occur only for L1I, because L1D prefetch requests get translations from STLB.
                assert(cache_type == IS_L1I);

                assert(tlb.PROCESSED.entry[index].l1_wq_index == -1 && tlb.PROCESSED.entry[index].l1_rq_index == -1); //Entry can't have write and read index

                int pq_index = tlb.PROCESSED.entry[index].l1_pq_index;
                if((tlb.PROCESSED.entry[index].full_addr) >> LOG2_PAGE_SIZE == (PQ.entry[pq_index].full_addr) >> LOG2_PAGE_SIZE)
                {

                    PQ.entry[pq_index].translated = COMPLETED;

                    if(tlb.cache_type == IS_ITLB)
                        PQ.entry[pq_index].full_physical_address = (tlb.PROCESSED.entry[index].instruction_pa << LOG2_PAGE_SIZE) | (PQ.entry[pq_index].full_addr & ((1 << LOG2_PAGE_SIZE) - 1));
                    else
                    {
                        //Neelu: L1D Prefetch translation requests don't go to DTLB.
                        assert(0);
                        PQ.entry[pq_index].full_physical_address = (tlb.PROCESSED.entry[index].data_pa << LOG2_PAGE_SIZE) | (PQ.entry[pq_index].full_addr & ((1 << LOG2_PAGE_SIZE) - 1));
                    }

                    DP ( if (warmup_complete[cpu] ) {
                            cout << "["<<NAME << "_handle_processed] packet: " << PQ.entry[pq_index];
                            });

                    // ADD LATENCY
                    if (PQ.entry[pq_index].event_cycle < current_core_cycle[cpu])
                        PQ.entry[pq_index].event_cycle = current_core_cycle[cpu] + LATENCY;
                    else
                        PQ.entry[pq_index].event_cycle += LATENCY;
                }
            }
            else
            {
                assert(0); //Either read queue, prefetch queue or write queue index should be present
            }


            //Neelu: Commenting this assert as ITLB can have translation requests from L1I prefetches. 
            //assert(tlb.PROCESSED.entry[index].prefetch_translation_merged == false);

            if(tlb.PROCESSED.entry[index].read_translation_merged)
            {
                ITERATE_SET(other_rq_index,tlb.PROCESSED.entry[index].l1_rq_index_depend_on_me, RQ.SIZE)
                {
                    if(RQ.entry[other_rq_index].translated == INFLIGHT && ((tlb.PROCESSED.entry[index].full_addr) >> LOG2_PAGE_SIZE == (RQ.entry[other_rq_index].full_addr) >> LOG2_PAGE_SIZE))
                    {
                        RQ.entry[other_rq_index].translated = COMPLETED;

                        if(tlb.cache_type == IS_ITLB)
                            RQ.entry[other_rq_index].full_physical_address = (tlb.PROCESSED.entry[index].instruction_pa << LOG2_PAGE_SIZE) | (RQ.entry[other_rq_index].full_addr & ((1 << LOG2_PAGE_SIZE) - 1));
                        else
                        {
                            //Neelu: Marking the corresponding LQ entry as translated. 
                            ooo_cpu[cpu].LQ.entry[RQ.entry[other_rq_index].lq_index].translated = COMPLETED;
                            ITERATE_SET(merged, RQ.entry[other_rq_index].lq_index_depend_on_me, ooo_cpu[cpu].LQ.SIZE)
                            {
                                ooo_cpu[cpu].LQ.entry[merged].translated = COMPLETED;                                          
                            }

                            RQ.entry[other_rq_index].full_physical_address = (tlb.PROCESSED.entry[index].data_pa << LOG2_PAGE_SIZE) | (RQ.entry[other_rq_index].full_addr & ((1 << LOG2_PAGE_SIZE) - 1));
                        }

                        RQ.entry[other_rq_index].event_cycle = current_core_cycle[cpu];
                        // ADD LATENCY
                        if (RQ.entry[other_rq_index].event_cycle < current_core_cycle[cpu])
                            RQ.entry[other_rq_index].event_cycle = current_core_cycle[cpu] + LATENCY;
                        else
                            RQ.entry[other_rq_index].event_cycle += LATENCY;

                        DP ( if (warmup_complete[cpu] ) {
                                cout << "["<<NAME << "_handle_processed] packet: " << RQ.entry[other_rq_index];
                                });
                    }
                }
            }


            if(tlb.PROCESSED.entry[index].write_translation_merged)
            {
                ITERATE_SET(other_wq_index,tlb.PROCESSED.entry[index].l1_wq_index_depend_on_me, WQ.SIZE) 
                {
                    if(WQ.entry[other_wq_index].translated == INFLIGHT && ((tlb.PROCESSED.entry[index].full_addr) >> LOG2_PAGE_SIZE == (WQ.entry[other_wq_index].full_addr) >> LOG2_PAGE_SIZE))
                    {

                        WQ.entry[other_wq_index].translated = COMPLETED;

                        if(tlb.cache_type == IS_ITLB)
                            WQ.entry[other_wq_index].full_physical_address = (tlb.PROCESSED.entry[index].instruction_pa << LOG2_PAGE_SIZE) | (WQ.entry[other_wq_index].full_addr & ((1 << LOG2_PAGE_SIZE) - 1));
                        else
                            WQ.entry[other_wq_index].full_physical_address = (tlb.PROCESSED.entry[index].data_pa << LOG2_PAGE_SIZE) | (WQ.entry[other_wq_index].full_addr & ((1 << LOG2_PAGE_SIZE) - 1));

                        WQ.entry[other_wq_index].event_cycle = current_core_cycle[cpu];
                        // ADD LATENCY
                        if (WQ.entry[other_wq_index].event_cycle < current_core_cycle[cpu])
                            WQ.entry[other_wq_index].event_cycle = current_core_cycle[cpu] + LATENCY;
                        else
                            WQ.entry[other_wq_index].event_cycle += LATENCY;

                        DP ( if (warmup_complete[cpu] ) {
                                cout << "["<<NAME << "_handle_processed] packet: " << WQ.entry[other_wq_index];
                                });
                    }
                }
            }


            //Neelu: Checking for prefetch_translation_merges too.
            if(tlb.PROCESSED.entry[index].prefetch_translation_merged)
            {
                ITERATE_SET(other_pq_index,tlb.PROCESSED.entry[index].l1_pq_index_depend_on_me, PQ.SIZE)
                {
                    if(PQ.entry[other_pq_index].translated == INFLIGHT && ((tlb.PROCESSED.entry[index].full_addr) >> LOG2_PAGE_SIZE == (PQ.entry[other_pq_index].full_addr) >> LOG2_PAGE_SIZE))
                    {

                        PQ.entry[other_pq_index].translated = COMPLETED;

                        if(tlb.cache_type == IS_ITLB)
                            PQ.entry[other_pq_index].full_physical_address = (tlb.PROCESSED.entry[index].instruction_pa << LOG2_PAGE_SIZE) | (PQ.entry[other_pq_index].full_addr & ((1 << LOG2_PAGE_SIZE) - 1));
                        else
                        {
                            assert(0); // Translation cannot come from DTLB
                            PQ.entry[other_pq_index].full_physical_address = (tlb.PROCESSED.entry[index].data_pa << LOG2_PAGE_SIZE) | (PQ.entry[other_pq_index].full_addr & ((1 << LOG2_PAGE_SIZE) - 1));
                        }

                        PQ.entry[other_pq_index].event_cycle = current_core_cycle[cpu];

                        DP ( if (warmup_complete[cpu] ) {
                                cout << "["<<NAME << "_handle_processed] packet: " << PQ.entry[other_pq_index];
                                });

                        // ADD LATENCY
                        if (PQ.entry[other_pq_index].event_cycle < current_core_cycle[cpu])
                            PQ.entry[other_pq_index].event_cycle = current_core_cycle[cpu] + LATENCY;
                        else
                            PQ.entry[other_pq_index].event_cycle += LATENCY;

                    }
                }

            }


            tlb.PROCESSED.remove_queue(&tlb.PROCESSED.entry[index]);
        }
    }

    //@Vishal: Check for Prefetch translations from STLB processed queue
    if(cache_type == IS_L1D)
    {
        CACHE &tlb = ooo_cpu[cpu].STLB;

        //@Vishal: one translation is processed per cycle
        if(tlb.PROCESSED.occupancy != 0)
        {
            if((tlb.PROCESSED.entry[tlb.PROCESSED.head].event_cycle <= current_core_cycle[cpu]))
            {
                int index = tlb.PROCESSED.head;

                if(tlb.PROCESSED.entry[index].l1_pq_index != -1)
                {
                    int pq_index = tlb.PROCESSED.entry[index].l1_pq_index;
                    if(PQ.entry[pq_index].translated == INFLIGHT && ((tlb.PROCESSED.entry[index].full_addr) >> LOG2_PAGE_SIZE == (PQ.entry[pq_index].full_addr) >> LOG2_PAGE_SIZE))
                    {
                        PQ.entry[pq_index].translated = COMPLETED;

                        //@Vishal: L1D prefetch is sending request, so translation should be in data_pa.
                        assert(tlb.PROCESSED.entry[index].data_pa != 0 && tlb.PROCESSED.entry[index].instruction_pa == 0);

                        PQ.entry[pq_index].full_physical_address = (tlb.PROCESSED.entry[index].data_pa << LOG2_PAGE_SIZE) | (PQ.entry[pq_index].full_addr & ((1 << LOG2_PAGE_SIZE) - 1));

                        DP ( if (warmup_complete[cpu] ) {
                                cout << "["<<NAME << "_handle_processed] packet: " << PQ.entry[pq_index];
                                });


                        // ADD LATENCY
                        if (PQ.entry[pq_index].event_cycle < current_core_cycle[cpu])
                            PQ.entry[pq_index].event_cycle = current_core_cycle[cpu] + LATENCY;
                        else
                            PQ.entry[pq_index].event_cycle += LATENCY;

                        assert((tlb.PROCESSED.entry[index].read_translation_merged == false) && (tlb.PROCESSED.entry[index].write_translation_merged == false));
                    }
                }

                if(tlb.PROCESSED.entry[index].prefetch_translation_merged)
                {
                    ITERATE_SET(other_pq_index, tlb.PROCESSED.entry[index].l1_pq_index_depend_on_me, PQ.SIZE) 
                    {
                        if(PQ.entry[other_pq_index].translated == INFLIGHT && ((tlb.PROCESSED.entry[index].full_addr) >> LOG2_PAGE_SIZE == (PQ.entry[other_pq_index].full_addr) >> LOG2_PAGE_SIZE))

                        {
                            PQ.entry[other_pq_index].translated = COMPLETED;
                            PQ.entry[other_pq_index].full_physical_address = (tlb.PROCESSED.entry[index].data_pa << LOG2_PAGE_SIZE) | (PQ.entry[other_pq_index].full_addr & ((1 << LOG2_PAGE_SIZE) - 1));

                            DP ( if (warmup_complete[cpu] ) {
                                    cout << "["<<NAME << "_handle_processed] packet: " << PQ.entry[other_pq_index];
                                    });


                            // ADD LATENCY
                            if (PQ.entry[other_pq_index].event_cycle < current_core_cycle[cpu])
                                PQ.entry[other_pq_index].event_cycle = current_core_cycle[cpu] + LATENCY;
                            else
                                PQ.entry[other_pq_index].event_cycle += LATENCY;
                        }
                    }
                }

                tlb.PROCESSED.remove_queue(&tlb.PROCESSED.entry[index]);
            }
            else
                return;
        }
    }
}

void CACHE::handle_read()
{
    // handle read
    uint32_t read_cpu = (RQ.next_access_index == RQ_SIZE) ? NUM_CPUS : RQ.entry[RQ.next_access_index].cpu;
    if (read_cpu == NUM_CPUS)
        return;

    if (RQ.next_access_cycle <= current_core_cycle[read_cpu]) {
        uint32_t rq_index = RQ.next_access_index;

        // Get candidate sets for PhantomCache
        uint64_t candidate_sets[8];
        uint32_t num_candidates = 0;
#ifdef PHANTOMCACHE
        num_candidates = get_candidate_sets(RQ.entry[rq_index].address, candidate_sets);
#endif

        // Check all candidate sets for hit
        bool hit = false;
        uint32_t set = 0, way = 0;
        
#ifdef PHANTOMCACHE
        for (uint32_t i = 0; i < num_candidates; i++) {
            set = candidate_sets[i];
            for (way = 0; way < NUM_WAY; way++) {
                if (block[set][way].valid && block[set][way].tag == RQ.entry[rq_index].address) {
                    hit = true;
                    break;
                }
            }
            if (hit)
                break;
        }
#else
        set = get_set(RQ.entry[rq_index].address);
        for (way = 0; way < NUM_WAY; way++) {
            if (block[set][way].valid && block[set][way].tag == RQ.entry[rq_index].address) {
                hit = true;
                break;
            }
        }
#endif

        if (hit) {
            // ... existing hit handling code ...
        } else {
            // ... existing miss handling code ...
        }

        // ... rest of existing code ...
    }
}

void CACHE::handle_prefetch()
{
    uint32_t prefetch_cpu = (PQ.next_access_index == PQ_SIZE) ? NUM_CPUS : PQ.entry[PQ.next_access_index].cpu;
    if (prefetch_cpu == NUM_CPUS)
        return;

    if (PQ.next_access_cycle <= current_core_cycle[prefetch_cpu]) {
        uint32_t pq_index = PQ.next_access_index;
        bool hit = false;
        uint32_t set = 0, way = 0;

#ifdef PHANTOMCACHE
        // Get candidate sets for PhantomCache
        uint64_t candidate_sets[8];
        uint32_t num_candidates = get_candidate_sets(PQ.entry[pq_index].address, candidate_sets);

        // Check all candidate sets for hit
        for (uint32_t i = 0; i < num_candidates; i++) {
            set = candidate_sets[i];
            for (way = 0; way < NUM_WAY; way++) {
                if (block[set][way].valid && block[set][way].tag == PQ.entry[pq_index].address) {
                    hit = true;
                    break;
                }
            }
            if (hit)
                break;
        }

        if (!hit) {
            // Try each candidate set until we find a victim
            for (uint32_t i = 0; i < num_candidates; i++) {
                set = candidate_sets[i];
                way = (this->*find_victim)(prefetch_cpu, PQ.entry[pq_index].instr_id, set, block[set], 
                                         PQ.entry[pq_index].ip, PQ.entry[pq_index].full_addr, 
                                         PQ.entry[pq_index].type);
                if (way != NUM_WAY)  // Found a victim
                    break;
            }
        }
#else
        // Original non-PhantomCache lookup
        set = get_set(PQ.entry[pq_index].address);
        for (way = 0; way < NUM_WAY; way++) {
            if (block[set][way].valid && block[set][way].tag == PQ.entry[pq_index].address) {
                hit = true;
                break;
            }
        }

        if (!hit) {
            way = (this->*find_victim)(prefetch_cpu, PQ.entry[pq_index].instr_id, set, block[set], 
                                     PQ.entry[pq_index].ip, PQ.entry[pq_index].full_addr, 
                                     PQ.entry[pq_index].type);
        }
#endif

        if (hit) {
            // update replacement policy
            (this->*update_replacement_state)(prefetch_cpu, set, way, block[set][way].full_addr, 
                                           PQ.entry[pq_index].ip, 0, PQ.entry[pq_index].type, 1);

            // COLLECT STATS
            sim_hit[prefetch_cpu][PQ.entry[pq_index].type]++;
            sim_access[prefetch_cpu][PQ.entry[pq_index].type]++;

            // mark prefetch as done
            PQ.entry[pq_index].translated = COMPLETED;
            PQ.entry[pq_index].event_cycle = current_core_cycle[prefetch_cpu];
        } else if (way != NUM_WAY) {
            // fill cache
            fill_cache(set, way, &PQ.entry[pq_index]);

            // update replacement policy
            (this->*update_replacement_state)(prefetch_cpu, set, way, PQ.entry[pq_index].full_addr, 
                                           PQ.entry[pq_index].ip, 0, PQ.entry[pq_index].type, 0);

            // COLLECT STATS
            sim_miss[prefetch_cpu][PQ.entry[pq_index].type]++;
            sim_access[prefetch_cpu][PQ.entry[pq_index].type]++;

            // mark prefetch as done
            PQ.entry[pq_index].translated = COMPLETED;
            PQ.entry[pq_index].event_cycle = current_core_cycle[prefetch_cpu];
        }

        // remove from queue
        PQ.remove_queue(&PQ.entry[pq_index]);
    }
}

void CACHE::operate()
{
    handle_fill();
    handle_writeback();
    reads_available_this_cycle = MAX_READ;

    //@Vishal: VIPT
    if(cache_type == IS_L1I || cache_type == IS_L1D)
        handle_processed();
    handle_read();

    if (PQ.occupancy && (reads_available_this_cycle > 0))
        handle_prefetch();

    if(PQ.occupancy && ((current_core_cycle[cpu] - PQ.entry[PQ.head].cycle_enqueued) > DEADLOCK_CYCLE))
    {
        cout << "DEADLOCK, PQ entry is not serviced for " << DEADLOCK_CYCLE << " cycles cache_type: " << NAME << " prefetch_id: "<<PQ.entry[PQ.head].prefetch_id<<  endl;
        cout << PQ.entry[PQ.head];	
        assert(0);
    }
}

uint32_t CACHE::get_set(uint64_t address)
{
    if (is_phantom_cache) {
        // For PhantomCache, get_set should return one of the candidate sets
        uint64_t candidate_sets[8];
        uint32_t num_candidates = get_candidate_sets(address, candidate_sets);
        // Select a candidate set using round-robin or other policy
        return select_candidate_set(candidate_sets);
    } else {
#ifdef PUSH_DTLB_PB
        if(cache_type == IS_DTLB_PB)
            return 0;
        else
#endif
            return (uint32_t) (address & ((1 << lg2(NUM_SET)) - 1)); 
    }
}

        uint32_t CACHE::get_way(uint64_t address, uint32_t set)
        {
            for (uint32_t way=0; way<NUM_WAY; way++) {
                if (block[set][way].valid && (block[set][way].tag == address)) 
                    return way;
            }

            return NUM_WAY;
        }

        void CACHE::fill_cache(uint32_t set, uint32_t way, PACKET *packet)
        {
#ifdef SANITY_CHECK
#ifdef PUSH_DTLB_PB
            if(cache_type == IS_DTLB_PB) {
                if(packet->data == 0)
                {
                    cout << "Inside DTLB_PB, current = " << current_core_cycle[cpu] << " instr_id = " << packet->instr_id << endl;
                    assert(0);
                }
            }
#endif
            if (cache_type == IS_ITLB) {
                if (packet->data == 0)
                {
                    cout << "current = " << current_core_cycle[cpu] << " instr_id = "<< packet->instr_id << endl;
                    assert(0);
                }
            }

            if (cache_type == IS_DTLB) {
                if (packet->data == 0)
                {
                    cout << "current = " << current_core_cycle[cpu] << " instr_id = "<< packet->instr_id << endl;
                    assert(0);
                }
            }

            if (cache_type == IS_STLB) {
                if (packet->data == 0)
                    assert(0);
            }

            if (cache_type == IS_PSCL5) {
                if (packet->data == 0)
                    assert(0);
            }

            if (cache_type == IS_PSCL4) {
                if (packet->data == 0)
                    assert(0);
            }

            if (cache_type == IS_PSCL3) {
                if (packet->data == 0)
                    assert(0);
            }

            if (cache_type == IS_PSCL2) {
                if (packet->data == 0)
                    assert(0);
            }
#endif
            if (block[set][way].prefetch && (block[set][way].used == 0))
                pf_useless++;

            if (block[set][way].valid == 0)
                block[set][way].valid = 1;
            block[set][way].dirty = 0;
            block[set][way].prefetch = (packet->type == PREFETCH || packet->type == PREFETCH_TRANSLATION || packet->type == TRANSLATION_FROM_L1D) ? 1 : 0;
            block[set][way].used = 0;

            //Neelu: Setting instruction and translation fields in L2C
            if(cache_type == IS_L2C)
            {	
                if(packet->type == PREFETCH_TRANSLATION || packet->type == TRANSLATION_FROM_L1D || packet->type == LOAD_TRANSLATION)
                    block[set][way].translation = 1;
                else
                    block[set][way].translation = 0;
                if((packet->type == LOAD || packet->type == PREFETCH) && packet->instruction)
                    block[set][way].instruction = 1;
                else
                    block[set][way].instruction = 0;
            }

            //Neelu: setting IPCP prefetch class
            block[set][way].pref_class = ((packet->pf_metadata & PREF_CLASS_MASK) >> NUM_OF_STRIDE_BITS);

            if (block[set][way].prefetch) 
            {
                pf_fill++;

                //Neelu: IPCP prefetch stats
                if(cache_type == IS_L1D)
                {
                    if(block[set][way].pref_class < 5)						                     
                    {
                        pref_filled[cpu][block[set][way].pref_class]++;
                    }
                }
            }

            block[set][way].delta = packet->delta;
            block[set][way].depth = packet->depth;
            block[set][way].signature = packet->signature;
            block[set][way].confidence = packet->confidence;

            block[set][way].tag = packet->address; //@Vishal: packet->address will be physical address for L1I, as it is only filled on a miss.
            block[set][way].address = packet->address;
            block[set][way].full_addr = packet->full_addr;
            block[set][way].data = packet->data;
            block[set][way].cpu = packet->cpu;
            block[set][way].instr_id = packet->instr_id;

            DP ( if (warmup_complete[packet->cpu] ) {
                    cout << "[" << NAME << "] " << __func__ << " set: " << set << " way: " << way;
                    cout << " lru: " << block[set][way].lru << " tag: " << hex << block[set][way].tag << " full_addr: " << block[set][way].full_addr;
                    cout << " data: " << block[set][way].data << dec << endl; });
        }

        int CACHE::check_hit(PACKET *packet)
        {
            // Get candidate sets for PhantomCache
            uint64_t candidate_sets[8];
            uint32_t num_candidates = 0;
            if (is_phantom_cache) {
                num_candidates = get_candidate_sets(packet->address, candidate_sets);
            }

            int match_way = -1;
            uint32_t set = 0;

            if (is_phantom_cache) {
                // Check all candidate sets for hit
                for (uint32_t i = 0; i < num_candidates; i++) {
                    set = candidate_sets[i];
                    if (NUM_SET < set) {
                        cerr << "[" << NAME << "_ERROR] " << __func__ << " invalid set index: " << set << " NUM_SET: " << NUM_SET;
                        cerr << " address: " << hex << packet->address << " full_addr: " << packet->full_addr << dec;
                        cerr << " event: " << packet->event_cycle << endl;
                        assert(0);
                    }

                    // Check each way in the current set
                    for (uint32_t way = 0; way < NUM_WAY; way++) {
                        if (block[set][way].valid && (block[set][way].tag == packet->address)) {
                            match_way = way;
                            break;
                        }
                    }
                    if (match_way != -1)
                        break;
                }
            } else {
                // Original non-PhantomCache lookup
                set = get_set(packet->address);
                if (NUM_SET < set) {
                    cerr << "[" << NAME << "_ERROR] " << __func__ << " invalid set index: " << set << " NUM_SET: " << NUM_SET;
                    cerr << " address: " << hex << packet->address << " full_addr: " << packet->full_addr << dec;
                    cerr << " event: " << packet->event_cycle << endl;
                    assert(0);
                }

                uint64_t packet_tag;
                if(cache_type == IS_L1I || cache_type == IS_L1D) //@Vishal: VIPT
                {
                    assert(packet->full_physical_address != 0);
                    packet_tag = packet->full_physical_address >> LOG2_BLOCK_SIZE;
                }
                else
                    packet_tag = packet->address;

                // Check each way in the set
                for (uint32_t way = 0; way < NUM_WAY; way++) {
                    if (block[set][way].valid && (block[set][way].tag == packet_tag)) {
                        match_way = way;
                        break;
                    }
                }
            }

            if (match_way != -1) {
                DP ( if (warmup_complete[packet->cpu] ) {
                        cout << "[" << NAME << "] " << __func__ << " instr_id: " << packet->instr_id << " type: " << +packet->type << hex << " addr: " << packet->address;
                        cout << " full_addr: " << packet->full_addr << " tag: " << block[set][match_way].tag << " data: " << block[set][match_way].data << dec;
                        cout << " set: " << set << " way: " << match_way << " lru: " << block[set][match_way].lru;
                        cout << " event: " << packet->event_cycle << " cycle: " << current_core_cycle[cpu] << endl; });
            }

#ifdef PRINT_QUEUE_TRACE
    if(packet->instr_id == QTRACE_INSTR_ID)
    {
        cout << "[" << NAME << "] " << __func__ << " instr_id: " << packet->instr_id << " type: " << +packet->type << hex << " addr: " << packet->address;
        cout << " full_addr: " << packet->full_addr<<dec;
        cout << " set: " << set << " way: " << match_way;
        cout << " event: " << packet->event_cycle << " cycle: " << current_core_cycle[cpu]<<" cpu: "<<cpu<< endl;
    }
#endif


            if (packet->address == 0)
                assert(0);

            RQ.TO_CACHE++;
            RQ.ACCESS++;

            return -1;
        }

        int CACHE::add_wq(PACKET *packet)
        {

            assert(cache_type != IS_L1I || cache_type != IS_ITLB || cache_type != IS_DTLB || cache_type != IS_STLB); //@Vishal: L1I cache does not have write packets

            // check for duplicates in the write queue
            int index;
            if(cache_type == IS_L1D)
                index = check_nonfifo_queue(&WQ,packet,false);
            else 
                index = WQ.check_queue(packet);

            if (index != -1) {
                if(WQ.entry[index].cpu != packet->cpu)
                {
                    cout << "Write request from CPU " << packet->cpu << " merging with Write request from CPU " << WQ.entry[index].cpu << endl;
                    assert(0);
                }


                WQ.MERGED++;
                WQ.ACCESS++;

                return index; // merged index
            }

            // sanity check
            if (WQ.occupancy >= WQ.SIZE)
                assert(0);

            bool translation_sent = false;
            int get_translation_index = -1;
            int get_translation_queue = IS_RQ;

            // if there is no duplicate, add it to the write queue
            index = WQ.tail;

            //@Vishal: Since L1 WQ is non fifo, find empty index
            if(cache_type == IS_L1D)
            {
                for (uint i = 0; i < WQ.SIZE; i++)
                    if(WQ.entry[i].address == 0)
                    {
                        index = i;
                        break;
                    }
            }

            //@Vishal: Check if pending translation sent to TLB
            if(cache_type == IS_L1D)
            {

                if(ooo_cpu[packet->cpu].DTLB.RQ.occupancy == ooo_cpu[packet->cpu].DTLB.RQ.SIZE)
                {
                    ooo_cpu[packet->cpu].DTLB.RQ.FULL++;
                    return -2; // cannot handle this request because translation cannotbe sent to TLB
                }
                PACKET translation_packet = *packet;
                translation_packet.instruction = 0;
                translation_packet.l1_wq_index = index;
                translation_packet.fill_level = FILL_L1;
                translation_packet.type = LOAD_TRANSLATION; 	
                if (knob_cloudsuite)
                    translation_packet.address = ((packet->full_addr >> LOG2_PAGE_SIZE) << 9) | packet->asid[1];
                else
                    translation_packet.address = packet->full_addr >> LOG2_PAGE_SIZE;

                ooo_cpu[packet->cpu].DTLB.add_rq(&translation_packet);
            }


            if (WQ.entry[index].address != 0) {
                cerr << "[" << NAME << "_ERROR] " << __func__ << " is not empty index: " << index;
                cerr << " address: " << hex << WQ.entry[index].address;
                cerr << " full_addr: " << WQ.entry[index].full_addr << dec << endl;
                assert(0);
            }

            WQ.entry[index] = *packet;

            // ADD LATENCY
            if (WQ.entry[index].event_cycle < current_core_cycle[packet->cpu])
                WQ.entry[index].event_cycle = current_core_cycle[packet->cpu] + LATENCY;
            else
                WQ.entry[index].event_cycle += LATENCY;

            if(cache_type == IS_L1D)
                WQ.entry[index].translated = INFLIGHT;

            WQ.occupancy++;
            WQ.tail++;
            if (WQ.tail >= WQ.SIZE)
                WQ.tail = 0;

            DP (if (warmup_complete[WQ.entry[index].cpu]) {
                    cout << "[" << NAME << "_WQ] " <<  __func__ << " instr_id: " << WQ.entry[index].instr_id << " address: " << hex << WQ.entry[index].address;
                    cout << " full_addr: " << WQ.entry[index].full_addr << dec;
                    cout << " head: " << WQ.head << " tail: " << WQ.tail << " occupancy: " << WQ.occupancy;
                    cout << " data: " << hex << WQ.entry[index].data << dec;
                    cout << " event: " << WQ.entry[index].event_cycle << " current: " << current_core_cycle[WQ.entry[index].cpu] << endl;});


#ifdef PRINT_QUEUE_TRACE
            if(packet->instr_id == QTRACE_INSTR_ID)
            {
                cout << "[" << NAME << "_WQ] " <<  __func__ << " instr_id: " << WQ.entry[index].instr_id << " address: " << hex << WQ.entry[index].address;
                cout << " full_addr: " << WQ.entry[index].full_addr << dec;
                cout << " head: " << WQ.head << " tail: " << WQ.tail << " occupancy: " << WQ.occupancy;
                cout << " data: " << hex << WQ.entry[index].data << dec;
                cout << " event: " << WQ.entry[index].event_cycle << " current: " << current_core_cycle[WQ.entry[index].cpu] << " cpu: "<<cpu<<endl;
            }
#endif

            WQ.TO_CACHE++;
            WQ.ACCESS++;

            return -1;
        }

        int CACHE::prefetch_line(uint64_t ip, uint64_t base_addr, uint64_t pf_addr, int pf_fill_level, uint32_t prefetch_metadata) /*, uint64_t prefetch_id)*/		//Neelu: commented. 
        {
            //	if(cache_type == IS_L2C)
            //		cout<<"Aye Aye, Captain, requested.";

            //Neelu: Todo: So, do all prefetches access STLB, even the same page ones? Is that correct? 
            pf_requested++;
            DP ( if (warmup_complete[cpu]) {cout << "entered prefetch_line, occupancy = " << PQ.occupancy << "SIZE=" << PQ.SIZE << endl; });
            if (PQ.occupancy < PQ.SIZE) {
                //if(cache_type == IS_L2C)
                //      cout<<"Aye Aye, Captain, issued.";

                DP ( if (warmup_complete[cpu]) {cout << "packet entered in PQ" << endl; });
                PACKET pf_packet;
                pf_packet.fill_level = pf_fill_level;
                pf_packet.pf_origin_level = fill_level;
                if(pf_fill_level == FILL_L1)		   
                {
                    pf_packet.fill_l1d = 1;
                }

                pf_packet.pf_metadata = prefetch_metadata;
                pf_packet.cpu = cpu;
                //pf_packet.data_index = LQ.entry[lq_index].data_index;
                //pf_packet.lq_index = lq_index;
                pf_packet.address = pf_addr >> LOG2_BLOCK_SIZE;
                pf_packet.full_addr = pf_addr;
                pf_packet.full_virtual_address = pf_addr;

#ifdef PUSH_PREFETCHES_FROM_L2_TO_L1

                if(cache_type == IS_L1D)
                {
                    //Neelu: Checking if the request is pushed from L2 or not,
                    if(((prefetch_metadata >> 16) & 1) == 1)
                    {
                        pf_packet.translated = COMPLETED; 
                        pf_packet.full_physical_address = pf_addr;
                        assert(pf_packet.full_physical_address != 0);
                        pf_pushed_from_L2C++;
                    }
                }

#endif

                //pf_packet.instr_id = LQ.entry[lq_index].instr_id;
                //pf_packet.rob_index = LQ.entry[lq_index].rob_index;
                pf_packet.ip = ip;
                //pf_packet.prefetch_id = prefetch_id;		Neelu: commented, Vasudha was using for debugging. Assigning to zero for now.
                pf_packet.prefetch_id = 0; 
                pf_packet.type = PREFETCH;
                pf_packet.event_cycle = current_core_cycle[cpu];

                // give a dummy 0 as the IP of a prefetch
                add_pq(&pf_packet);
                DP ( if (warmup_complete[pf_packet.cpu]) {cout << "returned from add_pq" << endl; });
                pf_issued++;

                if(cache_type == IS_L1D)
                {
                    if((base_addr >> LOG2_PAGE_SIZE) != (pf_addr >> LOG2_PAGE_SIZE))
                        cross_page_prefetch_requests++;
                    else
                        same_page_prefetch_requests++;
                }

                return 1;

            }

            return 0;
        }

        int CACHE::prefetch_translation(uint64_t ip, uint64_t pf_addr, int pf_fill_level, uint32_t prefetch_metadata, uint64_t prefetch_id, uint8_t instruction)
        {
            pf_requested++;
            DP ( if (warmup_complete[cpu]) {cout << "entered prefetch_translation, occupancy = " << PQ.occupancy << "SIZE=" << PQ.SIZE << endl; });
            if (PQ.occupancy < PQ.SIZE) 
            {
                DP ( if (warmup_complete[cpu]) {cout << "packet entered in PQ" << endl; });
                PACKET pf_packet;
                pf_packet.fill_level = pf_fill_level;
                pf_packet.pf_origin_level = fill_level;
                pf_packet.pf_metadata = prefetch_metadata;
                pf_packet.cpu = cpu;
                pf_packet.instruction = instruction;
                //pf_packet.data_index = LQ.entry[lq_index].data_index;
                //pf_packet.lq_index = lq_index;
                pf_packet.address = pf_addr >> LOG2_PAGE_SIZE;
                pf_packet.full_addr = pf_addr;
                pf_packet.full_virtual_address = pf_addr;
                //pf_packet.instr_id = LQ.entry[lq_index].instr_id;
                //pf_packet.rob_index = LQ.entry[lq_index].rob_index;
                pf_packet.ip = ip;
                pf_packet.prefetch_id = prefetch_id;
                pf_packet.type = PREFETCH_TRANSLATION;
                pf_packet.event_cycle = current_core_cycle[cpu];

                // give a dummy 0 as the IP of a prefetch
                add_pq(&pf_packet);
                DP ( if (warmup_complete[pf_packet.cpu]) {cout << "returned from add_pq" << endl; });
                pf_issued++;

                return 1;
            }

            return 0;
        }

        int CACHE::kpc_prefetch_line(uint64_t base_addr, uint64_t pf_addr, int pf_fill_level, int delta, int depth, int signature, int confidence, uint32_t prefetch_metadata)
        {

            assert(0); //@Vishal: This should not be called


            if (PQ.occupancy < PQ.SIZE) {

                PACKET pf_packet;
                pf_packet.fill_level = pf_fill_level;
                pf_packet.pf_origin_level = fill_level;
                pf_packet.pf_metadata = prefetch_metadata;
                pf_packet.cpu = cpu;
                //pf_packet.data_index = LQ.entry[lq_index].data_index;
                //pf_packet.lq_index = lq_index;
                pf_packet.address = pf_addr >> LOG2_BLOCK_SIZE;
                pf_packet.full_addr = pf_addr;
                //pf_packet.instr_id = LQ.entry[lq_index].instr_id;
                //pf_packet.rob_index = LQ.entry[lq_index].rob_index;
                pf_packet.ip = 0;
                pf_packet.type = PREFETCH;
                pf_packet.delta = delta;
                pf_packet.depth = depth;
                pf_packet.signature = signature;
                pf_packet.confidence = confidence;
                pf_packet.event_cycle = current_core_cycle[cpu];

                if ((base_addr>>LOG2_PAGE_SIZE) == (pf_addr>>LOG2_PAGE_SIZE))
                { 
                    pf_packet.full_physical_address = pf_addr;
                    pf_packet.translated = COMPLETED;
                }
                else
                    pf_packet.full_physical_address = 0;

                // give a dummy 0 as the IP of a prefetch
                int return_val = add_pq(&pf_packet);

                if(return_val > -2) //@Vishal: In some cases, even if the PQ is empty, request cannot be serviced.
                    pf_issued++;

                return 1;
            }

            return 0;
        }

        int CACHE::add_pq(PACKET *packet)
        {

            assert(packet->type == PREFETCH || packet->type == PREFETCH_TRANSLATION);

            // @Vishal: L1I cache does not send prefetch request
            // Neelu: Added instruction prefetching support, so commenting this assert. 
            //assert(cache_type != IS_L1I);

            // check for the latest wirtebacks in the write queue 
            // @Vishal: WQ is non-fifo for L1 cache

            int wq_index;
            if(cache_type == IS_L1D || cache_type == IS_L1I)
                wq_index = check_nonfifo_queue(&WQ,packet,false);
            else
                wq_index = WQ.check_queue(packet);

            if (wq_index != -1) {

                if(WQ.entry[wq_index].cpu != packet->cpu)
                {
                    cout << "Prefetch request from CPU " << packet->cpu << " merging with Write request from CPU " << WQ.entry[wq_index].cpu << endl;
                    assert(0);
                }

                //Neelu: Adding 1 cycle WQ forwarding latency
                if (packet->event_cycle < current_core_cycle[packet->cpu])
                    packet->event_cycle = current_core_cycle[packet->cpu] + 1;
                else
                    packet->event_cycle += 1; 


                //Neelu: Todo: Is this sanity check sane? Removed check for L1-I 
#ifdef SANITY_CHECK

                if(cache_type == IS_ITLB || cache_type == IS_DTLB || cache_type == IS_STLB)
                    assert(0);

#endif


                // check fill level
                if (packet->fill_level < fill_level) {

                    packet->data = WQ.entry[wq_index].data;

                    if(fill_level == FILL_L2)
                    {
                        if(packet->fill_l1i)
                        {
                            upper_level_icache[packet->cpu]->return_data(packet);
                        }
                        if(packet->fill_l1d)
                        {
                            upper_level_dcache[packet->cpu]->return_data(packet);
                        }
                    }
                    else
                    {

                        if (packet->instruction) 
                            upper_level_icache[packet->cpu]->return_data(packet);
                        else // data
                            upper_level_dcache[packet->cpu]->return_data(packet);
                    }
                }

                HIT[packet->type]++;
                ACCESS[packet->type]++;

                WQ.FORWARD++;
                PQ.ACCESS++;

                return -1;
            }

            // check for duplicates in the PQ
            int index = PQ.check_queue(packet);
            if (index != -1) {
                if(PQ.entry[index].cpu != packet->cpu)
                {
                    cout << "Prefetch request from CPU " << packet->cpu << " merging with Prefetch request from CPU " << PQ.entry[index].cpu << endl;
                    assert(0);
                }

                //@v send_both_tlb should be updated in STLB PQ if the entry needs to be serviced to both ITLB and DTLB
                if(cache_type == IS_STLB)
                {
                    /* Fill level of incoming request and prefetch packet should be same else STLB prefetch request(with instruction=1) might get 			merged with DTLB/ITLB, making send_both_tlb=1 due to a msimatch in instruction variable. If this happens, data will be returned to 			both ITLB and DTLB, incurring MSHR miss*/

                    if(PQ.entry[index].fill_level==1 && packet -> fill_level == 1)
                    {
                        if((PQ.entry[index].instruction != packet-> instruction) && PQ.entry[index].send_both_tlb == 0)
                        {        PQ.entry[index].send_both_tlb = 1;
                        }
                    }
                }

                if (packet->fill_level < PQ.entry[index].fill_level)
                {
                    PQ.entry[index].fill_level = packet->fill_level;
                    PQ.entry[index].instruction = packet->instruction; 
                }

                //@Vasudha: Fails when DTLB prefetch with instructions 0, STLB prefetch with instruction 0 and STLB prefetch with instruction 1 gets merged
                /*if((packet->instruction == 1) && (PQ.entry[index].instruction != 1))
                  {
                  PQ.entry[index].instruction = 1;
                  }*/
                if((packet->is_data == 1) && (PQ.entry[index].is_data != 1))
                {
                    PQ.entry[index].is_data = 1;
                }
                if((packet->fill_l1i) && (PQ.entry[index].fill_l1i != 1))
                {
                    PQ.entry[index].fill_l1i = 1;
                }
                if((packet->fill_l1d) && (PQ.entry[index].fill_l1d != 1))
                {
                    PQ.entry[index].fill_l1d = 1;
                }

                PQ.MERGED++;
                PQ.ACCESS++;

                return index; // merged index
            }

            // check occupancy
            if (PQ.occupancy == PQ_SIZE) {
                PQ.FULL++;

                DP ( if (warmup_complete[packet->cpu]) {
                        cout << "[" << NAME << "] cannot process add_pq since it is full" << endl; });
                return -2; // cannot handle this request
            }

            // if there is no duplicate, add it to PQ
            index = PQ.tail;

#ifdef SANITY_CHECK
            if (PQ.entry[index].address != 0) {
                cerr << "[" << NAME << "_ERROR] " << __func__ << " is not empty index: " << index;
                cerr << " address: " << hex << PQ.entry[index].address;
                cerr << " full_addr: " << PQ.entry[index].full_addr << dec << endl;
                assert(0);
            }
#endif


            bool translation_sent = false;
            int get_translation_index = -1;
            int get_translation_queue = IS_RQ;


            //Neelu: Not adding any addition condition for skipping translation for prefetches pushed from L2 to L1 because full_phy_addr != 0.

            //@Vishal: Check if pending translation sent to TLB if its need to be translated
            if(cache_type == IS_L1D && packet->full_physical_address == 0)
            {

#ifdef NO_TRANSLATION_PENALTY_FOR_PREFETCHES
                pf_requested++;
                pf_issued++;
                auto ppage_check = ooo_cpu[packet->cpu].PTW.page_table.find(packet->full_virtual_address >> LOG2_PAGE_SIZE);
                if(ppage_check == ooo_cpu[packet->cpu].PTW.page_table.end())
                {
                    //Neelu: Cannot issue prefetch request as it is a page fault. 
                    packet->full_physical_address = UINT64_MAX;
                    packet->full_addr = packet->full_virtual_address;
                }		
                else
                {
                    uint64_t phy_addr = (ppage_check->second) << LOG2_PAGE_SIZE;
                    phy_addr |= (packet->full_virtual_address & ((1 << LOG2_PAGE_SIZE)-1));
                    packet->full_physical_address = phy_addr;
                    packet->full_addr = packet->full_virtual_address;
                    //Neelu: TODO: Take care of cloudsuite for this knob
                }
                packet->translated = COMPLETED;

#else

                if(ooo_cpu[packet->cpu].STLB.RQ.occupancy == ooo_cpu[packet->cpu].STLB.RQ.SIZE)
                {
                    ooo_cpu[packet->cpu].STLB.RQ.FULL++;
                    return -2; // cannot handle this request because translation cannot be sent to TLB
                }

                PACKET translation_packet = *packet;
                translation_packet.l1_pq_index = index;
                translation_packet.fill_level = FILL_L2;
                translation_packet.type = TRANSLATION_FROM_L1D;		
                pf_requested++;
                if (knob_cloudsuite)
                    translation_packet.address = ((packet->full_addr >> LOG2_PAGE_SIZE) << 9) | packet -> asid[1]; //@Vishal: TODO Check this address, will be wrong when L1I prefetcher is used
                else
                    translation_packet.address = packet->full_addr >> LOG2_PAGE_SIZE;

                //@Vishal: Add translation packet from PQ to L2 cache.
                ooo_cpu[packet->cpu].STLB.add_rq(&translation_packet); 
                pf_issued++;
#endif
            }

            //Neelu: Adding translation request to ITLB for instruction prefetch requests.
            if(cache_type == IS_L1I && packet->full_physical_address == 0)
            {
                if(ooo_cpu[packet->cpu].ITLB.RQ.occupancy == ooo_cpu[packet->cpu].ITLB.RQ.SIZE)
                {
                    ooo_cpu[packet->cpu].ITLB.RQ.FULL++;
                    return -2; //cannot handle this request as ITLB read queue is full.
                }

                //ITLB RQ occupancy is not full.
                PACKET translation_packet = *packet;
                translation_packet.l1_pq_index = index;
                translation_packet.fill_level = FILL_L1;
                translation_packet.instruction = 1;
                translation_packet.type = TRANSLATION_FROM_L1D;
                //Neelu: As pf_v_addr is assigned to ip as well as full_addr in prefetch_code_line function, either will work for assigning address.
                if (knob_cloudsuite)
                    translation_packet.address = ((packet->ip >> LOG2_PAGE_SIZE) << 9) | ( 256 + packet->asid[0]);
                else
                    translation_packet.address = packet->ip >> LOG2_PAGE_SIZE;

                //Neelu: Assigning full virtual address to the packet.
                //Todo: Not sure of the implications to cloudsuite.
                translation_packet.full_virtual_address = packet->ip;

                ooo_cpu[packet->cpu].ITLB.add_rq(&translation_packet);	

            }


            PQ.entry[index] = *packet;
            PQ.entry[index].cycle_enqueued = current_core_cycle[cpu];

            //@Vasudha - if any TLB calls add_pq
            if(knob_cloudsuite && (cache_type==IS_ITLB || cache_type==IS_DTLB || cache_type==IS_STLB))
            {
                if(PQ.entry[index].instruction == 1)
                    PQ.entry[index].address = ((packet->ip >> LOG2_PAGE_SIZE) << 9) | ( 256 + packet->asid[0]);
                else
                    PQ.entry[index].address = ((packet->full_addr >> LOG2_PAGE_SIZE) << 9) | packet -> asid[1];
            }

            // ADD LATENCY
            if (PQ.entry[index].event_cycle < current_core_cycle[packet->cpu])
                PQ.entry[index].event_cycle = current_core_cycle[packet->cpu] + LATENCY;
            else
                PQ.entry[index].event_cycle += LATENCY ;

            //Neelu: Adding condition to mark translated as INFLIGHT only if it is COMPLETED.
#ifndef NO_TRANSLATION_PENALTY_FOR_PREFETCHES
            if(cache_type == IS_L1D)
            {
#ifdef PUSH_PREFETCHES_FROM_L2_TO_L1
                if(PQ.entry[index].translated != COMPLETED)
#endif	   
                    PQ.entry[index].translated = INFLIGHT;
            }
#endif

            //Neelu: Marking translations as inflight for L1I as well.
            if(cache_type == IS_L1I)
                PQ.entry[index].translated = INFLIGHT; 


            PQ.occupancy++;
            PQ.tail++;
            if (PQ.tail >= PQ.SIZE)
                PQ.tail = 0;

            DP ( if (warmup_complete[PQ.entry[index].cpu] ) {
                    cout << "[" << NAME << "_PQ] " <<  __func__ << " prefetch_id: " << PQ.entry[index].prefetch_id << " address: " << hex << PQ.entry[index].address;
                    cout << " full_addr: " << PQ.entry[index].full_addr << dec;
                    cout << " type: " << +PQ.entry[index].type << " head: " << PQ.head << " tail: " << PQ.tail << " occupancy: " << PQ.occupancy;
                    cout << " event: " << PQ.entry[index].event_cycle << " current: " << current_core_cycle[PQ.entry[index].cpu] << endl; });

#ifdef PRINT_QUEUE_TRACE
            if(packet->instr_id == QTRACE_INSTR_ID)
            {
                cout << "[" << NAME << "_PQ] " <<  __func__ << " instr_id: " << PQ.entry[index].instr_id << " address: " << hex << PQ.entry[index].address;
                cout << " full_addr: " << PQ.entry[index].full_addr << dec;
                cout << " type: " << +PQ.entry[index].type << " head: " << PQ.head << " tail: " << PQ.tail << " occupancy: " << PQ.occupancy;
                cout << " event: " << PQ.entry[index].event_cycle << " current: " << current_core_cycle[PQ.entry[index].cpu] << endl;
            }
#endif

            if (packet->address == 0)
                assert(0);

            PQ.TO_CACHE++;
            PQ.ACCESS++;

            return -1;
        }

        int CACHE::check_mshr(PACKET *packet)
        {
            return check_nonfifo_queue(&MSHR, packet, true); //@Vishal: Updated from check_mshr
        }

        void CACHE::return_data(PACKET *packet)
        {
            // check MSHR information
            int mshr_index = check_nonfifo_queue(&MSHR, packet, true); //@Vishal: Updated from check_mshr

            // sanity check
            if (mshr_index == -1) {
                cerr << "[" << NAME << "_MSHR] " << __func__ << " instr_id: " << packet->instr_id << " prefetch_id: " << packet->prefetch_id  << " cannot find a matching entry!";
                cerr << " full_addr: " << hex << packet->full_addr;
                cerr << " address: " << packet->address << dec;
                cerr << " event: " << packet->event_cycle << " current: " << current_core_cycle[packet->cpu] << endl;
                cerr << " send_both_tlb: " << unsigned(packet->send_both_tlb) << endl;
                cerr << " instruction: " << unsigned(packet->instruction) << ", data: " << unsigned(packet->is_data) << endl;
                cerr << " fill_l1d: " << unsigned(packet->fill_l1d) << ", fill_l1i: " << unsigned(packet->fill_l1i) << endl;
                assert(0);
            }

            // MSHR holds the most updated information about this request
            // no need to do memcpy
            MSHR.num_returned++;
            MSHR.entry[mshr_index].returned = COMPLETED;
#ifdef INS_PAGE_TABLE_WALKER
            if(cache_type == IS_STLB)
            {
                packet->data >>= LOG2_PAGE_SIZE; //@Vishal: Remove last 12 bits from the data coming from PTW
            }
            MSHR.entry[mshr_index].data = packet->data;
#endif

            if(cache_type==IS_ITLB||cache_type==IS_DTLB||cache_type==IS_STLB)
            {
                if(MSHR.entry[mshr_index].data == 0)
                {
                    cout << "return_data writes 0 in TLB.data\n";
                    assert(0);
                }
            }
            MSHR.entry[mshr_index].pf_metadata = packet->pf_metadata;

            // ADD LATENCY
            if (MSHR.entry[mshr_index].event_cycle < current_core_cycle[packet->cpu])
                MSHR.entry[mshr_index].event_cycle = current_core_cycle[packet->cpu] + LATENCY;
            else
                MSHR.entry[mshr_index].event_cycle += LATENCY;

            update_fill_cycle();

            DP (if (warmup_complete[packet->cpu] ) {
                    cout << "[" << NAME << "_MSHR] " <<  __func__ << " instr_id: " << MSHR.entry[mshr_index].instr_id;
                    cout << " address: " << hex << MSHR.entry[mshr_index].address << " full_addr: " << MSHR.entry[mshr_index].full_addr;
                    cout << " data: " << MSHR.entry[mshr_index].data << dec << " num_returned: " << MSHR.num_returned;
                    cout << " index: " << mshr_index << " occupancy: " << MSHR.occupancy;
                    if(MSHR.entry[mshr_index].read_translation_merged)
                    cout << " read_translation_merged ";
                    else if(MSHR.entry[mshr_index].write_translation_merged)
                    cout << " write_translation_merged ";
                    else if(MSHR.entry[mshr_index].prefetch_translation_merged)
                    cout << " prefetch_translation_merged ";

                    cout << " event: " << MSHR.entry[mshr_index].event_cycle << " current: " << current_core_cycle[packet->cpu] << " next: " << MSHR.next_fill_cycle << endl; });

#ifdef PRINT_QUEUE_TRACE
            if(packet->instr_id == QTRACE_INSTR_ID)
            {
                cout << "[" << NAME << "_MSHR] " <<  __func__ << " instr_id: " << MSHR.entry[mshr_index].instr_id;
                cout << " address: " << hex << MSHR.entry[mshr_index].address << " full_addr: " << MSHR.entry[mshr_index].full_addr;
                cout << " data: " << MSHR.entry[mshr_index].data << dec << " num_returned: " << MSHR.num_returned;
                cout << " index: " << mshr_index << " occupancy: " << MSHR.occupancy;
                cout << " event: " << MSHR.entry[mshr_index].event_cycle << " current: " << current_core_cycle[packet->cpu] << " next: " << MSHR.next_fill_cycle << endl;

            }
#endif

        }

        void CACHE::update_fill_cycle()
        {
            // update next_fill_cycle

            uint64_t min_cycle = UINT64_MAX;
            uint32_t min_index = MSHR.SIZE;
            for (uint32_t i=0; i<MSHR.SIZE; i++) {
                if ((MSHR.entry[i].returned == COMPLETED) && (MSHR.entry[i].event_cycle < min_cycle)) {
                    min_cycle = MSHR.entry[i].event_cycle;
                    min_index = i;
                }

                DP (if (warmup_complete[MSHR.entry[i].cpu] ) {
                        cout << "[" << NAME << "_MSHR] " <<  __func__ << " checking instr_id: " << MSHR.entry[i].instr_id;
                        cout << " address: " << hex << MSHR.entry[i].address << " full_addr: " << MSHR.entry[i].full_addr;
                        cout << " data: " << MSHR.entry[i].data << dec << " returned: " << +MSHR.entry[i].returned << " fill_level: " << MSHR.entry[i].fill_level;
                        cout << " index: " << i << " occupancy: " << MSHR.occupancy;
                        cout << " event: " << MSHR.entry[i].event_cycle << " current: " << current_core_cycle[MSHR.entry[i].cpu] << " next: " << MSHR.next_fill_cycle << endl; });
            }

            MSHR.next_fill_cycle = min_cycle;
            MSHR.next_fill_index = min_index;
            if (min_index < MSHR.SIZE) {

                DP (if (warmup_complete[MSHR.entry[min_index].cpu] ) {
                        cout << "[" << NAME << "_MSHR] " <<  __func__ << " instr_id: " << MSHR.entry[min_index].instr_id;
                        cout << " address: " << hex << MSHR.entry[min_index].address << " full_addr: " << MSHR.entry[min_index].full_addr;
                        cout << " data: " << MSHR.entry[min_index].data << dec << " num_returned: " << MSHR.num_returned;
                        cout << " event: " << MSHR.entry[min_index].event_cycle << " current: " << current_core_cycle[MSHR.entry[min_index].cpu] << " next: " << MSHR.next_fill_cycle << endl;});
            }
        }

        //@Vishal: Made check_mshr generic; packet_direction (Required only for MSHR) =>true, going to lower level else coming from lower level
        int CACHE::check_nonfifo_queue(PACKET_QUEUE *queue, PACKET *packet, bool packet_direction)
        {
            uint64_t check_address = packet->address;

            //@Vishal: packet_direction will be true only for return_data function. We don't need to check address translation for that.
            if(!packet_direction && (cache_type == IS_L1I || cache_type == IS_L1D) && queue->NAME.compare(NAME+"_MSHR") == 0)
            {
                if(packet->full_physical_address == 0)
                {
                    assert(packet->full_physical_address != 0); //@Vishal: If MSHR is checked, then address translation should be present 
                }

                if(packet->address != (packet->full_physical_address >> LOG2_BLOCK_SIZE))
                    check_address = packet->full_physical_address >> LOG2_BLOCK_SIZE; //@Vishal: L1 MSHR has physical address
            }

            if(cache_type == IS_L1D && queue->NAME.compare(NAME+"_WQ") == 0)
            {
                // search queue
                for (uint32_t index=0; index < queue->SIZE; index++) {
                    if (queue->entry[index].full_addr == packet->full_addr) {

                        DP ( if (warmup_complete[packet->cpu]) {
                                cout << "[" << NAME << "_" << queue->NAME << "] " << __func__ << " same entry instr_id: " << packet->instr_id << " prior_id: " << queue->entry[index].instr_id;
                                cout << " address: " << hex << packet->address;
                                cout << " full_addr: " << packet->full_addr << dec << endl; });

                        return index;
                    }
                }

            }
            else
            {
                // search queue
                for (uint32_t index=0; index < queue->SIZE; index++) {
                    if (queue->entry[index].address == check_address) {

                        DP ( if (warmup_complete[packet->cpu]) {
                                cout << "[" << NAME << "_" << queue->NAME << "] " << __func__ << " same entry instr_id: " << packet->instr_id << " prior_id: " << queue->entry[index].instr_id;
                                cout << " address: " << hex << packet->address;
                                cout << " full_addr: " << packet->full_addr << dec << endl; });

                        return index;
                    }
                }
            }

            DP ( if (warmup_complete[packet->cpu]) {
                    cout << "[" << NAME << "_" << queue->NAME << "] " << __func__ << " new address: " << hex << packet->address;
                    cout << " full_addr: " << packet->full_addr << dec << endl; });

            DP ( if (warmup_complete[packet->cpu] && (queue->occupancy == queue->SIZE)) { 
                    cout << "[" << NAME << "_" << queue->NAME << "] " << __func__ << " mshr is full";
                    cout << " instr_id: " << packet->instr_id << " occupancy: " << queue->occupancy;
                    cout << " address: " << hex << packet->address;
                    cout << " full_addr: " << packet->full_addr << dec;
                    cout << " cycle: " << current_core_cycle[packet->cpu] << endl;});

            return -1;
        }

        //@Vishal: Made add_mshr generic
        void CACHE::add_nonfifo_queue(PACKET_QUEUE *queue, PACKET *packet)
        {
            uint32_t index = 0;

            packet->cycle_enqueued = current_core_cycle[packet->cpu];

            // search queue
            for (index=0; index < queue->SIZE; index++) {
                if (queue->entry[index].address == 0) {

                    queue->entry[index] = *packet;
                    queue->entry[index].returned = INFLIGHT;
                    queue->occupancy++;

                    DP ( if (warmup_complete[packet->cpu]) {
                            cout << "[" << NAME << "_" << queue->NAME << "] " << __func__ << " instr_id: " << packet->instr_id;
                            cout << " address: " << hex << packet->address << " full_addr: " << packet->full_addr << dec;
                            if(packet->read_translation_merged)
                            cout << " read_translation_merged ";
                            else if(packet->write_translation_merged)
                            cout << " write_translation_merged ";
                            else if(packet->prefetch_translation_merged)
                            cout << " prefetch_translation_merged ";
                            cout << " fill_level: " << queue->entry[index].fill_level;
                            cout << " index: " << index << " occupancy: " << queue->occupancy << endl; });


#ifdef PRINT_QUEUE_TRACE
                    if(packet->instr_id == QTRACE_INSTR_ID)
                    {
                        cout << "[" << NAME << "_MSHR] " << __func__ << " instr_id: " << packet->instr_id;
                        cout << " address: " << hex << packet->address << " full_addr: " << packet->full_addr << dec<<endl;
                        cout << " index: " << index << " occupancy: " << MSHR.occupancy << " cpu: "<<cpu<<endl;
                    }
#endif

                    break;
                }
            }
        }

        uint32_t CACHE::get_occupancy(uint8_t queue_type, uint64_t address)
        {
            if (queue_type == 0)
                return MSHR.occupancy;
            else if (queue_type == 1)
                return RQ.occupancy;
            else if (queue_type == 2)
                return WQ.occupancy;
            else if (queue_type == 3)
                return PQ.occupancy;

            return 0;
        }

        uint32_t CACHE::get_size(uint8_t queue_type, uint64_t address)
        {
            if (queue_type == 0)
                return MSHR.SIZE;
            else if (queue_type == 1)
                return RQ.SIZE;
            else if (queue_type == 2)
                return WQ.SIZE;
            else if (queue_type == 3)
                return PQ.SIZE;

            return 0;
        }

        void CACHE::increment_WQ_FULL(uint64_t address)
        {
            WQ.FULL++;
        }

        void CACHE::initialize_phantom_cache() {
            // Set PhantomCache flag
            is_phantom_cache = true;
            num_candidate_sets = 8;  // Default number of candidate sets

            // Initialize random salts for mapping
            for (int i = 0; i < 8; i++) {
                salts[i][0] = rand() % (1ULL << 32);  // Left salt
                salts[i][1] = rand() % (1ULL << 32);  // Right salt
            }

            // Reset all blocks' salt indices and candidate sets
            for (uint32_t i = 0; i < NUM_SET; i++) {
                for (uint32_t j = 0; j < NUM_WAY; j++) {
                    block[i][j].salt_index = 0;
                    for (int k = 0; k < 8; k++) {
                        block[i][j].candidate_sets[k] = 0;
                    }
                }
            }

            cout << "[" << NAME << "] Initialized as PhantomCache with " << num_candidate_sets << " candidate sets" << endl;
        }

        uint64_t CACHE::compute_hash(uint64_t input, uint64_t salt_left, uint64_t salt_right) {
            // Implement LFSR-based Toeplitz hash
            uint64_t result = 0;
            uint64_t lfsr = (salt_left << 32) | salt_right;
            uint64_t tap_positions = 0xD0000001U; // Standard tap positions for 64-bit LFSR

            // Process each bit of input
            for (int i = 0; i < 64; i++) {
                // If current input bit is 1, XOR the result with current LFSR state
                if (input & (1ULL << i)) {
                    result ^= lfsr;
                }

                // Update LFSR state
                uint64_t feedback = __builtin_popcountll(lfsr & tap_positions) & 1;
                lfsr = (lfsr >> 1) | (feedback << 63);
            }

            return result;
        }

        uint32_t CACHE::get_candidate_sets(uint64_t address, uint64_t *candidate_sets) {
            // Extract the set index bits from the address
            uint64_t set_bits = log2(NUM_SET);
            uint64_t set_mask = (1ULL << set_bits) - 1;
            uint64_t original_set = address & set_mask;

            // Generate candidate sets using localized randomization
            for (uint32_t i = 0; i < num_candidate_sets; i++) {
                // Compute hash using the current salt pair
                uint64_t hash = compute_hash(address, salts[i][0], salts[i][1]);

                // Extract set index from hash, keeping it close to the original set
                uint64_t delta = (hash & 0xFF) % (NUM_SET / 8);  // Localized within 1/8th of cache
                uint64_t candidate_set = (original_set + delta) % NUM_SET;

                candidate_sets[i] = candidate_set;
            }

            return num_candidate_sets;
        }

        uint32_t CACHE::select_candidate_set(uint64_t *candidate_sets) {
            // Simple round-robin selection among candidate sets
            static uint32_t current_index = 0;
            uint32_t selected_set = candidate_sets[current_index];
            current_index = (current_index + 1) % num_candidate_sets;

            // Find the set with the most invalid or least recently used blocks
            uint32_t best_set = selected_set;
            uint32_t max_invalid = 0;
            uint32_t max_lru = 0;

            for (uint32_t i = 0; i < num_candidate_sets; i++) {
                uint32_t set = candidate_sets[i];
                uint32_t invalid_count = 0;
                uint32_t max_lru_in_set = 0;

                // Count invalid blocks and find highest LRU value
                for (uint32_t way = 0; way < NUM_WAY; way++) {
                    if (!block[set][way].valid) {
                        invalid_count++;
                    }
                    if (block[set][way].lru > max_lru_in_set) {
                        max_lru_in_set = block[set][way].lru;
                    }
                }

                // Update best set if we find more invalid blocks or higher LRU
                if (invalid_count > max_invalid || 
                    (invalid_count == max_invalid && max_lru_in_set > max_lru)) {
                    max_invalid = invalid_count;
                    max_lru = max_lru_in_set;
                    best_set = set;
                }
            }

            return best_set;
        }

        uint64_t CACHE::restore_address(uint32_t set, uint32_t way) {
            // Get the block at the specified set and way
            if (!block[set][way].valid) {
                return 0;  // Invalid block
            }

            // Get the original address and salt index stored in the block
            uint64_t stored_addr = block[set][way].address;
            uint8_t salt_idx = block[set][way].salt_index;

            // Verify the mapping using the stored salt
            uint64_t hash = compute_hash(stored_addr, salts[salt_idx][0], salts[salt_idx][1]);
            uint64_t set_bits = log2(NUM_SET);
            uint64_t set_mask = (1ULL << set_bits) - 1;
            uint64_t original_set = stored_addr & set_mask;
            uint64_t delta = (hash & 0xFF) % (NUM_SET / 8);
            uint64_t mapped_set = (original_set + delta) % NUM_SET;

            if (mapped_set != set) {
                // If mapping doesn't match, try all salts (fallback mechanism)
                for (uint32_t i = 0; i < num_candidate_sets; i++) {
                    hash = compute_hash(stored_addr, salts[i][0], salts[i][1]);
                    delta = (hash & 0xFF) % (NUM_SET / 8);
                    mapped_set = (original_set + delta) % NUM_SET;
                    if (mapped_set == set) {
                        // Update salt index if we find a match
                        block[set][way].salt_index = i;
                        break;
                    }
                }
            }

            return stored_addr;
        }

