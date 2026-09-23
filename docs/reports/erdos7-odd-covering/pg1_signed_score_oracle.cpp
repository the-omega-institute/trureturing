#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <limits>
#include <vector>

// Integer port of ExactSignedDigitDP.optimize for the fixed PG1 geometry.
// All seven digits and all subset blocks participate. Empty singleton is legal.
// Raw-input contract: only the guarded adjacent Python driver should produce
// input. It verifies dimensions, the realizable geometry, exact integer scores,
// and 4 * sum_{y,i} max_k |score[y][i][k]| < 2^61 before invoking this program.
// Scores may have either sign and arbitrary curvature. This program optimizes
// one supplied score table; it does not certify completeness of outer profiles.
using I = int64_t;
struct State { int mask; std::array<int,16> load; };
I scores[7][16][13];
std::vector<State> states;
std::array<std::vector<int>,64> subsets;

std::pair<I,I> optimize(const std::array<int,16>& a) {
    constexpr I neg = std::numeric_limits<I>::min()/4;
    I blocks[7][64];
    for(int y=0;y<7;y++) {
        std::fill(blocks[y],blocks[y]+64,neg);
        for(const auto& s:states) {
            I value=0, gain=0;
            for(int i=0;i<16;i++) {
                const int k=a[i]+s.load[i];
                value+=scores[y][i][k];
                gain=std::max(gain,scores[y][i][k+1]-scores[y][i][k]);
            }
            blocks[y][s.mask]=std::max(blocks[y][s.mask],value);
            blocks[y][s.mask|32]=std::max(blocks[y][s.mask|32],value+gain);
        }
    }
    std::array<I,64> previous,current;
    previous.fill(neg); previous[0]=0;
    for(int y=0;y<7;y++) {
        current.fill(neg);
        for(int s=0;s<64;s++) for(int t:subsets[s]) {
            if(previous[s^t]!=neg)
                current[s]=std::max(current[s],previous[s^t]+blocks[y][t]);
        }
        previous=current;
    }
    I baseline=0,common=neg;
    for(int y=0;y<7;y++) baseline+=blocks[y][0];
    for(int y=0;y<7;y++) common=std::max(common,baseline-blocks[y][0]+blocks[y][63]);
    return {previous[63],common};
}

int main(int argc,char** argv) {
    if(argc!=3) { std::cerr<<"usage: solver guarded_input all_A_values_output\n"; return 2; }
    std::ifstream in(argv[1]);
    int na,ns; in>>na>>ns;
    if(na!=11808 || ns!=3024) return 3;
    for(auto& plane:scores) for(auto& row:plane) for(auto& v:row) in>>v;
    states.resize(ns);
    for(auto& s:states) {
        in>>s.mask;
        if(s.mask<0 || s.mask>=32) return 4;
        for(auto& v:s.load) { in>>v; if(v<0 || v>5) return 5; }
    }
    std::vector<std::array<int,16>> old(na);
    for(auto& a:old) for(auto& v:a) { in>>v; if(v<0 || v>6) return 6; }
    if(!in) return 7;
    for(int s=0;s<64;s++) for(int t=0;t<=s;t++) if((t&s)==t) subsets[s].push_back(t);
    const int limit=na;
    std::ofstream out(argv[2]);
    const auto start=std::chrono::steady_clock::now();
    I best=std::numeric_limits<I>::min(); int winner=-1;
    for(int i=0;i<limit;i++) {
        const auto result=optimize(old[i]);
        out<<i<<' '<<result.first<<' '<<result.second<<'\n';
        if(result.first>best) { best=result.first; winner=i; }
    }
    out.flush();
    if(!out) return 8;
    std::cout<<"{\"queries\":"<<limit<<",\"seconds\":"
             <<std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()
             <<",\"maximum_numerator\":"<<best<<",\"maximizing_A_index\":"<<winner<<"}\n";
}
