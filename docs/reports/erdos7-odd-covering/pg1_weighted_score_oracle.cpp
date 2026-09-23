#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <limits>
#include <vector>

// Exact weighted-label extension of the PG1 signed-score oracle. The driver
// supplies every old layout and all six independent labels, including empty
// old classes and digit zero. The score table need not be convex or positive.
using I = int64_t;
struct State { int mask; std::array<int,16> load; };
std::array<std::array<std::vector<I>,16>,7> scores;
std::vector<State> states;
std::array<std::vector<int>,64> subsets;
int singleton_weight;

std::pair<I,I> optimize(const std::array<int,16>& a) {
    constexpr I neg = std::numeric_limits<I>::min()/4;
    I blocks[7][64];
    for(int y=0;y<7;y++) {
        std::fill(blocks[y],blocks[y]+64,neg);
        for(const auto& s:states) {
            I value=0, gain=0; // The PG1 cofactor45 has a realizable empty class.
            for(int i=0;i<16;i++) {
                const int k=a[i]+s.load[i];
                value+=scores[y][i][k];
                gain=std::max(gain,scores[y][i][k+singleton_weight]-scores[y][i][k]);
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
    if(argc!=3) return 2;
    std::ifstream in(argv[1]);
    int na,ns,maxload;
    if(!(in>>na>>ns>>maxload>>singleton_weight) || na<1 || ns!=3024 ||
       maxload<0 || singleton_weight<0 || singleton_weight>maxload) return 3;
    I score_bound=0;
    constexpr I guard_limit=(I(1)<<61)/4;
    for(auto& plane:scores) for(auto& row:plane) {
        row.resize(size_t(maxload)+1);
        I row_bound=0;
        for(auto& v:row) {
            if(!(in>>v) || v<=-guard_limit || v>=guard_limit) return 4;
            row_bound=std::max(row_bound,v<0 ? -v : v);
        }
        if(row_bound>=guard_limit-score_bound) return 4;
        score_bound+=row_bound;
    }
    states.resize(ns);
    int maxstate=0,maxold=0;
    for(auto& s:states) {
        if(!(in>>s.mask) || s.mask<0 || s.mask>=32) return 5;
        for(auto& v:s.load) {
            if(!(in>>v) || v<0 || v>maxload) return 5;
            maxstate=std::max(maxstate,v);
        }
    }
    std::vector<std::array<int,16>> old(na);
    for(auto& a:old) for(auto& v:a) {
        if(!(in>>v) || v<0 || v>maxload) return 6;
        maxold=std::max(maxold,v);
    }
    if(I(maxold)+maxstate+singleton_weight>maxload) return 7;
    for(int s=0;s<64;s++) for(int t=0;t<=s;t++) if((t&s)==t) subsets[s].push_back(t);
    std::ofstream out(argv[2]);
    const auto start=std::chrono::steady_clock::now();
    I best=std::numeric_limits<I>::min(); int winner=-1;
    for(int i=0;i<na;i++) {
        const auto result=optimize(old[i]);
        out<<i<<' '<<result.first<<' '<<result.second<<'\n';
        if(result.first>best) { best=result.first; winner=i; }
    }
    out.flush();
    if(!out) return 8;
    std::cout<<"{\"queries\":"<<na<<",\"seconds\":"
             <<std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()
             <<",\"maximum_numerator\":"<<best<<",\"maximizing_A_index\":"<<winner<<"}\n";
}
