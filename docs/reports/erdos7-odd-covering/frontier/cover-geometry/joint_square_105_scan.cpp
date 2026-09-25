// Exhaustive joint 105/147/245 boundary scan. Coefficients are directed
// rational roundings supplied by the companion producer; every arithmetic
// operation affecting the certificate is a bounded signed integer operation.
#include <algorithm>
#include <array>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <limits>
#include <stdexcept>
#include <string>
#include <vector>
using I = std::int64_t;
constexpr I SCREEN_DENOMINATOR = 87091200;
struct Block { int row, column, equal; std::vector<std::array<int,8>> points; };

I read_nonnegative(std::istream& input) {
    std::string text;
    if (!(input >> text) || text.empty()) throw std::runtime_error("missing integer");
    I value=0;
    for(char c:text) {
        if(c<'0' || c>'9' || value>(std::numeric_limits<I>::max()-(c-'0'))/10)
            throw std::runtime_error("invalid or overflowing integer");
        value=10*value+(c-'0');
    }
    return value;
}
std::array<int,6> screens(const int* g,int t) {
    int s0=g[0]+g[1]+g[2]+g[3],s1=g[4]+g[5]+g[6]+g[7];
    int m0=std::max({g[0],g[1],g[2],g[3]}),m1=std::max({g[4],g[5],g[6],g[7]});
    int cm=0;
    for(int j=0;j<4;++j)cm=std::max(cm,t*g[j]+(3-t)*g[j+4]);
    return {t*s0+(3-t)*s1,4*cm,std::max(t*s0,(3-t)*s1),std::max(s0,s1),4*std::max(t*m0,(3-t)*m1),4*std::max(m0,m1)};
}
int main(int argc,char**argv) {
 try {
    if(argc!=2)throw std::runtime_error("usage: engine coefficient-file");
    std::ifstream input(argv[1]);
    if(!input)throw std::runtime_error("cannot open input");
    const I scale=read_nonnegative(input),gain=read_nonnegative(input);
    if(scale!=1000000000 || gain!=11551020408)throw std::runtime_error("wrong scale or directed gain");
    std::array<I,192> coefficient;
    __int128 bound=gain;
    for(auto &c:coefficient){c=read_nonnegative(input);bound+=c;}
    if(bound*SCREEN_DENOMINATOR>=std::numeric_limits<I>::max())throw std::runtime_error("unsafe accumulation");
    if(read_nonnegative(input)!=8)throw std::runtime_error("expected eight root types");
    const int sizes[8]={374,347,416,320,347,277,410,311};
    std::vector<Block> blocks(8);
    for(int bi=0;bi<8;++bi) {
        auto& b=blocks[bi];
        const I row_value=read_nonnegative(input),column_value=read_nonnegative(input),equal_value=read_nonnegative(input);
        if(row_value>1 || column_value>1 || equal_value>1)throw std::runtime_error("invalid root identifier");
        b.row=int(row_value);b.column=int(column_value);b.equal=int(equal_value);
        I size=read_nonnegative(input);
        if(b.row!=bi/4 || b.column!=(bi/2)%2 || b.equal!=bi%2 || size!=sizes[bi])
            throw std::runtime_error("invalid root type or vector count");
        b.points.resize(size);
        for(auto &p:b.points){for(int &x:p){I v=read_nonnegative(input);if(v>210)throw std::runtime_error("invalid factor");x=int(v);}if(p[0]!=0)throw std::runtime_error("central cell not deleted");}
    }
    std::string extra;if(input>>extra)throw std::runtime_error("extra input");
    I minimum=std::numeric_limits<I>::max();
    int best_code=-1,best_block=-1,best_vector=-1,best_t=-1;
    std::uint64_t cases=0;
    const int caps[4]={10,12,16,18};
    // No sampling switch: each one of the16^4 named outside layouts occurs.
    for(int code=0;code<65536;++code) {
        int rem=code,row[4],column[4],equal[4];
        for(int q=0;q<4;++q){int v=rem&15;rem>>=4;row[q]=v&1;column[q]=(v>>1)&3;equal[q]=(v>>3)&1;}
        int grid[16][8];
        for(int k=0;k<8;++k) {
            int factor[4];
            for(int q=0;q<4;++q){int a=k/4==row[q],b=k%4==column[q];factor[q]=caps[q]-a-b+equal[q]*a*b;}
            for(int mask=0;mask<16;++mask){int g=k?1:0;for(int q=0;q<4;++q)g*=((mask>>q)&1)?caps[q]:factor[q];grid[mask][k]=g;}
        }
        for(int t=1;t<=2;++t) {
            I constant=0;
            // Query support containing7 drops its whole local block.
            for(int mask=0;mask<16;++mask){auto s=screens(grid[mask],t);for(int mode=0;mode<6;++mode)constant-=coefficient[mode*32+2*mask+1]*s[mode]*210;}
            for(int bi=0;bi<8;++bi) {
                const auto& block=blocks[bi];
                for(int vi=0;vi<int(block.points.size());++vi) {
                    const auto& p=block.points[vi];I gate=constant;
                    for(int mask=0;mask<16;++mask) {
                        int g[8];for(int k=0;k<8;++k)g[k]=grid[mask][k]*p[k];
                        auto s=screens(g,t);
                        if(mask==0)gate+=gain*s[0];
                        for(int mode=0;mode<6;++mode)gate-=coefficient[mode*32+2*mask]*s[mode];
                    }
                    ++cases;
                    if(gate<minimum){minimum=gate;best_code=code;best_block=bi;best_vector=vi;best_t=t;}
                }
            }
        }
    }
    std::cout<<cases<<' '<<minimum<<' '<<scale*SCREEN_DENOMINATOR<<' '<<best_code<<' '<<best_block<<' '<<best_vector<<' '<<best_t<<'\n';
    return 0;
 }catch(const std::exception& error){std::cerr<<error.what()<<'\n';return 1;}
}
