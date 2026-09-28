// Independent audit evaluator. The 27-residue is optimized by row gains;
// the other five residues are enumerated. No histogram or incidence encoding.
#include <algorithm>
#include <array>
#include <iostream>
#include <limits>
#include <vector>
using I = long long;
struct Q { I id, den, base, c[6], single, threshold; };
int main() {
    int n;
    if (!(std::cin >> n) || n < 1 || n > 135) return 1;
    std::vector<int> x(n), w(n), offset(n), row(n);
    for (int i=0; i<n; ++i) {
        std::cin >> x[i] >> w[i] >> offset[i];
        if (x[i]<0 || x[i]>=135 || w[i]<0) return 2;
    }
    std::vector<int> rows;
    for (int v:x) rows.push_back(v%27);
    std::sort(rows.begin(),rows.end());
    rows.erase(std::unique(rows.begin(),rows.end()),rows.end());
    int nr=rows.size();
    for (int i=0;i<n;++i)
        row[i]=std::lower_bound(rows.begin(),rows.end(),x[i]%27)-rows.begin();
    const int mod[5]={3,9,5,15,45}, ci[5]={0,1,3,4,5};
    std::array<std::vector<int>,5> residues;
    for (int d=0;d<5;++d) {
        for (int v:x) residues[d].push_back(v%mod[d]);
        std::sort(residues[d].begin(),residues[d].end());
        residues[d].erase(std::unique(residues[d].begin(),residues[d].end()),residues[d].end());
    }
    Q q;
    while (std::cin >> q.id >> q.den >> q.base >> q.c[0] >> q.c[1]
           >> q.c[2] >> q.c[3] >> q.c[4] >> q.c[5] >> q.single >> q.threshold) {
        if(q.single<0 || q.den<=0) return 3;
        for(I a:q.c) if(a<0) return 4;
        std::vector<I> values(n);
        for(int i=0;i<n;++i) values[i]=q.base-q.threshold+offset[i];
        I best=0;
        auto visit=[&](auto&& self,int d)->void {
            if(d<5) {
                for(int r:residues[d]) {
                    for(int i=0;i<n;++i) if(x[i]%mod[d]==r) values[i]+=q.c[ci[d]];
                    self(self,d+1);
                    for(int i=0;i<n;++i) if(x[i]%mod[d]==r) values[i]-=q.c[ci[d]];
                }
                return;
            }
            I sum=0, delta[27]={}, plain[27]={}, added[27]={};
            for(int i=0;i<n;++i) {
                I a=values[i], b=a+q.c[2];
                I pa=std::max(I(0),a), pb=std::max(I(0),b);
                sum+=w[i]*pa;
                delta[row[i]]+=w[i]*(pb-pa);
                plain[row[i]]=std::max(plain[row[i]],w[i]*(std::max(I(0),a+q.single)-pa));
                added[row[i]]=std::max(added[row[i]],w[i]*(std::max(I(0),b+q.single)-pb));
            }
            I largest=0,second=0; int owner=-1;
            for(int r=0;r<nr;++r) {
                if(plain[r]>=largest) {second=largest;largest=plain[r];owner=r;}
                else second=std::max(second,plain[r]);
            }
            for(int r=0;r<nr;++r) {
                I outside=(r==owner ? second:largest);
                best=std::max(best,sum+delta[r]+std::max(added[r],outside));
            }
        };
        visit(visit,0);
        std::cout << q.id << ' ' << q.den << ' ' << best << '\n';
    }
}
