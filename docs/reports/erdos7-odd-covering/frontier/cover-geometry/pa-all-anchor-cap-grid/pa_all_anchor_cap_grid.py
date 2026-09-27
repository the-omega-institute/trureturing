"""All 15 PA anchor pairs and complete unrefined constant-cap/order grid.
Each grid point is one law/order; the subset DP minimizes comparison debits,
not the actual state. Every hinge includes its full first moment.
"""
from fractions import Fraction as F
from functools import lru_cache
from itertools import combinations,product,permutations
from math import prod
from pathlib import Path
import argparse,json,hashlib
P=(5,7,11,13,17,19);INC=F(157471921154183512277,30602497889515978126);T=F(257,51)
arg=argparse.ArgumentParser(description=__doc__);arg.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'));args=arg.parse_args();N=F;zero=N(0);one=N(1)
checks={}
def require(name,p):
 checks[name]=bool(p)
 if not p:raise ValueError(name)

def run_pair(anchor):
    later=tuple(p for p in P if p not in anchor);ranges=tuple(range((p-1)//2) for p in later)
    anchor_coords=tuple((p,one,N(2,p-1)) for p in anchor);mixed=N(2,(anchor[0]-1)*(anchor[1]-1));W=prod(1-u for _,_,u in anchor_coords);startmass=W-mixed
    @lru_cache(None)
    def hinge(coords,t):
        mass=mean=one;low={1:one} if t>1 else {}
        for p,c,u in coords:
            mass*=1-u;mean*=1-u+c/(p-1)
            probs={1:1-u-c/p};probs.update({n:c*N(p-1,p**n) for n in range(2,t)})
            nxt={}
            for a,v in low.items():
                for b,w in probs.items():
                    if a*b<t:nxt[a*b]=nxt.get(a*b,zero)+v*w
            low=nxt
        return mean-t*mass+sum(((t-m)*v for m,v in low.items()),zero)
    rows=0;positive=0;best=None;digest=hashlib.sha256();bestedge=None
    for ts in product(*ranges):
        caps=tuple(N(p-1,p-1-2*t) for p,t in zip(later,ts));debit=tuple(N(2,p-1-2*t) for p,t in zip(later,ts))
        coords={mask:anchor_coords+tuple((p,c,zero) for i,(p,c) in enumerate(zip(later,caps)) if mask>>i&1) for mask in range(16)}
        edges={(mask,i):debit[i]*hinge(coords[mask],ts[i]) for mask in range(16) for i in range(4) if not(mask>>i&1)}
        dp={0:zero};paths={0:()}
        for mask in range(1,16):
            cost,path=min((dp[mask^(1<<i)]+edges[mask^(1<<i),i],paths[mask^(1<<i)]+(i,)) for i in range(4) if mask>>i&1)
            dp[mask]=cost;paths[mask]=path
        alpha=startmass-dp[15];row={'thresholds':ts,'alpha':alpha,'loss':dp[15]};rows+=1
        if alpha>0:
            positive+=1;query,h=min((h-1+hinge(coords[15],h)/alpha,h) for h in range(1,7));row.update({'query':query,'h':h,'order':tuple(later[i] for i in paths[15])})
            key=(query,ts,h,row['order'])
            if best is None or key<best[0]:
                best=(key,{**row,'anchors':anchor,'anchor_pure_masses':tuple(1-u for _,_,u in anchor_coords),'anchor_mixed_charge':mixed,'later_primes':later,'caps':caps,'Phi':hinge(coords[15],h)});bestedge=edges.copy()
        digest.update(json.dumps(row,sort_keys=True,default=str,separators=(',',':')).encode());digest.update(b'\n')
    require('full_grid_'+str(anchor),rows==prod(len(r) for r in ranges))
    # Enumerate all24 orders independently at this pair's winner.
    explicit=[];wr=best[1]
    for order in permutations(range(4)):
        mask=0;loss=zero
        for i in order:loss+=bestedge[mask,i];mask|=1<<i
        explicit.append((loss,tuple(later[i] for i in order)))
    require('pair_DP_24_orders_'+str(anchor),wr['loss']==min(explicit)[0])
    summary={'anchors':anchor,'tuples':rows,'positive_tuples':positive,'grid_result_sha256':digest.hexdigest(),'winner':wr,'hinge_cache_entries':hinge.cache_info().currsize}
    print(json.dumps({'anchors':anchor,'tuples':rows,'positive':positive,'query':float(wr['query']),'thresholds':wr['thresholds'],'order':wr['order'],'h':wr['h']},default=str),flush=True)
    return summary
pairs=[]
for anchor in combinations(P,2):pairs.append(run_pair(anchor))
winner=min((r['winner'] for r in pairs),key=lambda r:(r['query'],r['anchors'],r['thresholds'],r['h'],r['order']))
require('all15_pairs',len(pairs)==15);require('all10404_cap_tuples',sum(p['tuples'] for p in pairs)==10404)
base=pairs[0]['winner'];require('fixed57_560_recovered',base['query']==INC)
require('global_comparison_to_incumbent_consistent',all(winner['query']<=r['winner']['query'] for r in pairs))
require('all4546_positive_tuples',sum(r['positive_tuples'] for r in pairs)==4546)
require('target_not_crossed',winner['query']>T)
for r in pairs:require('no_improvement_'+str(r['anchors']),r['winner']['query']>=INC)
out={'scope':'Specified unrefined PA constant-cap comparison certificate, all15 anchor pairs, all integer cap endpoints and all24 fixed later orders; no optimization over actual laws or adaptive schedules.','arithmetic':'exact Fraction','Q':P,'total_anchor_pairs':15,'total_cap_tuples':10404,'query_h_values':list(range(1,7)),'incumbent560':str(INC),'target':str(T),'winner':winner,'strict_improvement':winner['query']<N(INC.numerator,INC.denominator),'crosses_target':winner['query']<N(T.numerator,T.denominator),'per_pair':pairs,'checks':checks,'check_count':len(checks)}
Path(args.output).write_text(json.dumps(out,indent=2,default=str)+'\n');print(json.dumps({'winner':winner,'strict_improvement':out['strict_improvement'],'check_count':len(checks),'output':args.output},indent=2,default=str))
