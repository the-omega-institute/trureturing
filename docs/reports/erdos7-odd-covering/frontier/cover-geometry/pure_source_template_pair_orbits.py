#!/usr/bin/env python3
"""Source-stabilizer orbits for the twenty pure-source corners.

No gate is evaluated. All permutations act simultaneously on both ordered
central templates. The source corner, central15 mask and full query menus
are preserved. Ordinary finite orbit certificate; not Lean verification.
"""
from dataclasses import dataclass
from functools import lru_cache
from itertools import product, permutations
from collections import Counter
from pathlib import Path
import argparse, json, hashlib

THREE=((0,1),(0,3),(3,4),(3,0))
FIVE=((0,1),(0,5),(5,6),(5,0),(5,10))
POINTS=tuple((i,j) for i in range(2) for j in range(4) if (i,j)!=(0,0))
CASES=tuple((z,w,zz,ww) for (z,w),(zz,ww) in product(THREE,FIVE))

@dataclass(frozen=True)
class LeafPairOrbit:
    first: int
    second: int
    size: int

@dataclass(frozen=True)
class QPairOrbit:
    # (C,I,J,M,C2,I2,J2,M2)
    key: tuple
    size: int
    # Each item is (target C, target C2, a realizable transported Q key).
    column_images: tuple

@dataclass(frozen=True)
class PairOrbit:
    first_id: int
    second_id: int
    size: int
    # Each item is (target C, target C2, transported first id, second id).
    column_images: tuple


def leaf_groups(blocks,width,null,weak):
    groups=[tuple(k for k in range(width*j,width*(j+1)) if k not in (null,weak)) for j in range(blocks)]
    groups.append((weak,))
    return tuple(g for g in groups if g)


def leaf_lookup(groups):
    return {leaf:g for g in groups for leaf in g}


def normalize_leaf_pair(x,y,lookup):
    a,b=lookup[x],lookup[y]
    if a!=b:return a[0],b[0]
    return (a[0],a[0]) if x==y else (a[0],a[1])


def leaf_pair_size(x,y,lookup):
    a,b=lookup[x],lookup[y]
    return len(a)*len(b) if a!=b else len(a) if x==y else len(a)*(len(a)-1)


@lru_cache(None)
def leaf_pair_orbits(blocks,width,null,weak):
    lookup=leaf_lookup(leaf_groups(blocks,width,null,weak))
    keys=sorted({normalize_leaf_pair(x,y,lookup) for x,y in product(lookup,repeat=2)})
    return tuple(LeafPairOrbit(x,y,leaf_pair_size(x,y,lookup)) for x,y in keys)


@lru_cache(None)
def column_permutations(null,weak):
    sig=tuple((int(j==null//5),int(j==weak//5)) for j in range(4))
    return tuple(perm for perm in permutations(range(4)) if perm[0]==0 and all(sig[j]==sig[perm[j]] for j in range(4)))


def transport_leaf_by_column(m,perm):
    # Marker columns are fixed. Normal columns have all five ordinary leaves,
    # and matching equal child indices is one explicit permissible transport.
    return 5*perm[m//5]+m%5


class QOrbitAction:
    def __init__(self,null,weak):
        self.null,self.weak=null,weak
        self.lookup=leaf_lookup(leaf_groups(4,5,null,weak))
        self.perms=column_permutations(null,weak)
        self.leaf_orbits=leaf_pair_orbits(4,5,null,weak)
        self.maps={}
        for row in self.leaf_orbits:
            self.maps[(row.first,row.second)]=tuple(normalize_leaf_pair(transport_leaf_by_column(row.first,p),transport_leaf_by_column(row.second,p),self.lookup) for p in self.perms)

    def images(self,key):
        C,I,J,M,D,K,L,N=key
        M,N=normalize_leaf_pair(M,N,self.lookup)
        return tuple((p[C],I,p[J],m,p[D],K,p[L],n) for p,(m,n) in zip(self.perms,self.maps[(M,N)]))

    def canonical(self,key):
        return min(self.images(key))


@lru_cache(None)
def quinary_pair_orbits(null,weak):
    action=QOrbitAction(null,weak)
    roots=tuple((C,I,J) for C in range(4) for I,J in POINTS)
    result=[]
    for (C,I,J),(D,K,L),row in product(roots,roots,action.leaf_orbits):
        key=(C,I,J,row.first,D,K,L,row.second)
        images=set(action.images(key))
        if key!=min(images):continue
        column_images={}
        for image in sorted(images):
            column_images.setdefault((image[0],image[4]),image)
        size=row.size*len(images)
        result.append(QPairOrbit(key,size,tuple((c,d,image) for (c,d),image in sorted(column_images.items()))))
    return tuple(result)


@lru_cache(None)
def templates(case):
    z,w,zz,ww=case
    return tuple((R,C,I,J,L,M) for R,C,(I,J),L,M in product(range(2),range(4),POINTS,[l for l in range(6) if l!=z],[m for m in range(20) if m!=zz]))


def ordered_template_pair_orbits(case):
    """Yield exact ordered-pair representatives and every shared-C table fill.

    Template IDs use the same product order as the twenty-source gate probe.
    One evaluation may be copied only to this record's column_images.
    The corresponding transported IDs are valid witnesses for those entries.
    """
    z,w,zz,ww=case
    ts=templates(case);ids={t:i for i,t in enumerate(ts)}
    for qo,lo,R,S in product(quinary_pair_orbits(zz,ww),leaf_pair_orbits(2,3,z,w),range(2),range(2)):
        C,I,J,M,D,K,L,N=qo.key
        t=(R,C,I,J,lo.first,M);u=(S,D,K,L,lo.second,N)
        fills=[]
        for c,d,key in qo.column_images:
            cc,ii,jj,mm,dd,kk,ll,nn=key
            fills.append((c,d,ids[(R,cc,ii,jj,lo.first,mm)],ids[(S,dd,kk,ll,lo.second,nn)]))
        yield PairOrbit(ids[t],ids[u],lo.size*qo.size,tuple(fills))


def first_template_orbit_count(case):
    z,w,zz,ww=case
    action=QOrbitAction(zz,ww)
    ll=leaf_lookup(leaf_groups(2,3,z,w));ml=action.lookup
    def canon(t):
        R,C,I,J,L,M=t
        return min((R,p[C],I,p[J],ll[L][0],ml[transport_leaf_by_column(M,p)][0]) for p in action.perms)
    return len({canon(t) for t in templates(case)})


def verify(output,exhaustive=False):
    checks={}
    def ck(name,condition):
        if not condition:raise ArithmeticError(name)
        checks[name]=True
    qstats=[]
    for index,(z,w) in enumerate(FIVE):
        action=QOrbitAction(z,w);reps=quinary_pair_orbits(z,w)
        ck(f'q{index}_leaf_normal_forms',len(action.leaf_orbits)==29 and sum(r.size for r in action.leaf_orbits)==19**2)
        ck(f'q{index}_orbit_partition',sum(r.size for r in reps)==(4*7*19)**2)
        ck(f'q{index}_unique_representatives',len({r.key for r in reps})==len(reps))
        hist=Counter()
        for row in reps:
            ckkey=len(row.column_images)
            if row.size%ckkey:raise ArithmeticError('nonintegral column fiber')
            for c,d,_ in row.column_images:hist[c,d]+=row.size//ckkey
        ck(f'q{index}_all_16_column_fibers',hist==Counter({(c,d):133**2 for c in range(4) for d in range(4)}))
        # Source weights, distinguished mask and root partition are preserved
        # by every outer column permutation; inner groups are equal-weight
        # leaves in one root by construction.
        W=[0 if k==z else 3 if k==w else 4 for k in range(20)]
        ck(f'q{index}_source_covariance',all(all(W[k]==W[transport_leaf_by_column(k,p)] for k in range(20)) and p[0]==0 for p in action.perms))
        ck(f'q{index}_inner_source_covariance',all(len({W[k] for k in group})==1 and len({k//5 for k in group})==1 for group in leaf_groups(4,5,z,w)))
        if exhaustive:
            partial=tuple((C,I,J,M) for C,(I,J),M in product(range(4),POINTS,[m for m in range(20) if m!=z]))
            empirical=Counter(action.canonical(t+u) for t,u in product(partial,repeat=2))
            ck(f'q{index}_exhaustive_actual_pair_fibers',empirical==Counter({r.key:r.size for r in reps}))
        qstats.append({'source':[z,w],'column_group_size':len(action.perms),'leaf_pair_reps':29,'partial_pair_reps':len(reps),'partial_pair_weight_sum':sum(r.size for r in reps),'column_fiber_count':133**2})
    tstats=[]
    for index,(z,w) in enumerate(THREE):
        lo=leaf_pair_orbits(2,3,z,w)
        lookup=leaf_lookup(leaf_groups(2,3,z,w))
        actual=Counter(normalize_leaf_pair(x,y,lookup) for x,y in product([k for k in range(6) if k!=z],repeat=2))
        ck(f't{index}_exact_leaf_pair_fibers',actual==Counter({(r.first,r.second):r.size for r in lo}) and sum(r.size for r in lo)==25)
        tstats.append({'source':[z,w],'leaf_pair_reps':len(lo),'leaf_pair_weight_sum':25})
    cases=[]
    for index,case in enumerate(CASES):
        z,w,zz,ww=case;lo=leaf_pair_orbits(2,3,z,w);qo=quinary_pair_orbits(zz,ww)
        ts=templates(case);count=4*len(lo)*len(qo);total=4*sum(r.size for r in lo)*sum(r.size for r in qo)
        ck(f'case{index}_5320_templates',len(ts)==len(set(ts))==5320)
        ck(f'case{index}_5320_squared_coverage',total==5320**2)
        column_fiber=4*sum(r.size for r in lo)*133**2
        ck(f'case{index}_shared_columns',column_fiber==1330**2)
        # Exercise yielded API records, including transported witnesses,
        # at both ends of each independently factored orbit family.
        ids={t:i for i,t in enumerate(ts)}
        for qr in (qo[0],qo[-1]):
            C,I,J,M,D,K,L,N=qr.key
            for lr in (lo[0],lo[-1]):
                for c,d,img in qr.column_images:
                    cc,ii,jj,mm,dd,kk,ll,nn=img
                    for R,S in product(range(2),repeat=2):
                        tid=ids[(R,cc,ii,jj,lr.first,mm)];uid=ids[(S,dd,kk,ll,lr.second,nn)]
                        if ts[tid][1]!=c or ts[uid][1]!=d:raise ArithmeticError('column witness')
        ck(f'case{index}_transported_witness_API',True)
        cases.append({'case':index,'source':case,'templates':5320,'first_template_orbits':first_template_orbit_count(case),'ordered_template_pair_orbits':count,'sum_orbit_size':total,'each_shared_C_pair_actual_count':column_fiber,'column_group_size':len(column_permutations(zz,ww)),'positive_unmasked_cells':sum(l!=z and m!=zz and (l//3,m//5)!=(0,0) for l in range(6) for m in range(20))})
    result={'schema':'pure-source-twenty-template-pair-orbits-v1','scope':'Exact source-stabilizer orbits only; no continuation gate or Lean claim.','quinary_partial_orbits':qstats,'ternary_leaf_orbits':tstats,'cases':cases,'exhaustive_actual_partial_pair_audit':exhaustive,'checks':checks,'check_count':len(checks),'generator_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'new_lean_verification':False}
    output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'checks':len(checks),'ordered_pair_orbits':[r['ordered_template_pair_orbits'] for r in cases],'all_coverage':5320**2,'exhaustive':exhaustive}),flush=True)

if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'));ap.add_argument('--exhaustive',action='store_true');args=ap.parse_args();verify(args.output,args.exhaustive)
