#!/usr/bin/env python3
"""Exact all-domain enclosure of a five-direction scalar dual. Integer arithmetic only."""
from fractions import Fraction as F
from itertools import combinations, product
from math import prod
from pathlib import Path
from collections import Counter
import json
from hashlib import sha256
import runpy

R=(28,30,36,40,42)
D=512
Q=(1550,70,0,0,0)
C=(52,89,50,36,30)
TARGET=19700
TRIPLES=tuple(combinations(range(5),3))
MAX_NODES=10000000
CORNERS=tuple(product((0,1),repeat=5))
E=256000
DEPENDENCIES={'fibre_credit_depth_two_conditioned_convex_source.py': '4bf5f7610dc21b0b410074d54ee23f7d10a2d08c0c726c1827adad1da3bab251', 'fibre_credit_depth_two_conditioned_convex_source.json': '2b74e5eb1fbcacf2b9f9493affdc1df9ff17af6c8096df46a23d678d491df8a3'}

def require(ok,msg):
    if not ok:raise RuntimeError(msg)

def polynomial(a):return sum(Q[i]*a[i]*a[i]*D+C[i]*a[i]**3 for i in range(5))

def calculate():
    directory=Path(__file__).resolve().parent
    for name,digest in DEPENDENCIES.items():
        require(sha256((directory/name).read_bytes()).hexdigest()==digest,
                'pinned conditioned-convex source dependency: '+name)
    api=runpy.run_path(str(directory/'fibre_credit_depth_two_conditioned_convex_source.py'))
    source=json.loads(json.dumps(api['calculate']()))
    require(source==json.loads((directory/'fibre_credit_depth_two_conditioned_convex_source.json').read_text()),
            'replayed complete conditioned-convex source')
    nodes=0;leaves=0;vol=0;depths=Counter();branches=Counter();max_depth=0
    low=(D,)*5;high=tuple(v*D for v in R)
    stack=[(low,high,0)]
    while stack:
        lo,hi,depth=stack.pop();nodes+=1
        u=tuple(R[i]*D-hi[i] for i in range(5))
        p=prod(u)
        ds=sum(prod(u[i]*u[i] for i in J) for J in TRIPLES)
        poly=polynomial(lo)
        if ds==0:
            branch='zero';lhs=poly;rhs=TARGET*100*D**3
        elif 500*p*D<=ds:
            branch='quadratic';lhs=poly*ds*D+100*p*p;rhs=TARGET*100*ds*D**4
        else:
            branch='linear';lhs=poly*2500*D**3+1000*p*D-ds;rhs=TARGET*250000*D**6
        if lhs<rhs:
            center=tuple(lo[i]+hi[i] for i in range(5))
            uc=tuple(2*R[i]*D-center[i] for i in range(5))
            pc=prod(uc);mc=sum(prod(uc[i]*uc[i] for i in J) for J in TRIPLES)
            t=min(1024,(500*1024*pc*(2*D))//mc) if mc else 0
            constant=sum(Q[i]*center[i]**2*(2*D)+C[i]*center[i]**3 for i in range(5))
            derivative=tuple(2*Q[i]*center[i]*(2*D)+3*C[i]*center[i]**2 for i in range(5))
            tangent_rhs=TARGET*800*E**2*D**6
            accepted=True
            for choice in CORNERS:
                corner=tuple(hi[i] if choice[i] else lo[i] for i in range(5))
                uv=tuple(R[i]*D-corner[i] for i in range(5))
                pv=prod(uv);mv=sum(prod(uv[i]*uv[i] for i in J) for J in TRIPLES)
                linear=constant+sum(derivative[i]*(2*corner[i]-center[i]) for i in range(5))
                tangent_lhs=linear*E**2*D**3+800*E*t*pv*D-200*t*t*mv
                if tangent_lhs<tangent_rhs:
                    accepted=False;break
            if accepted:
                lhs=rhs;branch='convex-unary-tangent-and-concave-corners'
        if lhs>=rhs:
            leaves+=1;vol+=prod(hi[i]-lo[i] for i in range(5));depths[depth]+=1;branches[branch]+=1;max_depth=max(max_depth,depth)
        else:
            widths=tuple(hi[i]-lo[i] for i in range(5));j=max(range(5),key=lambda i:widths[i])
            require(widths[j]>1,'exhausted exact grid at '+str((lo,hi,depth,branch)))
            mid=(lo[j]+hi[j])//2
            hi1=list(hi);hi1[j]=mid;lo2=list(lo);lo2[j]=mid
            stack.append((tuple(lo2),hi,depth+1));stack.append((lo,tuple(hi1),depth+1))
        require(nodes<=MAX_NODES,'bounded node cap exceeded')
    volume=prod((R[i]-1)*D for i in range(5))
    require(vol==volume,'exact accepted-leaf volume equals original box')
    require(nodes==2*leaves-1,'every nonleaf has both binary children checked')
    exterior=min(F(Q[i]*R[i]**2+C[i]*R[i]**3+sum(Q)+sum(C)-Q[i]-C[i],100) for i in range(5))
    require(exterior>TARGET,'all outside faces certified by unary polynomial alone')
    G1,G2,G3=map(F,source['common_Y_moments_one_through_four'][:3])
    hcoef=sum(prod((R[i]-1 for i in J),start=1) for size in range(3) for J in combinations(range(5),size))
    budget=(F(sum(Q),100)+10)*G2+F(sum(C),100)*G3+F(hcoef,250)*G1
    EW=250*(TARGET-budget)
    density=F(104726,6084351)*EW/prod(R)
    require(hcoef==11794,'complement coefficient count')
    require(EW>0 and density>F(1,30000),'positive mean and conservative Haar reserve')
    out={'scope':'Ordinary exact integer enclosure with replayed same-source convex-comparison arithmetic. Inherited actual-source and carving proofs remain ordinary, not Lean.',
         'grid_denominator':D,'target':TARGET,'square_weights':list(map(str,(F(v,100) for v in Q))),
         'cube_weights':list(map(str,(F(v,100) for v in C))),'kappa':'1/250',
         'nodes':nodes,'leaves':leaves,'accepted_volume_numerator':str(vol),'box_volume_numerator':str(volume),
         'box_volume':prod(v-1 for v in R),'leaf_depths':dict(sorted(depths.items())),'branch_counts':dict(branches),'max_depth':max_depth,
         'outside_lower':str(exterior),'mean_cap':str(G1),'square_cap':str(G2),'cube_cap':str(G3),
         'budget':str(budget),'target_minus_budget':str(TARGET-budget),'mean_W_lower':str(EW),
         'Haar_lower':str(density),'Haar_lower_decimal':float(density),'simple_Haar_lower':'1/30000',
         'exact_all_domain_enclosure_passed':True}
    out['dependency_hashes']=DEPENDENCIES
    out['conditioned_convex_source_replayed']=True
    return out
def main():
    import argparse
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    result=json.loads(json.dumps(calculate()))
    rendered=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if args.output is None:
        require(json.loads(Path(__file__).resolve().with_suffix('.json').read_text())==result,
                'retained result agrees with five-direction all-domain enclosure')
        print(rendered,end='')
    else:
        args.output.write_text(rendered)


if __name__=='__main__':main()
