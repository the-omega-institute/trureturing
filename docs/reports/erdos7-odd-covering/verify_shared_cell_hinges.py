#!/usr/bin/env python3
"""Exact shared actual-cell hinges for all original 3/5/7 heights.

Python 3.9+ standard library only. The ordinary proof gives the original-
label convex increment, complete geometric tails and continuous-domain
vertex argument. This program checks every parameter vertex and all
12 missing-class branches against the pinned preceding PR certificate.
"""
from fractions import Fraction as F
from functools import lru_cache
from itertools import product
from math import lcm
from pathlib import Path
import argparse
import hashlib
import json

Q=F
BASE=Path(__file__).resolve().parent
PINNED_PR_SHA256='eafd30f891efcf166eed4c10f0b9344048c276c942d1e5c1b6921a4879182d7b'

ROOTS=(0,0,1,1,1)
CHOICES=list(product(range(2),range(5)))
THRESHOLDS=sorted({Q(h,n) for h in (3,4,6) for n in range(1,h)})

def simplex(n,b):
    return [(Q(0),)*n]+[tuple(b if i==j else Q(0) for i in range(n)) for j in range(n)]

def coeff(fun,r,j):
    b=[1+(ROOTS[l]==r)+(l==j) for l in range(5)]
    initial=[fun(v) for v in b]
    increments=[]
    for a in range(3,11):
        increments.append([max(fun(v+i+1)-fun(v+i) for i in range(a-2)) for v in b])
    # All breakpoints are <=6. The complete geometric tail after depth10
    # therefore has the same maximal increment as at depth10.
    return initial,increments

def hinge(t):
    return lambda u:max(Q(u)-t,Q(0))

def prepare():
    costs={}
    for t in THRESHOLDS+[Q(1)]:
        f=hinge(t)
        item={'hinge':[coeff(f,*c) for c in CHOICES],
              'minimum':[coeff(lambda u,t=t:min(Q(u),t),*c) for c in CHOICES],
              'finite':[]}
        end=max(2,(t.numerator+t.denominator-1)//t.denominator)
        item['tail_start']=end
        for n in range(2,end):
            item['finite'].append((n,[coeff(lambda u,n=n,f=f:f(n*u)/n-f(u),*c) for c in CHOICES],
                                    [coeff(lambda u,n=n,f=f:f(n*u),*c) for c in CHOICES]))
        costs[t]=item
    return costs,[coeff(lambda u:Q(u),*c) for c in CHOICES]

COSTS,MEAN=prepare()

def vertex_data(params):
    deficit,alpha,beta,late,z=params
    width=[Q(1)-Q(d) for d in deficit]
    d=[Q(z)-Q(alpha[ROOTS[l]])-Q(beta[l]) for l in range(5)]
    mass=[width[l]*d[l]/9-Q(late[l]) for l in range(5)]
    pmass=[w/9 for w in width]
    s,x=sum(mass),sum(pmass)
    rm=[sum(mass[l] for l in range(5) if ROOTS[l]==r) for r in (0,1)]
    rw=[sum(width[l] for l in range(5) if ROOTS[l]==r) for r in (0,1)]
    T=max(rm)+max(mass)+max(d)/18+sum(width)/36+max(rw)/36+max(width)/36+Q(1)/72
    return width,d,mass,pmass,s,x,T

def params():
    return product(simplex(5,Q(1,2)),simplex(2,Q(1,4)),simplex(5,Q(1,4)),simplex(5,Q(1,72)),(Q(3,4),Q(1)))

def need(ok,msg):
    if not ok:raise ValueError(msg)

def pack(cf):
    initial,rows=cf
    terms=[list(initial)]
    grouped={}
    for a,row in zip(range(3,11),rows):
        key=tuple(row)
        grouped[key]=grouped.get(key,F(0))+F(1,3**a)
    key=tuple(rows[-1])
    grouped[key]=grouped.get(key,F(0))+F(1,2*3**10)
    terms.extend([[v*w for v in row] for row,w in grouped.items() if any(row)])
    den=lcm(*(v.denominator for row in terms for v in row))
    integer=[[int(v*den) for v in row] for row in terms]
    return den,integer[0],integer[1:]

def ev(cf,ms,av):
    den,initial,rows=cf
    return F(sum(a*b for a,b in zip(initial,ms))+sum(max(a*b for a,b in zip(row,av)) for row in rows),72*den)

PACK={t:{'hinge':list(map(pack,c['hinge'])),'minimum':list(map(pack,c['minimum'])),
         'finite':[(n,list(map(pack,g)),list(map(pack,f))) for n,g,f in c['finite']],
         'tail_start':c['tail_start']} for t,c in COSTS.items()}
MEAN=list(map(pack,MEAN))

@lru_cache(None)
def pure_part(pmass):
    unit=(72,)*5
    x=F(sum(pmass),72)
    pm=max(ev(c,pmass,unit) for c in MEAN)
    addition={}
    for t,item in PACK.items():
        values=[F(0)]*10
        for n,gcs,fcs in item['finite']:
            gf=max(ev(c,pmass,unit) for c in fcs)
            for i,g in enumerate(gcs):values[i]+=F(4,5**n)*(ev(g,pmass,unit)+F(n-1,n)*gf)
        N=item['tail_start']
        tail=F(1,5**(N-1))
        for i,c in enumerate(item['minimum']):values[i]+=tail*(ev(c,pmass,unit)-t*x+(N-F(3,4))*pm)
        addition[t]=values
    return pm,addition

def exact(par):
    width,d,ms,ps,s,x,T=vertex_data(par)
    need(min(ms)>=0 and min(d)>=F(1,4) and s>=F(1,4),'actual cell positivity')
    need(T>=0,'nonnegative mixed7 cylinder cap')
    def ints(vs):
        need(all((v*72).denominator==1 for v in vs),'shared cell scaling')
        return tuple(int(v*72) for v in vs)
    mi,di,pi=ints(ms),ints(d),ints(ps)
    pm,addition=pure_part(pi)
    mean=max(ev(c,mi,di) for c in MEAN)+pm/4
    costs={t:max(ev(c,mi,di)+a for c,a in zip(item['hinge'],addition[t])) for t,item in PACK.items()}
    den=F(5,6)*s-T/6
    need(den>0,'actual mixed7 positive denominator')
    out={}
    for h in (3,4,6):
        raw=F(29,42)*costs[F(h)]+sum((F(6*n,7**n)*costs[F(h,n)] for n in range(2,h)),F(0))
        raw+=F(1,7**(h-1))*((h+F(1,6))*mean-h*s)
        out[h]=raw/den
    return out,den

def no_duplicate(pairs):
    result={}
    for k,v in pairs:
        need(k not in result,'duplicate JSON key')
        result[k]=v
    return result

def result(source_directory):
    targets={3:F(1318076,584325),4:F(94745926,61354125),6:F(578163435166,676429228125)}
    maximum={h:F(0) for h in targets}
    minimargin={h:None for h in targets}
    witnesses={}
    denmin=None
    count=0
    for par in params():
        values,den=exact(par)
        denmin=den if denmin is None else min(den,denmin)
        for h,v in values.items():
            margin=(targets[h]-v)*den
            need(margin>=0,'complete shared-cell target margin')
            minimargin[h]=margin if minimargin[h] is None else min(margin,minimargin[h])
            if v>maximum[h]:maximum[h]=v;witnesses[h]=par
        count+=1
    need(count==1296 and maximum==targets,'complete vertex count and attained relaxed maxima')
    # Reuse the twelve branch values of the established PR result. The four
    # effective9 branches also admit the new shared-cell bound above; the
    # other eight are bounded by their already verified PR profiles.
    source=Path(source_directory)/'pure_root_profile_certificate.json'
    need(hashlib.sha256(source.read_bytes()).hexdigest()==PINNED_PR_SHA256,'pinned predecessor PR certificate hash')
    old=json.loads(source.read_text(),object_pairs_hook=no_duplicate)
    rows=[]
    for branch in old['branches']:
        values={h:F(branch['profile'][str(h)]) for h in targets}
        if branch['ternary_case']=='modulus9_effective':values={h:min(v,targets[h]) for h,v in values.items()}
        need(all(v<=targets[h] for h,v in values.items()),'all original missing-class branches')
        rows.append({'ternary_case':branch['ternary_case'],'modulus5_present':branch['modulus5_present'],
                     'modulus7_present':branch['modulus7_present'],'hinge_bounds':{str(h):str(v) for h,v in values.items()}})
    need(len(rows)==12,'all twelve branches')
    old_R=F(old['source_inputs']['R'])
    old_h2=F(old['generic_integer_hinges']['2'])
    need(old_R==F(1649,360) and old_h2==F(2159489,572400),'unchanged predecessor first and second hinge inputs')
    # These are complete-test hinge bounds. They do not lower the separate
    # sum of individually maximized cylinder masses.
    hinges={int(h):F(v) for h,v in old['generic_integer_hinges'].items()}
    hinges.update(targets)
    hinges[1]=min(old_R,2+targets[3])
    hinges[2]=min(old_h2,1+targets[3])
    hinges[5]=min(hinges[5],(targets[4]+targets[6])/2)
    R,h2=hinges[1],hinges[2]
    b11=targets[4]/6
    b13=(F(28,33)*targets[6]+F(100,363)*targets[3]+F(19300,483153)*h2+F(887,322102)*R+F(1,966306))/6
    rho=1-b11-b13
    physical=F(old['selected_actual_law']['physical_square'])
    need(physical==F(324599,3816) and rho>0,'same AP(4,6) physical square and positive continuation residual')
    gamma=1+(physical-1)/rho
    density=F(1440,53)/rho
    need(gamma<F(old['selected_actual_law']['supported_square']),'strict same-law AP13 improvement')
    return {'schema':'shared-cell-hinge-v1',
            'source_sha256':{'pure_root_profile_certificate.json':PINNED_PR_SHA256},
            'vertex_count':count,'minimum_raw_survivor_denominator':str(denmin),
            'targets':{str(h):str(v) for h,v in targets.items()},'minimum_raw_margins':{str(h):str(v) for h,v in minimargin.items()},
            'strict_gains_from_PR':{str(h):str(F(old['generic_integer_hinges'][str(h)])-v) for h,v in targets.items()},
            'relaxed_maximum_vertices':{str(h):[[str(v) for v in g] if isinstance(g,tuple) else str(g) for g in par] for h,par in witnesses.items()},
            'twelve_branches':rows,
            'generic_integer_hinges':{str(h):str(v) for h,v in sorted(hinges.items())},
            'complete_test_first_moment':str(1+hinges[1]),
            'unchanged_nonunit_cylinder_cap_sum':str(old_R),
            'same_actual_AP13_consumer':{'T11':4,'T13':6,'b11':str(b11),'b13':str(b13),'survival_lower':str(rho),
                                         'physical_square':str(physical),'supported_square':str(gamma),
                                         'supported_Haar_density':str(density)},
            'scope':'Same actual uniform357 law and all original labels/heights. Ordinary continuous-domain proof; not actual-family sharpness or Lean verification.'}

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-directory',type=Path,default=BASE)
    parser.add_argument('--certificate',type=Path,default=BASE/'shared_cell_hinges_certificate.json')
    parser.add_argument('--write',action='store_true')
    args=parser.parse_args()
    actual=result(args.source_directory)
    file=args.certificate
    if args.write:file.write_text(json.dumps(actual,indent=2)+'\n')
    else:
        need(json.loads(file.read_text(),object_pairs_hook=no_duplicate)==actual,'certificate mismatch')
    print('Verified 1296 complete shared-cell vertices and all 12 original missing branches; exact h3,h4,h6 margins are nonnegative.')
