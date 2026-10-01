"""Complete shared selected-depth budgets across two actual root carriers.

Finite support polynomial, exact radical enclosures, and 2^18 split vertices.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
from itertools import combinations
from math import prod,lcm
from bisect import bisect_right
import json
from pathlib import Path

ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument('--input',required=True)
ap.add_argument('--output',required=True)
ap.add_argument('--gamma',action='append',default=[])
args=ap.parse_args()
raw=Path(args.input).read_bytes();data=json.loads(raw)
Q=data['primes'];private=[q for q in Q if q>7]
checks=0
def need(ok,msg):
    global checks
    checks+=1
    if not ok:raise ValueError(msg)
need(Q==[5,7,11,13,17,19,23,29,31,37,41],'Reference complete-height prime support')
c={p:F(p-1,p-2) for p in Q};b={p:c[p]-1 for p in Q};a={p:c[p]/p for p in (5,7)}
g={1:{p:1-b[p] if p==5 else F(1) for p in Q},
   2:{p:F(1) if p==5 else 1-b[p] for p in Q}}
W={r:prod(g[r].values(),start=F(1)) for r in (1,2)}
G={r:prod((g[r][q] for q in private),start=F(1)) for r in (1,2)}
need(all(4*b[q]/g[r][q]<1 for r in (1,2) for q in private),'Paired raw cube stays strictly below one')

supports=[]
Frem={1:F(0),2:F(0)}
for size in range(2,len(Q)+1):
    for supp in combinations(Q,size):
        K=prod((b[p] for p in supp),start=F(1))
        if size==2 and supp[0] in (5,7) and supp[1]>7:
            p,q=supp;K=(b[p]-a[p])*b[q]
        need(K>=0,'Remaining support allowance is nonnegative')
        h={r:prod((g[r][p] for p in Q if p not in supp),start=F(1)) for r in (1,2)}
        supports.append((K,h[1],h[2]))
        for r in (1,2):Frem[r]+=K*h[r]
need(len(supports)==2**len(Q)-len(Q)-1,'Complete mixed support inventory')

SCALE=10**15
def radical(P,k):
    lo,hi=0,SCALE
    while lo+1<hi:
        mid=(lo+hi)//2
        if mid**k*P.denominator<=P.numerator*SCALE**k:lo=mid
        else:hi=mid
    L,H=F(lo,SCALE),F(lo+1,SCALE)
    need(L**k<=P<=H**k,'Exact radical enclosure')
    return L,H

N=1<<len(private)
axes={r:{p:{'lower':[],'upper':[],'branches':{}} for p in (5,7)} for r in (1,2)}
for r in (1,2):
    for mask in range(N):
        T=[(1+(bool(mask>>i&1) if r==1 else not bool(mask>>i&1)))*b[q]/g[r][q] for i,q in enumerate(private)]
        P=prod((1-t for t in T),start=F(1))
        need(all(0<=t<1 for t in T),'Axis raw budgets in cube')
        for p in (5,7):
            S=g[r][p]/a[p];k=S.numerator//S.denominator;rho=S-k
            pref=G[r]*g[r][7 if p==5 else 5]*a[p]
            if P>=rho**k:
                lo,hi=radical(P,k)
                low,high=pref*k*(1-hi),pref*k*(1-lo)
                branch='k_full'
            else:
                lo,hi=radical(rho*P,k+1)
                low,high=pref*(S-(k+1)*hi),pref*(S-(k+1)*lo)
                branch='fractional_active'
            low=max(F(0),min(W[r],low));high=max(F(0),min(W[r],high))
            need(0<=low<=high<=W[r],'One-axis bounds lie in monotone domain')
            axes[r][p]['lower'].append(low);axes[r][p]['upper'].append(high)
            axes[r][p]['branches'][branch]=axes[r][p]['branches'].get(branch,0)+1

coeff={r:[G[r]*a[5]*a[7]*(b[q]/g[r][q])**2 for q in private] for r in (1,2)}
den=lcm(*(v.denominator for r in (1,2) for p in (5,7) for side in ('lower','upper') for v in axes[r][p][side]),
        *(v.denominator for r in (1,2) for v in coeff[r]),*(v.denominator for v in W.values()))
def toint(x):
    z=x*den
    need(z.denominator==1,'Exact denominator clearing')
    return z.numerator
wi={r:toint(W[r]) for r in (1,2)}
ai={r:{p:{s:[toint(v) for v in axes[r][p][s]] for s in ('lower','upper')} for p in (5,7)} for r in (1,2)}
ci={r:[toint(v) for v in coeff[r]] for r in (1,2)}
cs={r:[0]*N for r in (1,2)}
for r in (1,2):
    for mask in range(1,N):
        bit=mask & -mask
        cs[r][mask]=cs[r][mask^bit]+ci[r][bit.bit_length()-1]
D=lcm(den*wi[1],den*wi[2]);mult={r:D//(den*wi[r]) for r in (1,2)}
gammas=[F(s) for s in (args.gamma or ['1/2'])]
need(all(0<=z<=1 for z in gammas),'Root weights in unit interval')
maximum={z:{'lower':None,'upper':None} for z in gammas}
argmax={z:{'lower':None,'upper':None} for z in gammas}
points={side:{} for side in ('lower','upper')}
Nvertices=0
for m5 in range(N):
    for m7 in range(N):
        Nvertices+=1
        both=m5&m7
        correction={1:cs[1][-1]+cs[1][m5]+cs[1][m7]+cs[1][both],
                    2:4*cs[2][-1]-2*cs[2][m5]-2*cs[2][m7]+cs[2][both]}
        values={}
        for side in ('lower','upper'):
            vals={}
            for r in (1,2):
                A=ai[r][5][side][m5];B=ai[r][7][side][m7]
                numerator=(A+B+correction[r])*wi[r]-A*B
                # Both the exact scalar maximum and the product-defect
                # upper may safely be clipped at the full carrier.
                numerator=min(numerator,wi[r]**2)
                vals[r]=numerator*mult[r]
            values[side]=vals
            previous=points[side].get(vals[1])
            if previous is None or vals[2]>previous[0]:
                points[side][vals[1]]=(vals[2],m5,m7)
        for z in gammas:
            for side in ('lower','upper'):
                value=z.numerator*values[side][1]+(z.denominator-z.numerator)*values[side][2]
                if maximum[z][side] is None or value>maximum[z][side]:
                    maximum[z][side]=value;argmax[z][side]=(m5,m7)
need(Nvertices==2**18,'Every shared split vertex evaluated')

# Build both radical-bracket envelopes ONCE from the already-computed
# vertex pairs. All subsequent weight optimization reuses these pairs.
def envelope(side):
    ordered=sorted((x,*v) for x,v in points[side].items())
    pareto=[];ybest=-1
    for point in reversed(ordered):
        if point[1]>ybest:
            pareto.append(point);ybest=point[1]
    pareto.reverse()
    hull=[]
    def cross(a,b,c):
        return (b[0]-a[0])*(c[1]-b[1])-(b[1]-a[1])*(c[0]-b[0])
    for point in pareto:
        while len(hull)>=2 and cross(hull[-2],hull[-1],point)>=0:
            hull.pop()
        hull.append(point)
    breaks=[F(p[1]-q[1],q[0]-p[0]+p[1]-q[1]) for p,q in zip(hull,hull[1:])]
    need(all(0<t<1 for t in breaks) and breaks==sorted(set(breaks)),
         'Upper-envelope root-weight breakpoints are ordered')
    need(all(cross(a,b,c)<0 for a,b,c in zip(hull,hull[1:],hull[2:])),
         'Strict upper-hull orientation')
    return hull,breaks,{'distinct_first_values':len(ordered),'pareto_points':len(pareto),'hull_points':len(hull)}

envelopes={side:envelope(side) for side in ('lower','upper')}
fee_events={}
for K,h1,h2 in supports:
    t=h2/(h1+h2)
    ds,db=fee_events.get(t,(F(0),F(0)))
    fee_events[t]=(ds+K*(h1+h2),db-K*h2)
fee_breaks=sorted(fee_events)
fee_slopes=[-Frem[2]];fee_intercepts=[Frem[2]]
for t in fee_breaks:
    ds,db=fee_events[t]
    fee_slopes.append(fee_slopes[-1]+ds)
    fee_intercepts.append(fee_intercepts[-1]+db)
need(fee_slopes[-1]==Frem[1] and fee_intercepts[-1]==0,'Complete selected fee affine pieces')

def fee(z):
    i=bisect_right(fee_breaks,z)
    return fee_intercepts[i]+fee_slopes[i]*z
def group_at(z,side):
    hull,breaks,stats=envelopes[side]
    point=hull[bisect_right(breaks,z)]
    return F(z.numerator*point[0]+(z.denominator-z.numerator)*point[1],D*z.denominator),point

def optimize_weight(side):
    hull,breaks,stats=envelopes[side]
    candidates=sorted(set([F(0),F(1)]+fee_breaks+breaks))
    best=None;best_weights=[];bestpoint=None
    for z in candidates:
        group,point=group_at(z,side)
        score=z*(W[1]-Frem[1])+(1-z)*(W[2]-Frem[2])-fee(z)-group
        if best is None or score>best:
            best=score;best_weights=[z];bestpoint=point
        elif score==best:
            best_weights.append(z)
    z=best_weights[0]
    need(fee(z)==sum((K*max(z*h1,(1-z)*h2) for K,h1,h2 in supports),F(0)),
         'Prefix affine fee agrees with direct shared-support maximum')
    # Verify the active hull face against all stored corner values;
    # this does not recompute any corner product or radical.
    direct=max(z.numerator*x+(z.denominator-z.numerator)*v[0] for x,v in points[side].items())
    need(F(direct,D*z.denominator)==group_at(z,side)[0],'Best-weight envelope agrees with every stored vertex')
    return {'bracket_side':side,'candidate_weight_count':len(candidates),
      'best_gamma':str(z),'maximizing_gamma_breakpoints':[str(z) for z in best_weights],
      'best_comparison':str(best),'best_comparison_decimal':float(best),
      'active_corner_masks':list(bestpoint[2:]),'envelope_statistics':stats,
      'group_envelope_breakpoints':[str(z) for z in breaks],
      'active_corner_root1_group_bracket_value':str(F(bestpoint[0],D)),
      'active_corner_root2_group_bracket_value':str(F(bestpoint[1],D)),
      'group_bracket_meaning':'The chosen lower/upper endpoint brackets the cheap product-defect formula. A lower endpoint is not a lower bound on the exact scalar optimum.',
      'group_envelope_vertices':[
          {'masks':list(point[2:]),
           'root1_group_bracket_value':str(F(point[0],D)),
           'root2_group_bracket_value':str(F(point[1],D))}
          for point in hull]}

optimized={side:optimize_weight(side) for side in ('lower','upper')}
need(F(optimized['upper']['best_comparison'])<=F(optimized['lower']['best_comparison']),
     'All-weight optimized radical comparison is bracketed')

records=[]
for z in gammas:
    selected=sum((K*max(z*h1,(1-z)*h2) for K,h1,h2 in supports),F(0))
    carrier=z*W[1]+(1-z)*W[2]
    free=z*Frem[1]+(1-z)*Frem[2]
    group_low=F(maximum[z]['lower'],D*z.denominator)
    group_high=F(maximum[z]['upper'],D*z.denominator)
    lower=carrier-free-selected-group_high
    upper=carrier-free-selected-group_low
    need(lower<=upper,'Certified comparison interval')
    need(group_at(z,'lower')[0]==group_low and group_at(z,'upper')[0]==group_high,
         'Envelopes agree with independent fixed-weight scan')
    masks=argmax[z]['upper']
    records.append({'gamma':str(z),'carrier':str(carrier),'free_remaining':str(free),
      'selected_remaining_shared_max':str(selected),'vertex_group_upper':str(group_high),
      'vertex_radical_upper_formula_lower_bound':str(group_low),
      'comparison_lower':str(lower),'comparison_upper':str(upper),
      'comparison_interval_decimal':[float(lower),float(upper)],
      'maximizing_vertex_upper_masks':list(masks),
      'selected_depth_budgets_assigned_root1_at_upper_vertex':{str(p):[q for i,q in enumerate(private) if mask>>i&1] for p,mask in zip((5,7),masks)},
      'positive_certificate':lower>0,
      'negative_even_for_unrounded_radical_comparison':upper<0})
out={'contract':'Complete mixed-cofactor allowance without a mixed palette. Fixed twelve-prime support, ternary height<=1, root1 only5 stars and root2 no5 stars. Every selected3d is paid at most once. Exact FC77 separate convexity reduces18 shared depth splits to262144vertices; cheaper product-defect bounds are used only at vertices.',
 'input_sha256':sha256(raw).hexdigest(),'checks':checks,'private_primes':private,'vertex_count':Nvertices,
 'radical_scale':SCALE,'axis_branch_counts':{str(r):{str(p):axes[r][p]['branches'] for p in (5,7)} for r in (1,2)},
 'root_carrier':{str(r):str(W[r]) for r in (1,2)},'root_free_remaining':{str(r):str(Frem[r]) for r in (1,2)},
 'support_count':len(supports),'results':records,
 'selected_fee_breakpoint_count':len(fee_breaks),
 'all_weight_optimization':{'certified_lower':optimized['upper'],'radical_comparison_upper':optimized['lower'],
       'best_radical_comparison_interval_decimal':[optimized['upper']['best_comparison_decimal'],optimized['lower']['best_comparison_decimal']],
       'fails_for_every_real_gamma':F(optimized['lower']['best_comparison'])<0},
 'limits':['The negative comparison, if present, concerns this vertex product-defect certificate, not the exact joint scalar optimum or actual survivor mass.',
           'No simultaneous phase realization of per-root extremizers is asserted.',
           'Prime support, ternary-height-one and star-pattern restrictions remain; unrestrictedErdos7 is not settled.',
           'No Lean verification.']}
Path(args.output).write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
print(json.dumps({'checks':checks,'vertices':Nvertices,'results':[{'gamma':r['gamma'],'interval':r['comparison_interval_decimal'],'masks':r['maximizing_vertex_upper_masks']} for r in records],
 'optimized_interval':out['all_weight_optimization']['best_radical_comparison_interval_decimal'],
 'best_gamma':optimized['upper']['best_gamma'],'hulls':[envelopes[s][2] for s in ('lower','upper')]},sort_keys=True))
