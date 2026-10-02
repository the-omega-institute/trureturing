"""Feasible exact FC77 scalar witnesses obstruct the shared-budget certificate.

Bounded deterministic coordinate ascent is only a witness search;
every final array and its exact objective are independently checked.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
from itertools import combinations, permutations
from math import prod
from pathlib import Path
import json

ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument('--input',required=True)
ap.add_argument('--shared-result',required=True)
ap.add_argument('--output',required=True)
args=ap.parse_args()
raw=Path(args.input).read_bytes();data=json.loads(raw)
sraw=Path(args.shared_result).read_bytes();shared=json.loads(sraw)
Q=data['primes'];P=[q for q in Q if q>7]
checks=0
def need(ok,msg):
    global checks
    checks+=1
    if not ok:raise ValueError(msg)
need(Q==[5,7,11,13,17,19,23,29,31,37,41],'Complete-geometric prime support')
need(shared['input_sha256']==sha256(raw).hexdigest(),'Same shared-budget input')
masks=(510,0)
c={p:F(p-1,p-2) for p in Q};b={p:c[p]-1 for p in Q};a={p:c[p]/p for p in (5,7)}
g={1:{p:1-b[p] if p==5 else F(1) for p in Q},2:{p:F(1) if p==5 else 1-b[p] for p in Q}}
W={r:prod(g[r].values(),start=F(1)) for r in (1,2)}
G={r:prod((g[r][q] for q in P),start=F(1)) for r in (1,2)}

def root_witness(r):
    S5=g[r][5]/a[5];S7=g[r][7]/a[7]
    k=S5.numerator//S5.denominator;l=S7.numerator//S7.denominator
    rho=S5-k;sigma=S7-l
    iw=[rho.denominator]*k+([rho.numerator] if rho else [])
    iv=[sigma.denominator]*l+([sigma.numerator] if sigma else [])
    n5,n7=len(iw),len(iv)
    denoms=[q-2 if r==1 else q-3 for q in P]
    nx=[1+((masks[0]>>i)&1) if r==1 else 2-((masks[0]>>i)&1) for i in range(len(P))]
    ny=[1+((masks[1]>>i)&1) if r==1 else 2-((masks[1]>>i)&1) for i in range(len(P))]
    need(all(x+y<d for x,y,d in zip(nx,ny,denoms)),'Strict raw paired budgets')
    def matrix(I,J):
        return [[prod(d-x*(I[q]==i)-y*(J[q]==j) for q,(d,x,y) in enumerate(zip(denoms,nx,ny)))
                 for j in range(n7)] for i in range(n5)]
    def cost(M):return sum(iw[i]*iv[j]*M[i][j] for i in range(n5) for j in range(n7))
    best=None
    for seed in range(8):
        if seed==0:
            I=[0]*len(P);J=[0]*len(P)
        else:
            I=[(q*seed+q//2+seed-1)%n5 for q in range(len(P))]
            J=[(q*(seed+1)+q//3+seed)%n7 for q in range(len(P))]
        M=matrix(I,J);initial=cost(M)
        for sweep in range(12):
            changed=False
            order=range(len(P)) if sweep%2==0 else range(len(P)-1,-1,-1)
            for q in order:
                d,x,y=denoms[q],nx[q],ny[q]
                N=[]
                for i in range(n5):
                    row=[]
                    for j in range(n7):
                        old=d-x*(I[q]==i)-y*(J[q]==j)
                        need(M[i][j]%old==0,'Remove actual q factor exactly')
                        row.append(M[i][j]//old)
                    N.append(row)
                rowgrad=[iw[i]*sum(iv[j]*N[i][j] for j in range(n7)) for i in range(n5)]
                colgrad=[iv[j]*sum(iw[i]*N[i][j] for i in range(n5)) for j in range(n7)]
                ii=max(range(n5),key=lambda i:rowgrad[i]);jj=max(range(n7),key=lambda j:colgrad[j])
                if rowgrad[ii]==rowgrad[I[q]]:ii=I[q]
                if colgrad[jj]==colgrad[J[q]]:jj=J[q]
                if (ii,jj)!=(I[q],J[q]):
                    changed=True
                I[q],J[q]=ii,jj
                M=[[N[i][j]*(d-x*(ii==i)-y*(jj==j)) for j in range(n7)] for i in range(n5)]
            if not changed:break
        final=cost(M)
        need(final<=initial and M==matrix(I,J),'Witness search is monotone and matrix reconstruction exact')
        if best is None or final<best[0]:best=(final,I.copy(),J.copy())
    Z,I,J=best
    factor=G[r]*a[5]*a[7]/(rho.denominator*sigma.denominator*prod(denoms))
    value=W[r]-factor*Z
    # Independently evaluate the literal full 5x7 array with Fractions.
    ws=[a[5]*F(v,rho.denominator) for v in iw]+[F(0)]*(5-n5)
    vs=[a[7]*F(v,sigma.denominator) for v in iv]+[F(0)]*(7-n7)
    X=[F(x,d) for x,d in zip(nx,denoms)];Y=[F(y,d) for y,d in zip(ny,denoms)]
    need(len(ws)==5 and len(vs)==7 and sum(ws)==g[r][5] and sum(vs)==g[r][7],
         'Actual row counts and capped-simplex sums')
    need(all(0<=v<=a[5] for v in ws) and all(0<=v<=a[7] for v in vs),
         'Every head weight obeys its cap')
    xrows=[[X[q] if I[q]==i else F(0) for i in range(5)] for q in range(len(P))]
    yrows=[[Y[q] if J[q]==j else F(0) for j in range(7)] for q in range(len(P))]
    for q,p in enumerate(P):
        budget5=(b[p]+((masks[0]>>q)&1 if r==1 else 1-((masks[0]>>q)&1))*b[p])/g[r][p]
        budget7=(b[p]+((masks[1]>>q)&1 if r==1 else 1-((masks[1]>>q)&1))*b[p])/g[r][p]
        need(sum(xrows[q])==budget5 and sum(yrows[q])==budget7,'Every original raw budget used once')
        need(all(v>=0 for v in xrows[q]+yrows[q]),'Nonnegative feasible raw allocations')
    literal=G[r]*sum((ws[i]*vs[j]*(1-prod((1-xrows[q][i]-yrows[q][j] for q in range(len(P))),start=F(1)))
                      for i in range(5) for j in range(7)),F(0))
    need(literal==value and 0<=literal<=W[r],'Independent exact FC77 objective agrees with integer search')
    return {'root':r,'objective':str(value),'objective_decimal':float(value),'carrier':str(W[r]),'G':str(G[r]),
            'head5_weights':[str(v) for v in ws],'head7_weights':[str(v) for v in vs],
            'raw_X':[str(v) for v in X],'raw_Y':[str(v) for v in Y],
            'head5_rows':I,'head7_rows':J,
            'q_arrays':{str(p):{'x':[str(v) for v in xrows[q]],'y':[str(v) for v in yrows[q]]} for q,p in enumerate(P)},
            'search_bound':{'starts':8,'maximum_sweeps_per_start':12}}

witnesses={r:root_witness(r) for r in (1,2)}
scores={r:F(witnesses[r]['objective']) for r in (1,2)}
# A genuine free original has one physical head address on both roots.
# Check the necessary positive-excess inequality at q=11,13 under every
# single global permutation from the second root's rows to the first's.
address_permutations=0
for permutation in permutations(range(5)):
    address_permutations+=1
    violations=[]
    for q in (11,13):
        x1=list(map(F,witnesses[1]['q_arrays'][str(q)]['x']))
        x2=list(map(F,witnesses[2]['q_arrays'][str(q)]['x']))
        selected2=(1-((masks[0]>>P.index(q))&1))*b[q]
        excess=sum((max(F(0),g[2][q]*x2[j]-x1[permutation[j]])
                    for j in range(5)),F(0))
        violations.append(excess>selected2)
    need(any(violations),'No common physical row permutation realizes both free-projection constraints')
need(address_permutations==120,'Every global five-row permutation checked')
supports=[];free={1:F(0),2:F(0)};breakpoints={F(0),F(1)}
for size in range(2,len(Q)+1):
    for S in combinations(Q,size):
        K=prod((b[p] for p in S),start=F(1))
        if size==2 and S[0] in (5,7) and S[1]>7:K=(b[S[0]]-a[S[0]])*b[S[1]]
        H={r:prod((g[r][p] for p in Q if p not in S),start=F(1)) for r in (1,2)}
        supports.append((K,H[1],H[2]));breakpoints.add(H[2]/(H[1]+H[2]))
        for r in (1,2):free[r]+=K*H[r]
need(all(free[r]==F(shared['root_free_remaining'][str(r)]) for r in (1,2)),
     'Same complete shared-budget free remainder')
# Fee is accumulated piecewise-affinely; verify the optimizing value
# independently against the original support sum afterwards.
events={}
for K,H1,H2 in supports:
    t=H2/(H1+H2);ds,db=events.get(t,(F(0),F(0)))
    events[t]=(ds+K*(H1+H2),db-K*H2)
intercept=free[2];slope=-free[2];best=None;weights=[]
for gamma in sorted(breakpoints):
    if gamma in events:
        ds,db=events[gamma];slope+=ds;intercept+=db
    fee=intercept+slope*gamma
    bound=gamma*(W[1]-free[1]-scores[1])+(1-gamma)*(W[2]-free[2]-scores[2])-fee
    if best is None or bound>best:best=bound;weights=[gamma]
    elif bound==best:weights.append(gamma)
gamma=weights[0]
direct_fee=sum((K*max(gamma*H1,(1-gamma)*H2) for K,H1,H2 in supports),F(0))
need(best==gamma*(W[1]-free[1]-scores[1])+(1-gamma)*(W[2]-free[2]-scores[2])-direct_fee,
     'Best-weight support fee independently agrees')
out={'contract':'One genuine feasible FC77 scalar array per root at a SINGLE shared-budget vertex. Its weighted line is a lower bound on the exact joint-scalar worst group fee. Thus the stated optimized comparison is an UPPER bound on the best all-real-weight exact-two-group/marginal-remainder certificate. No arithmetic AP realization or covering counterexample is asserted.',
 'input_sha256':sha256(raw).hexdigest(),'shared_result_sha256':sha256(sraw).hexdigest(),
 'masks':list(masks),'private_primes':P,'witnesses':{str(r):witnesses[r] for r in (1,2)},
 'common_free_address_test':{
     'private_primes':[11,13],
     'necessary_inequality':'sum_i (g_2q*x_2qi-x_1qi)_+ <= selected_root2_unnormalized_budget',
     'scope':'Projection unions before head-star restriction, with common physical head rows including zero-weight rows.',
     'global_head5_permutations_checked':address_permutations,
     'admissible_permutations':0},
 'weight_candidate_count':len(breakpoints),'maximizing_weights':[str(v) for v in weights],
 'best_certificate_upper_bound':str(best),'best_certificate_upper_bound_decimal':float(best),
 'rules_out_exact_two_group_certificate':best<0,'checks':checks,
 'limits':['Feasible scalar arrays need not arise from actual simultaneous AP phases.',
           'The conclusion concerns the exact two-group scalar maximum PLUS the unchanged separate shared-support remaining charge.',
           'Actual source relations, joint payment of remaining charges, more groups or other methods remain available.',
           'UnrestrictedErdos7 remains unresolved; no Lean verification.']}
Path(args.output).write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
print(json.dumps({'checks':checks,'witness_values':{str(r):float(scores[r]) for r in (1,2)},
 'best_gamma':str(gamma),'best_certificate_upper':float(best),'ruled_out':best<0},sort_keys=True))
