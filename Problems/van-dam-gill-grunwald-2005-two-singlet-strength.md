---
slug: van-dam-gill-grunwald-2005-two-singlet-strength
bibkey: vandam2005statisticalstrength
doi: 10.1109/TIT.2005.851738
url: https://arxiv.org/abs/quant-ph/0307125v2
triage: theorem
motivation_gids:
  - D5/S3/QuantumBounds/StatisticalStrengthMagicSquare.result
---

# Two singlets give more than twice the statistical strength of CHSH

## Problem

W. van Dam, R. D. Gill and P. D. Grünwald, “The Statistical Strength of
Nonlocality Proofs”, IEEE Transactions on Information Theory 51(8),
2812–2835 (2005), arXiv:quant-ph/0307125v2, Section VI.D, p. 11,
Conjecture 5 states:

> There is an experiment on pairs of Bell singlets, of the $2\times4\times4$ type, more than twice as strong as CHSH, and involving joint measurements on the pairs.

The counts are two parties, four settings per party and four outcomes
per setting. The source measures strength by KL divergence in bits,
minimized over every local response mixture, with uniform, product or
arbitrary correlated setting laws (Section IV.B, Definitions 1–3).

## Motivation

`D5/S3/QuantumBounds/StatisticalStrengthMagicSquare.result` proves the
existence of four nonzero-outcome PVM settings on each party's pair of
literal singlets, with a nonproduct projector and
$S_{\rm uni}(Q)>2S_{\rm cor}(Q_{\rm CHSH})$.
The inclusions of setting laws give
$S_{\rm uni}\le S\le S_{\rm cor}$; the displayed strict comparison
therefore answers the conjecture in all three source senses.

## Gap

Preregistration [#13919](https://github.com/the-omega-institute/trureturing/issues/13919)
classifies the published conjecture as Tier 1 and fixes its literal
probability, experiment and measurement conventions. The bounded
literature check reported by the probe covers arXiv:2005.13418v3,
quant-ph/0407221, arXiv:1510.07233v3, arXiv:1108.2468,
arXiv:1303.7464, quant-ph/0506225, quant-ph/0101108v5,
quant-ph/0206070, arXiv:0907.3584 and arXiv:2509.18033.
It finds magic-square constructions, the $8/9$ local value,
single-shot or noise comparisons and general KL evidence methods,
but no explicit joint-measurement two-singlet $2\times4\times4$
KL-strength comparison exceeding twice CHSH in that searched scope.
These are probe-reported literature readings, not a claim of exhaustive
priority verification.

## Route

The commuting rows and columns of the Mermin–Peres square provide the
first three PVM settings. The fourth measures $Y\otimes I$ and
$I\otimes Y$. Bob's transpose and local singlet conjugation make the
shared vector the literal tensor product of two Bell singlets.
Parity prohibits a deterministic local strategy from winning all nine
magic-square contexts. Every real-weight local mixture inherits the
$8/9$ winning bound. Uniform four-setting coarse-graining produces
quantum masses $(7/16,9/16,0)$ and local masses
$(7/16,p,9/16-p)$ with $p\le1/2$.
Log-sum gives the lower bound
$L=(9/16)\log_2(9/8)$.
One explicit local CHSH mixture bounds the divergence under every
setting law by
$c=2[((2+\sqrt2)/8)\log_2((2+\sqrt2)/3)
+((2-\sqrt2)/8)\log_2(2-\sqrt2)]$.
The fulfilled logarithm enclosures give
$2c<93/1000<95/1000<L$.
A nonzero realignment minor proves that an actual Alice projector is
not the product of single-qubit operators.

## Falsifier

Failure of PVM validity, literal two-singlet Born probabilities,
the local parity bound for an actual response mixture, the all-setting-law
CHSH upper bound or the strict enclosure would invalidate this route.
Replacing KL by a game score or restricting local theories to a finite
selected list would answer a different question.

## Evidence

The public theorem `result : claim` is in
`D5/S3/QuantumBounds/StatisticalStrengthMagicSquare.lean`, with the
corresponding Blueprint Scribe and the cited Library note.
The statement quantifies over actual projective experiments; local
optimization ranges over the full nonnegative real simplex of response
mixtures. Its axiom closure is contained in
$\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$.
Exact arithmetic computations below supply additional optimum values;
those optimum equalities are not kernel-checked statements of this module.

## Triage

Tier 1; Conjecture 5 is **proved in this module**. The declaration's
`proof_shape` is `bind-only`; its admission basis is
`open-problem-resolution` (#13919; Proved). All 52 private theorem
helpers have consumers on the live derivation leading to `result`.
Information-escape registration is paused under CLAUDE.md §3.9.

### What the settlement shows

- **Proved in this module:** the decisive mechanism is the parity
  obstruction, preserved by every local mixture, followed by log-sum
  coarse-graining. The witness has four nonzero outcomes at every setting
  and a literal joint projector. There is no rational-weight restriction
  on the local theories.
- **Proved in this module:** $S_{\rm uni}(Q)\ge(9/16)\log_2(9/8)$,
  $S_{\rm cor}(Q_{\rm CHSH})\le c$, and the strict enclosure above.
  These bounds settle Conjecture 5 without exact optimization.
- **Computed:** the exact uniform strength of this fixed four-setting
  witness is $S_{\rm uni}(Q)=\tfrac12\log_2(8/7)$,
  approximately $0.09632253897119791$ bits. A uniform mixture of 256
  deterministic response pairs attains it. Integer KKT scores test all
  65,536 deterministic response pairs; their maximum is $112/112=1$.
  Evidence: `numeric.py`, `exact_local_models.py`, `exact_checks.py`
  and `certify_numeric.py` below. This shows that the proved coarse bound,
  approximately $0.09558281331130071$ bits, is not sharp for this witness.
- **Computed:** the optimized uncorrelated and correlated strengths of
  this same witness both equal $\log_2(9/8)$,
  approximately $0.16992500144231237$ bits. The product marginals
  $(1/3,1/3,1/3,0)$ attain this value. An exact rational local mixture
  with 129 positive columns satisfies $P\ge(8/9)Q$ in all 256 cells,
  which bounds every setting law, including correlated ones.
  The parity/log-sum bound on the nine-context law supplies the matching
  lower bound. Evidence: all five certificate scripts below. The scope is
  this fixed experiment with exactly four settings and four outcomes;
  optimality equalities are external exact arithmetic, not Lean theorems.
- **Computed:** the reference $2c=0.0925476937068137$ bits is strictly
  below the proved coarse bound. Evidence: `benchmark_values.py` below.
  The reference is an upper bound for CHSH under every setting law;
  the settlement does not require a kernel proof of the exact CHSH optimum.
- **Open:** whether magic square is the best experiment among all
  two-singlet experiments. Optimization for this fixed witness does not
  establish global experiment optimality.
- **Open:** the source's Conjecture 3, that CHSH is globally best for a
  single singlet. This settlement does not bound arbitrary single-singlet
  experiments by CHSH.
- **Open:** superadditivity against the globally optimal single-singlet
  experiment. Conjecture 5 supplies a witness beating twice CHSH; the
  stronger benchmark remains undetermined without Conjecture 3 or another
  upper bound. The source's discussion of Conjecture 5 has the stated
  affirmative witness; no other conditional source claim is asserted proved.
- **Open:** kernel proofs of the computed exact optimum equalities and
  uniform extensions to other setting counts, measurement families or
  states. No additional Lean statement is delivered for those questions.

### Computational evidence

Save each fenced program to its named file in one directory, preserving
its final newline. The commands below run from that directory, in the
listed order. They regenerate their input tables and certificates; no
host-local data file is needed. Environment: Python 3.13.2, NumPy 2.2.5,
SciPy 1.16.0 and SymPy 1.14.0. Each script's hash is SHA256 over UTF-8
source bytes. The integer and rational certificate assertions, rather than
floating optimizer success, carry the reported computed optimum values.

#### numeric.py

Command: `python3.13 numeric.py`; exit code: 0. SHA256: `520c630b1dd61e30f62440d8ebaed3f880750a38024ba455df1d5c10e6aa451c`.

```python
import os,json,time,hashlib
os.environ['OPENBLAS_NUM_THREADS']='1'
os.environ['OMP_NUM_THREADS']='1'
import numpy as np
from scipy import sparse,optimize
from itertools import product
from pathlib import Path
start=time.monotonic()
I=np.eye(2,dtype=complex);X=np.array([[0,1],[1,0]],complex);Z=np.diag([1,-1]);Y=np.array([[0,-1j],[1j,0]])
k=np.kron
M=[[k(Z,I),k(I,Z),k(Z,Z)],[k(I,X),k(X,I),k(X,X)],[k(Z,X),k(X,Z),k(Y,Y)]]
U=k(np.array([[0,-1],[1,0]],complex),np.array([[0,-1],[1,0]],complex))
def pvm(A,B): return np.array([(np.eye(4)+s*A)@(np.eye(4)+t*B)/4 for s,t in product([1,-1],repeat=2)])
A=np.array([pvm(r[0],r[1]) for r in M]+[pvm(k(Y,I),k(I,Y))])
B=np.array([pvm(M[0][y],M[1][y]) for y in range(3)]+[pvm(k(Y,I),k(I,Y))])
B=np.array([[U@p.T@U.conj().T for p in b] for b in B])
psi=np.zeros(16,complex)
for a1,a2,b1,b2 in product(range(2),repeat=4):
 psi[(2*a1+a2)*4+2*b1+b2]= ((1 if a1==0 else -1)*(1 if a2==0 else -1)/2 if a1!=b1 and a2!=b2 else 0)
Q=np.array([np.vdot(psi,k(a,b)@psi).real for x in A for y in B for a in x for b in y]).reshape(4,4,4,4)
assert np.max(abs(Q.sum(axis=(2,3))-1))<1e-12
assert np.max(abs(Q[:3,:3]*8-np.round(Q[:3,:3]*8)))<1e-12
out={'probability_values':sorted(np.unique(Q).tolist()),'block_probability_values':sorted(np.unique(Q[:3,:3]).tolist()),'normalized_error':float(np.max(abs(Q.sum(axis=(2,3))-1))),'literal_two_singlet_vector':[[float(x.real),float(x.imag)] for x in psi]}
for who,P in [('A',A),('B',B)]:
 out[who+'_PVM_error']=float(max(np.max(abs(P.sum(axis=1)-np.eye(4))),max(np.max(abs(p@p-p)) for row in P for p in row),max(np.max(abs(p-p.conj().T)) for row in P for p in row)))
responses=np.array(list(product(range(4),repeat=4)),int)
ra=np.repeat(responses,256,axis=0);rb=np.tile(responses,(256,1))
cols=np.repeat(np.arange(65536),16)
rows=np.array([((x*4+y)*4+ra[:,x])*4+rb[:,y] for x in range(4) for y in range(4)]).T.ravel()
V=sparse.csc_matrix((np.ones(len(cols)),(rows,cols)),shape=(256,65536))
mask=Q.ravel()>1e-14; Vs=V[mask,:].tocsc(); qs=Q.ravel()[mask]
constants=[i*256+j for i in [0,85,170,255] for j in [0,85,170,255]]

def solve(alpha,beta,tol=1e-9,max_outer=160,verbose=False):
 law=np.outer(alpha,beta); ws=(law[:,:,None,None]*Q).ravel()[mask]
 active=constants.copy(); lam=np.ones(len(active))/len(active)
 for it in range(max_outer):
  C=Vs[:,active].toarray()
  def fun(l):
   p=C@l
   if np.any((p<=0)&(ws>0)): return 1e100,np.zeros_like(l)
   r=np.divide(ws,p,out=np.zeros_like(ws),where=p>0)
   return -float(ws@np.log(np.maximum(p,1e-300))),-C.T@r
  opt=optimize.minimize(fun,lam,jac=True,method='SLSQP',bounds=[(0,1)]*len(active),constraints={'type':'eq','fun':lambda l:l.sum()-1,'jac':lambda l:np.ones(len(l))},options={'ftol':1e-13,'maxiter':1500})
  lam=np.maximum(opt.x,0);lam/=lam.sum();p=C@lam
  r=np.divide(ws,p,out=np.zeros_like(ws),where=p>0)
  score=np.asarray(Vs.T@r).ravel();gap=max(0,float(score.max()-1))
  val=float(np.sum(ws*np.log2(qs/np.maximum(p,1e-300))))
  if verbose:print(json.dumps({'iteration':it,'columns':len(active),'bits':val,'dual_gap_bits':gap/np.log(2),'solver_success':bool(opt.success),'elapsed':time.monotonic()-start}),flush=True)
  if gap < tol:break
  new=[int(j) for j in np.argsort(score)[-16:][::-1] if j not in active and score[j]>1+tol]
  if not new:break
  active+=new;lam=np.r_[lam*(1-1e-4),np.full(len(new),1e-4/len(new))]
 return {'bits_upper':val,'bits_lower':val-gap/np.log(2),'dual_gap_bits':gap/np.log(2),'iterations':it+1,'active_columns':len(active),'solver_success':bool(opt.success),'setting_alpha':list(map(float,alpha)),'setting_beta':list(map(float,beta)),'local_weights':[(int(j),float(w)) for j,w in zip(active,lam) if w>1e-12]}

if __name__=='__main__':
 out['uniform']=solve(np.ones(4)/4,np.ones(4)/4,verbose=True)
 Path('numerical-uniform.json').write_text(json.dumps(out,indent=2)+'\n')
 np.save('quantum-Q.npy',Q)
 out['three_setting_uniform']=solve(np.array([1/3,1/3,1/3,0.]),np.array([1/3,1/3,1/3,0.]),verbose=True)
 Path('numerical-checks.json').write_text(json.dumps(out,indent=2)+'\n')
 print(json.dumps(out),flush=True)
```

#### product_check.py

Command: `python3.13 product_check.py`; exit code: 0. SHA256: `198b4a9884fc5ae9c56ef01d53caf323e28a76d783609d2f99779470616327b5`.

```python
import json,time,sys
sys.path.insert(0,'.')
import numeric as n
import numpy as np
from scipy.optimize import linprog
start=time.monotonic()
res=linprog(np.zeros(65536),A_ub=-n.Vs,b_ub=-(8/9)*n.qs,A_eq=np.ones((1,65536)),b_eq=[1.],bounds=(0,None),method='highs',options={'primal_feasibility_tolerance':1e-9,'dual_feasibility_tolerance':1e-9})
out={'status':int(res.status),'message':res.message,'seconds':time.monotonic()-start}
if res.success:
 p=(n.V@res.x).reshape(4,4,4,4)
 with np.errstate(divide='ignore',invalid='ignore'):d=np.where(n.Q>0,n.Q*np.log2(n.Q/p),0).sum(axis=(2,3))
 out.update({'min_reference_minus_eight_ninths_quantum':float((p.ravel()[n.mask]-8/9*n.qs).min()),'weight_sum':float(res.x.sum()),'min_weight':float(res.x.min()),'context_divergences':d.tolist(),'max_context_divergence':float(d.max()),'product_optimizer_alpha':[1/3,1/3,1/3,0.],'product_optimizer_beta':[1/3,1/3,1/3,0.],'product_value_log2_nine_eighths':float(np.log2(9/8)),'local_weights':[(int(i),float(res.x[i])) for i in np.flatnonzero(res.x>1e-12)]})
open('product-check.json','w').write(json.dumps(out,indent=2)+'\n')
print(json.dumps(out),flush=True)
```

#### exact_local_models.py

Command: `python3.13 exact_local_models.py`; exit code: 0. SHA256: `5e221820187279983aeb0f37a63a7a25709ea8ea6a351525f2f7d6f161cd24a2`.

```python
import sys,json
sys.path.insert(0,'.')
import numeric as n
import numpy as np
from fractions import Fraction
q=n.Q
outside=np.ones((4,4,4,4),dtype=bool);outside[:3,:3]=False
forbidden=(outside&(q<1e-14)).ravel()
classicalwins=(q[:3,:3]>0).astype(int)
blockwin=np.zeros_like(q);blockwin[:3,:3]=classicalwins
scores=np.asarray(n.V.T@blockwin.ravel()).ravel()
allowed=(np.asarray(n.V.T@forbidden.astype(int)).ravel()==0)&(scores==8)
ids=np.flatnonzero(allowed)
p=(np.asarray(n.V[:,ids].sum(axis=1)).ravel()/len(ids)).reshape(q.shape)
# Every allowed deterministic column fails at least one of the eight non-(2,2) magic contexts.
expected=q.copy()
for x in range(3):
 for y in range(3):
  if (x,y)!=(2,2): expected[x,y]=np.where(q[x,y]>0,7/64,1/64)
assert np.max(abs(p-expected))<1e-14
out={'uniform_exact_model_strategy_ids':list(map(int,ids)),'uniform_exact_model_denominator':int(len(ids)),'uniform_exact_model_counts':np.asarray(n.V[:,ids].sum(axis=1)).ravel().astype(int).tolist(),'matches_expected_table':True,'uniform_candidate_bits':float(np.log2(8/7)/2),'all_chosen_strategies_have_magic_score_eight':bool(np.all(scores[ids]==8)),'outside_support_exact':True}
# Construct a simple product/correlated upper model by a uniform mixture of all one-loss magic strategies,
# choosing fourth outputs to make YY disagreement costs balanced, then verify a pointwise 8/9 minorant.
# Solve a rational local witness by taking the LP active columns and exact linear equations.
r=json.load(open('product-check.json'))
from scipy.optimize import linprog
cols=[i for i,w in r['local_weights']]
C=n.V[:,cols].toarray().astype(int)
res=linprog(np.zeros(len(cols)),A_ub=-C[n.mask],b_ub=-8/9*n.qs,A_eq=np.ones((1,len(cols))),b_eq=[1.],bounds=(0,None),method='highs')
# Recover with bounded-denominator approximations; exact feasibility is checked over Fraction.
for den in [10**4,10**6,10**8,10**10,10**12]:
 w=[Fraction(float(v)).limit_denominator(den) for v in res.x]
 total=sum(w);w=[v/total for v in w]
 pp=[sum(w[j] for j in range(len(w)) if C[i,j]) for i in range(256)]
 QQ=[Fraction(float(v)).limit_denominator(16) for v in q.ravel()]
 if all(pv>=Fraction(8,9)*qv for pv,qv in zip(pp,QQ)):
  out['product_exact_model']={'weights':[[cols[j],str(v)] for j,v in enumerate(w) if v],'pointwise_minorant':'P >= (8/9) Q, all 256 cells','total':str(sum(w))};break
else:out['product_exact_recovery']='floating LP feasible, direct rational rounding not feasible; active equality solve needed'
open('exact-local-models.json','w').write(json.dumps(out,indent=2)+'\n')
print({k:v for k,v in out.items() if k not in ['uniform_exact_model_counts','uniform_exact_model_strategy_ids']},flush=True)
```

#### exact_checks.py

Command: `python3.13 exact_checks.py`; exit code: 0. SHA256: `4df497351c2b7cd519c5f75a1acb33299daa686f8b90cdd1e1585937255fcb55`.

```python
import sympy as s,json,itertools,time
from pathlib import Path
start=time.monotonic()
I=s.eye(2);X=s.Matrix([[0,1],[1,0]]);Z=s.diag(1,-1);Y=s.Matrix([[0,-s.I],[s.I,0]]);k=s.kronecker_product
M=[[k(Z,I),k(I,Z),k(Z,Z)],[k(I,X),k(X,I),k(X,X)],[k(Z,X),k(X,Z),k(Y,Y)]]
U=k(s.Matrix([[0,-1],[1,0]]),s.Matrix([[0,-1],[1,0]]))
def pvm(a,b):return [(s.eye(4)+u*a)*(s.eye(4)+v*b)/4 for u,v in itertools.product([1,-1],repeat=2)]
A=[pvm(r[0],r[1]) for r in M]+[pvm(k(Y,I),k(I,Y))]
B=[pvm(M[0][j],M[1][j]) for j in range(3)]+[pvm(k(Y,I),k(I,Y))]
B=[[U*p.T*U.conjugate().T for p in b] for b in B]
psi=s.zeros(16,1)
for a1,a2,b1,b2 in itertools.product(range(2),repeat=4):
 if a1!=b1 and a2!=b2:psi[(2*a1+a2)*4+2*b1+b2]=s.Rational((-1)**(a1+a2),2)
assert (psi.conjugate().T*psi)[0]==1
for P in A+B:
 assert sum(P,s.zeros(4))==s.eye(4)
 for i,p in enumerate(P):
  assert p*p==p and p.conjugate().T==p and s.trace(p)==1
  for j,q in enumerate(P):
   if i!=j:assert p*q==s.zeros(4)
probs={};Q=[]
def ro(a):
 u,v=divmod(a,2);return [u,v,u^v]
def co(y,b):
 u,v=divmod(b,2);return [u,v,u^v^(y==2)]
for x,y in itertools.product(range(4),repeat=2):
 tot=0
 for a,b in itertools.product(range(4),repeat=2):
  p=s.simplify((psi.conjugate().T*k(A[x][a],B[y][b])*psi)[0]);tot+=p;Q.append(str(p));probs[str(p)]=probs.get(str(p),0)+1
  assert p.is_nonnegative
  if x<3 and y<3: assert p== (s.Rational(1,8) if ro(a)[y]==co(y,b)[x] else 0)
 assert tot==1
# A rank-one projector is product only if its eigenvector is product; partial trace rank one is necessary.
p=A[2][0]
red=s.Matrix(2,2,lambda i,j:sum(p[2*i+t,2*j+t] for t in range(2)))
assert red==s.eye(2)/2
pb=B[2][0]
redb=s.Matrix(2,2,lambda i,j:sum(pb[2*i+t,2*j+t] for t in range(2)))
minor_b=pb[0,0]*pb[3,3]-pb[1,1]*pb[2,2]
assert redb==s.eye(2)/2 and minor_b==s.Rational(1,4)
scores=[]
for ar,br in itertools.product(itertools.product(range(4),repeat=3),repeat=2):scores.append(sum(ro(ar[x])[y]==co(y,br[y])[x] for x,y in itertools.product(range(3),repeat=2)))
assert max(scores)==8
out={'exact_arithmetic':'sympy rationals and I','quantum_all_256_probabilities':Q,'probability_counts':probs,'nine_context_Q_is_winning_indicator_over_8':True,'all_eight_measurements_rank_one_PVM':True,'two_literal_singlets_norm':str((psi.T*psi)[0]),'Alice_third_setting_first_projector_partial_trace':str(red),'Bob_third_setting_first_projector_partial_trace':str(redb),'Bob_nonproduct_realignment_minor':str(minor_b),'classical_4096_parity_valid_pairs_maximum':max(scores),'classical_maximizer_count':scores.count(8),'seconds':time.monotonic()-start}
Path('exact-checks.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out),flush=True)
```

#### certify_numeric.py

Command: `python3.13 certify_numeric.py`; exit code: 0. SHA256: `7e108918e2221bacbd7e2ba6871a219073b9dffbd05f0812ca6d76241cffcff9`.

```python
import sys,json,time
sys.path.insert(0,'.');import numeric as n
import numpy as np
from fractions import Fraction
import sympy as s
start=time.monotonic()
exact_input=json.load(open('exact-checks.json'))['quantum_all_256_probabilities']
assert all(Fraction(float(q))==Fraction(e) for q,e in zip(n.Q.ravel(),exact_input))
j=json.load(open('exact-local-models.json'))
counts=np.array(j['uniform_exact_model_counts'],int)
# Exact KKT score. The coefficient 7 makes all nonzero Q/P ratios integer.
Q16=np.rint(16*n.Q.ravel()).astype(int)
assert np.all(counts[Q16>0]>0)
ratio=np.zeros(256,int)
for i in range(256):
 if Q16[i]:
  r=Fraction(7*16*Q16[i],int(counts[i]))
  assert r.denominator==1
  ratio[i]=r.numerator
scores=np.asarray(n.V.T@ratio).ravel().astype(int)
assert scores.max()==112 # after / (7*16), this is exactly 1
out={'optimization_input_equals_exact_Born_table_in_all_256_cells':True,'uniform_strength_exact':'(1/2) log2(8/7)','uniform_strength_float':float(np.log2(8/7)/2),'uniform_local_denominator':256,'uniform_KKT_all_65536_scores_numerator_max':int(scores.max()),'uniform_KKT_denominator':112,'uniform_KKT_exact_integer_arithmetic':True}
# Recover exact product upper model on the floating LP's positive support.
r=json.load(open('product-check.json'))
cols=[i for i,w in r['local_weights']];w0=np.array([w for i,w in r['local_weights']])
C=n.V[:,cols].toarray().astype(int)
q=[Fraction(float(v)).limit_denominator(16) for v in n.Q.ravel()]
active=[i for i in range(256) if q[i] and abs(C[i]@w0-float(Fraction(8,9)*q[i]))<1e-8]
rows=[list(map(int,C[i])) for i in active]+[[1]*len(cols)]
rhs=[s.Rational((Fraction(8,9)*q[i]).numerator,(Fraction(8,9)*q[i]).denominator) for i in active]+[s.S.One]
mat=s.Matrix(rows);b=s.Matrix(rhs)
print('matrix shape',mat.shape,'elapsed',time.monotonic()-start,flush=True)
sol,params=mat.gauss_jordan_solve(b)
print('free parameters',len(params),'elapsed',time.monotonic()-start,flush=True)
assert len(params)==0
assert all(x>=0 for x in sol) and sum(sol)==1
pp=[sum(sol[j] for j in range(len(cols)) if C[i,j]) for i in range(256)]
assert all(p>=s.Rational(8,9)*s.Rational(qv.numerator,qv.denominator) for p,qv in zip(pp,q))
out.update({'product_and_correlated_strength_exact':'log2(9/8)','product_optimizer':[s.Rational(1,3).__str__()]*3+['0'],'product_local_model_exact_weights':[[cols[j],str(v)] for j,v in enumerate(sol) if v],'product_pointwise_minorant_verified_exactly':True,'product_reference_weight_sum':str(sum(sol)),'product_local_positive_columns':len(cols),'seconds':time.monotonic()-start})
open('numeric-certificates.json','w').write(json.dumps(out,indent=2)+'\n')
print({k:v for k,v in out.items() if 'weights' not in k},flush=True)
```

#### benchmark_values.py

Command: `python3.13 benchmark_values.py`; exit code: 0. SHA256: `361484bcf90addc401f628c18c1feea443d751192816f2f0e7cdde6cd053148f`.

```python
import math,json
p=(2+math.sqrt(2))/8;q=(2-math.sqrt(2))/8
c=2*(p*math.log2((2+math.sqrt(2))/3)+q*math.log2(2-math.sqrt(2)))
d={'CHSH_reference_bits':c,'twice_CHSH_reference_bits':2*c,'coarse_lower_bits':9/16*math.log2(9/8),'uniform_strength_bits':math.log2(8/7)/2,'optimized_strength_bits':math.log2(9/8)}
assert 2*c<93/1000<95/1000<d['coarse_lower_bits']
print(json.dumps(d,sort_keys=True))
```

## ASSUMED-UNVERIFIED

Literature-search completeness outside the stated bounded scope is unverified.
The computed optimum equalities have no kernel proof in this delivery.
Global optimality and superadditivity against the optimal single-singlet benchmark remain open.
