---
slug: wang-zhou-chen-fei-2026-conical-design-concurrence-comparability
bibkey: wangzhouchenfei2026conical
doi: null
url: https://arxiv.org/abs/2606.31010v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Entanglement/ConicalDesignConcurrenceComparability.result
---

# Comparability of conical-design concurrence bounds

## Problem

H.-F. Wang, W. Zhou, L. Chen and S.-M. Fei, *Estimating the concurrence
for quantum states via symmetric measurements*, arXiv:2606.31010v2,
Section IV, after Theorem 2:

> The lower bounds of concurrence induced by arbitrary two distinct conical 2-designs are comparable.

A finite positive semidefinite family satisfies
$\sum_i E_i\otimes E_i=\alpha_E I+\beta_E F$, where
$\alpha_E\geq\beta_E>0$ and $F$ is the tensor swap. For a positive
semidefinite trace-one bipartite state $\rho$, put
$P_E(\rho)_{ij}=\operatorname{tr}[\rho(E_i\otimes E_j)]$ and
$B_E(\rho)=c_d(\|P_E(\rho)\|_1-\alpha_E-\beta_E)/\beta_E$,
where $c_d=\sqrt{2/[d(d-1)]}$ and $d\geq2$.
The bound is the untruncated two-constant expression in Siudzińska,
J. Phys. A 58 (2025) 375302, Section 7, Theorem 6, Eqs. (73)–(74),
with $S=\beta_E$ and $\mathcal C_{\max}=\alpha_E+\beta_E$.

## Motivation

The settling declaration is
`D5/S3/Quantum/Entanglement/ConicalDesignConcurrenceComparability.result`.
It proves one ordering for all states for every pair of finite designs.
The measurement labels and dimension are arbitrary; the same design is
used on the two subsystems. The trace norm is reused from the frozen
`D5/S3/Quantum/Foundation/FiniteTraceDistance.traceNorm`.

## Gap

The source asks whether bounds from different designs admit a universal
ordering. Preregistration #13873 records the literal conjecture, the
bound's identification, the tier-1 literature checks and the Lean
conventions. Its literature search finds no settlement in the searched
MathDB and arXiv scope. Siudzińska supplies the two-constant formula;
that formula alone does not state the ordering.

## Route

Vectorize the effects as $A_{ip}=(E_i)_{p_2,p_1}$ and write
$v=\operatorname{vec}I$, $Q=vv^*/d$,
$t_E=\sqrt{1+d\alpha_E/\beta_E}$ and $M_t=I+(t-1)Q$.
The tensor identity gives $A^*A=\beta_E I+\alpha_E vv^*$, so
$A=\sqrt{\beta_E}\,U M_{t_E}$ with $U^*U=I$.
For $X(\rho)_{pq}=\rho_{(p_1,q_2),(p_2,q_1)}$ the correlation matrix
is $P_E(\rho)=A X(\rho)A^*$, and rectangular isometry invariance gives

$$
B_E(\rho)=c_d\left(\|M_{t_E}X(\rho)M_{t_E}\|_1
 -\frac{t_E^2+d-1}{d}\right).
$$

The projection dilation proves, for $0<s\leq t$ and
$\operatorname{Re}\operatorname{tr}(QX)=1/d$,

$$
\|M_tXM_t\|_1\geq\|M_sXM_s\|_1+\frac{t^2-s^2}{d}.
$$

The gain cancels the change of the offset. Consequently
$\alpha_E/\beta_E\geq\alpha_G/\beta_G$ implies
$B_E(\rho)\geq B_G(\rho)$ for every state, and the total order of real
ratios proves the conjecture. The private declarations `bound_normal_form`,
`normalized_monotonicity` and `ratio_monotonicity` carry these steps.

## Falsifier

A pair of finite PSD designs in dimension $d\geq2$ whose bounds reverse
order between two density states would refute the encoded statement.
A formula differing from the cited two-constant bound would invalidate
its correspondence to the source. Equal ratios must give equal bounds;
the order choice must lie outside the state quantifier.

## Evidence

**Kernel-checked declaration:** `result : claim` proves the uniform
ordering. The module also checks the normalization and monotonicity
helpers on its live proof path. The axiom closure is contained in
$\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$.
The definitions mirror the literal tensor identity, correlation matrix,
dimension coefficient and lower-bound formula.

**Literature reading:** `Library/QuantumStates/wangzhouchenfei2026conical.md`
locates the conjecture and Theorem 2; `Library/QuantumStates/siudzinska2025twoconstants.md`
locates the design identity and two-constant formula.

**Computation:** the reproducible script in Triage checks finite samples;
it supplies floating-point corroboration, not a proof of the universal claim.

## Triage

### What the settlement shows

| Item | Status | Evidence kind and scope |
| --- | --- | --- |
| Dependence only on $t_E^2=1+d\alpha_E/\beta_E$ and monotonicity in $t_E$ | proved | Kernel-checked private `conical_normalization`, `bound_normal_form`, `normalized_monotonicity`, `ratio_monotonicity`; the displayed normalization and dilation inequality give the mechanism. |
| State-independent ordering and equality of bounds at equal ratios | proved | Kernel-checked `result` and `ratio_monotonicity`; equal ratios permit that inequality in both directions. |
| Theorem 2's realignment comparison in the normalized family | proved | Paper argument below; the anchor is $t=1$, outside $t^2\geq d+1$, and is an extension rather than a limit of positive designs. This is not a separately exported Lean theorem. |
| A design attaining the largest admissible $\alpha/\beta$ gives the best bound | proved | Conditional application of kernel-checked `ratio_monotonicity` against each design; no existence assumption is discharged. |
| Finite attainment of the ratio supremum in each dimension | open | No declaration or paper argument here establishes an attained supremum. |
| Seeded SIC, complete MUB and binary $(N,M)$-POVM checks in $d=2,3$ | computed | Script below; seed 1387301, 152 states per dimension, zero adjacent ordering violations at tolerance $10^{-10}$. |
| Extension to the source's $\mathcal M_{\mu,\nu}$ matrices | open | No corresponding monotonicity declaration is delivered. |
| Designs chosen independently on the two subsystems | open | The delivered bound uses the same design on both factors; joint two-parameter ordering is not established. |
| Strictness of the ordering and exact concurrence for arbitrary states | open | The theorem is a weak comparison of lower bounds and does not identify concurrence. |

For the realignment anchor, the reshuffle $X$ differs from the usual
realignment matrix $R_{(a,b),(c,d)}=\rho_{(a,c),(b,d)}$ only by the
column swap $(c,d)\mapsto(d,c)$, a permutation isometry, so its trace
norm is the realignment trace norm. At $t=1$, $M_1=I$ and the offset is
$(1+d-1)/d=1$, giving $c_d(\|R\|_1-1)$.
Positive conical designs have $\alpha/\beta\geq1$, hence
$t^2=1+d\alpha/\beta\geq d+1$. For fixed $d\geq2$ this excludes
convergence to $t=1$. The projection-dilation argument at $s=1$
compares this extended anchor with every positive design. The source's
Theorem 2 already proves its stated realignment comparison; the settlement
supplies the general ordering between designs. The source's choice of the
tightest design reduces to admissible ratios, conditional on attainment;
its extended-matrix and independently chosen subsystem questions stay open.

### Reproducible numerical check

Save the following block as `checks.py` and run `python3 checks.py --output numerical-data`.
Measured command: `python3 /Users/auric/.sshx/b2a5cfe00a1c28811b016a45/attempt-1/numerical-checks.py --output /Users/auric/.sshx/b2a5cfe00a1c28811b016a45/attempt-1/numerical-data`.
Exit code: 0. Script SHA-256: `981a9ca0f8935c184b8e79225075a70cda0296c1c71b883cabc596fb6012f815`.
Python with NumPy 2.4.2 checks SIC, complete MUB, and binary
$(N,M)=(d^2-1,2)$ designs at four parameters
$\lambda\in\{0.05,0.1,0.2,0.3\}$. Each dimension has the maximally mixed
and maximally entangled states, 50 seeded random pure states and 100
seeded random mixed states. All effects are PSD numerically and their
tensor identities are checked by least squares. The largest SIC–MUB
bound differences are $1.4432899320127035\times10^{-15}$ for $d=2$ and
$9.992007221626409\times10^{-16}$ for $d=3$. Uniform numerical accuracy,
other dimensions and untested design families are open computational
extensions; the universal theorem does not rely on these samples.

```python
import numpy as np, json, argparse
from pathlib import Path
parser=argparse.ArgumentParser()
parser.add_argument("--output", type=Path, required=True)
output=parser.parse_args().output
output.mkdir(parents=True, exist_ok=True)
rng=np.random.default_rng(1387301)
def projector(v): return np.outer(v,v.conj())
def sic(d):
 if d==2:
  X=np.array([[0,1],[1,0]],complex); Y=np.array([[0,-1j],[1j,0]]); Z=np.diag([1,-1])
  return [(np.eye(2)+sum(s*a for s,a in zip(v,[X,Y,Z]))/np.sqrt(3))/4 for v in [(1,1,1),(1,-1,-1),(-1,1,-1),(-1,-1,1)]]
 w=np.exp(2j*np.pi/3)
 return [projector(np.array(v,complex)/np.sqrt(2))/3 for k in range(3) for v in [(0,1,-w**k),(-w**k,0,1),(1,-w**k,0)]]
def mubs(d):
 if d==2:
  X=np.array([[0,1],[1,0]],complex); Y=np.array([[0,-1j],[1j,0]]); Z=np.diag([1,-1])
  return [(np.eye(2)+s*a)/2 for a in [X,Y,Z] for s in [1,-1]]
 w=np.exp(2j*np.pi/d)
 return [projector(v) for v in np.eye(d,dtype=complex)]+[projector(np.array([w**(a*j*j+b*j)/np.sqrt(d) for j in range(d)])) for a in range(d) for b in range(d)]
def binary(d,lam):
 basis=[]
 for j in range(d):
  for k in range(j+1,d):
   g=np.zeros((d,d),complex);g[j,k]=g[k,j]=1/np.sqrt(2);basis.append(g)
   g=np.zeros((d,d),complex);g[j,k]=-1j/np.sqrt(2);g[k,j]=1j/np.sqrt(2);basis.append(g)
 for k in range(1,d):
  g=np.diag([1]*k+[-k]+[0]*(d-k-1))/np.sqrt(k*(k+1));basis.append(g)
 return [np.eye(d)/2+s*lam*g for g in basis for s in [1,-1]]
def constants(es,d):
 S=sum(np.kron(e,e) for e in es);I=np.eye(d*d);F=np.zeros_like(I)
 for i in range(d):
  for j in range(d):F[i*d+j,j*d+i]=1
 a,b=np.linalg.lstsq(np.stack([I.ravel(),F.ravel()],axis=1),S.ravel(),rcond=None)[0].real
 return a,b,float(np.max(abs(S-a*I-b*F)))
def bound(es,a,b,rho,d):
 P=np.array([[np.trace(rho@np.kron(e,f)) for f in es] for e in es])
 return np.sqrt(2/(d*(d-1)))*(np.linalg.svd(P,compute_uv=False).sum()-a-b)/b
out={'seed':1387301,'numpy_version':np.__version__,'dimensions':[]}
for d in [2,3]:
 designs=[('SIC',sic(d),None),('completeMUB',mubs(d),None)]
 for lam in [.05,.1,.2,.3]:designs.append((f'binary-NM-lambda-{lam}',binary(d,lam),d/4+lam**2))
 specs=[]
 for name,es,x in designs:
  a,b,err=constants(es,d)
  specs.append({'name':name,'alpha':a,'beta':b,'ratio':a/b,'x':x,'tensor_identity_max_abs_error':err,'minimum_effect_eigenvalue':float(min(np.linalg.eigvalsh(e).min() for e in es)),'outcomes':len(es)})
 designs=sorted(zip(specs,designs),key=lambda p:p[0]['ratio'])
 states=[np.eye(d*d)/(d*d),projector(np.eye(d).ravel()/np.sqrt(d))]
 for k in range(150):
  r=1 if k<50 else rng.integers(2,d*d+1)
  z=rng.normal(size=(d*d,r))+1j*rng.normal(size=(d*d,r));rho=z@z.conj().T;states.append(rho/np.trace(rho))
 bounds=np.array([[bound(es,s['alpha'],s['beta'],rho,d) for s,(_,es,_) in designs] for rho in states])
 diffs=np.diff(bounds,axis=1)
 si=[i for i,(s,_) in enumerate(designs) if s['name']=='SIC'][0];mi=[i for i,(s,_) in enumerate(designs) if s['name']=='completeMUB'][0]
 out['dimensions'].append({'d':d,'states':len(states),'pure_random':50,'mixed_random':100,'designs':[s for s,_ in designs],'minimum_adjacent_bound_difference':float(diffs.min()),'maximum_adjacent_bound_difference':float(diffs.max()),'ordering_violations_at_1e-10':int(np.sum(diffs < -1e-10)),'maximum_SIC_MUB_difference':float(np.max(abs(bounds[:,si]-bounds[:,mi]))),'maximally_mixed_bounds':bounds[0].tolist(),'maximally_entangled_bounds':bounds[1].tolist()})
 np.savez(output / f'checks-d{d}.npz',bounds=bounds,states=np.array(states),ratios=np.array([s['ratio'] for s,_ in designs]))
json.dump(out,(output / 'checks.json').open('w'),indent=2)
print(json.dumps(out,indent=2))
```

## ASSUMED-UNVERIFIED

Worldwide priority and absence of every independent in-flight solution
are not established by the searched literature scope. Floating-point
residuals do not certify exact PSD or exact tensor identities. The kernel
checks the encoded statement; source correspondence is supported by the
literal formulas and the cited source locators. Information-escape
registration is paused under CLAUDE.md section 3.9.
