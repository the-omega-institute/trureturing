---
slug: grandjean-liang-bancal-brunner-gisin-2012-mermin-cglmp-facet
bibkey: grandjean2012mermincglmpfacet
doi: 10.48550/arXiv.1204.3829
url: https://arxiv.org/abs/1204.3829v2
triage: theorem
motivation_gids:
  - D5/S3/QuantumBounds/MerminCglmpFacet.result
---

# The Grandjean et al. Mermin-CGLMP facet conjecture

## Problem

B. Grandjean, Y.-C. Liang, J.-D. Bancal, N. Brunner and N. Gisin,
“Bell inequalities for three systems and arbitrarily many measurement outcomes”,
*Physical Review A* 85, 052113 (2012), arXiv:1204.3829v2, Section II,
states:

> We conjecture that inequality (1) is indeed facet-defining for all $K\ge2$.

For two settings and $K$ outcomes at each of three parties, its functional is

$$
I_K=\langle[A_2-B_1+C_1]_K\rangle+
\langle[A_1+B_2-C_1]_K\rangle+
\langle[-A_1+B_1+C_2]_K\rangle+
\langle[-A_2-B_2-C_2-1]_K\rangle.
$$

Here $[X]_K$ is the least nonnegative residue and
$\langle[X]_K\rangle=\sum_{j=0}^{K-1}jP(X=j\bmod K)$.
Let $\mathcal L_K$ be the convex hull of all deterministic full behaviours
$p_s(a,b,c\mid x,y,z)=[A_x=a][B_y=b][C_z=c]$.
The settled statement is validity $I_K(p)\ge K-1$ on $\mathcal L_K$ and

$$
\dim\operatorname{aff}\{p\in\mathcal L_K:I_K(p)=K-1\}+1
=\dim\operatorname{aff}\mathcal L_K
\qquad(K\ge2).
$$

## Motivation

`D5/S3/QuantumBounds/MerminCglmpFacet.result` proves both clauses uniformly.
The full behaviour carrier retains all eight input triples and all $K^3$
output triples. Lean input $0$ represents source setting $1$, and input $1$
represents source setting $2$. Shared-randomness mixtures of local response
functions are exactly convex combinations of deterministic assignments.
Mathlib's `vectorSpan` is the direction space of the affine span, so its
`finrank` expresses the stated affine dimensions.

## Gap

Preregistration [#13574](https://github.com/the-omega-institute/trureturing/issues/13574)
records the verbatim Tier 1 conjecture, all quantifiers, the expected resolution
and the proposed rigidity argument. The source reports facets for $K\le8$.
The bounded literature reading in that issue inspected the citing passages of
19 arXiv works from the 22-item citing list; none states a general-$K$ proof.
The three unread non-arXiv citing works and exhaustive priority remain
`ASSUMED-UNVERIFIED`. Masanes's all-$d$ bipartite CGLMP facet theorem is an
existing result, rather than the externally open tripartite conjecture.

## Route

The general bridge in `FacetRigidityBridge.rigidity_facet_bridge` turns
rigidity on saturating generators into affine codimension one. A convex
combination can attain a valid lower bound only through its positively
weighted saturating generators. Normalisation converts affine functionals
to linear ones; the annihilator decomposition then supplies the dimension
identity.

`CglmpFacetRigidity.bipartite_rigidity` uses a short-arc potential and a single
wrap coefficient. It proves that every bipartite local coefficient function
vanishing at CGLMP saturation is a scalar multiple of its slack.
The conclusion is literature-attested by Masanes (2003),
arXiv:quant-ph/0210073, DOI 10.26421/QIC3.4-4; this is a different proof
from the source's construction of independent saturating vectors.

Fix Charlie's outputs $(c,C)$. Relabel Alice and Bob by
$a'=a-C$, $A'=A+c$, $b'=b$, $B'=B+C-c$.
The four residues become the bipartite CGLMP expression. Each slice has a
multiplier $\lambda(c,C)$. Every local coefficient function is additively
separable in $(c,C)$, hence satisfies a rectangular identity. Strategies
with $a+A+B-b=0$ produce slack $K\mathbf1_{c\ne p}$; those with
$a+A+B-b=-1$ produce slack $K\mathbf1_{C\ne p}$.
Varying $p$ forces the slice multiplier to be constant in both coordinates.
This proves tripartite rigidity and supplies the general bridge's hypothesis.
The all-zero strategy saturates; a strategy with Charlie's first output $1$
has nonzero slack for $K\ge2$, certifying a proper face.

## Falsifier

A counterexample would be some $K\ge2$ and a local behaviour below the bound,
or a saturating face whose affine dimension is not one less than that of
$\mathcal L_K$. The kernel-checked `result : claim` excludes both for the
literal functional and full local polytope. Changing the residue convention,
the four setting triples, or the carrier defines a different question.

## Evidence

The three Lean modules `FacetRigidityBridge`, `CglmpFacetRigidity` and
`MerminCglmpFacet`, with their Scribe mirrors, contain the complete proof.
The settling theorem is `D5/S3/QuantumBounds/MerminCglmpFacet.result`.
The axiom closure of every public declaration is contained in
$\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$.
No added axiom, `sorry` or `native_decide` is used. The settling Scribe
records `OpenProblemResolutionClaim` with resolution `Proved`.
The settling admission basis is `open-problem-resolution` (#13574; Proved).
Information-escape registration is paused under CLAUDE.md §3.9.

## Triage

### What the settlement shows

- **Proved:** the main-text facet clause holds for every $K\ge2$, on the
  full local polytope, with validity included. It replaces the source's
  finite-range evidence and conjectural all-$K$ facet clause by a uniform
  theorem. The source's quantum-value and visibility calculations are
  neither changed nor optimized by this result.
- **Proved (dual rigidity form):** bipartite CGLMP saturation determines
  every local functional up to a scalar for every nonzero $d$.
  `CglmpFacetRigidity.bipartite_rigidity` supplies a new short-arc proof of
  the rigidity underlying Masanes's all-$d\ge2$ facet theorem. The module
  states the rigidity conclusion; the reusable convex-geometric bridge
  supplies its facet interpretation.
- **Proved:** the Charlie-indexed relabelled CGLMP slices glue through the
  rectangular identity. The private `slice_AB`, `tripLocal_rectangular`
  and `tripartite_rigidity` are used by `result` through `rigidity_vertices`.
  The zero and minus-one witnesses make the multiplier constant; $K\ge2$
  is needed for the proper-face witness and coordinate comparison.
- **Open:** the facet clause of Appendix B inequality (B1) for every
  $K\ge2$. The general bridge is reusable, but the (B1)-specific rigidity
  proof is missing. Its all-$K$ local bound is separately proved by
  `D5/S3/QuantumBounds/SliwaSevenArbitraryOutcomeLocalBound.result`
  (#12317). That bound and this main-text facet proof settle different
  clauses; they do not establish the remaining (B1) facet conjecture.
  **Computed:** the finite (B1) rank test below covers exactly $K=2,3,4$.
  The source reports the facet property for $K\le8$; that source reading
  is an attestation, not an independently rerun computation here.
- **Open:** whether a slice structure explains the fully symmetric
  generalization (Eq:Mermin2). The source, Section IV, reports that it
  fails to be a facet at $K=4,5$. Those failures are source-reported finite
  readings; this proof establishes neither their explanation nor a
  uniform classification of the symmetric family.
- **Open:** extension to more parties. The source, Section V, reports an
  unsuccessful search for analogous four-party facet inequalities.
  This result proves the three-party statement and gives no four-party
  existence or impossibility theorem.

### Computed (B1) ranks for three outcome counts

Exhaustive enumeration over all $K^6$ deterministic strategies and exact
Gaussian elimination modulo $P=2^{31}-1$ gives:

| $K$ | Minimum (B1) value | Saturating vertices | Affine rank of saturation modulo $P$ | Affine rank of all vertices modulo $P$ |
| --- | --- | --- | --- | --- |
| 2 | 6 | 32 | 25 | 26 |
| 3 | 12 | 189 | 123 | 124 |
| 4 | 18 | 704 | 341 | 342 |

These are **computed** finite-field rank readings, not Lean theorems.
The full ranks equal $(2K-1)^3-1$ and the saturating ranks are one less
in this tested range. Finite-field rank supplies a lower bound on real
rank; validity and the local no-signalling dimension bound give the
corresponding upper bounds. No extension beyond $K=2,3,4$ is inferred
from this computation.

The measured command is `python3 /tmp/op-lit/glbbg/rank.py b 2 3 4`
(exit code $0$). Save the following exact source as `rank.py` and reproduce
it with `python3 rank.py b 2 3 4`.
The script's SHA-256 is `2478dd9cfcd896e427cf79d15c8b29e437d2c42e46789241646f170d8f59d3fe`.
Its only nonstandard dependency is NumPy. The `m` mode computes the
main-text functional; the recorded readings use only `b` mode.

```python
import itertools, numpy as np, sys
P=2**31-1
def rank_mod(M):
    M=M.copy()%P; r=0; rows,cols=M.shape
    for c in range(cols):
        piv=None
        for i in range(r,rows):
            if M[i,c]: piv=i;break
        if piv is None: continue
        M[[r,piv]]=M[[piv,r]]
        inv=pow(int(M[r,c]),P-2,P)
        M[r]=(M[r]*inv)%P
        nz=np.nonzero(M[:,c])[0]
        for i in nz:
            if i!=r: M[i]=(M[i]-M[i,c]*M[r])%P
        r+=1
        if r==rows: break
    return r
def br(x,K): return x%K
def J_mcglmp(s,K):
    A1,A2,B1,B2,C1,C2=s
    return br(A2-B1+C1,K)+br(A1+B2-C1,K)+br(-A1+B1+C2,K)+br(-A2-B2-C2-1,K)
def J_b1(s,K):
    A=[s[0],s[1]];B=[s[2],s[3]];C=[s[4],s[5]]
    t=0
    a1,b1,c1=A[0],B[0],C[0];a2,b2,c2=A[1],B[1],C[1]
    t+=2*br(a1+b1+c1,K)+2*br(-a1-b1-c1-1,K)+br(-a1-b1-c1,K)+3*br(-a2-b2-c2-1,K)+br(a2+b2+c2-1,K)+br(a2+b2+c2,K)
    # cyclic: -A2+B1+C1, -A1+B2+C2 and their cyclic permutations A->B->C->A
    for (X,Y,Z) in [(A,B,C),(B,C,A),(C,A,B)]:
        t+=br(-X[1]+Y[0]+Z[0],K)+br(-X[0]+Y[1]+Z[1],K)
    return t
def vec(s,K):
    v=np.zeros(8*K**3,dtype=np.int64)
    A=s[0:2];B=s[2:4];C=s[4:6]
    for x in range(2):
      for y in range(2):
        for z in range(2):
          v[(((x*2+y)*2+z)*K+A[x])*K*K+B[y]*K+C[z]]=1
    return v
which=sys.argv[1]; Ks=[int(k) for k in sys.argv[2:]]
for K in Ks:
    J=J_mcglmp if which=='m' else J_b1
    vals={}
    strat=list(itertools.product(range(K),repeat=6))
    js=[J(s,K) for s in strat]; m=min(js)
    sat=[s for s,j in zip(strat,js) if j==m]
    V=np.array([vec(s,K) for s in sat]); V0=V[0]
    ra=rank_mod(V[1:]-V0)
    allV=np.array([vec(s,K) for s in strat]); rall=rank_mod(allV[1:]-allV[0])
    print(which,K,'min',m,'nsat',len(sat),'affdim_sat',ra,'affdim_all',rall,'target',(2*K-1)**3-1, 'FACET' if ra==rall-1 else 'NOT')
    sys.stdout.flush()
```

## ASSUMED-UNVERIFIED

The bounded literature search does not prove worldwide priority. The three
unread citing works are “Quantum Benchmark Suite for IBM's Backend Based on
SupermarQ” (2024), “Bell inequalities for arbitrary situations” (2015), and
“Quantum nonlocality of generic family of four-qubit entangled pure states”
(2015). The source-reported symmetric-family failures and the source's
$K\le8$ (B1) computation were not independently rerun. The uniform (B1)
facet clause, the symmetric-family mechanism and extensions to more parties
remain open. The correspondence between source probabilities and the Lean
full-behaviour carrier uses the explicitly stated deterministic-mixture
interpretation; the kernel proves the resulting exact encoded statement.
