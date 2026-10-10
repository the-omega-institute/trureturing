---
slug: johnston-russo-2026-fourier-ldoi-locc-tightness
bibkey: johnston2026ldoi
doi: null
url: https://arxiv.org/abs/2604.12808v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Measurement/FourierLDOILOCCRefutation.result
---

# The Fourier LDOI LOCC lower bound is not tight

## Problem

Johnston and Russo, “Distinguishability of locally diagonal orthogonally invariant
quantum states,” Example 17, arXiv:2604.12808v1, ask:

> Whether the lower bound in Equation (61) is tight—that is, whether opt_LOCC(E) = 1/2 − (n − 2)/(2n²)—remains an open question.

The uniform ensemble contains $n^2$ states, with prior $1/n^2$ each. Its diagonal
vectors are $\phi_{ii}=\sum_k U_{ik}|kk\rangle$, where $U$ is the normalized Fourier
matrix. For $i<j$, its two ordered labels are
$\phi_{ij}=(|ij\rangle+|ji\rangle)/\sqrt2$ and
$\phi_{ji}=(|ij\rangle-|ji\rangle)/\sqrt2$. The question is the equality for every
$n\ge3$. Issue [#14672](https://github.com/the-omega-institute/trureturing/issues/14672)
fixes the source conventions and the literal equality claim.

## Motivation

Equation (61) gives a LOCC lower bound $1/2-(n-2)/(2n^2)$ and a PPT upper bound
$1/2$. The source constructs a PPT measurement attaining the upper bound.
An adaptive finite-round LOCC protocol reaches that same value, closing the
optimization interval for this ensemble.

## Gap

The source still asks the question in Example 17 and its Conclusion. The bounded
literature search recorded in #14672 found no settlement among the cited source
checks and eleven subsequent papers by the authors; this does not establish
exhaustive absence. The exact question is not supplied by a frozen repository
owner or the pinned Mathlib searches. The literature locator is
[Johnston–Russo](../Library/QuantumBounds/johnston2026ldoi.md).

## Route

The Lean carrier is finite-round LOCC, $\mathrm{LOCC}_{\mathbb N}$: a finite tree
with complete local Kraus instruments and a guessed ordered label at each leaf.
Classical communication enters through history-dependent child trees. Success
is the sum of correct-leaf squared norms with the uniform prior.

The supremum agrees with the source's full LOCC supremum: Section 2.2 of
[Chitambar et al.](../Library/QuantumBounds/chitambar2014locc.md) gives
$\mathrm{LOCC}_{\mathbb N}\subseteq\mathrm{LOCC}\subseteq
\overline{\mathrm{LOCC}_{\mathbb N}}$, and success is a continuous linear functional
of the measurement. Square Kraus operators preserve the statistics after pulling
output spaces back by polar decomposition. These correspondences are arguments
on paper, not statements in the Lean module.

For $n=3$, Alice selects a pair using its projector divided by $\sqrt2$; Bob tests
membership in that pair. Inside, a shared fair choice between X and Y bases
resolves the symmetric and antisymmetric labels. Outside, computational outcomes
identify the unordered pair, followed by a fair sign guess. The X/Y measurements
have a third outcome for the complementary level and reset measured factors with
$|0\rangle\langle x|$. An impossible branch receives the fixed guess $(0,1)$.

Completeness and structural induction bound every tree's success by one. The
explicit tree has success $1/2$, exceeding $\mathrm{lower}(3)=4/9$; hence the
supremum cannot equal the proposed lower bound.

## Falsifier

The refutation would fail if any local instrument were incomplete, the source
basis or prior differed from the encoding, or the explicit tree's success did
not exceed $4/9$. The completeness and success identities for dimension three
are checked in the settling module; the simulation separately checks completeness
and success for dimensions $3$ through $7$.

## Evidence

`D5/S3/Quantum/Measurement/FourierLDOILOCCRefutation.result : ¬ claim` is the
kernel-checked settlement. Its private `success_T` establishes success $1/2$ at
$n=3$; `score_le_mass` supplies the induction bound used to justify the supremum.
The sole public theorem has no hypotheses. Its axiom closure is contained in
$\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$.

The Scribe result carries `OpenProblemResolutionClaim` with resolution `Refuted`.
Admission basis is `open-problem-resolution` (#14672; Refuted); there is no atom
or coverage edge. Computational utility is `certified-instance`, with `refutes`
targeting this module's `claim` and `result` witnessing its negation. Registration
is paused under CLAUDE.md §3.9.

## Triage

### What the settlement shows

1. **The value — proved on paper using the kernel-checked dimension-three
   protocol and the source's PPT bound.** At $n=3$, the protocol gives
   $\operatorname{opt}_{\mathrm{LOCC}}\ge1/2$; Example 17 gives
   $\operatorname{opt}_{\mathrm{PPT}}=1/2$ and
   $\mathrm{LOCC}\subseteq\mathrm{PPT}$. Thus
   $\operatorname{opt}_{\mathrm{LOCC}}=\operatorname{opt}_{\mathrm{PPT}}=1/2$.
   The explicit protocol attains the supremum, so it is a maximum. The same
   conclusion for all $n\ge3$ follows from the paper argument in item 2 and
   the source's PPT bound. Exact optima and PPT containment are not Lean
   declarations of this module.

2. **Every $n\ge3$ — computed for $n=3,4,5,6,7$; proved on paper for all
   $n\ge3$.** Set $P_{ij}=|i\rangle\langle i|+|j\rangle\langle j|$ for $i<j$.
   Alice's instrument is $K_{ij}=P_{ij}/\sqrt{n-1}$, complete since each basis
   coordinate belongs to exactly $n-1$ pairs, giving
   $\sum_{i<j}K_{ij}^{\dagger}K_{ij}=I$. Bob's pair/complement projections
   are complete. The X/Y instruments include every complementary basis
   coordinate; the computational instruments and the fair coin are complete.
   No branch reports a diagonal label, so every diagonal state's correct
   score is zero.

   For an off-diagonal state on $\{a,b\}$, selection of that pair has probability
   $1/(n-1)$ and the inside X/Y correlations determine its sign perfectly.
   There are $2(n-2)$ other selected pairs containing exactly one of $a,b$,
   each with probability $1/(2(n-1))$. Bob is outside these pairs and the
   computational readout followed by a fair sign guess succeeds with
   probability $1/2$. All remaining pair outcomes have probability zero.
   Each off-diagonal label therefore has success
   $1/(n-1)+(n-2)/(2(n-1))=n/(2(n-1))$. Averaging the $n(n-1)$ such states
   among $n^2$ labels gives $1/2$.

   Computation: `python3 /tmp/op-jr/check.py`, exit 0; script SHA-256
   `c0df960df8154c3189b7a35e56c63e5db74088fca90759c73641d2f56f77aad8`. It constructs local Kraus effects and checks that their sum
   is the identity using `numpy.allclose`. Scope is exactly $n=3,\ldots,7$;
   the floating-point checks alone prove no uniform extension.

   | $n$ | computed success | proposed lower bound |
   | --- | --- | --- |
   | 3 | 0.5 | 0.4444444444444444 |
   | 4 | 0.5 | 0.4375 |
   | 5 | 0.5 | 0.44 |
   | 6 | 0.5 | 0.4444444444444444 |
   | 7 | 0.5 | 0.4489795918367347 |

3. **The extension — proved on paper.** Item 2 ignores $U$ because it never
   reports a diagonal label. It therefore gives success $1/2$ for every
   balanced-amplitude LDOI basis $A=(1/\sqrt2)1_n$. When
   $|u_{ki}|^2\le1/2$ for all indices, the source's Theorem 10, Eqs. (27)–(28),
   admits $c_i=1/2$: $c_i\ge\max_k|u_{ki}|^2$ and
   $c_ic_j=1/4=|a_{ij}|^2|a_{ji}|^2$. Its upper bound is
   $[n(n-1)/2+n/2]/n^2=1/2$. Hence
   $\operatorname{opt}_{\mathrm{LOCC}}=\operatorname{opt}_{\mathrm{PPT}}=1/2$,
   attained by this protocol. This includes normalized complex Hadamard
   bases for $n\ge3$, since their entry squares are $1/n$. This is a paper
   argument using Theorem 10, not an additional Lean theorem.

4. **The Corollary 16 gap bound — computed for $n=3,\ldots,7$; its failure
   to be attained here is proved on paper for all $n\ge3$.** The simulation
   returns success $1/2$ strictly above the proposed lower bound in every
   tested dimension. The difference is $(n-2)/(2n^2)>0$. Items 1–2 and the
   source PPT bound give actual PPT–LOCC gap zero for this basis, so it does
   not attain that positive gap estimate. Corollary 16 remains a valid
   upper bound; the protocol improves the LOCC lower bound for this basis.
   **Open:** whether any LDOI basis has a positive PPT–LOCC gap.

5. **The mechanism — proved in the concrete Lean construction and explained
   on paper for the general protocol.** Pair selection followed by Bob's
   membership test isolates each Bell-like pair. Inside it, symmetric and
   antisymmetric states have respectively equal and unequal outcomes in a
   shared X or Y basis, resolving their signs perfectly. The source's
   Theorem 10 lower bound uses a product-measurement assignment and does
   not express this adaptive pair-conditioned discrimination. The formal
   completeness and score evidence is `pair_complete`, `split_complete`,
   `basis_complete`, `cross_score` and `success_T`, all private and consumed
   on `result`'s proof path.

Theorem 10's bounds, the PPT/separable constructions in Eqs. (62)–(65), and
Corollary 16 remain valid. The tightness question for Example 17 is refuted;
its exact LOCC value is $1/2$ by the argument above. The source's broader
Conclusion question, equality of LOCC and PPT for every uniform orthonormal
LDOI ensemble outside the stated balanced-amplitude class, remains open.

### Reproducible simulation source

Save the following exact UTF-8 source as `/tmp/op-jr/check.py` and run
`python3 /tmp/op-jr/check.py` with NumPy installed. SHA-256: `c0df960df8154c3189b7a35e56c63e5db74088fca90759c73641d2f56f77aad8`.

```python
import numpy as np, itertools
def ensemble(n):
    U=np.array([[np.exp(2j*np.pi*i*k/n) for k in range(n)] for i in range(n)])/np.sqrt(n)
    e=lambda i,j: np.kron(np.eye(n)[i],np.eye(n)[j])
    vecs={}
    for i in range(n): vecs[(i,i)]=sum(U[i,k]*e(k,k) for k in range(n))
    for i in range(n):
        for j in range(i+1,n):
            vecs[(i,j)]=(e(i,j)+e(j,i))/np.sqrt(2); vecs[(j,i)]=(e(i,j)-e(j,i))/np.sqrt(2)
    return vecs
def protocol_success(n):
    vecs=ensemble(n); N=n*n
    # build LOCC protocol effects explicitly from local Kraus operators
    e=np.eye(n); succ=0.0; total=np.zeros((N,N),complex)
    Xp=lambda i,j,s:(e[i]+s*e[j])/np.sqrt(2)          # X basis on pair
    Yp=lambda i,j,s:(e[i]+s*1j*e[j])/np.sqrt(2)       # Y basis on pair
    for i,j in itertools.combinations(range(n),2):
        Ka=(np.outer(e[i],e[i])+np.outer(e[j],e[j]))/np.sqrt(n-1)   # Alice picks pair
        Pin=np.outer(e[i],e[i])+np.outer(e[j],e[j])
        # Bob inside: basis choice X/Y each prob 1/2, both measure; sym if product of signs... compute effects
        for basis in ['X','Y']:
            for sa in (1,-1):
                for sb in (1,-1):
                    va=Xp(i,j,sa) if basis=='X' else Yp(i,j,sa)
                    vb=Xp(i,j,sb) if basis=='X' else Yp(i,j,sb)
                    KA=np.outer(va,va.conj())@Ka; KB=np.outer(vb,vb.conj())@Pin
                    K=np.kron(KA,KB)/np.sqrt(2)
                    E=K.conj().T@K; total+=E
                    # guess: X basis: sym if sa==sb ; Y basis: |ij>+|ji> ... choose label maximizing for consistency
                    guess=None
                    best=-1
                    for lab in [(i,j),(j,i)]:
                        v=vecs[lab]; p=np.real(v.conj()@E@v)
                        if p>best: best=p; guess=lab
                    succ+=np.real(vecs[guess].conj()@E@vecs[guess])
        # Bob outside pair: both read computational labels, guess sign fairly
        Pout=np.eye(n)-Pin
        for a in (i,j):
            for b in range(n):
                if b in (i,j): continue
                KA=np.outer(e[a],e[a])@Ka; KB=np.outer(e[b],e[b])@Pout
                E=np.kron(KA,KB).conj().T@np.kron(KA,KB); total+=E
                lab=(a,b) if a<b else (b,a)
                lab2=(lab[1],lab[0])
                succ+=0.5*np.real(vecs[lab].conj()@E@vecs[lab])+0.5*np.real(vecs[lab2].conj()@E@vecs[lab2])
    assert np.allclose(total,np.eye(N)), "not complete"
    return succ/N
for n in range(3,8):
    s=protocol_success(n); print(n, round(s,12), "LB", 0.5-(n-2)/(2*n*n))
```

## ASSUMED-UNVERIFIED

The bounded literature search does not establish exhaustive novelty or priority.
The LOCC carrier correspondence, the PPT bound, the general-dimension counting
argument and the balanced-amplitude extension are arguments on paper, not
kernel-checked declarations of this delivery. The simulation is floating-point
and checks completeness with NumPy's default `allclose` tolerance; it is not
an exact rational certificate.
