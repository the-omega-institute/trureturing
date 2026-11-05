---
slug: gudder-2021-conditionally-random-uniform-attenuation
bibkey: gudder2021mutuallyunbiasedobservables
doi: 10.48550/arXiv.2110.03099
url: https://arxiv.org/abs/2110.03099v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Measurement/ConditionallyRandomUniformAttenuation.result
---

# Conditional randomness implies uniform attenuation without sharpness

## Problem

Stan Gudder, *Mutually Unbiased Quantum Observables* (2021), arXiv:2110.03099v1, Section 2, asks:

> We do not know whether the converse of Theorem~\ref{thm21}(i) or (ii) holds.

This is the first sentence of line 223 of the downloaded v1 TeX, `MutualUnbiasedQO.tex` (576 lines, MD5 `ea23a0dd97764fa2b7444408b910866f`); the reference resolves to Theorem 2.1. Its first two parts, lines 186–187, read, with typographical commands expanded:

> (i) Condition (1) implies Condition (2).

> (ii) If $A$ and $B$ are sharp, then Condition (1) and Condition (2) are equivalent.

For finite observables $A=(A_x)_{x\in\Omega_A}$ and $B=(B_y)_{y\in\Omega_B}$, with $|\Omega_A|=m\ge1$ and $|\Omega_B|=n\ge1$, the source specifies at line 182:

> Condition~(1) is shorthand for $A_x\circ B_y=\tfrac{1}{n}\,A_x$ and $B_y\circ A_x=\tfrac{1}{m}B_y$ for all $x\in\Omega _A$, $y\in\Omega _B$ and Condition~(2) is shorthand for $(B\mid A)_y=\tfrac{1}{n}\,I$ and $(A\mid B)_x=\tfrac{1}{m}\,I$ for all $x\in\Omega _A$, $y\in\Omega _B$.

Here $E\circ F=E^{1/2}FE^{1/2}$, using the positive square root, and $(B\mid A)_y=\sum_x A_x\circ B_y$ (Section 1, lines 97 and 117–120). Each observable consists of positive semidefinite effects summing to $I$. The source calls Condition (1) uniform attenuation and Condition (2) conditional randomness. The definitions and source locators are also in [the literature note](../Library/QuantumContext/gudder2021mutuallyunbiasedobservables.md).

Issue [#21653](https://github.com/the-omega-institute/trureturing/issues/21653) fixes the statement: for every finite-dimensional complex Hilbert space and all finite observables with positive outcome counts, Condition (2) implies Condition (1), without assuming sharpness. This converse of Theorem 2.1(i) is proved. The separately worded, ambiguous question about a converse of part (ii) is outside the registered statement.

## Motivation

The source compares sequential measurement, conditional randomness and value complementarity in its study of mutually unbiased observables. Conditional randomness constrains the sum over an unread measurement outcome; uniform attenuation constrains every individual sequential product. Establishing the converse identifies when these aggregate identities already determine the individual products and extends the equivalence beyond projection-valued measurements.

## Gap

The bounded literature check in #21653 records:

- the orchestrator's reading of the arXiv version listing, which contains only v1, and a web search for the two conditions and the converse, finding the source and related Gudder papers without a settlement;
- a search-seat report of six later Gudder papers checked without finding a settlement: arXiv:2208.07923, 2303.15640, 2307.16327, 2403.08126, 2404.00177 and 2603.27369v2;
- the orchestrator's repository search finding no existing treatment of this question; #16759 concerns a different Gudder question.

`not-found-in-searched-scope`. The v1 source and version listing are directly checked here; the wider search and the six-paper reading are attributed reports, not reproduced literature searches.

## Route

All matrices below are complex $d\times d$ matrices, with finite natural dimension $d$; each indexed family has index set $\mathrm{Fin}\,m$ for a natural number $m$.

1. **A nonnegative trace identity — `sqrt_sandwich_trace`.** For a positive semidefinite matrix $K$ and a Hermitian matrix $X$, put $R=K^{1/2}$. Then $R=R^*$, $R^2=K$ and $RXR$ is Hermitian. Trace cyclicity gives $\operatorname{Tr}(XKXK)=\operatorname{Tr}((RXR)^*(RXR))\ge0$.
2. **No cancellation — `psd_sum_sandwich_zero`.** For a finite family of positive semidefinite matrices $K_x$, a Hermitian matrix $X$ and the hypothesis $\sum_x K_xXK_x=0$, multiplying by $X$ and taking the trace gives a sum of the preceding nonnegative quantities equal to zero. Each trace is zero, hence $K_x^{1/2}XK_x^{1/2}=0$. Multiplying on both sides by $K_x^{1/2}$ yields $K_xXK_x=0$ for every $x$. This lemma requires neither normalization nor invertibility of $K_x$.
3. **Scalar conditioning — `attenuation_of_conditioned`.** Let $A$ be a finite POVM, meaning every $A_x$ is positive semidefinite and $\sum_xA_x=I$. Let $B$ be any Hermitian matrix and $c\in\mathbb C$ a self-adjoint scalar. Under the hypothesis $\sum_x A_x^{1/2}BA_x^{1/2}=cI$, take $K_x=A_x^{1/2}$ and $X=B-cI$. Normalization gives $\sum_xK_xXK_x=0$, and $X$ is Hermitian. The preceding lemma makes every centered summand zero, giving $A_x^{1/2}BA_x^{1/2}=cA_x$ for every $x$.
4. **Both measurement orders — `result`.** For natural $d$, positive $m,n$, POVMs $A,B$ and conditional randomness in both orders, apply `attenuation_of_conditioned` to $A$, the Hermitian effect $B_y$ and the self-adjoint scalar $c=1/n$, using $(B\mid A)_y=I/n$. This gives $A_x\circ B_y=A_x/n$. Apply it to $B$, the Hermitian effect $A_x$ and $c=1/m$, using $(A\mid B)_x=I/m$, to obtain $B_y\circ A_x=B_y/m$.

The three auxiliary lemmas are private, consumed steps in the proof of `result`.

## Falsifier

The settlement would not answer the question if the formal conditioning used a different instrument, required projections, omitted one measurement order or replaced positivity by Hermiticity. The compiled definitions fix these boundaries:

- `IsPOVM` requires positive semidefiniteness of every effect and a sum equal to the identity.
- `luders E F` is `CFC.sqrt E * F * CFC.sqrt E`; `conditioned A B y` unfolds through `unreadState` to its sum over $x$. For positive effects these are precisely the source's positive-square-root sequential products.
- `ConditionallyRandom` includes both families of identities, and `UniformAttenuation` includes both sequential-product identities for every $x,y$.
- `claim` quantifies over all natural $d,m,n$, with explicit hypotheses $0<m$ and $0<n$. There is no lower bound on $d$ and no nonzero-effect, rank or sharpness hypothesis. Dimension zero and one-outcome observables remain in scope. The POVM encoding permits zero effects; the conditional-randomness hypotheses must still hold.

Passing from a finite-dimensional Hilbert space to matrices uses a choice of orthonormal basis; arbitrary finite outcome sets are represented by $\mathrm{Fin}\,m$ and $\mathrm{Fin}\,n$. These coordinate identifications explain the source reading; no abstract Hilbert-space transport theorem is asserted by `result`.

## Evidence

The canonical source is `D5/S3/Quantum/Measurement/ConditionallyRandomUniformAttenuation.lean` (118 lines).

- **Proof.** It proves `result : claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Measurement/ConditionallyRandomUniformAttenuation.lean.json`, statement `sha256:9d9fd5309b1fe5639e877e23dd471beccf79acc9483ae0945c0d139113518929`.

Declaration statements:

- `result`: `sha256:effd0d5af07406c79815e01a731464674709d74c198652adc4468f766e156c96`;
- `claim`: `sha256:b821ca8f9fbc6c541ecc41521fb580b12be257d7050f33b26890c3239be03e54`.

## Triage

Tier 1: an explicitly stated open question in a 2021 preprint, preregistered in issue #21653 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every natural dimension $d$, positive natural outcome counts $m,n$ and families $A:\mathrm{Fin}\,m\to M_d(\mathbb C)$ and $B:\mathrm{Fin}\,n\to M_d(\mathbb C)$ whose effects are positive semidefinite and sum to $I$, the identities $(B\mid A)_y=I/n$ for every $y$ and $(A\mid B)_x=I/m$ for every $x$ imply $A_x^{1/2}B_yA_x^{1/2}=A_x/n$ and $B_y^{1/2}A_xB_y^{1/2}=B_y/m$ for every $x,y$.

**Computed, not formalized** (exact rational $2\times2$ matrix calculations):

- For the explicit unsharp pair with four effects $A_x=I/4$ and nine effects $B_y=I/9$, both families sum to $I$, both conditional-randomness identities are satisfied, and every sequential product in either order is $I/36$. All effects are nonprojective. This calculation concerns this pair only.
- For $X=\begin{pmatrix}0&1\\1&0\end{pmatrix}$, $Z=\operatorname{diag}(1,-1)$ and the four Hermitian operators $(K_1,K_2,K_3,K_4)=(I/2,I/2,Z/2,Z/2)$, the calculation gives $\sum_jK_j^2=I$ and sandwich terms $(X/4,X/4,-X/4,-X/4)$. Their sum is zero although each is nonzero; $K_3,K_4$ are not positive semidefinite.

**Argued, not formalized.**

- *Decisive mechanism and scope.* For finite positive semidefinite $K_x$ and Hermitian $X$, the hypotheses and trace identity of `sqrt_sandwich_trace` make every summand's quadratic form nonnegative. Under $\sum_xK_xXK_x=0$, `psd_sum_sandwich_zero` therefore prevents cancellation. For a finite POVM $A$, Hermitian $B$, self-adjoint scalar $c$ and $\sum_xA_x^{1/2}BA_x^{1/2}=cI$, `attenuation_of_conditioned` applies this mechanism to $B-cI$. Thus its scalar-conditioning conclusion does not require $B$ to be positive, an effect or an element of another POVM. This describes the private lemma's scope; `result` itself retains both POVM hypotheses.
- *Positivity boundary.* In the computed Kraus tuple, $ZXZ=-X$, so the two $I/2$ operators contribute $X/2$ and the two $Z/2$ operators contribute $-X/2$. Every $K_j$ is Hermitian and $\sum_jK_j^*K_j=I$, so complete positivity and normalization alone do not give the lemma's no-cancellation conclusion. Positivity of each $K_x$ is essential to this argument.
- *Equivalence and sharpness.* For finite POVMs with positive outcome counts, summing $A_x\circ B_y=A_x/n$ over $x$ gives $(B\mid A)_y=I/n$, and summing the reverse identities gives $(A\mid B)_x=I/m$. Combining this elementary converse with `result` yields equivalence of Conditions (1) and (2). No projection assumption is needed. This makes the sharpness restriction in the equivalence quoted from Gudder's Theorem 2.1(ii) unnecessary; it does not interpret the separate ambiguous request for a converse of that part.
- *Value complementarity.* Gudder's Theorem 2.2(ii), line 229, states: “If Condition~(1) holds, then $A,B$ are value-complementary.” Consequently conditional randomness can replace Condition (1) in that assertion. Directly, if a unit vector $\psi$ satisfies $\langle\psi,A_x\psi\rangle=1$, the effect inequality $0\le A_x\le I$ gives $A_x^{1/2}\psi=\psi$. Uniform attenuation then gives $\langle\psi,B_y\psi\rangle=1/n$ for every $y$; the exchanged argument applies to certain outcomes of $B$. For mixed states, a spectral decomposition with positive weights reduces certainty to these unit-vector cases. This removes sharpness from the conditional-randomness implication in Theorem 2.1(iii).
- *Scalar overlaps and the source's later results.* Gudder's Theorem 4.1(ii), line 476, states: “If $A,B$ satisfy Condition~(1) then $A,B$ are generalized MU.” Conditional randomness now supplies its hypothesis. Explicitly, cyclicity gives $\operatorname{Tr}(A_xB_y)=\operatorname{Tr}(A_x)/n=\operatorname{Tr}(B_y)/m$. Summing over $x$ gives $\operatorname{Tr}(B_y)=d/n$, hence $\operatorname{Tr}(A_xB_y)=d/(mn)$ for every $x,y$. The established sharp and atomic statements of Theorems 2.1 and 2.3 remain valid; the extra equivalences involving value complementarity and mutually unbiased bases in Theorem 2.3 are not asserted for general POVMs by this settlement.
- *Neighbouring questions.* A quantitative estimate converting approximate conditional randomness into approximate attenuation is not supplied by the exact zero-sum argument. Such stability bounds, and extensions to infinitely many outcomes or infinite-dimensional spaces, remain open here. The choice of a preferred definition of generalized mutually unbiased observables raised in Section 4 is not settled.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The web-search outcome and repository-search outcome attributed to the orchestrator in #21653, and the search-seat readings of the six later papers, are not independently reproduced here; their reported absence of a settlement remains `ASSUMED-UNVERIFIED` beyond the directly read source and version listing.

The exact matrix computations and all consequences grouped under “Argued, not formalized” are not additional statements of `result`. In particular the equivalence, value-complementarity and scalar-overlap consequences have the arguments given above but no separate declaration in this module. Transport to abstract finite-dimensional Hilbert spaces and arbitrary finite outcome labels is explanatory mathematics, not a compiled theorem of this module. Quantitative stability, infinite-dimensional or infinite-outcome extensions, the ambiguous converse of Theorem 2.1(ii), and the broader generalized-MU questions are not settled here.
