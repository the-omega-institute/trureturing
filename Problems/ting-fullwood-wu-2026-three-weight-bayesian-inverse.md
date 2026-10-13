---
slug: ting-fullwood-wu-2026-three-weight-bayesian-inverse
bibkey: ting2026operational
doi: 10.48550/arXiv.2605.10375
url: https://arxiv.org/abs/2605.10375v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Foundation/FiniteKrausRepresentation.exists_kraus
---

# Bayesian inverses of three-weight Pauli channels

## Problem

Ouyang Ting, James Fullwood and Zhen Wu, *Operational time-reversal symmetry for
unital qubit channels*, [arXiv:2605.10375v1](https://arxiv.org/html/2605.10375v1),
Section V, leave the alternative that a Pauli channel with precisely three
nonzero weights admits Bayesian inverses only at the maximally mixed state, or
that the admissible states form a measure-zero subset of the Bloch ball.
The [literature note](../Library/QuantumChannels/ting2026operational.md) contains
the exact quotation and the unrestricted Section II definition.

The full target associated with
[issue #13585](https://github.com/the-omega-institute/trureturing/issues/13585) is:
for every $p:\{0,1,2,3\}\to\mathbb R$ with $p_\mu\ge0$,
$\sum_\mu p_\mu=1$ and exactly three nonzero entries, let
\[
\mathcal P(A)=\sum_{\mu=0}^3p_\mu\sigma_\mu A\sigma_\mu,
\qquad (\sigma_0,\sigma_1,\sigma_2,\sigma_3)=(I,X,Y,Z),\quad Y=iXZ.
\]
Then the checked conclusion includes
\[
\operatorname{tr}(A^*\mathcal P(B))
=\operatorname{tr}(\mathcal P(A)^*B)\quad\text{for all }A,B,
\]
and, for every complex $2\times2$ PSD trace-one matrix $\rho$,
\[
\left(\exists\mathcal F\text{ complex-linear CPTP}:\;
 \{\mathcal P(\rho)\otimes I,\mathscr J[\mathcal F]\}
 =\{I\otimes\rho,\mathscr J[\mathcal P]\}\right)
\iff \rho=I/2.
\]
Here $\mathscr J[\mathcal N]=\sum_{i,j}E_{ij}\otimes\mathcal N(E_{ji})$.
Complete positivity means positivity at **every finite amplification**;
trace preservation holds on **all matrices**. The quantifier over $\mathcal F$
is unrestricted by Pauli form, unitality or equality to the adjoint. Pure
inputs, zero individual Bloch coordinates and all four missing weights are
included. The compiled endpoint retains this entire statement.

## Motivation

A Bayesian inverse implements the time-symmetry of the paper's sequential
measurement correlations. Theorem 1 and Proposition 2 concern the adjoint
candidate and unscathed states. The three-weight question requires an
obstruction that applies to any CPTP reverse map. Choi positivity supplies
such a test without imposing a form on that map.

## Gap

The bounded primary-source and arXiv search scope is recorded in the literature
note. The checked v1 text retains the Section V alternative; no separate
settlement was identified within that scope. This is not an assertion that
no independent proof exists.

The checked application below composes the supplied facts with explicit
polynomial and order normalization. The full exact statement and its suppliers
compile, and their inspected axiom closures contain only `propext`,
`Classical.choice` and `Quot.sound`. In particular, the selected-source Choi
equivalence in `FiniteKrausRepresentation` is kernel-checked. The supplier has
no frozen-state membership; compilation does not confer that status.

## Route

**States and forward channel.** The existing all-Hermitian Bloch representation
and all-PSD norm bound give $\rho=(I+r\cdot\sigma)/2$ and $\sum r_i^2\le1$.
No purity premise is used. The Pauli channel has output Bloch coordinates
$s_i=\lambda_i r_i$, where
\[
\lambda=(p_0+p_1-p_2-p_3,\ p_0-p_1+p_2-p_3,\ p_0-p_1-p_2+p_3).
\]
Hermitian Pauli involutions and trace cyclicity supply self-adjointness.
The Kraus family $\sqrt{p_\mu}\sigma_\mu$ supplies CP, and normalization plus
self-adjointness supplies unitality and trace preservation on all matrices.

**Arbitrary reverse map.** The output-first Choi matrix is
$C_\mathcal F[(b,i),(c,j)]=\mathcal F(E_{ij})_{bc}$, without a factor of $1/2$.
Its relation to the literal Jam matrix is
$C_\mathcal F[(b,i),(c,j)]=\mathscr J[\mathcal F][(j,b),(i,c)]$.
Reindexing the original Bayes equation gives
\[
\{I\otimes\mathcal P(\rho)^T,C_\mathcal F\}
=\{\rho\otimes I,C_\mathcal P\}.
\]
The selected equivalence `IsCompletelyPositive F ↔ PosSemidef (choi_matrix F)`
is used in its CP-to-PSD direction. No positivity of the Jam matrix is assumed.

**Scaled polynomial.** Set $V=I\otimes(s\cdot\sigma)^T$, $q=\sum s_i^2$,
$C=C_\mathcal F$ and $R=\{\rho\otimes I,C_\mathcal P\}$.
Then $V^2=qI$ and $C+(VC+CV)/2=R$ imply
\[
(1-q)C=T,\qquad
T=(1-q/2)R-\tfrac12(VR+RV)+\tfrac12VRV.
\]
This implication is denominator-free and holds at general $q=1$. At that
boundary it forces $T=0$ for any solution; it neither constructs nor uniquely
determines $C$. Strict three-weight normalized inputs with $r\ne0$ satisfy
$q<1$ by the separate sign argument below.

**Four literal witnesses.** For missing label $k$, choose active weights $a$
as in the table. Put $h_i=(1-a_i)r_i$, and vectorize
$(I-h\cdot\sigma)\sigma_k$ in order $(0,0),(0,1),(1,0),(1,1)$ to obtain $w_k$.
Coordinates here are numbered 1, 2, 3, corresponding to Lean indices 0, 1, 2.

| Missing weight | Active triple $a$ | Entries of $w_k$ |
| --- | --- | --- |
| $p_0=0$ | $(p_1,p_2,p_3)$ | $(1-h_3,-h_1+ih_2,-h_1-ih_2,1+h_3)$ |
| $p_1=0$ | $(p_0,p_3,p_2)$ | $(-h_1+ih_2,1-h_3,1+h_3,-h_1-ih_2)$ |
| $p_2=0$ | $(p_3,p_0,p_1)$ | $(-ih_1-h_2,-i(1-h_3),i(1+h_3),ih_1-h_2)$ |
| $p_3=0$ | $(p_2,p_1,p_0)$ | $(1-h_3,h_1-ih_2,-h_1-ih_2,-1-h_3)$ |

Define
\[
H=\sum h_i^2,\quad A=\sum a_i h_i^2,\quad
B=\sum a_i^2(1-a_i)r_i^2,\quad K=\sum a_i^2r_i^2,
\quad N(a,r)=(1-H)B+KA.
\]
The literal polynomial evaluations under normalization are
\[
\begin{aligned}
p_0=0&:\quad\operatorname{Re}(w_0^*Tw_0)=-4N((p_1,p_2,p_3),r),\\
p_1=0&:\quad\operatorname{Re}(w_1^*Tw_1)=-4N((p_0,p_3,p_2),r),\\
p_2=0&:\quad\operatorname{Re}(w_2^*Tw_2)=-4N((p_3,p_0,p_1),r),\\
p_3=0&:\quad\operatorname{Re}(w_3^*Tw_3)=-4N((p_2,p_1,p_0),r).
\end{aligned}
\]
Each row uses its own $h$ from its active triple. The witness quantity $H$
is not the output quantity $q$.

**Strict sign.** Since the active weights are positive and sum to one,
$0<a_i<1$. For $r\ne0$, select $j$ with $r_j\ne0$.
The bounds $(1-a_i)^2<1$ give $H<\sum r_i^2\le1$, with strictness supplied
by the $j$ term. The same term gives $B>0$; all terms of $A$ and $K$ are
nonnegative. Hence $N(a,r)>0$. In every table row,
$\lambda_i^2=(2a_i-1)^2<1$, so independently
$q<\sum r_i^2\le1$. Thus CP of $\mathcal F$ would make
$T=(1-q)C_\mathcal F$ PSD, contradicting the negative witness value.
This strict-sum argument permits pure states and vanishing coordinates other
than the chosen $j$; it never divides by a coordinate or by $1-q$.

**The maximally mixed converse.** If $r=0$, choose $\mathcal F=\mathcal P$.
It is CPTP and fixes $I/2$, and both anticommutators in the literal Bayes
equation equal $\mathscr J[\mathcal P]$. This case is handled directly,
without applying the strict witness argument at zero.

## Falsifier

A normalized three-weight probability vector, a PSD trace-one $\rho\ne I/2$,
and an arbitrary CPTP $\mathcal F$ satisfying the literal Bayes equation would
refute the target. A mismatch in any Choi index, scale, active-weight row,
or polynomial evaluation would invalidate the proposed source derivation;
it would not by itself refute the mathematical target.

## Evidence

The permanent application source is the existing
[FiniteKrausRepresentation Scribe](../Blueprint/D5/S3/Quantum/Foundation/FiniteKrausRepresentation.scribe.cs).
It adds narrative and formulas without a new mathematical Describe. The full
exact application belongs in transient anonymous Lean evidence, not a new
retained D5 theorem or Reg mirror. The original statement source is
[`91e62c309eda7ed8152c810d10770bffae1d2518`](https://github.com/the-omega-institute/trureturing/blob/91e62c309eda7ed8152c810d10770bffae1d2518/D5/S3/QuantumChannels/PauliThreeWeightBayesianInverseUniqueness.lean),
with preserved supplier-based source
[`18584173b3b7662448967ce0c7a64c3fffecc95f`](https://github.com/the-omega-institute/trureturing/blob/18584173b3b7662448967ce0c7a64c3fffecc95f/D5/S3/QuantumChannels/PauliThreeWeightBayesianInverseUniqueness.lean).
These are statement and proof-source inputs, not validated imports.

| Application step | Existing supplier or normalization |
| --- | --- |
| Full state and channel domains | `CoPRelativeQuantumnessRefutation.IsDensity`, `IsCPTP`; the original complex-linear `MatrixMap` |
| Pauli matrices and involutions | `StabilizerPairLocalUnitaryInequivalence.pauliMatrix`, `FiniteDimensional.qubit_weyl_star` |
| All-density Bloch coordinates | `ActualPureQubitCostInfimum.bloch_geometry_of_isHermitian`, first projection; `norm_bloch_le_trace_of_posSemidef` |
| Pauli CP and mixed-state converse | `FiniteKrausChannel.PhyslibLeaf.MatrixMap.of_kraus`, `of_kraus_isCompletelyPositive`; normalization and trace cyclicity |
| Arbitrary reverse-map positivity | `FiniteKrausRepresentation` source declarations `choi_matrix`, `choi_PSD_iff_CP_map`, selected Physlib revision `6a09b2d1761a0d4430083045a247eb121d8da260` |
| Original Bayes equation to Choi | Explicit entry reindexing; output-first, no normalization factor |
| Scaled Sylvester and four witnesses | Finite entrywise and polynomial normalization |
| Strict signs | Actual active-weight bounds, nonzero-coordinate selection, `Finset.sum_pos'`, `Finset.sum_lt_sum` and order normalization |
| PSD contradiction | Pinned Mathlib `Matrix.PosSemidef.smul`, `dotProduct_mulVec_nonneg` |

The pinned Mathlib revision is `db584cd6d46c92f209a44c0f1c829460d327499d`.
The application has no new escape content. Exact statement inspection and
kernel checking cover all original quantifiers and the literal Bayesian
equation. The full proof, including the scaled Sylvester implication, four
witness evaluations and strict output contraction, has only the standard
axioms `propext`, `Classical.choice` and `Quot.sound` in its inspected closure.

## Triage

The target is the full three-weight alternative under the unrestricted
definition. This application-exposition route creates no new D5 declaration,
Reg mirror, four-slot target or problem-resolution metadata. The mathematics
is a complete derivation with a kernel-checked exact application. No formal
problem-resolution status is asserted.

The negative Choi direction excludes every nonzero Bloch input, and the
mixed-state converse selects the paper's first alternative for Pauli channels.
Extension from Pauli channels to arbitrary unital channels would additionally
require a checked unitary-equivalence transport; it is not part of this exact
application. General four-weight classification is outside this target.

## ASSUMED-UNVERIFIED

Scribe source compilation and canonical rendering are checked. Full source
admission and required integration checks remain unverified. The bounded
literature check establishes neither worldwide novelty nor priority. No source
hash, polynomial calculation or prose assertion is a kernel or publication
certificate.
