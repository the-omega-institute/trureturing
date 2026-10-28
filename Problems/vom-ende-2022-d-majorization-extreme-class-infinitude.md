---
slug: vom-ende-2022-d-majorization-extreme-class-infinitude
bibkey: vomende2022strictpositivity
doi: 10.1080/03081087.2020.1860887
url: https://arxiv.org/abs/2004.05613v4
triage: theorem
motivation_gids:
  - D5/S3/Quantum/QuantumChannels/DMajorizationExtremeClassInfinitude.result
---

# Infinitely many extreme classes survive the commuting-unitary quotient in matrix D-majorization

## Problem

Frederik vom Ende, *Strict positivity and D-majorization*, Linear and Multilinear Algebra 70(19) (2022), 4023–4048, arXiv:2004.05613v4, asks in the Conclusion and Outlook, TeX file `strictly_positive_qc_v2.tex`, line 1064:

> Whether one ends up with finitely many extreme points after factoring out the unitary equivalents for now remains open.

The equivalence relation immediately preceding the question, lines 1060–1064, is
$X\sim UXU^*$ for unitary $U$ satisfying $[U,D]=0$, with $D=\operatorname{diag}(d)$, arbitrary $d\in\mathbb R_{++}^n$ and arbitrary $A\in\mathbb C^{n\times n}$. Here $M_D(A)=\{X:X\prec_D A\}$, and $X\prec_D A$ means that a complex linear, completely positive, trace-preserving map sends $A$ to $X$ and fixes $D$ (Definition `defi_matrix_D_maj`, lines 466–469; equation `eq:def_MD`, lines 926–932). See [the literature note](../Library/Eigenstructure/vomende2022strictpositivity.md).

Issue [#22739](https://github.com/the-omega-institute/trureturing/issues/22739) fixes the affirmative reading: for every positive dimension, strictly positive $d$ and complex matrix $A$, the real extreme points of $M_D(A)$ have finitely many classes under this relation. The module's `claim` quantifies over all natural dimensions, including zero, and asks for a finite set of ambient matrices representing every extreme point. Its negation is established using dimension two, so the positive-dimension reading is also refuted.

## Motivation

Matrix $D$-majorization describes the states reachable by quantum channels preserving a specified positive matrix. The source contrasts these reachable sets with the polytopes of vector $d$-majorization. A finite list of extreme classes would reduce their extreme-point analysis to finitely many representatives, despite the continuous unitary symmetry. The question asks whether that symmetry accounts for all the infinitude.

## Gap

Issue #22739 records the bounded literature check before any Lean:

- arXiv:2004.05613v4 retains the closing question;
- the search contributor `search-fo` reports screening eight citing works through OpenCitations, finding no settlement for this Gibbs-preserving reachable set;
- the same contributor reports no match in MathDB or formal-conjectures;
- the repository's recorded vom Ende problems concern other statements.

`not-found-in-searched-scope`.

A related observation appears in Frederik vom Ende, *Which Bath-Hamiltonians Matter for Thermal Operations?* (2022), arXiv:2207.11189v4, TeX file `thermal_op_JMP_rev1_2022.tex`, line 1420:

> In particular the boundary of the thermal cone is not linear, meaning that even after factoring out the rotational symmetry inflicted by the thermal operations $\rho\mapsto\operatorname{diag}(1,e^{i\phi})\rho\operatorname{diag}(1,e^{-i\phi})$ the set of extreme points is still infinite.

That paragraph concerns the reachable set under the closure of thermal operations (lines 1414–1420). These maps additionally satisfy energy covariance (lines 791–798); the present question allows every channel fixing $D$. The quoted observation concerns a different reachable set.

## Route

Fix $d=(1/3,2/3)$, $D=\operatorname{diag}(1/3,2/3)$ and $A=\operatorname{diag}(1,0)$. For every $m\in\mathbb N$, including zero, set $h=m^2+1$ and
$P_m=h^{-1}\begin{pmatrix}m^2&m\\m&1\end{pmatrix}$.

1. **Reachability.** For each natural $m$, put $r=1/\sqrt h$, $s=1/\sqrt2$ and use
   $K_0=\begin{pmatrix}mr&0\\r&0\end{pmatrix}$,
   $K_1=\begin{pmatrix}0&rs\\0&-mrs\end{pmatrix}$ and
   $K_2=\begin{pmatrix}0&0\\0&s\end{pmatrix}$.
   For every complex $2\times2$ matrix $X$, `kraus_action` gives
   $T_m(X)=X_{00}P_m+(X_{11}/2)(I-P_m+\operatorname{diag}(0,1))$, where $T_m(X)=\sum_jK_jXK_j^*$. For every natural $m$, `pure_mem` proves $P_m\in M_D(A)$ by checking complete positivity, trace preservation, $T_m(A)=P_m$ and $T_m(D)=D$.
2. **Extremality.** For any complex $2\times2$ matrix $X$ with $X\in M_D(A)$, `density` gives $X\ge0$ and $\operatorname{tr}X=1$. For every natural $m$ and complex $2\times2$ matrix $X$, `pure_rigidity` requires all three hypotheses $X\ge0$, $\operatorname{tr}X=1$ and $X(1,-m)^{\mathsf T}=0$, and concludes $X=P_m$. In `pure_extreme`, a decomposition $P_m=\alpha X+\beta Y$ with $X,Y\in M_D(A)$, real $\alpha,\beta>0$ and $\alpha+\beta=1$ forces the nonnegative quadratic form of $X$ on $(1,-m)^{\mathsf T}$ to vanish. Positivity then gives the annihilation hypothesis of `pure_rigidity`. Thus `pure_extreme` places $P_m$ in the real extreme points for every natural $m$.
3. **Separation.** For arbitrary complex $2\times2$ matrices $Y,U$, assuming $U$ is unitary and $UD=DU$, `invariant` proves $\operatorname{tr}(DUYU^*)=\operatorname{tr}(DY)$. The lemma `invariant_injective` proves that $m\mapsto\operatorname{tr}(DP_m)=(m^2+2)/(3(m^2+1))$ is injective on $\mathbb N$.
4. **Contradiction.** The proof of `result` applies the proposed finite-representative assertion to this strictly positive $d$ and this $A$. Representatives chosen for the $P_m$ must be distinct by `invariant` and `invariant_injective`, giving an injection from $\mathbb N$ into a finite set.

## Falsifier

The refutation would miss the source question if it used a weaker channel condition, a different equivalence relation or a different notion of extremality. The module uses:

- `MatrixMap`, the complex linear maps on square matrices, and `IsCPTP`, complete positivity together with preservation of the trace of every input matrix;
- `DMajorizedBy` and `majorizationSet`, with the channel fixing precisely $\operatorname{diag}(d)$;
- `Set.extremePoints ℝ`, so convex combinations have real coefficients;
- unitary conjugation $X=UYU^*$ with $UD=DU$, exactly the symmetry in the question.

The witness has strictly positive, distinct diagonal entries in $D$. The input $A$ is a positive semidefinite trace-one matrix, which is permitted by the source's unrestricted complex-matrix quantifier. The obstruction persists even when representatives may be arbitrary ambient matrices, as allowed by `claim`.

## Evidence

The canonical source is `D5/S3/Quantum/QuantumChannels/DMajorizationExtremeClassInfinitude.lean`.

- **Proof.** It defines `DMajorizedBy`, `majorizationSet` and `claim`, and proves `result : ¬ claim`.
- **Reuse.** The channel construction uses `MatrixMap.of_kraus` and `MatrixMap.of_kraus_isCompletelyPositive` from `FiniteKrausChannel`, and the channel predicate is `CoPRelativeQuantumnessRefutation.IsCPTP`. Extremality uses positive-semidefinite quadratic forms; separation uses `Matrix.trace_units_conj`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- **Escape registrations.** `result` is the designated refutation result of the `utility` header and is exempt. The module has no other public theorem.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/QuantumChannels/DMajorizationExtremeClassInfinitude.lean.json`.

Declaration statements:

- `result`: `sha256:4fb59b0ec0031193a400d81c05c040fcbe10668230b842b686bdec64381a7861`;
- `claim`: `sha256:d2dd23bb48fb6a6a005c7aca586d2c2b9433abfa3f039e5049f5ada3dda432f6`.

## Triage

Tier 1 closing question of a 2022 paper, preregistered in issue #22739 before any Lean.
`theorem`; resolution `refuted`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2. The refutation is a certified instance with basis `refutes`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** it is false that for every natural dimension $n$, every strictly positive real vector $d$ and every complex $n\times n$ matrix $A$, there is a finite set of ambient matrices representing every real extreme point of $M_D(A)$ by conjugation with unitaries commuting with $D=\operatorname{diag}(d)$.

**Argued, not formalized.**

- *Mechanism and missing structure.* For this $D$, the off-diagonal entries of $UD=DU$ give $(2/3-1/3)U_{01}=0$ and $(1/3-2/3)U_{10}=0$. Hence every commuting unitary is diagonal and its conjugation preserves diagonal populations. The populations $m^2/(m^2+1)$ vary injectively for natural $m$. A simple spectrum therefore does not supply the missing finite-orbit structure: the symmetry removes phases while preserving infinitely many population choices. This explains the separation established by `invariant` and `invariant_injective` for the fixed $D$ and family above.
- *A surviving restriction.* For any strictly positive diagonal $D$ and any complex scalar $c$, the input $A=cD$ has $M_D(A)=\{cD\}$: linearity and $T(D)=D$ force $T(cD)=cD$, and the identity channel attains it. Its extreme points therefore have one class. In dimension one every complex matrix is of this form because the single entry of $D$ is nonzero. Thus the refutation does not imply infinitude for every input or every dimension.
- *Relation to the source's order theorem.* For strictly positive $d$ with $\sum_i d_i=1$, the proof of Theorem `d_matrix_minmax` (ii), lines 889–897, establishes reachability of every density matrix from a minimal-weight basis state. Applied to the present $d$ and $A$, it identifies $M_D(A)$ with the whole qubit state space. Concretely, any qubit density matrix $\rho$ satisfies $\rho\le I\le3D$, because its nonnegative eigenvalues sum to one. Thus $\sigma=(3D-\rho)/2$ is positive semidefinite with trace one. The map $X\mapsto X_{00}\rho+X_{11}\sigma$ has positive semidefinite Choi matrix $\rho\oplus\sigma$, preserves trace, fixes $D$, and sends $A$ to $\rho$. Conversely, every channel image of $A$ is a density matrix. This is the construction in the source's Lemma `thm_channel_pure_max_state`, lines 841–865. The stronger identification is not a conclusion of `result`; the Lean proof only needs the reachable family and the density condition in `pure_mem` and `density` for the fixed $d,A$ and natural $m$ above.
- *Effect on the paper.* The question is in the outlook, following the proved results; the refutation does not supply a counterexample to those results. The outlook also proposes using an answer to help establish continuity of $(D,P)\mapsto M_D(P)$ (line 1079). A general reduction to finitely many extreme classes is unavailable. Continuity itself is not decided by `result`, and neither is finiteness for strictly positive inputs $A$.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The eight-work OpenCitations screen, MathDB and formal-conjectures queries, and the reported recurrence of the question in arXiv:2012.03496v2, Chapter 6, are reports by `search-fo` in issue #22739; their underlying readings have not been independently reproduced. The related arXiv:2207.11189v4 observation and its reachable-set definition were checked in the source text, but its full proof was not independently verified.

Every extension or interpretation in "Argued, not formalized" is not additional formalized conclusions. The identification of the entire reachable set with the state space relies on the cited source proof, rather than a declaration of this module. Continuity, classification of all extreme classes, and the restriction to strictly positive inputs remain open within this settlement.
