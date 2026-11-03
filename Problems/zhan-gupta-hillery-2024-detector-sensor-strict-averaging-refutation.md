---
slug: zhan-gupta-hillery-2024-detector-sensor-strict-averaging-refutation
bibkey: zhanguptahillery2024detectorsensor
doi: 10.1145/3655028
url: https://arxiv.org/abs/2306.17401v6
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Measurements/DetectorSensorStrictAveragingRefutation.result
---

# Strict averaging need not improve detector-sensor probes

## Problem

C. Zhan, H. Gupta and M. Hillery, *Optimizing Initial State of Detector Sensors in Quantum Sensor Networks*, ACM Transactions on Quantum Computing 5(2), Article 10 (2024), DOI 10.1145/3655028, arXiv:2306.17401v6, Section 5, Conjecture 2 (`optimal.tex`, lines 131–149, label `conj:avg`):

> For a given $U$, consider two initial states $\ket{\psi} = \sum\limits_j \psi_j \ket{j}$ and $\ket{\psi'} = \sum\limits_j \psi'_j \ket{j}$ such that (i) they are two unequal coefficient-squares, i.e., for some $j$, $|\psi_j|^2 \neq |\psi'_j|^2$, and (ii) they have the same objective function value, i.e., $P(\ket{\psi}, U) = P(\ket{\psi'}, U)$. We claim that the ``average'' state given by $\ket{\psi_{avg}} = \sum_j \sqrt{\frac{|\psi_j|^2 + |\psi'_j|^2}{2}}  \ket{j}$ has a lower objective function value, i.e., $P(\ket{\psi_{avg}}, U) < P(\ket{\psi'}, U)$.

The quotation is from the v6 source TeX. The [Library note](../Library/QuantumBounds/zhanguptahillery2024detectorsensor.md) records the paper and its encoding. In the source's setting (`problem-related.tex`, lines 17–47), exactly one of $n$ qubit sensors fires, with equal priors $1/n$; its unitary has eigenvalues $e^{\pm i\theta}$. The objective is the minimum error of a global POVM discriminating the $n$ possible fired states.

Write $X_n=\{0,1\}^{\mathrm{Fin}\,n}$, with $1$ representing the plus eigenvector. A probe is an amplitude function $\psi:X_n\to\mathbb C$, normalized by $\sum_x|\psi(x)|^2=1$. For $n\ge1$, the reused `fire` and `isoSuccess` give $\phi_i(x)=e^{i\theta(2x_i-1)}\psi(x)$ and $S_\theta(\psi,M)=n^{-1}\sum_i\operatorname{Re}\langle\phi_i,M_i\phi_i\rangle$. The module defines `optSuccess` as the real indexed supremum of $S_\theta(\psi,M)$ over `LocalPOVM (Fin n → Bool) (Fin n)`, `errorProb` as $P_\theta(\psi)=1-\operatorname{optSuccess}_\theta(\psi)$, and `average` as $a(\psi,\psi')(x)=\sqrt{(|\psi(x)|^2+|\psi'(x)|^2)/2}$, included in $\mathbb C$ with zero imaginary part.

Issue [#26032](https://github.com/the-omega-institute/trureturing/issues/26032) fixes `claim`: for every natural $n$, every $0<\theta<\pi$, and every pair of normalized complex probes, unequal coefficient-squares somewhere and equal $P_\theta$ imply $P_\theta(a(\psi,\psi'))<P_\theta(\psi')$. Radians replace the source's degrees. This universal strict statement is refuted at $n=3$.

## Motivation

The source uses Conjecture 2 as a route to Conjecture 1, its proposed optimal Dicke probe. Theorem 3 (`optimal.tex`, label `thm:final`, lines 153–233) derives symmetry of coefficients from strict averaging and minimizes the common fired-state overlap. Distinguishing strict improvement from non-increase determines whether averaging supplies that contradiction to optimality.

## Gap

Issue #26032 records the bounded literature check before any Lean:

- The v6 source retains Conjecture 2 and the conditional route to Conjecture 1.
- The citation-search report lists twelve OpenCitations citing records and seven supplementary arXiv readings, with no settlement found in those readings; two IEEE full texts were unavailable.
- The orchestrator reports that web searches for the conjecture, its averaging formulation and later optimal-state proofs found no proof or counterexample in the searched scope.
- The repository's [Dicke-optimality dossier](zhan-gupta-hillery-2024-detector-sensor-dicke-optimality.md) and issue #16668 settle Conjecture 1 independently of Conjecture 2.

`not-found-in-searched-scope`.

## Route

All unqualified lemma names below belong to `DetectorSensorStrictAveragingRefutation`; the helpers are private.

1. **Two normalized probes.** For $l\in\{1,2\}$, let $\varphi_l(x)=1/\sqrt3$ on words of weight $l$ and zero elsewhere; these are `layer 1` and `layer 2`. For every natural $l$ and every $x:X_3$, `layer_squares` gives the squared amplitude of `layer l` as $1/\binom3l$ when the weight is $l$, and zero otherwise. For $l=1$ or $l=2$, the pointwise formula and $l\le3$ satisfy `DetectorSensorDickeOptimality.dicke_normalized`, giving normalization. `different_layers` supplies a word with unequal squared amplitudes; the proof uses the word whose only true coordinate is $0$.
2. **Both layers minimize at an admissible angle.** `threshold_value` gives $T(3)=\pi/3$, and `angle_admissible` gives $0<\pi/4\le T(3)$. For every natural $k\le3$, `counts` gives $R_k=1$ and $L_k=2$ if $k=1$ or $k=2$, otherwise $L_k=0$, for sensor indices $0$ and $1$. At $\theta=\pi/4$ the ratios $(R_k+\cos(2\theta)L_k)/(R_k+L_k)$ are $1,1/3,1/3,1$. For $l=1$ or $l=2$, `layer_minimizes` states that $l$ minimizes this ratio on `Set.Iic 3`.
3. **Global comparison.** For $l=1$ or $l=2$, every normalized $\psi:X_3\to\mathbb C$ and every three-outcome global POVM $M$, `layer_optimal` supplies a POVM $M'$ with $S_{\pi/4}(\psi,M)\le S_{\pi/4}(\varphi_l,M')$. Its call to `DetectorSensorDickeOptimality.result` uses $3\ge3$, the lower admissible angle interval, $l\le3$, the minimizing-ratio hypothesis and the pointwise squared-amplitude formula.
4. **Legitimate suprema.** `povm_nonempty` gives a POVM on $X_3$ with three outcomes: the identity effect at outcome $0$ and zero effects elsewhere. For every normalized $\psi:X_3\to\mathbb C$, `bounded_success` gives boundedness above of the success range at $\pi/4$; its proof applies the frozen `DetectorSensorDickeOptimality.global_success_upper_bound`, which bounds every success at the admissible angle by $d_3(c^\ast_3(\pi/4))^2$. With this nonempty index type and the bound for the normalized target layer, `optimal_sup` passes the preceding comparison to suprema: for $l=1$ or $l=2$ and every normalized $\psi:X_3\to\mathbb C$, $\operatorname{optSuccess}_{\pi/4}(\psi)\le\operatorname{optSuccess}_{\pi/4}(\varphi_l)$.
5. **Contradiction to strictness.** For every natural $n$ and two normalized probes on $X_n$, `average_normalized` gives normalization of their coefficient-square average. At the fixed three-sensor probes and angle $\pi/4$, `equal_error` states $P_{\pi/4}(\varphi_1)=P_{\pi/4}(\varphi_2)$, while `average_no_improvement` states $P_{\pi/4}(\varphi_2)\le P_{\pi/4}(a(\varphi_1,\varphi_2))$. Together with the two normalizations, `different_layers` and $0<\pi/4<\pi$, these contradict the strict inequality required by `claim`, yielding `result : ¬ claim`.

## Falsifier

The refutation would miss the source conjecture if it used a different objective, a restricted measurement class, probes differing only in phase, or an ill-defined supremum. Here:

- `LocalPOVM` consists of positive semidefinite effects summing to the identity on the full tensor-product space; its name imposes no locality restriction. `isoSuccess` uses the source's equal priors and one firing sensor.
- At the word whose only true coordinate is $0$, the two squared amplitudes are $1/3$ and $0$, so they differ in precisely the sense required by the conjecture.
- `average` takes the nonnegative square root of the mean coefficient-square, as in the source, and `average_normalized` applies because both inputs are normalized.
- Nonemptiness and boundedness for the three-sensor success suprema are supplied by `povm_nonempty` and `bounded_success`, under the normalization hypotheses stated in Route. The argument does not rely on default values of an empty or unbounded real supremum.

The compiled contradiction needs only the opposite weak inequality for the average's error. Equality of the average's optimal error with the two input errors is not a statement of `result` or `average_no_improvement`.

## Evidence

The canonical source is `D5/S3/Quantum/Measurements/DetectorSensorStrictAveragingRefutation.lean`.

- **Proof.** It defines `optSuccess`, `errorProb`, `average` and `claim`, and proves `result : ¬ claim`.
- **Reuse.** It reuses `fire`, `isoSuccess`, `rCount`, `lCount`, `T`, `dicke_normalized` and `result` of `DetectorSensorDickeOptimality`, `dickeCoefficient` of `AnticoherenceSpinCovariance`, and `LocalPOVM` of `TriangleIndependentSourceNoise`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- **Escape registrations.** `result` is the designated refutation result of the `utility` header and is exempt. The module has no other public theorem.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Measurements/DetectorSensorStrictAveragingRefutation.lean.json`.

Declaration statements:

- `result`: `sha256:6b14bb53efc611db4c2d4eecd8eee7eba823e4f49f1b2faadf0a54bd9d5f04f8`;
- `claim`: `sha256:81f13bd619be13be802f8b283b6e3395b60427a54d6011bf2eac818637837bfc`.

## Triage

Tier 1 conjecture of a 2024 ACM Transactions on Quantum Computing paper, preregistered in issue #26032 before any Lean.
`theorem`; resolution `refuted`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2. The refutation is a certified instance with basis `refutes`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** it is false that, for every natural $n$, every $0<\theta<\pi$ and every pair of normalized probes on $X_n$ with unequal coefficient-squares somewhere and equal minimum error, their coefficient-square average has strictly smaller minimum error than the second probe.

**Computed, not formalized:** None.

**Argued, not formalized.**

- *Mechanism and missing structure.* Two global error minimizers cannot have a normalized average with error below their common global minimum. The proof's specific instances are `equal_error` and `average_no_improvement` for $\varphi_1,\varphi_2$ at $n=3$, $\theta=\pi/4$, with normalization supplied as in Route. Unequal coefficient-squares do not ensure strict improvement. Any repaired strict statement must exclude pairs of global minimizers; excluding them is not shown sufficient. A strict statement restricted to nonoptimal probes, or requiring different fired-state Gram matrices, remains open here.
- *A weak replacement.* For $n\ge1$, $0<\theta<\pi$ and normalized probes in this same pure-state, equal-prior, global-POVM model, the following Gram argument gives $P_\theta(a(\psi,\psi'))\le(P_\theta(\psi)+P_\theta(\psi'))/2$. Let $A$ have the fired states as columns, $G=A^\dagger A$, and let $F(G)$ be the supremum of $n^{-1}\sum_i\operatorname{Re}((N_i)_{ii})$ over positive semidefinite $N_i$ with $\sum_iN_i=G$. This feasible set is nonempty by assigning $G$ to one outcome, and the objective lies between $0$ and $\operatorname{tr}(G)/n$. A POVM gives such a decomposition by $N_i=A^\dagger M_iA$. Conversely, $0\preceq N_i\preceq G$ makes each $N_i$ supported on the range of $G$. With the Moore–Penrose inverse $A^+$, the effects $(A^+)^\dagger N_iA^+$ are positive and sum to the projection $AA^+$; adding the complementary projection to one outcome completes a POVM and recovers every $N_i$ under compression by $A$. Hence optimal success equals $F(G)$. Averaging feasible decompositions and taking the bounded suprema gives $F((G+G')/2)\ge(F(G)+F(G'))/2$. Finally, $G_{ij}=\sum_x|\psi(x)|^2\overline{e^{i\theta(2x_i-1)}}e^{i\theta(2x_j-1)}$ is affine in coefficient-squares, so the average probe has Gram matrix $(G+G')/2$, giving the stated weak inequality. This is the Gram-concavity argument discussed in the Dicke-optimality dossier, not an additional Lean theorem of this settlement. Applied to two global minimizers, it gives equality for their average, since global minimality supplies the reverse inequality.
- *Symmetry and scope.* Sensor renumbering preserves weight, so it cannot turn $\varphi_1$ into $\varphi_2$. Both probes already have equal coefficient-squares within each weight class. This counterexample therefore does not by itself refute the symmetry property or settle a restriction to pairs related by sensor renumbering. No family at other sensor counts, or strictness criterion for nonoptimal pairs, is certified by this module.
- *Effect on the paper.* Theorem 3's conditional implication from Conjecture 2 to Conjecture 1 does not supply an unconditional proof when its premise is false. Its strict-averaging contradiction for symmetry cannot be justified by Conjecture 2 as stated. This does not refute Conjecture 1: the independent `DetectorSensorDickeOptimality.result` used in Route supplies the relevant optimality comparisons without strict averaging. The unambiguous-discrimination objective discussed in Section 8.1 (`extend.tex`, lines 8–40) is outside `claim`; this settlement gives no conclusion about its conjectures. The finite empirical comparisons in Section 7 (`simulation.tex`, lines 103–116) cannot establish the universal strict inequality, and their reported numerical outputs are not contradicted merely by a counterexample outside those tested pairs.

## ASSUMED-UNVERIFIED

The bounded literature check in #26032 does not establish exhaustive worldwide novelty or priority. Its citation count, seven supplementary-text readings and web-search results remain reported evidence; those readings and searches are not independently reproduced here. The two IEEE full texts were unavailable in that check, and their contents are unverified.

The finite Gram and square-root-measurement calculations are not Lean declarations or numerical optimizations over all POVMs. The general weak-averaging argument, its equality consequence for global minimizers, and the interpretive consequences in “Argued, not formalized” have no additional formalization in this settlement. Strictness for nonoptimal pairs, a sensor-permutation restriction, other sensor counts, unambiguous discrimination, unequal priors and noisy channels remain unsettled by this module. The source's empirical study has not been reproduced.
