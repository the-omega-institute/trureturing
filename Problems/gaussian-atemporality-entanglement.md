---
slug: gaussian-atemporality-entanglement
bibkey: song2025gaussianatemporality
doi: 10.48550/arXiv.2508.11804
url: https://arxiv.org/abs/2508.11804v2
triage: theorem
motivation_gids:
  - D5/S3/Estimation/GaussianAtemporalityEntanglement.result
---

# Gaussian atemporality implies entanglement

## Problem

Song et al., “Gaussian Atemporality: When Gaussian Quantum Correlations Imply Common Cause”, arXiv:2508.11804v2, Section III.D (the fourth subsection of Section III), p. 6, state:

> From Fig. 3, Gaussian-atemporality appears to imply entanglement. The converse, on the other hand is not generally true.

Preregistration [#19029](https://github.com/the-omega-institute/trureturing/issues/19029) supplies the source quotations, Tier 1 classification, binding covariance conventions and literature screen. The assertion concerns every physical two-mode Gaussian covariance matrix in standard form, in quadrature order $(q_A,p_A,q_B,p_B)$ and units $\hbar=2$.

### Statement echo

| Source clause | Formal counterpart | Scope |
| --- | --- | --- |
| Eq. (2), $V_{AB}=\begin{pmatrix}V_A&C\\C^T&V_B\end{pmatrix}$ | `covariance` | Arbitrary real two-by-two blocks, indexed by `Fin 2`; the combined index is `Fin 2 ⊕ Fin 2`. |
| Definition 1, “with locally diagonal covariance matrices” | `IsStandardForm` | Both local blocks satisfy `Matrix.IsDiag`. |
| Spatial uncertainty inequality | `IsSpatiallyPhysical` | $V_{AB}+i(\Omega\oplus\Omega)\succeq0$, including Hermiticity. |
| Eqs. (7)–(8) | `forwardX` | $T=C^TV_A^{-1}$, $N=V_B-C^TV_A^{-1}C$, $X_f=N+i\Omega-iT\Omega T^T$. |
| Reverse temporal direction | `forwardX VB VA Cᵀ` | Exchange the local blocks and transpose $C$. |
| Section III.B, “Gaussian-atemporal in both temporal direction” | `IsGaussianAtemporal` | Both directional matrices fail to be positive semidefinite. |
| Section III.D, the two-mode Gaussian PPT criterion | `partialTransposeA`, `IsEntangled` | $\Lambda=\operatorname{diag}(1,-1,1,1)$ and failure of $\Lambda V_{AB}\Lambda+i(\Omega\oplus\Omega)\succeq0$. |
| Section III.D, the quoted implication | `claim`, `result` | All three hypotheses imply the covariance NPT predicate. |

The symplectic form is the existing `D5.S3.Quantum.Thermal.PositiveOneModeWilliamson.physicalJ2`, namely $\Omega=\begin{pmatrix}0&1\\-1&0\end{pmatrix}$. Real-to-complex conversion is `Matrix.map Complex.ofReal`; no additional conversion or reverse-direction alias is introduced. The inverse is Mathlib's total nonsingular matrix inverse. Physicality supplies the invertibility used by the proof. No assumption beyond the displayed source hypotheses is added to `claim`.

## Motivation

The result replaces the source's numerical implication by a covariance-matrix proof. The formal meaning of `IsEntangled` is failure of the partially transposed uncertainty inequality. Interpreting this as nonseparability uses the two-mode Gaussian PPT equivalence cited by the source (Simon, 2000; Werner–Wolf, 2001). A Hilbert-space separability theorem is not independently formalized here.

## Gap

The literature screen in #19029 records the belief in arXiv:2508.11804v2. It records Song–Parzygnat, arXiv:2507.14278v3, as a finite-dimensional predecessor that leaves the infinite-dimensional extension to future work; that finite-dimensional statement is not the Gaussian covariance assertion proved here. The screen records no citing work in its INSPIRE query and no match in the searched formal-conjectures corpus. It does not establish external priority or exhaustive absence of a published settlement.

## Route

Write $A=V_A$, $B=V_B$ and $V=V_{AB}$. The argument has four matrix steps, implemented by consumed private helpers of `D5.S3.Estimation.GaussianAtemporalityEntanglement`.

First, physicality gives $A+i\Omega\succeq0$ and $B+i\Omega\succeq0$ by principal submatrices. After identifying the single-mode symplectic coordinates, `D5.S3.Estimation.GaussianThermometryJointMeasurementRefutation.physical_data` gives positive semidefiniteness and determinant at least one for each real block. The determinant is nonzero, so `Matrix.PosSemidef.posDef_iff_det_ne_zero` gives positive definiteness of $A$ and $B$. This is `local_posDef`, consumed by `physical_blocks_posDef`.

Second, congruence by $\Lambda$ transforms the PPT inequality into

$$H=V+i((-\Omega)\oplus\Omega)\succeq0.$$

The real momentum-flip square and sign identities use `D5.S3.Quantum.FiniteDimensional.qubit_weyl_star` after the real-to-complex entry correspondences with `qubitZ` and `qubitX`. The helper `ppt_signed` performs this congruence.

Third, put $K=[-T,I]$ with $T=C^TA^{-1}$. Block multiplication and inverse cancellation give

$$KVK^T=B-C^TA^{-1}C=N,$$
$$K((-\Omega)\oplus\Omega)K^T=\Omega-T\Omega T^T.$$

Consequently $KHK^T=X_f\succeq0$. The helper `forward_congruence` proves the identity, and `ppt_both_directions` applies positive-semidefinite congruence.

Fourth, entrywise complex conjugation gives $\overline H=V+i(\Omega\oplus(-\Omega))\succeq0$. Exchanging the two modes and applying the same congruence gives $X_r\succeq0$. The helper `psd_entrywise_conj` and the swapped principal-index construction supply this step. The theorem `result` contradicts forward compatibility using the first conjunct of atemporality.

## Falsifier

A physical standard-form covariance matrix with both incompatible directions and a positive-semidefinite partially transposed uncertainty matrix would falsify the stated implication. The proof retains all real two-by-two blocks and both temporal directions; it introduces no commutativity or extra diagonal cross-block hypothesis. Replacing covariance NPT by an arbitrary Hilbert-space entanglement predicate without the Gaussian PPT bridge would exceed this formal statement.

## Evidence

Kernel evidence is `D5/S3/Estimation/GaussianAtemporalityEntanglement.result`, with the private matrix statements described above. The module has `generality: I`, `utility: none` and `admission_basis: open-problem-resolution (#19029; Proved)`. Every theorem is classified `bind-only`; no escape witness is asserted. The named external problem provides the admission basis, and every auxiliary theorem is consumed.

The four-slot escape audit for the sole public theorem `D5.S3.Estimation.GaussianAtemporalityEntanglement.result` is unfinished: [#19151](https://github.com/the-omega-institute/trureturing/issues/19151). No Reg mirror or validated registration is asserted. The generic dependent-family enrollment does not supply the required realization, statement bridge, variation, sensitivity and observational-dependence proofs for this covariance implication.

Experiment: [pinned result directory](https://github.com/the-omega-institute/trureturing-experiments/tree/057ac13a40ec8b5b52b5909815ec7d63cf0adfad/docs/reports/song-et-al-2025-gaussian-atemporality-implies-entanglement). Run `python3 check.py` from that directory; exit 0, `RESULT PASS 0`. Script SHA-256: `f12b7fc30b597e7bf2f2d8d14dfeff22d3f5527cb5587aeab6fcff5a96554b5b`.

The symbolic part checks the two congruence identities in each direction, Eq. (6)'s reconstruction identities and the partial-transpose sign identity, for positive diagonal local blocks and real cross-block entries. The numerical part checks 20,000 sampled physical standard-form covariance matrices with seed 20261019: 797 are PPT and all 797 compatible both ways; 18,298 are atemporal and all NPT; all 18,688 samples incompatible in at least one direction are NPT. A $40\times40$ source beam-splitter grid with $u\in[0.2,0.99]$ and $v\in[1.01,6]$ has 985 atemporal points, all NPT. These finite readings are computed checks, not a proof for the full covariance family.

## Triage

### What the settlement shows

- **Proved in Lean:** the source implication under the binding conventions, by `D5.S3.Estimation.GaussianAtemporalityEntanglement.result`.
- **Proved in Lean:** for physical covariance matrices, PPT implies compatibility in both directions without standard form, by the private theorem `D5.S3.Estimation.GaussianAtemporalityEntanglement.ppt_both_directions`. The formal statement retains physicality and drops the locally diagonal hypothesis.
- **Proved in prose from that theorem:** incompatibility in either direction suffices for the binding NPT entanglement predicate. If PPT held, `ppt_both_directions` would make both matrices positive semidefinite, contradicting either failed inequality. This is a logical consequence of the checked matrix theorem, not an additional public Lean declaration.
- **Literature-attested, not independently formalized:** the source's identification of covariance NPT with entanglement is exact for two-mode Gaussian states by its Gaussian PPT criterion. The finite-dimensional Song–Parzygnat theorem is a predecessor; it supplies no dependency in this module.
- **Computed:** the symbolic identities and finite numerical readings in the pinned experiment entry above. Their exact tested scope is that entry's symbolic standard-form family, 20,000 sampled states and $40\times40$ beam-splitter grid; the computation alone makes no uniform claim.
- **Open in this delivery:** the quantitative sufficient-entanglement threshold in Observation 1. The qualitative atemporality-implies-entanglement result neither supplies nor sharpens such a threshold.
- **Not a claimed equivalence:** the converse implication fails in the source's reported entangled but temporally compatible examples. These examples are literature evidence, not a counterexample formalized by this module.
- **Open:** external literature priority and exhaustive absence of a published settlement. Completeness is `ASSUMED-UNVERIFIED`.

The decisive mechanism is positivity preserved by the signed symplectic congruence. Standard form is unnecessary for that mechanism. The numerical implication associated with Figure 3 has a covariance proof; the source's converse discussion and Observation 1 remain separate claims, with no quantitative conclusion imported from this proof.

## ASSUMED-UNVERIFIED

The literature screen is bounded by #19029's accessible sources. Google Scholar returned HTTP 403, Semantic Scholar returned HTTP 429, and native MathDB was not accessed. No completeness or priority claim follows. The analytic Gaussian PPT bridge to Hilbert-space separability is taken from the source's literature rather than separately established by this Lean module. Four-slot escape registration remains unfinished under #19151.
