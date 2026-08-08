/- GID: D5/S3/Divergence/GrandmotherTheorem
   generality: G
   mirror-B: D5/B/S3/Divergence/GrandmotherTheorem
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Prove nonnegativity of finite classical KL divergence under absolute continuity. -/

/- Library-search audit trail (2026-08-08):
   * Local pinned-mathlib grep terms: `klDiv_nonneg`, `klDiv_eq_zero_iff`, `klFun_nonneg`,
     `convexOn_neg_log`, `ConvexOn.map_sum_le`, `StrictConvexOn.map_sum_lt`,
     `Real.inner_le_nnorm`, `sum_mul_log`, and `Gibbs`.
   * `Mathlib.InformationTheory.KullbackLeibler.Basic` provides measure-valued `klDiv`,
     Gibbs' inequality as `InformationTheory.integral_llr_add_sub_measure_univ_nonneg`, and
     `InformationTheory.klDiv_eq_zero_iff`. Its divergence takes values in `ℝ≥0∞`.
   * No pinned theorem was found that identifies that measure-valued divergence with the real
     finite sum `ClassicalDPI.klDivergence` used here.
   * `InformationTheory.klFun_nonneg` is the directly reusable real-valued Gibbs core. Multiplying
     `klFun (p i / q i)` by `q i` and summing produces `klDivergence p q` plus the affine correction
     `∑ i, q i - ∑ i, p i`, which vanishes by normalization. The proof below is therefore the
     thinnest bridge to the upstream nonnegativity result and does not rebuild Jensen machinery.
     At a zero of `q`, absolute continuity makes `p` zero as well; the proof treats that boundary
     case separately before simplifying the positive-denominator terms.
-/

import D5.S3.Divergence.ClassicalDPI

namespace D5.S3.Divergence.GrandmotherTheorem

open D5.S3.Divergence.ClassicalDPI
open InformationTheory

/-- Gibbs' inequality for the real-valued finite KL divergence used by `ClassicalDPI`.
The hypotheses give nonnegative normalized masses and discrete absolute continuity `p ≪ q`. -/
theorem kl_divergence_nonneg {ι : Type*} [Fintype ι]
    (p q : ι → ℝ)
    (hp : (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1)
    (hq : (∀ i, 0 ≤ q i) ∧ ∑ i, q i = 1)
    (hac : ∀ i, q i = 0 → p i = 0) :
    0 ≤ klDivergence p q := by
  have hterm (i : ι) : 0 ≤ q i * klFun (p i / q i) :=
    mul_nonneg (hq.1 i) (klFun_nonneg (div_nonneg (hp.1 i) (hq.1 i)))
  rw [klDivergence]
  calc
    0 ≤ ∑ i, q i * klFun (p i / q i) := Finset.sum_nonneg fun i _ => hterm i
    _ = ∑ i, (p i * Real.log (p i / q i) + q i - p i) := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hqi : q i = 0
      · simp [hqi, hac i hqi, klFun_apply]
      · rw [klFun_apply]
        field_simp [hqi]
    _ = (∑ i, p i * Real.log (p i / q i)) + ∑ i, q i - ∑ i, p i := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    _ = ∑ i, p i * Real.log (p i / q i) := by rw [hq.2, hp.2, add_sub_cancel_right]

end D5.S3.Divergence.GrandmotherTheorem
