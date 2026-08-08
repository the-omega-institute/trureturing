/- GID: D5/S3/Divergence/GibbsEquality
   generality: G
   mirror-B: D5/B/S3/Divergence/GibbsEquality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Characterize equality in Gibbs' inequality for finite probability distributions. -/

/- Library-search audit trail (2026-08-08):
   * Local pinned-mathlib grep terms: `klFun_eq_zero_iff`, `strictConvexOn_klFun`,
     `klFun_pos_of_ne_one`, `klFun_nonneg`, `sum_eq_zero_iff_of_nonneg`, and
     `Fintype.sum_eq_zero_iff_of_nonneg`.
   * `Mathlib.InformationTheory.KullbackLeibler.KLFun` provides the exact strictness result
     `InformationTheory.klFun_eq_zero_iff`: on the nonnegative half-line, `klFun x = 0` if and
     only if `x = 1`. Its proof already uses `strictConvexOn_klFun`; no convexity argument is
     repeated here. No pinned theorem named `klFun_pos_of_ne_one` was found.
   * `Finset.sum_eq_zero_iff_of_nonneg` is the exact finite-sum equality criterion required below.
     The proof only supplies its pointwise nonnegativity premise and then invokes the upstream
     zero characterization term by term.
   * The repository definitions and nonnegativity theorem remain the single sources imported from
     `ClassicalDPI` and `GrandmotherTheorem`; this file neither redefines divergence nor reproves
     Gibbs' inequality.
-/

import D5.S3.Divergence.ClassicalDPI
import D5.S3.Divergence.GrandmotherTheorem

namespace D5.S3.Divergence.GibbsEquality

open D5.S3.Divergence.ClassicalDPI
open D5.S3.Divergence.GrandmotherTheorem
open InformationTheory

/-- Equality in Gibbs' inequality holds exactly when the two finite probability mass functions
agree pointwise. Absolute continuity handles the coordinates where the reference mass is zero. -/
theorem kl_divergence_eq_zero_iff {ι : Type*} [Fintype ι]
    (p q : ι → ℝ)
    (hp : (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1)
    (hq : (∀ i, 0 ≤ q i) ∧ ∑ i, q i = 1)
    (hac : ∀ i, q i = 0 → p i = 0) :
    klDivergence p q = 0 ↔ p = q := by
  classical
  have hterm (i : ι) : 0 ≤ q i * klFun (p i / q i) :=
    mul_nonneg (hq.1 i) (klFun_nonneg (div_nonneg (hp.1 i) (hq.1 i)))
  have hrepresentation :
      klDivergence p q = ∑ i, q i * klFun (p i / q i) := by
    rw [klDivergence]
    calc
      (∑ i, p i * Real.log (p i / q i)) =
          (∑ i, p i * Real.log (p i / q i)) + ∑ i, q i - ∑ i, p i := by
            rw [hq.2, hp.2, add_sub_cancel_right]
      _ = ∑ i, (p i * Real.log (p i / q i) + q i - p i) := by
            rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
      _ = ∑ i, q i * klFun (p i / q i) := by
            apply Finset.sum_congr rfl
            intro i _
            by_cases hqi : q i = 0
            · simp [hqi, hac i hqi, klFun_apply]
            · rw [klFun_apply]
              field_simp [hqi]
  constructor
  · intro hzero
    have hsum_nonneg : 0 ≤ ∑ i, q i * klFun (p i / q i) := by
      rw [← hrepresentation]
      exact kl_divergence_nonneg p q hp hq hac
    have hsum_nonpos : ∑ i, q i * klFun (p i / q i) ≤ 0 := by
      rw [← hrepresentation, hzero]
    have hsum_zero : ∑ i, q i * klFun (p i / q i) = 0 :=
      le_antisymm hsum_nonpos hsum_nonneg
    have hall : ∀ i ∈ Finset.univ, q i * klFun (p i / q i) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hterm i).mp hsum_zero
    funext i
    by_cases hqi : q i = 0
    · simpa [hqi] using hac i hqi
    · have hkl_zero : klFun (p i / q i) = 0 :=
        (mul_eq_zero.mp (hall i (Finset.mem_univ i))).resolve_left hqi
      have hratio : p i / q i = 1 :=
        (klFun_eq_zero_iff (div_nonneg (hp.1 i) (hq.1 i))).mp hkl_zero
      exact (div_eq_one_iff_eq hqi).mp hratio
  · rintro rfl
    rw [klDivergence]
    apply Finset.sum_eq_zero
    intro i _
    by_cases hpi : p i = 0
    · simp [hpi]
    · simp [hpi]

end D5.S3.Divergence.GibbsEquality
