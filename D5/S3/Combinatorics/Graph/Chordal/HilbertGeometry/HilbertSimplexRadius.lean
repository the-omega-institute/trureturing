/- GID: D5/S3/Combinatorics/Graph/Chordal/HilbertGeometry/HilbertSimplexRadius
   generality: G
   mirror-B: none(waiver:covered-by-chordal-banach-exact-strata-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Centred regular simplices realize the sharp finite Hilbert enclosing radius. -/

import OmegaBuild.Commands
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

compile_only_with_mathlib

/-! Omega original.

Centred regular simplices realize the sharp finite Hilbert enclosing radius.
-/

open scoped BigOperators InnerProductSpace RealInnerProductSpace

namespace FiniteHilbertJung

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι] [Nonempty ι]

omit [Nonempty ι] in
private lemma sum_norm_sub_sq (a : ι → E) (x : E) :
    ∑ i, ‖a i - x‖ ^ 2 =
      (∑ i, ‖a i‖ ^ 2) - 2 * ⟪(∑ i, a i), x⟫_ℝ +
        (Fintype.card ι : ℝ) * ‖x‖ ^ 2 := by
  simp_rw [norm_sub_sq_real]
  simp_rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [← Finset.mul_sum, ← sum_inner]
  simp [Finset.sum_const]

omit [Nonempty ι] in
private lemma sum_norm_sub_sq_of_sum_eq_zero (a : ι → E) (x : E)
    (hzero : ∑ i, a i = 0) :
    ∑ i, ‖a i - x‖ ^ 2 =
      (∑ i, ‖a i‖ ^ 2) + (Fintype.card ι : ℝ) * ‖x‖ ^ 2 := by
  rw [sum_norm_sub_sq, hzero, inner_zero_left]
  ring

/-- A centred constant-norm family has radius at least its common norm. -/
theorem radius_lower_of_centred_constant_norm
    (a : ι → E) (r R : ℝ) (x : E)
    (hzero : ∑ i, a i = 0)
    (hnorm : ∀ i, ‖a i‖ ^ 2 = r ^ 2)
    (hball : ∀ i, ‖a i - x‖ ≤ R) :
    r ≤ R := by
  have hcard : (0 : ℝ) < Fintype.card ι := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card ι)
  have hR : 0 ≤ R := by
    let i : ι := Classical.choice ‹Nonempty ι›
    exact le_trans (norm_nonneg (a i - x)) (hball i)
  have hsq : r ^ 2 ≤ R ^ 2 := by
    have hsum : (∑ i, ‖a i - x‖ ^ 2) ≤
        ∑ _ : ι, R ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      exact (sq_le_sq₀ (norm_nonneg _) (by exact hR)).2 (hball i)
    have hsumR : (∑ _ : ι, R ^ 2) = (Fintype.card ι : ℝ) * R ^ 2 := by
      simp
    rw [sum_norm_sub_sq_of_sum_eq_zero a x hzero] at hsum
    rw [show (∑ i, ‖a i‖ ^ 2) = (Fintype.card ι : ℝ) * r ^ 2 by
      simp_rw [hnorm]
      simp] at hsum
    rw [hsumR] at hsum
    nlinarith [sq_nonneg (‖x‖ : ℝ)]
  nlinarith [hsq]

section Simplex

open Finset

/-- A diameter-one simplex in real Euclidean space, with a witness to the
doubled enclosing radius at each possible center. -/
theorem exists_diameter_one_simplex (k : ℕ) (hk : 0 < k) :
    ∃ x : Fin k → EuclideanSpace ℝ (Fin k),
      (∀ a b, ‖x a - x b‖ ≤ 1) ∧
      ∀ y, ∃ a, Real.sqrt (2 - 2 / (k : ℝ)) ≤ ‖(2 : ℝ) • x a - y‖ := by
  classical
  let : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  let K : ℝ := k
  have hK : 0 < K := Nat.cast_pos.mpr hk
  have hK1 : 1 ≤ K := by
    dsimp [K]
    exact_mod_cast (show 1 ≤ k from hk)
  let e (a : Fin k) := EuclideanSpace.single a (1 : ℝ)
  let b : EuclideanSpace ℝ (Fin k) := WithLp.toLp 2 fun _ : Fin k => 1 / K
  let c := Real.sqrt 2
  let x (a : Fin k) := (c / 2) • (e a - b)
  have hc : c ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hcn : 0 ≤ c := Real.sqrt_nonneg _
  have hbcoord (i : Fin k) : b i = 1 / K := rfl
  have hbn : ‖b‖ ^ 2 = 1 / K := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [hbcoord, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    change K * (1 / K) ^ 2 = 1 / K
    field_simp
  have he (i : Fin k) : ‖e i‖ = 1 := by simp [e, PiLp.norm_single]
  have heia (i : Fin k) : ⟪e i, b⟫_ℝ = 1 / K := by
    simp [e, EuclideanSpace.inner_single_left, hbcoord]
  have heij (i j : Fin k) (h : i ≠ j) : ⟪e i, e j⟫_ℝ = 0 := by
    simp [e, EuclideanSpace.inner_single_left, h]
  have hcsub (i : Fin k) : ‖e i - b‖ ^ 2 = 1 - 1 / K := by
    rw [norm_sub_sq_real, he, heia, hbn]
    ring
  have hsum : ∑ a, (e a - b) = 0 := by
    apply PiLp.ext
    intro i
    simp only [Finset.sum_sub_distrib, PiLp.sub_apply, PiLp.zero_apply]
    change ((∑ a, e a) - ∑ _a : Fin k, b) i = 0
    rw [PiLp.sub_apply]
    have heall : (∑ a, e a) i = 1 := by
      change WithLp.ofLp (∑ a, e a) i = 1
      simp [WithLp.ofLp_sum, e]
    rw [heall, Finset.sum_const, Finset.card_univ, Fintype.card_fin, PiLp.smul_apply,
      hbcoord, nsmul_eq_mul]
    change 1 - K * (1 / K) = 0
    field_simp
    norm_num
  refine ⟨x, ?_, ?_⟩
  · intro i j
    by_cases hij : i = j
    · simp [hij]
    have hx : x i - x j = (c / 2) • (e i - e j) := by
      simp only [x, ← smul_sub]
      rw [show e i - b - (e j - b) = e i - e j by abel]
    have hnorm : ‖e i - e j‖ ^ 2 = 2 := by
      rw [norm_sub_sq_real, he, he, heij i j hij]
      norm_num
    have hsq : ‖x i - x j‖ ^ 2 = 1 := by
      rw [hx, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), mul_pow, hnorm,
        div_pow, hc]
      norm_num
    nlinarith [norm_nonneg (x i - x j)]
  · intro y
    let r := Real.sqrt (2 - 2 / (k : ℝ))
    have hrnon : 0 ≤ 2 - 2 / K := by
      have : 1 / K ≤ 1 := (div_le_iff₀ hK).2 (by linarith)
      rw [show 2 / K = 2 * (1 / K) by ring]
      linarith
    have hdbl (i : Fin k) : (2 : ℝ) • x i = c • (e i - b) := by
      dsimp [x]
      rw [smul_smul, show 2 * (c / 2) = c by ring]
    have hzero : ∑ i, (2 : ℝ) • x i = 0 := by
      simp_rw [hdbl]
      rw [← Finset.smul_sum, hsum, smul_zero]
    have hnorm (i : Fin k) : ‖(2 : ℝ) • x i‖ ^ 2 = r ^ 2 := by
      rw [hdbl, norm_smul, Real.norm_eq_abs, abs_of_nonneg hcn, mul_pow, hc, hcsub,
        Real.sq_sqrt hrnon]
      ring
    obtain ⟨a, -, ha⟩ := Finset.exists_max_image Finset.univ
      (fun i => ‖(2 : ℝ) • x i - y‖) Finset.univ_nonempty
    exact ⟨a, radius_lower_of_centred_constant_norm _ r _ y hzero hnorm
      (fun i => ha i (Finset.mem_univ i))⟩

end Simplex
end
end FiniteHilbertJung
