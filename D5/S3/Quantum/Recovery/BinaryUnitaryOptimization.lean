/- GID: D5/S3/Quantum/Recovery/BinaryUnitaryOptimization
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/BinaryUnitaryOptimization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Scalar phases attain the two-column complex norm bound. -/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-! A finite two-column optimization for binary unitary recovery. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ComplexConjugate InnerProductSpace
open Finset

noncomputable section

namespace D5.S3.Quantum.Recovery.BinaryUnitaryOptimization

variable {J H : Type*} [Fintype J]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The Hilbert–Schmidt length of the two weighted sums. -/
def columnLength (r s : ℝ) (z : J → ℂ) (v : J → H) : ℝ :=
  Real.sqrt (‖(r : ℂ) • ∑ j, v j‖ ^ 2 + ‖(s : ℂ) • ∑ j, z j • v j‖ ^ 2)

private lemma two_cauchy {a b c d : ℝ} (h : a ^ 2 + b ^ 2 = 1) :
    a * c + b * d ≤ Real.sqrt (c ^ 2 + d ^ 2) := by
  apply le_of_pow_le_pow_left₀ (n := 2) (by decide) (Real.sqrt_nonneg _)
  rw [Real.sq_sqrt (by positivity)]
  have h' := congrArg (fun x : ℝ => x * (c ^ 2 + d ^ 2)) h
  nlinarith [sq_nonneg (a * d - b * c)]

/-- Pairing with the normalized columns bounds the objective by a sum of norms. -/
theorem columnLength_le_dual (r s : ℝ) (z : J → ℂ) (v : J → H)
    (hv : ∀ j, ‖v j‖ ≤ 1) (hL : columnLength r s z v ≠ 0) :
    ∃ x y : H, ‖x‖ ^ 2 + ‖y‖ ^ 2 = 1 ∧
      columnLength r s z v ≤ ∑ j, ‖(r : ℂ) • x + ((s : ℂ) * conj (z j)) • y‖ := by
  let A : H := (r : ℂ) • ∑ j, v j
  let B : H := (s : ℂ) • ∑ j, z j • v j
  let L := columnLength r s z v
  have hLpos : 0 < L := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hL)
  have hsq : L ^ 2 = ‖A‖ ^ 2 + ‖B‖ ^ 2 := Real.sq_sqrt (by positivity)
  let x : H := ((L⁻¹ : ℝ) : ℂ) • A
  let y : H := ((L⁻¹ : ℝ) : ℂ) • B
  have hnorm : ‖x‖ ^ 2 + ‖y‖ ^ 2 = 1 := by
    simp only [x, y, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hLpos.le)]
    rw [mul_pow, mul_pow, ← mul_add, ← hsq]
    field_simp
  have hpair : (⟪x, A⟫_ℂ + ⟪y, B⟫_ℂ).re = L := by
    simp only [x, y, inner_smul_left, Complex.conj_ofReal, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    change L⁻¹ * RCLike.re ⟪A, A⟫_ℂ + L⁻¹ * RCLike.re ⟪B, B⟫_ℂ = L
    rw [← norm_sq_eq_re_inner, ← norm_sq_eq_re_inner]
    rw [← mul_add, ← hsq]
    field_simp
  refine ⟨x, y, hnorm, ?_⟩
  change L ≤ _
  rw [← hpair]
  have heq : ⟪x, A⟫_ℂ + ⟪y, B⟫_ℂ =
      ∑ j, ⟪(r : ℂ) • x + ((s : ℂ) * conj (z j)) • y, v j⟫_ℂ := by
    simp only [A, B, inner_smul_right, inner_sum, mul_sum, ← sum_add_distrib,
      inner_add_left, inner_smul_left, map_mul, Complex.conj_ofReal, Complex.conj_conj]
    exact sum_congr rfl fun _ _ => by ring
  rw [heq, Complex.re_sum]
  exact sum_le_sum fun j _ =>
    (re_inner_le_norm (𝕜 := ℂ) _ _).trans
      (mul_le_of_le_one_right (norm_nonneg _) (hv j))

private lemma scalar_gram (a : ℝ) (c : ℂ) (ha : 0 ≤ a)
    (hc : ‖c‖ ^ 2 = a * (1 - a)) :
    ∃ x y : ℂ, ‖x‖ ^ 2 = a ∧ ‖y‖ ^ 2 = 1 - a ∧ ⟪x, y⟫_ℂ = c := by
  rcases eq_or_lt_of_le ha with rfl | hpos
  · have hz : c = 0 := by simpa using hc
    exact ⟨0, 1, by simp, by simp, by simp [hz]⟩
  · have hs : 0 < Real.sqrt a := Real.sqrt_pos.2 hpos
    have hs2 := Real.sq_sqrt ha
    refine ⟨(Real.sqrt a : ℂ), c / (Real.sqrt a : ℂ), ?_, ?_, ?_⟩
    · simpa [Complex.norm_real, abs_of_nonneg hs.le] using hs2
    · rw [norm_div, div_pow, Complex.norm_of_nonneg hs.le, hs2, hc]
      field_simp
    · simp only [RCLike.inner_apply', Complex.conj_ofReal]
      have hsC : (Real.sqrt a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hs.ne'
      field_simp

lemma sq_form {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (x y : E) (a b : ℂ) :
    ‖a • x + b • y‖ ^ 2 =
      ‖a‖ ^ 2 * ‖x‖ ^ 2 + ‖b‖ ^ 2 * ‖y‖ ^ 2 +
        2 * (conj a * b * ⟪x, y⟫_ℂ).re := by
  rw [norm_add_sq (𝕜 := ℂ)]
  simp only [norm_smul, mul_pow, inner_smul_left, inner_smul_right]
  have h : b * (conj a * ⟪x, y⟫_ℂ) = conj a * b * ⟪x, y⟫_ℂ := by ring
  rw [h]
  change _ + 2 * (conj a * b * ⟪x, y⟫_ℂ).re + _ = _
  ring

/-- Choose a rank-one Gram matrix with the same off-diagonal entry. The
    diagonal endpoint increases every quadratic form of the given weights. -/
theorem rank_one_dual (r s : ℝ) (x y : H) (hn : ‖x‖ ^ 2 + ‖y‖ ^ 2 = 1) :
    ∃ b e : ℂ, ‖b‖ ^ 2 + ‖e‖ ^ 2 = 1 ∧
      ∀ z : ℂ, ‖z‖ = 1 →
        ‖(r : ℂ) • x + ((s : ℂ) * conj z) • y‖ ≤
          ‖(r : ℂ) * b + ((s : ℂ) * conj z) * e‖ := by
  let a := ‖x‖ ^ 2
  let c := ⟪x, y⟫_ℂ
  have hy : ‖y‖ ^ 2 = 1 - a := by dsimp [a]; linarith
  have hc : ‖c‖ ^ 2 ≤ a * (1 - a) := by
    rw [← hy, ← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm x y) 2
  have hdisc : 0 ≤ 1 - 4 * ‖c‖ ^ 2 := by nlinarith [sq_nonneg (2 * a - 1)]
  let t := Real.sqrt (1 - 4 * ‖c‖ ^ 2)
  have ht : t ^ 2 = 1 - 4 * ‖c‖ ^ 2 := Real.sq_sqrt hdisc
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have ht1 : t ≤ 1 := by nlinarith [sq_nonneg ‖c‖]
  have hdist : |2 * a - 1| ≤ t := by
    apply le_of_pow_le_pow_left₀ (n := 2) (by decide) ht0
    rw [sq_abs, ht]
    nlinarith
  let a' := if s ^ 2 ≤ r ^ 2 then (1 + t) / 2 else (1 - t) / 2
  have bounds : 0 ≤ a' ∧ a' ≤ 1 ∧ ‖c‖ ^ 2 = a' * (1 - a') ∧
      r ^ 2 * a + s ^ 2 * (1 - a) ≤ r ^ 2 * a' + s ^ 2 * (1 - a') := by
    rcases abs_le.mp hdist with ⟨hlo, hhi⟩
    by_cases h : s ^ 2 ≤ r ^ 2
    · simp only [a', ite_eq_left h]
      have hprod := mul_nonneg (sub_nonneg.mpr h) (show 0 ≤ (1 + t) / 2 - a by linarith)
      exact ⟨by linarith, by linarith, by nlinarith, by nlinarith⟩
    · simp only [a', ite_eq_right h]
      have hprod := mul_nonneg (sub_nonneg.mpr (le_of_not_ge h))
        (show 0 ≤ a - (1 - t) / 2 by linarith)
      exact ⟨by linarith, by linarith, by nlinarith, by nlinarith⟩
  obtain ⟨b, e, hb, he, hbe⟩ := scalar_gram a' c bounds.1 bounds.2.2.1
  refine ⟨b, e, by linarith, fun z hz => ?_⟩
  apply le_of_pow_le_pow_left₀ (n := 2) (by decide) (norm_nonneg _)
  change _ ≤ ‖(r : ℂ) • b + ((s : ℂ) * conj z) • e‖ ^ 2
  rw [sq_form, sq_form, hbe, hb, he, hy]
  simp only [norm_mul, Complex.norm_conj, hz, mul_one, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  exact add_le_add_left bounds.2.2.2 _

/-- The phase aligning a scalar with the nonnegative real axis. -/
def aligningPhase (m : ℂ) : ℂ := if m = 0 then 1 else m / (‖m‖ : ℂ)

theorem norm_aligningPhase (m : ℂ) : ‖aligningPhase m‖ = 1 := by
  by_cases hm : m = 0
  · simp [aligningPhase, hm]
  · simp [aligningPhase, hm]

theorem conj_mul_aligningPhase (m : ℂ) : conj m * aligningPhase m = (‖m‖ : ℂ) := by
  by_cases hm : m = 0
  · simp [hm, aligningPhase]
  · rw [aligningPhase, ite_eq_right hm, ← mul_div_assoc, mul_comm (conj m), Complex.mul_conj,
      Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
    have hn : (‖m‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 hm)
    field_simp

/-- Scalar phases attain at least the entire scalar dual sum. -/
theorem scalar_dual_le_phase (r s : ℝ) (z : J → ℂ) (b e : ℂ)
    (hn : ‖b‖ ^ 2 + ‖e‖ ^ 2 = 1) :
    (∑ j, ‖(r : ℂ) * b + (s : ℂ) * conj (z j) * e‖) ≤
      columnLength r s z (fun j => aligningPhase ((r : ℂ) * b + (s : ℂ) * conj (z j) * e)) := by
  let m (j : J) := (r : ℂ) * b + (s : ℂ) * conj (z j) * e
  let u (j : J) := aligningPhase (m j)
  let A := (r : ℂ) * ∑ j, u j
  let B := (s : ℂ) * ∑ j, z j * u j
  have hsum : (∑ j, ‖m j‖) = (conj b * A + conj e * B).re := by
    have heq : conj b * A + conj e * B = ∑ j, conj (m j) * u j := by
      simp only [A, B, m, mul_sum, ← sum_add_distrib, map_add, map_mul,
        Complex.conj_ofReal, Complex.conj_conj]
      exact sum_congr rfl fun _ _ => by ring
    rw [heq, Complex.re_sum]
    simp_rw [u, conj_mul_aligningPhase, Complex.ofReal_re]
  change (∑ j, ‖m j‖) ≤ Real.sqrt (‖A‖ ^ 2 + ‖B‖ ^ 2)
  rw [hsum, Complex.add_re]
  calc
    _ ≤ ‖b‖ * ‖A‖ + ‖e‖ * ‖B‖ := by
      simpa only [norm_mul, Complex.norm_conj] using
        add_le_add (Complex.re_le_norm (conj b * A)) (Complex.re_le_norm (conj e * B))
    _ ≤ _ := two_cauchy hn

/-- Every feasible vector family is dominated by unit-modulus scalar phases. -/
theorem phases_dominate (r s : ℝ) (z : J → ℂ) (hz : ∀ j, ‖z j‖ = 1)
    (v : J → H) (hv : ∀ j, ‖v j‖ ≤ 1) :
    ∃ u : J → ℂ, (∀ j, ‖u j‖ = 1) ∧ columnLength r s z v ≤ columnLength r s z u := by
  by_cases hL : columnLength r s z v = 0
  · exact ⟨fun _ => 1, fun _ => norm_one, hL ▸ Real.sqrt_nonneg _⟩
  · obtain ⟨x, y, hn, hupper⟩ := columnLength_le_dual r s z v hv hL
    obtain ⟨b, e, hbe, hform⟩ := rank_one_dual r s x y hn
    refine ⟨fun j => aligningPhase ((r : ℂ) * b + (s : ℂ) * conj (z j) * e),
      fun _ => norm_aligningPhase _, hupper.trans ?_⟩
    exact (sum_le_sum (fun j _ => hform (z j) (hz j))).trans (scalar_dual_le_phase r s z b e hbe)

theorem columnLength_sq (r s : ℝ) (z : J → ℂ) (v : J → H) :
    columnLength r s z v ^ 2 =
      r ^ 2 * ‖∑ j, v j‖ ^ 2 + s ^ 2 * ‖∑ j, z j • v j‖ ^ 2 := by
  rw [columnLength, Real.sq_sqrt (by positivity)]
  simp only [norm_smul, Complex.norm_real, mul_pow, Real.norm_eq_abs, sq_abs]

/-- Compactness yields a single phase family dominating every feasible family. -/
theorem optimal_phases (r s : ℝ) (z : J → ℂ) (hz : ∀ j, ‖z j‖ = 1) :
    ∃ u : J → ℂ, (∀ j, ‖u j‖ = 1) ∧ ∀ {E : Type*} [NormedAddCommGroup E]
      [InnerProductSpace ℂ E] (v : J → E), (∀ j, ‖v j‖ ≤ 1) →
        columnLength r s z v ≤ columnLength r s z u := by
  let phases : Set (J → ℂ) := Set.pi Set.univ (fun _ => Metric.sphere 0 1)
  have hc : IsCompact phases := isCompact_univ_pi fun _ => isCompact_sphere _ _
  have hm (u : J → ℂ) : u ∈ phases ↔ ∀ j, ‖u j‖ = 1 := by
    simp [phases]
  have hne : phases.Nonempty := ⟨fun _ => 1, (hm _).2 fun _ => norm_one⟩
  have hcont : Continuous (columnLength r s z : (J → ℂ) → ℝ) := by
    unfold columnLength
    fun_prop
  obtain ⟨u, hu, hmax⟩ := hc.exists_isMaxOn hne hcont.continuousOn
  refine ⟨u, (hm _).1 hu, fun v hv => ?_⟩
  obtain ⟨w, hw, hle⟩ := phases_dominate r s z hz v hv
  exact hle.trans (hmax ((hm _).2 hw))

#print axioms phases_dominate
#print axioms optimal_phases

end D5.S3.Quantum.Recovery.BinaryUnitaryOptimization
