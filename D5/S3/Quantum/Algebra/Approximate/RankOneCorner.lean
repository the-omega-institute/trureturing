/- GID: D5/S3/Quantum/Algebra/Approximate/RankOneCorner
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/Approximate/RankOneCorner
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Conditional scalar geometry of the actual one-dimensional corrected corner. -/

import D5.S3.Quantum.Algebra.Approximate.RegularCompression

/-! The original product, norm, involution and corrected corners are retained.
Exact one-dimensionality is supplied only as a conditional extension input. -/

noncomputable section
set_option autoImplicit false

namespace D5.S3.Quantum.Algebra.Approximate.RegularCompression.Product

open scoped InnerProductSpace


variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [FiniteDimensional ℂ H] [StarAddMonoid H] [StarModule ℂ H]
  {M δ : ℝ} (D : Product H M δ)

local instance : CompleteSpace H := FiniteDimensional.complete ℂ H

/-- The rank-one hypothesis is an input of the conditional extension lemma. -/
structure RankOneInput (Q : H) (τ : ℝ) : Prop where
  selfadjoint : star Q = Q
  tau_nonneg : 0 ≤ τ
  small : τ + M * δ ≤ 1 / 1024
  defect : D.p (D.mul Q Q - Q) ≤ τ
  positive : 520000 * (τ + M * δ) * M ^ 2 ≤ 1
  dimension : Module.finrank ℂ (D.corner Q Q) = 1

variable {D} {Q : H} {τ : ℝ} (I : D.RankOneInput Q τ)

/-- The designated approximate unit is not rescaled. -/
def cornerUnit (D : Product H M δ) (Q : H) : H := D.compression Q Q Q

include I

private theorem radius_bounds :
    0 ≤ τ + M * δ ∧ τ ≤ τ + M * δ ∧ δ ≤ τ + M * δ ∧
      τ + M * δ ≤ 1 / 520000 := by
  have hM : 0 ≤ M := le_trans zero_le_one D.one_le_M
  have he := mul_nonneg hM D.delta_nonneg
  have hτ0 := I.tau_nonneg
  have hr := add_nonneg hτ0 he
  have hδ : δ ≤ M * δ := by nlinarith [D.one_le_M, D.delta_nonneg]
  have hM2 : 1 ≤ M ^ 2 := by nlinarith [D.one_le_M]
  refine ⟨hr, by linarith, by linarith, ?_⟩
  nlinarith [I.positive, mul_nonneg hr (sub_nonneg.mpr hM2)]

private theorem unit_closeness :
    D.p (D.cornerUnit Q - Q) ≤ 9737 * (τ + M * δ) := by
  obtain ⟨hr, hτ, hδ, hb⟩ := (radius_bounds I)
  have hq := D.projection_norm_le_two Q I.selfadjoint
    (by linarith : τ ≤ 1 / 4) (by linarith : δ ≤ 1 / 4) I.defect
  have hc := (D.compression_closeness Q Q I.selfadjoint I.selfadjoint
    I.tau_nonneg I.small I.defect I.defect Q).1
  have hm := D.p_mul Q (D.mul Q Q - Q)
  have hm' : D.p (D.mul Q (D.mul Q Q - Q)) ≤ 4 * τ := by
    calc
      _ ≤ (1 + δ) * D.p Q * τ := hm.trans
        (mul_le_mul_of_nonneg_left I.defect (mul_nonneg (by linarith [D.delta_nonneg]) (show 0 ≤ D.p Q from norm_nonneg _)))
      _ ≤ _ := by
        have ha : (1 + δ) * D.p Q ≤ 4 := by
          have hh := mul_le_mul_of_nonneg_right (by linarith : 1 + δ ≤ 2)
            (show 0 ≤ D.p Q from norm_nonneg _)
          linarith
        exact mul_le_mul_of_nonneg_right ha I.tau_nonneg
  have hid : D.cornerUnit Q - Q =
      (D.compression Q Q Q - D.mul Q (D.mul Q Q)) +
        (D.mul Q (D.mul Q Q - Q) + (D.mul Q Q - Q)) := by
    simp only [cornerUnit, map_sub]
    abel
  rw [hid]
  have ha := D.p_add (D.compression Q Q Q - D.mul Q (D.mul Q Q))
    (D.mul Q (D.mul Q Q - Q) + (D.mul Q Q - Q))
  have ha' := D.p_add (D.mul Q (D.mul Q Q - Q)) (D.mul Q Q - Q)
  have hd := I.defect
  nlinarith [mul_le_mul_of_nonneg_left hq (by positivity : 0 ≤ 4866 * (τ + M * δ))]

private theorem compression_bound (z : H) :
    D.p (D.compression Q Q z) ≤ 5 * D.p z := by
  obtain ⟨hr, hτ, hδ, hb⟩ := (radius_bounds I)
  have hq := D.projection_norm_le_two Q I.selfadjoint
    (by linarith : τ ≤ 1 / 4) (by linarith : δ ≤ 1 / 4) I.defect
  have hn : 0 ≤ D.p z := norm_nonneg _
  have hq0 : 0 ≤ D.p Q := norm_nonneg _
  have hm (x : H) : D.p (D.mul Q x) ≤ (201 / 100) * D.p x := by
    apply (D.p_mul Q x).trans
    have h : (1 + δ) * D.p Q ≤ 201 / 100 := by nlinarith
    exact mul_le_mul_of_nonneg_right h (norm_nonneg _)
  have hm' : D.p (D.mul z Q) ≤ (201 / 100) * D.p z := by
    apply (D.p_mul z Q).trans
    have h : (1 + δ) * D.p Q ≤ 201 / 100 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h hn]
  have hprod := (hm (D.mul z Q)).trans
    (mul_le_mul_of_nonneg_left hm' (by norm_num))
  have hc := (D.compression_closeness Q Q I.selfadjoint I.selfadjoint
    I.tau_nonneg I.small I.defect I.defect z).1
  have ha := D.p_add (D.compression Q Q z - D.mul Q (D.mul z Q))
    (D.mul Q (D.mul z Q))
  simp only [sub_add_cancel] at ha
  nlinarith [mul_le_mul_of_nonneg_right hb hn]

private theorem unit_action {x : H} (hx : x ∈ D.corner Q Q) :
    D.p (D.compression Q Q (D.mul (D.cornerUnit Q) x) - x) ≤
      219140 * (τ + M * δ) * D.p x := by
  obtain ⟨hr, hτ, hδ, hb⟩ := (radius_bounds I)
  have hs := D.corner_left_support Q Q I.selfadjoint I.selfadjoint
    I.tau_nonneg I.small I.defect I.defect hx
  have hm := D.p_mul (D.cornerUnit Q - Q) x
  have hm' : D.p (D.mul (D.cornerUnit Q - Q) x) ≤
      (2 * 9737) * (τ + M * δ) * D.p x := by
    have ht := (unit_closeness I)
    have hc : (1 + δ) * D.p (D.cornerUnit Q - Q) ≤
        2 * (9737 * (τ + M * δ)) := by
      calc
        _ ≤ 2 * D.p (D.cornerUnit Q - Q) := by
          exact mul_le_mul_of_nonneg_right (by linarith : 1 + δ ≤ 2)
            (show 0 ≤ D.p (D.cornerUnit Q - Q) from norm_nonneg _)
        _ ≤ _ := by linarith
    exact hm.trans (by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hc
        (show 0 ≤ D.p x from norm_nonneg _))
  have hid : D.compression Q Q (D.mul (D.cornerUnit Q) x) - x =
      D.compression Q Q (D.mul (D.cornerUnit Q - Q) x + (D.mul Q x - x)) := by
    simp only [map_add, map_sub, sub_apply]
    rw [D.compression_eq_self_of_mem Q Q I.selfadjoint I.selfadjoint
        I.tau_nonneg I.small I.defect I.defect hx]
    abel
  rw [hid]
  apply ((compression_bound I) _).trans
  have ha := D.p_add (D.mul (D.cornerUnit Q - Q) x) (D.mul Q x - x)
  linarith

private theorem unit_ne_zero : D.cornerUnit Q ≠ 0 := by
  let : Nontrivial (D.corner Q Q) := Module.nontrivial_of_finrank_eq_succ I.dimension
  obtain ⟨x, hx⟩ := exists_ne (0 : D.corner Q Q)
  have hx0 : (x : H) ≠ 0 := fun h => hx (Subtype.ext h)
  have hn : 0 < D.p (x : H) := lt_of_lt_of_le (norm_pos_iff.mpr hx0) (D.norm_le_p _)
  intro hz
  have h := (unit_action I) x.property
  simp only [hz, map_zero, zero_apply, zero_sub, p, map_neg,
    norm_neg] at h
  have hb := (radius_bounds I).2.2.2
  have hlt : 219140 * (τ + M * δ) < 1 := by linarith
  change 0 < ‖D.mul (x : H)‖ at hn
  nlinarith [mul_pos (sub_pos.mpr hlt) hn]

private theorem unit_mem : D.cornerUnit Q ∈ D.corner Q Q := ⟨Q, rfl⟩

private theorem unit_star : star (D.cornerUnit Q) = D.cornerUnit Q := by
  simpa only [cornerUnit, I.selfadjoint] using
    D.compression_star Q Q I.selfadjoint I.selfadjoint I.tau_nonneg I.small
      I.defect I.defect Q

/-- A coordinate on the literal designated corner line, defined on the original H. -/
def cornerCoordinate (D : Product H M δ) (Q : H) : H →ₗ[ℂ] ℂ :=
  (inner ℂ (D.cornerUnit Q) (D.cornerUnit Q))⁻¹ • innerₛₗ ℂ (D.cornerUnit Q)

private theorem coordinate_smul (c : ℂ) :
    D.cornerCoordinate Q (c • D.cornerUnit Q) = c := by
  have ht : inner ℂ (D.cornerUnit Q) (D.cornerUnit Q) ≠ 0 :=
    inner_self_ne_zero.mpr (unit_ne_zero I)
  simp only [cornerCoordinate, LinearMap.smul_apply, smul_eq_mul,
    innerₛₗ_apply_apply, inner_smul_right]
  rw [mul_comm c, ← mul_assoc, inv_mul_cancel₀ ht, one_mul]

private theorem coordinate_eq {x : H} (hx : x ∈ D.corner Q Q) :
    D.cornerCoordinate Q x • D.cornerUnit Q = x := by
  have hs := eq_span_singleton_of_mem_of_finrank_eq_one I.dimension
    (unit_mem I) (unit_ne_zero I)
  rw [hs, Submodule.mem_span_singleton] at hx
  obtain ⟨c, rfl⟩ := hx
  rw [(coordinate_smul I)]

private theorem coordinate_star {x : H} (hx : x ∈ D.corner Q Q) :
    D.cornerCoordinate Q (star x) = star (D.cornerCoordinate Q x) := by
  calc
    _ = D.cornerCoordinate Q (star (D.cornerCoordinate Q x • D.cornerUnit Q)) :=
      congrArg (fun z => D.cornerCoordinate Q (star z)) ((coordinate_eq I) hx).symm
    _ = _ := by rw [star_smul, (unit_star I), (coordinate_smul I)]

/-- The actual compressed-product coefficient with the original generator. -/
def cornerPairing (D : Product H M δ) (Q : H) (y x : H) : ℂ :=
  D.cornerCoordinate Q (D.compression Q Q (D.mul (star y) x))

private theorem pairing_equation (y x : H) :
    D.cornerPairing Q y x • D.cornerUnit Q =
      D.compression Q Q (D.mul (star y) x) := (coordinate_eq I) ⟨_, rfl⟩

private theorem pairing_hermitian (y x : H) :
    star (D.cornerPairing Q y x) = D.cornerPairing Q x y := by
  rw [cornerPairing, ← (coordinate_star I) (show D.compression Q Q (D.mul (star y) x) ∈
    D.corner Q Q from ⟨_, rfl⟩), D.compression_star Q Q I.selfadjoint I.selfadjoint I.tau_nonneg
      I.small I.defect I.defect, D.star_mul, star_star]
  rfl

private theorem pairing_self_real (x : H) :
    D.cornerPairing Q x x = ((D.cornerPairing Q x x).re : ℂ) := by
  have h := congrArg Complex.im ((pairing_hermitian I) x x)
  simp only [Complex.star_def, Complex.conj_im] at h
  apply Complex.ext
  · simp
  · simp only [Complex.ofReal_im]
    linarith

/-- The scale of the designated generator in its own scalar geometry. -/
def cornerBeta (D : Product H M δ) (Q : H) : ℝ :=
  (D.cornerPairing Q (D.cornerUnit Q) (D.cornerUnit Q)).re

/-- The original Hilbert expectation of the designated generator. -/
def cornerAlpha (D : Product H M δ) (Q : H) : ℝ :=
  (inner ℂ D.unit (D.cornerUnit Q)).re

private theorem beta_bounds : |D.cornerBeta Q - 1| ≤ 219140 * (τ + M * δ) := by
  have h := (unit_action I) (unit_mem I)
  have he := (pairing_equation I) (D.cornerUnit Q) (D.cornerUnit Q)
  rw [(unit_star I)] at he
  rw [← he] at h
  have hid : D.cornerPairing Q (D.cornerUnit Q) (D.cornerUnit Q) • D.cornerUnit Q -
      D.cornerUnit Q =
      (D.cornerPairing Q (D.cornerUnit Q) (D.cornerUnit Q) - 1) • D.cornerUnit Q := by
    module
  rw [hid] at h
  simp only [p, map_smul, norm_smul] at h
  have hn : 0 < D.p (D.cornerUnit Q) :=
    (norm_pos_iff.mpr (unit_ne_zero I)).trans_le (D.norm_le_p _)
  change 0 < ‖D.mul (D.cornerUnit Q)‖ at hn
  have hc : ‖D.cornerPairing Q (D.cornerUnit Q) (D.cornerUnit Q) - 1‖ ≤
      219140 * (τ + M * δ) := (mul_le_mul_iff_left₀ hn).mp (by nlinarith only [h])
  exact (Complex.abs_re_le_norm _).trans hc

private theorem beta_pos : 0 < D.cornerBeta Q := by
  have h := (abs_le.mp (beta_bounds I)).1
  have hb := (radius_bounds I).2.2.2
  linarith

private theorem expectation_eq (x : H) :
    (inner ℂ D.unit (D.compression Q Q (D.mul (star x) x))).re =
      D.cornerAlpha Q * (D.cornerPairing Q x x).re := by
  rw [← (pairing_equation I) x x, inner_smul_right, (pairing_self_real I)]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, cornerAlpha]
  ring

private theorem alpha_pos : 0 < D.cornerAlpha Q := by
  have h := (D.corner_square_nondegenerate Q Q I.selfadjoint I.selfadjoint
    I.tau_nonneg I.small I.defect I.defect I.positive (unit_mem I)).1
  rw [(expectation_eq I)] at h
  have hn := norm_pos_iff.mpr (unit_ne_zero I)
  have hb := (beta_pos I)
  change ‖D.cornerUnit Q‖ ^ 2 / 2 ≤ D.cornerAlpha Q * D.cornerBeta Q at h
  nlinarith

private theorem pairing_positive (P : H) (hP : star P = P)
    (hPP : D.p (D.mul P P - P) ≤ τ) {x : H} (hx : x ∈ D.corner P Q) :
    0 ≤ (D.cornerPairing Q x x).re ∧
      ((D.cornerPairing Q x x).re = 0 ↔ x = 0) := by
  have h := (D.corner_square_nondegenerate P Q hP I.selfadjoint
    I.tau_nonneg I.small hPP I.defect I.positive hx).1
  rw [(expectation_eq I)] at h
  have ha := (alpha_pos I)
  refine ⟨by nlinarith [sq_nonneg ‖x‖], ?_⟩
  constructor
  · intro hz
    rw [hz, mul_zero] at h
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg x])
  · rintro rfl
    simp [cornerPairing]

private theorem pairing_hilbert_bounds (P : H) (hP : star P = P)
    (hPP : D.p (D.mul P P - P) ≤ τ) {x : H} (hx : x ∈ D.corner P Q) :
    (1 - 260000 * (τ + M * δ) * M ^ 2) * ‖x‖ ^ 2 ≤
      D.cornerAlpha Q * (D.cornerPairing Q x x).re ∧
    D.cornerAlpha Q * (D.cornerPairing Q x x).re ≤
      (1 + 260000 * (τ + M * δ) * M ^ 2) * ‖x‖ ^ 2 := by
  have hsx : star x ∈ D.corner Q P := by
    obtain ⟨z, rfl⟩ := hx
    exact ⟨star z, (D.compression_star P Q hP I.selfadjoint I.tau_nonneg
      I.small hPP I.defect z).symm⟩
  have hs := D.corner_product_support Q P Q I.selfadjoint hP I.selfadjoint
    I.tau_nonneg I.small I.defect hPP I.defect hsx hx
  rw [D.p_star] at hs
  have he : ‖D.compression Q Q (D.mul (star x) x) - D.mul (star x) x‖ ≤
      260000 * (τ + M * δ) * D.p x ^ 2 := by
    exact (D.norm_le_p _).trans (by simpa only [pow_two, mul_assoc] using hs)
  have hid : inner ℂ D.unit (D.mul (star x) x) = inner ℂ x x := by
    simpa only [D.adjoint_mul, D.right_unit] using
      ContinuousLinearMap.adjoint_inner_right (D.mul x) D.unit x
  have hc := norm_inner_le_norm (𝕜 := ℂ) D.unit
    (D.compression Q Q (D.mul (star x) x) - D.mul (star x) x)
  rw [D.unit_norm, one_mul] at hc
  have hd := (Complex.abs_re_le_norm _).trans (hc.trans he)
  rw [inner_sub_right, hid] at hd
  change |(inner ℂ D.unit (D.compression Q Q (D.mul (star x) x))).re -
    (inner ℂ x x).re| ≤ _ at hd
  rw [(expectation_eq I)] at hd
  have hself : (inner ℂ x x).re = ‖x‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) x
  rw [hself] at hd
  have hr := (radius_bounds I).1
  have hn : D.p x ^ 2 ≤ (M * ‖x‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (D.p_le x) 2
  have hb := mul_le_mul_of_nonneg_left hn
    (by positivity : 0 ≤ 260000 * (τ + M * δ))
  constructor <;> nlinarith only [(abs_le.mp hd).1, (abs_le.mp hd).2, hb]

private theorem square_norm_bounds (x : H) :
    (1 - δ) * D.p x ^ 2 ≤ D.p (D.mul (star x) x) ∧
      D.p (D.mul (star x) x) ≤ (1 + δ) * D.p x ^ 2 := by
  have ha := D.action_defect (star x) x
  have hnorm : ‖D.mul (star x) * D.mul x‖ = D.p x ^ 2 := by
    simpa only [D.adjoint_mul, p, pow_two, ContinuousLinearMap.mul_def] using
      ContinuousLinearMap.norm_adjoint_comp_self (D.mul x)
  have hb := norm_sub_norm_le (D.mul (star x) * D.mul x) (D.mul (D.mul (star x) x))
  rw [norm_sub_rev] at ha
  rw [hnorm] at hb
  have hs : ‖star x‖ ≤ D.p x := by simpa only [D.p_star] using D.norm_le_p (star x)
  have hc : δ * ‖star x‖ * ‖x‖ ≤ δ * D.p x ^ 2 := by
    have hh := mul_le_mul hs (D.norm_le_p x) (norm_nonneg x) (norm_nonneg _)
    nlinarith [mul_le_mul_of_nonneg_left hh D.delta_nonneg]
  refine ⟨?_, ?_⟩
  · change (1 - δ) * D.p x ^ 2 ≤ ‖D.mul (D.mul (star x) x)‖
    linarith
  · simpa only [D.p_star, pow_two, mul_assoc] using D.p_mul (star x) x

private theorem pairing_regular_bounds (P : H) (hP : star P = P)
    (hPP : D.p (D.mul P P - P) ≤ τ) {x : H} (hx : x ∈ D.corner P Q) :
    (1 - (δ + 260000 * (τ + M * δ))) * D.p x ^ 2 ≤
      (D.cornerPairing Q x x).re * D.p (D.cornerUnit Q) ∧
    (D.cornerPairing Q x x).re * D.p (D.cornerUnit Q) ≤
      (1 + (δ + 260000 * (τ + M * δ))) * D.p x ^ 2 := by
  have hsx : star x ∈ D.corner Q P := by
    obtain ⟨z, rfl⟩ := hx
    exact ⟨star z, (D.compression_star P Q hP I.selfadjoint I.tau_nonneg
      I.small hPP I.defect z).symm⟩
  have hs := D.corner_product_support Q P Q I.selfadjoint hP I.selfadjoint
    I.tau_nonneg I.small I.defect hPP I.defect hsx hx
  have hn := abs_norm_sub_norm_le
    (D.mul (D.compression Q Q (D.mul (star x) x))) (D.mul (D.mul (star x) x))
  simp only [← map_sub] at hn
  change |D.p (D.compression Q Q (D.mul (star x) x)) - D.p (D.mul (star x) x)| ≤
    D.p (D.compression Q Q (D.mul (star x) x) - D.mul (star x) x) at hn
  have he : |D.p (D.compression Q Q (D.mul (star x) x)) - D.p (D.mul (star x) x)| ≤
      260000 * (τ + M * δ) * D.p x ^ 2 := hn.trans
    (by simpa only [D.p_star, pow_two, mul_assoc] using hs)
  rw [← (pairing_equation I) x x, (pairing_self_real I)] at he
  have hid : D.p (((D.cornerPairing Q x x).re : ℂ) • D.cornerUnit Q) =
      (D.cornerPairing Q x x).re * D.p (D.cornerUnit Q) := by
    simp only [p, map_smul, norm_smul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg ((pairing_positive I) P hP hPP hx).1]
  rw [hid] at he
  have hb := (square_norm_bounds I) x
  constructor <;> nlinarith only [(abs_le.mp he).1, (abs_le.mp he).2, hb.1, hb.2]

/-- All scalar geometry is conditional on the original exact rank-one input.
The regular comparison retains the scale of the literal designated generator. -/
theorem rank_one_pairing_bounds :
    D.cornerUnit Q ≠ 0 ∧ 0 < D.cornerBeta Q ∧ 0 < D.cornerAlpha Q ∧
    |D.cornerBeta Q - 1| ≤ 219140 * (τ + M * δ) ∧
    ∀ (P : H), star P = P → D.p (D.mul P P - P) ≤ τ →
      ∀ (x : H), x ∈ D.corner P Q →
      D.cornerPairing Q x x • D.cornerUnit Q =
        D.compression Q Q (D.mul (star x) x) ∧
      0 ≤ (D.cornerPairing Q x x).re ∧
      ((D.cornerPairing Q x x).re = 0 ↔ x = 0) ∧
      ((1 - 260000 * (τ + M * δ) * M ^ 2) * ‖x‖ ^ 2 ≤
        D.cornerAlpha Q * (D.cornerPairing Q x x).re ∧
       D.cornerAlpha Q * (D.cornerPairing Q x x).re ≤
        (1 + 260000 * (τ + M * δ) * M ^ 2) * ‖x‖ ^ 2) ∧
      ((1 - (δ + 260000 * (τ + M * δ))) * D.p x ^ 2 ≤
        (D.cornerPairing Q x x).re * D.p (D.cornerUnit Q) ∧
       (D.cornerPairing Q x x).re * D.p (D.cornerUnit Q) ≤
        (1 + (δ + 260000 * (τ + M * δ))) * D.p x ^ 2) := by
  refine ⟨(unit_ne_zero I), (beta_pos I), (alpha_pos I), (beta_bounds I), ?_⟩
  intro P hP hPP x hx
  exact ⟨(pairing_equation I) x x, ((pairing_positive I) P hP hPP hx).1,
    ((pairing_positive I) P hP hPP hx).2, (pairing_hilbert_bounds I) P hP hPP hx,
    (pairing_regular_bounds I) P hP hPP hx⟩

/-- A separate type carries the coefficient Hilbert geometry; H keeps its original norm. -/
def CornerHilbert (_I : D.RankOneInput Q τ) (P : H) (_hP : star P = P)
    (_hPP : D.p (D.mul P P - P) ≤ τ) : Type _ :=
  D.corner P Q

instance (P : H) (hP : star P = P) (hPP : D.p (D.mul P P - P) ≤ τ) :
    AddCommGroup ((CornerHilbert I) P hP hPP) :=
  inferInstanceAs (AddCommGroup (D.corner P Q))

instance (P : H) (hP : star P = P) (hPP : D.p (D.mul P P - P) ≤ τ) :
    Module ℂ ((CornerHilbert I) P hP hPP) :=
  inferInstanceAs (Module ℂ (D.corner P Q))

instance (P : H) (hP : star P = P) (hPP : D.p (D.mul P P - P) ≤ τ) :
    FiniteDimensional ℂ ((CornerHilbert I) P hP hPP) :=
  inferInstanceAs (FiniteDimensional ℂ (D.corner P Q))

@[instance_reducible] private def hilbertCore (P : H) (hP : star P = P)
    (hPP : D.p (D.mul P P - P) ≤ τ) :
    InnerProductSpace.Core ℂ ((CornerHilbert I) P hP hPP) where
  inner x y := D.cornerPairing Q (Subtype.val (show D.corner P Q from x))
    (Subtype.val (show D.corner P Q from y))
  conj_inner_symm x y := (pairing_hermitian I) _ _
  re_inner_nonneg x := ((rank_one_pairing_bounds I).2.2.2.2 P hP hPP
    (Subtype.val (show D.corner P Q from x)) (show D.corner P Q from x).property).2.1
  add_left x y z := by
    change D.cornerPairing Q ((show D.corner P Q from x).val +
      (show D.corner P Q from y).val) (show D.corner P Q from z).val = _
    simp [cornerPairing, star_add, map_add]
  smul_left x y c := by
    change D.cornerPairing Q (c • (show D.corner P Q from x).val)
      (show D.corner P Q from y).val = _
    simp [cornerPairing, star_smul, map_smul, smul_eq_mul]
  definite x hx := by
    apply Subtype.ext
    exact ((pairing_positive I) P hP hPP x.property).2.mp (by rw [hx]; rfl)

instance (P : H) (hP : star P = P) (hPP : D.p (D.mul P P - P) ≤ τ) :
    NormedAddCommGroup ((CornerHilbert I) P hP hPP) :=
  letI := (hilbertCore I) P hP hPP
  InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)

instance (P : H) (hP : star P = P) (hPP : D.p (D.mul P P - P) ≤ τ) :
    InnerProductSpace ℂ ((CornerHilbert I) P hP hPP) :=
  letI := hilbertCore I P hP hPP
  InnerProductSpace.ofCore (hilbertCore I P hP hPP).toCore

/-- The normalized scalar column uses beta, leaving the designated t unchanged. -/
def scalarColumn : ℂ →ₗᵢ[ℂ] CornerHilbert I Q I.selfadjoint I.defect := by
  let t : CornerHilbert I Q I.selfadjoint I.defect := ⟨D.cornerUnit Q, unit_mem I⟩
  let s : ℂ := (Real.sqrt (D.cornerBeta Q) : ℂ)⁻¹
  refine (LinearMap.toSpanSingleton ℂ _ (s • t)).isometryOfInner ?_
  intro c d
  have ht : inner ℂ t t = (D.cornerBeta Q : ℂ) := by
    change D.cornerPairing Q (D.cornerUnit Q) (D.cornerUnit Q) = _
    exact pairing_self_real I _
  have hs : (Real.sqrt (D.cornerBeta Q) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (beta_pos I)).ne'
  have hsq : (Real.sqrt (D.cornerBeta Q) : ℂ) ^ 2 = (D.cornerBeta Q : ℂ) := by
    exact_mod_cast Real.sq_sqrt (le_of_lt (beta_pos I))
  simp only [LinearMap.toSpanSingleton_apply, inner_smul_left, inner_smul_right,
    ht, RCLike.inner_apply']
  dsimp [s]
  rw [map_inv₀, Complex.conj_ofReal, ← hsq]
  field_simp

private def compressedLeft (P R : H) (hP : star P = P) (hR : star R = R)
    (hPP : D.p (D.mul P P - P) ≤ τ) (hRR : D.p (D.mul R R - R) ≤ τ)
    (z : H) : CornerHilbert I R hR hRR →ₗ[ℂ] CornerHilbert I P hP hPP where
  toFun x := ⟨D.compression P Q (D.mul z (Subtype.val (show D.corner R Q from x))), ⟨_, rfl⟩⟩
  map_add' x y := by
    apply Subtype.ext
    change D.compression P Q (D.mul z ((show D.corner R Q from x).val +
      (show D.corner R Q from y).val)) = _
    simp only [map_add]
    rfl
  map_smul' c x := by
    apply Subtype.ext
    change D.compression P Q (D.mul z (c • (show D.corner R Q from x).val)) = _
    simp only [map_smul]
    rfl

/-- The two directions of the actual symmetric compressed left action.
The reverse is exactly the Hilbert adjoint in the coefficient geometry. -/
def symmetricCornerMaps (P R : H) (hP : star P = P) (hR : star R = R)
    (hPP : D.p (D.mul P P - P) ≤ τ) (hRR : D.p (D.mul R R - R) ≤ τ)
    (z : D.corner P R) :
    { a : (CornerHilbert I R hR hRR →ₗ[ℂ] CornerHilbert I P hP hPP) ×
        (CornerHilbert I P hP hPP →ₗ[ℂ] CornerHilbert I R hR hRR) //
      a.2 = a.1.adjoint ∧
      ∀ (x : CornerHilbert I R hR hRR) (y : CornerHilbert I P hP hPP),
        2 * inner ℂ y (a.1 x) =
          D.cornerPairing Q
            (D.compression R Q (D.mul (star (z : H)) (Subtype.val (show D.corner P Q from y))))
            (Subtype.val (show D.corner R Q from x)) +
          D.cornerPairing Q (Subtype.val (show D.corner P Q from y))
            (D.compression P Q (D.mul (z : H) (Subtype.val (show D.corner R Q from x)))) } := by
  let f := compressedLeft I P R hP hR hPP hRR (z : H)
  let g := compressedLeft I R P hR hP hRR hPP (star (z : H))
  refine ⟨((1 / 2 : ℂ) • (f + g.adjoint), (1 / 2 : ℂ) • (g + f.adjoint)), ?_, ?_⟩
  · simp only [map_smulₛₗ, map_add, LinearMap.adjoint_adjoint]
    norm_num [map_ofNat]
    rw [add_comm]
  · intro x y
    change 2 * inner ℂ y (((1 / 2 : ℂ) • (f + g.adjoint)) x) =
      inner ℂ (g y) x + inner ℂ y (f x)
    rw [LinearMap.smul_apply, LinearMap.add_apply, inner_smul_right, inner_add_right,
      LinearMap.adjoint_inner_right]
    ring

end D5.S3.Quantum.Algebra.Approximate.RegularCompression.Product
