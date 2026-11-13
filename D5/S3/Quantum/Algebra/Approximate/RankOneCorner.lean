/- GID: D5/S3/Quantum/Algebra/Approximate/RankOneCorner
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/Approximate/RankOneCorner
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Conditional scalar geometry of the actual one-dimensional corrected corner. -/

import D5.S3.Quantum.Algebra.Approximate.RegularCompression

noncomputable section
set_option autoImplicit false

namespace D5.S3.Quantum.Algebra.Approximate.RegularCompression.Product

open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [FiniteDimensional ℂ H] [StarAddMonoid H] [StarModule ℂ H]
  {M δ : ℝ} (D : Product H M δ)

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

private theorem radius_bounds :
    0 ≤ τ + M * δ ∧ τ ≤ τ + M * δ ∧ δ ≤ τ + M * δ ∧
      τ + M * δ ≤ 1 / 520000 := by
  have hM : 0 ≤ M := le_trans zero_le_one D.one_le_M
  have he := mul_nonneg hM D.delta_nonneg
  have hr := add_nonneg I.tau_nonneg he
  have hδ : δ ≤ M * δ := by nlinarith [D.one_le_M, D.delta_nonneg]
  have hM2 : 1 ≤ M ^ 2 := by nlinarith [D.one_le_M]
  refine ⟨hr, by linarith, by linarith, ?_⟩
  nlinarith [I.positive, mul_nonneg hr (sub_nonneg.mpr hM2)]

private theorem unit_closeness :
    D.p (D.cornerUnit Q - Q) ≤ 9737 * (τ + M * δ) := by
  obtain ⟨hr, hτ, hδ, hb⟩ := I.radius_bounds
  have hq := D.projection_norm_le_two Q I.selfadjoint
    (by linarith : τ ≤ 1 / 4) (by linarith : δ ≤ 1 / 4) I.defect
  have hc := (D.compression_closeness Q Q I.selfadjoint I.selfadjoint
    I.tau_nonneg I.small I.defect I.defect Q).1
  have hm := D.p_mul Q (D.mul Q Q - Q)
  have hm' : D.p (D.mul Q (D.mul Q Q - Q)) ≤ 4 * τ := by
    calc
      _ ≤ (1 + δ) * D.p Q * τ := hm.trans
        (mul_le_mul_of_nonneg_left I.defect (by positivity [D.delta_nonneg]))
      _ ≤ _ := by
        have ha : (1 + δ) * D.p Q ≤ 4 := by nlinarith [norm_nonneg (D.mul Q)]
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
  nlinarith [mul_le_mul_of_nonneg_left hq (by positivity : 0 ≤ 4866 * (τ + M * δ))]

private theorem compression_bound (z : H) :
    D.p (D.compression Q Q z) ≤ 5 * D.p z := by
  obtain ⟨hr, hτ, hδ, hb⟩ := I.radius_bounds
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
  obtain ⟨hr, hτ, hδ, hb⟩ := I.radius_bounds
  have hs := D.corner_left_support Q Q I.selfadjoint I.selfadjoint
    I.tau_nonneg I.small I.defect I.defect hx
  have hm := D.p_mul (D.cornerUnit Q - Q) x
  have hm' : D.p (D.mul (D.cornerUnit Q - Q) x) ≤
      (2 * 9737) * (τ + M * δ) * D.p x := by
    have ht := I.unit_closeness
    have hc : (1 + δ) * D.p (D.cornerUnit Q - Q) ≤
        2 * (9737 * (τ + M * δ)) := by
      calc
        _ ≤ 2 * D.p (D.cornerUnit Q - Q) := by
          nlinarith [norm_nonneg (D.mul (D.cornerUnit Q - Q))]
        _ ≤ _ := by linarith
    exact hm.trans (by nlinarith [mul_le_mul_of_nonneg_right hc (norm_nonneg (D.mul x))])
  have hid : D.compression Q Q (D.mul (D.cornerUnit Q) x) - x =
      D.compression Q Q (D.mul (D.cornerUnit Q - Q) x + (D.mul Q x - x)) := by
    rw [map_add, map_sub, map_sub, ContinuousLinearMap.sub_apply,
      D.compression_eq_self_of_mem Q Q I.selfadjoint I.selfadjoint
        I.tau_nonneg I.small I.defect I.defect hx]
    abel
  rw [hid]
  apply (I.compression_bound _).trans
  have ha := D.p_add (D.mul (D.cornerUnit Q - Q) x) (D.mul Q x - x)
  linarith

private theorem unit_ne_zero : D.cornerUnit Q ≠ 0 := by
  letI : Nontrivial (D.corner Q Q) := Module.nontrivial_of_finrank_eq_succ I.dimension
  obtain ⟨x, hx⟩ := exists_ne (0 : D.corner Q Q)
  have hx0 : (x : H) ≠ 0 := by simpa only [← Subtype.ext_iff] using hx
  have hn : 0 < D.p (x : H) := lt_of_lt_of_le (norm_pos_iff.mpr hx0) (D.norm_le_p _)
  intro hz
  have h := I.unit_action x.property
  simp only [hz, map_zero, ContinuousLinearMap.zero_apply, zero_sub, p, map_neg,
    norm_neg] at h
  have hb := I.radius_bounds.2.2.2
  have hlt : 219140 * (τ + M * δ) < 1 := by linarith
  nlinarith [mul_pos (sub_pos.mpr hlt) hn]

private theorem unit_mem : D.cornerUnit Q ∈ D.corner Q Q := ⟨Q, rfl⟩

private theorem unit_star : star (D.cornerUnit Q) = D.cornerUnit Q := by
  simpa only [cornerUnit, I.selfadjoint] using
    D.compression_star Q Q I.selfadjoint I.selfadjoint I.tau_nonneg I.small
      I.defect I.defect Q

/-- A coordinate on the literal designated corner line, defined on the original H. -/
def cornerCoordinate (D : Product H M δ) (Q : H) : H →ₗ[ℂ] ℂ :=
  (‖D.cornerUnit Q‖ ^ 2 : ℂ)⁻¹ • innerₛₗ ℂ (D.cornerUnit Q)

private theorem coordinate_smul (c : ℂ) :
    D.cornerCoordinate Q (c • D.cornerUnit Q) = c := by
  have ht : (‖D.cornerUnit Q‖ ^ 2 : ℂ) ≠ 0 := by
    exact_mod_cast pow_ne_zero 2 (norm_ne_zero_iff.mpr I.unit_ne_zero)
  simp only [cornerCoordinate, LinearMap.smul_apply, smul_eq_mul, innerₛₗ_apply_apply,
    inner_smul_right, inner_self_eq_norm_sq_to_K]
  field_simp

private theorem coordinate_eq {x : H} (hx : x ∈ D.corner Q Q) :
    D.cornerCoordinate Q x • D.cornerUnit Q = x := by
  have hs := eq_span_singleton_of_mem_of_finrank_eq_one I.dimension
    I.unit_mem I.unit_ne_zero
  rw [hs, Submodule.mem_span_singleton] at hx
  obtain ⟨c, rfl⟩ := hx
  rw [I.coordinate_smul]

private theorem coordinate_star {x : H} (hx : x ∈ D.corner Q Q) :
    D.cornerCoordinate Q (star x) = star (D.cornerCoordinate Q x) := by
  rw [← I.coordinate_eq hx, star_smul, I.unit_star, I.coordinate_smul]

/-- The actual compressed-product coefficient with the original generator. -/
def cornerPairing (D : Product H M δ) (Q : H) (y x : H) : ℂ :=
  D.cornerCoordinate Q (D.compression Q Q (D.mul (star y) x))

private theorem pairing_equation (y x : H) :
    D.cornerPairing Q y x • D.cornerUnit Q =
      D.compression Q Q (D.mul (star y) x) := I.coordinate_eq ⟨_, rfl⟩

private theorem pairing_hermitian (y x : H) :
    star (D.cornerPairing Q y x) = D.cornerPairing Q x y := by
  rw [cornerPairing, ← I.coordinate_star (x := D.compression Q Q (D.mul (star y) x))
    ⟨_, rfl⟩, D.compression_star Q Q I.selfadjoint I.selfadjoint I.tau_nonneg
      I.small I.defect I.defect, D.star_mul, star_star]
  rfl

end D5.S3.Quantum.Algebra.Approximate.RegularCompression.Product
