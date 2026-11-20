/- GID: D5/S3/Quantum/AURICOmega/CapCausalOrder
   generality: I
   mirror-B: D5/B/S3/Quantum/AURICOmega/CapCausalOrder
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Open caps of the unit quaternions and the causal order of the one-sheeted hyperboloid. -/

import D5.S3.Quantum.AURICOmega.QuaternionComparisonModel
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality

/-! Open caps of the unit three-sphere and the one-sheeted hyperboloid.

For a unit quaternion `n` and `a ∈ (0, π)` the cap `cap n a` consists of the unit quaternions whose
reading with `n` in the quaternion comparison model exceeds `cos (a / 2) ^ 2`, equivalently whose
inner product with `n` exceeds `cos a`. The cap is sent to the point `(-cot a, n / sin a)` of the
hyperboloid `‖v‖ ^ 2 - t ^ 2 = 1` in `ℝ × ℍ`. This is a bijection, caps determine centre and
radius, and `cap n a ⊆ cap n' a'` holds exactly when `a ≤ a'` and `cos (a' - a) ≤ ⟪n, n'⟫`, i.e.
when the angle between the centres plus `a` is at most `a'`; this is the future causal condition
for the difference of the two hyperboloid points. -/

open scoped InnerProductSpace Quaternion
open CStarRing (norm_coe_unitary)

noncomputable section

namespace D5.S3.Quantum.AURICOmega.CapCausalOrder

open D5.S3.Quantum.AURICOmega.QuaternionComparisonModel

/-- The open cap with centre `n` and angular radius `a`: the unit quaternions `x` whose reading
with `n` exceeds `cos (a / 2) ^ 2`. -/
def cap (n : unitary ℍ[ℝ]) (a : ℝ) : Set (unitary ℍ[ℝ]) :=
  {x | Real.cos (a / 2) ^ 2 < quaternionModel.kappa n x}

/-- The point `(-cot a, n / sin a)` of the hyperboloid `‖v‖ ^ 2 - t ^ 2 = 1` attached to the cap
with centre `n` and angular radius `a`. -/
def deSitterPoint (n : unitary ℍ[ℝ]) (a : ℝ) : ℝ × ℍ[ℝ] :=
  (-(Real.cos a / Real.sin a), (Real.sin a)⁻¹ • (n : ℍ[ℝ]))

/-- Membership in a cap is the inequality `cos a < ⟪n, x⟫`. -/
private lemma mem_cap {n x : unitary ℍ[ℝ]} {a : ℝ} :
    x ∈ cap n a ↔ Real.cos a < ⟪(n : ℍ[ℝ]), (x : ℍ[ℝ])⟫_ℝ := by
  change Real.cos (a / 2) ^ 2 < (1 + ⟪(n : ℍ[ℝ]), (x : ℍ[ℝ])⟫_ℝ) / 2 ↔ _
  rw [Real.cos_sq, mul_div_cancel₀ a two_ne_zero]
  constructor <;> intro h <;> linarith

/-- A quaternion of norm one is a unit quaternion. -/
private lemma mem_unitary_of_norm {q : ℍ[ℝ]} (hq : ‖q‖ = 1) : q ∈ unitary ℍ[ℝ] := by
  rw [← SetLike.mem_coe, coe_unitary_eq_sphere, mem_sphere_zero_iff_norm]
  exact hq

/-- The angle between unit quaternions is the arccosine of their inner product. -/
private lemma angle_eq (n x : unitary ℍ[ℝ]) :
    InnerProductGeometry.angle (n : ℍ[ℝ]) (x : ℍ[ℝ]) =
      Real.arccos ⟪(n : ℍ[ℝ]), (x : ℍ[ℝ])⟫_ℝ := by
  rw [InnerProductGeometry.angle, norm_coe_unitary, norm_coe_unitary, mul_one, div_one]

/-- A unit vector orthogonal to `n` along which `n'` has component `-‖n' - ⟪n, n'⟫ n‖`. -/
private lemma exists_unit_orthogonal (n n' : unitary ℍ[ℝ]) :
    ∃ u : ℍ[ℝ], ‖u‖ = 1 ∧ ⟪(n : ℍ[ℝ]), u⟫_ℝ = 0 ∧
      ⟪(n' : ℍ[ℝ]), u⟫_ℝ = -‖(n' : ℍ[ℝ]) - ⟪(n : ℍ[ℝ]), (n' : ℍ[ℝ])⟫_ℝ • (n : ℍ[ℝ])‖ := by
  set p := ⟪(n : ℍ[ℝ]), (n' : ℍ[ℝ])⟫_ℝ with hp
  set w := (n' : ℍ[ℝ]) - p • (n : ℍ[ℝ]) with hw
  have hnn : ⟪(n : ℍ[ℝ]), (n : ℍ[ℝ])⟫_ℝ = 1 := by
    rw [real_inner_self_eq_norm_sq, norm_coe_unitary, one_pow]
  have hnw : ⟪(n : ℍ[ℝ]), w⟫_ℝ = 0 := by
    rw [hw, inner_sub_right, real_inner_smul_right, hnn, mul_one, sub_self]
  have hn'w : ⟪(n' : ℍ[ℝ]), w⟫_ℝ = ‖w‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, hw, inner_sub_left, inner_smul_left, hnw]
    simp
  by_cases hw0 : w = 0
  · have hu : ⟪(n : ℍ[ℝ]), (n : ℍ[ℝ]) * (unitI : ℍ[ℝ])⟫_ℝ = 0 := by
      rw [inner_eq_components]
      simp [unitI]
      ring
    refine ⟨(n : ℍ[ℝ]) * (unitI : ℍ[ℝ]),
      by rw [norm_mul, norm_coe_unitary, norm_coe_unitary, one_mul], hu, ?_⟩
    have hn' : (n' : ℍ[ℝ]) = p • (n : ℍ[ℝ]) := sub_eq_zero.mp hw0
    rw [hw0, norm_zero, neg_zero, hn', real_inner_smul_left, hu, mul_zero]
  · have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
    refine ⟨-‖w‖⁻¹ • w, ?_, ?_, ?_⟩
    · rw [norm_smul, norm_neg, norm_inv, norm_norm, inv_mul_cancel₀ hwpos.ne']
    · rw [real_inner_smul_right, hnw, mul_zero]
    · rw [real_inner_smul_right, hn'w]
      field_simp


/-- The component of `n'` orthogonal to the unit vector `n` has squared norm `1 - ⟪n, n'⟫ ^ 2`. -/
private lemma norm_sub_smul_sq (n n' : unitary ℍ[ℝ]) :
    ‖(n' : ℍ[ℝ]) - ⟪(n : ℍ[ℝ]), (n' : ℍ[ℝ])⟫_ℝ • (n : ℍ[ℝ])‖ ^ 2 =
      1 - ⟪(n : ℍ[ℝ]), (n' : ℍ[ℝ])⟫_ℝ ^ 2 := by
  rw [norm_sub_sq_real, norm_smul, real_inner_smul_right, norm_coe_unitary, norm_coe_unitary,
    Real.norm_eq_abs, real_inner_comm (n : ℍ[ℝ])]
  rw [mul_one, sq_abs]
  ring

/-- Inclusion of caps in terms of the radii and the inner product of the centres. -/
private lemma cap_subset_iff {n n' : unitary ℍ[ℝ]} {a a' : ℝ} (ha : a ∈ Set.Ioo 0 Real.pi)
    (ha' : a' ∈ Set.Ioo 0 Real.pi) :
    cap n a ⊆ cap n' a' ↔ a ≤ a' ∧ Real.cos (a' - a) ≤ ⟪(n : ℍ[ℝ]), (n' : ℍ[ℝ])⟫_ℝ := by
  have hp1 := real_inner_le_one_of_norm_eq_one (norm_coe_unitary n) (norm_coe_unitary n')
  have hpm := neg_one_le_real_inner_of_norm_eq_one (norm_coe_unitary n) (norm_coe_unitary n')
  constructor
  · intro hsub
    obtain ⟨u, hu1, hnu, hn'u⟩ := exists_unit_orthogonal n n'
    have hsin : Real.sin (Real.arccos ⟪(n : ℍ[ℝ]), (n' : ℍ[ℝ])⟫_ℝ) =
        ‖(n' : ℍ[ℝ]) - ⟪(n : ℍ[ℝ]), (n' : ℍ[ℝ])⟫_ℝ • (n : ℍ[ℝ])‖ := by
      rw [Real.sin_arccos, ← norm_sub_smul_sq n n', Real.sqrt_sq (norm_nonneg _)]
    have hcos := Real.cos_arccos hpm hp1
    have hφ0 := Real.arccos_nonneg ⟪(n : ℍ[ℝ]), (n' : ℍ[ℝ])⟫_ℝ
    have hφπ := Real.arccos_le_pi ⟪(n : ℍ[ℝ]), (n' : ℍ[ℝ])⟫_ℝ
    have hφ : Real.arccos ⟪(n : ℍ[ℝ]), (n' : ℍ[ℝ])⟫_ℝ + a ≤ a' := by
      by_contra hlt'
      have hlt := not_le.mp hlt'
      obtain ⟨b, hb0, hba, hb1, hb2⟩ : ∃ b : ℝ, 0 ≤ b ∧ b < a ∧
          a' ≤ Real.arccos ⟪(n : ℍ[ℝ]), (n' : ℍ[ℝ])⟫_ℝ + b ∧
          Real.arccos ⟪(n : ℍ[ℝ]), (n' : ℍ[ℝ])⟫_ℝ + b ≤ Real.pi := by
        rcases le_total a' (Real.arccos ⟪(n : ℍ[ℝ]), (n' : ℍ[ℝ])⟫_ℝ) with h | h
        · exact ⟨0, le_rfl, ha.1, by linarith, by linarith⟩
        · exact ⟨a' - Real.arccos ⟪(n : ℍ[ℝ]), (n' : ℍ[ℝ])⟫_ℝ, by linarith, by linarith,
            by linarith, by linarith [ha'.2]⟩
      have hx1 : ‖Real.cos b • (n : ℍ[ℝ]) + Real.sin b • u‖ = 1 := by
        have h2 : ‖Real.cos b • (n : ℍ[ℝ]) + Real.sin b • u‖ ^ 2 = 1 := by
          rw [norm_add_sq_real, norm_smul, norm_smul, real_inner_smul_left,
            real_inner_smul_right, hnu, norm_coe_unitary, hu1, Real.norm_eq_abs, Real.norm_eq_abs]
          nlinarith [Real.sin_sq_add_cos_sq b, sq_abs (Real.cos b), sq_abs (Real.sin b)]
        exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h2
      let x : unitary ℍ[ℝ] := ⟨_, mem_unitary_of_norm hx1⟩
      have hnx : ⟪(n : ℍ[ℝ]), (x : ℍ[ℝ])⟫_ℝ = Real.cos b := by
        change ⟪(n : ℍ[ℝ]), Real.cos b • (n : ℍ[ℝ]) + Real.sin b • u⟫_ℝ = _
        rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, hnu,
          real_inner_self_eq_norm_sq, norm_coe_unitary]
        ring
      have hn'x : ⟪(n' : ℍ[ℝ]), (x : ℍ[ℝ])⟫_ℝ =
          Real.cos (Real.arccos ⟪(n : ℍ[ℝ]), (n' : ℍ[ℝ])⟫_ℝ + b) := by
        change ⟪(n' : ℍ[ℝ]), Real.cos b • (n : ℍ[ℝ]) + Real.sin b • u⟫_ℝ = _
        rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, hn'u,
          Real.cos_add, hcos, hsin, real_inner_comm (n' : ℍ[ℝ])]
        ring
      have hxa : x ∈ cap n a := mem_cap.mpr (by
        rw [hnx]; exact Real.cos_lt_cos_of_nonneg_of_le_pi hb0 ha.2.le hba)
      have hxa' := mem_cap.mp (hsub hxa)
      rw [hn'x] at hxa'
      exact absurd (Real.cos_le_cos_of_nonneg_of_le_pi ha'.1.le hb2 hb1) (not_le.mpr hxa')
    refine ⟨by linarith, ?_⟩
    calc Real.cos (a' - a) ≤ Real.cos (Real.arccos ⟪(n : ℍ[ℝ]), (n' : ℍ[ℝ])⟫_ℝ) :=
          Real.cos_le_cos_of_nonneg_of_le_pi hφ0 (by linarith [ha.1, ha'.2]) (by linarith)
      _ = _ := hcos
  · rintro ⟨haa, hc⟩ x hx
    rw [mem_cap] at hx ⊢
    have hx1 := real_inner_le_one_of_norm_eq_one (norm_coe_unitary n) (norm_coe_unitary x)
    have h1 : InnerProductGeometry.angle (n : ℍ[ℝ]) (x : ℍ[ℝ]) < a := by
      rw [angle_eq, ← Real.arccos_cos ha.1.le ha.2.le]
      exact Real.arccos_lt_arccos (Real.neg_one_le_cos a) hx hx1
    have h2 : InnerProductGeometry.angle (n' : ℍ[ℝ]) (n : ℍ[ℝ]) ≤ a' - a := by
      rw [angle_eq, real_inner_comm, ← Real.arccos_cos (sub_nonneg.mpr haa)
        (by linarith [ha.1, ha'.2])]
      exact Real.arccos_le_arccos hc
    have h3 := InnerProductGeometry.angle_le_angle_add_angle (n' : ℍ[ℝ]) (n : ℍ[ℝ]) (x : ℍ[ℝ])
    have h4 : Real.cos a' < Real.cos (InnerProductGeometry.angle (n' : ℍ[ℝ]) (x : ℍ[ℝ])) :=
      Real.cos_lt_cos_of_nonneg_of_le_pi (InnerProductGeometry.angle_nonneg _ _) ha'.2.le
        (by linarith)
    rwa [angle_eq, Real.cos_arccos (neg_one_le_real_inner_of_norm_eq_one (norm_coe_unitary n')
      (norm_coe_unitary x))
      (real_inner_le_one_of_norm_eq_one (norm_coe_unitary n') (norm_coe_unitary x))] at h4


/-- The future causal condition between the hyperboloid points of two caps. -/
private lemma causal_iff {n n' : unitary ℍ[ℝ]} {a a' : ℝ} (ha : a ∈ Set.Ioo 0 Real.pi)
    (ha' : a' ∈ Set.Ioo 0 Real.pi) :
    ((deSitterPoint n a).1 ≤ (deSitterPoint n' a').1 ∧
      ‖(deSitterPoint n' a').2 - (deSitterPoint n a).2‖ ^ 2 ≤
        ((deSitterPoint n' a').1 - (deSitterPoint n a).1) ^ 2) ↔
    a ≤ a' ∧ Real.cos (a' - a) ≤ ⟪(n : ℍ[ℝ]), (n' : ℍ[ℝ])⟫_ℝ := by
  have hs := Real.sin_pos_of_pos_of_lt_pi ha.1 ha.2
  have hs' := Real.sin_pos_of_pos_of_lt_pi ha'.1 ha'.2
  simp only [deSitterPoint]
  apply and_congr
  · rw [neg_le_neg_iff, div_le_div_iff₀ hs' hs]
    have hsub : Real.cos a' * Real.sin a - Real.cos a * Real.sin a' = Real.sin (a - a') := by
      rw [Real.sin_sub]; ring
    constructor
    · intro h
      by_contra hlt'
      have hlt := not_le.mp hlt'
      have := Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr hlt) (by linarith [ha.2, ha'.1])
      linarith
    · intro h
      have := Real.sin_nonpos_of_nonpos_of_neg_pi_le (x := a - a') (by linarith)
        (by linarith [ha.1, ha'.2])
      linarith
  · have e1 : Real.sin a * (Real.sin a)⁻¹ = 1 := mul_inv_cancel₀ hs.ne'
    have e2 : Real.sin a' * (Real.sin a')⁻¹ = 1 := mul_inv_cancel₀ hs'.ne'
    have hc2 : ∀ b : ℝ, 0 < Real.sin b →
        (Real.cos b / Real.sin b) ^ 2 = (Real.sin b)⁻¹ ^ 2 - 1 := by
      intro b hb
      rw [div_pow, Real.cos_sq', sub_div, div_self (pow_ne_zero _ hb.ne'), inv_pow, one_div]
    have hL : ‖(Real.sin a')⁻¹ • (n' : ℍ[ℝ]) - (Real.sin a)⁻¹ • (n : ℍ[ℝ])‖ ^ 2 =
        (Real.sin a')⁻¹ ^ 2 + (Real.sin a)⁻¹ ^ 2 -
          2 * ((Real.sin a')⁻¹ * (Real.sin a)⁻¹) * ⟪(n : ℍ[ℝ]), (n' : ℍ[ℝ])⟫_ℝ := by
      rw [norm_sub_sq_real, norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right,
        norm_coe_unitary, norm_coe_unitary, Real.norm_eq_abs, Real.norm_eq_abs,
        real_inner_comm (n' : ℍ[ℝ])]
      rw [mul_one, mul_one, sq_abs, sq_abs]
      ring
    have hR : (-(Real.cos a' / Real.sin a') - -(Real.cos a / Real.sin a)) ^ 2 =
        (Real.sin a')⁻¹ ^ 2 + (Real.sin a)⁻¹ ^ 2 -
          2 * ((Real.sin a')⁻¹ * (Real.sin a)⁻¹) * Real.cos (a' - a) := by
      rw [Real.cos_sub]
      calc (-(Real.cos a' / Real.sin a') - -(Real.cos a / Real.sin a)) ^ 2
          = (Real.cos a / Real.sin a) ^ 2 + (Real.cos a' / Real.sin a') ^ 2 -
              2 * (Real.cos a * Real.cos a') * ((Real.sin a)⁻¹ * (Real.sin a')⁻¹) := by ring
        _ = _ := by
          rw [hc2 a hs, hc2 a' hs']
          linear_combination (2 * Real.sin a' * (Real.sin a')⁻¹) * e1 + 2 * e2
    have hk : 0 < 2 * ((Real.sin a')⁻¹ * (Real.sin a)⁻¹) := by positivity
    rw [hL, hR]
    constructor
    · intro h
      exact le_of_mul_le_mul_left (by linarith) hk
    · intro h
      nlinarith [mul_le_mul_of_nonneg_left h hk.le]

/-- The point map is a bijection from centres and radii in `(0, π)` onto the hyperboloid. -/
private lemma bijOn_deSitterPoint :
    Set.BijOn (fun na : unitary ℍ[ℝ] × ℝ => deSitterPoint na.1 na.2)
      {na | na.2 ∈ Set.Ioo 0 Real.pi} {ξ | ‖ξ.2‖ ^ 2 - ξ.1 ^ 2 = 1} := by
  refine ⟨fun na ha => ?_, fun na ha nb hb h => ?_, fun ξ hξ => ?_⟩
  · have hs := Real.sin_pos_of_pos_of_lt_pi ha.1 ha.2
    simp only [Set.mem_ofPred_eq, deSitterPoint]
    rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hs, norm_coe_unitary, mul_one]
    field_simp
    linarith [Real.sin_sq_add_cos_sq na.2]
  · obtain ⟨n, a⟩ := na
    obtain ⟨n', a'⟩ := nb
    simp only [Set.mem_ofPred_eq] at ha hb
    have hs := Real.sin_pos_of_pos_of_lt_pi ha.1 ha.2
    have hs' := Real.sin_pos_of_pos_of_lt_pi hb.1 hb.2
    simp only [deSitterPoint, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have hn := congrArg norm h2
    rw [norm_smul, norm_smul, norm_inv, norm_inv, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos hs, abs_of_pos hs', norm_coe_unitary, norm_coe_unitary, mul_one, mul_one] at hn
    have hsin : Real.sin a = Real.sin a' := inv_injective hn
    have hcos : Real.cos a = Real.cos a' := by
      rw [hsin, neg_inj, div_left_inj' hs'.ne'] at h1
      exact h1
    have haa : a = a' := Real.injOn_cos ⟨ha.1.le, ha.2.le⟩ ⟨hb.1.le, hb.2.le⟩ hcos
    subst haa
    have hnn : (n : ℍ[ℝ]) = n' := smul_right_injective _ (inv_ne_zero hs.ne') h2
    exact Prod.ext (Subtype.ext hnn) rfl
  · obtain ⟨t, v⟩ := ξ
    simp only [Set.mem_ofPred_eq] at hξ
    have hv : 0 < ‖v‖ := by
      by_contra h0
      have : ‖v‖ = 0 := le_antisymm (not_lt.mp h0) (norm_nonneg v)
      rw [this] at hξ
      nlinarith [sq_nonneg t]
    have hc2 : 1 - (-t / ‖v‖) ^ 2 = ‖v‖⁻¹ ^ 2 := by
      field_simp
      linarith
    have hlt : (-t / ‖v‖) ^ 2 < 1 := by
      have : 0 < ‖v‖⁻¹ ^ 2 := by positivity
      linarith
    obtain ⟨hcm, hc1⟩ := abs_lt.mp ((sq_lt_one_iff_abs_lt_one _).mp hlt)
    have hunit : ‖‖v‖⁻¹ • v‖ = 1 := by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hv.ne']
    refine ⟨(⟨‖v‖⁻¹ • v, mem_unitary_of_norm hunit⟩, Real.arccos (-t / ‖v‖)),
      ⟨Real.arccos_pos.mpr hc1, Real.arccos_lt_pi.mpr hcm⟩, ?_⟩
    have hsin : Real.sin (Real.arccos (-t / ‖v‖)) = ‖v‖⁻¹ := by
      rw [Real.sin_arccos, hc2, Real.sqrt_sq (inv_nonneg.mpr (norm_nonneg _))]
    simp only [deSitterPoint]
    rw [hsin, Real.cos_arccos hcm.le hc1.le]
    refine Prod.ext ?_ ?_
    · change -(-t / ‖v‖ / ‖v‖⁻¹) = t
      field_simp
    · change (‖v‖⁻¹)⁻¹ • ‖v‖⁻¹ • v = v
      rw [inv_inv, smul_smul, mul_inv_cancel₀ hv.ne', one_smul]

/-- Caps with radius in `(0, π)` correspond bijectively to points of the one-sheeted hyperboloid
`‖v‖ ^ 2 - t ^ 2 = 1`; a cap determines its centre and radius; and one cap lies in another exactly
when the difference of the corresponding points is future-directed and causal. -/
theorem cap_causal_order :
    Set.BijOn (fun na : unitary ℍ[ℝ] × ℝ => deSitterPoint na.1 na.2)
        {na | na.2 ∈ Set.Ioo 0 Real.pi} {ξ | ‖ξ.2‖ ^ 2 - ξ.1 ^ 2 = 1} ∧
    (∀ n n' : unitary ℍ[ℝ], ∀ a a' : ℝ, a ∈ Set.Ioo 0 Real.pi → a' ∈ Set.Ioo 0 Real.pi →
      (cap n a = cap n' a' ↔ n = n' ∧ a = a')) ∧
    ∀ n n' : unitary ℍ[ℝ], ∀ a a' : ℝ, a ∈ Set.Ioo 0 Real.pi → a' ∈ Set.Ioo 0 Real.pi →
      (cap n a ⊆ cap n' a' ↔
        (deSitterPoint n a).1 ≤ (deSitterPoint n' a').1 ∧
          ‖(deSitterPoint n' a').2 - (deSitterPoint n a).2‖ ^ 2 ≤
            ((deSitterPoint n' a').1 - (deSitterPoint n a).1) ^ 2) := by
  refine ⟨bijOn_deSitterPoint, fun n n' a a' ha ha' => ⟨fun h => ?_, ?_⟩,
    fun n n' a a' ha ha' => (cap_subset_iff ha ha').trans (causal_iff ha ha').symm⟩
  · obtain ⟨h1, h2⟩ := (cap_subset_iff ha ha').mp h.subset
    obtain ⟨h3, -⟩ := (cap_subset_iff ha' ha).mp h.symm.subset
    have haa : a = a' := le_antisymm h1 h3
    subst haa
    rw [sub_self, Real.cos_zero] at h2
    have hn := norm_coe_unitary n
    have hn' := norm_coe_unitary n'
    exact ⟨Subtype.ext ((inner_eq_one_iff_of_norm_eq_one hn hn').mp
      (le_antisymm (real_inner_le_one_of_norm_eq_one hn hn') h2)), rfl⟩
  · rintro ⟨rfl, rfl⟩
    rfl

end D5.S3.Quantum.AURICOmega.CapCausalOrder
