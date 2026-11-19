/- GID: D5/S3/Quantum/AURICOmega/QuaternionTwoPointHomogeneity
   generality: I
   mirror-B: D5/B/S3/Quantum/AURICOmega/QuaternionTwoPointHomogeneity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Left-right unit quaternion translations act transitively on pairs with equal reading. -/

import D5.S3.Quantum.AURICOmega.QuaternionComparisonModel
import Mathlib.Tactic.Group
import Mathlib.Tactic.LinearCombination

/-! Two-point homogeneity of the quaternion comparison model.

The left-right translations `z ↦ p * z * q` by unit quaternions preserve the reading. Two pairs
of unit quaternions with the same reading are related by such a translation: the quotients
`x⁻¹ * y` and `x'⁻¹ * y'` have the same real part, and two unit quaternions with the same real
part are conjugate by a unit quaternion. -/

open scoped InnerProductSpace Quaternion

noncomputable section

namespace D5.S3.Quantum.AURICOmega.QuaternionTwoPointHomogeneity

open D5.S3.Quantum.AURICOmega.QuaternionComparisonModel

/-- The reading is invariant under the left-right translation `z ↦ p * z * q`: the products
`p * x` and `x * q` are the transfers `tri p 1 x` and `tri x 1 q`, which preserve the reading. -/
theorem kappa_mul_mul (p q x y : unitary ℍ[ℝ]) :
    quaternionModel.kappa (p * x * q) (p * y * q) = quaternionModel.kappa x y := by
  have e : ∀ a b : unitary ℍ[ℝ], quaternionModel.tri a 1 b = a * b := fun a b => by
    change a * 1⁻¹ * b = a * b
    rw [inv_one, mul_one]
  calc quaternionModel.kappa (p * x * q) (p * y * q)
      = quaternionModel.kappa (quaternionModel.tri (quaternionModel.tri p 1 x) 1 q)
          (quaternionModel.tri (quaternionModel.tri p 1 y) 1 q) := by rw [e, e, e, e]
    _ = quaternionModel.kappa (quaternionModel.tri p 1 x) (quaternionModel.tri p 1 y) :=
        quaternionModel.kappa_tri_right _ _ 1 q
    _ = quaternionModel.kappa x y := quaternionModel.kappa_tri_left p 1 x y

/-- Two quaternions with the same real part and the same norm are intertwined by a nonzero
quaternion: `w * a = a' * w`. With imaginary parts `v, v'`, the quaternion `‖v‖² - v' * v`
works unless `v' = -v`; in that case any nonzero imaginary quaternion orthogonal to `v`
works. -/
private lemma exists_ne_zero_mul_eq_mul (a a' : ℍ[ℝ]) (hre : a.re = a'.re)
    (hn : Quaternion.normSq a = Quaternion.normSq a') :
    ∃ w : ℍ[ℝ], w ≠ 0 ∧ w * a = a' * w := by
  obtain ⟨t, b₁, b₂, b₃⟩ := a
  obtain ⟨t', c₁, c₂, c₃⟩ := a'
  simp only [Quaternion.normSq_def'] at hn
  change t = t' at hre
  subst hre
  have hb : c₁ ^ 2 + c₂ ^ 2 + c₃ ^ 2 = b₁ ^ 2 + b₂ ^ 2 + b₃ ^ 2 := by linarith
  by_cases hopp : c₁ = -b₁ ∧ c₂ = -b₂ ∧ c₃ = -b₃
  · obtain ⟨rfl, rfl, rfl⟩ := hopp
    by_cases h12 : b₁ = 0 ∧ b₂ = 0
    · obtain ⟨rfl, rfl⟩ := h12
      refine ⟨⟨0, 1, 0, 0⟩, fun h => ?_, ?_⟩
      · have := congrArg (fun q : ℍ[ℝ] => q.imI) h
        simp only [QuaternionAlgebra.imI_zero, one_ne_zero] at this
      · ext <;> simp only [QuaternionAlgebra.mk_mul_mk] <;> ring
    · refine ⟨⟨0, -b₂, b₁, 0⟩, fun h => h12 ?_, ?_⟩
      · have h1 := congrArg (fun q : ℍ[ℝ] => q.imI) h
        have h2 := congrArg (fun q : ℍ[ℝ] => q.imJ) h
        simp only [QuaternionAlgebra.imI_zero, neg_eq_zero, QuaternionAlgebra.imJ_zero] at h1 h2
        exact ⟨h2, h1⟩
      · ext <;> simp only [QuaternionAlgebra.mk_mul_mk] <;> ring
  · refine ⟨⟨(b₁ ^ 2 + b₂ ^ 2 + b₃ ^ 2) + (c₁ * b₁ + c₂ * b₂ + c₃ * b₃),
      -(c₂ * b₃ - c₃ * b₂), -(c₃ * b₁ - c₁ * b₃), -(c₁ * b₂ - c₂ * b₁)⟩, fun h => hopp ?_, ?_⟩
    · have h0 := congrArg (fun q : ℍ[ℝ] => q.re) h
      simp only [QuaternionAlgebra.re_zero] at h0
      have hs : (c₁ + b₁) ^ 2 + (c₂ + b₂) ^ 2 + (c₃ + b₃) ^ 2 = 0 := by
        linear_combination hb + 2 * h0
      refine ⟨?_, ?_, ?_⟩ <;> nlinarith [sq_nonneg (c₁ + b₁), sq_nonneg (c₂ + b₂),
        sq_nonneg (c₃ + b₃)]
    · ext <;> simp only [QuaternionAlgebra.mk_mul_mk]
      · ring
      · linear_combination -b₁ * hb
      · linear_combination -b₂ * hb
      · linear_combination -b₃ * hb

/-- Two unit quaternions with the same real part are conjugate by a unit quaternion. -/
private lemma exists_unitary_mul_eq_mul (a a' : unitary ℍ[ℝ])
    (hre : (a : ℍ[ℝ]).re = (a' : ℍ[ℝ]).re) :
    ∃ c : unitary ℍ[ℝ], c * a = a' * c := by
  have hn : Quaternion.normSq (a : ℍ[ℝ]) = Quaternion.normSq (a' : ℍ[ℝ]) := by
    rw [Quaternion.normSq_eq_norm_mul_self, Quaternion.normSq_eq_norm_mul_self,
      CStarRing.norm_coe_unitary, CStarRing.norm_coe_unitary]
  obtain ⟨w, hw, hwa⟩ := exists_ne_zero_mul_eq_mul a a' hre hn
  set c : ℍ[ℝ] := ‖w‖⁻¹ • w with hc
  have hcn : ‖c‖ = 1 := by
    rw [hc, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hw)]
  have hsq : ((Quaternion.normSq c : ℝ) : ℍ[ℝ]) = 1 := by
    rw [Quaternion.normSq_eq_norm_mul_self, hcn, mul_one, Quaternion.coe_one]
  refine ⟨⟨c, Unitary.mem_iff.mpr ⟨(Quaternion.star_mul_self c).trans hsq,
    (Quaternion.self_mul_star c).trans hsq⟩⟩, Subtype.ext ?_⟩
  change c * (a : ℍ[ℝ]) = (a' : ℍ[ℝ]) * c
  rw [hc, smul_mul_assoc, mul_smul_comm, hwa]

/-- Two-point homogeneity: two pairs of unit quaternions with the same reading are related by
a left-right translation `z ↦ p * z * q` by unit quaternions. -/
theorem exists_mul_mul_eq_of_kappa_eq (x y x' y' : unitary ℍ[ℝ])
    (h : quaternionModel.kappa x y = quaternionModel.kappa x' y') :
    ∃ p q : unitary ℍ[ℝ], p * x * q = x' ∧ p * y * q = y' := by
  have hk : ∀ u v : unitary ℍ[ℝ],
      quaternionModel.kappa u v = (1 + ((u⁻¹ * v : unitary ℍ[ℝ]) : ℍ[ℝ]).re) / 2 := by
    intro u v
    rw [← kappa_mul_mul u⁻¹ 1 u v, inv_mul_cancel, mul_one, mul_one]
    change (1 + ⟪((1 : unitary ℍ[ℝ]) : ℍ[ℝ]), ((u⁻¹ * v : unitary ℍ[ℝ]) : ℍ[ℝ])⟫_ℝ) / 2 = _
    rw [Quaternion.inner_def, OneMemClass.coe_one, one_mul, Quaternion.re_star]
  have hre : ((x⁻¹ * y : unitary ℍ[ℝ]) : ℍ[ℝ]).re = ((x'⁻¹ * y' : unitary ℍ[ℝ]) : ℍ[ℝ]).re := by
    have := h
    rw [hk, hk] at this
    linarith
  obtain ⟨c, hc⟩ := exists_unitary_mul_eq_mul _ _ hre
  refine ⟨x' * c * x⁻¹, c⁻¹, by group, ?_⟩
  calc x' * c * x⁻¹ * y * c⁻¹ = x' * (c * (x⁻¹ * y)) * c⁻¹ := by group
    _ = x' * (x'⁻¹ * y' * c) * c⁻¹ := by rw [hc]
    _ = y' := by group

end D5.S3.Quantum.AURICOmega.QuaternionTwoPointHomogeneity
