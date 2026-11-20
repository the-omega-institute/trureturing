/- GID: D5/S3/Quantum/AURICOmega/QuaternionModelAutomorphism
   generality: I
   mirror-B: D5/B/S3/Quantum/AURICOmega/QuaternionModelAutomorphism
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Maps into unit quaternions preserving transfer and reading are unique up to p * x * q. -/

import D5.S3.Quantum.AURICOmega.QuaternionTwoPointHomogeneity
import D5.S3.Quantum.AURICOmega.UnitQuaternionClosedSubgroup

/-! Rigidity of the unit-quaternion comparison model.

Let `u` and `v` map a ternary comparison structure to the unit quaternions, both preserving the
transfer `x * y⁻¹ * z` and the reading `(1 + ⟪x, y⟫) / 2`; `u` need not be onto. Normalizing at a
base point `o`, the families `x ↦ (u o)⁻¹ * u x` and `x ↦ (v o)⁻¹ * v x` have the same inner
products and real parts and turn the transfer `tri x o y` into products. If every member is `1`
or `-1` the two families agree. Otherwise conjugations move a non-real member into the plane of
`1` and `i`; if every member commutes with it, the families agree; if some member does not, a
conjugation by a unit of that plane moves it into the space of `1, i, j`, and the inner products
with these two members and their product determine every member. So the families are
conjugate and `v x = p * u x * q`. The translations by `(p, q)` and `(p', q')` agree exactly when
`(p', q') = ±(p, q)`, because a unit quaternion commuting with `i` and `j` is `1` or `-1`. -/

open scoped InnerProductSpace Quaternion

noncomputable section

namespace D5.S3.Quantum.AURICOmega.QuaternionModelAutomorphism

open D5.S3.Quantum.AURICOmega.TernaryComparisonGroup
open D5.S3.Quantum.AURICOmega.QuaternionComparisonModel
open D5.S3.Quantum.AURICOmega.QuaternionTwoPointHomogeneity
open D5.S3.Quantum.AURICOmega.UnitQuaternionClosedSubgroup

/-- The reading of the model is `(1 + ⟪x, y⟫) / 2`, so preserving it is preserving the inner
product. -/
private lemma inner_eq_of_kappa_eq {x y x' y' : unitary ℍ[ℝ]}
    (h : quaternionModel.kappa x' y' = quaternionModel.kappa x y) :
    ⟪(x' : ℍ[ℝ]), (y' : ℍ[ℝ])⟫_ℝ = ⟪(x : ℍ[ℝ]), (y : ℍ[ℝ])⟫_ℝ := by
  change (1 + ⟪(x' : ℍ[ℝ]), (y' : ℍ[ℝ])⟫_ℝ) / 2 = (1 + ⟪(x : ℍ[ℝ]), (y : ℍ[ℝ])⟫_ℝ) / 2 at h
  linarith

/-- The real part is the inner product with `1`. -/
private lemma re_eq_inner_one (x : ℍ[ℝ]) : x.re = ⟪x, 1⟫_ℝ := by
  rw [inner_eq_components]
  simp

/-- Conjugation by a unit quaternion preserves the inner product. -/
private lemma inner_conj (c x y : unitary ℍ[ℝ]) :
    ⟪((c * x * c⁻¹ : unitary ℍ[ℝ]) : ℍ[ℝ]), ((c * y * c⁻¹ : unitary ℍ[ℝ]) : ℍ[ℝ])⟫_ℝ =
      ⟪(x : ℍ[ℝ]), (y : ℍ[ℝ])⟫_ℝ :=
  inner_eq_of_kappa_eq (kappa_mul_mul c c⁻¹ x y)

/-- Conjugation by a unit quaternion preserves the real part. -/
private lemma re_conj (c x : unitary ℍ[ℝ]) :
    ((c * x * c⁻¹ : unitary ℍ[ℝ]) : ℍ[ℝ]).re = (x : ℍ[ℝ]).re := by
  have h := inner_conj c x 1
  rw [mul_one, mul_inv_cancel, OneMemClass.coe_one, ← re_eq_inner_one, ← re_eq_inner_one] at h
  exact h

/-- Quaternions in the plane spanned by `1` and `i` commute. -/
private lemma mul_comm_of_mem_plane (p q : ℍ[ℝ]) (hpj : p.imJ = 0) (hpk : p.imK = 0)
    (hqj : q.imJ = 0) (hqk : q.imK = 0) : p * q = q * p := by
  ext <;> simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
    Quaternion.imK_mul, hpj, hpk, hqj, hqk] <;> ring

/-- A quaternion commuting with an element of the plane of `1` and `i` that is not real lies in
that plane. -/
private lemma mem_plane_of_mul_comm (q H : ℍ[ℝ]) (hj : H.imJ = 0) (hk : H.imK = 0)
    (hi : H.imI ≠ 0) (h : q * H = H * q) : q.imJ = 0 ∧ q.imK = 0 := by
  have h2 := congrArg (fun p : ℍ[ℝ] => p.imJ) h
  have h3 := congrArg (fun p : ℍ[ℝ] => p.imK) h
  simp only [Quaternion.imJ_mul, Quaternion.imK_mul, hj, hk] at h2 h3
  have e2 : q.imK * H.imI = 0 := by linear_combination h2 / 2
  have e3 : q.imJ * H.imI = 0 := by linear_combination -h3 / 2
  exact ⟨(mul_eq_zero.mp e3).resolve_right hi, (mul_eq_zero.mp e2).resolve_right hi⟩

/-- Two quaternions with the same real and `i` coordinates and the same inner products with `G`
and `H * G` are equal, when `H` lies in the plane of `1` and `i` with `H.imI ≠ 0` and `G` lies
in the space of `1, i, j` with `G.imJ ≠ 0`. -/
private lemma eq_of_inner_frame (P Q H G : ℍ[ℝ]) (hre : P.re = Q.re) (hI : P.imI = Q.imI)
    (hHj : H.imJ = 0) (hHk : H.imK = 0) (hHi : H.imI ≠ 0) (hGk : G.imK = 0) (hGj : G.imJ ≠ 0)
    (eG : ⟪P, G⟫_ℝ = ⟪Q, G⟫_ℝ) (eHG : ⟪P, H * G⟫_ℝ = ⟪Q, H * G⟫_ℝ) : P = Q := by
  rw [inner_eq_components, inner_eq_components, hre, hI, hGk] at eG
  rw [inner_eq_components, inner_eq_components, hre, hI] at eHG
  have hJ : P.imJ = Q.imJ := by
    have e : (P.imJ - Q.imJ) * G.imJ = 0 := by linear_combination eG
    exact sub_eq_zero.mp ((mul_eq_zero.mp e).resolve_right hGj)
  rw [hJ] at eHG
  simp only [Quaternion.imK_mul, hHj, hHk, hGk] at eHG
  have hK : P.imK = Q.imK := by
    have e : (P.imK - Q.imK) * (H.imI * G.imJ) = 0 := by linear_combination eHG
    exact sub_eq_zero.mp ((mul_eq_zero.mp e).resolve_right (mul_ne_zero hHi hGj))
  exact Quaternion.ext _ _ hre hI hJ hK

/-- A unit quaternion whose real part has square one is `1` or `-1`, so its imaginary part
vanishes. -/
private lemma im_eq_zero_of_re_sq (w : unitary ℍ[ℝ]) (h : (w : ℍ[ℝ]).re ^ 2 = 1) :
    (w : ℍ[ℝ]).imI = 0 ∧ (w : ℍ[ℝ]).imJ = 0 ∧ (w : ℍ[ℝ]).imK = 0 := by
  have n := sq_add_sq_coe_unitary w
  have hI : (w : ℍ[ℝ]).imI ^ 2 = 0 := by
    nlinarith [sq_nonneg (w : ℍ[ℝ]).imI, sq_nonneg (w : ℍ[ℝ]).imJ, sq_nonneg (w : ℍ[ℝ]).imK]
  have hJ : (w : ℍ[ℝ]).imJ ^ 2 = 0 := by
    nlinarith [sq_nonneg (w : ℍ[ℝ]).imI, sq_nonneg (w : ℍ[ℝ]).imJ, sq_nonneg (w : ℍ[ℝ]).imK]
  have hK : (w : ℍ[ℝ]).imK ^ 2 = 0 := by
    nlinarith [sq_nonneg (w : ℍ[ℝ]).imI, sq_nonneg (w : ℍ[ℝ]).imJ, sq_nonneg (w : ℍ[ℝ]).imK]
  exact ⟨pow_eq_zero_iff two_ne_zero |>.mp hI, pow_eq_zero_iff two_ne_zero |>.mp hJ,
    pow_eq_zero_iff two_ne_zero |>.mp hK⟩

/-- The unit quaternion `α + √(1 - α ^ 2) i`. -/
private lemma exists_unitary_eq_re_imI (α : ℝ) (hα : α ^ 2 ≤ 1) :
    ∃ H : unitary ℍ[ℝ], (H : ℍ[ℝ]) = ⟨α, Real.sqrt (1 - α ^ 2), 0, 0⟩ := by
  refine ⟨⟨_, mem_unitary_of_normSq ?_⟩, rfl⟩
  rw [Quaternion.normSq_def']
  change α ^ 2 + Real.sqrt (1 - α ^ 2) ^ 2 + 0 ^ 2 + 0 ^ 2 = 1
  rw [Real.sq_sqrt (by linarith)]
  ring

/-- A nonzero quaternion `r` normalizes to the unit quaternion `‖r‖⁻¹ • r`. -/
private lemma exists_unitary_smul (r : ℍ[ℝ]) (hr : r ≠ 0) :
    ∃ c : unitary ℍ[ℝ], (c : ℍ[ℝ]) = ‖r‖⁻¹ • r := by
  have hcn : ‖‖r‖⁻¹ • r‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hr)]
  exact ⟨⟨‖r‖⁻¹ • r, by
    rw [← SetLike.mem_coe, coe_unitary_eq_sphere, mem_sphere_zero_iff_norm]
    exact hcn⟩, rfl⟩

/-- A unit quaternion `w` is moved by conjugation with a unit quaternion of the plane of `1` and
`i` to `re w + imI w * i + √(imJ w ^ 2 + imK w ^ 2) j`. For `w = t + s i + b j + d k` and
`ρ = √(b ^ 2 + d ^ 2)` the quaternion `ρ + b - d i` works unless `b = -ρ` and `d = 0`, in which
case `i` works. -/
private lemma exists_plane_conj (w : unitary ℍ[ℝ]) :
    ∃ c : unitary ℍ[ℝ], (c : ℍ[ℝ]).imJ = 0 ∧ (c : ℍ[ℝ]).imK = 0 ∧
      ((c * w * c⁻¹ : unitary ℍ[ℝ]) : ℍ[ℝ]) =
        ⟨(w : ℍ[ℝ]).re, (w : ℍ[ℝ]).imI,
          Real.sqrt ((w : ℍ[ℝ]).imJ ^ 2 + (w : ℍ[ℝ]).imK ^ 2), 0⟩ := by
  set t := (w : ℍ[ℝ]).re
  set s := (w : ℍ[ℝ]).imI
  set b := (w : ℍ[ℝ]).imJ
  set d := (w : ℍ[ℝ]).imK
  set ρ := Real.sqrt (b ^ 2 + d ^ 2)
  have hρ : ρ ^ 2 = b ^ 2 + d ^ 2 := Real.sq_sqrt (by positivity)
  have hw : (w : ℍ[ℝ]) = ⟨t, s, b, d⟩ := rfl
  obtain ⟨r, hr, hrj, hrk, hrw⟩ : ∃ r : ℍ[ℝ], r ≠ 0 ∧ r.imJ = 0 ∧ r.imK = 0 ∧
      r * (w : ℍ[ℝ]) = ⟨t, s, ρ, 0⟩ * r := by
    rw [hw]
    by_cases hb : ρ + b = 0 ∧ d = 0
    · refine ⟨⟨0, 1, 0, 0⟩, fun h => ?_, rfl, rfl, ?_⟩
      · have := congrArg (fun q : ℍ[ℝ] => q.imI) h
        simp at this
      · rw [show b = -ρ by linarith [hb.1], hb.2]
        ext <;> simp only [QuaternionAlgebra.mk_mul_mk] <;> ring
    · refine ⟨⟨ρ + b, -d, 0, 0⟩, fun h => hb ?_, rfl, rfl, ?_⟩
      · have h0 := congrArg (fun q : ℍ[ℝ] => q.re) h
        have h1 := congrArg (fun q : ℍ[ℝ] => q.imI) h
        simp only [QuaternionAlgebra.re_zero, QuaternionAlgebra.imI_zero] at h0 h1
        exact ⟨h0, by linarith⟩
      · ext <;> simp only [QuaternionAlgebra.mk_mul_mk]
        · ring
        · ring
        · linear_combination -hρ
        · ring
  obtain ⟨c, hc⟩ := exists_unitary_smul r hr
  have hcw : (c : ℍ[ℝ]) * w = ⟨t, s, ρ, 0⟩ * c := by
    rw [hc, smul_mul_assoc, mul_smul_comm, hrw]
  refine ⟨c, ?_, ?_, ?_⟩
  · rw [hc, Quaternion.imJ_smul, hrj, smul_zero]
  · rw [hc, Quaternion.imK_smul, hrk, smul_zero]
  · change (c : ℍ[ℝ]) * w * ((c⁻¹ : unitary ℍ[ℝ]) : ℍ[ℝ]) = _
    rw [← Unitary.star_eq_inv, hcw, mul_assoc, Unitary.coe_mul_star_self,
      mul_one]

/-- Two families `a, b` of unit quaternions are compatible when every product `a x * a y` is a
member `a z` with `b z = b x * b y`, and `b` has the same inner products and real parts as `a`. -/
private def Compatible {ι : Type*} (a b : ι → unitary ℍ[ℝ]) : Prop :=
  (∀ x y, ∃ z, a z = a x * a y ∧ b z = b x * b y) ∧
    (∀ x y, ⟪(b x : ℍ[ℝ]), (b y : ℍ[ℝ])⟫_ℝ = ⟪(a x : ℍ[ℝ]), (a y : ℍ[ℝ])⟫_ℝ) ∧
    ∀ x, (b x : ℍ[ℝ]).re = (a x : ℍ[ℝ]).re

/-- Compatibility survives separate conjugations of the two families. -/
private lemma Compatible.conj {ι : Type*} {a b : ι → unitary ℍ[ℝ]} (h : Compatible a b)
    (e c : unitary ℍ[ℝ]) :
    Compatible (fun x => e * a x * e⁻¹) (fun x => c * b x * c⁻¹) := by
  obtain ⟨hm, hi, hr⟩ := h
  refine ⟨fun x y => ?_, fun x y => ?_, fun x => ?_⟩
  · obtain ⟨z, hza, hzb⟩ := hm x y
    exact ⟨z, by simp only [hza]; group, by simp only [hzb]; group⟩
  · simp only [inner_conj]
    exact hi x y
  · simp only [re_conj]
    exact hr x

/-- For compatible families, `a z = a z'` exactly when `b z = b z'`: inner product one between
unit vectors means equality. -/
private lemma Compatible.eq_iff {ι : Type*} {a b : ι → unitary ℍ[ℝ]} (h : Compatible a b)
    (z z' : ι) : a z = a z' ↔ b z = b z' := by
  have key : ∀ p q : unitary ℍ[ℝ], p = q ↔ ⟪(p : ℍ[ℝ]), (q : ℍ[ℝ])⟫_ℝ = 1 := fun p q =>
    Subtype.ext_iff.trans (inner_eq_one_iff_of_norm_eq_one (𝕜 := ℝ)
      (CStarRing.norm_coe_unitary p) (CStarRing.norm_coe_unitary q)).symm
  rw [key, key, h.2.1]

/-- For compatible families, commuting members of `a` correspond to commuting members of `b`. -/
private lemma Compatible.mul_comm {ι : Type*} {a b : ι → unitary ℍ[ℝ]} (h : Compatible a b)
    (x y : ι) (hc : a x * a y = a y * a x) : b x * b y = b y * b x := by
  obtain ⟨z, hza, hzb⟩ := h.1 x y
  obtain ⟨z', hza', hzb'⟩ := h.1 y x
  rw [← hzb, ← hzb', ← h.eq_iff, hza, hza', hc]

/-- If `b x₀ = a x₀` lies in the plane of `1` and `i` and is not real, then `b` and `a` have
the same `i` coordinates. -/
private lemma Compatible.imI_eq {ι : Type*} {a b : ι → unitary ℍ[ℝ]} (h : Compatible a b)
    (x₀ : ι) (h₀ : b x₀ = a x₀) (hHj : (a x₀ : ℍ[ℝ]).imJ = 0) (hHk : (a x₀ : ℍ[ℝ]).imK = 0)
    (hHi : (a x₀ : ℍ[ℝ]).imI ≠ 0) (x : ι) : (b x : ℍ[ℝ]).imI = (a x : ℍ[ℝ]).imI := by
  have e := h.2.1 x x₀
  rw [h₀, inner_eq_components, inner_eq_components, hHj, hHk, h.2.2 x] at e
  have e' : ((b x : ℍ[ℝ]).imI - (a x : ℍ[ℝ]).imI) * (a x₀ : ℍ[ℝ]).imI = 0 := by
    linear_combination e
  exact sub_eq_zero.mp ((mul_eq_zero.mp e').resolve_right hHi)

/-- Compatible families agree once they agree at a non-real member `a x₀` of the plane of `1`
and `i` and at a member `a x₁` of the space of `1, i, j` with nonzero `j` coordinate. -/
private lemma Compatible.eq_of_frame {ι : Type*} {a b : ι → unitary ℍ[ℝ]} (h : Compatible a b)
    (x₀ x₁ : ι) (h₀ : b x₀ = a x₀) (h₁ : b x₁ = a x₁) (hHj : (a x₀ : ℍ[ℝ]).imJ = 0)
    (hHk : (a x₀ : ℍ[ℝ]).imK = 0) (hHi : (a x₀ : ℍ[ℝ]).imI ≠ 0)
    (hGk : (a x₁ : ℍ[ℝ]).imK = 0) (hGj : (a x₁ : ℍ[ℝ]).imJ ≠ 0) (x : ι) : b x = a x := by
  obtain ⟨z, hza, hzb⟩ := h.1 x₀ x₁
  have hz : b z = a z := by rw [hzb, hza, h₀, h₁]
  have e : ∀ y, b y = a y → ⟪(b x : ℍ[ℝ]), (a y : ℍ[ℝ])⟫_ℝ = ⟪(a x : ℍ[ℝ]), (a y : ℍ[ℝ])⟫_ℝ :=
    fun y hy => by
      have := h.2.1 x y
      rwa [hy] at this
  have eHG := e z hz
  have hcoe : ((a z : unitary ℍ[ℝ]) : ℍ[ℝ]) = (a x₀ : ℍ[ℝ]) * (a x₁ : ℍ[ℝ]) := by
    rw [hza]
    rfl
  rw [hcoe] at eHG
  exact Subtype.ext (eq_of_inner_frame _ _ _ _ (h.2.2 x) (h.imI_eq x₀ h₀ hHj hHk hHi x) hHj hHk
    hHi hGk hGj (e x₁ h₁) eHG)

/-- Compatible families agree when they agree at a non-real member `a x₀` of the plane of `1`
and `i` and every member of `a` commutes with it. -/
private lemma Compatible.eq_of_plane {ι : Type*} {a b : ι → unitary ℍ[ℝ]} (h : Compatible a b)
    (x₀ : ι) (h₀ : b x₀ = a x₀) (hHj : (a x₀ : ℍ[ℝ]).imJ = 0) (hHk : (a x₀ : ℍ[ℝ]).imK = 0)
    (hHi : (a x₀ : ℍ[ℝ]).imI ≠ 0)
    (hpl : ∀ x, (a x : ℍ[ℝ]).imJ = 0 ∧ (a x : ℍ[ℝ]).imK = 0) (x : ι) : b x = a x := by
  have hc : a x * a x₀ = a x₀ * a x :=
    Subtype.ext (mul_comm_of_mem_plane _ _ (hpl x).1 (hpl x).2 hHj hHk)
  have hb := congrArg Subtype.val (h.mul_comm x x₀ hc)
  rw [h₀] at hb
  obtain ⟨hbj, hbk⟩ := mem_plane_of_mul_comm _ _ hHj hHk hHi hb
  exact Subtype.ext (Quaternion.ext _ _ (h.2.2 x) (h.imI_eq x₀ h₀ hHj hHk hHi x)
    (hbj.trans (hpl x).1.symm) (hbk.trans (hpl x).2.symm))

/-- If the conjugated families `e₀ * a * e₀⁻¹` and `c₀ * b * c₀⁻¹` are conjugate to each other,
so are `a` and `b`. -/
private lemma conj_of_conj {ι : Type*} {a b : ι → unitary ℍ[ℝ]} (e₀ c₀ : unitary ℍ[ℝ])
    (h : ∃ c e : unitary ℍ[ℝ], ∀ x, c * (c₀ * b x * c₀⁻¹) * c⁻¹ = e * (e₀ * a x * e₀⁻¹) * e⁻¹) :
    ∃ c e : unitary ℍ[ℝ], ∀ x, c * b x * c⁻¹ = e * a x * e⁻¹ := by
  obtain ⟨c, e, h⟩ := h
  refine ⟨c * c₀, e * e₀, fun x => ?_⟩
  calc c * c₀ * b x * (c * c₀)⁻¹ = c * (c₀ * b x * c₀⁻¹) * c⁻¹ := by group
    _ = e * (e₀ * a x * e₀⁻¹) * e⁻¹ := h x
    _ = e * e₀ * a x * (e * e₀)⁻¹ := by group

/-- Compatible families that agree at a non-real member `a x₀` of the plane of `1` and `i` are
conjugate. -/
private lemma Compatible.exists_conj_of_plane {ι : Type*} {a b : ι → unitary ℍ[ℝ]}
    (h : Compatible a b) (x₀ : ι) (h₀ : b x₀ = a x₀) (hHj : (a x₀ : ℍ[ℝ]).imJ = 0)
    (hHk : (a x₀ : ℍ[ℝ]).imK = 0) (hHi : (a x₀ : ℍ[ℝ]).imI ≠ 0) :
    ∃ c e : unitary ℍ[ℝ], ∀ x, c * b x * c⁻¹ = e * a x * e⁻¹ := by
  by_cases hpl : ∀ x, (a x : ℍ[ℝ]).imJ = 0 ∧ (a x : ℍ[ℝ]).imK = 0
  · exact ⟨1, 1, fun x => by rw [h.eq_of_plane x₀ h₀ hHj hHk hHi hpl x]⟩
  push Not at hpl
  obtain ⟨x₁, hx₁⟩ := hpl
  have hpos : 0 < (a x₁ : ℍ[ℝ]).imJ ^ 2 + (a x₁ : ℍ[ℝ]).imK ^ 2 := by
    by_cases hj : (a x₁ : ℍ[ℝ]).imJ = 0
    · have := hx₁ hj
      positivity
    · positivity
  have hnorm : (b x₁ : ℍ[ℝ]).imJ ^ 2 + (b x₁ : ℍ[ℝ]).imK ^ 2 =
      (a x₁ : ℍ[ℝ]).imJ ^ 2 + (a x₁ : ℍ[ℝ]).imK ^ 2 := by
    have na := sq_add_sq_coe_unitary (a x₁)
    have nb := sq_add_sq_coe_unitary (b x₁)
    rw [h.2.2 x₁, h.imI_eq x₀ h₀ hHj hHk hHi x₁] at nb
    linarith
  obtain ⟨d₁, hd₁j, hd₁k, hd₁⟩ := exists_plane_conj (a x₁)
  obtain ⟨d₂, hd₂j, hd₂k, hd₂⟩ := exists_plane_conj (b x₁)
  have hfix : ∀ d : unitary ℍ[ℝ], (d : ℍ[ℝ]).imJ = 0 → (d : ℍ[ℝ]).imK = 0 →
      d * a x₀ * d⁻¹ = a x₀ := fun d hdj hdk => by
    rw [mul_inv_eq_iff_eq_mul]
    exact Subtype.ext (mul_comm_of_mem_plane _ _ hdj hdk hHj hHk)
  have hG : ((d₂ * b x₁ * d₂⁻¹ : unitary ℍ[ℝ]) : ℍ[ℝ]) =
      ((d₁ * a x₁ * d₁⁻¹ : unitary ℍ[ℝ]) : ℍ[ℝ]) := by
    rw [hd₁, hd₂, hnorm, h.2.2 x₁, h.imI_eq x₀ h₀ hHj hHk hHi x₁]
  apply conj_of_conj d₁ d₂
  refine ⟨1, 1, fun x => ?_⟩
  simp only [one_mul, inv_one, mul_one]
  have h' := h.conj d₁ d₂
  refine h'.eq_of_frame x₀ x₁ ?_ (Subtype.ext hG) ?_ ?_ ?_ ?_ ?_ x
  · rw [h₀, hfix d₁ hd₁j hd₁k, hfix d₂ hd₂j hd₂k]
  · rw [hfix d₁ hd₁j hd₁k, hHj]
  · rw [hfix d₁ hd₁j hd₁k, hHk]
  · rw [hfix d₁ hd₁j hd₁k]
    exact hHi
  · rw [hd₁]
  · rw [hd₁]
    exact Real.sqrt_ne_zero'.mpr hpos

/-- Compatible families of unit quaternions are conjugate to each other. -/
private lemma Compatible.exists_conj {ι : Type*} {a b : ι → unitary ℍ[ℝ]}
    (h : Compatible a b) : ∃ c e : unitary ℍ[ℝ], ∀ x, c * b x * c⁻¹ = e * a x * e⁻¹ := by
  by_cases hreal : ∀ x, (a x : ℍ[ℝ]).re ^ 2 = 1
  · refine ⟨1, 1, fun x => ?_⟩
    obtain ⟨ha1, ha2, ha3⟩ := im_eq_zero_of_re_sq (a x) (hreal x)
    obtain ⟨hb1, hb2, hb3⟩ := im_eq_zero_of_re_sq (b x) (by rw [h.2.2 x]; exact hreal x)
    rw [Subtype.ext (Quaternion.ext _ _ (h.2.2 x) (hb1.trans ha1.symm) (hb2.trans ha2.symm)
      (hb3.trans ha3.symm))]
  push Not at hreal
  obtain ⟨x₀, hx₀⟩ := hreal
  set α := (a x₀ : ℍ[ℝ]).re
  have hα : α ^ 2 < 1 := by
    have n := sq_add_sq_coe_unitary (a x₀)
    have hle : α ^ 2 ≤ 1 := by
      nlinarith [sq_nonneg (a x₀ : ℍ[ℝ]).imI, sq_nonneg (a x₀ : ℍ[ℝ]).imJ,
        sq_nonneg (a x₀ : ℍ[ℝ]).imK]
    exact lt_of_le_of_ne hle hx₀
  obtain ⟨H, hH⟩ := exists_unitary_eq_re_imI α hα.le
  obtain ⟨e, he⟩ := exists_unitary_mul_eq_mul (a x₀) H (by rw [hH])
  obtain ⟨c, hc⟩ := exists_unitary_mul_eq_mul (b x₀) H (by rw [hH, h.2.2 x₀])
  have hea : e * a x₀ * e⁻¹ = H := by rw [mul_inv_eq_iff_eq_mul, he]
  have hcb : c * b x₀ * c⁻¹ = H := by rw [mul_inv_eq_iff_eq_mul, hc]
  apply conj_of_conj e c
  refine (h.conj e c).exists_conj_of_plane x₀ (hcb.trans hea.symm) ?_ ?_ ?_
  · rw [hea, hH]
  · rw [hea, hH]
  · rw [hea, hH]
    exact Real.sqrt_ne_zero'.mpr (by linarith)

/-- A unit quaternion commuting with `i` and `j` is `1` or `-1`. -/
private lemma eq_one_or_eq_neg_one (s : unitary ℍ[ℝ]) (hi : s * unitI = unitI * s)
    (hj : s * unitJ = unitJ * s) : s = 1 ∨ s = -1 := by
  have h := sq_add_sq_coe_unitary s
  obtain ⟨⟨a, b, c, d⟩, hs⟩ := s
  have hi' := congrArg Subtype.val hi
  have hj' := congrArg Subtype.val hj
  change (⟨a, b, c, d⟩ : ℍ[ℝ]) * ⟨0, 1, 0, 0⟩ = ⟨0, 1, 0, 0⟩ * ⟨a, b, c, d⟩ at hi'
  change (⟨a, b, c, d⟩ : ℍ[ℝ]) * ⟨0, 0, 1, 0⟩ = ⟨0, 0, 1, 0⟩ * ⟨a, b, c, d⟩ at hj'
  simp only [QuaternionAlgebra.mk_mul_mk, QuaternionAlgebra.mk.injEq] at hi' hj'
  norm_num at hi' hj'
  have hb : b = 0 := by linarith [hj'.2]
  have hc : c = 0 := by linarith [hi'.2]
  have hd : d = 0 := by linarith [hi'.1]
  subst hb hc hd
  change a ^ 2 + 0 ^ 2 + 0 ^ 2 + 0 ^ 2 = 1 at h
  rcases mul_self_eq_one_iff.mp (by linarith : a * a = 1) with ha | ha
  · left
    apply Subtype.ext
    change (⟨a, 0, 0, 0⟩ : ℍ[ℝ]) = 1
    ext <;> simp [ha]
  · right
    apply Subtype.ext
    change (⟨a, 0, 0, 0⟩ : ℍ[ℝ]) = -1
    ext <;> simp [ha]

/-- Rigidity: let `u` map a ternary comparison structure to the unit quaternions, preserving the
transfer and the reading. A map `v` to the unit quaternions preserves the transfer and the
reading if and only if `v x = p * u x * q` for some unit quaternions `p` and `q`. -/
theorem preserves_iff_exists_mul_mul {M : Type*} (C : TernaryComparison M)
    (u : M → unitary ℍ[ℝ])
    (hut : ∀ x y z, u (C.tri x y z) = quaternionModel.tri (u x) (u y) (u z))
    (huk : ∀ x y, C.kappa x y = quaternionModel.kappa (u x) (u y))
    (v : M → unitary ℍ[ℝ]) :
    ((∀ x y z, v (C.tri x y z) = quaternionModel.tri (v x) (v y) (v z)) ∧
        ∀ x y, C.kappa x y = quaternionModel.kappa (v x) (v y)) ↔
      ∃ p q : unitary ℍ[ℝ], ∀ x, v x = p * u x * q := by
  constructor
  · rintro ⟨hvt, hvk⟩
    rcases isEmpty_or_nonempty M with hM | ⟨⟨o⟩⟩
    · exact ⟨1, 1, fun x => isEmptyElim x⟩
    have hk : ∀ x y, quaternionModel.kappa ((v o)⁻¹ * v x) ((v o)⁻¹ * v y) =
        quaternionModel.kappa ((u o)⁻¹ * u x) ((u o)⁻¹ * u y) := fun x y => by
      have h1 := kappa_mul_mul (u o)⁻¹ 1 (u x) (u y)
      have h2 := kappa_mul_mul (v o)⁻¹ 1 (v x) (v y)
      simp only [mul_one] at h1 h2
      rw [h1, h2, ← hvk, huk]
    have hcomp : Compatible (fun x => (u o)⁻¹ * u x) (fun x => (v o)⁻¹ * v x) := by
      refine ⟨fun x y => ⟨C.tri x o y, ?_, ?_⟩, fun x y => inner_eq_of_kappa_eq (hk x y),
        fun x => ?_⟩
      · change (u o)⁻¹ * u (C.tri x o y) = (u o)⁻¹ * u x * ((u o)⁻¹ * u y)
        rw [hut]
        change (u o)⁻¹ * (u x * (u o)⁻¹ * u y) = (u o)⁻¹ * u x * ((u o)⁻¹ * u y)
        group
      · change (v o)⁻¹ * v (C.tri x o y) = (v o)⁻¹ * v x * ((v o)⁻¹ * v y)
        rw [hvt]
        change (v o)⁻¹ * (v x * (v o)⁻¹ * v y) = (v o)⁻¹ * v x * ((v o)⁻¹ * v y)
        group
      · have e := inner_eq_of_kappa_eq (hk x o)
        rw [inv_mul_cancel, inv_mul_cancel, OneMemClass.coe_one, ← re_eq_inner_one,
          ← re_eq_inner_one] at e
        exact e
    obtain ⟨c, e, hce⟩ := hcomp.exists_conj
    refine ⟨v o * c⁻¹ * e * (u o)⁻¹, e⁻¹ * c, fun x => ?_⟩
    have hx : c * ((v o)⁻¹ * v x) * c⁻¹ = e * ((u o)⁻¹ * u x) * e⁻¹ := hce x
    calc v x = v o * c⁻¹ * (c * ((v o)⁻¹ * v x) * c⁻¹) * c := by group
      _ = v o * c⁻¹ * (e * ((u o)⁻¹ * u x) * e⁻¹) * c := by rw [hx]
      _ = v o * c⁻¹ * e * (u o)⁻¹ * u x * (e⁻¹ * c) := by group
  · rintro ⟨p, q, hpq⟩
    refine ⟨fun x y z => ?_, fun x y => ?_⟩
    · rw [hpq, hpq, hpq, hpq, hut]
      change p * (u x * (u y)⁻¹ * u z) * q = p * u x * q * (p * u y * q)⁻¹ * (p * u z * q)
      group
    · rw [hpq, hpq, kappa_mul_mul]
      exact huk x y

/-- The translation `x ↦ p * x * q` of the unit quaternions determines `(p, q)` up to a common
sign: it agrees with `x ↦ p' * x * q'` exactly when `(p', q') = (p, q)` or
`(p', q') = (-p, -q)`. -/
theorem mul_mul_eq_mul_mul_iff (p q p' q' : unitary ℍ[ℝ]) :
    (∀ x : unitary ℍ[ℝ], p * x * q = p' * x * q') ↔
      (p' = p ∧ q' = q) ∨ (p' = -p ∧ q' = -q) := by
  constructor
  · intro h
    have h1 := h 1
    rw [mul_one, mul_one] at h1
    have hp' : p' = p * (q * q'⁻¹) := by rw [← mul_assoc, h1, mul_inv_cancel_right]
    have hcomm : ∀ x, q * q'⁻¹ * x = x * (q * q'⁻¹) := fun x => by
      have hx := h x
      rw [hp'] at hx
      calc q * q'⁻¹ * x = p⁻¹ * (p * (q * q'⁻¹) * x * q') * q'⁻¹ := by group
        _ = p⁻¹ * (p * x * q) * q'⁻¹ := by rw [hx]
        _ = x * (q * q'⁻¹) := by group
    rcases eq_one_or_eq_neg_one (q * q'⁻¹) (hcomm unitI) (hcomm unitJ) with hs | hs
    · left
      rw [hp', hs, mul_one]
      exact ⟨rfl, (mul_inv_eq_one.mp hs).symm⟩
    · right
      rw [hp', hs, mul_neg_one]
      refine ⟨rfl, ?_⟩
      rw [mul_inv_eq_iff_eq_mul] at hs
      rw [hs, neg_one_mul, neg_neg]
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) x
    · rfl
    · simp only [mul_neg, neg_mul, neg_neg]

end D5.S3.Quantum.AURICOmega.QuaternionModelAutomorphism
