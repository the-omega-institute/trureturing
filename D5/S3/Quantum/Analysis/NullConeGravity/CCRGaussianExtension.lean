/- GID: D5/S3/Quantum/Analysis/NullConeGravity/CCRGaussianExtension
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/NullConeGravity/CCRGaussianExtension
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Coercivity, common pure Gaussian extension and square-summable squeezing. -/

import D5.S3.Quantum.Analysis.NullConeGravity.CCRConjugation
import D5.S3.Quantum.Analysis.NullConeGravity.CCRAbsoluteValueHS
import D5.S3.Quantum.Analysis.NullConeGravity.QuarterPowerSqrtHilbertSchmidt
import D5.S3.Quantum.Analysis.CompactEigenbasis
import D5.S3.Quantum.Analysis.TraceClass.HilbertSchmidt
import D5.S3.Analysis.PositiveSkew
import D5.S3.Analysis.HilbertSqueeze

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped Ring InnerProductSpace
open ContinuousLinearMap HilbertSchmidt NullConeGravity
open Omega.Analysis.HilbertSqueeze

namespace D5.S3.Quantum.Analysis.NullConeGravity.CCRGaussianExtension

open CCRAbsoluteValueHS QuarterPowerSqrtHilbertSchmidt

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local notation "Op" => H →L[ℂ] H

private abbrev IsReal (Γ : RealConjugation H) (T : Op) : Prop :=
  ∀ x, Γ.toLinearIsometryEquiv (T x) = T (Γ.toLinearIsometryEquiv x)

private def conjugateRingHom (Γ : RealConjugation H) : Op →+* Op where
  toFun := conjOp Γ
  map_one' := by ext x; simp [Γ.involutive x]
  map_zero' := by ext x; simp
  map_mul' := conjOp_comp Γ
  map_add' S T := by ext x; simp

omit [CompleteSpace H] in
private theorem conjugate_smul (Γ : RealConjugation H) (a : ℂ) (T : Op) :
    conjugateRingHom Γ (a • T) = star a • conjugateRingHom Γ T := by
  ext x
  change Γ.toLinearIsometryEquiv (a • T (Γ.toLinearIsometryEquiv x)) =
    star a • Γ.toLinearIsometryEquiv (T (Γ.toLinearIsometryEquiv x))
  exact Γ.map_complex_smul _ _

omit [CompleteSpace H] in
private theorem real_iff_conjugate (Γ : RealConjugation H) (T : Op) :
    IsReal Γ T ↔ conjugateRingHom Γ T = T := by
  constructor
  · intro h
    ext x
    change Γ.toLinearIsometryEquiv (T (Γ.toLinearIsometryEquiv x)) = T x
    rw [h, Γ.involutive]
  · intro h x
    have hx := DFunLike.congr_fun h (Γ.toLinearIsometryEquiv x)
    simpa [conjugateRingHom, Γ.involutive x] using hx

private theorem conjugate_sqrt (Γ : RealConjugation H) {T : Op} (hT : 0 ≤ T) :
    conjugateRingHom Γ (CFC.sqrt T) = CFC.sqrt (conjugateRingHom Γ T) := by
  symm
  apply CFC.sqrt_unique _ (conjOp_nonneg Γ _ (CFC.sqrt_nonneg T))
  change conjugateRingHom Γ (CFC.sqrt T) * conjugateRingHom Γ (CFC.sqrt T) = _
  rw [← map_mul, CFC.sqrt_mul_sqrt_self T hT]

private theorem rootReal (Γ : RealConjugation H) {T : Op} (hT : 0 ≤ T) (hr : IsReal Γ T) :
    IsReal Γ (CFC.sqrt T) := by
  rw [real_iff_conjugate, conjugate_sqrt Γ hT, (real_iff_conjugate Γ T).mp hr]

omit [CompleteSpace H] in
private theorem inverseReal (Γ : RealConjugation H) {T : Op} (hT : IsUnit T) (hr : IsReal Γ T) :
    IsReal Γ T⁻¹ʳ := by
  have h := (real_iff_conjugate Γ T).mp hr
  apply (real_iff_conjugate Γ _).mpr
  refine left_inv_eq_right_inv (?_ : conjugateRingHom Γ T⁻¹ʳ * T = 1)
    (Ring.mul_inverse_cancel T hT)
  calc
    _ = conjugateRingHom Γ (T⁻¹ʳ * T) := by rw [map_mul, h]
    _ = 1 := by rw [Ring.inverse_mul_cancel T hT, map_one]

private theorem conjugate_hs (Γ : RealConjugation H) {T : Op} (hT : IsHilbertSchmidt T) :
    IsHilbertSchmidt (conjugateRingHom Γ T) := by
  classical
  obtain ⟨w, b, hb⟩ := hT
  let v (i : w) := Γ.toLinearIsometryEquiv (b i)
  have ho : Orthonormal ℂ v := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [show ⟪v i, v j⟫_ℂ = star ⟪b i, b j⟫_ℂ from conj_inner Γ _ _,
      orthonormal_iff_ite.mp b.orthonormal]
    split_ifs <;> simp
  have hd : (Submodule.span ℂ (Set.range v))ᗮ = ⊥ := by
    apply le_antisymm _ bot_le
    intro x hx
    have hz (i : w) : ⟪b i, Γ.toLinearIsometryEquiv x⟫_ℂ = 0 := by
      apply star_injective
      rw [← conj_inner Γ, star_zero, Γ.involutive]
      exact (Submodule.mem_orthogonal _ _).mp hx _ (Submodule.subset_span ⟨i, rfl⟩)
    have he : Γ.toLinearIsometryEquiv x = 0 := by
      apply b.repr.injective
      ext i
      simpa [HilbertBasis.repr_apply_apply] using hz i
    simpa using Γ.toLinearIsometryEquiv.injective (he.trans (map_zero _).symm)
  let c := HilbertBasis.mkOfOrthogonalEqBot ho hd
  refine ⟨w, c, ?_⟩
  simpa [c, v, conjugateRingHom, show ∀ x, Γ.toLinearIsometryEquiv
    (Γ.toLinearIsometryEquiv x) = x from Γ.involutive] using hb

private theorem adjoint_of_nonneg {T : Op} (hT : 0 ≤ T) : T.adjoint = T :=
  IsSelfAdjoint.of_nonneg hT

private theorem inverse_root_conj {Q : Op} (hQ : 0 ≤ Q) (hU : IsUnit (CFC.sqrt Q)) :
    (CFC.sqrt Q)⁻¹ʳ * Q * (CFC.sqrt Q)⁻¹ʳ = 1 := by
  nth_rw 2 [← CFC.sqrt_mul_sqrt_self Q hQ]
  rw [← mul_assoc, Ring.inverse_mul_cancel _ hU, one_mul, Ring.mul_inverse_cancel _ hU]

private theorem root_sub_one_hs {Q : Op} (hQ : 0 ≤ Q) (h : IsHilbertSchmidt (Q - 1)) :
    IsHilbertSchmidt (CFC.sqrt Q - 1) := by
  let A := CFC.sqrt Q
  have ha : IsStrictlyPositive (A + 1) := IsStrictlyPositive.nonneg_add (CFC.sqrt_nonneg Q) isStrictlyPositive_one
  have he : (A - 1) * (A + 1) = Q - 1 := by
    rw [show Q = A * A from (CFC.sqrt_mul_sqrt_self Q hQ).symm]
    noncomm_ring
  have hh := isHilbertSchmidt_mul_right (U := (A + 1)⁻¹ʳ) h
  rwa [← he, Ring.mul_inverse_cancel_right _ _ ha.isUnit] at hh

private theorem inverse_sub_one_hs {T : Op} (hU : IsUnit T) (h : IsHilbertSchmidt (T - 1)) :
    IsHilbertSchmidt (T⁻¹ʳ - 1) := by
  have hh := isHilbertSchmidt_mul_left (U := T⁻¹ʳ) h
  simpa [mul_sub, Ring.inverse_mul_cancel _ hU] using
    (isHilbertSchmidt_smul (-1 : ℂ) hh : IsHilbertSchmidt ((-1 : ℂ) • (T⁻¹ʳ * (T - 1))))

/-- A Hilbert–Schmidt difference of covariance roots yields a Hilbert–Schmidt covariance
perturbation, a positive lower bound, and Hilbert–Schmidt changes of the root and its inverse. -/
theorem covariance_coercive {Q R : Op} (hQ : 0 ≤ Q) (hker : Q.ker = ⊥)
    (h₁ : 0 ≤ 1 - Complex.I • R) (h₂ : 0 ≤ Q - Complex.I • R)
    (h : IsHilbertSchmidt (CFC.sqrt (Q - Complex.I • R) - CFC.sqrt (1 - Complex.I • R))) :
    IsHilbertSchmidt (Q - 1) ∧ (∃ d : ℝ, 0 < d ∧ d • (1 : Op) ≤ Q) ∧
      IsUnit Q ∧ IsUnit (CFC.sqrt Q) ∧ IsHilbertSchmidt (CFC.sqrt Q - 1) ∧
      IsHilbertSchmidt ((CFC.sqrt Q)⁻¹ʳ - 1) := by
  let A := CFC.sqrt (Q - Complex.I • R)
  let B := CFC.sqrt (1 - Complex.I • R)
  have hfactor : Q - 1 = A * (A - B) + (A - B) * B := by
    calc
      Q - 1 = (Q - Complex.I • R) - (1 - Complex.I • R) := by abel
      _ = A * A - B * B := by rw [CFC.sqrt_mul_sqrt_self _ h₂, CFC.sqrt_mul_sqrt_self _ h₁]
      _ = _ := by noncomm_ring
  have hh : IsHilbertSchmidt (Q - 1) := hfactor ▸
    isHilbertSchmidt_add (isHilbertSchmidt_mul_left h) (isHilbertSchmidt_mul_right h)
  have hT := isCompactOperator_of_isHilbertSchmidt hh
  have he : ¬ Module.End.HasEigenvalue (Q - 1).toLinearMap (-1) := by
    intro e
    obtain ⟨x, hx, hne⟩ := (Submodule.ne_bot_iff _).mp (Module.End.hasEigenvalue_iff.mp e)
    have hx' : (Q - 1) x = (-1 : ℂ) • x := Module.End.mem_eigenspace_iff.mp hx
    have hz : x ∈ Q.ker := by
      change Q x = 0
      simpa using hx'
    rw [hker, Submodule.mem_bot] at hz
    exact hne hz
  have hU : IsUnit Q := by
    have hr := (hT.hasEigenvalue_or_mem_resolventSet (show (-1 : ℂ) ≠ 0 by norm_num)).resolve_left he
    rw [spectrum.mem_resolventSet_iff, map_neg, map_one] at hr
    have heq : -(1 : Op) - (Q - 1) = -Q := by abel
    rw [heq, IsUnit.neg_iff] at hr
    exact hr
  have hbound := Omega.positive_lower_bound hQ hU
  have hA := (CFC.isUnit_sqrt_iff Q hQ).2 hU
  have hHS := root_sub_one_hs hQ hh
  exact ⟨hh, hbound, hU, hA, hHS, inverse_sub_one_hs hA hHS⟩

/-- The skew operator in the Hilbert norm determined by the covariance. -/
def normalizedSkew (Q R : Op) : Op := (CFC.sqrt Q)⁻¹ʳ * R * (CFC.sqrt Q)⁻¹ʳ

/-- The positive root of one plus the square of the normalized skew operator. -/
def defectRoot (Q R : Op) : Op := CFC.sqrt (1 + normalizedSkew Q R ^ 2)

omit [CompleteSpace H] in
private theorem conjugate_signed (Γ : RealConjugation H) {S : Op} (hS : IsReal Γ S) :
    conjugateRingHom Γ (1 - Complex.I • S) = 1 + Complex.I • S := by
  rw [map_sub, map_one, conjugate_smul, (real_iff_conjugate Γ S).mp hS]
  simp [sub_eq_add_neg]

private theorem normalized_minus_nonneg {Q R : Op} (hQ : 0 ≤ Q)
    (hU : IsUnit (CFC.sqrt Q)) (h : 0 ≤ Q - Complex.I • R) :
    0 ≤ 1 - Complex.I • normalizedSkew Q R := by
  let B := (CFC.sqrt Q)⁻¹ʳ
  have hb : 0 ≤ B := (CFC.ringInverse_nonneg_iff_nonneg_of_isUnit hU).2 (CFC.sqrt_nonneg _)
  have he : B * (Q - Complex.I • R) * B = 1 - Complex.I • normalizedSkew Q R := by
    simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, normalizedSkew]
    rw [inverse_root_conj hQ hU]
  rw [← he]
  exact conjugate_nonneg_of_nonneg h hb

private theorem normalized_real (Γ : RealConjugation H) {Q R : Op}
    (hQ : 0 ≤ Q) (hU : IsUnit (CFC.sqrt Q)) (hq : IsReal Γ Q) (hr : IsReal Γ R) :
    IsReal Γ (normalizedSkew Q R) := by
  rw [real_iff_conjugate]
  simp only [normalizedSkew, map_mul, (real_iff_conjugate Γ _).mp
    (inverseReal Γ hU (rootReal Γ hQ hq)), (real_iff_conjugate Γ _).mp hr]

private theorem normalized_defect (Γ : RealConjugation H) {Q R : Op}
    (hQ : 0 ≤ Q) (hU : IsUnit (CFC.sqrt Q)) (hq : IsReal Γ Q)
    (hR : R.adjoint = -R) (hr : IsReal Γ R) (h : 0 ≤ Q - Complex.I • R) :
    ‖normalizedSkew Q R‖ ≤ 1 ∧ 0 ≤ 1 + normalizedSkew Q R ^ 2 ∧
      defectRoot Q R ≤ 1 ∧
      defectRoot Q R = CFC.sqrt (1 - Complex.I • normalizedSkew Q R) *
        CFC.sqrt (1 + Complex.I • normalizedSkew Q R) := by
  let S := normalizedSkew Q R
  have hb : 0 ≤ (CFC.sqrt Q)⁻¹ʳ :=
    (CFC.ringInverse_nonneg_iff_nonneg_of_isUnit hU).2 (CFC.sqrt_nonneg _)
  have hs : star S = -S := by
    unfold S normalizedSkew
    simp only [star_mul, (IsSelfAdjoint.of_nonneg hb).star_eq, ← star_eq_adjoint] at hR ⊢
    rw [hR]
    simp [mul_assoc]
  have hm : 0 ≤ 1 - Complex.I • S := normalized_minus_nonneg hQ hU h
  have hp : 0 ≤ 1 + Complex.I • S := by
    rw [← conjugate_signed Γ (normalized_real Γ hQ hU hq hr)]
    exact conjOp_nonneg Γ _ hm
  exact Omega.skew_defect hs hm hp

/-- The normalized skew operator is a contraction and its real defect has the two-root
factorization. -/
theorem normalized_properties (Γ : RealConjugation H) {Q R : Op}
    (hQ : 0 ≤ Q) (hU : IsUnit (CFC.sqrt Q)) (hq : IsReal Γ Q)
    (hR : R.adjoint = -R) (hr : IsReal Γ R) (h : 0 ≤ Q - Complex.I • R) :
    ‖normalizedSkew Q R‖ ≤ 1 ∧ IsReal Γ (defectRoot Q R) ∧
      0 ≤ defectRoot Q R ∧ defectRoot Q R ≤ 1 ∧
      defectRoot Q R = CFC.sqrt (1 - Complex.I • normalizedSkew Q R) *
        CFC.sqrt (1 + Complex.I • normalizedSkew Q R) := by
  obtain ⟨hn, hz, hb, hf⟩ := normalized_defect Γ hQ hU hq hR hr h
  have hreal : IsReal Γ (1 + normalizedSkew Q R ^ 2) := by
    rw [real_iff_conjugate, map_add, map_one, map_pow,
      (real_iff_conjugate Γ _).mp (normalized_real Γ hQ hU hq hr)]
  exact ⟨hn, rootReal Γ hz hreal, CFC.sqrt_nonneg _, hb, hf⟩

private theorem absolute_normalized {Q R : Op} (hQ : 0 ≤ Q) (hU : IsUnit (CFC.sqrt Q))
    (h : 0 ≤ Q - Complex.I • R) :
    opAbs (CFC.sqrt (Q - Complex.I • R) * (CFC.sqrt Q)⁻¹ʳ) =
      CFC.sqrt (1 - Complex.I • normalizedSkew Q R) := by
  let A := CFC.sqrt (Q - Complex.I • R)
  let B := (CFC.sqrt Q)⁻¹ʳ
  have hb : 0 ≤ B := (CFC.ringInverse_nonneg_iff_nonneg_of_isUnit hU).2 (CFC.sqrt_nonneg _)
  unfold opAbs
  congr 1
  change star (A * B) * (A * B) = _
  have ha : IsSelfAdjoint A := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg _)
  simp only [star_mul, (IsSelfAdjoint.of_nonneg hb).star_eq, ha.star_eq]
  rw [← mul_assoc, mul_assoc B A A, show A * A = Q - Complex.I • R from CFC.sqrt_mul_sqrt_self _ h]
  simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, normalizedSkew]
  rw [inverse_root_conj hQ hU]

/-- The difference of the real defects is Hilbert–Schmidt. -/
theorem defectRoot_sub_hs (Γ : RealConjugation H) {Q R : Op} (hQ : 0 ≤ Q)
    (hU : IsUnit (CFC.sqrt Q)) (hq : IsReal Γ Q) (hR : R.adjoint = -R) (hr : IsReal Γ R)
    (h₁ : 0 ≤ 1 - Complex.I • R) (h₂ : 0 ≤ Q - Complex.I • R)
    (hA : IsHilbertSchmidt ((CFC.sqrt Q)⁻¹ʳ - 1))
    (h : IsHilbertSchmidt (CFC.sqrt (Q - Complex.I • R) - CFC.sqrt (1 - Complex.I • R))) :
    IsHilbertSchmidt (defectRoot Q R - defectRoot 1 R) := by
  let Y₂ := CFC.sqrt (Q - Complex.I • R) * (CFC.sqrt Q)⁻¹ʳ
  let Y₁ := CFC.sqrt (1 - Complex.I • R)
  have he : Y₂ - Y₁ = (CFC.sqrt (Q - Complex.I • R) - Y₁) +
      CFC.sqrt (Q - Complex.I • R) * ((CFC.sqrt Q)⁻¹ʳ - 1) := by
    unfold Y₂
    noncomm_ring
  have hY : IsHilbertSchmidt (Y₂ - Y₁) := he ▸
    isHilbertSchmidt_add h (isHilbertSchmidt_mul_left hA)
  let X₂ := 1 - Complex.I • normalizedSkew Q R
  let X₁ := 1 - Complex.I • normalizedSkew 1 R
  have hu₁ : IsUnit (CFC.sqrt (1 : Op)) := by simp
  have hY₁ : opAbs Y₁ = CFC.sqrt X₁ := by
    simpa [Y₁, X₁] using absolute_normalized (Q := (1 : Op)) zero_le_one hu₁ h₁
  have hm : IsHilbertSchmidt (CFC.sqrt X₂ - CFC.sqrt X₁) := by
    obtain ⟨hh, _⟩ := opAbs_sub hY
    simpa [Y₂, absolute_normalized hQ hU h₂, hY₁, X₂] using hh
  have hpos₂ : 0 ≤ X₂ := normalized_minus_nonneg hQ hU h₂
  have hpos₁ : 0 ≤ X₁ := normalized_minus_nonneg zero_le_one hu₁ h₁
  have hone : IsReal Γ (1 : Op) := by intro x; simp
  have hs₂ := normalized_real Γ hQ hU hq hr
  have hs₁ : IsReal Γ (normalizedSkew 1 R) := by simpa [normalizedSkew] using hr
  have hp := conjugate_hs Γ hm
  rw [map_sub, conjugate_sqrt Γ hpos₂, conjugate_sqrt Γ hpos₁,
    show conjugateRingHom Γ X₂ = _ from conjugate_signed Γ hs₂,
    show conjugateRingHom Γ X₁ = _ from conjugate_signed Γ hs₁] at hp
  rw [(normalized_properties Γ hQ hU hq hR hr h₂).2.2.2.2,
    (normalized_properties Γ zero_le_one hu₁ hone hR hr h₁).2.2.2.2]
  let A := CFC.sqrt (1 + Complex.I • normalizedSkew Q R)
  let B := CFC.sqrt (1 + Complex.I • normalizedSkew 1 R)
  change IsHilbertSchmidt (CFC.sqrt X₂ * A - CFC.sqrt X₁ * B)
  rw [show CFC.sqrt X₂ * A - CFC.sqrt X₁ * B =
    CFC.sqrt X₂ * (A - B) + (CFC.sqrt X₂ - CFC.sqrt X₁) * B by noncomm_ring]
  exact isHilbertSchmidt_add (isHilbertSchmidt_mul_left hp) (isHilbertSchmidt_mul_right hm)

/-- Doubled covariance with the common canonical alternating form. -/
def doubleCovariance (Q R : Op) : Op :=
  CFC.sqrt Q * (1 + defectRoot Q R) * CFC.sqrt Q

/-- In the reference norm the outer covariance roots are identities. -/
theorem doubleCovariance_one (R : Op) : doubleCovariance 1 R = 1 + CFC.sqrt (1 + R ^ 2) := by
  simp [doubleCovariance, defectRoot, normalizedSkew]

/-- The doubled covariance is real, is bounded between the covariance and twice the covariance,
and recovers the original covariance on the common embedded subspace. -/
theorem doubleCovariance_properties (Γ : RealConjugation H) {Q R : Op}
    (hQ : 0 ≤ Q) (hU : IsUnit (CFC.sqrt Q)) (hq : IsReal Γ Q)
    (hR : R.adjoint = -R) (hr : IsReal Γ R) (h : 0 ≤ Q - Complex.I • R) :
    IsReal Γ (doubleCovariance Q R) ∧ Q ≤ doubleCovariance Q R ∧
      doubleCovariance Q R ≤ (2 : ℝ) • Q ∧ IsUnit (doubleCovariance Q R) ∧
      (1 / 2 : ℝ) • (doubleCovariance Q R - R * (doubleCovariance Q R)⁻¹ʳ * R) = Q := by
  let A := CFC.sqrt Q
  let P := defectRoot Q R
  let C : Op := 1 + P
  let D := doubleCovariance Q R
  obtain ⟨_, hPr, hP, hP₁, _⟩ := normalized_properties Γ hQ hU hq hR hr h
  have hA : 0 ≤ A := CFC.sqrt_nonneg _
  have hA₂ : A * A = Q := CFC.sqrt_mul_sqrt_self Q hQ
  have hCu : IsUnit C := (isStrictlyPositive_one.add_nonneg hP).isUnit
  have hDu : IsUnit D := (hU.mul hCu).mul hU
  have hDr : IsReal Γ D := by
    apply (real_iff_conjugate Γ _).mpr
    simp only [D, doubleCovariance, map_mul, map_add, map_one,
      (real_iff_conjugate Γ _).mp (rootReal Γ hQ hq), (real_iff_conjugate Γ _).mp hPr]
  have hD₀ : Q ≤ D := by
    have h₀ : (1 : Op) ≤ C := le_add_of_nonneg_right hP
    simpa [A, C, D, doubleCovariance, hA₂] using conjugate_le_conjugate_of_nonneg h₀ hA
  have hD₂ : D ≤ (2 : ℝ) • Q := by
    have h₂ : C ≤ (2 : ℝ) • (1 : Op) := by
      rw [two_smul]
      exact add_le_add_right hP₁ 1
    simpa [D, doubleCovariance, C, mul_smul_comm, smul_mul_assoc, hA₂] using
      conjugate_le_conjugate_of_nonneg h₂ hA
  have hz := (normalized_defect Γ hQ hU hq hR hr h).2.1
  exact ⟨hDr, hD₀, hD₂, hDu, (Omega.skew_defect_congruence hU hz).trans hA₂⟩

/-- Doubling preserves the Hilbert–Schmidt comparison of the two covariances. -/
theorem doubleCovariance_sub_hs {Q R : Op} (hQ : IsHilbertSchmidt (CFC.sqrt Q - 1))
    (hP : IsHilbertSchmidt (defectRoot Q R - defectRoot 1 R)) :
    IsHilbertSchmidt (doubleCovariance Q R - doubleCovariance 1 R) := by
  let A := CFC.sqrt Q
  let C : Op := 1 + defectRoot 1 R
  have hP' := (adjointCongr_hsSq_le A hP).choose
  have he : doubleCovariance Q R - doubleCovariance 1 R =
      (A - 1) * C * A + C * (A - 1) + adjointCongr A (defectRoot Q R - defectRoot 1 R) := by
    have ha : A.adjoint = A := adjoint_of_nonneg (CFC.sqrt_nonneg Q)
    simp only [doubleCovariance, CFC.sqrt_one, one_mul, mul_one, adjointCongr, ha,
      ← ContinuousLinearMap.mul_def]
    unfold C
    noncomm_ring
  exact he ▸ isHilbertSchmidt_add
    (isHilbertSchmidt_add (isHilbertSchmidt_mul_right (isHilbertSchmidt_mul_right hQ))
      (isHilbertSchmidt_mul_left hQ)) hP'

section PureExtension

variable (Γ : RealConjugation H)
local notation "Hℝ" => realSubspace Γ
local notation "J" => Γ.toLinearIsometryEquiv

omit [CompleteSpace H] in
private theorem squeeze_mul_real {A B : H →L[ℂ] H}
    (hA : ∀ x, J (A x) = A (J x)) (hB : ∀ x, J (B x) = B (J x)) (x : H) :
    J ((A * B) x) = (A * B) (J x) := by
  simp [mul_apply_eq_comp, hA, hB]

private def realCoordinates : (Hℝ × Hℝ) ≃ₗ[ℝ] H where
  toFun x := (x.1 : H) - Complex.I • (x.2 : H)
  invFun z := (⟨realPart Γ z, realPart_mem Γ z⟩, -⟨imagPart Γ z, imagPart_mem Γ z⟩)
  left_inv x := by
    have h := real_imag_unique Γ ((x.1 : H) - Complex.I • (x.2 : H)) x.1 (-x.2)
      (by simp [sub_eq_add_neg])
    exact Prod.ext (Subtype.ext h.1) (neg_eq_iff_eq_neg.mpr (Subtype.ext h.2))
  right_inv z := by simpa [sub_eq_add_neg] using (real_imag_decomposition Γ z).symm
  map_add' x y := by simp [smul_add, sub_eq_add_neg]; abel
  map_smul' r x := by simp [smul_sub, smul_comm r Complex.I]

/-- The common real embedding uses the same skew operator for both extensions. -/
def phaseEmbedding (R : H →L[ℂ] H) (hR : ∀ x, J (R x) = R (J x)) :
    Hℝ →ₗ[ℝ] Hℝ × Hℝ :=
  (Real.sqrt 2)⁻¹ • (LinearMap.id.prod (restrictReal Γ R hR).toLinearMap)

private def realUnitEquiv (S : H →L[ℂ] H) (hS : IsUnit S) (hr : ∀ x, J (S x) = S (J x)) :
    Hℝ ≃ₗ[ℝ] Hℝ :=
  { (restrictReal Γ S hr).toLinearMap with
    invFun := restrictReal Γ S⁻¹ʳ (inverseReal Γ hS hr)
    left_inv := fun x => Subtype.ext (DFunLike.congr_fun (Ring.inverse_mul_cancel S hS) (x : H))
    right_inv := fun x => Subtype.ext (DFunLike.congr_fun (Ring.mul_inverse_cancel S hS) (x : H)) }

/-- A strictly positive real covariance defines real-linear one-particle coordinates. -/
def pureExtension (D : H →L[ℂ] H) (hD : 0 ≤ D) (hu : IsUnit D)
    (hr : ∀ x, J (D x) = D (J x)) : (Hℝ × Hℝ) ≃ₗ[ℝ] H :=
  let e := realUnitEquiv Γ (CFC.sqrt D) ((CFC.isUnit_sqrt_iff D hD).mpr hu)
    (rootReal Γ hD hr)
  (LinearEquiv.prodCongr e e.symm).trans (realCoordinates Γ)

private theorem pureExtension_apply (D : H →L[ℂ] H) (hD : 0 ≤ D) (hu : IsUnit D)
    (hr : ∀ x, J (D x) = D (J x)) (x : Hℝ × Hℝ) :
    pureExtension Γ D hD hu hr x =
      CFC.sqrt D (x.1 : H) - Complex.I • (CFC.sqrt D)⁻¹ʳ (x.2 : H) := rfl

private theorem inner_squeeze {A B : H →L[ℂ] H} (x y : H) :
    ⟪A x, B y⟫_ℂ = ⟪x, (A.adjoint * B) y⟫_ℂ :=
  (adjoint_inner_right A x (B y)).symm

/-- The inner product of embedded real data recovers the original complex covariance. -/
theorem pureExtension_inner (D Q R : H →L[ℂ] H) (hD : 0 ≤ D) (hu : IsUnit D)
    (hd : ∀ x, J (D x) = D (J x)) (hr : ∀ x, J (R x) = R (J x))
    (hs : R.adjoint = -R) (hcov : (1 / 2 : ℝ) • (D - R * D⁻¹ʳ * R) = Q)
    (f g : Hℝ) :
    ⟪pureExtension Γ D hD hu hd (phaseEmbedding Γ R hr f),
      pureExtension Γ D hD hu hd (phaseEmbedding Γ R hr g)⟫_ℂ =
    ⟪(f : H), Q (g : H)⟫_ℂ - Complex.I * ⟪(f : H), R (g : H)⟫_ℂ := by
  let S := CFC.sqrt D
  have hS : IsUnit S := (CFC.isUnit_sqrt_iff D hD).mpr hu
  have hsadj : S.adjoint = S := adjoint_of_nonneg (CFC.sqrt_nonneg D)
  have hinvadj := inverse_adjoint_eq_self hsadj
  have hsq : S * S = D := CFC.sqrt_mul_sqrt_self D hD
  have hinv : S⁻¹ʳ * S⁻¹ʳ = D⁻¹ʳ := by rw [← hsq, Ring.inverse_mul (Or.inl hS)]
  let a : ℝ := (Real.sqrt 2)⁻¹
  have ha : a * a = 1 / 2 := by
    dsimp [a]
    rw [← mul_inv, ← pow_two, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), one_div]
  have he (x : Hℝ) : pureExtension Γ D hD hu hd (phaseEmbedding Γ R hr x) =
      a • (S (x : H) - Complex.I • S⁻¹ʳ (R (x : H))) := by
    rw [pureExtension_apply]
    change S (a • (x : H)) - Complex.I • S⁻¹ʳ (a • R (x : H)) = _
    rw [S.map_smul_of_tower, S⁻¹ʳ.map_smul_of_tower, smul_sub, smul_comm Complex.I a]
  rw [he, he, inner_smul_left_eq_smul, inner_smul_right_eq_smul, smul_smul, ha]
  have hdiag : ⟪R (f : H), D⁻¹ʳ (R (g : H))⟫_ℂ =
      -⟪(f : H), (R * D⁻¹ʳ * R) (g : H)⟫_ℂ := by
    rw [← adjoint_inner_right, hs, neg_apply, inner_neg_right]
    rfl
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    Complex.conj_I, inner_squeeze, hsadj, hinvadj, hsq, hinv,
    Ring.mul_inverse_cancel S hS, Ring.inverse_mul_cancel S hS, hdiag]
  rw [← hcov, smul_apply, inner_smul_right_eq_smul, sub_apply, inner_sub_right]
  rw [hs, mul_one, neg_apply, inner_neg_right]
  simp [Algebra.smul_def]
  ring_nf
  simp
  ring

/-- The transition on the real coordinate of the two pure extensions. -/
def squeezeTransition (D₁ D₂ : H →L[ℂ] H) : H →L[ℂ] H :=
  CFC.sqrt D₂ * (CFC.sqrt D₁)⁻¹ʳ

/-- The transition is real and invertible, with a coercive metric differing from the identity by a Hilbert–Schmidt operator. -/
theorem squeezeTransition_properties (D₁ D₂ : H →L[ℂ] H) (h₁ : 0 ≤ D₁) (h₂ : 0 ≤ D₂)
    (u₁ : IsUnit D₁) (u₂ : IsUnit D₂) (r₁ : ∀ x, J (D₁ x) = D₁ (J x))
    (r₂ : ∀ x, J (D₂ x) = D₂ (J x)) (hdiff : IsHilbertSchmidt (D₂ - D₁)) :
    let L := squeezeTransition D₁ D₂
    let A := L.adjoint * L - 1
    (∀ x, J (L x) = L (J x)) ∧ IsUnit L ∧
      (∀ x, J (A x) = A (J x)) ∧ IsSelfAdjoint A ∧ IsHilbertSchmidt A ∧
      ∃ c : ℝ, 0 < c ∧ c • (1 : H →L[ℂ] H) ≤ L.adjoint * L := by
  let L := squeezeTransition D₁ D₂
  have hS := (CFC.isUnit_sqrt_iff D₁ h₁).mpr u₁
  have hT := (CFC.isUnit_sqrt_iff D₂ h₂).mpr u₂
  have hL : IsUnit L := hT.mul hS.ringInverse
  have hr : ∀ x, J (L x) = L (J x) :=
    squeeze_mul_real Γ (rootReal Γ h₂ r₂)
      (inverseReal Γ hS (rootReal Γ h₁ r₁))
  have ha : IsSelfAdjoint (L.adjoint * L) := by
    rw [← star_eq_adjoint]
    exact IsSelfAdjoint.of_nonneg (star_mul_self_nonneg L)
  refine ⟨hr, hL, ?_, ha.sub (IsSelfAdjoint.one _), ?_, star_mul_self_coercive L hL⟩
  · intro x
    change J ((L.adjoint * L - 1) x) = (L.adjoint * L - 1) (J x)
    simp [mul_apply_eq_comp, hr, adjoint_commutes Γ L hr]
  · change IsHilbertSchmidt (L.adjoint * L - 1)
    exact (sqrt_transition_metric_sub D₁ D₂ h₁ h₂ u₁).symm ▸
      isHilbertSchmidt_mul_right (isHilbertSchmidt_mul_left hdiff)

omit [CompleteSpace H] in
private theorem squeeze_norm_add (x y : Hℝ) :
    ‖(x : H) + Complex.I • (y : H)‖ ^ 2 = ‖(x : H)‖ ^ 2 + ‖(y : H)‖ ^ 2 := by
  have h := real_imag_unique Γ _ x y rfl
  simpa only [h.1, h.2] using norm_sq_decomposition Γ ((x : H) + Complex.I • (y : H))

/-- The countable real eigenbasis of the transition metric gives square-summable squeeze parameters and the norm expansion on the entire complex space. -/
theorem exists_squeeze_eigenbasis [TopologicalSpace.SeparableSpace H]
    (D₁ D₂ : H →L[ℂ] H) (h₁ : 0 ≤ D₁) (h₂ : 0 ≤ D₂) (u₁ : IsUnit D₁) (u₂ : IsUnit D₂)
    (r₁ : ∀ x, J (D₁ x) = D₁ (J x)) (r₂ : ∀ x, J (D₂ x) = D₂ (J x))
    (hdiff : IsHilbertSchmidt (D₂ - D₁)) :
    ∃ (w : Set Hℝ) (b : HilbertBasis w ℝ Hℝ) (r : w → ℝ), Countable w ∧
      Summable (fun i => (r i)^2) ∧
      ∀ z : H,
        ‖pureExtension Γ D₂ h₂ u₂ r₂ ((pureExtension Γ D₁ h₁ u₁ r₁).symm z)‖ ^ 2 =
          ∑' i, (Real.exp (2 * r i) * (⟪complexHilbertBasis Γ b i, z⟫_ℂ).re ^ 2 +
            Real.exp (-2 * r i) * (⟪complexHilbertBasis Γ b i, z⟫_ℂ).im ^ 2) := by
  let L := squeezeTransition D₁ D₂
  let A := L.adjoint * L - 1
  obtain ⟨hLr, hLu, hAr, hAs, hAhs, c, hc, hcoer⟩ :=
    squeezeTransition_properties Γ D₁ D₂ h₁ h₂ u₁ u₂ r₁ r₂ hdiff
  obtain ⟨w, b, lam, hLam⟩ :=
    CompactEigenbasis.exists_setIndex_real_eigenbasis_rclike
      (restrictReal_isCompact Γ A hAr hAhs) (restrictReal_selfAdjoint Γ A hAr hAs).isSymmetric
  let C := complexHilbertBasis Γ b
  have he (i : w) : (L.adjoint * L) (C i) = ((1 + lam i : ℝ) : ℂ) • C i := by
    have hh := congrArg (fun x : Hℝ => (x : H)) (hLam i)
    change (L.adjoint * L) (b i : H) - (b i : H) = lam i • (b i : H) at hh
    rw [sub_eq_iff_eq_add] at hh
    simp only [C, complexHilbertBasis_apply]
    rw [hh]
    change lam i • (b i : H) + (b i : H) = (1 + lam i) • (b i : H)
    simp [add_smul, add_comm]
  have hs := (restrictReal_hasSum_hsSq Γ A hAr hAhs b).summable
  have hLamS : Summable (fun i => (lam i) ^ 2) := by
    simpa only [hLam, norm_smul, b.orthonormal.1, mul_one, Real.norm_eq_abs, sq_abs,
      RCLike.ofReal_real_eq_id, id_eq] using hs
  obtain ⟨r, hrs, hnorm⟩ := exists_logWeights_of_metric C L hLu lam he hLamS
  refine ⟨w, b, r, countable_basis C, hrs, ?_⟩
  intro z
  let x : Hℝ := ⟨realPart Γ z, realPart_mem Γ z⟩
  let y : Hℝ := ⟨imagPart Γ z, imagPart_mem Γ z⟩
  let S := CFC.sqrt D₁
  let T := CFC.sqrt D₂
  have hS : IsUnit S := (CFC.isUnit_sqrt_iff D₁ h₁).mpr u₁
  have hT : IsUnit T := (CFC.isUnit_sqrt_iff D₂ h₂).mpr u₂
  let M := T⁻¹ʳ * S
  have hMr : ∀ x, J (M x) = M (J x) :=
    squeeze_mul_real Γ (inverseReal Γ hT (rootReal Γ h₂ r₂))
      (rootReal Γ h₁ r₁)
  have hM : M = (L.adjoint)⁻¹ʳ := by
    change T⁻¹ʳ * S = ((T * S⁻¹ʳ).adjoint)⁻¹ʳ
    rw [← star_eq_adjoint, star_mul, star_eq_adjoint, star_eq_adjoint,
      inverse_adjoint_eq_self (adjoint_of_nonneg (CFC.sqrt_nonneg D₁)), adjoint_of_nonneg (CFC.sqrt_nonneg D₂),
      Ring.inverse_mul (Or.inl hS.ringInverse), Ring.inverse_inverse hS]
  have hz : pureExtension Γ D₂ h₂ u₂ r₂ ((pureExtension Γ D₁ h₁ u₁ r₁).symm z) =
      L (x : H) + Complex.I • M (y : H) := by
    change T (S⁻¹ʳ (x : H)) - Complex.I • T⁻¹ʳ (S (-(y : H))) = _
    simp [L, M, S, T, squeezeTransition, mul_apply_eq_comp]
  have hz₁ : ‖pureExtension Γ D₂ h₂ u₂ r₂ ((pureExtension Γ D₁ h₁ u₁ r₁).symm z)‖ ^ 2 =
      ‖L (x : H)‖ ^ 2 + ‖M (y : H)‖ ^ 2 := by
    rw [hz]
    exact squeeze_norm_add Γ (restrictReal Γ L hLr x) (restrictReal Γ M hMr y)
  rw [hz₁, hM, hnorm]
  apply tsum_congr
  intro i
  have hi : ⟪C i, z⟫_ℂ = ⟪(b i : H), (x : H)⟫_ℂ + Complex.I * ⟪(b i : H), (y : H)⟫_ℂ := by
    conv_lhs => rw [real_imag_decomposition Γ z]
    simp only [C, complexHilbertBasis_apply, inner_add_right, inner_smul_right]
    rfl
  change _ = Real.exp (2 * r i) * (⟪C i, z⟫_ℂ).re ^ 2 +
    Real.exp (-2 * r i) * (⟪C i, z⟫_ℂ).im ^ 2
  rw [hi]
  simp [C, real_inner Γ, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.norm_real, sq_abs]

end PureExtension

omit [CompleteSpace H] in
/-- The phase embedding is injective even when the common skew operator has a kernel. -/
theorem phaseEmbedding_injective (Γ : RealConjugation H) (R : Op) (hr : IsReal Γ R) :
    Function.Injective (phaseEmbedding Γ R hr) := by
  intro f g h
  have hf := congrArg Prod.fst h
  change (Real.sqrt 2)⁻¹ • f = (Real.sqrt 2)⁻¹ • g at hf
  have hs : Real.sqrt (2 : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  simpa only [smul_smul, mul_inv_cancel₀ hs, one_smul] using
    congrArg (fun x : realSubspace Γ => Real.sqrt 2 • x) hf

/-- The original signed covariances are the restrictions of the same real phase space,
and the two pure coordinates have square-summable relative squeezing. -/
theorem commonPureExtension [TopologicalSpace.SeparableSpace H]
    (Γ : RealConjugation H) {Q R : Op} (hQ : 0 ≤ Q) (hker : Q.ker = ⊥)
    (hq : IsReal Γ Q) (hR : R.adjoint = -R) (hr : IsReal Γ R)
    (h₁ : 0 ≤ 1 - Complex.I • R) (h₂ : 0 ≤ Q - Complex.I • R)
    (hHS : IsHilbertSchmidt (CFC.sqrt (Q - Complex.I • R) - CFC.sqrt (1 - Complex.I • R))) :
    let D₁ := doubleCovariance 1 R
    let D₂ := doubleCovariance Q R
    ∃ (p₁ : 0 ≤ D₁) (p₂ : 0 ≤ D₂) (u₁ : IsUnit D₁) (u₂ : IsUnit D₂)
      (r₁ : IsReal Γ D₁) (r₂ : IsReal Γ D₂),
      let l₁ := pureExtension Γ D₁ p₁ u₁ r₁
      let l₂ := pureExtension Γ D₂ p₂ u₂ r₂
      let ι := phaseEmbedding Γ R hr
      (∀ f g, ⟪l₁ (ι f), l₁ (ι g)⟫_ℂ = ⟪(f : H), (g : H)⟫_ℂ - Complex.I * ⟪(f : H), R (g : H)⟫_ℂ) ∧
      (∀ f g, ⟪l₂ (ι f), l₂ (ι g)⟫_ℂ = ⟪(f : H), Q (g : H)⟫_ℂ - Complex.I * ⟪(f : H), R (g : H)⟫_ℂ) ∧
      ∃ (w : Set (realSubspace Γ)) (b : HilbertBasis w ℝ (realSubspace Γ)) (r : w → ℝ),
        Countable w ∧ Summable (fun i => (r i)^2) ∧ ∀ z : H,
          ‖l₂ (l₁.symm z)‖ ^ 2 =
            ∑' i, (Real.exp (2 * r i) * (⟪complexHilbertBasis Γ b i, z⟫_ℂ).re ^ 2 +
              Real.exp (-2 * r i) * (⟪complexHilbertBasis Γ b i, z⟫_ℂ).im ^ 2) := by
  obtain ⟨_, _, _, hu, hroot, hinv⟩ := covariance_coercive hQ hker h₁ h₂ hHS
  have hOne : IsReal Γ (1 : Op) := fun _ => rfl
  have huOne : IsUnit (CFC.sqrt (1 : Op)) := by simp
  obtain ⟨r₁, hle₁, _, u₁, he₁⟩ := doubleCovariance_properties Γ zero_le_one huOne hOne hR hr h₁
  obtain ⟨r₂, hle₂, _, u₂, he₂⟩ := doubleCovariance_properties Γ hQ hu hq hR hr h₂
  have hdiff := doubleCovariance_sub_hs hroot (defectRoot_sub_hs Γ hQ hu hq hR hr h₁ h₂ hinv hHS)
  have p₁ := zero_le_one.trans hle₁
  have p₂ := hQ.trans hle₂
  refine ⟨p₁, p₂, u₁, u₂, r₁, r₂, ?_, pureExtension_inner Γ _ Q R p₂ u₂ r₂ hr hR he₂, ?_⟩
  · simpa using pureExtension_inner Γ _ 1 R p₁ u₁ r₁ hr hR he₁
  · exact exists_squeeze_eigenbasis Γ _ _ p₁ p₂ u₁ u₂ r₁ r₂ hdiff

end D5.S3.Quantum.Analysis.NullConeGravity.CCRGaussianExtension
