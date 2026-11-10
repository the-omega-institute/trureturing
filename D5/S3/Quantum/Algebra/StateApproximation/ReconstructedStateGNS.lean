/- GID: D5/S3/Quantum/Algebra/StateApproximation/ReconstructedStateGNS
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/StateApproximation/ReconstructedStateGNS
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original real states, pure cyclic representations and self-adjoint operator approximation. -/

import D5.S3.Quantum.Algebra.CentralPositiveFunctionalExtension
import D5.S3.Quantum.Algebra.StateApproximation.Physicslib4.GNS.ExtremeState

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped ComplexOrder InnerProductSpace ComplexStarModule
open Physicslib4.GNS

namespace D5.S3.Quantum.Algebra.StateApproximation.ReconstructedStateGNS
universe u
variable {A : Type u} [CStarAlgebra A] [Nontrivial A] [PartialOrder A] [StarOrderedRing A]

def IsRealState (β : selfAdjoint A →ₗ[ℝ] ℝ) : Prop :=
  (∀ a : selfAdjoint A, 0 ≤ (a : A) → 0 ≤ β a) ∧ β 1 = 1

def realStateSpace (A : Type u) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] :
    Set (selfAdjoint A →ₗ[ℝ] ℝ) := {β | IsRealState β}

theorem state_abs_le (β : selfAdjoint A →ₗ[ℝ] ℝ) (hβ : IsRealState β)
    (a : selfAdjoint A) : |β a| ≤ ‖a‖ := by
  have hm : Monotone β := by
    intro x y hxy
    have h := hβ.1 (y - x) (show 0 ≤ ((y - x : selfAdjoint A) : A) from sub_nonneg.mpr hxy)
    simpa only [map_sub, sub_nonneg] using h
  have hu : a ≤ ‖a‖ • (1 : selfAdjoint A) := by
    change (a : A) ≤ ‖a‖ • (1 : A)
    simpa [Algebra.algebraMap_eq_smul_one] using a.property.le_algebraMap_norm_self
  have hl : -(‖a‖ • (1 : selfAdjoint A)) ≤ a := by
    change -(‖a‖ • (1 : A)) ≤ (a : A)
    simpa [Algebra.algebraMap_eq_smul_one] using a.property.neg_algebraMap_norm_le_self
  have h1 := hm hu
  have h2 := hm hl
  simp only [map_smul, map_neg, hβ.2, smul_eq_mul, mul_one] at h1 h2
  exact abs_le.mpr ⟨h2, h1⟩

def realCLM (β : selfAdjoint A →ₗ[ℝ] ℝ) (hβ : IsRealState β) :
    StrongDual ℝ (selfAdjoint A) :=
  β.mkContinuous 1 (fun a => by simpa only [Real.norm_eq_abs, one_mul] using state_abs_le β hβ a)

theorem realCLM_norm_le (β : selfAdjoint A →ₗ[ℝ] ℝ) (hβ : IsRealState β) :
    ‖realCLM β hβ‖ ≤ 1 :=
  β.mkContinuous_norm_le zero_le_one (fun a => by
    simpa only [Real.norm_eq_abs, one_mul] using state_abs_le β hβ a)

def complexStateSpace (A : Type u) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] :
    Set (A →L[ℂ] ℂ) := {φ | (∀ a : A, 0 ≤ a → 0 ≤ φ a) ∧ φ 1 = 1}

def restriction : (A →L[ℂ] ℂ) →ₗ[ℝ] (selfAdjoint A →ₗ[ℝ] ℝ) where
  toFun φ := {
    toFun a := (φ (a : A)).re
    map_add' a b := by simp
    map_smul' c a := by simp }
  map_add' φ ψ := by ext a; simp
  map_smul' c φ := by ext a; simp

def positiveMap (φ : A →L[ℂ] ℂ) (hφ : φ ∈ complexStateSpace A) : A →P[ℂ] ℂ :=
  PositiveContinuousLinearMap.mk₀ φ hφ.1

theorem state_moment (φ : A →L[ℂ] ℂ) (hφ : φ ∈ complexStateSpace A)
    (a : selfAdjoint A) : φ (a : A) = (restriction φ a : ℂ) := by
  exact (Complex.re_eq_ofReal_of_isSelfAdjoint (a.property.map' (positiveMap φ hφ))).mp rfl

theorem restriction_mem (φ : A →L[ℂ] ℂ) (hφ : φ ∈ complexStateSpace A) :
    restriction φ ∈ realStateSpace A := by
  refine ⟨fun a ha => (Complex.nonneg_iff.mp (hφ.1 a ha)).1, ?_⟩
  change (φ (1 : A)).re = 1
  rw [hφ.2, Complex.one_re]

theorem ext_selfAdjoint (φ ψ : A →L[ℂ] ℂ)
    (h : ∀ a : selfAdjoint A, φ (a : A) = ψ (a : A)) : φ = ψ := by
  ext a
  rw [← realPart_add_I_smul_imaginaryPart a]
  simp only [map_add, map_smul, h]

theorem exists_extension (β : selfAdjoint A →ₗ[ℝ] ℝ) (hβ : IsRealState β) :
    ∃ φ : A →L[ℂ] ℂ, φ ∈ complexStateSpace A ∧
      ∀ a : selfAdjoint A, φ (a : A) = (β a : ℂ) := by
  obtain ⟨p, n, hread, hmass⟩ :=
    D5.S3.Quantum.Algebra.CentralPositiveFunctionalExtension.exists_positive_extensions_norm_additive
      (selfAdjoint.submodule ℝ A) (fun a => a.property) (realCLM β hβ)
  have hdiff := hread (1 : selfAdjoint A)
  change β 1 = (p (1 : A)).re - (n (1 : A)).re at hdiff
  have hn0 : 0 ≤ (n (1 : A)).re :=
    (Complex.nonneg_iff.mp (n.map_nonneg (show 0 ≤ (1 : A) from zero_le_one))).1
  have hnb := realCLM_norm_le β hβ
  change (p (1 : A)).re + (n (1 : A)).re = ‖realCLM β hβ‖ at hmass
  have hnzero : (n (1 : A)).re = 0 := by
    rw [hβ.2] at hdiff
    linarith! only [hdiff, hmass, hnb, hn0]
  have hnnorm := congrArg Complex.re (PositiveContinuousLinearMap.ofReal_opNorm_eq_map_one n)
  simp only [Complex.ofReal_re] at hnnorm
  have hnCLM : (n : A →L[ℂ] ℂ) = 0 := norm_eq_zero.mp (hnnorm.trans hnzero)
  have nz (a : A) : n a = 0 := congrArg (fun f : A →L[ℂ] ℂ => f a) hnCLM
  have hmom (a : selfAdjoint A) : p (a : A) = (β a : ℂ) := by
    apply (Complex.re_eq_ofReal_of_isSelfAdjoint (a.property.map' p)).mp
    have hr := hread a
    change β a = (p (a : A)).re - (n (a : A)).re at hr
    simpa only [nz, Complex.zero_re, sub_zero] using hr.symm
  refine ⟨p, ⟨fun a ha => p.map_nonneg ha, ?_⟩, hmom⟩
  simpa only [PositiveContinuousLinearMap.coe_toContinuousLinearMap,
    selfAdjoint.val_one, hβ.2, Complex.ofReal_one] using hmom 1

def extension (β : realStateSpace A) : complexStateSpace A :=
  ⟨(exists_extension β.val β.property).choose, (exists_extension β.val β.property).choose_spec.1⟩

theorem extension_moment (β : realStateSpace A) (a : selfAdjoint A) :
    (extension β).val (a : A) = (β.val a : ℂ) :=
  (exists_extension β.val β.property).choose_spec.2 a

theorem restriction_extension (β : realStateSpace A) : restriction (extension β).val = β.val := by
  ext a
  change ((extension β).val (a : A)).re = β.val a
  rw [extension_moment, Complex.ofReal_re]

theorem extension_restriction (φ : complexStateSpace A) :
    extension ⟨restriction φ.val, restriction_mem φ.val φ.property⟩ = φ := by
  apply Subtype.ext
  apply ext_selfAdjoint
  intro a
  exact (extension_moment _ a).trans (state_moment φ.val φ.property a).symm

def realComplexEquiv : realStateSpace A ≃ complexStateSpace A where
  toFun := extension
  invFun φ := ⟨restriction φ.val, restriction_mem φ.val φ.property⟩
  left_inv β := Subtype.ext (restriction_extension β)
  right_inv := extension_restriction

theorem extension_affine_iff (x y z : realStateSpace A) (s t : ℝ) :
    z.val = s • x.val + t • y.val ↔
      (extension z).val = s • (extension x).val + t • (extension y).val := by
  constructor
  · intro h
    apply ext_selfAdjoint
    intro a
    have ha := congrArg (fun f : selfAdjoint A →ₗ[ℝ] ℝ => f a) h
    simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul] at ha
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, extension_moment,
      Complex.real_smul, smul_eq_mul]
    exact_mod_cast ha
  · intro h
    have hr := congrArg (fun φ : A →L[ℂ] ℂ => restriction φ) h
    simpa only [map_add, map_smul, restriction_extension] using hr

section Transport
variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
variable {S : Set E} {T : Set F}

theorem extreme_forward (e : S ≃ T)
    (haff : ∀ x y z : S, ∀ s t : ℝ,
      z.val = s • x.val + t • y.val ↔ (e z).val = s • (e x).val + t • (e y).val)
    (x : S) (hx : x.val ∈ S.extremePoints ℝ) : (e x).val ∈ T.extremePoints ℝ := by
  rw [mem_extremePoints_iff_left] at hx ⊢
  refine ⟨(e x).property, ?_⟩
  intro y hy z hz hseg
  rcases hseg with ⟨s,t,hs,ht,hst,hcomb⟩
  let y' : S := e.symm ⟨y,hy⟩
  let z' : S := e.symm ⟨z,hz⟩
  have hc : (e x).val = s • (e y').val + t • (e z').val := by
    simpa only [y', z', e.apply_symm_apply] using hcomb.symm
  have hr := (haff y' z' x s t).mpr hc
  have hl := hx.2 y'.val y'.property z'.val z'.property ⟨s,t,hs,ht,hst,hr.symm⟩
  have he : y' = x := Subtype.ext hl
  have he' := congrArg (fun q : S => (e q).val) he
  simpa only [y', e.apply_symm_apply] using he'

theorem extreme_equiv (e : S ≃ T)
    (haff : ∀ x y z : S, ∀ s t : ℝ,
      z.val = s • x.val + t • y.val ↔ (e z).val = s • (e x).val + t • (e y).val)
    (x : S) : x.val ∈ S.extremePoints ℝ ↔ (e x).val ∈ T.extremePoints ℝ := by
  constructor
  · exact extreme_forward e haff x
  · intro h
    have haff' : ∀ x y z : T, ∀ s t : ℝ,
        z.val = s • x.val + t • y.val ↔
        (e.symm z).val = s • (e.symm x).val + t • (e.symm y).val := by
      intro x y z s t
      simpa only [e.apply_symm_apply] using (haff (e.symm x) (e.symm y) (e.symm z) s t).symm
    simpa only [e.symm_apply_apply] using extreme_forward e.symm haff' (e x) h
end Transport

theorem real_complex_extreme_iff (β : realStateSpace A) :
    β.val ∈ (realStateSpace A).extremePoints ℝ ↔
      (extension β).val ∈ (complexStateSpace A).extremePoints ℝ :=
  extreme_equiv realComplexEquiv extension_affine_iff β

def provider (φ : complexStateSpace A) : State A where
  toContinuousLinearMap := φ.val
  isPositive a := φ.property.1 (star a * a) (star_mul_self_nonneg a)
  isNormalized := by
    rw [norm_eq_re_apply_one_of_positive (fun a => φ.property.1 _ (star_mul_self_nonneg a))]
    rw [φ.property.2, Complex.one_re]

theorem provider_mem (ω : State A) : ω.toContinuousLinearMap ∈ complexStateSpace A :=
  ⟨fun a ha => ω.toPositiveLinearMap.map_nonneg ha, ω.apply_one⟩

theorem provider_stateSpace_eq : Physicslib4.GNS.stateSpace A = complexStateSpace A := by
  ext φ
  constructor
  · rintro ⟨ω,rfl⟩
    exact provider_mem ω
  · intro hφ
    exact ⟨provider ⟨φ,hφ⟩,rfl⟩

def originalState (β : realStateSpace A) : State A := provider (extension β)

theorem original_moment (β : realStateSpace A) (a : selfAdjoint A) :
    originalState β (a : A) = (β.val a : ℂ) := extension_moment β a

theorem original_extreme_iff (β : realStateSpace A) :
    β.val ∈ (realStateSpace A).extremePoints ℝ ↔ (originalState β).IsExtremePoint := by
  rw [← mem_extremePoints_iff_isExtremePoint, provider_stateSpace_eq]
  exact real_complex_extreme_iff β

theorem original_pure_iff (β : realStateSpace A) :
    β.val ∈ (realStateSpace A).extremePoints ℝ ↔ IsPure (originalState β) := by
  rw [isPure_iff_isExtremePoint]
  exact original_extreme_iff β

theorem actual_pure_gns (β : selfAdjoint A →ₗ[ℝ] ℝ) (hβ : IsRealState β)
    (hpure : β ∈ (realStateSpace A).extremePoints ℝ) :
    ∃ (φ : A →L[ℂ] ℂ), φ ∈ complexStateSpace A ∧
      (∀ a : selfAdjoint A, φ (a : A) = (β a : ℂ)) ∧
      (∀ ψ : A →L[ℂ] ℂ, ψ ∈ complexStateSpace A →
        (∀ a : selfAdjoint A, ψ (a : A) = (β a : ℂ)) → ψ = φ) ∧
      ∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
        (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (Ω : H),
        ‖Ω‖ = 1 ∧ Dense (Set.range (fun a : A => π a Ω)) ∧
        (∀ a : A, φ a = inner ℂ Ω (π a Ω)) ∧
        (∀ a : selfAdjoint A, inner ℂ Ω (π (a : A) Ω) = (β a : ℂ)) ∧
        (∀ T : H →L[ℂ] H, (∀ a : A, π a * T = T * π a) → ∃ c : ℂ, T = c • 1) := by
  let b : realStateSpace A := ⟨β,hβ⟩
  let ω := originalState b
  have hw : IsPure ω := (original_pure_iff b).mp hpure
  obtain ⟨H, hN, hI, hC, π, Ω, hcyc, hrep, _⟩ := gns_construction ω
  letI := hN
  letI := hI
  letI := hC
  have hn : ‖Ω‖ = 1 := by
    have hunit := hrep (1 : A)
    rw [map_one π, ContinuousLinearMap.one_apply] at hunit
    have hr : (1 : ℝ) = ‖Ω‖ ^ 2 := by
      simpa only [ω.apply_one, RCLike.one_re, ← norm_sq_eq_re_inner] using
        congrArg (RCLike.re : ℂ → ℝ) hunit
    nlinarith [norm_nonneg Ω]
  refine ⟨(extension b).val, (extension b).property, extension_moment b, ?_,
    H, hN, hI, hC, π, Ω, hn, hcyc, hrep, ?_, isIrreducible_of_isPure hcyc hrep hw⟩
  · intro ψ hψ hm
    exact ext_selfAdjoint _ _ (fun a => (hm a).trans (extension_moment b a).symm)
  · intro a
    exact (hrep a).symm.trans (original_moment b a)

end D5.S3.Quantum.Algebra.StateApproximation.ReconstructedStateGNS
