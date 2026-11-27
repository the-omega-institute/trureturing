/- GID: D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondExcitability4D
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/NullConeGravity/NullDiamondExcitability4D
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Mutual Gaussian excitability on the complete real-conjugation invariant null-diamond subspaces. -/

import D5.S3.Quantum.Analysis.NullConeGravity.CCRGaussianFolium
import D5.S3.Quantum.Analysis.NullConeGravity.CCRWeylState
import D5.S3.Quantum.Analysis.NullConeGravity.CCRGaussianExtension
import D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondEq71Trace4D
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import D5.S3.Quantum.Analysis.NullConeGravity.CCRFockWeyl
import Mathlib.MeasureTheory.Measure.SeparableMeasure

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open ContinuousLinearMap HilbertSchmidt MeasureTheory
open D5.S3.Quantum.Analysis.NullConeGravity.CCRWeylState
open D5.S3.Quantum.Analysis.NullConeGravity.CCRFockOccupation
open D5.S3.Quantum.Analysis.NullConeGravity.CCRFockWeyl
open D5.S3.Quantum.Analysis.NullConeGravity.CCRGaussianExtension
open D5.S3.Quantum.Analysis.NullConeGravity.QuarterPowerSqrtHilbertSchmidt
open scoped ComplexOrder InnerProductSpace NNReal Ring CStarAlgebra

namespace NullConeGravity
private local instance : SFinite phaseMeasure := by unfold phaseMeasure; infer_instance
private local instance : SecondCountableTopology H4D := by
  have : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  exact Lp.SecondCountableTopology

/-- Restriction of frequency-reflecting conjugation to an invariant complex subspace. -/
def subspaceConjugation (V : Submodule ℂ H4D) (hV : ∀ x ∈ V, nullConj x ∈ V) : RealConjugation V where
  toLinearIsometryEquiv :=
    { toLinearEquiv := LinearEquiv.ofInvolutive
        { toFun := fun x => ⟨nullConj x, hV x x.property⟩
          map_add' := fun x y => Subtype.ext (map_add nullConj (x : H4D) y)
          map_smul' := fun c x => Subtype.ext (map_smul nullConj c (x : H4D)) }
        (fun x => Subtype.ext (nullConj_involutive x))
      norm_map' := fun x => nullConj.norm_map (x : H4D) }
  involutive := fun x => Subtype.ext (nullConj_involutive x)
  map_complex_smul := fun c x => Subtype.ext (nullConj_smul c x)

section OperatorReality
variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
private abbrev RealOperator (Γ : RealConjugation H) (T : H →L[ℂ] H) : Prop :=
  ∀ x, Γ.toLinearIsometryEquiv (T x) = T (Γ.toLinearIsometryEquiv x)
private theorem adjoint_conjugation (Γ : RealConjugation H) (Γ' : RealConjugation K)
    (C : K →L[ℂ] H) (hC : ∀ x, Γ.toLinearIsometryEquiv (C x) = C (Γ'.toLinearIsometryEquiv x))
    (y : H) : Γ'.toLinearIsometryEquiv (C.adjoint y) = C.adjoint (Γ.toLinearIsometryEquiv y) := by
  apply ext_inner_left ℂ
  intro x
  have h := conj_inner Γ' (Γ'.toLinearIsometryEquiv x) (C.adjoint y)
  rw [Γ'.involutive, adjoint_inner_right, ← hC, ← conj_inner Γ, Γ.involutive] at h
  rwa [adjoint_inner_right]
private theorem congr_conjugation (Γ : RealConjugation H) (Γ' : RealConjugation K)
    (C : K →L[ℂ] H) (hC : ∀ x, Γ.toLinearIsometryEquiv (C x) = C (Γ'.toLinearIsometryEquiv x))
    {A : H →L[ℂ] H} (hA : RealOperator Γ A) : RealOperator Γ' (adjointCongr C A) := by
  intro x
  simp only [adjointCongr, comp_apply, adjoint_conjugation Γ Γ' C hC, hA, hC]
private theorem squareRoot_real (Γ : RealConjugation H) {T : H →L[ℂ] H}
    (hT : 0 ≤ T) (hr : RealOperator Γ T) : RealOperator Γ (CFC.sqrt T) := by
  have h : conjOp Γ T = T := by ext x; rw [conjOp_apply, hr, Γ.involutive]
  have he : CFC.sqrt T = conjOp Γ (CFC.sqrt T) := by
    apply CFC.sqrt_unique _ (conjOp_nonneg Γ _ (CFC.sqrt_nonneg T))
    change (conjOp Γ (CFC.sqrt T)).comp (conjOp Γ (CFC.sqrt T)) = T
    rw [← conjOp_comp]
    change conjOp Γ (CFC.sqrt T * CFC.sqrt T) = T
    rw [CFC.sqrt_mul_sqrt_self T hT, h]
  intro x
  have hx := DFunLike.congr_fun he (Γ.toLinearIsometryEquiv x)
  change (CFC.sqrt T) (Γ.toLinearIsometryEquiv x) = Γ.toLinearIsometryEquiv
    ((CFC.sqrt T) (Γ.toLinearIsometryEquiv (Γ.toLinearIsometryEquiv x))) at hx
  rw [Γ.involutive] at hx
  exact hx.symm
private theorem inverse_real (Γ : RealConjugation H) {T : H →L[ℂ] H}
    (hr : RealOperator Γ T) : RealOperator Γ T⁻¹ʳ := by
  by_cases hT : IsUnit T
  · have hinj := (isUnit_iff_bijective.mp hT).1
    intro x
    apply hinj
    rw [← hr, ← mul_apply_eq_comp, Ring.mul_inverse_cancel _ hT, one_apply_eq_self]
    rw [← mul_apply_eq_comp, Ring.mul_inverse_cancel _ hT, one_apply_eq_self]
  · rw [Ring.inverse_non_unit _ hT]
    simp [RealOperator]
end OperatorReality

section RelativeOperators
variable (V : Submodule ℂ H4D) [CompleteSpace V]
variable (hV : ∀ x ∈ V, nullConj x ∈ V) (M : ℝ) (hM : 0 < M)
private theorem compressed_real : RealOperator (subspaceConjugation V hV) (compressedN V M hM) := by
  apply congr_conjugation nullDiamondRealConjugation (subspaceConjugation V hV) V.subtypeL (fun _ => rfl)
  intro x
  change nullConj (nullN M hM x) = nullN M hM (nullConj x)
  simp [nullN, nullConj_comm_T]
set_option maxHeartbeats 1600000 in
private theorem compressed_positive : 0 ≤ compressedN V M hM := by
  obtain ⟨c, hc, hle⟩ := nullN_coercive M hM
  have hn : 0 ≤ nullN M hM := (show 0 ≤ c • (1 : H4D →L[ℂ] H4D) from
    nonneg_iff_isPositive.mpr (isPositive_one.smul_of_nonneg (Complex.zero_le_real.mpr hc.le))).trans hle
  exact nonneg_iff_isPositive.mpr ((nonneg_iff_isPositive.mp hn).adjoint_conj V.subtypeL)
set_option maxHeartbeats 1600000 in
private theorem inverseRoot_real : RealOperator (subspaceConjugation V hV) (invRootN V M hM) :=
  inverse_real _ (squareRoot_real _ (compressed_positive V M hM) (compressed_real V hV M hM))
private theorem reference_real (x : V) :
    nullConj (referenceMap V M hM x) = referenceMap V M hM ((subspaceConjugation V hV).toLinearIsometryEquiv x) :=
  congrArg Subtype.val (inverseRoot_real V hV M hM x)
set_option maxHeartbeats 1600000 in
private theorem relativeQ_real : RealOperator (subspaceConjugation V hV) (relativeQ V M hM) :=
  congr_conjugation nullDiamondRealConjugation (subspaceConjugation V hV)
    (referenceMap V M hM) (reference_real V hV M hM) (fun _ => rfl)
set_option maxHeartbeats 1600000 in
private theorem relativeR_real : RealOperator (subspaceConjugation V hV) (relativeR V M hM) := by
  let Γ := subspaceConjugation V hV
  let C := referenceMap V M hM
  intro x
  change Γ.toLinearIsometryEquiv (Complex.I • C.adjoint (nullJ (C x))) =
    Complex.I • C.adjoint (nullJ (C (Γ.toLinearIsometryEquiv x)))
  rw [Γ.map_complex_smul, adjoint_conjugation nullDiamondRealConjugation Γ C (reference_real V hV M hM)]
  change star Complex.I • C.adjoint (nullConj (nullJ (C x))) = _
  rw [nullConj_anti_J, map_neg, reference_real V hV M hM]
  simp only [Complex.star_def, Complex.conj_I, neg_smul, smul_neg, neg_neg]
  rfl
set_option maxHeartbeats 1600000 in
private theorem relativeR_adjoint : (relativeR V M hM).adjoint = -relativeR V M hM := by
  let C := referenceMap V M hM
  have hj : nullJ.adjoint = nullJ := (IsSelfAdjoint.of_nonneg nullA_nonneg).sub (IsSelfAdjoint.one _)
  have hsa : IsSelfAdjoint (adjointCongr C nullJ) := by
    change (adjointCongr C nullJ).adjoint = _
    simp [adjointCongr, adjoint_comp, hj, comp_assoc]
  rw [← star_eq_adjoint]
  change star (Complex.I • adjointCongr C nullJ) = -(Complex.I • adjointCongr C nullJ)
  rw [star_smul, hsa.star_eq]
  simp

set_option maxHeartbeats 2000000 in
/-- Real and positive relative covariance data, with finite square-root difference. -/
theorem nullDiamondRelativeProperties :
    0 ≤ relativeQ V M hM ∧ (relativeQ V M hM).ker = ⊥ ∧
    (∀ x, (subspaceConjugation V hV).toLinearIsometryEquiv (relativeQ V M hM x) =
      relativeQ V M hM ((subspaceConjugation V hV).toLinearIsometryEquiv x)) ∧
    (relativeR V M hM).adjoint = -relativeR V M hM ∧
    (∀ x, (subspaceConjugation V hV).toLinearIsometryEquiv (relativeR V M hM x) =
      relativeR V M hM ((subspaceConjugation V hV).toLinearIsometryEquiv x)) ∧
    0 ≤ (1 : V →L[ℂ] V) - Complex.I • relativeR V M hM ∧
    0 ≤ relativeQ V M hM - Complex.I • relativeR V M hM ∧
    IsHilbertSchmidt (eq71Delta V M hM) := by
  obtain ⟨_, _, _, hv⟩ := nullDiamond_eq71_4D M 1 hM zero_lt_one
  simp only [mul_one] at hv
  obtain ⟨_, _, hk, hp₂, hp₁, hd, _⟩ := hv V
  refine ⟨?_, hk, relativeQ_real V hV M hM, relativeR_adjoint V M hM,
    relativeR_real V hV M hM, hp₁, hp₂, hd⟩
  exact nonneg_iff_isPositive.mpr (isPositive_one.adjoint_conj (referenceMap V M hM))
end RelativeOperators

section Excitability

open D5.S3.Quantum.Analysis.NullConeGravity.CCRGaussianFolium
variable {S A : Type*} [AddCommGroup S] [Module ℝ S]
variable [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {σ : S →ₗ[ℝ] S →ₗ[ℝ] ℝ}

set_option maxHeartbeats 2000000 in
/-- The relative massless and massive Gaussian states are in one another's countable GNS folia. -/
theorem nullDiamond_excitable_4D (m L : ℝ) (hm : 0 < m) (hL : 0 < L)
    (V : Submodule ℂ H4D) [CompleteSpace V] (hV : ∀ x ∈ V, nullConj x ∈ V)
    (W : WeylSystem (A := A) σ) (ω₀ ω_m : A →ₚ[ℂ] ℂ) (e : S →ₗ[ℝ] V)
    (he : ∀ f, (subspaceConjugation V hV).toLinearIsometryEquiv (e f) = e f)
    (hd : Dense (Submodule.span ℂ (Set.range e) : Set V))
    (hσ : ∀ f g, σ f g = -2 * (⟪e f, relativeR V (m * L) (mul_pos hm hL) (e g)⟫_ℂ).re)
    (h₀ : ω₀ 1 = 1) (hmState : ω_m 1 = 1)
    (hRef : ∀ f, ω_m (W.weyl f) = Complex.exp (-(‖e f‖^2 : ℂ)/2))
    (hTarget : ∀ f, ω₀ (W.weyl f) = Complex.exp
      (-((⟪e f, relativeQ V (m * L) (mul_pos hm hL) (e f)⟫_ℂ).re : ℂ)/2)) :
    Excitability ω₀ ω_m ∧ Excitability ω_m ω₀ := by
  let hM := mul_pos hm hL
  obtain ⟨hQ, hker, hq, hR, hr, h₁, h₂, hHS⟩ := nullDiamondRelativeProperties V hV (m * L) hM
  exact gaussian_mutual_excitable_of_sqrt_hs W ω_m ω₀ (subspaceConjugation V hV) e he hd
    (relativeQ V (m * L) hM) (relativeR V (m * L) hM) hQ hker hq hR hr h₁ h₂
    hmState h₀ hσ hRef hTarget hHS
end Excitability

section ConcreteAlgebra

variable {S H I J : Type*} [AddCommGroup S] [Module ℝ S]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]

private abbrev FockOperators (I : Type*) := BosonFock I →L[ℂ] BosonFock I

def pairDisplacements (b₁ : HilbertBasis I ℂ H) (b₂ : HilbertBasis J ℂ H)
    (z₁ z₂ : S →ₗ[ℝ] H) (f : S) : FockOperators I × FockOperators J :=
  ((fockWeyl b₁ (z₁ f) : FockOperators I), (fockWeyl b₂ (z₂ f) : FockOperators J))

variable (b₁ : HilbertBasis I ℂ H) (b₂ : HilbertBasis J ℂ H)
    (z₁ z₂ : S →ₗ[ℝ] H)
    (σ : S →ₗ[ℝ] S →ₗ[ℝ] ℝ)
    (h₁ : ∀ f g, σ f g = 2 * (⟪z₁ f, z₁ g⟫_ℂ).im)
    (h₂ : ∀ f g, σ f g = 2 * (⟪z₂ f, z₂ g⟫_ℂ).im)
private theorem pairDisplacements_zero :
    pairDisplacements b₁ b₂ z₁ z₂ 0 = 1 := by
  apply Prod.ext <;> ext ψ <;> simp [pairDisplacements, fockWeyl_zero]

include h₁ h₂ in
private theorem pairDisplacements_mul (f g : S) :
    pairDisplacements b₁ b₂ z₁ z₂ f * pairDisplacements b₁ b₂ z₁ z₂ g =
      Complex.exp (-(Complex.I * (σ f g : ℂ)) / 2) •
        pairDisplacements b₁ b₂ z₁ z₂ (f + g) := by
  have phase (r : ℝ) : -(Complex.I * ((2 * r : ℝ) : ℂ)) / 2 = -(Complex.I * (r : ℂ)) := by
    push_cast
    ring
  apply Prod.ext
  · apply ContinuousLinearMap.ext
    intro ψ
    change fockWeyl b₁ (z₁ f) (fockWeyl b₁ (z₁ g) ψ) =
      Complex.exp (-(Complex.I * (σ f g : ℂ)) / 2) • fockWeyl b₁ (z₁ (f + g)) ψ
    rw [fockWeyl_mul, h₁, phase, map_add]
  · apply ContinuousLinearMap.ext
    intro ψ
    change fockWeyl b₂ (z₂ f) (fockWeyl b₂ (z₂ g) ψ) =
      Complex.exp (-(Complex.I * (σ f g : ℂ)) / 2) • fockWeyl b₂ (z₂ (f + g)) ψ
    rw [fockWeyl_mul, h₂, phase, map_add]

private theorem pairDisplacements_star (f : S) :
    star (pairDisplacements b₁ b₂ z₁ z₂ f) = pairDisplacements b₁ b₂ z₁ z₂ (-f) := by
  apply Prod.ext
  · change adjoint (fockWeyl b₁ (z₁ f) : FockOperators I) =
      (fockWeyl b₁ (z₁ (-f)) : FockOperators I)
    rw [LinearIsometryEquiv.adjoint_eq_symm, map_neg, fockWeyl_symm]
  · change adjoint (fockWeyl b₂ (z₂ f) : FockOperators J) =
      (fockWeyl b₂ (z₂ (-f)) : FockOperators J)
    rw [LinearIsometryEquiv.adjoint_eq_symm, map_neg, fockWeyl_symm]

include h₁ h₂ in
private def pairWeylSpan : StarSubalgebra ℂ (FockOperators I × FockOperators J) := by
  let P := Submodule.span ℂ (Set.range (pairDisplacements b₁ b₂ z₁ z₂))
  have hOne : (1 : FockOperators I × FockOperators J) ∈ P := by
    rw [← pairDisplacements_zero b₁ b₂ z₁ z₂]
    exact Submodule.subset_span (Set.mem_range_self 0)
  have hMul : ∀ a b, a ∈ P → b ∈ P → a * b ∈ P := by
    intro a b ha hb
    induction ha, hb using Submodule.span_induction₂ with
    | mem_mem x y hx hy =>
      obtain ⟨f, rfl⟩ := hx
      obtain ⟨g, rfl⟩ := hy
      rw [pairDisplacements_mul b₁ b₂ z₁ z₂ σ h₁ h₂]
      exact P.smul_mem _ (Submodule.subset_span (Set.mem_range_self _))
    | zero_left => simp [P]
    | zero_right => simp [P]
    | add_left _ _ _ _ _ _ hx hy => rw [add_mul]; exact P.add_mem hx hy
    | add_right _ _ _ _ _ _ hx hy => rw [mul_add]; exact P.add_mem hx hy
    | smul_left c _ _ _ _ hx => rw [smul_mul_assoc]; exact P.smul_mem c hx
    | smul_right c _ _ _ _ hx => rw [mul_smul_comm]; exact P.smul_mem c hx
  refine { P.toSubalgebra hOne hMul with star_mem' := ?_ }
  intro x hx
  change x ∈ P at hx
  change star x ∈ P
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, rfl⟩ := hx
    rw [pairDisplacements_star]
    exact Submodule.subset_span (Set.mem_range_self _)
  | zero =>
    have h : star (0 : FockOperators I × FockOperators J) = 0 := by
      apply Prod.ext
      · change adjoint (0 : FockOperators I) = 0
        simp
      · change adjoint (0 : FockOperators J) = 0
        simp
    exact h.symm ▸ P.zero_mem
  | add x y _ _ hx hy =>
    change (star (x + y) : FockOperators I × FockOperators J) ∈ P
    have h : star (x+y) = star x + star y := star_add x y
    exact h.symm ▸ P.add_mem hx hy
  | smul c x _ hx =>
    change (star (c • x) : FockOperators I × FockOperators J) ∈ P
    have h : star (c • x) = star c • star x := star_smul c x
    exact h.symm ▸ P.smul_mem _ hx
/-- The norm-closed star algebra generated by the paired Weyl displacements. -/
def pairWeylAlgebra : StarSubalgebra ℂ (FockOperators I × FockOperators J) :=
  (StarAlgebra.adjoin ℂ (Set.range (pairDisplacements b₁ b₂ z₁ z₂))).topologicalClosure

instance pairWeylAlgebra_isClosed :
    IsClosed (pairWeylAlgebra b₁ b₂ z₁ z₂ : Set (FockOperators I × FockOperators J)) :=
  StarSubalgebra.isClosed_topologicalClosure _
instance (priority := 1100) pairWeylAlgebraOrder : PartialOrder (pairWeylAlgebra b₁ b₂ z₁ z₂) :=
  CStarAlgebra.spectralOrder _
instance pairWeylAlgebraStarOrdered : StarOrderedRing (pairWeylAlgebra b₁ b₂ z₁ z₂) :=
  CStarAlgebra.spectralOrderedRing (pairWeylAlgebra b₁ b₂ z₁ z₂)
private def pairWeylGenerator (f : S) : pairWeylAlgebra b₁ b₂ z₁ z₂ :=
  ⟨pairDisplacements b₁ b₂ z₁ z₂ f,
    StarSubalgebra.le_topologicalClosure _ (StarAlgebra.subset_adjoin ℂ _ (Set.mem_range_self f))⟩

/-- The common Weyl system in the closed pair algebra. -/
def pairWeylSystem : WeylSystem (A := pairWeylAlgebra b₁ b₂ z₁ z₂) σ where
  alternating f := by
    rw [h₁]
    change 2 * RCLike.im ⟪z₁ f, z₁ f⟫_ℂ = 0
    rw [inner_self_im, mul_zero]
  weyl := pairWeylGenerator b₁ b₂ z₁ z₂
  weyl_zero := Subtype.ext (pairDisplacements_zero b₁ b₂ z₁ z₂)
  weyl_mul f g := Subtype.ext (pairDisplacements_mul b₁ b₂ z₁ z₂ σ h₁ h₂ f g)
  weyl_star f := Subtype.ext (pairDisplacements_star b₁ b₂ z₁ z₂ f)
  dense_span := by
    rw [Subtype.dense_iff]
    let P := pairWeylAlgebra b₁ b₂ z₁ z₂
    change (P : Set (FockOperators I × FockOperators J)) ⊆ closure
      ((Submodule.map P.toSubalgebra.toSubmodule.subtype
        (Submodule.span ℂ (Set.range (pairWeylGenerator b₁ b₂ z₁ z₂)))) :
          Set (FockOperators I × FockOperators J))
    rw [Submodule.map_span, ← Set.range_comp]
    exact closure_mono (StarAlgebra.adjoin_le
      (S := pairWeylSpan b₁ b₂ z₁ z₂ σ h₁ h₂) Submodule.subset_span)
private def fockVacuumExpectation (I : Type*) : FockOperators I →ₚ[ℂ] ℂ where
  toFun T := ⟪fockVacuum I, T (fockVacuum I)⟫_ℂ
  map_add' T U := by simp [inner_add_right]
  map_smul' c T := by simp [inner_smul_right]
  monotone' := by
    intro T U h
    rw [← sub_nonneg]
    change 0 ≤ ⟪fockVacuum I, U (fockVacuum I)⟫_ℂ - ⟪fockVacuum I, T (fockVacuum I)⟫_ℂ
    rw [← inner_sub_right]
    change 0 ≤ ⟪fockVacuum I, (U - T) (fockVacuum I)⟫_ℂ
    exact (nonneg_iff_isPositive.mp (sub_nonneg.mpr h)).inner_nonneg_right _

def pairVacuumRef : pairWeylAlgebra b₁ b₂ z₁ z₂ →ₚ[ℂ] ℂ :=
  (fockVacuumExpectation I).comp
    (PositiveLinearMap.ofClass ((StarAlgHom.fst ℂ (FockOperators I) (FockOperators J)).comp
      (pairWeylAlgebra b₁ b₂ z₁ z₂).subtype))

def pairVacuumTarget : pairWeylAlgebra b₁ b₂ z₁ z₂ →ₚ[ℂ] ℂ :=
  (fockVacuumExpectation J).comp
    (PositiveLinearMap.ofClass ((StarAlgHom.snd ℂ (FockOperators I) (FockOperators J)).comp
      (pairWeylAlgebra b₁ b₂ z₁ z₂).subtype))

private theorem pairVacuumRef_gaussian (μ : S →ₗ[ℝ] S →ₗ[ℝ] ℝ)
    (hμ : ∀ f, ‖z₁ f‖ ^ 2 = μ f f) :
    IsGaussian (pairWeylSystem b₁ b₂ z₁ z₂ σ h₁ h₂) μ
      (pairVacuumRef b₁ b₂ z₁ z₂) := by
  constructor
  · change ⟪fockVacuum I, fockVacuum I⟫_ℂ = 1
    rw [inner_self_eq_norm_sq_to_K, fockVacuum_norm]
    norm_num
  · intro f
    change ⟪fockVacuum I, fockWeyl b₁ (z₁ f) (fockVacuum I)⟫_ℂ = _
    rw [fockWeyl_vacuum_inner, ← Complex.ofReal_pow, hμ]

private theorem pairVacuumTarget_gaussian (μ : S →ₗ[ℝ] S →ₗ[ℝ] ℝ)
    (hμ : ∀ f, ‖z₂ f‖ ^ 2 = μ f f) :
    IsGaussian (pairWeylSystem b₁ b₂ z₁ z₂ σ h₁ h₂) μ
      (pairVacuumTarget b₁ b₂ z₁ z₂) := by
  constructor
  · change ⟪fockVacuum J, fockVacuum J⟫_ℂ = 1
    rw [inner_self_eq_norm_sq_to_K, fockVacuum_norm]
    norm_num
  · intro f
    change ⟪fockVacuum J, fockWeyl b₂ (z₂ f) (fockVacuum J)⟫_ℂ = _
    rw [fockWeyl_vacuum_inner, ← Complex.ofReal_pow, hμ]
end ConcreteAlgebra
section RealData

open D5.S3.Quantum.Analysis.NullConeGravity.CCRGaussianFolium

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] 
    (Γ : RealConjugation H)
set_option synthInstance.maxHeartbeats 200000 in
/-- A concrete pair of Fock representations with the prescribed Gaussian covariances. -/
def GaussianPairRealization (Q R : H →L[ℂ] H) : Prop :=
  let σ := realSymplecticForm Γ R
  ∃ (w : Set (realSubspace Γ)) (b : HilbertBasis w ℂ H)
    (z_m z₀ : realSubspace Γ →ₗ[ℝ] H)
    (hm : ∀ f g, σ f g = 2 * (⟪z_m f, z_m g⟫_ℂ).im)
    (h₀ : ∀ f g, σ f g = 2 * (⟪z₀ f, z₀ g⟫_ℂ).im),
    let W := pairWeylSystem b b z_m z₀ σ hm h₀
    let ω_m := pairVacuumRef b b z_m z₀
    let ω₀ := pairVacuumTarget b b z_m z₀
    Countable w ∧ IsGaussian W (realCovariance Γ Q) ω₀ ∧
      IsGaussian W (realCovariance Γ 1) ω_m ∧
      Excitability (A := pairWeylAlgebra b b z_m z₀) ω₀ ω_m ∧
      Excitability (A := pairWeylAlgebra b b z_m z₀) ω_m ω₀

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 200000 in
private theorem gaussianPairRealization [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (Q R : H →L[ℂ] H) (hQ : 0 ≤ Q) (hker : Q.ker = ⊥)
    (hq : ∀ x, Γ.toLinearIsometryEquiv (Q x) = Q (Γ.toLinearIsometryEquiv x))
    (hR : R.adjoint = -R) (hr : ∀ x, Γ.toLinearIsometryEquiv (R x) = R (Γ.toLinearIsometryEquiv x))
    (h₁ : 0 ≤ 1 - Complex.I • R) (h₂ : 0 ≤ Q - Complex.I • R)
    (hHS : IsHilbertSchmidt (CFC.sqrt (Q - Complex.I • R) - CFC.sqrt (1 - Complex.I • R))) :
    GaussianPairRealization Γ Q R := by
  obtain ⟨p₁, p₂, u₁, u₂, r₁, r₂, hi₁, hi₂, w, bR, r, hw, hrs, hcov⟩ :=
    commonPureExtension Γ hQ hker hq hR hr h₁ h₂ hHS
  let b := complexHilbertBasis Γ bR
  let z_m := (pureExtension Γ (doubleCovariance 1 R) p₁ u₁ r₁).toLinearMap.comp (phaseEmbedding Γ R hr)
  let z₀ := (pureExtension Γ (doubleCovariance Q R) p₂ u₂ r₂).toLinearMap.comp (phaseEmbedding Γ R hr)
  have hmInner : ∀ f g, ⟪z_m f, z_m g⟫_ℂ =
      ⟪(f : H), (1 : H →L[ℂ] H) (g : H)⟫_ℂ - Complex.I * ⟪(f : H), R (g : H)⟫_ℂ := by
    intro f g
    change ⟪(pureExtension Γ (doubleCovariance 1 R) p₁ u₁ r₁) ((phaseEmbedding Γ R hr) f),
      (pureExtension Γ (doubleCovariance 1 R) p₁ u₁ r₁) ((phaseEmbedding Γ R hr) g)⟫_ℂ = _
    simpa only [one_apply_eq_self] using hi₁ f g
  obtain ⟨hmPhase, hmNorm⟩ := extensionPhaseNorm Γ 1 R (fun _ => rfl) hr z_m hmInner
  obtain ⟨h₀Phase, h₀Norm⟩ := extensionPhaseNorm Γ Q R hq hr z₀ hi₂
  let σ := realSymplecticForm Γ R
  let W := pairWeylSystem b b z_m z₀ σ hmPhase h₀Phase
  let ω_m := pairVacuumRef b b z_m z₀
  let ω₀ := pairVacuumTarget b b z_m z₀
  have gm := pairVacuumRef_gaussian b b z_m z₀ σ hmPhase h₀Phase (realCovariance Γ 1) hmNorm
  have g₀ := pairVacuumTarget_gaussian b b z_m z₀ σ hmPhase h₀Phase (realCovariance Γ Q) h₀Norm
  refine ⟨w, b, z_m, z₀, hmPhase, h₀Phase, hw, g₀, gm, ?_⟩
  apply gaussian_mutual_excitable_of_sqrt_hs W ω_m ω₀ Γ (fixedInclusion Γ)
    (fun f => f.property) (fixedInclusion_dense Γ) Q R hQ hker hq hR hr h₁ h₂ gm.1 g₀.1
    (fun _ _ => rfl) _ g₀.2 hHS
  intro f
  rw [gm.2 f]
  change Complex.exp (-((⟪(f : H), (1 : H →L[ℂ] H) (f : H)⟫_ℂ).re : ℂ)/2) = _
  rw [one_apply_eq_self]
  change Complex.exp (-((RCLike.re ⟪(f : H), (f : H)⟫_ℂ : ℝ) : ℂ)/2) = _
  rw [inner_self_eq_norm_sq, Complex.ofReal_pow]
  rfl
end RealData

/-- The concrete massless and massive covariances on the fixed real form of a null subspace. -/
def NullDiamondConcreteRealization (m L : ℝ) (hm : 0 < m) (hL : 0 < L)
    (V : Submodule ℂ H4D) [CompleteSpace V] (hV : ∀ x ∈ V, nullConj x ∈ V) : Prop :=
  GaussianPairRealization (subspaceConjugation V hV)
    (relativeQ V (m * L) (mul_pos hm hL)) (relativeR V (m * L) (mul_pos hm hL))
set_option maxHeartbeats 2000000 in
/-- The paired Fock Weyl algebra realizes both Gaussian states with mutual excitability. -/
theorem nullDiamond_concrete_gaussian_excitable_4D (m L : ℝ) (hm : 0 < m) (hL : 0 < L)
    (V : Submodule ℂ H4D) [CompleteSpace V] (hV : ∀ x ∈ V, nullConj x ∈ V) :
    NullDiamondConcreteRealization m L hm hL V hV := by
  let hM := mul_pos hm hL
  obtain ⟨hQ, hk, hq, hR, hr, h₁, h₂, hHS⟩ := nullDiamondRelativeProperties V hV (m * L) hM
  exact gaussianPairRealization (subspaceConjugation V hV) _ _ hQ hk hq hR hr h₁ h₂ hHS

private local instance : CompleteSpace (⊤ : Submodule ℂ H4D) :=
  (show IsClosed ((⊤ : Submodule ℂ H4D) : Set H4D) from isClosed_univ).completeSpace_coe

/-- The unconditional realization on the full null-diamond Hilbert space. -/
theorem nullDiamond_full_space_excitable_4D (m L : ℝ) (hm : 0 < m) (hL : 0 < L) :
    NullDiamondConcreteRealization m L hm hL (⊤ : Submodule ℂ H4D)
      (fun _ _ => Submodule.mem_top) :=
  nullDiamond_concrete_gaussian_excitable_4D m L hm hL ⊤ (fun _ _ => Submodule.mem_top)

end NullConeGravity
