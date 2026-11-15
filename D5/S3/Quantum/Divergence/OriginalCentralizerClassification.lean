/- GID: D5/S3/Quantum/Divergence/OriginalCentralizerClassification
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/OriginalCentralizerClassification
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: Original maximal-hockey equality and the compressed GNS centralizer. -/

import D5.S3.Quantum.Divergence.GNSOverlapRigidity
import D5.S3.Quantum.Divergence.SpectralCentralizerEquality
import D5.S3.Quantum.Lieb.OperatorConvexCurvature

/-!
The original whole-complex-L1 source class is used throughout. Full support
of the actual curvature is required for the convex core and is derived for
the literal nonaffine all-Hilbert operator-convex specialization. The
unrestricted classification retains the separate infinite hockey branch.

admission_basis: open-problem-resolution
All transport and extended-value helpers are consumed by the classifiers.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/29713
No literature novelty or independent final acceptance is asserted.
-/

noncomputable section
universe u v
open Set MeasureTheory
open scoped ComplexOrder InnerProductSpace Topology ENNReal
open D5.S3.Quantum.Analysis
open GNSOrderCoordinates GNSMomentFamilies NormalMomentFamily
open ConcreteCoefficientSeries
open D5.S3.Quantum.Divergence.GeneralConvexReverseTestAttainment
open D5.S3.Quantum.Divergence.NormalOverlapCompatibility
open D5.S3.Quantum.Divergence.NormalOverlapCurvatureEquality
open D5.S3.Quantum.Divergence.NormalOverlapOperational
open D5.S3.Analytic.Convexity.CurvatureHingeRepresentation

namespace D5.S3.Quantum.Divergence.OriginalCentralizerClassification

section Transport
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

private theorem commutant_carrier (ψ : A →ₚ[ℂ] ℂ) :
    GNSMomentFamilies.commutant ψ = (GNSSpectralMoments.commutant ψ).toStarSubalgebra := rfl

private theorem spectralOverlap_coe (ψ : A →ₚ[ℂ] ℂ)
    (C : GNSMomentFamilies.commutant ψ) (hC : IsSelfAdjoint C) (t : ℝ) :
    (GNSOverlapRigidity.spectralOverlap C t).val =
      ContinuousCutoffCentralizer.overlap C.val t := by
  exact (GNSMomentFamilies.commutant ψ).subtype.map_cfc
    (fun x : ℝ => min x (t * (1 - x))) C (by fun_prop) (by fun_prop)
    hC (hC.map _)

private theorem vectorFunctional_mass (ψ : A →ₚ[ℂ] ℂ)
    (T : GNSMomentFamilies.commutant ψ) :
    (vectorFunctional ψ T).re =
      ContinuousCutoffCentralizer.vectorValue (cyclicVector ψ) T.val := by
  change (coefficient ψ T.val 1).re = _
  simp [coefficient, ContinuousCutoffCentralizer.vectorValue]

private theorem pairCoordinate_coe_eq (ρ σ : StrongDual ℂ A)
    (hρ : Positive ρ) (hσ : Positive σ)
    (C : (pairFunctional ρ σ hρ hσ).GNS →L[ℂ] (pairFunctional ρ σ hρ hσ).GNS)
    (hc : ∀ a, Commute C ((pairFunctional ρ σ hρ hσ).gnsStarAlgHom a))
    (hCr : coefficient (pairFunctional ρ σ hρ hσ) C = ρ.toLinearMap) :
    (pairCoordinate ρ σ hρ hσ).val = C := by
  let ψ := pairFunctional ρ σ hρ hσ
  apply coefficient_injective ψ _ C
  · apply (GNSSpectralMoments.mem_commutant ψ _).mp
    change _ ∈ (GNSSpectralMoments.commutant ψ).toStarSubalgebra
    rw [← commutant_carrier]
    exact (pairCoordinate ρ σ hρ hσ).property
  · exact hc
  · exact (congrArg ContinuousLinearMap.toLinearMap
      (pairCoordinate_coefficient ρ σ hρ hσ)).trans hCr.symm

private theorem spectral_feasible (ψ : A →ₚ[ℂ] ℂ)
    (C : (ψ).GNS →L[ℂ] (ψ).GNS) (hC0 : 0 ≤ C) (hC1 : C ≤ 1)
    (hc : ∀ a, Commute C ((ψ).gnsStarAlgHom a)) (t : ℝ) (ht : 0 < t) :
    ContinuousCutoffCentralizer.Feasible (GNSSpectralMoments.commutant ψ)
      C (ContinuousCutoffCentralizer.overlap C t) t := by
  have hs := IsSelfAdjoint.of_nonneg hC0
  refine ⟨(GNSSpectralMoments.mem_commutant ψ _).mpr (fun a => (hc a).cfc_real _),
    ?_, ?_, ?_⟩
  · apply cfc_nonneg
    intro x hx
    exact le_min (spectrum_nonneg_of_nonneg hC0 hx)
      (mul_nonneg ht.le (sub_nonneg.mpr ((CFC.le_one_iff C hs).mp hC1 x hx)))
  · change cfc _ C ≤ C
    conv_rhs => rw [← cfc_id' ℝ C hs]
    exact (cfc_le_iff _ _ C (by fun_prop) continuousOn_id hs).mpr
      (fun _ _ => min_le_left _ _)
  · have he : cfc (fun x : ℝ => t * (1 - x)) C = t • (1 - C) := by
      rw [cfc_const_mul t (fun x : ℝ => 1 - x) C (by fun_prop),
        cfc_sub (fun _ : ℝ => 1) (fun x : ℝ => x) C continuousOn_const continuousOn_id,
        cfc_const_one ℝ C hs, cfc_id' ℝ C hs]
    rw [← he]
    exact (cfc_le_iff _ _ C (by fun_prop) (by fun_prop) hs).mpr
      (fun _ _ => min_le_right _ _)

set_option maxHeartbeats 1200000 in
-- Ambient/subtype CFC transport elaborates the actual dependent GNS carriers.
private theorem ambient_optimal_of_spectral_mass
    (ρ σ : StrongDual ℂ A) (hρ : Positive ρ) (hσ : Positive σ)
    (C : (pairFunctional ρ σ hρ hσ).GNS →L[ℂ] (pairFunctional ρ σ hρ hσ).GNS)
    (hC0 : 0 ≤ C) (hC1 : C ≤ 1)
    (hc : ∀ a, Commute C ((pairFunctional ρ σ hρ hσ).gnsStarAlgHom a))
    (hCr : coefficient (pairFunctional ρ σ hρ hσ) C = ρ.toLinearMap)
    (hCs : coefficient (pairFunctional ρ σ hρ hσ) (1 - C) = σ.toLinearMap)
    (v : ℝ → ℝ)
    (hmax : ∀ t : ℝ, 0 < t → ∀ η : StrongDual ℂ A,
      Positive η → Below η ρ → Below η (t • σ) → (η 1).re ≤ v t)
    (hmass : ∀ t : ℝ, 0 < t →
      (vectorFunctional (pairFunctional ρ σ hρ hσ)
        (GNSOverlapRigidity.spectralOverlap (pairCoordinate ρ σ hρ hσ) t)).re = v t) :
    ContinuousCutoffCentralizer.AllOverlapOptimal
      (GNSSpectralMoments.commutant (pairFunctional ρ σ hρ hσ)) C
      (cyclicVector (pairFunctional ρ σ hρ hσ)) := by
  let ψ := pairFunctional ρ σ hρ hσ
  let Cn := pairCoordinate ρ σ hρ hσ
  have hCe : Cn.val = C := pairCoordinate_coe_eq ρ σ hρ hσ C hc hCr
  have hCn : 0 ≤ Cn := by change 0 ≤ Cn.val; rwa [hCe]
  have hKs : coefficientMap ψ (1 - Cn) = σ := by
    apply ContinuousLinearMap.coe_injective
    change coefficient ψ (1 - Cn.val) = σ.toLinearMap
    rw [hCe, hCs]
  intro t ht
  refine ⟨spectral_feasible ψ C hC0 hC1 hc t ht, ?_⟩
  intro X hX
  let Xn : GNSMomentFamilies.commutant ψ := ⟨X, by
    rw [commutant_carrier]
    exact hX.1⟩
  have hXn : 0 ≤ Xn := hX.2.1
  have hXC : Xn ≤ Cn := by
    change X ≤ Cn.val
    rw [hCe]
    exact hX.2.2.1
  have hXs : Xn ≤ (t : ℂ) • (1 - Cn) := by
    change X ≤ (t : ℂ) • (1 - Cn.val)
    simpa only [hCe, Complex.coe_smul] using hX.2.2.2
  have hηr : Below (coefficientMap ψ Xn) ρ := by
    have hb := (coefficientMap_order ψ Xn Cn).mpr hXC
    have he : coefficientMap ψ Cn = ρ := pairCoordinate_coefficient ρ σ hρ hσ
    intro a ha
    exact (hb a ha).trans_eq (congrArg (fun η : StrongDual ℂ A => η a) he)
  have hηs : Below (coefficientMap ψ Xn) (t • σ) := by
    have hb := (coefficientMap_order ψ Xn ((t : ℂ) • (1 - Cn))).mpr hXs
    have he : coefficientMap ψ ((t : ℂ) • (1 - Cn)) = t • σ := by
      rw [map_smul, hKs, Complex.coe_smul]
    intro a ha
    exact (hb a ha).trans_eq (congrArg (fun η : StrongDual ℂ A => η a) he)
  have hb := hmax t ht (coefficientMap ψ Xn)
    ((coefficientMap_nonneg ψ Xn).mpr hXn) hηr hηs
  have hG : ContinuousCutoffCentralizer.vectorValue (cyclicVector ψ)
      (ContinuousCutoffCentralizer.overlap C t) = v t := by
    have he := hmass t ht
    rw [vectorFunctional_mass, spectralOverlap_coe ψ Cn hCn.isSelfAdjoint t, hCe] at he
    exact he
  rw [hG]
  change (vectorFunctional ψ Xn).re ≤ v t at hb
  rw [vectorFunctional_mass ψ Xn] at hb
  exact hb

end Transport

private abbrev concreteCStarAlgebra
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (M : VonNeumannAlgebra H) : CStarAlgebra M.toStarSubalgebra := inferInstance
attribute [local instance] concreteCStarAlgebra

private abbrev concreteNonUnitalCStarAlgebra
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (M : VonNeumannAlgebra H) : NonUnitalCStarAlgebra M.toStarSubalgebra := inferInstance

attribute [local instance] concreteNonUnitalCStarAlgebra

private abbrev concreteStarOrderedRing
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (M : VonNeumannAlgebra H) : StarOrderedRing M.toStarSubalgebra := inferInstance

attribute [local instance] concreteStarOrderedRing

private abbrev concreteTopology
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (M : VonNeumannAlgebra H) : TopologicalSpace M.toStarSubalgebra := inferInstance

attribute [local instance] concreteTopology

private abbrev concreteAddCommMonoid
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (M : VonNeumannAlgebra H) : AddCommMonoid M.toStarSubalgebra := inferInstance

attribute [local instance] concreteAddCommMonoid

private abbrev concreteModule
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (M : VonNeumannAlgebra H) : Module ℂ M.toStarSubalgebra := inferInstance

attribute [local instance] concreteModule

private abbrev Op {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] (ψ : A →ₚ[ℂ] ℂ) := ψ.GNS →L[ℂ] ψ.GNS

private abbrev nonnegative {A : Type*} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] (ψ : A →ₚ[ℂ] ℂ) (C : Op ψ) : Prop := 0 ≤ C

private abbrev atMostOne {A : Type*} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] (ψ : A →ₚ[ℂ] ℂ) (C : Op ψ) : Prop := C ≤ 1

private abbrev commutesOriginal {A : Type*} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] (ψ : A →ₚ[ℂ] ℂ) (C : Op ψ) : Prop :=
  ∀ a, Commute C (ψ.gnsStarAlgHom a)

private abbrev complement {A : Type*} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] (ψ : A →ₚ[ℂ] ℂ) (C : Op ψ) : Op ψ := 1 - C

private abbrev compressedCentralizer {A : Type*} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] (ψ : A →ₚ[ℂ] ℂ) (C : Op ψ) : Prop :=
  ContinuousCutoffCentralizer.CompressedCentralizes
    (GNSSpectralMoments.commutant ψ) C (cyclicVector ψ)

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (M : VonNeumannAlgebra H) (ρ σ : StrongDual ℂ M.toStarSubalgebra)
    (hρ : Positive ρ) (hσ : Positive σ)
    (hρs : IsCoefficientSeries M ρ) (hσs : IsCoefficientSeries M σ)

local notation "ψ" => pairFunctional ρ σ hρ hσ
include hρ hσ hρs hσs

set_option maxHeartbeats 3000000 in
-- The full spectral-moment theorem retains its actual commutant and whole-L1 carriers.
private theorem compatibility_implies_centralizes
    (C : Op ψ) (hC0 : nonnegative ψ C) (hC1 : atMostOne ψ C)
    (hc : commutesOriginal ψ C)
    (hCr : coefficient ψ C = ρ.toLinearMap)
    (hCs : coefficient ψ (complement ψ C) = σ.toLinearMap)
    (hK : FiniteCompatibility M ρ σ univ) :
    compressedCentralizer ψ C := by
  obtain ⟨F, hF⟩ :=
    (finite_compatibility_iff_simultaneous M ρ σ hρ hσ hρs hσs univ).mp hK
  have hopt (t : ℝ) (ht : 0 < t) :
      (overlap F t 1).re = overlapValue M ρ σ t := hF ⟨t, ht⟩ (mem_univ _)
  obtain ⟨Φ, hfirst, hcoeff, hover, hmass, Γ, hΓ⟩ :=
    GNSOverlapRigidity.spectral_moments_of_all_overlap_optima M ρ σ hρ hσ hρs hσs F hopt
  apply (ContinuousCutoffCentralizer.all_overlap_optimal_iff_compressed_centralizes
    (GNSSpectralMoments.commutant ψ) ((GNSSpectralMoments.mem_commutant ψ C).mpr hc)
      hC0 hC1 (cyclicVector ψ)).mp
  exact ambient_optimal_of_spectral_mass ρ σ hρ hσ C hC0 hC1 hc hCr hCs
    (overlapValue M ρ σ)
    (fun t ht => (value_attained M ρ σ hρ hσ hρs hσs t ht).choose_spec.2) hmass

private theorem centralizes_implies_compatibility
    (C : Op ψ) (hC0 : nonnegative ψ C) (hC1 : atMostOne ψ C)
    (hc : commutesOriginal ψ C)
    (hCr : coefficient ψ C = ρ.toLinearMap)
    (hCs : coefficient ψ (complement ψ C) = σ.toLinearMap)
    (hcentral : compressedCentralizer ψ C)
    (K : Set {t : ℝ // 0 < t}) : FiniteCompatibility M ρ σ K := by
  have hopt := SpectralCentralizerEquality.spectral_overlap_optimal
    M ρ σ hρ hσ hρs hσs C hC0 hC1 hc hCr hCs hcentral
  exact (finite_compatibility_iff_simultaneous M ρ σ hρ hσ hρs hσs K).mpr
    ⟨GNSSpectralMoments.spectralFamily ρ σ ψ C hC0 hC1 hc hCr hCs,
      fun t _ => hopt t t.property⟩

/-- Full actual curvature support and a real-finite literal original maximal
value characterize equality by centralization on the actual interior corner. -/
theorem full_support_finite_iff
    (C : Op ψ) (hC0 : nonnegative ψ C) (hC1 : atMostOne ψ C)
    (hc : commutesOriginal ψ C)
    (hCr : coefficient ψ C = ρ.toLinearMap)
    (hCs : coefficient ψ (complement ψ C) = σ.toLinearMap)
    {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ioi 0) f)
    (hsupport : (curvature hf).support = univ)
    (hfinite : ∃ c : ℝ, maximalValue.{u} M ρ σ hf = (c : EReal)) :
    maximalValue.{u} M ρ σ hf = originalHockeyValue.{u} M ρ σ hf ↔
      compressedCentralizer ψ C := by
  rw [original_operational_equality_iff_finite_compatibility.{u}
    M ρ σ hρ hσ hρs hσs hf hfinite, hsupport]
  exact ⟨compatibility_implies_centralizes M ρ σ hρ hσ hρs hσs C hC0 hC1 hc hCr hCs,
    fun h => centralizes_implies_compatibility M ρ σ hρ hσ hρs hσs
      C hC0 hC1 hc hCr hCs h univ⟩

private theorem equality_iff_top_or_compatibility
    {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ioi 0) f) :
    maximalValue.{u} M ρ σ hf = originalHockeyValue.{u} M ρ σ hf ↔
      originalHockeyValue.{u} M ρ σ hf = ⊤ ∨
        FiniteCompatibility M ρ σ (curvature hf).support := by
  classical
  have hnotbot : maximalValue.{u} M ρ σ hf ≠ ⊥ := by
    obtain ⟨_, _, hbot, _⟩ := standard_original_reverse_test_extended_attainment.{u}
      M ρ σ hρ hσ hρs hσs hf
    simpa only [maximalValue] using hbot
  have hformula := originalHockeyValue_eq_overlap.{u} M ρ σ hρ hσ hρs hσs hf
  constructor
  · intro heq
    by_cases htop : originalHockeyValue.{u} M ρ σ hf = ⊤
    · exact Or.inl htop
    · have hnotop : maximalValue.{u} M ρ σ hf ≠ ⊤ :=
        fun h => htop (heq.symm.trans h)
      have hfinite : ∃ c : ℝ, maximalValue.{u} M ρ σ hf = (c : EReal) :=
        ⟨_, (EReal.coe_toReal hnotop hnotbot).symm⟩
      exact Or.inr ((original_operational_equality_iff_finite_compatibility.{u}
        M ρ σ hρ hσ hρs hσs hf hfinite).mp heq)
  · rintro (htop | hK)
    · have hmax : maximalValue.{u} M ρ σ hf = ⊤ := by
        by_contra hnotop
        have hfinite : ∃ c : ℝ, maximalValue.{u} M ρ σ hf = (c : EReal) :=
          ⟨_, (EReal.coe_toReal hnotop hnotbot).symm⟩
        obtain ⟨c, hc⟩ := hockey_real_of_maximal_real.{u}
          M ρ σ hρ hσ hρs hσs hf hfinite
        exact (EReal.coe_ne_top c) (hc.symm.trans (hformula.symm.trans htop))
      exact hmax.trans htop.symm
    · exact (finite_compatibility_implies_original_equality.{u}
        M ρ σ hρ hσ hρs hσs hf hK).1.trans hformula.symm

/-- Unrestricted extended-value equality has a separate top branch. No
centralization is inferred from equality of two infinite values. -/
theorem full_support_iff_top_or_centralizes
    (C : Op ψ) (hC0 : nonnegative ψ C) (hC1 : atMostOne ψ C)
    (hc : commutesOriginal ψ C)
    (hCr : coefficient ψ C = ρ.toLinearMap)
    (hCs : coefficient ψ (complement ψ C) = σ.toLinearMap)
    {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ioi 0) f)
    (hsupport : (curvature hf).support = univ) :
    maximalValue.{u} M ρ σ hf = originalHockeyValue.{u} M ρ σ hf ↔
      originalHockeyValue.{u} M ρ σ hf = ⊤ ∨
        compressedCentralizer ψ C := by
  rw [equality_iff_top_or_compatibility.{u} M ρ σ hρ hσ hρs hσs hf, hsupport]
  exact or_congr Iff.rfl
    ⟨compatibility_implies_centralizes M ρ σ hρ hσ hρs hσs C hC0 hC1 hc hCr hCs,
      fun h => centralizes_implies_compatibility M ρ σ hρ hσ hρs hσs
        C hC0 hC1 hc hCr hCs h univ⟩

/-- The literal nonaffine all-Hilbert operator-convex hypothesis derives
scalar convexity and full actual curvature support, with no added premise. -/
theorem operatorConvex_finite_iff
    (C : Op ψ) (hC0 : nonnegative ψ C) (hC1 : atMostOne ψ C)
    (hc : commutesOriginal ψ C)
    (hCr : coefficient ψ C = ρ.toLinearMap)
    (hCs : coefficient ψ (complement ψ C) = σ.toLinearMap)
    {f : ℝ → ℝ}
    (hconv : LownerHeinzTheorem.OperatorConvexOnAll.{0} (Ioi 0) f)
    (nonaffine : ¬ ∃ α β : ℝ, ∀ x ∈ Ioi 0, f x = α * x + β)
    (hfinite : ∃ c : ℝ, maximalValue.{u} M ρ σ
      (Lieb.OperatorConvexCurvature.convexOn_of_operatorConvexOnAll (f := f) (@hconv)) = (c : EReal)) :
    maximalValue.{u} M ρ σ
        (Lieb.OperatorConvexCurvature.convexOn_of_operatorConvexOnAll (f := f) (@hconv)) =
      originalHockeyValue.{u} M ρ σ
        (Lieb.OperatorConvexCurvature.convexOn_of_operatorConvexOnAll (f := f) (@hconv)) ↔
      compressedCentralizer ψ C :=
  full_support_finite_iff.{u} M ρ σ hρ hσ hρs hσs C hC0 hC1 hc hCr hCs _
    (Lieb.OperatorConvexCurvature.operatorConvex_curvature_full_support (f := f) (@hconv) nonaffine) hfinite

/-- Literal original operator-convex classification, including both the
real-finite structural case and the essential infinite hockey case. -/
theorem operatorConvex_iff_top_or_centralizes
    (C : Op ψ) (hC0 : nonnegative ψ C) (hC1 : atMostOne ψ C)
    (hc : commutesOriginal ψ C)
    (hCr : coefficient ψ C = ρ.toLinearMap)
    (hCs : coefficient ψ (complement ψ C) = σ.toLinearMap)
    {f : ℝ → ℝ}
    (hconv : LownerHeinzTheorem.OperatorConvexOnAll.{0} (Ioi 0) f)
    (nonaffine : ¬ ∃ α β : ℝ, ∀ x ∈ Ioi 0, f x = α * x + β) :
    maximalValue.{u} M ρ σ
        (Lieb.OperatorConvexCurvature.convexOn_of_operatorConvexOnAll (f := f) (@hconv)) =
      originalHockeyValue.{u} M ρ σ
        (Lieb.OperatorConvexCurvature.convexOn_of_operatorConvexOnAll (f := f) (@hconv)) ↔
      originalHockeyValue.{u} M ρ σ
        (Lieb.OperatorConvexCurvature.convexOn_of_operatorConvexOnAll (f := f) (@hconv)) = ⊤ ∨
      compressedCentralizer ψ C :=
  full_support_iff_top_or_centralizes.{u} M ρ σ hρ hσ hρs hσs C hC0 hC1 hc hCr hCs _
    (Lieb.OperatorConvexCurvature.operatorConvex_curvature_full_support (f := f) (@hconv) nonaffine)

#print axioms full_support_finite_iff
#print axioms full_support_iff_top_or_centralizes
#print axioms operatorConvex_finite_iff
#print axioms operatorConvex_iff_top_or_centralizes

end D5.S3.Quantum.Divergence.OriginalCentralizerClassification
