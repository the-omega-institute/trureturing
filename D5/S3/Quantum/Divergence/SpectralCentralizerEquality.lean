/- GID: D5/S3/Quantum/Divergence/SpectralCentralizerEquality
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/SpectralCentralizerEquality
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: Compressed GNS centralization suffices for original operational equality. -/

import D5.S3.Quantum.Analysis.GNSSpectralMoments
import D5.S3.Quantum.Analysis.ContinuousCutoffCentralizer
import D5.S3.Quantum.Divergence.NormalOverlapOperational

/-! One genuine spectral family for the fixed original pair is optimal at
every positive threshold. The original standard-predual whole-complex-L1
source class is retained. Only the sufficient direction is asserted. -/

noncomputable section
universe u v
open Set MeasureTheory
open scoped ComplexOrder InnerProductSpace Topology
open D5.S3.Quantum.Analysis
open GNSOrderCoordinates NormalMomentFamily
open D5.S3.Quantum.Analysis.NormalFunctionals
open D5.S3.Quantum.Analysis.ConcreteCoefficientSeries
open D5.S3.Quantum.Divergence.NormalOverlapCompatibility
open D5.S3.Quantum.Divergence.GeneralConvexReverseTestAttainment
open D5.S3.Quantum.Divergence.NormalOverlapCurvatureEquality
open D5.S3.Quantum.Divergence.NormalOverlapOperational

namespace D5.S3.Quantum.Divergence.SpectralCentralizerEquality

private theorem coefficient_smul {A : Type*} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] (ψ : A →ₚ[ℂ] ℂ) (T : (ψ).GNS →L[ℂ] (ψ).GNS) (t : ℝ) :
    coefficient ψ (t • T) = t • coefficient ψ T := by
  ext a
  simp [coefficient, Physicslib4.GNS.coeffFunctional_apply,
    smul_apply]

private theorem coefficient_mass {A : Type*} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] (ψ : A →ₚ[ℂ] ℂ) (T : (ψ).GNS →L[ℂ] (ψ).GNS) :
    (coefficient ψ T 1).re = ContinuousCutoffCentralizer.vectorValue (cyclicVector ψ) T := by
  simp [coefficient, ContinuousCutoffCentralizer.vectorValue]

private abbrev concreteCStarAlgebra
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (M : VonNeumannAlgebra H) : CStarAlgebra M.toStarSubalgebra := inferInstance

attribute [instance] concreteCStarAlgebra

private abbrev concreteNonUnitalCStarAlgebra
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (M : VonNeumannAlgebra H) : NonUnitalCStarAlgebra M.toStarSubalgebra := inferInstance

attribute [instance] concreteNonUnitalCStarAlgebra

private abbrev concreteStarOrderedRing
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (M : VonNeumannAlgebra H) : StarOrderedRing M.toStarSubalgebra := inferInstance

attribute [instance] concreteStarOrderedRing

private abbrev concreteTopology
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (M : VonNeumannAlgebra H) : TopologicalSpace M.toStarSubalgebra := inferInstance

attribute [instance] concreteTopology

private abbrev concreteAddCommMonoid
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (M : VonNeumannAlgebra H) : AddCommMonoid M.toStarSubalgebra := inferInstance

attribute [instance] concreteAddCommMonoid

private abbrev concreteModule
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (M : VonNeumannAlgebra H) : Module ℂ M.toStarSubalgebra := inferInstance

attribute [instance] concreteModule

private abbrev originalFunctional {A : Type*} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] (ρ σ : StrongDual ℂ A)
    (hρ : Positive ρ) (hσ : Positive σ) : A →ₚ[ℂ] ℂ :=
  positiveOfDual (ρ + σ) (fun a ha => add_nonneg (hρ a ha) (hσ a ha))

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

local notation "ψ" => originalFunctional ρ σ hρ hσ

/-- Every actual feasible dual overlap is bounded by the spectral overlap.
The competing dual functional is given its own actual dominated GNS coordinate. -/
private theorem spectral_bounds_feasible
    (C : Op ψ) (hC0 : nonnegative ψ C) (hC1 : atMostOne ψ C)
    (hc : commutesOriginal ψ C)
    (hCr : coefficient ψ C = ρ.toLinearMap)
    (hCs : coefficient ψ (complement ψ C) = σ.toLinearMap)
    (hcentral : compressedCentralizer ψ C)
    (t : ℝ) (ht : 0 < t) (η : StrongDual ℂ M.toStarSubalgebra)
    (hη : Positive η) (hηr : Below η ρ) (hηs : Below η (t • σ)) :
    (η 1).re ≤ (overlap (GNSSpectralMoments.spectralFamily ρ σ ψ C hC0 hC1 hc hCr hCs) t 1).re := by
  have hd : Dominated (positiveOfDual η hη) ψ := by
    intro a ha
    exact (hηr a ha).trans (le_add_of_nonneg_right (hσ a ha))
  obtain ⟨X, hX, _⟩ := existsUnique_coordinate (positiveOfDual η hη) ψ hd
  have hXc := hX.2.2.1
  have hXe : coefficient ψ X = η.toLinearMap := hX.2.2.2
  have hXC : X ≤ C := (coefficient_order_iff ψ X C hXc hc).mp (by
    intro a ha
    simpa only [hXe, hCr, ContinuousLinearMap.coe_coe] using hηr a ha)
  have hcomp : ∀ a, Commute (1 - C) ((ψ).gnsStarAlgHom a) :=
    fun a => (Commute.one_left _).sub_left (hc a)
  have hscaled : ∀ a, Commute (t • (1 - C)) ((ψ).gnsStarAlgHom a) :=
    fun a => (hcomp a).smul_left t
  have hXs : X ≤ t • (1 - C) :=
    (coefficient_order_iff ψ X _ hXc hscaled).mp (by
      intro a ha
      simpa only [hXe, coefficient_smul, hCs, LinearMap.smul_apply,
        ContinuousLinearMap.coe_coe, smul_apply] using hηs a ha)
  have hopt := ContinuousCutoffCentralizer.compressed_centralization_implies_optimal
    (GNSSpectralMoments.commutant ψ) ((GNSSpectralMoments.mem_commutant ψ C).mpr hc)
      hC0 hC1 (cyclicVector ψ) hcentral t ht
  have hb := hopt.2 X ⟨(GNSSpectralMoments.mem_commutant ψ X).mpr hXc, hX.1, hXC, hXs⟩
  have hm := GNSSpectralMoments.spectralFamily_moment ρ σ ψ C hC0 hC1 hc hCr hCs
    (fun x : ℝ => min x (t * (1 - x))) (by fun_prop)
  change (linearMap _ (overlapFunction t)).toLinearMap = _ at hm
  have hm1 := congrArg (fun f : M.toStarSubalgebra →ₗ[ℂ] ℂ => (f 1).re) hm
  rw [coefficient_mass] at hm1
  change (overlap _ t 1).re = ContinuousCutoffCentralizer.vectorValue _ _ at hm1
  rw [hm1]
  simpa only [← coefficient_mass, hXe, ContinuousLinearMap.coe_coe,
    ContinuousCutoffCentralizer.overlap] using hb

variable (hρs : IsCoefficientSeries M ρ) (hσs : IsCoefficientSeries M σ)

include hρs hσs

/-- The same constructed spectral family attains every original overlap maximum. -/
theorem spectral_overlap_optimal
    (C : Op ψ) (hC0 : nonnegative ψ C) (hC1 : atMostOne ψ C)
    (hc : commutesOriginal ψ C)
    (hCr : coefficient ψ C = ρ.toLinearMap)
    (hCs : coefficient ψ (complement ψ C) = σ.toLinearMap)
    (hcentral : compressedCentralizer ψ C) :
    ∀ t : ℝ, 0 < t →
      (overlap (GNSSpectralMoments.spectralFamily ρ σ ψ C hC0 hC1 hc hCr hCs) t 1).re =
        overlapValue M ρ σ t := by
  intro t ht
  let F := GNSSpectralMoments.spectralFamily ρ σ ψ C hC0 hC1 hc hCr hCs
  obtain ⟨F', hm, hbound⟩ := value_attained M ρ σ hρ hσ hρs hσs t ht
  obtain ⟨hp, hr, hs⟩ := overlap_feasible F t ht.le
  apply le_antisymm (hbound _ hp hr hs)
  rw [← hm]
  obtain ⟨hp', hr', hs'⟩ := overlap_feasible F' t ht.le
  exact spectral_bounds_feasible M ρ σ hρ hσ C hC0 hC1 hc hCr hCs hcentral
    t ht (overlap F' t) hp' hr' hs'

set_option maxHeartbeats 1200000 in
/-- Compressed centralization suffices for the literal original equality for
every convex generator, allowing extended-valued original divergence. The displayed
spectral family has an actual whole-complex-L1 realization with series outputs. -/
theorem spectral_centralizer_equality
    (C : Op ψ) (hC0 : nonnegative ψ C) (hC1 : atMostOne ψ C)
    (hc : commutesOriginal ψ C)
    (hCr : coefficient ψ C = ρ.toLinearMap)
    (hCs : coefficient ψ (complement ψ C) = σ.toLinearMap)
    (hcentral : compressedCentralizer ψ C)
    {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ioi 0) f) :
    let F := GNSSpectralMoments.spectralFamily ρ σ ψ C hC0 hC1 hc hCr hCs
    (∀ t : ℝ, 0 < t → (overlap F t 1).re = overlapValue M ρ σ t) ∧
    maximalValue.{u} M ρ σ hf = originalHockeyValue.{u} M ρ σ hf ∧
    ∃ Γ : (Interval →₁[scalarMeasure F] ℂ) →L[ℂ] StrongDual ℂ M.toStarSubalgebra,
      (∀ g : C(Interval, ℂ), Γ (ContinuousMap.toLp 1 (scalarMeasure F) ℂ g) = linearMap F g) ∧
      (∀ h, IsOrderNormal (Γ h)) ∧
      (∀ h, (∀ᵐ x ∂scalarMeasure F, 0 ≤ h x) → Positive (Γ h)) ∧
      (∀ h, Γ h 1 = ∫ x, h x ∂scalarMeasure F) ∧ ‖Γ‖ ≤ 1 ∧
      Γ (ContinuousMap.toLp 1 (scalarMeasure F) ℂ posterior) = ρ ∧
      Γ (ContinuousMap.toLp 1 (scalarMeasure F) ℂ (1 - posterior)) = σ ∧
      (∀ h, IsCoefficientSeries M (Γ h)) := by
  let F := GNSSpectralMoments.spectralFamily ρ σ ψ C hC0 hC1 hc hCr hCs
  have hopt := spectral_overlap_optimal M ρ σ hρ hσ hρs hσs C hC0 hC1 hc hCr hCs hcentral
  have hcompat : FiniteCompatibility M ρ σ
      (D5.S3.Analytic.Convexity.CurvatureHingeRepresentation.curvature hf).support :=
    (finite_compatibility_iff_simultaneous M ρ σ hρ hσ hρs hσs _).mpr
      ⟨F, fun t _ => hopt t t.property⟩
  have heq : maximalValue.{u} M ρ σ hf = originalHockeyValue.{u} M ρ σ hf := by
    rw [NormalOverlapOperational.originalHockeyValue_eq_overlap.{u}
      M ρ σ hρ hσ hρs hσs hf]
    exact (NormalOverlapCurvatureEquality.finite_compatibility_implies_original_equality.{u}
      M ρ σ hρ hσ hρs hσs hf hcompat).1
  obtain ⟨Γ, hagree, hn, hp, hm, hb, hl, hr, hΓE, _⟩ :=
    standard_posterior_realization M ρ σ hρ hσ hρs hσs F
  exact ⟨hopt, heq, Γ, hagree, hn, hp, hm, hb, hl, hr,
    fun h => (mem_coefficientSpace_iff_series M _).mp (hΓE h)⟩

#print axioms spectral_overlap_optimal
#print axioms spectral_centralizer_equality

end D5.S3.Quantum.Divergence.SpectralCentralizerEquality
