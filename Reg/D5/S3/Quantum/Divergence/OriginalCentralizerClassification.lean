import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Quantum.Divergence.OriginalCentralizerClassification

/-! Exact original-source reconstruction for the four classifiers.
The source laws retain all input hypotheses and vary the two propositions
observed by each biconditional. Four-slot variation, sensitivity and native
source-binding evidence remain unfinished under issue 29713. These bridges
are not declared-validated registrations. -/

noncomputable section
universe u v
open Set MeasureTheory LeanInformationAudit
open scoped ComplexOrder InnerProductSpace Topology ENNReal
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Analysis
open GNSOrderCoordinates GNSMomentFamilies NormalMomentFamily ConcreteCoefficientSeries
open _root_.D5.S3.Quantum.Divergence.GeneralConvexReverseTestAttainment
open _root_.D5.S3.Quantum.Divergence.NormalOverlapCompatibility
open _root_.D5.S3.Quantum.Divergence.NormalOverlapCurvatureEquality
open _root_.D5.S3.Quantum.Divergence.NormalOverlapOperational
open _root_.D5.S3.Analytic.Convexity.CurvatureHingeRepresentation
open _root_.D5.S3.Quantum.Divergence.OriginalCentralizerClassification

namespace Reg.D5.S3.Quantum.Divergence.OriginalCentralizerClassification

abbrev signature : Signature where
  Params := Unit
  State _ := Prop
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ p q => p ↔ q) (fun e => nomatch e)

def full_support_finite_iff_arena : Arena where
  signature := signature
  Law R := ∀ {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (M : VonNeumannAlgebra H) (ρ σ : StrongDual ℂ M.toStarSubalgebra)
    (hρ : Positive ρ) (hσ : Positive σ)
    (hρs : IsCoefficientSeries M ρ) (hσs : IsCoefficientSeries M σ)
    (C : (pairFunctional ρ σ hρ hσ).GNS →L[ℂ] (pairFunctional ρ σ hρ hσ).GNS) (hC0 : 0 ≤ C) (hC1 :
      C ≤ 1)
    (hc : ∀ a, Commute C ((pairFunctional ρ σ hρ hσ).gnsStarAlgHom a))
    (hCr : coefficient (pairFunctional ρ σ hρ hσ) C = ρ.toLinearMap)
    (hCs : coefficient (pairFunctional ρ σ hρ hσ) (1 - C) = σ.toLinearMap)
    {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ioi 0) f)
    (hsupport : (curvature hf).support = univ)
    (hfinite : ∃ c : ℝ, maximalValue.{u} M ρ σ hf = (c : EReal)),
    R.readout () () (maximalValue.{u} M ρ σ hf = originalHockeyValue.{u} M ρ σ hf)
      (ContinuousCutoffCentralizer.CompressedCentralizes
        (GNSSpectralMoments.commutant (pairFunctional ρ σ hρ hσ)) C (cyclicVector (pairFunctional
          ρ σ hρ hσ)))

theorem full_support_finite_iff_source_bridge :
    (type_of% (@full_support_finite_iff.{u,v})) ↔ full_support_finite_iff_arena.{u,v}.Law actual
      := Iff.rfl

theorem full_support_finite_iff_source_law : full_support_finite_iff_arena.{u,v}.Law actual :=
  full_support_finite_iff_source_bridge.mp (@full_support_finite_iff.{u,v})

#print axioms full_support_finite_iff_source_bridge
#print axioms full_support_finite_iff_source_law

def full_support_iff_top_or_centralizes_arena : Arena where
  signature := signature
  Law R := ∀ {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (M : VonNeumannAlgebra H) (ρ σ : StrongDual ℂ M.toStarSubalgebra)
    (hρ : Positive ρ) (hσ : Positive σ)
    (hρs : IsCoefficientSeries M ρ) (hσs : IsCoefficientSeries M σ)
    (C : (pairFunctional ρ σ hρ hσ).GNS →L[ℂ] (pairFunctional ρ σ hρ hσ).GNS) (hC0 : 0 ≤ C) (hC1 :
      C ≤ 1)
    (hc : ∀ a, Commute C ((pairFunctional ρ σ hρ hσ).gnsStarAlgHom a))
    (hCr : coefficient (pairFunctional ρ σ hρ hσ) C = ρ.toLinearMap)
    (hCs : coefficient (pairFunctional ρ σ hρ hσ) (1 - C) = σ.toLinearMap)
    {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ioi 0) f)
    (hsupport : (curvature hf).support = univ),
    R.readout () () (maximalValue.{u} M ρ σ hf = originalHockeyValue.{u} M ρ σ hf)
      (originalHockeyValue.{u} M ρ σ hf = ⊤ ∨
        ContinuousCutoffCentralizer.CompressedCentralizes
          (GNSSpectralMoments.commutant (pairFunctional ρ σ hρ hσ)) C (cyclicVector
            (pairFunctional ρ σ hρ hσ)))

theorem full_support_iff_top_or_centralizes_source_bridge :
    (type_of% (@full_support_iff_top_or_centralizes.{u,v})) ↔
      full_support_iff_top_or_centralizes_arena.{u,v}.Law actual := Iff.rfl

theorem full_support_iff_top_or_centralizes_source_law :
      full_support_iff_top_or_centralizes_arena.{u,v}.Law actual :=
  full_support_iff_top_or_centralizes_source_bridge.mp (@full_support_iff_top_or_centralizes.{u,v})

#print axioms full_support_iff_top_or_centralizes_source_bridge
#print axioms full_support_iff_top_or_centralizes_source_law

def operatorConvex_finite_iff_arena : Arena where
  signature := signature
  Law R := ∀ {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (M : VonNeumannAlgebra H) (ρ σ : StrongDual ℂ M.toStarSubalgebra)
    (hρ : Positive ρ) (hσ : Positive σ)
    (hρs : IsCoefficientSeries M ρ) (hσs : IsCoefficientSeries M σ)
    (C : (pairFunctional ρ σ hρ hσ).GNS →L[ℂ] (pairFunctional ρ σ hρ hσ).GNS) (hC0 : 0 ≤ C) (hC1 :
      C ≤ 1)
    (hc : ∀ a, Commute C ((pairFunctional ρ σ hρ hσ).gnsStarAlgHom a))
    (hCr : coefficient (pairFunctional ρ σ hρ hσ) C = ρ.toLinearMap)
    (hCs : coefficient (pairFunctional ρ σ hρ hσ) (1 - C) = σ.toLinearMap)
    {f : ℝ → ℝ}
    (hconv : _root_.LownerHeinzTheorem.OperatorConvexOnAll.{0} (Ioi 0) f)
    (nonaffine : ¬ ∃ α β : ℝ, ∀ x ∈ Ioi 0, f x = α * x + β)
    (hfinite : ∃ c : ℝ, maximalValue.{u} M ρ σ
      (_root_.D5.S3.Quantum.Lieb.OperatorConvexCurvature.convexOn_of_operatorConvexOnAll (f := f)
        (@hconv)) = (c : EReal)),
    R.readout () () (maximalValue.{u} M ρ σ
        (_root_.D5.S3.Quantum.Lieb.OperatorConvexCurvature.convexOn_of_operatorConvexOnAll (f :=
          f) (@hconv)) =
      originalHockeyValue.{u} M ρ σ
        (_root_.D5.S3.Quantum.Lieb.OperatorConvexCurvature.convexOn_of_operatorConvexOnAll (f :=
          f) (@hconv)))
      (ContinuousCutoffCentralizer.CompressedCentralizes
        (GNSSpectralMoments.commutant (pairFunctional ρ σ hρ hσ)) C (cyclicVector (pairFunctional
          ρ σ hρ hσ)))

theorem operatorConvex_finite_iff_source_bridge :
    (type_of% (@operatorConvex_finite_iff.{u,v})) ↔ operatorConvex_finite_iff_arena.{u,v}.Law
      actual := Iff.rfl

theorem operatorConvex_finite_iff_source_law : operatorConvex_finite_iff_arena.{u,v}.Law actual :=
  operatorConvex_finite_iff_source_bridge.mp (@operatorConvex_finite_iff.{u,v})

#print axioms operatorConvex_finite_iff_source_bridge
#print axioms operatorConvex_finite_iff_source_law

def operatorConvex_iff_top_or_centralizes_arena : Arena where
  signature := signature
  Law R := ∀ {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (M : VonNeumannAlgebra H) (ρ σ : StrongDual ℂ M.toStarSubalgebra)
    (hρ : Positive ρ) (hσ : Positive σ)
    (hρs : IsCoefficientSeries M ρ) (hσs : IsCoefficientSeries M σ)
    (C : (pairFunctional ρ σ hρ hσ).GNS →L[ℂ] (pairFunctional ρ σ hρ hσ).GNS) (hC0 : 0 ≤ C) (hC1 :
      C ≤ 1)
    (hc : ∀ a, Commute C ((pairFunctional ρ σ hρ hσ).gnsStarAlgHom a))
    (hCr : coefficient (pairFunctional ρ σ hρ hσ) C = ρ.toLinearMap)
    (hCs : coefficient (pairFunctional ρ σ hρ hσ) (1 - C) = σ.toLinearMap)
    {f : ℝ → ℝ}
    (hconv : _root_.LownerHeinzTheorem.OperatorConvexOnAll.{0} (Ioi 0) f)
    (nonaffine : ¬ ∃ α β : ℝ, ∀ x ∈ Ioi 0, f x = α * x + β),
    R.readout () () (maximalValue.{u} M ρ σ
        (_root_.D5.S3.Quantum.Lieb.OperatorConvexCurvature.convexOn_of_operatorConvexOnAll (f :=
          f) (@hconv)) =
      originalHockeyValue.{u} M ρ σ
        (_root_.D5.S3.Quantum.Lieb.OperatorConvexCurvature.convexOn_of_operatorConvexOnAll (f :=
          f) (@hconv)))
      (originalHockeyValue.{u} M ρ σ
        (_root_.D5.S3.Quantum.Lieb.OperatorConvexCurvature.convexOn_of_operatorConvexOnAll (f :=
          f) (@hconv)) = ⊤ ∨
      ContinuousCutoffCentralizer.CompressedCentralizes
        (GNSSpectralMoments.commutant (pairFunctional ρ σ hρ hσ)) C (cyclicVector (pairFunctional
          ρ σ hρ hσ)))

theorem operatorConvex_iff_top_or_centralizes_source_bridge :
    (type_of% (@operatorConvex_iff_top_or_centralizes.{u,v})) ↔
      operatorConvex_iff_top_or_centralizes_arena.{u,v}.Law actual := Iff.rfl

theorem operatorConvex_iff_top_or_centralizes_source_law :
      operatorConvex_iff_top_or_centralizes_arena.{u,v}.Law actual :=
  operatorConvex_iff_top_or_centralizes_source_bridge.mp
      (@operatorConvex_iff_top_or_centralizes.{u,v})

#print axioms operatorConvex_iff_top_or_centralizes_source_bridge
#print axioms operatorConvex_iff_top_or_centralizes_source_law

end Reg.D5.S3.Quantum.Divergence.OriginalCentralizerClassification
