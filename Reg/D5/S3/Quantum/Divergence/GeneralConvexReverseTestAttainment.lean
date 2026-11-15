import Reg.D5.S3.Quantum.Analysis.NormalL1Realization
import D5.S3.Quantum.Divergence.GeneralConvexReverseTestAttainment

/-! The complete independent-universe original attainment statement is retained.
The varied observation is the actual posterior realization's sharp norm bound.
Serialization, source identity bytes and source-selection certification remain
subject to the existing information-escape issue; compilation is not validation. -/

open Set MeasureTheory LeanInformationAudit
open scoped ComplexOrder
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Analytic.Convexity.CurvatureHingeRepresentation
open _root_.D5.S3.Quantum.Analysis.NormalFunctionals
open _root_.D5.S3.Quantum.Analysis.NormalMomentFamily
open _root_.D5.S3.Quantum.Divergence.GeneralConvexReverseTestAttainment

noncomputable section
universe u v
namespace Reg.D5.S3.Quantum.Divergence.GeneralConvexReverseTestAttainment

abbrev signature := Reg.D5.S3.Quantum.Analysis.NormalL1Realization.signature
abbrev actual := Reg.D5.S3.Quantum.Analysis.NormalL1Realization.actual
abbrev rejected := Reg.D5.S3.Quantum.Analysis.NormalL1Realization.rejected

def arena : Arena where
  signature := signature
  Law R := ∀ {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (M : VonNeumannAlgebra H) (ρ σ : StrongDual ℂ M.toStarSubalgebra)
    (hρ : ∀ a, 0 ≤ a → 0 ≤ ρ a) (hσ : ∀ a, 0 ≤ a → 0 ≤ σ a)
    (hn : IsOrderNormal (ρ + σ))
    {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ioi 0) f),
    ∃ F : Family ρ σ,
      familyCost hf F = sInf (attainableCosts.{u} hf ρ σ) ∧
      sInf (attainableCosts.{u} hf ρ σ) ≠ ⊥ ∧
      (ρ = 0 → σ = 0 → sInf (attainableCosts.{u} hf ρ σ) = 0) ∧
      (scalarMeasure F).Regular ∧
      IsFiniteMeasure (liftedMeasure.{u} (scalarMeasure F)) ∧
      (∃ R : NormalL1ReverseTest ρ σ (liftedMeasure.{u} (scalarMeasure F)),
        R.p = (fun x => x.down.val) ∧ R.q = (fun x => 1 - x.down.val) ∧
        closedPerspectiveCost hf (liftedMeasure (scalarMeasure F)) R.p R.q =
          sInf (attainableCosts.{u} hf ρ σ)) ∧
      ∃ Γ : (Interval →₁[scalarMeasure F] ℂ) →L[ℂ] StrongDual ℂ M.toStarSubalgebra,
        (∀ g : C(Interval, ℂ), Γ (ContinuousMap.toLp 1 (scalarMeasure F) ℂ g) = linearMap F g) ∧
        (∀ h, IsOrderNormal (Γ h)) ∧
        (∀ h, (∀ᵐ t ∂scalarMeasure F, 0 ≤ h t) → ∀ a : M.toStarSubalgebra, 0 ≤ a → 0 ≤ Γ h a) ∧
        (∀ h, Γ h 1 = ∫ t, h t ∂scalarMeasure F) ∧ R.readout () () ‖Γ‖ 1 ∧
        Γ (ContinuousMap.toLp 1 (scalarMeasure F) ℂ posterior) = ρ ∧
        Γ (ContinuousMap.toLp 1 (scalarMeasure F) ℂ (1 - posterior)) = σ

private theorem actual_law : arena.{u,v}.Law actual :=
  @original_reverse_test_extended_attainment.{u,v}

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  let M : VonNeumannAlgebra PUnit.{v+1} :=
    { toStarSubalgebra := ⊤
      centralizer_centralizer' := by
        ext x
        constructor
        · intro _; trivial
        · intro _ y _hy; exact Subsingleton.elim _ _ }
  have : IsClosed (M.toStarSubalgebra : Set (PUnit.{v+1} →L[ℂ] PUnit.{v+1})) :=
    _root_.D5.S3.Quantum.Analysis.VonNeumannNormalL1.closedCarrier M
  have hn : IsOrderNormal (A := M.toStarSubalgebra) (0 : StrongDual ℂ M.toStarSubalgebra) :=
    (normalDual (A := M.toStarSubalgebra)).zero_mem
  have hc : ConvexOn ℝ (Ioi 0) (fun _ : ℝ => (0 : ℝ)) :=
    convexOn_const _ (convex_Ioi _)
  obtain ⟨_, _, _, _, _, _, _, Γ, _, _, _, _, hf, _, _⟩ :=
    h M 0 0 (by intro a ha; simp) (by intro a ha; simp)
      (by simpa only [add_zero] using hn) hc
  exact hf

def family : Registration arena.{u,v}
    (type_of% (@original_reverse_test_extended_attainment.{u,v})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (show j = i from @Subsingleton.elim Unit _ j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
    intro h
    have hf : (1 : ℝ) ≤ 0 := Eq.mp (congrFun h 0) le_rfl
    norm_num at hf

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@original_reverse_test_extended_attainment.{u,v}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Divergence.GeneralConvexReverseTestAttainment.attainmentUnit
  realizationName := `Reg.D5.S3.Quantum.Divergence.GeneralConvexReverseTestAttainment.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v}⟩
  objectArena := .source ⟨arena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v} ⟨family.{u,v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]


/-- Complete original L1-element cost-set comparison telescope. -/
theorem cost_set_source_bridge : (type_of% (@attainableCosts_eq_range.{u,v})) ↔
    ∀ {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (M : VonNeumannAlgebra H) (ρ σ : StrongDual ℂ M.toStarSubalgebra)
      (hρ : ∀ a, 0 ≤ a → 0 ≤ ρ a) (hσ : ∀ a, 0 ≤ a → 0 ≤ σ a)
      (hn : IsOrderNormal (ρ + σ)) {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ioi 0) f),
      attainableCosts.{u} hf ρ σ = Set.range (familyCost hf (ρ := ρ) (σ := σ)) := Iff.rfl

/-- The measurable presentation is compared to the actual entire-L1 source class. -/
theorem representative_source_bridge :
    (type_of% (@attainableCosts_eq_representativeCosts.{u,v})) ↔
    ∀ {A : Type v} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
      {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ioi 0) f) (ρ σ : StrongDual ℂ A),
      attainableCosts.{u} hf ρ σ = representativeCosts.{u} hf ρ σ := Iff.rfl

/-- No endpoint or finite-value restriction is inserted into the objective bridge. -/
theorem affine_source_bridge : (type_of% (@familyCost_eq_affine.{v})) ↔
    ∀ {A : Type v} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
      {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ioi 0) f) {ρ σ : StrongDual ℂ A} (F : Family ρ σ),
      familyCost hf F = (affineCost f ρ σ : EReal) +
        (_root_.D5.S3.Analytic.Convexity.PosteriorCurvatureCost.posteriorCurvatureCost
          hf (finiteMeasure F) : EReal) := Iff.rfl


/-- Every nonnegative original L1 input retains the original preparation. -/
theorem positive_input_source_bridge : (type_of% (@representativeCosts_of_positive_L1.{u,v})) ↔
    ∀ {A : Type v} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
      {X : Type u} [MeasurableSpace X] {μ : Measure X} [SigmaFinite μ]
      (Γ : NormalL1Preparation (A := A) μ) {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ioi 0) f)
      (p q : X →₁[μ] ℂ), (∀ᵐ x ∂μ, 0 ≤ p x) → (∀ᵐ x ∂μ, 0 ≤ q x) →
      closedPerspectiveCost hf μ (fun x => (p x).re) (fun x => (q x).re) ∈
        representativeCosts.{u} hf (Γ.toLinearMap p) (Γ.toLinearMap q) := Iff.rfl

/-- The actual scalar Riesz measure is compared with the weighted pushforward. -/
theorem scalar_measure_source_bridge : (type_of% (@posteriorFamily_scalarMeasure.{v,u})) ↔
    ∀ {A : Type v} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
      {ρ σ : StrongDual ℂ A} {X : Type u} [MeasurableSpace X] {μ : Measure X}
      (R : NormalL1ReverseTest ρ σ μ), scalarMeasure (posteriorFamily R) =
        _root_.D5.S3.Quantum.Divergence.PosteriorSourceNormalization.posteriorMeasure μ R.p R.q :=
  Iff.rfl

/-- The literal extended cost identity retains arbitrary source measures. -/
theorem source_cost_source_bridge : (type_of% (@source_cost_eq_familyCost.{v,u})) ↔
    ∀ {A : Type v} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
      {ρ σ : StrongDual ℂ A} {X : Type u} [MeasurableSpace X] {μ : Measure X}
      (R : NormalL1ReverseTest ρ σ μ) {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ioi 0) f),
      closedPerspectiveCost hf μ R.p R.q = familyCost hf (posteriorFamily R) := Iff.rfl

#print axioms family
#print axioms audit

end Reg.D5.S3.Quantum.Divergence.GeneralConvexReverseTestAttainment
