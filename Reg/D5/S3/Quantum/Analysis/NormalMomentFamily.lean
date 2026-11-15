import Reg.D5.S3.Quantum.Analysis.NormalL1Realization
import D5.S3.Quantum.Analysis.NormalMomentFamily

/-! The original full telescope and every compactness, Riesz and whole-L1
conclusion are retained. The varied observation is the sharp norm comparison. -/

open Set MeasureTheory
open scoped ComplexOrder
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Analysis.NormalFunctionals
open _root_.D5.S3.Quantum.Analysis.NormalMomentFamily

noncomputable section
universe u

namespace Reg.D5.S3.Quantum.Analysis.NormalMomentFamily

abbrev signature := Reg.D5.S3.Quantum.Analysis.NormalL1Realization.signature
abbrev actual := Reg.D5.S3.Quantum.Analysis.NormalL1Realization.actual
abbrev rejected := Reg.D5.S3.Quantum.Analysis.NormalL1Realization.rejected

def arena : Arena where
  signature := signature
  Law R := ∀
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (M : VonNeumannAlgebra H) (ρ σ : StrongDual ℂ M.toStarSubalgebra)
    (hρ : ∀ a, 0 ≤ a → 0 ≤ ρ a) (hσ : ∀ a, 0 ≤ a → 0 ≤ σ a)
    (hn : IsOrderNormal (ρ + σ)),
    IsCompact {F : Ambient M.toStarSubalgebra | Compatible ρ σ F} ∧
    Nonempty (Family ρ σ) ∧
    Continuous (finiteMeasure (ρ := ρ) (σ := σ)) ∧
    IsCompact (Set.range (finiteMeasure (ρ := ρ) (σ := σ))) ∧
    ∀ F : Family ρ σ,
      (scalarMeasure F).Regular ∧
      scalarMeasure F Set.univ = ENNReal.ofReal (((ρ + σ) 1).re) ∧
      (∀ g : C(Interval, ℂ), linearMap F g 1 = ∫ x, g x ∂scalarMeasure F) ∧
      ∃ Γ : (Interval →₁[scalarMeasure F] ℂ) →L[ℂ] StrongDual ℂ M.toStarSubalgebra,
        (∀ g : C(Interval, ℂ), Γ (ContinuousMap.toLp 1 (scalarMeasure F) ℂ g) =
          linearMap F g) ∧
        (∀ h : Interval →₁[scalarMeasure F] ℂ, IsOrderNormal (Γ h)) ∧
        (∀ h : Interval →₁[scalarMeasure F] ℂ, (∀ᵐ x ∂scalarMeasure F, 0 ≤ h x) →
          ∀ a : M.toStarSubalgebra, 0 ≤ a → 0 ≤ Γ h a) ∧
        (∀ h : Interval →₁[scalarMeasure F] ℂ, Γ h 1 = ∫ x, h x ∂scalarMeasure F) ∧
        R.readout () () ‖Γ‖ 1 ∧
        Γ (ContinuousMap.toLp 1 (scalarMeasure F) ℂ posterior) = ρ ∧
        Γ (ContinuousMap.toLp 1 (scalarMeasure F) ℂ (1 - posterior)) = σ

private theorem actual_law : arena.{u}.Law actual := @compact_normal_posterior_family.{u}

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let M : VonNeumannAlgebra PUnit.{u+1} :=
    { toStarSubalgebra := ⊤
      centralizer_centralizer' := by
        ext x
        constructor
        · intro _; trivial
        · intro _ y _hy; exact Subsingleton.elim _ _ }
  have : IsClosed (M.toStarSubalgebra : Set (PUnit.{u+1} →L[ℂ] PUnit.{u+1})) :=
    _root_.D5.S3.Quantum.Analysis.VonNeumannNormalL1.closedCarrier M
  have hn : IsOrderNormal (A := M.toStarSubalgebra) (0 : StrongDual ℂ M.toStarSubalgebra) :=
    (normalDual (A := M.toStarSubalgebra)).zero_mem
  have hall := h M (0 : StrongDual ℂ M.toStarSubalgebra) (0 : StrongDual ℂ M.toStarSubalgebra)
    (by intro a ha; simp) (by intro a ha; simp) (by simpa only [add_zero] using hn)
  obtain ⟨F⟩ := hall.2.1
  obtain ⟨_, _, _, Γ, _, _, _, _, hf, _, _⟩ := hall.2.2.2.2 F
  exact hf

def sourceProposition : Prop := type_of% (@compact_normal_posterior_family.{u})

def family : Registration arena.{u} sourceProposition.{u} where
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
    (P := sourceProposition.{u})
    (@compact_normal_posterior_family.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Analysis.NormalMomentFamily.posteriorUnit
  realizationName := `Reg.D5.S3.Quantum.Analysis.NormalMomentFamily.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.NormalMomentFamily
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "arg", "arg", "arg", "arg", "body", "arg", "arg", "arg",
        "arg", "body", "arg", "arg", "arg", "arg", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


/-- Exact exposed unit source; no serialization certificate is claimed. -/
theorem unit_source_bridge : (type_of% (@unit_value.{u})) ↔
    ∀ {A : Type u} [CStarAlgebra A] [PartialOrder A]
      {ρ σ : StrongDual ℂ A} (F : Family ρ σ), linearMap F 1 = ρ + σ := Iff.rfl

/-- Exact exposed posterior source with its original generic algebra. -/
theorem posterior_source_bridge : (type_of% (@posterior_value.{u})) ↔
    ∀ {A : Type u} [CStarAlgebra A] [PartialOrder A]
      {ρ σ : StrongDual ℂ A} (F : Family ρ σ), linearMap F posterior = ρ := Iff.rfl

/-- All continuous complex integrals, with the entire original telescope. -/
theorem complex_mass_source_bridge : (type_of% (@integral_complex.{u})) ↔
    ∀ {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
      {ρ σ : StrongDual ℂ A} (F : Family ρ σ) (g : C(Interval, ℂ)),
      linearMap F g 1 = ∫ t, g t ∂scalarMeasure F := Iff.rfl

#print axioms family
#print axioms audit

end Reg.D5.S3.Quantum.Analysis.NormalMomentFamily
