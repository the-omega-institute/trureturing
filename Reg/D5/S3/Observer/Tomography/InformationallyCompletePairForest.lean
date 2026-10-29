import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.Tomography.InformationallyCompletePairForest
import Reg.Support.DependentFamily

/-! Source-bound audit of the injectivity coordinate in the forest characterization. -/

namespace Reg.D5.S3.Observer.Tomography.InformationallyCompletePairForest

open _root_.D5.S3.Observer.Tomography.InformationallyCompletePairForest
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

/-- Observe injectivity of a joint value map on an arbitrary source type. -/
abbrev signature : Signature where
  Params := Type u
  State α := α → ℝ × ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature
    (fun _ _ h => @decide (Function.Injective h) (Classical.propDecidable _))
    (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)

/-- Keep the entire characterization, including both dictionaries and acyclicity. -/
abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {α : Type u} [Fintype α] [DecidableEq α] (f g : α → ℝ),
    IsICPair f g ↔ R.readout () α (fun x => (f x, g x)) = true ∧
      (fiberGraph f g).IsAcyclic

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hic : IsICPair (fun _ : ULift.{u} Empty => (0 : ℝ)) (fun _ => (0 : ℝ)) := by
    intro μ ν _ _ _ _
    funext x
    exact nomatch x.down
  exact Bool.noConfusion
    (((h (fun _ : ULift.{u} Empty => (0 : ℝ)) (fun _ => (0 : ℝ))).mp hic).1)

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨ULift.{u} Bool, (fun _ => (0, 0)),
    (fun b => (if b.down then (1 : ℝ) else 0, (0 : ℝ))), ?_⟩
  change @decide (Function.Injective (fun _ : ULift.{u} Bool => ((0 : ℝ), (0 : ℝ))))
    (Classical.propDecidable _) ≠
    @decide (Function.Injective (fun b : ULift.{u} Bool =>
      (if b.down then (1 : ℝ) else 0, (0 : ℝ)))) (Classical.propDecidable _)
  have hi : Function.Injective (fun b : ULift.{u} Bool =>
      (if b.down then (1 : ℝ) else 0, (0 : ℝ))) := by
    rintro ⟨x⟩ ⟨y⟩ h
    cases x <;> cases y <;> simp_all
  have hn : ¬ Function.Injective (fun _ : ULift.{u} Bool => ((0 : ℝ), (0 : ℝ))) := by
    intro hc
    have hf : false = true := congrArg ULift.down
      (hc (a₁ := (⟨false⟩ : ULift.{u} Bool)) (a₂ := ⟨true⟩) rfl)
    exact Bool.noConfusion hf
  simp [hn, hi]

def source_registration : Registration arena.{u} (type_of% (@result.{u})) where
  actual := realize signature.{u} actual.readout actual.anchor
  bridge := by simp [actual, realize]
  variation := ⟨by intro α _ _ f g; simpa [actual, realize] using result f g,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Observer.Tomography.InformationallyCompletePairForest.result.{u})
      (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Observer.Tomography.InformationallyCompletePairForest.unit
  realizationName :=
    `Reg.D5.S3.Observer.Tomography.InformationallyCompletePairForest.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.Tomography.InformationallyCompletePairForest
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Observer.Tomography.InformationallyCompletePairForest
