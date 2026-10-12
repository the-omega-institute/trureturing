import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Dynamics.Shadowing.StableCoreImage
import Reg.Support.DependentFamily

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S1.Dynamics.Shadowing
open Set Function

namespace Reg.D5.S1.Dynamics.Shadowing.StableCoreImage

noncomputable section
universe u v

abbrev observationParameters := Σ X : Type u, Σ Y : Type v, X → Y

abbrev observationSignature : Signature where
  Params := observationParameters.{u,v}
  State p := p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.2.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature.{u,v} :=
  realize observationSignature (fun _ p x => p.2.2 x) (fun e => nomatch e)

def rejected : Realization observationSignature.{u,v} := by
  classical
  exact realize observationSignature (fun _ p x =>
    if h : Nonempty p.2.1 then Classical.choice h else p.2.2 x) (fun e => nomatch e)

/-- Vary only the observation function in the left-hand image. The complete
compactness, separation, continuity and infinite right-hand telescope remain. -/
abbrev imageArena : Arena where
  signature := observationSignature.{u,v}
  Law R := ∀ {X : Type u} {Y : Type v}
    [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [TopologicalSpace Y] [T1Space Y]
    (f : X → X) (q : X → Y) (_hf : Continuous f) (_hq : Continuous q),
    (fun x => R.readout () ⟨X, Y, q⟩ x) '' stableCore f =
      ⋂ n : ℕ, q '' Set.range (f^[n])

private theorem rejected_law : ¬ imageArena.{u,v}.Law rejected := by
  classical
  intro h
  let X := ULift.{u} Bool
  let Y := ULift.{v} Bool
  let : TopologicalSpace X := ⊥
  let : DiscreteTopology X := ⟨rfl⟩
  let : TopologicalSpace Y := ⊥
  let : DiscreteTopology Y := ⟨rfl⟩
  let q : X → Y := fun x => ⟨x.down⟩
  have heq := h (id : X → X) q continuous_id continuous_of_discreteTopology
  have hall (b : Y) : b ∈ ⋂ n : ℕ, q '' Set.range ((id : X → X)^[n]) := by
    apply Set.mem_iInter.mpr
    intro n
    exact ⟨⟨b.down⟩, ⟨⟨b.down⟩, by simp⟩, rfl⟩
  have hfalse := hall (⟨false⟩ : Y)
  have htrue := hall (⟨true⟩ : Y)
  rw [← heq] at hfalse htrue
  obtain ⟨x, _, hx⟩ := hfalse
  obtain ⟨z, _, hz⟩ := htrue
  change (if h : Nonempty Y then Classical.choice h else q x) = ⟨false⟩ at hx
  change (if h : Nonempty Y then Classical.choice h else q z) = ⟨true⟩ at hz
  simp only [dif_pos (inferInstance : Nonempty Y)] at hx hz
  have hbad := congrArg ULift.down (hx.symm.trans hz)
  contradiction

def imageRegistration : Registration imageArena.{u,v}
    (type_of% (@image_stableCore_eq_iInter.{u,v})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@image_stableCore_eq_iInter.{u,v}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    let X := ULift.{u} Bool
    let Y := ULift.{v} Bool
    refine ⟨⟨X, Y, fun x => ⟨x.down⟩⟩, ⟨false⟩, ⟨true⟩, ?_⟩
    intro heq
    have hbad := congrArg ULift.down heq
    change false = true at hbad
    contradiction

def registration_1 : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@image_stableCore_eq_iInter.{u,v})
    (Realization observationSignature.{u,v}) Unit Unit where
  unitName := `Reg.D5.S1.Dynamics.Shadowing.StableCoreImage.observedStableImage
  realizationName := `Reg.D5.S1.Dynamics.Shadowing.StableCoreImage.imageRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨imageArena.{u,v}⟩
  objectArena := .source ⟨imageArena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source imageArena.{u,v} ⟨imageRegistration.{u,v}⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize observationSignature (fun _ p x => p.2.2 x)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Dynamics.Shadowing.StableCoreImage
    definition := none
    coordinates := #[0, 1, 8]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms imageRegistration
#print axioms registration_1

end
end Reg.D5.S1.Dynamics.Shadowing.StableCoreImage
