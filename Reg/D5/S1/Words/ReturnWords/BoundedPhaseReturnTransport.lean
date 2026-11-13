import D5.S1.Words.ReturnWords.BoundedPhaseReturnTransport
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

open _root_.D5.S1.Words.ReturnWords.CoherentReturnPathTemplates
open _root_.D5.S1.Words.ReturnWords.BoundedPhaseReturnTransport
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open Quiver

/-! Four-slot audit attempt for the bounded-phase path transport theorem. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S1.Words.ReturnWords.BoundedPhaseReturnTransport

universe u v w

structure Input where
  V : Type u
  quiver : Quiver.{v} V
  finite : Finite V
  α : Type w
  label : @EdgeLabel V quiver α
  S : @StronglyConnectedComponent V quiver
  phases : @BoundedPhases V quiver α label S

abbrev signature : Signature where
  Params := Unit
  State _ := Input.{u, v, w} × Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def target (p : Input.{u, v, w}) :=
  type_of% (@path_output_of_bounded_phases p.V p.quiver p.finite p.α p.label p.S p.phases)

private theorem target_valid (p : Input.{u, v, w}) : target p := by
  change type_of% (@path_output_of_bounded_phases p.V p.quiver p.finite p.α p.label p.S p.phases)
  exact @path_output_of_bounded_phases p.V p.quiver p.finite p.α p.label p.S p.phases

noncomputable def actual : Realization signature.{u, v, w} :=
  realize signature
    (fun _ _ s => if s.2 then @decide (target s.1) (Classical.propDecidable _) else false)
    (fun e => nomatch e)

def rejected : Realization signature.{u, v, w} :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u, v, w}
  Law R := ∀ {V : Type u} [q : Quiver.{v} V] [f : Finite V]
    {α : Type w} (label : @EdgeLabel V q α)
    (S : @StronglyConnectedComponent V q)
    (hP : @BoundedPhases V q α label S),
    R.readout () ()
      ⟨⟨V, q, f, α, label, S, hP⟩, true⟩ =
      true

theorem actual_law : arena.{u, v, w}.Law actual := by
  intro V q f α label S hP
  have ht : target ⟨V, q, f, α, label, S, hP⟩ :=
    target_valid ⟨V, q, f, α, label, S, hP⟩
  simpa [actual, realize, target, Classical.propDecidable] using
    (@decide_eq_true (target ⟨V, q, f, α, label, S, hP⟩)
      (Classical.propDecidable _) ht)

theorem rejected_law : ¬ arena.{u, v, w}.Law rejected := by
  intro h
  let q : Quiver.{v} (ULift.{u} Unit) := ⟨fun _ _ => ULift.{v} Empty⟩
  let S : @StronglyConnectedComponent (ULift.{u} Unit) q :=
    @StronglyConnectedComponent.mk (ULift.{u} Unit) q ⟨()⟩
  let label : @EdgeLabel (ULift.{u} Unit) q (ULift.{w} Unit) :=
    fun {_ _} e => nomatch e
  have phases : @BoundedPhases (ULift.{u} Unit) q (ULift.{w} Unit) label S := by
    refine ⟨1, by decide, ?_, fun _ => ULift.up (), fun _ => 0, ?_⟩
    · simp [S, Component]
    · intro a b e
      exact nomatch e
  let p : Input.{u, v, w} :=
    ⟨ULift.{u} Unit, q, inferInstance, ULift.{w} Unit, label, S, phases⟩
  have hp := h label S phases
  have : False := by
    have hb : false = true := by simpa [rejected, realize] using hp
    exact Bool.noConfusion hb
  exact this

noncomputable def family : Registration arena.{u, v, w}
    (type_of% (@path_output_of_bounded_phases.{u, v, w})) where
  actual := actual
  bridge := by
    constructor
    · intro h V q f α label S hP
      have ht : target ⟨V, q, f, α, label, S, hP⟩ := by
        simpa [target] using (@h V q f α label S hP)
      simpa [actual, realize, target, Classical.propDecidable] using
        (@decide_eq_true (target ⟨V, q, f, α, label, S, hP⟩)
          (Classical.propDecidable _) ht)
    · intro h V q f α label S hP
      have hh := h label S hP
      have hb : @decide (target ⟨V, q, f, α, label, S, hP⟩)
          (Classical.propDecidable _) = true := by
        simpa [actual, realize, target, Classical.propDecidable] using hh
      have ht : target ⟨V, q, f, α, label, S, hP⟩ :=
        @of_decide_eq_true (target ⟨V, q, f, α, label, S, hP⟩)
          (Classical.propDecidable _) hb
      simpa [target] using ht
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, ?_, rejected_law⟩
      · intro j hj
        exact (hj (Subsingleton.elim j i)).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := by
    intro i
    let q : Quiver.{v} (ULift.{u} Unit) := ⟨fun _ _ => ULift.{v} Empty⟩
    let S : @StronglyConnectedComponent (ULift.{u} Unit) q :=
      @StronglyConnectedComponent.mk (ULift.{u} Unit) q ⟨()⟩
    let label : @EdgeLabel (ULift.{u} Unit) q (ULift.{w} Unit) :=
      fun {_ _} e => nomatch e
    have phases : @BoundedPhases (ULift.{u} Unit) q (ULift.{w} Unit) label S := by
      refine ⟨1, by decide, ?_, fun _ => ULift.up (), fun _ => 0, ?_⟩
      · simp [S, Component]
      · intro a b e
        exact nomatch e
    let p : Input.{u, v, w} :=
      ⟨ULift.{u} Unit, q, inferInstance, ULift.{w} Unit, label, S, phases⟩
    refine ⟨(), (p, true), (p, false), ?_⟩
    change @decide (target p) (Classical.propDecidable _) ≠ false
    intro hfalse
    have htrue := @decide_eq_true (target p) (Classical.propDecidable _) (target_valid p)
    exact Bool.noConfusion (hfalse ▸ htrue)

noncomputable def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@path_output_of_bounded_phases.{u, v, w})
    (type_of% (realize signature.{u, v, w}
      (fun _ _ s => if s.2 then @decide (target s.1) (Classical.propDecidable _) else false)
        (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S1.Words.ReturnWords.BoundedPhaseReturnTransport.path_output_of_bounded_phases.__information_unit
  realizationName := `Reg.D5.S1.Words.ReturnWords.BoundedPhaseReturnTransport.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u, v, w}⟩
  objectArena := .source ⟨arena.{u, v, w}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u, v, w} ⟨family.{u, v, w}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u, v, w}
    (fun _ _ s => if s.2 then @decide (target s.1) (Classical.propDecidable _) else false)
      (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.ReturnWords.BoundedPhaseReturnTransport
    definition := none
    coordinates := #[]
    readouts := #[] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms family
#print axioms audit

end Reg.D5.S1.Words.ReturnWords.BoundedPhaseReturnTransport
