import D5.S0.Certificates.Quandles.PresentedQuandle
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

/-! A source-bound audit attempt preserving the full presentation-evaluation telescope. -/

noncomputable section

namespace Reg.D5.S0.Certificates.Quandles.PresentedQuandle

open _root_.D5.S0.Certificates.Quandles.PresentedQuandle
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

universe u v w

/-- Keep every original type, structure, equation and satisfaction proof. -/
structure Params where
  G : Type u
  Q : Type v
  quandle : Quandle Q
  relations : Term G → Term G → Prop
  values : G → Q
  respects : ∀ x y, relations x y →
    @Term.eval G Q quandle values x = @Term.eval G Q quandle values y

private abbrev signature : Signature where
  Params := Params.{u,v}
  State p := p.G
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.Q
  Anchor := Empty
  finiteAnchor := inferInstance

private def actual : Realization signature.{u,v} :=
  realize signature.{u,v} (fun _ p g => p.values g) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature.{u,v}
  Law r := ∀ (p : Params.{u,v}) (g : p.G),
    @lift p.G p.relations p.Q p.quandle p.values p.respects (of p.relations g) =
      r.readout () p g

private abbrev upQuandle (Q : Type w) [Quandle Q] : Quandle (ULift.{v} Q) where
  act x y := ⟨Shelf.act x.down y.down⟩
  invAct x y := ⟨Rack.invAct x.down y.down⟩
  self_distrib := by intro x y z; apply ULift.ext; exact Shelf.self_distrib
  left_inv := by intro x y; apply ULift.ext; exact Rack.invAct_act_eq _ _
  right_inv := by intro x y; apply ULift.ext; exact Rack.act_invAct_eq _ _
  fix := by intro x; apply ULift.ext; exact Quandle.fix

private def witness : Params.{u,v} where
  G := ULift.{u} Bool
  Q := ULift.{v} (Quandle.Dihedral 9)
  quandle := upQuandle (Quandle.Dihedral 9)
  relations := fun _ _ => False
  values g := ⟨if g.down then (1 : ZMod 9) else (0 : ZMod 9)⟩
  respects := by intro x y h; exact h.elim

private def perturb {Q : Type v} (q : Q) : Q :=
  by
    classical
    exact if h : ∃ r, r ≠ q then Classical.choose h else q

private def rejected : Realization signature.{u,v} :=
  realize signature.{u,v} (fun _ p g => perturb (p.values g)) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.{u,v}.Law rejected.{u,v} := by
  intro h
  have he := h witness ⟨false⟩
  change (⟨(0 : ZMod 9)⟩ : ULift.{v} (Quandle.Dihedral 9)) = perturb ⟨(0 : ZMod 9)⟩ at he
  have hex : ∃ r : ULift.{v} (Quandle.Dihedral 9), r ≠ ⟨(0 : ZMod 9)⟩ := by
    refine ⟨⟨(1 : ZMod 9)⟩, ?_⟩
    intro h
    have hc : (1 : ZMod 9) = 0 := congrArg ULift.down h
    exact (by decide : (1 : ZMod 9) ≠ 0) hc
  have hn : perturb (⟨(0 : ZMod 9)⟩ : ULift.{v} (Quandle.Dihedral 9)) ≠ ⟨(0 : ZMod 9)⟩ := by
    unfold perturb
    rw [dif_pos hex]
    exact Classical.choose_spec hex
  exact hn he.symm

private theorem actual_dependence : ObservationalDependence signature.{u,v} actual.{u,v} := by
  intro i
  refine ⟨witness, ⟨false⟩, ⟨true⟩, ?_⟩
  intro h
  have hc : (0 : ZMod 9) = 1 := congrArg ULift.down h
  exact (by decide : (0 : ZMod 9) ≠ 1) hc

private theorem sensitivity : Sensitivity arena.{u,v} actual.{u,v} := by
  constructor
  · intro i
    refine ⟨rejected, ?_, ?_, rejected_law⟩
    · intro j h
      exact (h (Subsingleton.elim _ _)).elim
    · funext e
      exact nomatch e
  · intro e
    exact nomatch e

/-- Exact original telescope, with variable generator readout, not a truth-bit wrapper. -/
def liftOfFamily : Registration arena.{u,v} (type_of% (@lift_of.{u,v})) where
  actual := actual
  bridge := by
    constructor
    · intro h p g
      exact @h p.G p.relations p.Q p.quandle p.values p.respects g
    · intro h G R Q inst v hv g
      exact h ⟨G, Q, inst, R, v, hv⟩ g
  variation := ⟨by intro p g; exact @lift_of p.G p.relations p.Q p.quandle p.values p.respects g,
    rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := actual_dependence

/-- Source-bound four-slot registration attempt for the actual public helper. -/
def liftOfAudit.{audit_u,audit_v} : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@lift_of.{audit_u,audit_v}) (Realization signature.{audit_u,audit_v}) (Type) Unit where
  unitName := `D5.S0.Certificates.Quandles.PresentedQuandle.lift_of.__information_unit
  realizationName := `Reg.D5.S0.Certificates.Quandles.PresentedQuandle.liftOfFamily
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨liftOfFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{audit_u,audit_v} (fun _ p g => p.values g) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S0.Certificates.Quandles.PresentedQuandle
    definition := none
    coordinates := #[4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 6
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S0.Certificates.Quandles.PresentedQuandle

end
