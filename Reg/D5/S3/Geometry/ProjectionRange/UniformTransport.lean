import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Geometry.ProjectionRange.UniformTransport
import Mathlib.Analysis.Complex.Basic
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open ProjectionRange.UniformTransport

namespace Reg.D5.S3.Geometry.ProjectionRange.UniformTransport
noncomputable section
universe u v

abbrev signature : Signature where
  Params := Σ T : Type u, Σ R : Type v, T → R
  State p := p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.2.1
  Anchor := Empty
  finiteAnchor := inferInstance

def absentAnchor : ∀ (_ : signature.{u,v}.Anchor) p, signature.{u,v}.State p :=
  fun e => nomatch e

def actual : Realization signature.{u,v} :=
  realize signature (fun _ p t => p.2.2 t) absentAnchor

/-- An intervention on the whole family, with no ring dictionary smuggled into
the independent coordinates. It need not vary a singleton output fiber. -/
def different {R : Type v} (x : R) : R := by
  classical
  exact if h : ∃ y : R, y ≠ x then Classical.choose h else x

def rejected : Realization signature.{u,v} :=
  realize signature (fun _ p t => different (p.2.2 t)) absentAnchor

abbrev arena : Arena where
  signature := signature.{u,v}
  Law ρ := ∀ {T : Type u} {R : Type v}
    [TopologicalSpace T] [PreconnectedSpace T] [NormedRing R] [CompleteSpace R]
    (P : T → R) (_hP : Continuous P) (_hidem : ∀ t, P t * P t = P t)
    (s t : T), ∃ z : Rˣ,
      ρ.readout () ⟨T, R, P⟩ t * (z : R) = (z : R) * P s

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  classical
  intro h
  let T := ULift.{u} Unit
  let R := ULift.{v} ℂ
  obtain ⟨z, hz⟩ := @h T R inferInstance inferInstance inferInstance inferInstance
    (fun _ => 1) continuous_const (by intro t; simp) ⟨()⟩ ⟨()⟩
  change different (1 : R) * (z : R) = (z : R) * 1 at hz
  have hd : different (1 : R) ≠ 1 := by
    have hex : ∃ y : R, y ≠ 1 := ⟨0, zero_ne_one⟩
    simpa only [different, dif_pos hex] using Classical.choose_spec hex
  apply hd
  have he := congrArg (fun w : R => w * (↑z⁻¹ : R)) hz
  simpa [mul_assoc] using he

def family : Registration arena.{u,v}
    (type_of% (@connected_idempotents_intertwiner.{u,v})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@connected_idempotents_intertwiner.{u,v}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨ULift.{u} Bool, ULift.{v} Bool, fun t => ⟨t.down⟩⟩,
      ⟨false⟩, ⟨true⟩, ?_⟩
    intro he
    have hb := congrArg ULift.down he
    exact Bool.false_ne_true hb

def registration_1 :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@connected_idempotents_intertwiner.{u,v})
      (Realization signature.{u,v}) Unit Unit where
  unitName := `Reg.D5.S3.Geometry.ProjectionRange.UniformTransport.intertwiner
  realizationName := `Reg.D5.S3.Geometry.ProjectionRange.UniformTransport.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v}⟩
  objectArena := .source ⟨arena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v} ⟨family.{u,v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u,v} (fun _ p t => p.2.2 t) absentAnchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some { owner := `D5.S3.Geometry.ProjectionRange.UniformTransport, definition := none, coordinates := #[0, 1, 6], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "fn", "arg", "fn", "arg", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms registration_1

end

end Reg.D5.S3.Geometry.ProjectionRange.UniformTransport
