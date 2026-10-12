import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Transportation.FerrersIntegerRectanglePaths
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Combinatorics.Transportation.FerrersIntegerRectanglePaths

open _root_.D5.S3.Combinatorics.Transportation.FerrersIntegerRectanglePaths
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

universe u_1 u_2
noncomputable section

abbrev signature : Signature where
  Params := Σ _R : Type u_1, Type u_2
  State p := p.1 → p.2 → ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.1 → p.2 → ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u_1,u_2} :=
  realize.{max (u_1 + 1) (u_2 + 1), max u_1 u_2, 0, max u_1 u_2, 0} signature (fun _ _ P => P) (fun e => Empty.elim e)

def rejected : Realization signature.{u_1,u_2} :=
  realize.{max (u_1 + 1) (u_2 + 1), max u_1 u_2, 0, max u_1 u_2, 0} signature (fun _ _ _ => fun _ _ => 0) (fun e => Empty.elim e)

abbrev arena : Arena where
  signature := signature.{u_1,u_2}
  Law Z := ∀ {R : Type u_1} {C : Type u_2}
    [fr : Fintype R] [fc : Fintype C] [lr : LinearOrder R] [dc : DecidableEq C]
    (E : R → C → Prop)
    (_nested : ∀ i l, i ≤ l → ∀ j, E i j → E l j)
    (P Q : R → C → ℕ), Supported E P → Supported E Q → SameMargins P Q →
    Relation.ReflTransGen
      (fun A B => RectangleStep E A B ∧ Supported E B ∧ SameMargins B Q)
      (Z.readout () ⟨R, C⟩ P) Q

private theorem rejected_law : ¬ arena.{u_1,u_2}.Law rejected := by
  intro h
  let P : ULift.{u_1} Unit → ULift.{u_2} Unit → ℕ := fun _ _ => 1
  have hs : Supported (fun (_ : ULift.{u_1} Unit) (_ : ULift.{u_2} Unit) => True) P := by
    intro i j h; exact (h trivial).elim
  have hm : SameMargins P P := ⟨fun _ => rfl, fun _ => rfl⟩
  have hh := h (fun (_ : ULift.{u_1} Unit) (_ : ULift.{u_2} Unit) => True)
    (by intro i l h j hj; trivial) P P hs hs hm
  rcases hh.cases_head with heq | ⟨B, hstep, _⟩
  · have hh := congrFun (congrFun heq ⟨()⟩) ⟨()⟩
    exact Nat.zero_ne_one hh
  · rcases hstep.1 with ⟨i, l, j, k, _, _, _, _, _, _, hij, _⟩
    exact (Nat.lt_irrefl 0) hij

def registration : Registration arena.{u_1,u_2} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨by
    intro R C fr fc lr dc E nested P Q hP hQ hm
    exact ferrers_integer_rectangle_connected E nested P Q hP hQ hm,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h; exact (h (Subsingleton.elim _ _)).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨ULift.{u_1} Unit, ULift.{u_2} Unit⟩, (fun _ _ => 0), (fun _ _ => 1), ?_⟩
    intro h
    have hh := congrFun (congrFun h ⟨()⟩) ⟨()⟩
    exact Nat.zero_ne_one hh

def registration_contract : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Combinatorics.Transportation.FerrersIntegerRectanglePaths.ferrers_integer_rectangle_connected.{u_1,u_2})
    (type_of% (realize.{max (u_1 + 1) (u_2 + 1), max u_1 u_2, 0, max u_1 u_2, 0} signature.{u_1,u_2} (fun _ _ P => P) (fun e => Empty.elim e)))
    Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str
    `D5.S3.Combinatorics.Transportation.FerrersIntegerRectanglePaths.ferrers_integer_rectangle_connected
    "Reg.D5.S3.Combinatorics.Transportation.FerrersIntegerRectanglePaths/Reg.D5.S3.Combinatorics.Transportation.FerrersIntegerRectanglePaths.arena/[anonymous]")
    "__information_unit"
  realizationName := `Reg.D5.S3.Combinatorics.Transportation.FerrersIntegerRectanglePaths.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u_1,u_2}⟩
  objectArena := .source ⟨arena.{u_1,u_2}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u_1,u_2} ⟨registration.{u_1,u_2}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{max (u_1 + 1) (u_2 + 1), max u_1 u_2, 0, max u_1 u_2, 0} signature.{u_1,u_2} (fun _ _ P => P) (fun e => Empty.elim e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    definition := none
    owner := `D5.S3.Combinatorics.Transportation.FerrersIntegerRectanglePaths
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 8, functionOperand := false, stateOperand := none,
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms registration
end
end Reg.D5.S3.Combinatorics.Transportation.FerrersIntegerRectanglePaths
