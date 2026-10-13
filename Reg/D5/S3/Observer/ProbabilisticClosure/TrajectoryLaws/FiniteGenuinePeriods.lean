import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteGenuinePeriods
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteGenuinePeriods
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws
open FiniteClosedClasses FiniteGenuinePeriods
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Matrix
open scoped BigOperators
noncomputable section
universe u
abbrev Params := Σ X : Type u, Fintype X × DecidableEq X
abbrev signature : Signature where
  Params := Params.{u}
  State p := Matrix p.1 p.1 ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Matrix p.1 p.1 ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun (_ : Unit) (_ : Params.{u}) P => P) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun (_ : Unit) (_ : Params.{u}) _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature.{u}
  Law R := ∀ (X : Type u) [Fintype X] [DecidableEq X] (P : Matrix X X ℝ),
    P ∈ rowStochastic ℝ X →
    let B := R.readout () ⟨X, inferInstance, inferInstance⟩ P
    ∀ C : ClosedClass B, Nonempty (ClassPeriods B C)

private theorem actual_law : arena.Law actual.{u} := by
  intro X fs ds P hP
  dsimp [actual, realize]
  intro C
  exact actual_periods P hP C

private theorem rejected_law : ¬ arena.Law rejected.{u} := by
  intro h
  let X := ULift.{u} Unit
  let B : Matrix X X ℝ := 0
  let a : X := ⟨()⟩
  have ht : Terminal B a := by
    intro y _
    have he : y = a := Subsingleton.elim _ _
    subst y
    exact ⟨@Quiver.Path.nil X B.toQuiver a⟩
  let C : ClosedClass B := ⟨communicatingClass B a, a, ht, rfl⟩
  obtain ⟨K⟩ := h X 1 (rowStochastic ℝ X).one_mem C
  have he : period (restriction B C.val) K.base = 0 := by
    apply Nat.setGcd_eq_zero_iff.mpr
    intro n hn
    have hp : n ≠ 0 := ne_of_gt hn.1
    have hz : restriction B C.val = 0 := rfl
    simp only [returns, Set.mem_setOf_eq, hz, zero_pow hp, Matrix.zero_apply, lt_self_iff_false,
      and_false] at hn
  have hp := K.positive
  change 0 < period (restriction B C.val) K.base at hp
  rw [he] at hp
  exact (Nat.lt_irrefl 0) hp

def evidence : Registration arena.{u} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    dsimp only [Sensitivity, arena, signature]
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim _ _)).elim
    · intro e; exact nomatch e
  dependence := by
    change ∀ i : Unit, ∃ p x y, actual.readout i p x ≠ actual.readout i p y
    intro i
    let X := ULift.{u} Unit
    refine ⟨⟨X, inferInstance, inferInstance⟩, (0 : Matrix X X ℝ), 1, ?_⟩
    intro he
    have hh := congrArg (fun M => M ⟨()⟩ ⟨()⟩) he
    change (0 : ℝ) = 1 at hh
    exact zero_ne_one hh

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteGenuinePeriods.actual_periods.{u})
    (type_of% (actual.{u})) (Type u → Type u → Type → Type u) Unit := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteGenuinePeriods.actual_periods,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteGenuinePeriods.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena.{u}⟩,
  objectArena := .source ⟨arena.{u}⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena.{u} ⟨evidence.{u}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature.{u} (fun (_ : Unit) (_ : Params.{u}) P => P)
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := some (Matrix),
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteGenuinePeriods,
    definition := none,
    coordinates := #[0, 1, 2],
    readouts := #[{ path := #["body", "body", "body", "body", "body", "domain", "arg"], stateBinder := 3, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms evidence
end
end Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteGenuinePeriods
