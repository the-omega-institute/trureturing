import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteAllStateLimits
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteAllStateLimits
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws
open FiniteClosedClasses FiniteAllStateLimits
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Matrix Filter Topology Finset
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
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
  realize signature (fun (_ : Unit) (_ : Params.{u}) P => (2 : ℝ) • P) (fun e => nomatch e)

def arena : Arena where
  signature := signature.{u}
  Law R := ∀ (X : Type u) [Fintype X] [DecidableEq X] (P : Matrix X X ℝ),
    P ∈ rowStochastic ℝ X →
    Nonempty (AllStateLimits (R.readout () ⟨X, inferInstance, inferInstance⟩ P))

private theorem actual_law : arena.Law actual.{u} := by
  intro X fs ds P hP
  exact actual_all_state_limits P hP

private abbrev Counter := ULift.{u} Unit
private def a : Counter := ⟨()⟩
private def bad : Matrix Counter Counter ℝ := (2 : ℝ) • 1

private theorem bad_terminal : Terminal bad a := by
  intro y _
  have he : y = a := Subsingleton.elim _ _
  subst y
  exact ⟨@Quiver.Path.nil Counter bad.toQuiver a⟩

private theorem bad_class_eq : communicatingClass bad a = univ := by
  classical
  ext y
  simp only [communicatingClass, mem_filter, mem_univ, true_and]
  have he : y = a := Subsingleton.elim _ _
  subst y
  simp only [iff_true]
  exact ⟨⟨@Quiver.Path.nil Counter bad.toQuiver a⟩, ⟨@Quiver.Path.nil Counter bad.toQuiver a⟩⟩

private def bad_class : ClosedClass bad :=
  ⟨univ, a, bad_terminal, bad_class_eq.symm⟩

private theorem rejected_law : ¬ arena.Law rejected.{u} := by
  intro h
  have hn : Nonempty (AllStateLimits bad) :=
    h Counter (1 : Matrix Counter Counter ℝ) (rowStochastic ℝ Counter).one_mem
  let A := Classical.choice hn
  let L := A.classes bad_class
  let yy : bad_class.val := ⟨a, mem_univ _⟩
  have hm : L.stationaryRow yy = 1 := by
    have hh := L.normalized
    rw [Fintype.sum_subsingleton _ yy] at hh
    exact hh
  have ht := congrFun L.stationary yy
  change (∑ z : bad_class.val, L.stationaryRow z * bad z.val yy.val) = L.stationaryRow yy at ht
  have hb : bad yy.val yy.val = 2 := by simp [bad]
  rw [Fintype.sum_subsingleton _ yy, hb, hm] at ht
  norm_num at ht

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
    (@_root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteAllStateLimits.actual_all_state_limits.{u})
    (type_of% (actual.{u})) (Type u → Type u → Type → Type u) Unit := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteAllStateLimits.actual_all_state_limits,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteAllStateLimits.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena.{u}⟩,
  objectArena := .source ⟨arena.{u}⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena.{u} ⟨evidence.{u}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature.{u} (fun (_ : Unit) (_ : Params.{u}) A => A)
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := some (Matrix),
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteAllStateLimits,
    definition := none,
    coordinates := #[0, 1, 2],
    readouts := #[{ path := #["body", "body", "body", "body", "body", "arg", "arg"], stateBinder := 3, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms evidence
end
end Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteAllStateLimits
