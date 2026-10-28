import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteEntranceDecomposition
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteEntranceDecomposition
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws
open FiniteClosedClasses FiniteEntranceDecomposition
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
    EntranceLaw (R.readout () ⟨X, inferInstance, inferInstance⟩ P)

private theorem actual_law : arena.Law actual.{u} := by
  intro X fs ds P hP
  exact actual_entrance P hP

private abbrev Counter := ULift.{u} (Fin 2)
private def good : Matrix Counter Counter ℝ := fun _ y => if y.down = 1 then 1 else 0
private def bad : Matrix Counter Counter ℝ := (2 : ℝ) • good
private def a0 : Counter := ⟨0⟩
private def a1 : Counter := ⟨1⟩
local instance (P : Matrix Counter Counter ℝ) : DecidablePred (Recurrent P) := Classical.decPred _

private theorem sum_counter (f : Counter → ℝ) : ∑ x, f x = f a0 + f a1 := by
  rw [Fintype.sum_equiv Equiv.ulift f (fun x => f ⟨x⟩) (fun _ => rfl)]
  simp [Fin.sum_univ_succ, a0, a1]

private theorem good_stoch : good ∈ rowStochastic ℝ Counter := by
  apply mem_rowStochastic_iff_sum.mpr
  constructor
  · intro x y; simp only [good]; split_ifs <;> norm_num
  · intro x; rw [sum_counter]; norm_num [good, a0, a1]

private theorem bad_nonneg (x y : Counter) : 0 ≤ bad x y := by
  change (0 : ℝ) ≤ (2 : ℝ) * (if y.down = 1 then 1 else 0)
  split_ifs <;> norm_num

private theorem bad_no_back : ¬ Reach bad a1 a0 := by
  let := bad.toQuiver
  rintro ⟨p⟩
  have hz (n : ℕ) : (bad ^ n) a1 a0 = 0 := by
    induction n with
    | zero => simp [a0, a1]
    | succ n ih =>
      rw [pow_succ, Matrix.mul_apply, sum_counter]
      simp [bad, good, a0]
  have hp := (Matrix.pow_apply_pos_iff_nonempty_path bad_nonneg p.length a1 a0).mpr ⟨p, rfl⟩
  rw [hz] at hp
  exact (lt_irrefl 0) hp

private theorem bad_forward : Reach bad a0 a1 := by
  exact ⟨@Quiver.Hom.toPath Counter bad.toQuiver a0 a1
    (PLift.up (by norm_num [bad, good, a0, a1]))⟩

private theorem bad_terminal : Terminal bad a1 := by
  intro y hy
  rcases y with ⟨y⟩
  fin_cases y
  · exact (bad_no_back hy).elim
  · exact ⟨@Quiver.Path.nil Counter bad.toQuiver a1⟩

private theorem bad_class_eq : communicatingClass bad a1 = {a1} := by
  classical
  ext y
  rcases y with ⟨y⟩
  fin_cases y
  · have hb : ¬ Reach bad a1 ⟨0⟩ := bad_no_back
    simp only [communicatingClass, mem_filter, mem_univ, true_and]
    simp [a1] at hb ⊢
    exact fun hp => (hb hp).elim
  · have hr : Reach bad a1 a1 := ⟨@Quiver.Path.nil Counter bad.toQuiver a1⟩
    simp [communicatingClass, a1] at hr ⊢
    exact hr

private def bad_class : ClosedClass bad :=
  ⟨{a1}, a1, bad_terminal, bad_class_eq.symm⟩

private theorem bad_transient : ¬ Recurrent bad a0 := by
  rintro ⟨C, hx⟩
  obtain ⟨a, ht, he⟩ := C.property
  rw [he] at hx
  have hx' : Reach bad a a0 :=
    (show Reach bad a a0 ∧ Reach bad a0 a from by simpa [communicatingClass] using hx).1
  rcases a with ⟨a⟩
  fin_cases a
  · exact bad_no_back (ht a1 bad_forward)
  · exact bad_no_back hx'

private def bad_start : Transient bad := ⟨a0, bad_transient⟩
private def bad_target : bad_class.val := ⟨a1, by simp [bad_class]⟩

private theorem bad_entry : entrance bad bad_class 0 bad_start bad_target = 2 := by
  simp [entrance, Matrix.one_apply, bad, good, bad_start, bad_target, a1]

private theorem rejected_law : ¬ arena.Law rejected.{u} := by
  intro h
  have H : EntranceLaw bad := h Counter good good_stoch
  have hs := H.total_mass bad_start
  have hn n : 0 ≤ ∑ C : ClosedClass bad, ∑ z : C.val, entrance bad C n bad_start z :=
    sum_nonneg fun C _ => sum_nonneg fun z _ => H.nonnegative C n bad_start z
  have hu : (∑ C : ClosedClass bad, ∑ z : C.val, entrance bad C 0 bad_start z) ≤ 1 := by
    have hh := hs.summable.sum_le_tsum {0} (fun n _ => hn n)
    rw [hs.tsum_eq] at hh
    simpa only [Finset.sum_singleton] using hh
  have hl : 2 ≤ ∑ C : ClosedClass bad, ∑ z : C.val, entrance bad C 0 bad_start z := by
    rw [← bad_entry]
    calc
      _ ≤ ∑ z : bad_class.val, entrance bad bad_class 0 bad_start z :=
        single_le_sum (fun z _ => H.nonnegative bad_class 0 bad_start z) (mem_univ bad_target)
      _ ≤ _ := single_le_sum (f := fun C : ClosedClass bad =>
        ∑ z : C.val, entrance bad C 0 bad_start z)
        (fun C _ => sum_nonneg fun z _ => H.nonnegative C 0 bad_start z) (mem_univ bad_class)
  linarith

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
    (@_root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteEntranceDecomposition.actual_entrance.{u})
    (type_of% (actual.{u})) (Type u → Type u → Type → Type u) Unit := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteEntranceDecomposition.actual_entrance,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteEntranceDecomposition.evidence,
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
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteEntranceDecomposition,
    definition := none,
    coordinates := #[0, 1, 2],
    readouts := #[{ path := #["body", "body", "body", "body", "body", "arg"], stateBinder := 3, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms evidence
end
end Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteEntranceDecomposition
