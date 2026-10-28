import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FinitePeriodicArithmetic
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FinitePeriodicArithmetic
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws
open FiniteClosedClasses FiniteAllStateLimits FinitePeriodicArithmetic FiniteGenuinePeriods
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

private def Goal {X : Type u} [Fintype X] [DecidableEq X]
    (P : Matrix X X ℝ) (N L : ℕ) : Prop :=
    ∃ (A : AllStateLimits P) (D : ℕ), 0 < D ∧
      D ≤ (2*L)^(N^3) * ((N+1)*L)^(N^2) ∧ (IsEmpty X → D = 1) ∧
      (∀ (B : AllStateLimits P) (i : ℕ) (x y : X), ∃ z : ℤ,
        (D : ℝ) * periodicEntry B.periods B.classes i x y = z) ∧
      ∀ (B : AllStateLimits P) (d : ℕ), 0 < d →
        (∀ C, period (restriction P C.val) (B.periods C).base ∣ d) →
        ∀ (i : ℕ) (x y : X), ∃ z : ℤ,
          periodicEntry B.periods B.classes i x y = (z : ℝ) / (D : ℝ) ∧
          Tendsto (fun t : ℕ => (P^(d*t+i)) x y) atTop (𝓝 ((z : ℝ) / (D : ℝ)))

def arena : Arena where
  signature := signature.{u}
  Law R := ∀ (X : Type u) [Fintype X] [DecidableEq X] (P : Matrix X X ℝ),
    P ∈ rowStochastic ℝ X → ∀ (N L : ℕ), Fintype.card X ≤ N → 0 < L →
    (∀ x y, ∃ z : ℤ, (L : ℝ) * P x y = z) →
    Goal (R.readout () ⟨X, inferInstance, inferInstance⟩ P) N L

private theorem actual_law : arena.Law actual.{u} := by
  intro X fs ds P hP N L hN hL hclear
  exact actual_common_denominator P hP N L hN hL hclear

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
  constructor
  · intro _; trivial
  · intro _
    exact ⟨⟨@Quiver.Path.nil Counter bad.toQuiver a⟩, ⟨@Quiver.Path.nil Counter bad.toQuiver a⟩⟩

private def bad_class : ClosedClass bad :=
  ⟨univ, a, bad_terminal, bad_class_eq.symm⟩

private theorem rejected_law : ¬ arena.Law rejected.{u} := by
  intro h
  have hn : Goal bad 1 1 :=
    h Counter (1 : Matrix Counter Counter ℝ) (rowStochastic ℝ Counter).one_mem
      1 1 (by simp) (by norm_num) (by
        intro x y
        refine ⟨1, ?_⟩
        simp [Matrix.one_apply, Subsingleton.elim x y])
  let A : AllStateLimits bad := hn.choose
  let L := A.classes bad_class
  let yy : bad_class.val := ⟨a, mem_univ _⟩
  let : Unique bad_class.val := ⟨⟨yy⟩, fun z => Subsingleton.elim _ _⟩
  have he : (default : bad_class.val) = yy := Subsingleton.elim _ _
  have hm : L.stationaryRow yy = 1 := by
    simpa only [univ_unique, sum_singleton, he] using L.normalized
  have ht := congrFun L.stationary yy
  change (∑ z : bad_class.val, L.stationaryRow z * bad z.val yy.val) = L.stationaryRow yy at ht
  have hb : bad yy.val yy.val = 2 := by simp [bad]
  simp only [univ_unique, sum_singleton, he, hb, hm] at ht
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
    (@_root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FinitePeriodicArithmetic.actual_common_denominator.{u})
    (type_of% (actual.{u})) (Type u → Type u → Type → Type u) Unit := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FinitePeriodicArithmetic.actual_common_denominator,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FinitePeriodicArithmetic.evidence,
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
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FinitePeriodicArithmetic,
    definition := none,
    coordinates := #[0, 1, 2],
    readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg"], stateBinder := 3, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms evidence
end
end Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FinitePeriodicArithmetic
