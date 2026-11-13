import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Observer.ProbabilisticClosure.AdaptiveActualRiseCounts

/-! Source-bound audit of chronological rise counts at the first marker. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Reg.D5.S3.Observer.ProbabilisticClosure.AdaptiveActualRiseCounts

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Observer.ProbabilisticClosure.AdaptiveMarkerStoppingTails
open _root_.D5.S3.Observer.ProbabilisticClosure.AdaptiveActualRiseCounts

universe u

abbrev Parameters := Σ Seed : Type u, Σ m : MeasurableSpace Seed,
  Σ _p : @Policy Seed m, Seed × ℕ × Side

abbrev signature : Signature where
  Params := Parameters.{u}
  State _ := Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p z =>
    @actualRiseCount p.1 p.2.1 p.2.2.1 p.2.2.2.1 z p.2.2.2.2.2 p.2.2.2.2.1)
    Empty.elim

/-- Only the first chronological count occurrence is varied. Every original
hypothesis and the entire remaining conclusion stay in the law. -/
def arena : Arena where
  signature := signature.{u}
  Law R := ∀ {Seed : Type u} [m : MeasurableSpace Seed] (p : Policy Seed) (seed : Seed)
    (z : Source) (T : ℕ), noAdjacentOnes z → stoppingTime p seed z = (T : WithTop ℕ) →
    0 < T ∧ ∀ side,
      R.readout () ⟨Seed, m, p, seed, T, side⟩ z = actualRiseCount p seed z side (T - 1) ∧
      actualRiseCount p seed z side T =
        (if z.1 then sideCount (zeroReplay p seed (T - 1)) side / 2
          else (sideCount (zeroReplay p seed (T - 1)) side + 1) / 2)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 1) Empty.elim

def leftPolicy : Policy (ULift.{u} Unit) where
  choose _ _ _ := false
  measurable_section _ _ := measurable_const

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro law
  have ht : stoppingTime leftPolicy.{u} (ULift.up ()) (false, (fun _ => false), fun _ => false) =
      (1 : WithTop ℕ) := by
    unfold stoppingTime
    have hex : ∃ n, (actualRun leftPolicy.{u} (ULift.up ())
        (false, (fun _ => false), fun _ => false) n).stopped = true := ⟨1, rfl⟩
    rw [dite_eq_left hex]
    have he : Nat.find hex = 1 := by
      apply (Nat.find_eq_iff hex).mpr
      refine ⟨rfl, ?_⟩
      intro n hn
      have : n = 0 := by omega
      subst n
      decide
    exact congrArg (fun n : ℕ => (n : WithTop ℕ)) he
  have hs : noAdjacentOnes (false, (fun _ => false), fun _ => false) := by
    intro side i
    cases i <;> cases side <;> simp [endpoint, arm]
  have hh := ((law leftPolicy.{u} (ULift.up ()) _ 1 hs ht).2 false).1
  norm_num [rejected, realize, actualRiseCount, Nat.count] at hh

private theorem actual_dependence : ObservationalDependence signature.{u} actual := by
  intro _
  refine ⟨⟨ULift Unit, inferInstance, leftPolicy, ULift.up (), 1, false⟩,
    (false, (fun _ => false), fun _ => false),
    (false, (fun i => decide (i = 0)), fun _ => false), ?_⟩
  norm_num [actual, realize, actualRiseCount, Nat.count, actualRun,
    sideCount, endpoint, arm, leftPolicy]

def family : Registration arena.{u} (type_of% (@actual_rise_count_at_first_stop.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@actual_rise_count_at_first_stop.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@actual_rise_count_at_first_stop.{u})
    (Realization signature.{u}) Type Unit where
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.AdaptiveActualRiseCounts.unit
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.AdaptiveActualRiseCounts.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ p z =>
    @actualRiseCount p.1 p.2.1 p.2.2.1 p.2.2.2.1 z p.2.2.2.2.2 p.2.2.2.2.1) Empty.elim)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.AdaptiveActualRiseCounts
    definition := none
    coordinates := #[0, 1, 2, 3, 5, 8]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Observer.ProbabilisticClosure.AdaptiveActualRiseCounts
