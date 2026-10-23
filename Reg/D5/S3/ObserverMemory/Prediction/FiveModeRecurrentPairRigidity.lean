import D5.S3.ObserverMemory.Prediction.FiveModeRecurrentPairRigidity
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

/-! Source-bound audit of the complete actual recurrent-pair theorem. -/

open _root_.D5.S3.ObserverMemory.Prediction.FiniteStartFiveModeSource
open _root_.D5.S3.ObserverMemory.Prediction.FiveModePredictiveLawGeometry
open _root_.D5.S3.ObserverMemory.Prediction.FiveModeAutonomousSharpCount
open _root_.D5.S3.ObserverMemory.Prediction.FiveModeSelfGeneratedLaws
open _root_.D5.S3.ObserverMemory.Prediction.FiveModeRecurrentPairRigidity
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteClosedClasses
open _root_.D5.S3.TotalVariation.Pinsker _root_.D5.S3.TotalVariation.Metric
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix
open scoped BigOperators

namespace Reg.D5.S3.ObserverMemory.Prediction.FiveModeRecurrentPairRigidity

universe u_1
noncomputable section
attribute [local instance] Classical.propDecidable

@[reducible] def signature : Signature where
  Params := Type u_1
  State Z := GeneratedObserver Z
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ Z := Z → Visible → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ O => O.row) (fun e => Empty.elim e)

def rejected : Realization signature := realize signature
  (fun _ _ _ => fun _ _ => 0) (fun e => Empty.elim e)

/-- The full original theorem, varying its literal forecast emission row in the guarantee. -/
@[reducible] def arena : Arena where
  signature := signature
  Law F := ∀ {Z : Type u_1} {p q r ε : ℝ} [Fintype Z]
    (_hp : admissible p q r) (O : GeneratedObserver Z) (_hε : ε < 1)
    (_hacc : ∀ h : List Visible, 0 < historyMass p q r h → ∀ H : Nat, 0 < H →
      totalVariation (actualFutureWordWeight p q r h H)
        (generatedLaw O.update (F.readout () Z O) (O.toObserver.run h) H) ≤ ε),
    Nonempty (ActualPair p q r O) ∧
    (∀ h : List Visible, 0 < historyMass p q r h → (∃ y ∈ h, y ≠ B) →
      ∃ t : ActualPair p q r O, t.val.2 = O.toObserver.run h ∧
        acquiredPosterior p q r h = pureVector t.val.1) ∧
    (∀ t : ActualPair p q r O, ∀ y, 0 < pureRow p q r t.val.1 y →
      (actualStep O t y).val = nextPair O t.val y) ∧
    pairMatrix (p := p) (q := q) (r := r) O ∈ rowStochastic ℝ (ActualPair p q r O) ∧
    Nonempty (ClosedClass (pairMatrix (p := p) (q := q) (r := r) O)) ∧
    (∀ C : ClosedClass (pairMatrix (p := p) (q := q) (r := r) O),
      C.val.Nonempty ∧ IsIrreducible (restriction (pairMatrix O) C.val) ∧
      (∀ t ∈ C.val, ∀ u_1, Reach (pairMatrix O) t u_1 → u_1 ∈ C.val) ∧
      (∀ t ∈ C.val, O.row t.val.2 = pureRow p q r t.val.1) ∧
      (∀ t ∈ C.val, generatedLaw O.update O.row t.val.2 = pureLaw p q r t.val.1) ∧
      (∀ i : State, ∃ t ∈ C.val, t.val.1 = i)) ∧
    (∃ f : State → Z, Function.Injective f ∧ ∀ i,
      f i ∈ O.toObserver.Reached p q r ∧
      generatedLaw O.update O.row (f i) = pureLaw p q r i)

private def deltaObserver (y : Visible) : GeneratedObserver (ULift.{u_1} Unit) where
  initial := ⟨()⟩
  update _ _ := ⟨()⟩
  row _ v := if v = y then 1 else 0
  row_nonneg _ _ := by split_ifs <;> norm_num
  row_sum _ := by simp

private theorem positive : arena.{u_1}.Law actual := by
  exact @recurrent_pair_rigidity.{u_1}

private theorem negative : ¬ arena.{u_1}.Law rejected := by
  intro law
  let O := deltaObserver.{u_1} 0
  have hp : admissible (1/8) (1/8) (1/8) := by norm_num [admissible]
  have hg : ∀ h : List Visible, 0 < historyMass (1/8) (1/8) (1/8) h →
      ∀ H : Nat, 0 < H →
      totalVariation (actualFutureWordWeight (1/8) (1/8) (1/8) h H)
        (generatedLaw O.update (rejected.readout () _ O) (O.toObserver.run h) H) ≤ (3/4 : ℝ) := by
    intro h hh H hH
    obtain ⟨H, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hH)
    have hn (w : Fin (H+1) → Visible) :=
      (actual_law_probability_and_coherence hp h hh (H+1) w).1
    have hs := (actual_law_probability_and_coherence hp h hh (H+1) (fun _ => B)).2.1
    simp only [rejected, realize, generatedLaw, zero_mul, totalVariation, sub_zero,
      abs_of_nonneg (hn _)]
    rw [hs]
    norm_num
  have result := law hp O (ε := 3/4) (by norm_num) hg
  obtain ⟨f, hf, _⟩ := result.2.2.2.2.2.2
  have impossible : (0 : State) = 1 := hf (Subsingleton.elim (f 0) (f 1))
  norm_num at impossible

private theorem dependent : ObservationalDependence signature.{u_1} actual := by
  intro i
  refine ⟨ULift.{u_1} Unit, deltaObserver 0, deltaObserver 1, ?_⟩
  intro he
  have hz := congrFun (congrFun he ⟨()⟩) 0
  norm_num [actual, realize, deltaObserver] at hz

def evidence : Registration arena.{u_1}
    (type_of% (@recurrent_pair_rigidity.{u_1})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨positive, rejected, negative⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, negative⟩, fun i => nomatch i⟩
  dependence := dependent

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.ObserverMemory.Prediction.FiveModeRecurrentPairRigidity.recurrent_pair_rigidity.{u_1})
    (type_of% (realize signature.{u_1} (fun _ _ O => O.row) (fun e => Empty.elim e))) Unit Unit := {
  unitName := `Reg.D5.S3.ObserverMemory.Prediction.FiveModeRecurrentPairRigidity.recurrent_pair_rigidity,
  realizationName := `Reg.D5.S3.ObserverMemory.Prediction.FiveModeRecurrentPairRigidity.evidence,
  realizationSource := none, generated := false,
  arena := .source ⟨arena.{u_1}⟩, objectArena := .source ⟨arena.{u_1}⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena.{u_1} ⟨evidence.{u_1}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature.{u_1} (fun _ _ O => O.row) (fun e => Empty.elim e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Prediction.FiveModeRecurrentPairRigidity,
    definition := none, coordinates := #[0],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "domain",
        "body", "body", "body", "body", "fn", "arg", "arg", "fn", "fn", "arg"],
      stateBinder := 7, functionOperand := false, stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

#print axioms evidence
#print axioms registration
end
end Reg.D5.S3.ObserverMemory.Prediction.FiveModeRecurrentPairRigidity
