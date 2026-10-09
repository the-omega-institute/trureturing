import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Dyadic.WhiteboxThreeBatchPhase
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Arith.FibonacciAtomic.Dyadic.WhiteboxThreeBatchPhase
open _root_.D5.S3.Arith.FibonacciAtomic.Dyadic.WhiteboxThreeBatchPhase
open _root_.D5.S3.Arith.FibonacciAtomic.Dyadic.WhiteboxDyadicPrefixTail
open _root_.D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped ENNReal
noncomputable section

abbrev signature : Signature.{0, 0, 0, 0, 0} where
  Params := ℝ
  State _ := ℕ
  Role := Fin 4
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ≥0∞
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun r l N => if r = 0 then rawGamma N l else if r = 1 then coarseGamma N l
    else if r = 2 then rawH N l else coarseH N l) (fun e => nomatch e)

abbrev arena : Arena.{0, 0, 0, 0, 0} where
  signature := signature
  Law R := ∀ N : ℕ, 1 ≤ N → ∀ l : ℝ, 0 < l →
    R.readout 0 l N = ENNReal.ofReal (Phase.sharp N l) ∧
    R.readout 1 l N = ENNReal.ofReal (Phase.sharp N l) ∧
    (∃ s : PrefixSampler Strategy, Coarse s ∧ G s N l = ENNReal.ofReal (Phase.sharp N l)) ∧
    (N ≤ 6*l → rawGamma N l = ENNReal.ofReal (17*N)) ∧
    (6*l ≤ N → N ≤ 14*l → rawGamma N l = ENNReal.ofReal (67*N/4+3*l/2)) ∧
    (14*l ≤ N → rawGamma N l = ENNReal.ofReal (50*N/3+8*l/3)) ∧
    R.readout 2 l N = ENNReal.ofReal (17*N) ∧
    R.readout 3 l N = ENNReal.ofReal (17*N) ∧
    (∃ s : PrefixSampler Strategy, Coarse s ∧ H s N l = ENNReal.ofReal (17*N))

private theorem bridge : Claim ↔ arena.Law actual := by
  simp only [arena, actual, realize, Fin.reduceEq, if_true, if_false]
  rfl

private theorem actual_law : arena.Law actual := bridge.mp result

def changed (r : Fin 4) : Realization signature := realize signature
  (fun j l N => if j = r then 0 else actual.readout j l N) (fun e => nomatch e)

private theorem rejected (r : Fin 4) : ¬ arena.Law (changed r) := by
  intro h
  have data := h 1 (by decide) 1 (by norm_num)
  fin_cases r
  · have bad := data.1
    norm_num [changed, realize, Phase.sharp] at bad
  · have bad := data.2.1
    norm_num [changed, realize, Phase.sharp] at bad
  · have bad := data.2.2.2.2.2.2.1
    have same : (2 : Fin 4) = ⟨2, by decide⟩ := by decide
    simp only [changed, realize, if_pos same] at bad
    norm_num at bad
  · have bad := data.2.2.2.2.2.2.2.1
    have same : (3 : Fin 4) = ⟨3, by decide⟩ := by decide
    simp only [changed, realize, if_pos same] at bad
    norm_num at bad

private theorem nonconstant (r : Fin 4) :
    actual.readout r 10 1 ≠ actual.readout r 10 2 := by
  have one := actual_law 1 (by decide) 10 (by norm_num)
  have two := actual_law 2 (by decide) 10 (by norm_num)
  fin_cases r <;> simp [actual, realize] at one two ⊢ <;>
    first | rw [one.1, two.1] | rw [one.2.1, two.2.1]
          | rw [one.2.2.2.2.2.2.1, two.2.2.2.2.2.2.1]
          | rw [one.2.2.2.2.2.2.2.1, two.2.2.2.2.2.2.2.1]
  all_goals norm_num [Phase.sharp]

def proof_record : Registration arena Claim where
  actual := actual
  bridge := bridge
  variation := ⟨actual_law, changed 0, rejected 0⟩
  sensitivity := ⟨fun i => ⟨changed i, fun j h => by
    funext l N
    simp [changed, realize, h], rfl, rejected i⟩, fun i => nomatch i⟩
  dependence := fun i => ⟨10, 1, 2, nonconstant i⟩

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Dyadic.WhiteboxThreeBatchPhase.result)
    (Realization signature) Unit Unit where
  unitName := Lean.Name.str
    `Reg.D5.S3.Arith.FibonacciAtomic.Dyadic.WhiteboxThreeBatchPhase.result "__information_unit"
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Dyadic.WhiteboxThreeBatchPhase.proof_record
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨proof_record⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun r l N => if r = 0 then rawGamma N l else if r = 1 then coarseGamma N l
      else if r = 2 then rawH N l else coarseH N l) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Dyadic.WhiteboxThreeBatchPhase
    definition := some {
      owner := `D5.S3.Arith.FibonacciAtomic.Dyadic.WhiteboxThreeBatchPhase
      name := `D5.S3.Arith.FibonacciAtomic.Dyadic.WhiteboxThreeBatchPhase.Claim
      path := #[] }
    coordinates := #[2]
    readouts := #[
      { path := #["body", "body", "body", "body", "fn", "arg", "fn", "arg"]
        stateBinder := 0
        functionOperand := false
        stateOperand := some #["fn", "arg"]
        booleanPredicate := false },
      { path := #["body", "body", "body", "body", "arg", "fn", "arg", "fn", "arg"]
        stateBinder := 0
        functionOperand := false
        stateOperand := some #["fn", "arg"]
        booleanPredicate := false },
      { path := #["body", "body", "body", "body", "arg", "arg", "arg", "arg", "arg", "arg", "fn", "arg", "fn", "arg"]
        stateBinder := 0
        functionOperand := false
        stateOperand := some #["fn", "arg"]
        booleanPredicate := false },
      { path := #["body", "body", "body", "body", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "fn", "arg", "fn", "arg"]
        stateBinder := 0
        functionOperand := false
        stateOperand := some #["fn", "arg"]
        booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Arith.FibonacciAtomic.Dyadic.WhiteboxThreeBatchPhase
