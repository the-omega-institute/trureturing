import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourthSegmentLengthStability
import Reg.Support.DependentFamily

open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws
open FourthSegmentStoppedLaw FourthSegmentLawRecovery.Length
open NativeConditionalControl.DepthLaw
open _root_.D5.S3.Estimation.DataProcessing.MeasurablePostprocessingDefectContraction
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Topology
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourthSegmentLengthStability
open FourthSegmentLengthStability
abbrev signature : Signature where
  Params := Bool
  State b := if b then ℝ else unitInterval
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ b := if b then ℕ → ℝ × ℝ else Measure RawTail × Measure Stream
  Anchor := Empty
  finiteAnchor := inferInstance

def observations : ∀ b, signature.State b → signature.Output () b
  | false => fun r => (explicitStoppedWordLaw .p r,rawReadLaw r)
  | true => fun (r : ℝ) (j : ℕ) => (r*(r*(1-r))^j,(1-r)^2*(r*(1-r))^j)

def actual : Realization signature :=
  realize signature (fun _ => observations) (fun e => nomatch e)

def rejectedObservations : ∀ b, signature.State b → signature.Output () b
  | false => fun _ => (0,0)
  | true => fun _ _ => (0,0)

def rejected : Realization signature :=
  realize signature (fun _ => rejectedObservations) (fun e => nomatch e)

def wordAt (f : Realization signature) (r : unitInterval) : Measure RawTail :=
  (f.readout () false r).1

def streamAt (f : Realization signature) (r : unitInterval) : Measure Stream :=
  (f.readout () false r).2

def arena : Arena where
  signature := signature
  Law f :=
    (∀ r : unitInterval,
      (streamAt f r).map (fun ω => lengthProjection (stoppedReadWord .p ω)) =
        (wordAt f r).map lengthProjection ∧
      streamAt f r {ω | stoppedReadWord .p ω = none} = 0 ∧
      ((wordAt f r).map lengthProjection) {none} = 0 ∧
      ((wordAt f r).map lengthProjection) {some 0} = 0 ∧
      ∀ j : ℕ,
        (((wordAt f r).map lengthProjection) {some (2*j+1)}).toReal =
          (r:ℝ)*((r:ℝ)*(1-r))^j ∧
        (((wordAt f r).map lengthProjection) {some (2*j+2)}).toReal =
          (1-(r:ℝ))^2*((r:ℝ)*(1-r))^j) ∧
    (∀ r : ℝ, r ∈ Set.Icc (1/3:ℝ) (2/5) →
      Summable (fun j : ℕ =>
        |deriv (fun t : ℝ => (f.readout () true t j).1) r| +
        |deriv (fun t : ℝ => (f.readout () true t j).2) r|) ∧
      (1/2:ℝ)*(∑' j : ℕ,
        (|deriv (fun t : ℝ => (f.readout () true t j).1) r| +
        |deriv (fun t : ℝ => (f.readout () true t j).2) r|)) ≤
        2*(1-r)/(1-r*(1-r)) ∧ 2*(1-r)/(1-r*(1-r)) ≤ 12/7) ∧
    (∀ r s : unitInterval, (r:ℝ) ∈ Set.Icc (1/3:ℝ) (2/5) →
      (s:ℝ) ∈ Set.Icc (1/3:ℝ) (2/5) →
      measurableTotalVariation ((wordAt f r).map lengthProjection)
        ((wordAt f s).map lengthProjection) ≤
        ENNReal.ofReal ((12/7:ℝ)*|(r:ℝ)-(s:ℝ)|)) ∧
    (∀ k : Depth,
      |(rate k:ℝ)-(rate ⟨k.val+1,by omega⟩:ℝ)| =
        1/((Nat.fib (k.val+3):ℝ)*Nat.fib (k.val+4)) ∧
      measurableTotalVariation ((wordAt f (rate k)).map lengthProjection)
        ((wordAt f (rate ⟨k.val+1,by omega⟩)).map lengthProjection) ≤
        ENNReal.ofReal (12/(7*(Nat.fib (k.val+3):ℝ)*Nat.fib (k.val+4)))) ∧
    Tendsto (fun n : ℕ => ENNReal.ofReal
      (12/(7*(Nat.fib (n+4):ℝ)*Nat.fib (n+5)))) atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => measurableTotalVariation
      ((wordAt f (rate ⟨n+1,by omega⟩)).map lengthProjection)
      ((wordAt f (rate ⟨n+2,by omega⟩)).map lengthProjection)) atTop (𝓝 0) ∧
    (∀ k l : Depth, k ≠ l →
      measurableTotalVariation (Measure.dirac k) (Measure.dirac l) = 1)

theorem source_bridge : (type_of% (@original_stopped_length_stability)) ↔ arena.Law actual :=
  Iff.rfl

theorem rejects : ¬ arena.Law rejected := by
  intro h
  have hh := (((h.1 (1 : unitInterval)).2.2.2.2) 0).1
  norm_num [wordAt,rejected,realize,rejectedObservations] at hh

def record : Registration arena (type_of% (@original_stopped_length_stability)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨original_stopped_length_stability,rejected,rejects⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejects⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro i; exact nomatch i
  dependence := by
    intro i
    cases i
    refine ⟨true, (1/3:ℝ), (2/5:ℝ), ?_⟩
    intro he
    have hh := congrArg (fun f : ℕ → ℝ × ℝ => (f 0).1) he
    norm_num [actual,realize,observations] at hh

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@original_stopped_length_stability) (Realization signature) (Type) Unit := {
  unitName := `FourthSegmentLengthStability.original_stopped_length_stability.__information_unit
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourthSegmentLengthStability.record
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨record⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ => observations) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourthSegmentLengthStability
    definition := none
    coordinates := #[]
    readouts := #[
      { path := #["fn","arg","body","fn","arg","arg","arg"],
        stateBinder := 0, functionOperand := false, stateOperand := some #["arg"],
        booleanPredicate := false },
      { path := #["fn","arg","body","fn","arg","fn","arg","arg"],
        stateBinder := 0, functionOperand := false, stateOperand := some #["arg"],
        booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
#print axioms record

end Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourthSegmentLengthStability
