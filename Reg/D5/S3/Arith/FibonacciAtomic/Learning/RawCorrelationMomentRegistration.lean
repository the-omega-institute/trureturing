import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities
import Reg.Support.DependentFamily

open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S3.Arith.FibonacciAtomic
open D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities
open Law Filter LeanInformationAudit
open LiteralWindowEnd (Window first last)
open scoped BigOperators Topology
noncomputable section
attribute [local instance] Classical.propDecidable
set_option quotPrecheck false in
local notation "trueClass" =>
  (fun w : Record => GarbledPosteriorRootGap.teacher (m := 0) ![w.1, w.2.2.1, w.2.2.2.1])
set_option quotPrecheck false in
local notation "rivalClass" =>
  (fun w : Record => GarbledPosteriorRootGap.teacher (m := 0) ![w.2.1, w.2.2.1, w.2.2.2.1])
namespace Reg.D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities

namespace PositionAdmissible
abbrev signature : Signature where
  Params := Unit
  State p := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := HeterogeneousTeacherSeparation.Laws 4
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ rho => positionLaw rho) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => fun _ _ => 0) (fun e => nomatch e)

def sourceStatement : Prop := ∀ (rho : ℝ) (hr : 0 < rho) (hr8 : rho ≤ 1 / 8),
    HeterogeneousTeacherSeparation.Admissible rho (positionLaw rho)
def arena : Arena where
  signature := signature
  Law R := ∀ (rho : ℝ) (hr : 0 < rho) (hr8 : rho ≤ 1 / 8),
    HeterogeneousTeacherSeparation.Admissible rho (R.readout () () rho)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := (h (1/8) (by norm_num) (by norm_num)).1 (0 : Fin 4) Window.zero
  norm_num [rejected, realize] at hb

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(),0,1,?_⟩
  intro h
  have hb := congrFun (congrFun h (0 : Fin 4)) Window.zero
  norm_num [actual, realize, positionLaw, biased] at hb

def proof_record : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities.Law.position_law_admissible, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      cases i
      cases j
      exact (hji rfl).elim
    · intro e; exact nomatch e
  dependence := dependence

def audit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities.Law.position_law_admissible)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ _ rho => positionLaw rho) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities.Law.position_law_admissible.__information_unit,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities.PositionAdmissible.proof_record,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨proof_record⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ _ rho => positionLaw rho) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities,
    definition := none,
    coordinates := #[], readouts := #[{
      path := #["body","body","body","arg"],
      stateBinder := 0, functionOperand := false,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }
end PositionAdmissible

namespace ActualMoments
abbrev signature : Signature where
  Params := ℝ
  State p := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ a rho => expectation rho a (fun w => difference w ^ 2)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def sourceStatement : Prop := ∀ (rho a : ℝ) (hr : 0 < rho) (ha : 0 < a),
    expectation rho a (fun w => difference w ^ 2) = 2 * rho * (1 - 5 * rho + 12 * rho ^ 2) ∧
    expectation rho a (fun w => (((trueClass w).val : ℝ) - 1) ^ 2 -
      (((rivalClass w).val : ℝ) - 1) ^ 2) = -2 * rho + 10 * rho ^ 2 ∧
    expectation rho a (fun w => (score w : ℝ)) = 3 * a * rho ^ 3 ∧
    variance rho a = (8 + a) / 12 * (2 * rho * (1 - 5 * rho + 12 * rho ^ 2)) - 9 * a ^ 2 * rho ^ 6 ∧
    0 < expectation rho a (fun w => (score w : ℝ))
def arena : Arena where
  signature := signature
  Law R := ∀ (rho a : ℝ) (hr : 0 < rho) (ha : 0 < a),
    R.readout () a rho = 2 * rho * (1 - 5 * rho + 12 * rho ^ 2) ∧
    expectation rho a (fun w => (((trueClass w).val : ℝ) - 1) ^ 2 -
      (((rivalClass w).val : ℝ) - 1) ^ 2) = -2 * rho + 10 * rho ^ 2 ∧
    expectation rho a (fun w => (score w : ℝ)) = 3 * a * rho ^ 3 ∧
    variance rho a = (8 + a) / 12 * (2 * rho * (1 - 5 * rho + 12 * rho ^ 2)) - 9 * a ^ 2 * rho ^ 6 ∧
    0 < expectation rho a (fun w => (score w : ℝ))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := (h 1 1 (by norm_num) (by norm_num)).1
  norm_num [rejected, realize] at hb

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1,1,2,?_⟩
  change expectation 1 1 (fun w => difference w ^ 2) ≠ expectation 2 1 (fun w => difference w ^ 2)
  rw [(actual_moments 1 1 (by norm_num) (by norm_num)).1,
    (actual_moments 2 1 (by norm_num) (by norm_num)).1]
  norm_num

def proof_record : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities.Law.actual_moments, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      cases i
      cases j
      exact (hji rfl).elim
    · intro e; exact nomatch e
  dependence := dependence

def audit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities.Law.actual_moments)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ a rho => expectation rho a (fun w => difference w ^ 2)) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities.Law.actual_moments.__information_unit,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities.ActualMoments.proof_record,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨proof_record⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ a rho => expectation rho a (fun w => difference w ^ 2)) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities,
    definition := none,
    coordinates := #[1], readouts := #[{
      path := #["body","body","body","body","fn","arg","fn","arg"],
      stateBinder := 0, functionOperand := false,
      stateOperand := some #["fn", "fn", "arg"], booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }
end ActualMoments

namespace AllCleanLimit
abbrev signature : Signature where
  Params := Σ _ : ℝ, ℝ
  State p := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p rho => ∑ w : Fin (Scale.sampleLength rho p.1 p.2) → Record, if ∀ i, ¬ reverse (w i) then ∏ i, recordMass rho p.1 (w i) else 0) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun i p rho => (fun _ p rho => ∑ w : Fin (Scale.sampleLength rho p.1 p.2) → Record, if ∀ i, ¬ reverse (w i) then ∏ i, recordMass rho p.1 (w i) else 0) i p rho + 1) (fun e => nomatch e)

def sourceStatement : Prop := ∀ (a K : ℝ) (ha : 0 < a) (hK : 0 < K),
    Tendsto (fun rho => ∑ w : Fin (Scale.sampleLength rho a K) → Record,
      if ∀ i, ¬ reverse (w i) then ∏ i, recordMass rho a (w i) else 0)
      (𝓝[>] (0 : ℝ)) (𝓝 1)
def arena : Arena where
  signature := signature
  Law R := ∀ (a K : ℝ) (ha : 0 < a) (hK : 0 < K),
    Tendsto (fun rho => R.readout () ⟨a,K⟩ rho)
      (𝓝[>] (0 : ℝ)) (𝓝 1)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 1 1 (by norm_num) (by norm_num)
  have hg := (all_clean_limit 1 1 (by norm_num) (by norm_num)).add_const (1 : ℝ)
  have heq : (1 : ℝ) = 1 + 1 := tendsto_nhds_unique hb hg
  norm_num at heq

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1,1⟩,0,1,?_⟩
  change (∑ w : Fin (Scale.sampleLength 0 1 1) → Record,
    if ∀ j, ¬ reverse (w j) then ∏ j, recordMass 0 1 (w j) else 0) ≠
    (∑ w : Fin (Scale.sampleLength 1 1 1) → Record,
    if ∀ j, ¬ reverse (w j) then ∏ j, recordMass 1 1 (w j) else 0)
  rw [all_clean_mass, all_clean_mass]
  norm_num [Scale.sampleLength]

def proof_record : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities.Law.all_clean_limit, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      cases i
      cases j
      exact (hji rfl).elim
    · intro e; exact nomatch e
  dependence := dependence

def audit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities.Law.all_clean_limit)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ p rho => ∑ w : Fin (Scale.sampleLength rho p.1 p.2) → Record, if ∀ i, ¬ reverse (w i) then ∏ i, recordMass rho p.1 (w i) else 0) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities.Law.all_clean_limit.__information_unit,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities.AllCleanLimit.proof_record,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨proof_record⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ p rho => ∑ w : Fin (Scale.sampleLength rho p.1 p.2) → Record, if ∀ i, ¬ reverse (w i) then ∏ i, recordMass rho p.1 (w i) else 0) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities,
    definition := none,
    coordinates := #[0,1], readouts := #[{
      path := #["body","body","body","body","fn","fn","arg","body"],
      stateBinder := 4, functionOperand := false,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }
end AllCleanLimit

end Reg.D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities
