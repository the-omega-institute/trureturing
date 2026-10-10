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
namespace Reg.D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities

namespace TotalMass
abbrev signature : Signature where
  Params := Σ _ : ℝ, ℝ
  State p := Record
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p w => recordMass p.1 p.2 w) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def sourceStatement : Prop := ∀ (rho a : ℝ),
    (∑ w, recordMass rho a w) = 1
def arena : Arena where
  signature := signature
  Law R := ∀ (rho a : ℝ),
    (∑ w, R.readout () ⟨rho,a⟩ w) = 1

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h0 := h 0 0
  norm_num [arena, rejected, realize] at h0

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨0,1⟩, (.zero,.zero,.zero,.zero,1), (.high,.zero,.zero,.zero,1), ?_⟩
  norm_num [actual, realize, Law.recordMass, Law.cleanRecordMass, Law.biased,
      HeterogeneousTeacherSeparation.extremal, Law.channel, Law.reverse,
      GarbledPosteriorRootGap.teacher, LiteralWindowEnd.first, LiteralWindowEnd.last]

def proof_record : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities.Law.total_mass, rejected, rejected_law⟩
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
    (@_root_.D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities.Law.total_mass)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ p w => recordMass p.1 p.2 w) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities.Law.total_mass.__information_unit,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities.TotalMass.proof_record,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨proof_record⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ p w => recordMass p.1 p.2 w) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities,
    definition := none,
    coordinates := #[0,1], readouts := #[{
      path := #["body","body","fn","arg","arg","body"],
      stateBinder := 2, functionOperand := false,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }
end TotalMass

namespace RecordNonnegative
abbrev signature : Signature where
  Params := Σ _ : ℝ, ℝ
  State p := Record
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p w => recordMass p.1 p.2 w) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

def sourceStatement : Prop := ∀ (rho a : ℝ) (hr : 0 < rho) (hr8 : rho ≤ 1 / 8)
    (ha : 0 < a) (ha1 : a ≤ 1) (w : Record),
    0 ≤ recordMass rho a w
def arena : Arena where
  signature := signature
  Law R := ∀ (rho a : ℝ) (hr : 0 < rho) (hr8 : rho ≤ 1 / 8)
    (ha : 0 < a) (ha1 : a ≤ 1) (w : Record),
    0 ≤ R.readout () ⟨rho,a⟩ w

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h0 := h (1/8) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (.zero,.zero,.zero,.zero,1)
  norm_num [arena, rejected, realize] at h0

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨0,1⟩, (.zero,.zero,.zero,.zero,1), (.high,.zero,.zero,.zero,1), ?_⟩
  norm_num [actual, realize, Law.recordMass, Law.cleanRecordMass, Law.biased,
      HeterogeneousTeacherSeparation.extremal, Law.channel, Law.reverse,
      GarbledPosteriorRootGap.teacher, LiteralWindowEnd.first, LiteralWindowEnd.last]

def proof_record : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities.Law.record_mass_nonneg, rejected, rejected_law⟩
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
    (@_root_.D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities.Law.record_mass_nonneg)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ p w => recordMass p.1 p.2 w) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities.Law.record_mass_nonneg.__information_unit,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities.RecordNonnegative.proof_record,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨proof_record⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ p w => recordMass p.1 p.2 w) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities,
    definition := none,
    coordinates := #[0,1], readouts := #[{
      path := #["body","body","body","body","body","body","body","arg"],
      stateBinder := 6, functionOperand := false,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }
end RecordNonnegative

namespace CleanRecordNonnegative
abbrev signature : Signature where
  Params := Σ _ : ℝ, ℝ
  State p := Record
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p w => cleanRecordMass p.1 p.2 w) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

def sourceStatement : Prop := ∀ (rho a : ℝ) (hr : 0 < rho) (hr8 : rho ≤ 1 / 8)
    (ha : 0 < a) (ha1 : a ≤ 1) (w : Record),
    0 ≤ cleanRecordMass rho a w
def arena : Arena where
  signature := signature
  Law R := ∀ (rho a : ℝ) (hr : 0 < rho) (hr8 : rho ≤ 1 / 8)
    (ha : 0 < a) (ha1 : a ≤ 1) (w : Record),
    0 ≤ R.readout () ⟨rho,a⟩ w

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h0 := h (1/8) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (.zero,.zero,.zero,.zero,1)
  norm_num [arena, rejected, realize] at h0

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨0,1⟩, (.zero,.zero,.zero,.zero,1), (.high,.zero,.zero,.zero,1), ?_⟩
  norm_num [actual, realize, Law.recordMass, Law.cleanRecordMass, Law.biased,
      HeterogeneousTeacherSeparation.extremal, Law.channel, Law.reverse,
      GarbledPosteriorRootGap.teacher, LiteralWindowEnd.first, LiteralWindowEnd.last]

def proof_record : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities.Law.clean_record_mass_nonneg, rejected, rejected_law⟩
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
    (@_root_.D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities.Law.clean_record_mass_nonneg)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ p w => cleanRecordMass p.1 p.2 w) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities.Law.clean_record_mass_nonneg.__information_unit,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities.CleanRecordNonnegative.proof_record,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨proof_record⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ p w => cleanRecordMass p.1 p.2 w) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities,
    definition := none,
    coordinates := #[0,1], readouts := #[{
      path := #["body","body","body","body","body","body","body","arg"],
      stateBinder := 6, functionOperand := false,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }
end CleanRecordNonnegative

namespace CleanRecordTotal
abbrev signature : Signature where
  Params := Σ _ : ℝ, ℝ
  State p := Record
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p w => cleanRecordMass p.1 p.2 w) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def sourceStatement : Prop := ∀ (rho a : ℝ) (hr : 0 < rho) (hr8 : rho ≤ 1 / 8),
    (∑ w, cleanRecordMass rho a w) = 1
def arena : Arena where
  signature := signature
  Law R := ∀ (rho a : ℝ) (hr : 0 < rho) (hr8 : rho ≤ 1 / 8),
    (∑ w, R.readout () ⟨rho,a⟩ w) = 1

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h0 := h (1/8) 1 (by norm_num) (by norm_num)
  norm_num [arena, rejected, realize] at h0

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨0,1⟩, (.zero,.zero,.zero,.zero,1), (.high,.zero,.zero,.zero,1), ?_⟩
  norm_num [actual, realize, Law.recordMass, Law.cleanRecordMass, Law.biased,
      HeterogeneousTeacherSeparation.extremal, Law.channel, Law.reverse,
      GarbledPosteriorRootGap.teacher, LiteralWindowEnd.first, LiteralWindowEnd.last]

def proof_record : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities.Law.clean_record_mass_total, rejected, rejected_law⟩
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
    (@_root_.D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities.Law.clean_record_mass_total)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ p w => cleanRecordMass p.1 p.2 w) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities.Law.clean_record_mass_total.__information_unit,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities.CleanRecordTotal.proof_record,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨proof_record⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ p w => cleanRecordMass p.1 p.2 w) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities,
    definition := none,
    coordinates := #[0,1], readouts := #[{
      path := #["body","body","body","body","fn","arg","arg","body"],
      stateBinder := 4, functionOperand := false,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }
end CleanRecordTotal

namespace CleanSampleFactor
abbrev signature : Signature where
  Params := Σ _ : ℝ, Σ _ : ℝ, ℕ
  State p := Fin p.2.2 → Record
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p w => cleanSampleMass p.1 p.2.1 w) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def sourceStatement : Prop := ∀ (rho a : ℝ) (m : ℕ) (w : Fin m → Record),
    cleanSampleMass rho a w = ∏ i, cleanRecordMass rho a (w i)
def arena : Arena where
  signature := signature
  Law R := ∀ (rho a : ℝ) (m : ℕ) (w : Fin m → Record),
    R.readout () ⟨rho,a,m⟩ w = ∏ i, cleanRecordMass rho a (w i)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h0 := h 0 1 0 (fun i => Fin.elim0 i)
  norm_num [arena, rejected, realize] at h0

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨0,1,1⟩, (fun _ => (.zero,.zero,.zero,.zero,1)),
    (fun _ => (.high,.zero,.zero,.zero,1)), ?_⟩
  change cleanSampleMass 0 1 _ ≠ cleanSampleMass 0 1 _
  rw [clean_sample_factor, clean_sample_factor]
  norm_num [cleanRecordMass, recordMass, biased, HeterogeneousTeacherSeparation.extremal,
    channel, reverse, GarbledPosteriorRootGap.teacher, first, last]

def proof_record : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities.Law.clean_sample_factor, rejected, rejected_law⟩
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
    (@_root_.D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities.Law.clean_sample_factor)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ p w => cleanSampleMass p.1 p.2.1 w) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities.Law.clean_sample_factor.__information_unit,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities.CleanSampleFactor.proof_record,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨proof_record⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ p w => cleanSampleMass p.1 p.2.1 w) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities,
    definition := none,
    coordinates := #[0,1,2], readouts := #[{
      path := #["body","body","body","body","fn","arg"],
      stateBinder := 3, functionOperand := false,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }
end CleanSampleFactor

namespace CleanDenominator
abbrev signature : Signature where
  Params := Unit
  State p := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ rho => 1 - 12 * rho ^ 3) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def sourceStatement : Prop := ∀ (rho : ℝ) (hr : 0 < rho) (hr8 : rho ≤ 1 / 8),
    0 < 1 - 12 * rho ^ 3
def arena : Arena where
  signature := signature
  Law R := ∀ (rho : ℝ) (hr : 0 < rho) (hr8 : rho ≤ 1 / 8),
    0 < R.readout () () rho

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h0 := h (1/8) (by norm_num) (by norm_num)
  norm_num [arena, rejected, realize] at h0

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(),0,1,?_⟩
  norm_num [actual, realize]

def proof_record : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities.Law.clean_denominator_pos, rejected, rejected_law⟩
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
    (@_root_.D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities.Law.clean_denominator_pos)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ _ rho => 1 - 12 * rho ^ 3) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities.Law.clean_denominator_pos.__information_unit,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities.CleanDenominator.proof_record,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨proof_record⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ _ rho => 1 - 12 * rho ^ 3) (fun e => nomatch e)),
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
end CleanDenominator

namespace AllCleanMass
abbrev signature : Signature where
  Params := ℕ
  State p := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ m rho => (1 - 12 * rho ^ 3) ^ m) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def sourceStatement : Prop := ∀ (rho a : ℝ) (m : ℕ),
    (∑ w : Fin m → Record, if ∀ i, ¬ reverse (w i) then
      ∏ i, recordMass rho a (w i) else 0) = (1 - 12 * rho ^ 3) ^ m
def arena : Arena where
  signature := signature
  Law R := ∀ (rho a : ℝ) (m : ℕ),
    (∑ w : Fin m → Record, if ∀ i, ¬ reverse (w i) then
      ∏ i, recordMass rho a (w i) else 0) = R.readout () m rho

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h0 := h 0 1 0
  have hg := all_clean_mass 0 1 0
  change _ = (0 : ℝ) at h0
  rw [hg] at h0
  norm_num at h0

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1,0,1,?_⟩
  norm_num [actual, realize]

def proof_record : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities.Law.all_clean_mass, rejected, rejected_law⟩
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
    (@_root_.D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities.Law.all_clean_mass)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ m rho => (1 - 12 * rho ^ 3) ^ m) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities.Law.all_clean_mass.__information_unit,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities.AllCleanMass.proof_record,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨proof_record⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ m rho => (1 - 12 * rho ^ 3) ^ m) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities,
    definition := none,
    coordinates := #[2], readouts := #[{
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
end AllCleanMass

namespace ScoreRange
abbrev signature : Signature where
  Params := Unit
  State p := Record
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ w => score w) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)

def sourceStatement : Prop := ∀ (w : Record),
    score w = -1 ∨ score w = 0 ∨ score w = 1
def arena : Arena where
  signature := signature
  Law R := ∀ (w : Record),
    R.readout () () w = -1 ∨ score w = 0 ∨ score w = 1

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h0 := h (.high,.zero,.low,.zero,0)
  norm_num [arena, rejected, realize, score, GarbledPosteriorRootGap.teacher, first, last] at h0

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (.zero,.zero,.zero,.zero,1), (.high,.zero,.low,.zero,0), ?_⟩
  norm_num [actual, realize, score, GarbledPosteriorRootGap.teacher, first, last]

def proof_record : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities.Law.score_range, rejected, rejected_law⟩
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
    (@_root_.D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities.Law.score_range)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ _ w => score w) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities.Law.score_range.__information_unit,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities.ScoreRange.proof_record,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨proof_record⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ _ w => score w) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities,
    definition := none,
    coordinates := #[], readouts := #[{
      path := #["body","fn","arg","fn","arg"],
      stateBinder := 0, functionOperand := false,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }
end ScoreRange

end Reg.D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities
