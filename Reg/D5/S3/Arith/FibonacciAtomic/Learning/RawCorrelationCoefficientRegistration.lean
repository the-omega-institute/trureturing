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
open Binomial
namespace Reg.D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities

namespace FairTieNonnegative
abbrev signature : Signature where
  Params := Unit
  State p := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ j => Binomial.fairTie j) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

def sourceStatement : Prop := ∀ (j : ℕ),
    0 ≤ fairTie j
def arena : Arena where
  signature := signature
  Law R := ∀ (j : ℕ),
    0 ≤ R.readout () () j

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h0 := h 0
  change (0 : ℝ) ≤ -1 at h0
  norm_num at h0

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(),0,1,?_⟩
  norm_num [actual, realize, Binomial.fairTie]

def proof_record : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities.Binomial.fair_tie_nonneg, rejected, rejected_law⟩
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
    (@_root_.D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities.Binomial.fair_tie_nonneg)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ _ j => Binomial.fairTie j) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities.Binomial.fair_tie_nonneg.__information_unit,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities.FairTieNonnegative.proof_record,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨proof_record⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ _ j => Binomial.fairTie j) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities,
    definition := none,
    coordinates := #[], readouts := #[{
      path := #["body","arg"],
      stateBinder := 0, functionOperand := false,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }
end FairTieNonnegative

namespace FairTieSquare
abbrev signature : Signature where
  Params := Unit
  State p := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ j => Binomial.fairTie j) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)

def sourceStatement : Prop := ∀ (j : ℕ),
    (fairTie j) ^ 2 ≤ 1 / ((j : ℝ) + 1)
def arena : Arena where
  signature := signature
  Law R := ∀ (j : ℕ),
    (R.readout () () j) ^ 2 ≤ 1 / ((j : ℝ) + 1)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h0 := h 0
  change (2 : ℝ) ^ 2 ≤ _ at h0
  norm_num at h0

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(),0,1,?_⟩
  norm_num [actual, realize, Binomial.fairTie]

def proof_record : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities.Binomial.fair_tie_square_bound, rejected, rejected_law⟩
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
    (@_root_.D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities.Binomial.fair_tie_square_bound)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ _ j => Binomial.fairTie j) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities.Binomial.fair_tie_square_bound.__information_unit,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities.FairTieSquare.proof_record,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨proof_record⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ _ j => Binomial.fairTie j) (fun e => nomatch e)),
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
end FairTieSquare

namespace FairTieLimit
abbrev signature : Signature where
  Params := Unit
  State p := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ j => Binomial.fairTie j) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

def sourceStatement : Prop := Tendsto fairTie atTop (𝓝 (0 : ℝ))
def arena : Arena where
  signature := signature
  Law R := Tendsto (R.readout () ()) atTop (𝓝 (0 : ℝ))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h0 : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 0) := h
  have heq : (1 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds h0
  norm_num at heq

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(),0,1,?_⟩
  norm_num [actual, realize, Binomial.fairTie]

def proof_record : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities.Binomial.fair_tie_vanishes, rejected, rejected_law⟩
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
    (@_root_.D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities.Binomial.fair_tie_vanishes)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ _ j => Binomial.fairTie j) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities.Binomial.fair_tie_vanishes.__information_unit,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities.FairTieLimit.proof_record,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨proof_record⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ _ j => Binomial.fairTie j) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities,
    definition := none,
    coordinates := #[], readouts := #[{
      path := #["fn","fn","arg"],
      stateBinder := 0, functionOperand := true,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }
end FairTieLimit

namespace CleanScoreSigns
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
  realize signature (fun _ a rho => cleanScore rho a 1) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ a rho => cleanScore rho a 1 + 1) (fun e => nomatch e)

def sourceStatement : Prop := ∀ (rho a : ℝ),
    cleanScore rho a 1 = (((8 + a) / 12) * (2 * rho * (1 - 3 * rho) * (1 - 2 * rho)) / (1 - 12 * rho ^ 3)) / 2 ∧
    cleanScore rho a (-1) = (((8 + a) / 12) * (2 * rho * (1 - 3 * rho) * (1 - 2 * rho)) / (1 - 12 * rho ^ 3)) / 2
def arena : Arena where
  signature := signature
  Law R := ∀ (rho a : ℝ),
    R.readout () a rho = (((8 + a) / 12) * (2 * rho * (1 - 3 * rho) * (1 - 2 * rho)) / (1 - 12 * rho ^ 3)) / 2 ∧
    cleanScore rho a (-1) = (((8 + a) / 12) * (2 * rho * (1 - 3 * rho) * (1 - 2 * rho)) / (1 - 12 * rho ^ 3)) / 2

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := (h 0 1).1
  have hg := (clean_score_signs 0 1).1
  change cleanScore 0 1 1 + 1 = _ at hb
  linarith only [hb,hg]

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1,0,1/8,?_⟩
  change cleanScore 0 1 1 ≠ cleanScore (1/8) 1 1
  rw [(clean_score_signs 0 1).1, (clean_score_signs (1/8) 1).1]
  norm_num

def proof_record : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities.Law.clean_score_signs, rejected, rejected_law⟩
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
    (@_root_.D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities.Law.clean_score_signs)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ a rho => cleanScore rho a 1) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities.Law.clean_score_signs.__information_unit,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities.CleanScoreSigns.proof_record,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨proof_record⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ a rho => cleanScore rho a 1) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities,
    definition := none,
    coordinates := #[1], readouts := #[{
      path := #["body","body","fn","arg","fn","arg"],
      stateBinder := 0, functionOperand := false,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }
end CleanScoreSigns

namespace CleanScorePartition
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
  realize signature (fun _ a rho => cleanScore rho a (-1)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ a rho => cleanScore rho a (-1) + 1) (fun e => nomatch e)

def sourceStatement : Prop := ∀ (rho a : ℝ),
    cleanScore rho a (-1) + cleanScore rho a 0 + cleanScore rho a 1 =
      ∑ w, cleanRecordMass rho a w
def arena : Arena where
  signature := signature
  Law R := ∀ (rho a : ℝ),
    R.readout () a rho + cleanScore rho a 0 + cleanScore rho a 1 =
      ∑ w, cleanRecordMass rho a w

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 0 1
  have hg := clean_score_partition 0 1
  change (cleanScore 0 1 (-1) + 1) + cleanScore 0 1 0 + cleanScore 0 1 1 = _ at hb
  linarith only [hb,hg]

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1,0,1/8,?_⟩
  change cleanScore 0 1 (-1) ≠ cleanScore (1/8) 1 (-1)
  rw [(clean_score_signs 0 1).2, (clean_score_signs (1/8) 1).2]
  norm_num

def proof_record : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities.Law.clean_score_partition, rejected, rejected_law⟩
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
    (@_root_.D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities.Law.clean_score_partition)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ a rho => cleanScore rho a (-1)) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities.Law.clean_score_partition.__information_unit,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities.CleanScorePartition.proof_record,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨proof_record⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ a rho => cleanScore rho a (-1)) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities,
    definition := none,
    coordinates := #[1], readouts := #[{
      path := #["body","body","fn","arg","fn","arg","fn","arg"],
      stateBinder := 0, functionOperand := false,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }
end CleanScorePartition

namespace CleanActiveMass
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
  realize signature (fun _ a rho => Scale.activeProbability rho a) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ a rho => Scale.activeProbability rho a + 1) (fun e => nomatch e)

def sourceStatement : Prop := ∀ (rho a : ℝ),
    (∑ w, if score w ≠ 0 then cleanRecordMass rho a w else 0) =
      Scale.activeProbability rho a
def arena : Arena where
  signature := signature
  Law R := ∀ (rho a : ℝ),
    (∑ w, if score w ≠ 0 then cleanRecordMass rho a w else 0) =
      R.readout () a rho

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 0 1
  have hg := clean_active_mass 0 1
  change _ = Scale.activeProbability 0 1 + 1 at hb
  linarith only [hb,hg]

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1,0,1/8,?_⟩
  norm_num [actual, realize, Scale.activeProbability]

def proof_record : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities.Law.clean_active_mass, rejected, rejected_law⟩
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
    (@_root_.D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities.Law.clean_active_mass)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ a rho => Scale.activeProbability rho a) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities.Law.clean_active_mass.__information_unit,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities.CleanActiveMass.proof_record,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨proof_record⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ a rho => Scale.activeProbability rho a) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities,
    definition := none,
    coordinates := #[1], readouts := #[{
      path := #["body","body","arg"],
      stateBinder := 0, functionOperand := false,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }
end CleanActiveMass

namespace DifferenceFormula
abbrev signature : Signature where
  Params := Unit
  State p := Record
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ w => difference w) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)

def sourceStatement : Prop := ∀ (w : Record),
    difference w =
      (HeterogeneousTeacherSeparation.highIndicator w.1 -
        HeterogeneousTeacherSeparation.highIndicator w.2.1) *
      HeterogeneousTeacherSeparation.lowIndicator w.2.2.1 *
      (1 - 2 * HeterogeneousTeacherSeparation.highIndicator w.2.2.1 *
        HeterogeneousTeacherSeparation.lowIndicator w.2.2.2.1)
def arena : Arena where
  signature := signature
  Law R := ∀ (w : Record),
    R.readout () () w =
      (HeterogeneousTeacherSeparation.highIndicator w.1 -
        HeterogeneousTeacherSeparation.highIndicator w.2.1) *
      HeterogeneousTeacherSeparation.lowIndicator w.2.2.1 *
      (1 - 2 * HeterogeneousTeacherSeparation.highIndicator w.2.2.1 *
        HeterogeneousTeacherSeparation.lowIndicator w.2.2.2.1)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h (.zero,.zero,.zero,.zero,1)
  norm_num [arena, rejected, realize, HeterogeneousTeacherSeparation.highIndicator,
    HeterogeneousTeacherSeparation.lowIndicator, first, last] at hb

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (.zero,.zero,.zero,.zero,1), (.high,.zero,.low,.zero,0), ?_⟩
  norm_num [actual, realize, difference, GarbledPosteriorRootGap.teacher, first, last]

def proof_record : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities.Law.difference_formula, rejected, rejected_law⟩
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
    (@_root_.D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities.Law.difference_formula)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ _ w => difference w) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities.Law.difference_formula.__information_unit,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities.DifferenceFormula.proof_record,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨proof_record⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ _ w => difference w) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities,
    definition := none,
    coordinates := #[], readouts := #[{
      path := #["body","fn","arg"],
      stateBinder := 0, functionOperand := false,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }
end DifferenceFormula

end Reg.D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities
