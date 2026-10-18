/- SOURCE_ONLY_UNCOMPILED.
Merged Reg owner candidate for the 19 original public source theorems.
No D5/Scribe bytes changed. Every law below retains the complete literal source
telescope, including implicit binders, hypotheses and all degenerate fibers.
One actual source operand is replaced per target; all other occurrences stay
fixed. Raw Expr paths are proposals, never compiled extraction or binding evidence.
All proof bodies require real elaboration/kernel/axiom/source-binding/Reg/Scribe/CI
acceptance. No RH/Robin, full-Weil positivity or accepted proof claim is made.
-/
import LeanInformationAuditInterface.Contract.Registration
import LeanInformationAuditInterface.Contract.Analysis.Source
import D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare
open D5.S3.Weil.ZetaBridge.WeilArithmeticCouplingJet
open LeanInformationAudit
namespace Reg.D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare

private theorem weight_zero : primeWeight 0 = 0 := by simp [primeWeight]
private theorem weight_one : primeWeight 1 = 0 := by simp [primeWeight]
private theorem weight_two_pos : 0 < primeWeight 2 := by
  unfold primeWeight
  rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
  exact div_pos (Real.log_pos (by norm_num)) (Real.sqrt_pos.mpr (by norm_num))
private theorem indices_two : primeIndices 2 = ∅ := by decide
private theorem indices_three : primeIndices 3 = {2} := by decide
private theorem square_two : primeSquareMass 2 = 0 := by
  simp [primeSquareMass, indices_two]
private theorem cross_two : primeCross 2 = 0 := by
  simp [primeCross, orderedCross, indices_two]
private theorem cross_three : primeCross 3 = 0 := by
  simp [primeCross, orderedCross, indices_three]
private theorem square_three_pos : 0 < primeSquareMass 3 := by
  simpa [primeSquareMass, indices_three] using pow_pos weight_two_pos 2
private theorem symbol_zero (c : ℕ) : primeSymbol c 0 = 0 := by simp [primeSymbol]
private theorem one_not_summable : ¬ Summable (fun _ : ℕ => (1 : ℝ)) := by
  intro hs
  have hz : (1 : ℝ) = 0 :=
    tendsto_nhds_unique tendsto_const_nhds hs.tendsto_atTop_zero
  norm_num at hz

namespace prime_symbol_block
abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ c => primeSquareMass c) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => (-1 : ℝ)) (fun e => nomatch e)

/-- Complete original law with exactly the selected operand replaced. -/
def arena : Arena where
  signature := signature
  Law r := ∀ {c : ℕ} (hc : 2 ≤ c) (M : ℤ) (K : ℕ),
    (∑ j ∈ Finset.range K, primeSymbol c (M + (j : ℤ)) ^ 2) ≤
      (K : ℝ) * r.readout () () c + primeCross c

private theorem actual_law : arena.Law actual := by
  exact @prime_symbol_block
private theorem source_equivalence : (type_of% (@prime_symbol_block)) ↔ arena.Law actual := Iff.rfl
private def source_reconstruction : Analysis.Reconstruction
    (type_of% (@prime_symbol_block)) (arena.Law actual) := .exact

/-- A countermodel to the whole universal law, not a failed fiber alone. -/
private theorem rejected_law : ¬ arena.Law rejected := by
  intro hall
  have h := hall (c := 2) (by decide) (0 : ℤ) 1
  norm_num [rejected, realize, primeSymbol, indices_two, cross_two] at h
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 2, 3, ?_⟩
  change primeSquareMass 2 ≠ primeSquareMass 3
  rw [square_two]
  exact ne_of_lt square_three_pos

def family : Registration arena (type_of% (@prime_symbol_block)) where
  actual := actual
  bridge := source_equivalence
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      cases i
      cases j
      exact (hj rfl).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

/-- PROPOSED raw Expr paths. Compiler acquisition has not run. -/
def selection : Contract.SourceSelection := { owner := `D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare, definition := none, coordinates := #[],
    readouts := #[{ path := #["body", "body", "body", "body", "arg", "fn", "arg", "arg", "fn"],
      stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }
def sourceModel : Analysis.Source (@prime_symbol_block) :=
  Analysis.Source.ofRegistration (@prime_symbol_block) family source_reconstruction selection

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@prime_symbol_block) (type_of% actual) Type Unit := {
  unitName := `Reg.D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare.prime_symbol_block.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare.prime_symbol_block.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ c => primeSquareMass c) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (ℕ)
  sourceSelection := some { owner := `D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare, definition := none, coordinates := #[],
    readouts := #[{ path := #["body", "body", "body", "body", "arg", "fn", "arg", "arg", "fn"],
      stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end prime_symbol_block

namespace finite_abel_majorant
abbrev signature : Signature where
  Params := (ℕ → ℝ)
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ w i => w i) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => (-1 : ℝ)) (fun e => nomatch e)

/-- Complete original law with exactly the selected operand replaced. -/
def arena : Arena where
  signature := signature
  Law r := ∀ (x w : ℕ → ℝ) (D C : ℝ)
    (hC : 0 ≤ C) (hw : ∀ i, 0 ≤ w i) (hanti : ∀ i, w (i + 1) ≤ w i)
    (hA : ∀ K, (∑ i ∈ Finset.range K, x i) ≤ (K : ℝ) * D + C) (K : ℕ),
    (∑ i ∈ Finset.range K, x i * w i) ≤
      D * (∑ i ∈ Finset.range K, r.readout () w i) + C * w 0

private theorem actual_law : arena.Law actual := by
  exact @finite_abel_majorant
private theorem source_equivalence : (type_of% (@finite_abel_majorant)) ↔ arena.Law actual := Iff.rfl
private def source_reconstruction : Analysis.Reconstruction
    (type_of% (@finite_abel_majorant)) (arena.Law actual) := .exact

/-- A countermodel to the whole universal law, not a failed fiber alone. -/
private theorem rejected_law : ¬ arena.Law rejected := by
  intro hall
  have h := hall (fun _ => 0) (fun _ => 1) 1 0 (by norm_num)
    (fun _ => by norm_num) (fun _ => le_rfl)
    (fun K => by simp; positivity) 1
  norm_num [rejected, realize] at h
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(fun n : ℕ => (n : ℝ)), 0, 1, ?_⟩
  norm_num [actual, realize]

def family : Registration arena (type_of% (@finite_abel_majorant)) where
  actual := actual
  bridge := source_equivalence
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      cases i
      cases j
      exact (hj rfl).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

/-- PROPOSED raw Expr paths. Compiler acquisition has not run. -/
def selection : Contract.SourceSelection := { owner := `D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare, definition := none, coordinates := #[1],
    readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg", "arg", "arg", "body", "fn"],
      stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }
def sourceModel : Analysis.Source (@finite_abel_majorant) :=
  Analysis.Source.ofRegistration (@finite_abel_majorant) family source_reconstruction selection

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@finite_abel_majorant) (type_of% actual) Type Unit := {
  unitName := `Reg.D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare.finite_abel_majorant.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare.finite_abel_majorant.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ w i => w i) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (ℕ)
  sourceSelection := some { owner := `D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare, definition := none, coordinates := #[1],
    readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg", "arg", "arg", "body", "fn"],
      stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end finite_abel_majorant

namespace prime_symbol_square_tail
abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ c M => primeTailBudget c M) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => (-1 : ℝ)) (fun e => nomatch e)

/-- Complete original law with exactly the selected operand replaced. -/
def arena : Arena where
  signature := signature
  Law r := ∀ {c M : ℕ} (hc : 2 ≤ c) (hM : 0 < M),
    Summable (fun j : ℕ =>
      primeSymbol c ((M + j + 1 : ℕ) : ℤ) ^ 2 * inverseSquareWeight M j) ∧
    (∑' j : ℕ, primeSymbol c ((M + j + 1 : ℕ) : ℤ) ^ 2 * inverseSquareWeight M j) ≤
      r.readout () c M

private theorem actual_law : arena.Law actual := by
  exact @prime_symbol_square_tail
private theorem source_equivalence : (type_of% (@prime_symbol_square_tail)) ↔ arena.Law actual := Iff.rfl
private def source_reconstruction : Analysis.Reconstruction
    (type_of% (@prime_symbol_square_tail)) (arena.Law actual) := .exact

/-- A countermodel to the whole universal law, not a failed fiber alone. -/
private theorem rejected_law : ¬ arena.Law rejected := by
  intro hall
  have h := (hall (c := 2) (M := 1) (by decide) (by decide)).2
  norm_num [rejected, realize, primeSymbol, indices_two] at h
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨3, 0, 1, ?_⟩
  change primeTailBudget 3 0 ≠ primeTailBudget 3 1
  simpa [primeTailBudget, cross_three] using
    (ne_of_lt square_three_pos : (0 : ℝ) ≠ primeSquareMass 3)

def family : Registration arena (type_of% (@prime_symbol_square_tail)) where
  actual := actual
  bridge := source_equivalence
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      cases i
      cases j
      exact (hj rfl).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

/-- PROPOSED raw Expr paths. Compiler acquisition has not run. -/
def selection : Contract.SourceSelection := { owner := `D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare, definition := none, coordinates := #[0],
    readouts := #[{ path := #["body", "body", "body", "body", "arg", "arg", "fn"],
      stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }
def sourceModel : Analysis.Source (@prime_symbol_square_tail) :=
  Analysis.Source.ofRegistration (@prime_symbol_square_tail) family source_reconstruction selection

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@prime_symbol_square_tail) (type_of% actual) Type Unit := {
  unitName := `Reg.D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare.prime_symbol_square_tail.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare.prime_symbol_square_tail.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ c M => primeTailBudget c M) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (ℕ)
  sourceSelection := some { owner := `D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare, definition := none, coordinates := #[0],
    readouts := #[{ path := #["body", "body", "body", "body", "arg", "arg", "fn"],
      stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end prime_symbol_square_tail

namespace canonical_first_jet_prime_tail
abbrev signature : Signature where
  Params := Unit
  State _ := ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ z => ‖z‖) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => (1 : ℝ)) (fun e => nomatch e)

/-- Complete original law with exactly the selected operand replaced. -/
def arena : Arena where
  signature := signature
  Law r := ∀ {c M : ℕ} (hc : 2 ≤ c) (hM : 0 < M)
    (S : Finset ℤ) (v : ℤ → ℂ),
    Summable (fun k : ℕ => r.readout () () (canonicalPrimeFirstJetFar c S v ((M + k + 1 : ℕ) : ℤ)) ^ 2) ∧
    (∑' k : ℕ, ‖canonicalPrimeFirstJetFar c S v ((M + k + 1 : ℕ) : ℤ)‖ ^ 2) ≤
      (‖∑ n ∈ S, v n‖ ^ 2 / Real.pi ^ 2) *
        (primeSquareMass c / (M : ℝ) + primeCross c / ((M : ℝ) + 1) ^ 2)

private theorem actual_law : arena.Law actual := by
  exact @canonical_first_jet_prime_tail
private theorem source_equivalence : (type_of% (@canonical_first_jet_prime_tail)) ↔ arena.Law actual := Iff.rfl
private def source_reconstruction : Analysis.Reconstruction
    (type_of% (@canonical_first_jet_prime_tail)) (arena.Law actual) := .exact

/-- A countermodel to the whole universal law, not a failed fiber alone. -/
private theorem rejected_law : ¬ arena.Law rejected := by
  intro hall
  have hs := (hall (c := 2) (M := 1) (by decide) (by decide) ∅ (fun _ => 0)).1
  exact one_not_summable (by simpa [rejected, realize] using hs)
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0 : ℂ), (1 : ℂ), ?_⟩
  norm_num [actual, realize]

def family : Registration arena (type_of% (@canonical_first_jet_prime_tail)) where
  actual := actual
  bridge := source_equivalence
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      cases i
      cases j
      exact (hj rfl).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

/-- PROPOSED raw Expr paths. Compiler acquisition has not run. -/
def selection : Contract.SourceSelection := { owner := `D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare, definition := none, coordinates := #[],
    readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "arg", "body", "fn", "arg", "fn"],
      stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }
def sourceModel : Analysis.Source (@canonical_first_jet_prime_tail) :=
  Analysis.Source.ofRegistration (@canonical_first_jet_prime_tail) family source_reconstruction selection

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@canonical_first_jet_prime_tail) (type_of% actual) Type Unit := {
  unitName := `Reg.D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare.canonical_first_jet_prime_tail.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare.canonical_first_jet_prime_tail.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => ‖z‖) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (ℂ)
  sourceSelection := some { owner := `D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare, definition := none, coordinates := #[],
    readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "arg", "body", "fn", "arg", "fn"],
      stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end canonical_first_jet_prime_tail

namespace logLength_pos
abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ c => logLength c) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => (-1 : ℝ)) (fun e => nomatch e)

/-- Complete original law with exactly the selected operand replaced. -/
def arena : Arena where
  signature := signature
  Law r := ∀ {c : ℕ} (hc : 2 ≤ c),
    0 < r.readout () () c

private theorem actual_law : arena.Law actual := by
  exact @logLength_pos
private theorem source_equivalence : (type_of% (@logLength_pos)) ↔ arena.Law actual := Iff.rfl
private def source_reconstruction : Analysis.Reconstruction
    (type_of% (@logLength_pos)) (arena.Law actual) := .exact

/-- A countermodel to the whole universal law, not a failed fiber alone. -/
private theorem rejected_law : ¬ arena.Law rejected := by
  intro hall
  have h := hall (c := 2) (by decide)
  change (0 : ℝ) < -1 at h
  norm_num at h
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 1, 2, ?_⟩
  change logLength 1 ≠ logLength 2
  simp only [logLength, Nat.cast_one, Real.log_one]
  exact ne_of_lt (Real.log_pos (by norm_num))

def family : Registration arena (type_of% (@logLength_pos)) where
  actual := actual
  bridge := source_equivalence
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      cases i
      cases j
      exact (hj rfl).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

/-- PROPOSED raw Expr paths. Compiler acquisition has not run. -/
def selection : Contract.SourceSelection := { owner := `D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare, definition := none, coordinates := #[],
    readouts := #[{ path := #["body", "body", "arg", "fn"],
      stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }
def sourceModel : Analysis.Source (@logLength_pos) :=
  Analysis.Source.ofRegistration (@logLength_pos) family source_reconstruction selection

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@logLength_pos) (type_of% actual) Type Unit := {
  unitName := `Reg.D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare.logLength_pos.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare.logLength_pos.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ c => logLength c) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (ℕ)
  sourceSelection := some { owner := `D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare, definition := none, coordinates := #[],
    readouts := #[{ path := #["body", "body", "arg", "fn"],
      stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end logLength_pos

namespace phase_geometry
abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ c q => theta c q) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => (-1 : ℝ)) (fun e => nomatch e)

/-- Complete original law with exactly the selected operand replaced. -/
def arena : Arena where
  signature := signature
  Law r := ∀ {c q : ℕ} (hc : 2 ≤ c) (hq : q ∈ primeIndices c),
    0 < r.readout () c q ∧ theta c q < 1

private theorem actual_law : arena.Law actual := by
  exact @phase_geometry
private theorem source_equivalence : (type_of% (@phase_geometry)) ↔ arena.Law actual := Iff.rfl
private def source_reconstruction : Analysis.Reconstruction
    (type_of% (@phase_geometry)) (arena.Law actual) := .exact

/-- A countermodel to the whole universal law, not a failed fiber alone. -/
private theorem rejected_law : ¬ arena.Law rejected := by
  intro hall
  have h := (hall (c := 3) (q := 2) (by decide) (by decide)).1
  change (0 : ℝ) < -1 at h
  norm_num at h
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨2, 1, 2, ?_⟩
  have hlog : Real.log (2 : ℝ) ≠ 0 := (Real.log_pos (by norm_num)).ne'
  norm_num [actual, realize, theta, logLength, hlog]

def family : Registration arena (type_of% (@phase_geometry)) where
  actual := actual
  bridge := source_equivalence
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      cases i
      cases j
      exact (hj rfl).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

/-- PROPOSED raw Expr paths. Compiler acquisition has not run. -/
def selection : Contract.SourceSelection := { owner := `D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare, definition := none, coordinates := #[0],
    readouts := #[{ path := #["body", "body", "body", "body", "fn", "arg", "arg", "fn"],
      stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }
def sourceModel : Analysis.Source (@phase_geometry) :=
  Analysis.Source.ofRegistration (@phase_geometry) family source_reconstruction selection

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@phase_geometry) (type_of% actual) Type Unit := {
  unitName := `Reg.D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare.phase_geometry.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare.phase_geometry.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ c q => theta c q) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (ℕ)
  sourceSelection := some { owner := `D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare, definition := none, coordinates := #[0],
    readouts := #[{ path := #["body", "body", "body", "body", "fn", "arg", "arg", "fn"],
      stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end phase_geometry

namespace primePhase_norm
abbrev signature : Signature where
  Params := Unit
  State _ := ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ z => ‖z‖) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => (0 : ℝ)) (fun e => nomatch e)

/-- Complete original law with exactly the selected operand replaced. -/
def arena : Arena where
  signature := signature
  Law r := ∀ (c q : ℕ),
    r.readout () () (primePhase c q) = 1

private theorem actual_law : arena.Law actual := by
  exact @primePhase_norm
private theorem source_equivalence : (type_of% (@primePhase_norm)) ↔ arena.Law actual := Iff.rfl
private def source_reconstruction : Analysis.Reconstruction
    (type_of% (@primePhase_norm)) (arena.Law actual) := .exact

/-- A countermodel to the whole universal law, not a failed fiber alone. -/
private theorem rejected_law : ¬ arena.Law rejected := by
  intro hall
  have h := hall 0 0
  norm_num [rejected, realize] at h
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0 : ℂ), (1 : ℂ), ?_⟩
  norm_num [actual, realize]

def family : Registration arena (type_of% (@primePhase_norm)) where
  actual := actual
  bridge := source_equivalence
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      cases i
      cases j
      exact (hj rfl).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

/-- PROPOSED raw Expr paths. Compiler acquisition has not run. -/
def selection : Contract.SourceSelection := { owner := `D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare, definition := none, coordinates := #[],
    readouts := #[{ path := #["body", "body", "fn", "arg", "fn"],
      stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }
def sourceModel : Analysis.Source (@primePhase_norm) :=
  Analysis.Source.ofRegistration (@primePhase_norm) family source_reconstruction selection

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@primePhase_norm) (type_of% actual) Type Unit := {
  unitName := `Reg.D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare.primePhase_norm.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare.primePhase_norm.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => ‖z‖) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (ℂ)
  sourceSelection := some { owner := `D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare, definition := none, coordinates := #[],
    readouts := #[{ path := #["body", "body", "fn", "arg", "fn"],
      stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end primePhase_norm

namespace primePhase_noncollision
abbrev signature : Signature where
  Params := Unit
  State _ := ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ z => conj z) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => (primePhase 4 2)⁻¹) (fun e => nomatch e)

/-- Complete original law with exactly the selected operand replaced. -/
def arena : Arena where
  signature := signature
  Law r := ∀ {c p q : ℕ} (hc : 2 ≤ c)
    (hp : p ∈ primeIndices c) (hq : q ∈ primeIndices c) (hpq : p ≠ q),
    primePhase c p * r.readout () () (primePhase c q) ≠ 1

private theorem actual_law : arena.Law actual := by
  exact @primePhase_noncollision
private theorem source_equivalence : (type_of% (@primePhase_noncollision)) ↔ arena.Law actual := Iff.rfl
private def source_reconstruction : Analysis.Reconstruction
    (type_of% (@primePhase_noncollision)) (arena.Law actual) := .exact

/-- A countermodel to the whole universal law, not a failed fiber alone. -/
private theorem rejected_law : ¬ arena.Law rejected := by
  intro hall
  have h := hall (c := 4) (p := 2) (q := 3)
    (by decide) (by decide) (by decide) (by decide)
  have hz : primePhase 4 2 ≠ 0 := by
    intro he
    have hn := primePhase_norm 4 2
    rw [he, norm_zero] at hn
    norm_num at hn
  apply h
  change primePhase 4 2 * (primePhase 4 2)⁻¹ = 1
  exact mul_inv_cancel₀ hz
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0 : ℂ), (1 : ℂ), ?_⟩
  norm_num [actual, realize]

def family : Registration arena (type_of% (@primePhase_noncollision)) where
  actual := actual
  bridge := source_equivalence
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      cases i
      cases j
      exact (hj rfl).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

/-- PROPOSED raw Expr paths. Compiler acquisition has not run. -/
def selection : Contract.SourceSelection := { owner := `D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare, definition := none, coordinates := #[],
    readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg", "fn"],
      stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }
def sourceModel : Analysis.Source (@primePhase_noncollision) :=
  Analysis.Source.ofRegistration (@primePhase_noncollision) family source_reconstruction selection

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@primePhase_noncollision) (type_of% actual) Type Unit := {
  unitName := `Reg.D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare.primePhase_noncollision.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare.primePhase_noncollision.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => conj z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (ℂ)
  sourceSelection := some { owner := `D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare, definition := none, coordinates := #[],
    readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg", "fn"],
      stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end primePhase_noncollision

namespace owner_term_cutoff
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x => Real.sin x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => (1 : ℝ)) (fun e => nomatch e)

/-- Complete original law with exactly the selected operand replaced. -/
def arena : Arena where
  signature := signature
  Law r := ∀ {c : ℕ} (hc : 2 ≤ c) (m : ℤ),
    primeWeight c * r.readout () () (frequency c m * Real.log (c : ℝ)) = 0

private theorem actual_law : arena.Law actual := by
  exact @owner_term_cutoff
private theorem source_equivalence : (type_of% (@owner_term_cutoff)) ↔ arena.Law actual := Iff.rfl
private def source_reconstruction : Analysis.Reconstruction
    (type_of% (@owner_term_cutoff)) (arena.Law actual) := .exact

/-- A countermodel to the whole universal law, not a failed fiber alone. -/
private theorem rejected_law : ¬ arena.Law rejected := by
  intro hall
  have h := hall (c := 2) (by decide) (0 : ℤ)
  have he : primeWeight 2 = 0 := by simpa [rejected, realize] using h
  exact weight_two_pos.ne' he
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0 : ℝ), Real.pi / 2, ?_⟩
  norm_num [actual, realize, Real.sin_pi_div_two]

def family : Registration arena (type_of% (@owner_term_cutoff)) where
  actual := actual
  bridge := source_equivalence
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      cases i
      cases j
      exact (hj rfl).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

/-- PROPOSED raw Expr paths. Compiler acquisition has not run. -/
def selection : Contract.SourceSelection := { owner := `D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare, definition := none, coordinates := #[],
    readouts := #[{ path := #["body", "body", "body", "fn", "arg", "arg", "fn"],
      stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }
def sourceModel : Analysis.Source (@owner_term_cutoff) :=
  Analysis.Source.ofRegistration (@owner_term_cutoff) family source_reconstruction selection

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@owner_term_cutoff) (type_of% actual) Type Unit := {
  unitName := `Reg.D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare.owner_term_cutoff.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare.owner_term_cutoff.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => Real.sin x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (ℝ)
  sourceSelection := some { owner := `D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare, definition := none, coordinates := #[],
    readouts := #[{ path := #["body", "body", "body", "fn", "arg", "arg", "fn"],
      stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end owner_term_cutoff

namespace owner_prime_sum_eq
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x => Real.sin x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => (1 : ℝ)) (fun e => nomatch e)

/-- Complete original law with exactly the selected operand replaced. -/
def arena : Arena where
  signature := signature
  Law r := ∀ (c : ℕ) (m : ℤ),
    (∑ q ∈ Finset.range c, primeWeight q * r.readout () () (frequency c m * Real.log (q : ℝ))) =
      primeSymbol c m

private theorem actual_law : arena.Law actual := by
  exact @owner_prime_sum_eq
private theorem source_equivalence : (type_of% (@owner_prime_sum_eq)) ↔ arena.Law actual := Iff.rfl
private def source_reconstruction : Analysis.Reconstruction
    (type_of% (@owner_prime_sum_eq)) (arena.Law actual) := .exact

/-- A countermodel to the whole universal law, not a failed fiber alone. -/
private theorem rejected_law : ¬ arena.Law rejected := by
  intro hall
  have h := hall 3 (0 : ℤ)
  have he : primeWeight 2 = 0 := by
    simpa [rejected, realize, Finset.sum_range_succ, weight_zero, weight_one, symbol_zero] using h
  exact weight_two_pos.ne' he
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0 : ℝ), Real.pi / 2, ?_⟩
  norm_num [actual, realize, Real.sin_pi_div_two]

def family : Registration arena (type_of% (@owner_prime_sum_eq)) where
  actual := actual
  bridge := source_equivalence
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      cases i
      cases j
      exact (hj rfl).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

/-- PROPOSED raw Expr paths. Compiler acquisition has not run. -/
def selection : Contract.SourceSelection := { owner := `D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare, definition := none, coordinates := #[],
    readouts := #[{ path := #["body", "body", "fn", "arg", "arg", "body", "arg", "fn"],
      stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }
def sourceModel : Analysis.Source (@owner_prime_sum_eq) :=
  Analysis.Source.ofRegistration (@owner_prime_sum_eq) family source_reconstruction selection

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@owner_prime_sum_eq) (type_of% actual) Type Unit := {
  unitName := `Reg.D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare.owner_prime_sum_eq.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare.owner_prime_sum_eq.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => Real.sin x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (ℝ)
  sourceSelection := some { owner := `D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare, definition := none, coordinates := #[],
    readouts := #[{ path := #["body", "body", "fn", "arg", "arg", "body", "arg", "fn"],
      stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end owner_prime_sum_eq

namespace owner_prime_sum_inclusive
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x => Real.sin x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => (1 : ℝ)) (fun e => nomatch e)

/-- Complete original law with exactly the selected operand replaced. -/
def arena : Arena where
  signature := signature
  Law r := ∀ {c : ℕ} (hc : 2 ≤ c) (m : ℤ),
    (∑ q ∈ Finset.range (c + 1), primeWeight q * r.readout () () (frequency c m * Real.log (q : ℝ))) =
      primeSymbol c m

private theorem actual_law : arena.Law actual := by
  exact @owner_prime_sum_inclusive
private theorem source_equivalence : (type_of% (@owner_prime_sum_inclusive)) ↔ arena.Law actual := Iff.rfl
private def source_reconstruction : Analysis.Reconstruction
    (type_of% (@owner_prime_sum_inclusive)) (arena.Law actual) := .exact

/-- A countermodel to the whole universal law, not a failed fiber alone. -/
private theorem rejected_law : ¬ arena.Law rejected := by
  intro hall
  have h := hall (c := 2) (by decide) (0 : ℤ)
  have he : primeWeight 2 = 0 := by
    simpa [rejected, realize, Finset.sum_range_succ, weight_zero, weight_one, symbol_zero] using h
  exact weight_two_pos.ne' he
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0 : ℝ), Real.pi / 2, ?_⟩
  norm_num [actual, realize, Real.sin_pi_div_two]

def family : Registration arena (type_of% (@owner_prime_sum_inclusive)) where
  actual := actual
  bridge := source_equivalence
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      cases i
      cases j
      exact (hj rfl).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

/-- PROPOSED raw Expr paths. Compiler acquisition has not run. -/
def selection : Contract.SourceSelection := { owner := `D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare, definition := none, coordinates := #[],
    readouts := #[{ path := #["body", "body", "body", "fn", "arg", "arg", "body", "arg", "fn"],
      stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }
def sourceModel : Analysis.Source (@owner_prime_sum_inclusive) :=
  Analysis.Source.ofRegistration (@owner_prime_sum_inclusive) family source_reconstruction selection

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@owner_prime_sum_inclusive) (type_of% actual) Type Unit := {
  unitName := `Reg.D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare.owner_prime_sum_inclusive.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare.owner_prime_sum_inclusive.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => Real.sin x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (ℝ)
  sourceSelection := some { owner := `D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare, definition := none, coordinates := #[],
    readouts := #[{ path := #["body", "body", "body", "fn", "arg", "arg", "body", "arg", "fn"],
      stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end owner_prime_sum_inclusive

namespace primeSymbol_is_im
abbrev signature : Signature where
  Params := Unit
  State _ := ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ z => z.im) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => (1 : ℝ)) (fun e => nomatch e)

/-- Complete original law with exactly the selected operand replaced. -/
def arena : Arena where
  signature := signature
  Law r := ∀ (c : ℕ) (m : ℤ),
    primeSymbol c m =
      r.readout () () (∑ q ∈ primeIndices c, (primeWeight q : ℂ) * primePhase c q ^ m)

private theorem actual_law : arena.Law actual := by
  exact @primeSymbol_is_im
private theorem source_equivalence : (type_of% (@primeSymbol_is_im)) ↔ arena.Law actual := Iff.rfl
private def source_reconstruction : Analysis.Reconstruction
    (type_of% (@primeSymbol_is_im)) (arena.Law actual) := .exact

/-- A countermodel to the whole universal law, not a failed fiber alone. -/
private theorem rejected_law : ¬ arena.Law rejected := by
  intro hall
  have h := hall 2 (0 : ℤ)
  norm_num [rejected, realize, primeSymbol, indices_two] at h
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0 : ℂ), Complex.I, ?_⟩
  norm_num [actual, realize]

def family : Registration arena (type_of% (@primeSymbol_is_im)) where
  actual := actual
  bridge := source_equivalence
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      cases i
      cases j
      exact (hj rfl).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

/-- PROPOSED raw Expr paths. Compiler acquisition has not run. -/
def selection : Contract.SourceSelection := { owner := `D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare, definition := none, coordinates := #[],
    readouts := #[{ path := #["body", "body", "arg", "fn"],
      stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }
def sourceModel : Analysis.Source (@primeSymbol_is_im) :=
  Analysis.Source.ofRegistration (@primeSymbol_is_im) family source_reconstruction selection

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@primeSymbol_is_im) (type_of% actual) Type Unit := {
  unitName := `Reg.D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare.primeSymbol_is_im.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare.primeSymbol_is_im.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => z.im) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (ℂ)
  sourceSelection := some { owner := `D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare, definition := none, coordinates := #[],
    readouts := #[{ path := #["body", "body", "arg", "fn"],
      stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end primeSymbol_is_im

namespace geometric_block_norm
abbrev signature : Signature where
  Params := Unit
  State _ := ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ z => ‖z‖) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => (3 : ℝ)) (fun e => nomatch e)

/-- Complete original law with exactly the selected operand replaced. -/
def arena : Arena where
  signature := signature
  Law r := ∀ {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1)
    (M : ℤ) (K : ℕ),
    r.readout () () (∑ j ∈ Finset.range K, z ^ (M + (j : ℤ))) ≤ 2 / ‖1 - z‖

private theorem actual_law : arena.Law actual := by
  exact @geometric_block_norm
private theorem source_equivalence : (type_of% (@geometric_block_norm)) ↔ arena.Law actual := Iff.rfl
private def source_reconstruction : Analysis.Reconstruction
    (type_of% (@geometric_block_norm)) (arena.Law actual) := .exact

/-- A countermodel to the whole universal law, not a failed fiber alone. -/
private theorem rejected_law : ¬ arena.Law rejected := by
  intro hall
  have h := hall (z := (-1 : ℂ)) (by norm_num) (by norm_num) (0 : ℤ) 0
  norm_num [rejected, realize] at h
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0 : ℂ), (1 : ℂ), ?_⟩
  norm_num [actual, realize]

def family : Registration arena (type_of% (@geometric_block_norm)) where
  actual := actual
  bridge := source_equivalence
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      cases i
      cases j
      exact (hj rfl).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

/-- PROPOSED raw Expr paths. Compiler acquisition has not run. -/
def selection : Contract.SourceSelection := { owner := `D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare, definition := none, coordinates := #[],
    readouts := #[{ path := #["body", "body", "body", "body", "body", "fn", "arg", "fn"],
      stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }
def sourceModel : Analysis.Source (@geometric_block_norm) :=
  Analysis.Source.ofRegistration (@geometric_block_norm) family source_reconstruction selection

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@geometric_block_norm) (type_of% actual) Type Unit := {
  unitName := `Reg.D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare.geometric_block_norm.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare.geometric_block_norm.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => ‖z‖) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (ℂ)
  sourceSelection := some { owner := `D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare, definition := none, coordinates := #[],
    readouts := #[{ path := #["body", "body", "body", "body", "body", "fn", "arg", "fn"],
      stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end geometric_block_norm

namespace norm_square_expansion
abbrev signature : Signature where
  Params := Unit
  State _ := ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ z => ‖z‖) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => (1 : ℝ)) (fun e => nomatch e)

/-- Complete original law with exactly the selected operand replaced. -/
def arena : Arena where
  signature := signature
  Law r := ∀ (s : Finset ℕ) (a : ℕ → ℝ) (z : ℕ → ℂ) (m : ℤ),
    r.readout () () (∑ p ∈ s, (a p : ℂ) * z p ^ m) ^ 2 =
      ∑ p ∈ s, ∑ q ∈ s, (((a p * a q : ℝ) : ℂ) * (z p * conj (z q)) ^ m).re

private theorem actual_law : arena.Law actual := by
  exact @norm_square_expansion
private theorem source_equivalence : (type_of% (@norm_square_expansion)) ↔ arena.Law actual := Iff.rfl
private def source_reconstruction : Analysis.Reconstruction
    (type_of% (@norm_square_expansion)) (arena.Law actual) := .exact

/-- A countermodel to the whole universal law, not a failed fiber alone. -/
private theorem rejected_law : ¬ arena.Law rejected := by
  intro hall
  have h := hall ∅ (fun _ => 0) (fun _ => 0) (0 : ℤ)
  norm_num [rejected, realize] at h
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0 : ℂ), (1 : ℂ), ?_⟩
  norm_num [actual, realize]

def family : Registration arena (type_of% (@norm_square_expansion)) where
  actual := actual
  bridge := source_equivalence
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      cases i
      cases j
      exact (hj rfl).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

/-- PROPOSED raw Expr paths. Compiler acquisition has not run. -/
def selection : Contract.SourceSelection := { owner := `D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare, definition := none, coordinates := #[],
    readouts := #[{ path := #["body", "body", "body", "body", "fn", "arg", "fn", "arg", "fn"],
      stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }
def sourceModel : Analysis.Source (@norm_square_expansion) :=
  Analysis.Source.ofRegistration (@norm_square_expansion) family source_reconstruction selection

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@norm_square_expansion) (type_of% actual) Type Unit := {
  unitName := `Reg.D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare.norm_square_expansion.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare.norm_square_expansion.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => ‖z‖) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (ℂ)
  sourceSelection := some { owner := `D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare, definition := none, coordinates := #[],
    readouts := #[{ path := #["body", "body", "body", "body", "fn", "arg", "fn", "arg", "fn"],
      stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end norm_square_expansion

namespace inverseSquareWeight_antitone
abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ M j => inverseSquareWeight M j) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => (1 : ℝ)) (fun e => nomatch e)

/-- Complete original law with exactly the selected operand replaced. -/
def arena : Arena where
  signature := signature
  Law r := ∀ {M : ℕ} (hM : 0 < M) (i : ℕ),
    r.readout () M (i + 1) ≤ inverseSquareWeight M i

private theorem actual_law : arena.Law actual := by
  exact @inverseSquareWeight_antitone
private theorem source_equivalence : (type_of% (@inverseSquareWeight_antitone)) ↔ arena.Law actual := Iff.rfl
private def source_reconstruction : Analysis.Reconstruction
    (type_of% (@inverseSquareWeight_antitone)) (arena.Law actual) := .exact

/-- A countermodel to the whole universal law, not a failed fiber alone. -/
private theorem rejected_law : ¬ arena.Law rejected := by
  intro hall
  have h := hall (M := 1) (by decide) 0
  norm_num [rejected, realize, inverseSquareWeight] at h
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 0, 1, ?_⟩
  norm_num [actual, realize, inverseSquareWeight]

def family : Registration arena (type_of% (@inverseSquareWeight_antitone)) where
  actual := actual
  bridge := source_equivalence
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      cases i
      cases j
      exact (hj rfl).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

/-- PROPOSED raw Expr paths. Compiler acquisition has not run. -/
def selection : Contract.SourceSelection := { owner := `D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare, definition := none, coordinates := #[0],
    readouts := #[{ path := #["body", "body", "body", "fn", "arg", "fn"],
      stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }
def sourceModel : Analysis.Source (@inverseSquareWeight_antitone) :=
  Analysis.Source.ofRegistration (@inverseSquareWeight_antitone) family source_reconstruction selection

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@inverseSquareWeight_antitone) (type_of% actual) Type Unit := {
  unitName := `Reg.D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare.inverseSquareWeight_antitone.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare.inverseSquareWeight_antitone.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ M j => inverseSquareWeight M j) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (ℕ)
  sourceSelection := some { owner := `D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare, definition := none, coordinates := #[0],
    readouts := #[{ path := #["body", "body", "body", "fn", "arg", "fn"],
      stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end inverseSquareWeight_antitone

namespace complex_prime_energy
abbrev signature : Signature where
  Params := Unit
  State _ := ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ z => ‖z‖) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => (1 : ℝ)) (fun e => nomatch e)

/-- Complete original law with exactly the selected operand replaced. -/
def arena : Arena where
  signature := signature
  Law r := ∀ (c M j : ℕ) (β : ℂ),
    r.readout () () (β * (primeSymbol c ((M + j + 1 : ℕ) : ℤ) : ℂ) / ((M + j + 1 : ℕ) : ℂ)) ^ 2 =
      ‖β‖ ^ 2 * (primeSymbol c ((M + j + 1 : ℕ) : ℤ) ^ 2 * inverseSquareWeight M j)

private theorem actual_law : arena.Law actual := by
  exact @complex_prime_energy
private theorem source_equivalence : (type_of% (@complex_prime_energy)) ↔ arena.Law actual := Iff.rfl
private def source_reconstruction : Analysis.Reconstruction
    (type_of% (@complex_prime_energy)) (arena.Law actual) := .exact

/-- A countermodel to the whole universal law, not a failed fiber alone. -/
private theorem rejected_law : ¬ arena.Law rejected := by
  intro hall
  have h := hall 0 0 0 (0 : ℂ)
  norm_num [rejected, realize] at h
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0 : ℂ), (1 : ℂ), ?_⟩
  norm_num [actual, realize]

def family : Registration arena (type_of% (@complex_prime_energy)) where
  actual := actual
  bridge := source_equivalence
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      cases i
      cases j
      exact (hj rfl).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

/-- PROPOSED raw Expr paths. Compiler acquisition has not run. -/
def selection : Contract.SourceSelection := { owner := `D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare, definition := none, coordinates := #[],
    readouts := #[{ path := #["body", "body", "body", "body", "fn", "arg", "fn", "arg", "fn"],
      stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }
def sourceModel : Analysis.Source (@complex_prime_energy) :=
  Analysis.Source.ofRegistration (@complex_prime_energy) family source_reconstruction selection

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@complex_prime_energy) (type_of% actual) Type Unit := {
  unitName := `Reg.D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare.complex_prime_energy.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare.complex_prime_energy.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => ‖z‖) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (ℂ)
  sourceSelection := some { owner := `D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare, definition := none, coordinates := #[],
    readouts := #[{ path := #["body", "body", "body", "body", "fn", "arg", "fn", "arg", "fn"],
      stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end complex_prime_energy

namespace complex_prime_tail
abbrev signature : Signature where
  Params := Unit
  State _ := ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ z => ‖z‖) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => (1 : ℝ)) (fun e => nomatch e)

/-- Complete original law with exactly the selected operand replaced. -/
def arena : Arena where
  signature := signature
  Law r := ∀ {c M : ℕ} (hc : 2 ≤ c) (hM : 0 < M) (β : ℂ),
    Summable (fun j : ℕ =>
      r.readout () () (β * (primeSymbol c ((M + j + 1 : ℕ) : ℤ) : ℂ) / ((M + j + 1 : ℕ) : ℂ)) ^ 2) ∧
    (∑' j : ℕ,
      ‖β * (primeSymbol c ((M + j + 1 : ℕ) : ℤ) : ℂ) / ((M + j + 1 : ℕ) : ℂ)‖ ^ 2) ≤
        ‖β‖ ^ 2 * (primeSquareMass c / (M : ℝ) + primeCross c / ((M : ℝ) + 1) ^ 2)

private theorem actual_law : arena.Law actual := by
  exact @complex_prime_tail
private theorem source_equivalence : (type_of% (@complex_prime_tail)) ↔ arena.Law actual := Iff.rfl
private def source_reconstruction : Analysis.Reconstruction
    (type_of% (@complex_prime_tail)) (arena.Law actual) := .exact

/-- A countermodel to the whole universal law, not a failed fiber alone. -/
private theorem rejected_law : ¬ arena.Law rejected := by
  intro hall
  have hs := (hall (c := 2) (M := 1) (by decide) (by decide) (0 : ℂ)).1
  exact one_not_summable (by simpa [rejected, realize] using hs)
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0 : ℂ), (1 : ℂ), ?_⟩
  norm_num [actual, realize]

def family : Registration arena (type_of% (@complex_prime_tail)) where
  actual := actual
  bridge := source_equivalence
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      cases i
      cases j
      exact (hj rfl).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

/-- PROPOSED raw Expr paths. Compiler acquisition has not run. -/
def selection : Contract.SourceSelection := { owner := `D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare, definition := none, coordinates := #[],
    readouts := #[{ path := #["body", "body", "body", "body", "body", "fn", "arg", "arg", "body", "fn", "arg", "fn"],
      stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }
def sourceModel : Analysis.Source (@complex_prime_tail) :=
  Analysis.Source.ofRegistration (@complex_prime_tail) family source_reconstruction selection

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@complex_prime_tail) (type_of% actual) Type Unit := {
  unitName := `Reg.D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare.complex_prime_tail.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare.complex_prime_tail.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => ‖z‖) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (ℂ)
  sourceSelection := some { owner := `D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare, definition := none, coordinates := #[],
    readouts := #[{ path := #["body", "body", "body", "body", "body", "fn", "arg", "arg", "body", "fn", "arg", "fn"],
      stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end complex_prime_tail

namespace retained_arithmetic_tail
abbrev signature : Signature where
  Params := Unit
  State _ := ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ z => ‖z‖) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => (1 : ℝ)) (fun e => nomatch e)

/-- Complete original law with exactly the selected operand replaced. -/
def arena : Arena where
  signature := signature
  Law r := ∀ {c M : ℕ} (hc : 2 ≤ c) (hM : 0 < M)
    (S : Finset ℕ) (A : ℕ → ℝ) (v : ℕ → ℂ) (j : ℕ) (κ : ℂ),
    Summable (fun k : ℕ => r.readout () () (retainedArithmeticColumn c S A v j κ (M + k + 1)) ^ 2) ∧
    (∑' k : ℕ, ‖retainedArithmeticColumn c S A v j κ (M + k + 1)‖ ^ 2) ≤
      ‖κ‖ ^ 2 * ‖retainedBoundaryMoment c S A v j‖ ^ 2 *
        (primeSquareMass c / (M : ℝ) + primeCross c / ((M : ℝ) + 1) ^ 2)

private theorem actual_law : arena.Law actual := by
  exact @retained_arithmetic_tail
private theorem source_equivalence : (type_of% (@retained_arithmetic_tail)) ↔ arena.Law actual := Iff.rfl
private def source_reconstruction : Analysis.Reconstruction
    (type_of% (@retained_arithmetic_tail)) (arena.Law actual) := .exact

/-- A countermodel to the whole universal law, not a failed fiber alone. -/
private theorem rejected_law : ¬ arena.Law rejected := by
  intro hall
  have hs := (hall (c := 2) (M := 1) (by decide) (by decide)
    ∅ (fun _ => 0) (fun _ => 0) 0 (0 : ℂ)).1
  exact one_not_summable (by simpa [rejected, realize] using hs)
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0 : ℂ), (1 : ℂ), ?_⟩
  norm_num [actual, realize]

def family : Registration arena (type_of% (@retained_arithmetic_tail)) where
  actual := actual
  bridge := source_equivalence
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      cases i
      cases j
      exact (hj rfl).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

/-- PROPOSED raw Expr paths. Compiler acquisition has not run. -/
def selection : Contract.SourceSelection := { owner := `D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare, definition := none, coordinates := #[],
    readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg", "body", "fn", "arg", "fn"],
      stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }
def sourceModel : Analysis.Source (@retained_arithmetic_tail) :=
  Analysis.Source.ofRegistration (@retained_arithmetic_tail) family source_reconstruction selection

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@retained_arithmetic_tail) (type_of% actual) Type Unit := {
  unitName := `Reg.D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare.retained_arithmetic_tail.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare.retained_arithmetic_tail.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => ‖z‖) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (ℂ)
  sourceSelection := some { owner := `D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare, definition := none, coordinates := #[],
    readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg", "body", "fn", "arg", "fn"],
      stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end retained_arithmetic_tail

namespace canonical_first_jet_split
abbrev signature : Signature where
  Params := (Σ _ : ℕ, ℤ)
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p x => arithmeticBoundarySymbol p.1 p.2 + x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ p x => arithmeticBoundarySymbol p.1 p.2 + x + 1) (fun e => nomatch e)

/-- Complete original law with exactly the selected operand replaced. -/
def arena : Arena where
  signature := signature
  Law r := ∀ (c : ℕ) (S : Finset ℤ) (v : ℤ → ℂ) (m : ℤ),
    couplingFirstJet c S v m =
      (∑ n ∈ S, (arithmeticBoundarySymbol c n : ℂ) * v n) /
        ((Real.pi : ℂ) * (m : ℂ)) -
      ((r.readout () ⟨c, m⟩ (primeSymbol c m) : ℝ) : ℂ) *
        (∑ n ∈ S, v n) / ((Real.pi : ℂ) * (m : ℂ)) +
      canonicalPrimeFirstJetFar c S v m

private theorem actual_law : arena.Law actual := by
  exact @canonical_first_jet_split
private theorem source_equivalence : (type_of% (@canonical_first_jet_split)) ↔ arena.Law actual := Iff.rfl
private def source_reconstruction : Analysis.Reconstruction
    (type_of% (@canonical_first_jet_split)) (arena.Law actual) := .exact

/-- A countermodel to the whole universal law, not a failed fiber alone. -/
private theorem rejected_law : ¬ arena.Law rejected := by
  intro hall
  have hb := canonical_first_jet_split 0 ({0} : Finset ℤ) (fun _ => (1 : ℂ)) 1
  have hh := hall 0 ({0} : Finset ℤ) (fun _ => (1 : ℂ)) 1
  simp only [Finset.sum_singleton, Int.cast_one, mul_one, Complex.ofReal_add] at hb
  simp only [rejected, realize, Finset.sum_singleton, Int.cast_one, mul_one,
    Complex.ofReal_add, Complex.ofReal_one] at hh
  have hd :
      ((arithmeticBoundarySymbol 0 1 : ℂ) + (primeSymbol 0 1 : ℂ) + 1) /
          (Real.pi : ℂ) =
        ((arithmeticBoundarySymbol 0 1 : ℂ) + (primeSymbol 0 1 : ℂ)) / (Real.pi : ℂ) := by
    linear_combination hh - hb
  have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have he := congrArg (fun z : ℂ => z * (Real.pi : ℂ)) hd
  simp only [div_mul_cancel₀ _ hp] at he
  have hzero : (1 : ℂ) = 0 := add_left_cancel (by simpa only [add_zero] using he)
  norm_num at hzero
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨0, 0⟩, (0 : ℝ), (1 : ℝ), ?_⟩
  change arithmeticBoundarySymbol 0 0 + 0 ≠ arithmeticBoundarySymbol 0 0 + 1
  intro h
  have he : (0 : ℝ) = 1 := add_left_cancel h
  norm_num at he

def family : Registration arena (type_of% (@canonical_first_jet_split)) where
  actual := actual
  bridge := source_equivalence
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      cases i
      cases j
      exact (hj rfl).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

/-- PROPOSED raw Expr paths. Compiler acquisition has not run. -/
def selection : Contract.SourceSelection := { owner := `D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare, definition := none, coordinates := #[0, 3],
    readouts := #[{ path := #["body", "body", "body", "body", "arg", "fn", "arg", "arg", "fn", "arg", "fn", "arg", "arg", "fn"],
      stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }
def sourceModel : Analysis.Source (@canonical_first_jet_split) :=
  Analysis.Source.ofRegistration (@canonical_first_jet_split) family source_reconstruction selection

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@canonical_first_jet_split) (type_of% actual) Type Unit := {
  unitName := `Reg.D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare.canonical_first_jet_split.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare.canonical_first_jet_split.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p x => arithmeticBoundarySymbol p.1 p.2 + x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (ℝ)
  sourceSelection := some { owner := `D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare, definition := none, coordinates := #[0, 3],
    readouts := #[{ path := #["body", "body", "body", "body", "arg", "fn", "arg", "arg", "fn", "arg", "fn", "arg", "arg", "fn"],
      stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end canonical_first_jet_split

end Reg.D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare
