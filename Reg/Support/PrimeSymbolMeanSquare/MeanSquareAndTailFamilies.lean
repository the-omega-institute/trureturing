/- SOURCE_ONLY_UNCOMPILED.
Mean-square block, Abel majorant and real/complex arithmetic tail families.
Static source preparation only; formal verification remains pending.
-/
import LeanInformationAuditInterface.Contract.Registration
import LeanInformationAuditInterface.Contract.Analysis.Source
import D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare
import Reg.Support.DependentFamily
import Reg.Support.PrimeSymbolMeanSquare.ArithmeticHelpers

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare
open D5.S3.Weil.ZetaBridge.WeilArithmeticCouplingJet
open LeanInformationAudit
namespace Reg.D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare

private theorem indices_three : primeIndices 3 = {2} := by decide

private theorem square_two : primeSquareMass 2 = 0 := by
  simp [primeSquareMass, indices_two]

private theorem cross_two : primeCross 2 = 0 := by
  simp [primeCross, orderedCross, indices_two]

private theorem cross_three : primeCross 3 = 0 := by
  simp [primeCross, orderedCross, indices_three]

private theorem square_three_pos : 0 < primeSquareMass 3 := by
  simpa [primeSquareMass, indices_three] using pow_pos weight_two_pos 2

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
def selection : Contract.SourceSelection := {
  owner := `D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare
  definition := none
  coordinates := #[]
  readouts := #[{
    path := #["body", "body", "body", "body", "arg", "fn", "arg", "arg", "fn"]
    stateBinder := 0
    functionOperand := true
    stateOperand := none
    booleanPredicate := false }] }
def sourceModel : Analysis.Source (@prime_symbol_block) :=
  Analysis.Source.ofRegistration (@prime_symbol_block) family source_reconstruction selection

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
    (fun K => by simp) 1
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
def selection : Contract.SourceSelection := {
  owner := `D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare
  definition := none
  coordinates := #[1]
  readouts := #[{
    path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg", "arg", "arg", "body", "fn"]
    stateBinder := 0
    functionOperand := true
    stateOperand := none
    booleanPredicate := false }] }
def sourceModel : Analysis.Source (@finite_abel_majorant) :=
  Analysis.Source.ofRegistration (@finite_abel_majorant) family source_reconstruction selection

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
def selection : Contract.SourceSelection := {
  owner := `D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare
  definition := none
  coordinates := #[0]
  readouts := #[{
    path := #["body", "body", "body", "body", "arg", "arg", "fn"]
    stateBinder := 0
    functionOperand := true
    stateOperand := none
    booleanPredicate := false }] }
def sourceModel : Analysis.Source (@prime_symbol_square_tail) :=
  Analysis.Source.ofRegistration (@prime_symbol_square_tail) family source_reconstruction selection

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
def selection : Contract.SourceSelection := {
  owner := `D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare
  definition := none
  coordinates := #[]
  readouts := #[{
    path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg", "body", "fn", "arg", "fn"]
    stateBinder := 0
    functionOperand := true
    stateOperand := none
    booleanPredicate := false }] }
def sourceModel : Analysis.Source (@canonical_first_jet_prime_tail) :=
  Analysis.Source.ofRegistration (@canonical_first_jet_prime_tail) family source_reconstruction selection

end canonical_first_jet_prime_tail

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
def selection : Contract.SourceSelection := {
  owner := `D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare
  definition := none
  coordinates := #[0]
  readouts := #[{
    path := #["body", "body", "body", "fn", "arg", "fn"]
    stateBinder := 0
    functionOperand := true
    stateOperand := none
    booleanPredicate := false }] }
def sourceModel : Analysis.Source (@inverseSquareWeight_antitone) :=
  Analysis.Source.ofRegistration (@inverseSquareWeight_antitone) family source_reconstruction selection

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
def selection : Contract.SourceSelection := {
  owner := `D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare
  definition := none
  coordinates := #[]
  readouts := #[{
    path := #["body", "body", "body", "body", "fn", "arg", "fn", "arg", "fn"]
    stateBinder := 0
    functionOperand := true
    stateOperand := none
    booleanPredicate := false }] }
def sourceModel : Analysis.Source (@complex_prime_energy) :=
  Analysis.Source.ofRegistration (@complex_prime_energy) family source_reconstruction selection

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
def selection : Contract.SourceSelection := {
  owner := `D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare
  definition := none
  coordinates := #[]
  readouts := #[{
    path := #["body", "body", "body", "body", "body", "fn", "arg", "fn", "arg", "body", "fn", "arg", "fn"]
    stateBinder := 0
    functionOperand := true
    stateOperand := none
    booleanPredicate := false }] }
def sourceModel : Analysis.Source (@complex_prime_tail) :=
  Analysis.Source.ofRegistration (@complex_prime_tail) family source_reconstruction selection

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
def selection : Contract.SourceSelection := {
  owner := `D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare
  definition := none
  coordinates := #[]
  readouts := #[{
    path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg", "body", "fn", "arg", "fn"]
    stateBinder := 0
    functionOperand := true
    stateOperand := none
    booleanPredicate := false }] }
def sourceModel : Analysis.Source (@retained_arithmetic_tail) :=
  Analysis.Source.ofRegistration (@retained_arithmetic_tail) family source_reconstruction selection

end retained_arithmetic_tail

end Reg.D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare
