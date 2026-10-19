/- SOURCE_ONLY_UNCOMPILED.
Complete source candidates against the pinned Contract.Registration and enrolled
DependentFamily.realize support. No compiled source-selection or audit result is
claimed. Each law retains its complete original telescope and proposition except
for the single selected absolute-value/norm function operand. In particular, the
remaining absolute values and norms are held fixed. No composite norm-square
function is postulated as an original source operand.
-/
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.ZetaBridge.ActualFullSymbolTail
import Reg.Support.DependentFamily
import Mathlib.Analysis.Real.Pi.Bounds

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Reg.D5.S3.Weil.ZetaBridge.ActualFullSymbolTail
open scoped BigOperators
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Weil.ZetaBridge.ActualFullSymbolTail
open _root_.D5.S3.Weil.ZetaBridge.ActualColumnRemainder
open _root_.D5.S3.Weil.ZetaBridge.WeilArithmeticCouplingParityGram
open _root_.D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare
open _root_.D5.S3.Weil.ZetaBridge.WeilArithmeticCouplingJet
open LeanInformationAudit

abbrev absSignature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def absActual : Realization absSignature :=
  realize absSignature (fun _ _ x => |x|) (fun e => nomatch e)

def absRejected : Realization absSignature :=
  realize absSignature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev normSignature : Signature where
  Params := Unit
  State _ := ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def normActual : Realization normSignature :=
  realize normSignature (fun _ _ z => ‖z‖) (fun e => nomatch e)

def normRejected : Realization normSignature :=
  realize normSignature (fun _ _ _ => 1) (fun e => nomatch e)

private theorem absDependence : ObservationalDependence absSignature absActual := by
  intro i
  refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
  norm_num [absActual, realize]

private theorem normDependence : ObservationalDependence normSignature normActual := by
  intro i
  refine ⟨(), (0 : ℂ), (1 : ℂ), ?_⟩
  norm_num [normActual, realize]

private theorem one_not_summable : ¬ Summable (fun _ : ℕ => (1 : ℝ)) := by
  intro hs
  have hz : (1 : ℝ) = 0 :=
    tendsto_nhds_unique tendsto_const_nhds hs.tendsto_atTop_zero
  norm_num at hz

/-- The selected operand is the absolute-value function at exactly one source occurrence. -/
def prime_first_moment_block_arena : Arena where
  signature := absSignature
  Law r := ∀ {c : ℕ} (hc : 2 ≤ c) (M : ℤ) (k : ℕ),
    r.readout () () (∑ j ∈ Finset.range k, primeSymbol c (M + (j : ℤ))) ≤ primeFirstMoment c

private theorem prime_first_moment_block_actual_law : prime_first_moment_block_arena.Law absActual := by
  exact @prime_first_moment_block

private theorem prime_first_moment_block_rejected_law : ¬ prime_first_moment_block_arena.Law absRejected := by
  intro hall
  have h := hall (c := 2) (by decide) (0 : ℤ) 0
  norm_num [prime_first_moment_block_arena, absRejected, realize, primeFirstMoment, primeIndices] at h

def prime_first_moment_block_family : Registration prime_first_moment_block_arena
    (type_of% (@prime_first_moment_block)) where
  actual := absActual
  bridge := Iff.rfl
  variation := ⟨prime_first_moment_block_actual_law, absRejected, prime_first_moment_block_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨absRejected, ?_, rfl, prime_first_moment_block_rejected_law⟩
      intro j hj
      cases i; cases j
      exact (hj rfl).elim
    · intro e
      exact nomatch e
  dependence := absDependence

/- The path is a raw-Expr candidate, pending compiledSourceSelection checks.
The closed function operand introduces one unrestricted real input.
No original telescope binder is removed from the law. -/
noncomputable def registration_1 : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@prime_first_moment_block) (type_of% absActual) Type Unit := {
  unitName := `Reg.D5.S3.Weil.ZetaBridge.ActualFullSymbolTail.prime_first_moment_block.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZetaBridge.ActualFullSymbolTail.prime_first_moment_block_family
  realizationSource := none
  generated := false
  arena := .source ⟨prime_first_moment_block_arena⟩
  objectArena := .source ⟨prime_first_moment_block_arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source prime_first_moment_block_arena ⟨prime_first_moment_block_family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize absSignature (fun _ _ x => |x|) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaBridge.ActualFullSymbolTail
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "fn"],
      stateBinder := 0,
      functionOperand := true,
      stateOperand := none,
      booleanPredicate := false
    }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

/-- The selected operand is the absolute-value function at exactly one source occurrence. -/
def signed_mixed_partial_arena : Arena where
  signature := absSignature
  Law r := ∀ {c N : ℕ} (hc : 2 ≤ c) (k : ℕ),
    r.readout () () (∑ j ∈ Finset.range k,
      primeSymbol c ((N + j + 1 : ℕ) : ℤ) *
        (arithmeticBoundarySymbol c ((N + j + 1 : ℕ) : ℤ) +
          primeSymbol c ((N + j + 1 : ℕ) : ℤ)) / ((N + j + 1 : ℕ) : ℝ) ^ 2) ≤
      primeFirstMoment c * smoothEnvelope c (N + 1) / ((N + 1 : ℕ) : ℝ) ^ 2

private theorem signed_mixed_partial_actual_law : signed_mixed_partial_arena.Law absActual := by
  exact @signed_mixed_partial

private theorem signed_mixed_partial_rejected_law : ¬ signed_mixed_partial_arena.Law absRejected := by
  intro hall
  have h := hall (c := 2) (N := 0) (by decide) 0
  norm_num [signed_mixed_partial_arena, absRejected, realize, primeFirstMoment, primeIndices] at h

def signed_mixed_partial_family : Registration signed_mixed_partial_arena
    (type_of% (@signed_mixed_partial)) where
  actual := absActual
  bridge := Iff.rfl
  variation := ⟨signed_mixed_partial_actual_law, absRejected, signed_mixed_partial_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨absRejected, ?_, rfl, signed_mixed_partial_rejected_law⟩
      intro j hj
      cases i; cases j
      exact (hj rfl).elim
    · intro e
      exact nomatch e
  dependence := absDependence

/- The path is a raw-Expr candidate, pending compiledSourceSelection checks.
The closed function operand introduces one unrestricted real input.
No original telescope binder is removed from the law. -/
noncomputable def registration_2 : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@signed_mixed_partial) (type_of% absActual) Type Unit := {
  unitName := `Reg.D5.S3.Weil.ZetaBridge.ActualFullSymbolTail.signed_mixed_partial.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZetaBridge.ActualFullSymbolTail.signed_mixed_partial_family
  realizationSource := none
  generated := false
  arena := .source ⟨signed_mixed_partial_arena⟩
  objectArena := .source ⟨signed_mixed_partial_arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source signed_mixed_partial_arena ⟨signed_mixed_partial_family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize absSignature (fun _ _ x => |x|) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaBridge.ActualFullSymbolTail
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "fn"],
      stateBinder := 0,
      functionOperand := true,
      stateOperand := none,
      booleanPredicate := false
    }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

/-- The selected operand is the absolute-value function at exactly one source occurrence. -/
def signed_mixed_tail_arena : Arena where
  signature := absSignature
  Law r := ∀ {c N : ℕ} (hc : 2 ≤ c) (hN : 0 < N),
    Summable (fun j : ℕ =>
      r.readout () () (primeSymbol c ((N + j + 1 : ℕ) : ℤ) *
        (arithmeticBoundarySymbol c ((N + j + 1 : ℕ) : ℤ) +
          primeSymbol c ((N + j + 1 : ℕ) : ℤ)) / ((N + j + 1 : ℕ) : ℝ) ^ 2)) ∧
    |∑' j : ℕ, primeSymbol c ((N + j + 1 : ℕ) : ℤ) *
      (arithmeticBoundarySymbol c ((N + j + 1 : ℕ) : ℤ) +
        primeSymbol c ((N + j + 1 : ℕ) : ℤ)) / ((N + j + 1 : ℕ) : ℝ) ^ 2| ≤
      primeFirstMoment c * smoothEnvelope c (N + 1) / ((N + 1 : ℕ) : ℝ) ^ 2

private theorem signed_mixed_tail_actual_law : signed_mixed_tail_arena.Law absActual := by
  exact @signed_mixed_tail

private theorem signed_mixed_tail_rejected_law : ¬ signed_mixed_tail_arena.Law absRejected := by
  intro hall
  have hs := (hall (c := 2) (N := 1) (by decide) (by decide)).1
  change Summable (fun _ : ℕ => (1 : ℝ)) at hs
  exact one_not_summable hs

def signed_mixed_tail_family : Registration signed_mixed_tail_arena
    (type_of% (@signed_mixed_tail)) where
  actual := absActual
  bridge := Iff.rfl
  variation := ⟨signed_mixed_tail_actual_law, absRejected, signed_mixed_tail_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨absRejected, ?_, rfl, signed_mixed_tail_rejected_law⟩
      intro j hj
      cases i; cases j
      exact (hj rfl).elim
    · intro e
      exact nomatch e
  dependence := absDependence

/- The path is a raw-Expr candidate, pending compiledSourceSelection checks.
The closed function operand introduces one unrestricted real input.
No original telescope binder is removed from the law. -/
noncomputable def registration_3 : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@signed_mixed_tail) (type_of% absActual) Type Unit := {
  unitName := `Reg.D5.S3.Weil.ZetaBridge.ActualFullSymbolTail.signed_mixed_tail.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZetaBridge.ActualFullSymbolTail.signed_mixed_tail_family
  realizationSource := none
  generated := false
  arena := .source ⟨signed_mixed_tail_arena⟩
  objectArena := .source ⟨signed_mixed_tail_arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source signed_mixed_tail_arena ⟨signed_mixed_tail_family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize absSignature (fun _ _ x => |x|) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaBridge.ActualFullSymbolTail
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "fn", "arg", "body", "fn"],
      stateBinder := 0,
      functionOperand := true,
      stateOperand := none,
      booleanPredicate := false
    }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

/-- The selected operand is the complex norm function at exactly one source occurrence. -/
def full_symbol_square_tail_arena : Arena where
  signature := normSignature
  Law r := ∀ {c N : ℕ} (hc : 2 ≤ c) (hN : 0 < N) (β : ℂ),
    Summable (fun j : ℕ =>
      r.readout () () (β * (arithmeticBoundarySymbol c ((N + j + 1 : ℕ) : ℤ) : ℂ) /
        ((N + j + 1 : ℕ) : ℂ)) ^ 2) ∧
    (∑' j : ℕ, ‖β * (arithmeticBoundarySymbol c ((N + j + 1 : ℕ) : ℤ) : ℂ) /
      ((N + j + 1 : ℕ) : ℂ)‖ ^ 2) ≤ ‖β‖ ^ 2 * fullSymbolTailBudget c N

private theorem full_symbol_square_tail_actual_law : full_symbol_square_tail_arena.Law normActual := by
  exact @full_symbol_square_tail

private theorem full_symbol_square_tail_rejected_law : ¬ full_symbol_square_tail_arena.Law normRejected := by
  intro hall
  have hs := (hall (c := 2) (N := 1) (by decide) (by decide) (0 : ℂ)).1
  change Summable (fun _ : ℕ => (1 : ℝ) ^ 2) at hs
  exact one_not_summable (by simpa only [one_pow] using hs)

def full_symbol_square_tail_family : Registration full_symbol_square_tail_arena
    (type_of% (@full_symbol_square_tail)) where
  actual := normActual
  bridge := Iff.rfl
  variation := ⟨full_symbol_square_tail_actual_law, normRejected, full_symbol_square_tail_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨normRejected, ?_, rfl, full_symbol_square_tail_rejected_law⟩
      intro j hj
      cases i; cases j
      exact (hj rfl).elim
    · intro e
      exact nomatch e
  dependence := normDependence

/- The path is a raw-Expr candidate, pending compiledSourceSelection checks.
The closed function operand introduces one unrestricted complex input.
No original telescope binder is removed from the law. -/
noncomputable def registration_4 : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@full_symbol_square_tail) (type_of% normActual) Type Unit := {
  unitName := `Reg.D5.S3.Weil.ZetaBridge.ActualFullSymbolTail.full_symbol_square_tail.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZetaBridge.ActualFullSymbolTail.full_symbol_square_tail_family
  realizationSource := none
  generated := false
  arena := .source ⟨full_symbol_square_tail_arena⟩
  objectArena := .source ⟨full_symbol_square_tail_arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source full_symbol_square_tail_arena ⟨full_symbol_square_tail_family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize normSignature (fun _ _ z => ‖z‖) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaBridge.ActualFullSymbolTail
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "fn", "arg", "body", "fn", "arg", "fn"],
      stateBinder := 0,
      functionOperand := true,
      stateOperand := none,
      booleanPredicate := false
    }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

/-- The selected operand is the complex norm function at exactly one source occurrence. -/
def paired_first_jet_tail_arena : Arena where
  signature := normSignature
  Law r := ∀ {c N : ℕ} (hc : 2 ≤ c) (hN : 0 < N)
    (S : Finset ℤ) (v : ℤ → ℂ),
    Summable (fun j : ℕ =>
      r.readout () () (couplingFirstJet c S v ((N + j + 1 : ℕ) : ℤ)) ^ 2 +
      ‖couplingFirstJet c S v (-((N + j + 1 : ℕ) : ℤ))‖ ^ 2) ∧
    (∑' j : ℕ,
      (‖couplingFirstJet c S v ((N + j + 1 : ℕ) : ℤ)‖ ^ 2 +
        ‖couplingFirstJet c S v (-((N + j + 1 : ℕ) : ℤ))‖ ^ 2)) ≤
      (2 / Real.pi ^ 2) *
        (‖∑ n ∈ S, (arithmeticBoundarySymbol c n : ℂ) * v n‖ ^ 2 / (N : ℝ) +
          ‖∑ n ∈ S, v n‖ ^ 2 * fullSymbolTailBudget c N)

private theorem paired_first_jet_tail_actual_law : paired_first_jet_tail_arena.Law normActual := by
  exact @paired_first_jet_tail

private theorem paired_first_jet_tail_rejected_law : ¬ paired_first_jet_tail_arena.Law normRejected := by
  intro hall
  have hs := (hall (c := 2) (N := 1) (by decide) (by decide)
    (∅ : Finset ℤ) (fun _ : ℤ => (0 : ℂ))).1
  have hzero (m : ℤ) : couplingFirstJet 2 (∅ : Finset ℤ)
      (fun _ : ℤ => (0 : ℂ)) m = 0 := by
    simp [couplingFirstJet]
  change Summable (fun j : ℕ => (1 : ℝ) ^ 2 +
    ‖couplingFirstJet 2 (∅ : Finset ℤ) (fun _ : ℤ => (0 : ℂ))
      (-((1 + j + 1 : ℕ) : ℤ))‖ ^ 2) at hs
  exact one_not_summable (by simpa only [hzero, norm_zero, zero_pow (by decide : 2 ≠ 0),
    one_pow, add_zero] using hs)

def paired_first_jet_tail_family : Registration paired_first_jet_tail_arena
    (type_of% (@paired_first_jet_tail)) where
  actual := normActual
  bridge := Iff.rfl
  variation := ⟨paired_first_jet_tail_actual_law, normRejected, paired_first_jet_tail_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨normRejected, ?_, rfl, paired_first_jet_tail_rejected_law⟩
      intro j hj
      cases i; cases j
      exact (hj rfl).elim
    · intro e
      exact nomatch e
  dependence := normDependence

/- The path is a raw-Expr candidate, pending compiledSourceSelection checks.
The closed function operand introduces one unrestricted complex input.
No original telescope binder is removed from the law. -/
noncomputable def registration_5 : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@paired_first_jet_tail) (type_of% normActual) Type Unit := {
  unitName := `Reg.D5.S3.Weil.ZetaBridge.ActualFullSymbolTail.paired_first_jet_tail.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZetaBridge.ActualFullSymbolTail.paired_first_jet_tail_family
  realizationSource := none
  generated := false
  arena := .source ⟨paired_first_jet_tail_arena⟩
  objectArena := .source ⟨paired_first_jet_tail_arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source paired_first_jet_tail_arena ⟨paired_first_jet_tail_family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize normSignature (fun _ _ z => ‖z‖) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaBridge.ActualFullSymbolTail
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg", "body", "fn", "arg", "fn", "arg", "fn"],
      stateBinder := 0,
      functionOperand := true,
      stateOperand := none,
      booleanPredicate := false
    }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

/- SOURCE_ONLY_UNCOMPILED extensions: exact complete telescopes, one original
norm function operand each, the enrolled DependentFamily.realize, and raw AST
path candidates. These are attempts, not compiled source reconstruction,
enrollment validation, four-slot success or a declared_validated result. -/

def paired_coupling_column_tail_arena : Arena where
  signature := normSignature
  Law r := ∀ {c M : ℕ} (hc : 2 ≤ c) (hM : 0 < M)
    (S : Finset ℤ) (v : ℤ → ℂ) {A : ℝ} (hA : 0 ≤ A)
    (hS : ∀ n ∈ S, |(n : ℝ)| ≤ A) (hsep : A < (M : ℝ) + 1),
    Summable (fun j : ℕ =>
      r.readout () () (couplingColumn c S v ((M + j + 1 : ℕ) : ℤ)) ^ 2 +
      ‖couplingColumn c S v (-((M + j + 1 : ℕ) : ℤ))‖ ^ 2) ∧
    (∑' j : ℕ,
      (‖couplingColumn c S v ((M + j + 1 : ℕ) : ℤ)‖ ^ 2 +
        ‖couplingColumn c S v (-((M + j + 1 : ℕ) : ℤ))‖ ^ 2)) ≤
      (Real.sqrt (pairedJetBudget c M S v) +
        Real.sqrt (pairedRemainderBudget c M A S v)) ^ 2

private theorem paired_coupling_column_tail_actual_law : paired_coupling_column_tail_arena.Law normActual := by
  exact @paired_coupling_column_tail

private theorem paired_coupling_column_tail_rejected_law : ¬ paired_coupling_column_tail_arena.Law normRejected := by
  intro hall
  have hs := (hall (c := 2) (M := 1) (by decide) (by decide)
    (∅ : Finset ℤ) (fun _ => (0 : ℂ)) (A := 0) (by norm_num) (by simp)
    (by norm_num)).1
  have hone : Summable (fun _ : ℕ => (1 : ℝ)) := by
    simpa [paired_coupling_column_tail_arena, normRejected, realize, couplingColumn, couplingFirstJet] using hs
  exact one_not_summable hone

def paired_coupling_column_tail_family : Registration paired_coupling_column_tail_arena
    (type_of% (@paired_coupling_column_tail)) where
  actual := normActual
  bridge := Iff.rfl
  variation := ⟨paired_coupling_column_tail_actual_law, normRejected, paired_coupling_column_tail_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨normRejected, ?_, rfl, paired_coupling_column_tail_rejected_law⟩
      intro j hj
      cases i; cases j
      exact (hj rfl).elim
    · intro e
      exact nomatch e
  dependence := normDependence

noncomputable def registration_8 : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@paired_coupling_column_tail) (type_of% normActual) Type Unit := {
  unitName := `Reg.D5.S3.Weil.ZetaBridge.ActualFullSymbolTail.paired_coupling_column_tail.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZetaBridge.ActualFullSymbolTail.paired_coupling_column_tail_family
  realizationSource := none
  generated := false
  arena := .source ⟨paired_coupling_column_tail_arena⟩
  objectArena := .source ⟨paired_coupling_column_tail_arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source paired_coupling_column_tail_arena ⟨paired_coupling_column_tail_family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize normSignature (fun _ _ z => ‖z‖) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaBridge.ActualFullSymbolTail
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg", "body", "fn", "arg", "fn", "arg", "fn"],
      stateBinder := 0,
      functionOperand := true,
      stateOperand := none,
      booleanPredicate := false
    }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

/- Paired lower-tail registration over the original complete theorem telescope.
The sole selected source occurrence is the positive-column norm function operand
in Summable. All lower-bound norms, moments, lets and cutoffs stay actual.
Source-role reconstruction, registration and native checks for this repair remain
caller-owned and pending. -/


/-- One selected positive-column norm occurrence in Summable.
All other norms, including both lower-bound norms, stay actual, as do all
moments, lets and cutoff operands. -/
def paired_coupling_column_tail_lower_arena : Arena where
  signature := normSignature
  Law r := ∀ {c M : ℕ} (hc : 2 ≤ c) (hM : 0 < M)
    (S : Finset ℤ) (v : ℤ → ℂ) {A : ℝ} (hA : 0 ≤ A)
    (hS : ∀ n ∈ S, |(n : ℝ)| ≤ A),
    let alpha : ℂ := ∑ n ∈ S, (arithmeticBoundarySymbol c n : ℂ) * v n
    let beta : ℂ := ∑ n ∈ S, v n
    let q : ℝ := ‖alpha‖ ^ 2 + smoothFloor c ^ 2 * ‖beta‖ ^ 2
    let U : ℝ := 2 * (Real.cosh (logLength c / 2) - 1) / (2 * Real.pi / logLength c)
    let D0 : ℝ := 2 * primeFirstMoment c * (2 + U)
    1 ≤ frequency c ((M + 1 : ℕ) : ℤ) →
    2 * A ≤ (M : ℝ) + 1 →
    0 < q →
    2 * ‖beta‖ ^ 2 * D0 / q ≤ (M : ℝ) + 1 →
    256 * arithmeticBoundaryBudget c ^ 2 * weightedHeadMass S v ^ 2 / (3 * q) ≤
      (M : ℝ) ^ 2 →
    Summable (fun j : ℕ =>
      r.readout () () (couplingColumn c S v ((M + j + 1 : ℕ) : ℤ)) ^ 2 +
        ‖couplingColumn c S v (-((M + j + 1 : ℕ) : ℤ))‖ ^ 2) ∧
    q / (4 * Real.pi ^ 2 * ((M : ℝ) + 1)) ≤
      ∑' j : ℕ, (‖couplingColumn c S v ((M + j + 1 : ℕ) : ℤ)‖ ^ 2 +
        ‖couplingColumn c S v (-((M + j + 1 : ℕ) : ℤ))‖ ^ 2)

private theorem paired_coupling_column_tail_lower_actual_law :
    paired_coupling_column_tail_lower_arena.Law normActual := by
  exact @paired_coupling_column_tail_lower

private theorem paired_coupling_column_tail_lower_rejected_law :
    ¬ paired_coupling_column_tail_lower_arena.Law normRejected := by
  intro hall
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlogle : Real.log (2 : ℝ) ≤ 1 := by
    simpa only [show (2 : ℝ) - 1 = 1 by norm_num] using
      (Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2))
  have hw1 : 1 ≤ frequency 2 ((1 : ℕ) : ℤ) := by
    norm_num [frequency, logLength]
    apply (le_div_iff₀ hlog).2
    nlinarith only [hlogle, Real.pi_gt_three]
  have hw2 : 1 ≤ frequency 2 ((1 + 1 : ℕ) : ℤ) := by
    norm_num [frequency, logLength]
    apply (le_div_iff₀ hlog).2
    nlinarith only [hlogle, Real.pi_gt_three]
  have hdelta : 0 < smoothFloor 2 :=
    (smooth_weight_floor (c := 2) (m := 1) (by decide) (by decide) hw1).1
  have hsymbol : arithmeticBoundarySymbol 2 0 = 0 := by
    have ho : arithmeticBoundarySymbol 2 (-(0 : ℤ)) =
        -arithmeticBoundarySymbol 2 0 := by rw [arithmetic_boundary_symbol_neg]
    simp only [neg_zero] at ho
    linarith only [ho]
  have hP : primeFirstMoment 2 = 0 := by
    norm_num [primeFirstMoment, primeIndices]
  have hmass : weightedHeadMass ({0} : Finset ℤ) (fun _ : ℤ => (1 : ℂ)) = 0 := by
    simp [weightedHeadMass]
  have hqw : 0 <
      ‖∑ n ∈ ({0} : Finset ℤ), (arithmeticBoundarySymbol 2 n : ℂ) * (1 : ℂ)‖ ^ 2 +
        smoothFloor 2 ^ 2 * ‖∑ _n ∈ ({0} : Finset ℤ), (1 : ℂ)‖ ^ 2 := by
    simpa [hsymbol] using (sq_pos_of_pos hdelta)
  have hs := (hall (c := 2) (M := 1) (by decide) (by decide)
    ({0} : Finset ℤ) (fun _ : ℤ => (1 : ℂ)) (A := 0) (by norm_num) (by simp)
    hw2 (by norm_num) hqw (by simp [hP]) (by simp [hmass])).1
  change Summable (fun j : ℕ => (1 : ℝ) ^ 2 +
    ‖couplingColumn 2 ({0} : Finset ℤ) (fun _ : ℤ => (1 : ℂ))
      (-((1 + j + 1 : ℕ) : ℤ))‖ ^ 2) at hs
  apply one_not_summable
  refine Summable.of_nonneg_of_le (fun _ => by norm_num) ?_ hs
  intro j
  nlinarith only [sq_nonneg
    ‖couplingColumn 2 ({0} : Finset ℤ) (fun _ : ℤ => (1 : ℂ))
      (-((1 + j + 1 : ℕ) : ℤ))‖]

def paired_coupling_column_tail_lower_family :
    Registration paired_coupling_column_tail_lower_arena
      (type_of% (@paired_coupling_column_tail_lower)) where
  actual := normActual
  bridge := Iff.rfl
  variation := ⟨paired_coupling_column_tail_lower_actual_law, normRejected,
    paired_coupling_column_tail_lower_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨normRejected, ?_, rfl, paired_coupling_column_tail_lower_rejected_law⟩
      intro j hj
      cases i; cases j
      exact (hj rfl).elim
    · intro e
      exact nomatch e
  dependence := normDependence

/- 9 original binders + 5 let bodies + 5 cutoff arrows precede the conjunction.
The single path selects the positive-column Norm.norm function operand in
Summable. The lower-bound tsum retains both actual norms. Unit supplies one role
for this one readout. Source-role reconstruction, registration and native checks
for this repair remain caller-owned and pending. -/
noncomputable def registration_9 : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@paired_coupling_column_tail_lower) (type_of% normActual) Type Unit := {
  unitName := `Reg.D5.S3.Weil.ZetaBridge.ActualFullSymbolTail.paired_coupling_column_tail_lower.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZetaBridge.ActualFullSymbolTail.paired_coupling_column_tail_lower_family
  realizationSource := none
  generated := false
  arena := .source ⟨paired_coupling_column_tail_lower_arena⟩
  objectArena := .source ⟨paired_coupling_column_tail_lower_arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source paired_coupling_column_tail_lower_arena ⟨paired_coupling_column_tail_lower_family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize normSignature (fun _ _ z => ‖z‖) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaBridge.ActualFullSymbolTail
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg", "body", "fn", "arg", "fn", "arg", "fn"],
      stateBinder := 0,
      functionOperand := true,
      stateOperand := none,
      booleanPredicate := false
    }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.Weil.ZetaBridge.ActualFullSymbolTail
