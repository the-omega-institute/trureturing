import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Filter Topology

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral

noncomputable section

abbrev parserSignature : Signature where
  Params := Unit
  State _ := List Return
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Nat
  Anchor := Empty
  finiteAnchor := inferInstance

def parserActual : Realization parserSignature :=
  realize parserSignature (fun _ _ xs => wordWeight (executionWord xs)) (fun e => nomatch e)

def parserRejected : Realization parserSignature :=
  realize parserSignature (fun _ _ _ => 1) (fun e => nomatch e)

/-- The word-weight observation varies inside the complete parser statement. -/
abbrev parserArena : Arena where
  signature := parserSignature
  Law R :=
    (∀ (a : Return) (xs : List Return),
      (executionWord (a :: xs)).takeWhile isC = List.replicate a.r CuLetter.c) ∧
    (∀ (a : Return) (xs : List Return),
      ((executionWord (a :: xs)).drop a.r).takeWhile isU = List.replicate a.m CuLetter.u) ∧
    Function.Injective executionWord ∧
    (∀ xs : List Return, R.readout () () xs = listWeight xs) ∧
    (∀ model : Model, Function.Injective (history model))

theorem parser_rejected_law : ¬ parserArena.Law parserRejected := by
  intro h
  have hh := h.2.2.2.1 []
  norm_num [parserRejected, realize, listWeight] at hh

def parserRegistration : Registration parserArena
    ((∀ (a : Return) (xs : List Return),
      (executionWord (a :: xs)).takeWhile isC = List.replicate a.r CuLetter.c) ∧
    (∀ (a : Return) (xs : List Return),
      ((executionWord (a :: xs)).drop a.r).takeWhile isU = List.replicate a.m CuLetter.u) ∧
    Function.Injective executionWord ∧
    (∀ xs : List Return, wordWeight (executionWord xs) = listWeight xs) ∧
    (∀ model : Model, Function.Injective (history model))) where
  actual := parserActual
  bridge := Iff.rfl
  variation := ⟨complete_execution_word_parser, parserRejected, parser_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨parserRejected, ?_, rfl, parser_rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), [], [{ m := 1, r := 1, m_pos := Nat.zero_lt_one,
      r_pos := Nat.zero_lt_one }], ?_⟩
    change (0 : ℕ) ≠ 26
    norm_num

def complete_execution_word_parser_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral.complete_execution_word_parser)
      (type_of% (realize.{0,0,0,0,0} parserSignature
        (fun _ _ xs => wordWeight (executionWord xs)) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral.complete_execution_word_parser_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral.parserRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨parserArena⟩
  objectArena := .source ⟨parserArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source parserArena ⟨parserRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} parserSignature
    (fun _ _ xs => wordWeight (executionWord xs)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "arg", "arg", "fn", "arg", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev pastSignature : Signature where
  Params := Σ _ : (ℤ → CuLetter), Σ _ : ℤ, ℕ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def pastActual : Realization pastSignature :=
  realize pastSignature (fun _ p y => finitePast p.1 p.2.1 p.2.2 y) (fun e => nomatch e)

def pastRejected : Realization pastSignature :=
  realize pastSignature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Only the first finite-past minuend varies; all twelve source clauses remain. -/
abbrev pastArena : Arena where
  signature := pastSignature
  Law R :=
    (∀ (ω : ℤ → CuLetter) (i : ℤ) (N : ℕ) (x y : ℝ),
      R.readout () ⟨ω, i, N⟩ y - finitePast ω i N x = g ^ pastWeight ω i N * (y - x)) ∧
    (∀ (ω : ℤ → CuLetter) (i : ℤ) (N : ℕ),
      0 ≤ g ^ pastWeight ω i N ∧ g ^ pastWeight ω i N ≤ rho ^ N) ∧
    (∀ (ω : ℤ → CuLetter) (i : ℤ),
      0 ≤ pastState ω i ∧ pastState ω i ≤ hSide .high) ∧
    (∀ (ω : ℤ → CuLetter) (i : ℤ) (z : ℝ), 0 ≤ z → z ≤ hSide .high →
      Tendsto (fun N : ℕ => finitePast ω i N z) atTop (𝓝 (pastState ω i))) ∧
    (∀ (ω : ℤ → CuLetter) (i : ℤ),
      pastState ω (i + 1) = letterMap (ω i) (pastState ω i)) ∧
    (∀ (ω : ℤ → CuLetter) (y : ℤ → ℝ),
      (∀ i, 0 ≤ y i ∧ y i ≤ hSide .high) →
      (∀ i, y (i + 1) = letterMap (ω i) (y i)) → y = pastState ω) ∧
    (∀ (ω ν : ℤ → CuLetter) (i : ℤ) (N : ℕ),
      (∀ k : Fin N, ω (i - 1 - (k : ℕ)) = ν (i - 1 - (k : ℕ))) →
      |pastState ω i - pastState ν i| ≤ hSide .high * rho ^ N) ∧
    (∀ i : ℤ, pastState (fun _ => CuLetter.u) i = hSide .high) ∧
    (∀ i : ℤ, Continuous (fun ω : ℤ → CuLetter => pastState ω i)) ∧
    (∀ (K : ℕ) (d : ℝ), 1 ≤ K →
      (AuxiliaryLanguage K d).Nonempty ∧ IsCompact (AuxiliaryLanguage K d)) ∧
    (∀ (ω : ℤ → CuLetter) (i j : ℤ),
      pastState (fun n => ω (n + j)) i = pastState ω (i + j)) ∧
    (∀ (ω : ℤ → CuLetter) (j : ℤ) (K : ℕ) (d : ℝ),
      ω ∈ AuxiliaryLanguage K d ↔ (fun n => ω (n + j)) ∈ AuxiliaryLanguage K d)

theorem past_rejected_law : ¬ pastArena.Law pastRejected := by
  intro h
  have hh := h.1 (fun _ => CuLetter.c) 0 0 0 1
  norm_num [pastRejected, realize, finitePast, pastWeight] at hh

def pastRegistration : Registration pastArena
    ((∀ (ω : ℤ → CuLetter) (i : ℤ) (N : ℕ) (x y : ℝ),
      finitePast ω i N y - finitePast ω i N x = g ^ pastWeight ω i N * (y - x)) ∧
    (∀ (ω : ℤ → CuLetter) (i : ℤ) (N : ℕ),
      0 ≤ g ^ pastWeight ω i N ∧ g ^ pastWeight ω i N ≤ rho ^ N) ∧
    (∀ (ω : ℤ → CuLetter) (i : ℤ),
      0 ≤ pastState ω i ∧ pastState ω i ≤ hSide .high) ∧
    (∀ (ω : ℤ → CuLetter) (i : ℤ) (z : ℝ), 0 ≤ z → z ≤ hSide .high →
      Tendsto (fun N : ℕ => finitePast ω i N z) atTop (𝓝 (pastState ω i))) ∧
    (∀ (ω : ℤ → CuLetter) (i : ℤ),
      pastState ω (i + 1) = letterMap (ω i) (pastState ω i)) ∧
    (∀ (ω : ℤ → CuLetter) (y : ℤ → ℝ),
      (∀ i, 0 ≤ y i ∧ y i ≤ hSide .high) →
      (∀ i, y (i + 1) = letterMap (ω i) (y i)) → y = pastState ω) ∧
    (∀ (ω ν : ℤ → CuLetter) (i : ℤ) (N : ℕ),
      (∀ k : Fin N, ω (i - 1 - (k : ℕ)) = ν (i - 1 - (k : ℕ))) →
      |pastState ω i - pastState ν i| ≤ hSide .high * rho ^ N) ∧
    (∀ i : ℤ, pastState (fun _ => CuLetter.u) i = hSide .high) ∧
    (∀ i : ℤ, Continuous (fun ω : ℤ → CuLetter => pastState ω i)) ∧
    (∀ (K : ℕ) (d : ℝ), 1 ≤ K →
      (AuxiliaryLanguage K d).Nonempty ∧ IsCompact (AuxiliaryLanguage K d)) ∧
    (∀ (ω : ℤ → CuLetter) (i j : ℤ),
      pastState (fun n => ω (n + j)) i = pastState ω (i + j)) ∧
    (∀ (ω : ℤ → CuLetter) (j : ℤ) (K : ℕ) (d : ℝ),
      ω ∈ AuxiliaryLanguage K d ↔ (fun n => ω (n + j)) ∈ AuxiliaryLanguage K d)) where
  actual := pastActual
  bridge := Iff.rfl
  variation := ⟨bilateral_past_state, pastRejected, past_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨pastRejected, ?_, rfl, past_rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨(fun _ => CuLetter.c), (0 : ℤ), (0 : ℕ)⟩, 0, 1, ?_⟩
    norm_num [pastActual, realize, finitePast]

def bilateral_past_state_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral.bilateral_past_state)
      (type_of% (realize.{0,0,0,0,0} pastSignature
        (fun _ p y => finitePast p.1 p.2.1 p.2.2 y) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral.bilateral_past_state_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral.pastRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨pastArena⟩
  objectArena := .source ⟨pastArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source pastArena ⟨pastRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} pastSignature
    (fun _ p y => finitePast p.1 p.2.1 p.2.2 y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["fn", "arg", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral
