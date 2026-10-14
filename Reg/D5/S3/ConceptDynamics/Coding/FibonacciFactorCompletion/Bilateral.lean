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
    refine ⟨(), [], [(⟨1, 1, Nat.zero_lt_one, Nat.zero_lt_one⟩ : Return)], ?_⟩
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

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Completion

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Completion.ExactOriginal54
noncomputable section

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := Unit
  State := fun _ => List Return
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun _ => List Return
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature :=
  realize.{0,0,0,0,0} observationSignature (fun _ _ state => state) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => [⟨1, 2, by decide, by decide⟩]) (fun e => nomatch e)

abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (K : ℕ) (d : ℝ) (hK : 1 ≤ K)
    (ω : ℤ → CuLetter) (hω : ω ∈ AuxiliaryLanguage K d)
    (i : ℤ) (xs : List Return)
    (letters : ∀ k : Fin (executionWord xs).length,
      (k.val + 1 < (executionWord xs).length ∨ (executionWord xs)[k.val] = .c) →
      ω (i + (k : ℕ)) = (executionWord xs)[k.val]),
    GuardTrace K d false .high (r.readout () () xs) (pastState ω i)

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have hω : (fun _ : ℤ => CuLetter.u) ∈ AuxiliaryLanguage 1 0 := by
    constructor
    · intro i hc
      have impossible := hc ⟨0, by decide⟩
      cases impossible
    · intro i hc
      have impossible := hc ⟨0, by decide⟩
      cases impossible
  have bad := h 1 0 (by decide) (fun _ => .u) hω 0 [] (by
    intro k
    exact Fin.elim0 k)
  have impossible := bad.1
  change 2 ≤ 1 at impossible
  omega

def evidence : Registration sourceArena (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Completion.occurrence_run_guards) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Completion.occurrence_run_guards, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), [], [⟨1, 1, by decide, by decide⟩], ?_⟩
    simp [actual, realize]

def occurrence_run_guards_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Completion.occurrence_run_guards)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ _ state => state) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Completion.ExactOriginal54.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Completion.ExactOriginal54.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature
    (fun _ _ state => state) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms occurrence_run_guards_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Completion.ExactOriginal54

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Completion.ExactOriginal53
noncomputable section

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := Unit
  State := fun _ => List Return
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun _ => List CuLetter
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature :=
  realize.{0,0,0,0,0} observationSignature (fun _ _ xs => executionWord xs) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize.{0,0,0,0,0} observationSignature (fun _ _ _ => [CuLetter.c]) (fun e => nomatch e)

abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (w : List CuLetter)
    (hend : w = [] ∨ w.getLast? = some CuLetter.u),
    ∃! p : ℕ × List Return,
      w = List.replicate p.1 CuLetter.u ++ r.readout () () p.2


theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  obtain ⟨p, hp, _⟩ := h [] (Or.inl rfl)
  have impossible := congrArg List.length hp
  simp [rejected, realize] at impossible

def evidence : Registration sourceArena (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Completion.finite_run_decomposition) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Completion.finite_run_decomposition, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), [], [⟨1, 1, by decide, by decide⟩], ?_⟩
    change ([] : List CuLetter) ≠ [.c, .u]
    decide

def finite_run_decomposition_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Completion.finite_run_decomposition)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ _ xs => executionWord xs) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Completion.ExactOriginal53.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Completion.ExactOriginal53.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature
    (fun _ _ xs => executionWord xs) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "body", "arg", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms finite_run_decomposition_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Completion.ExactOriginal53

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply.ExactOriginal152
noncomputable section

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := Σ _ : Side, List Return
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature := realize.{0,0,0,0,0} observationSignature (fun _ p D => execute p.1 p.2 D) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (K : ℕ) (d : ℝ) (strict : Bool) (j : Side)
  (execution : List Return) (D : ℝ),
  GuardTrace K d strict j execution D ↔
  ∀ (before : List Return) (a : Return) (after : List Return),
    execution = before ++ a :: after →
    a.r ≤ K ∧ (a.r = K →
      if strict then d < r.readout () ⟨j, before⟩ D
      else d ≤ execute j before D)

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  let a : Return := ⟨1, 1, by decide, by decide⟩
  have left : GuardTrace 1 0 true .high [a] 1 := by
    norm_num [GuardTrace, a]
  have impossible := ((h 1 0 true .high [a] 1).mp left [] a [] rfl).2 rfl
  norm_num [rejected, realize] at impossible

def evidence : Registration sourceArena (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply.uniform_guard_trace_iff_split) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply.uniform_guard_trace_iff_split, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨Side.high, []⟩, 0, 1, ?_⟩
    norm_num [actual, realize, execute]

def uniform_guard_trace_iff_split_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply.uniform_guard_trace_iff_split)
      (type_of% (realize.{0,0,0,0,0} observationSignature (fun _ p D => execute p.1 p.2 D) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply.ExactOriginal152.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply.ExactOriginal152.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature (fun _ p D => execute p.1 p.2 D) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral
    definition := none
    coordinates := #[3, 6]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "body", "body", "body", "body", "arg", "body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms uniform_guard_trace_iff_split_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply.ExactOriginal152

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply.ExactOriginal154
noncomputable section

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := Σ _ : Side, List Return
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature := realize.{0,0,0,0,0} observationSignature (fun _ p D => execute p.1 p.2 D) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (j : Side) (budget : ℝ) (execution : List Return) (D : ℝ),
  StrictControl j budget execution D ↔
  ∀ (before : List Return) (a : Return) (after : List Return),
    execution = before ++ a :: after →
    lam - g ^ 2 * chi ^ a.r * r.readout () ⟨j, before⟩ D < budget

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  let a : Return := ⟨1, 1, by decide, by decide⟩
  have gp : 0 < g := by
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
    dsimp [g, t]
    nlinarith [Real.sqrt_nonneg (5 : ℝ)]
  have cp : 0 < chi := by dsimp [chi]; positivity
  have left : StrictControl .high lam [a] 1 := by
    simp only [StrictControl, a, pow_one, mul_one, and_true]
    nlinarith [mul_pos (sq_pos_of_pos gp) cp]
  have impossible := (h .high lam [a] 1).mp left [] a [] rfl
  norm_num [rejected, realize] at impossible

def evidence : Registration sourceArena (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply.exact_control_iff_split) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply.exact_control_iff_split, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨Side.high, []⟩, 0, 1, ?_⟩
    norm_num [actual, realize, execute]

def exact_control_iff_split_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply.exact_control_iff_split)
      (type_of% (realize.{0,0,0,0,0} observationSignature (fun _ p D => execute p.1 p.2 D) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply.ExactOriginal154.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply.ExactOriginal154.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature (fun _ p D => execute p.1 p.2 D) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral
    definition := none
    coordinates := #[0, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "body", "body", "body", "body", "fn", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms exact_control_iff_split_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply.ExactOriginal154
