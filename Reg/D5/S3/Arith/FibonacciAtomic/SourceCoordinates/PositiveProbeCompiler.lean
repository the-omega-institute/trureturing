import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.SourceCoordinates.PositiveProbeCompiler
import Reg.Support.DependentFamily

/-! # The full natural-pair family of the positive short compiler -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open _root_.D5.S3.Arith.FibonacciAtomic.SourceCoordinates.PositiveProbeCompiler
open _root_.D5.S3.Arith.FibonacciAtomic.TerminalGcdAcquisitionCost
  (replace runWord quantity terminalGcd)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Arith.FibonacciAtomic.SourceCoordinates.PositiveProbeCompiler

abbrev signature : Signature where
  Params := ℕ × ℕ × ℕ
  State _ := ℕ × ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p v => quantity (runWord (compile p.1 p.2.1 p.2.2) v))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (H : ℕ), 1 < H →
    1 ≤ direction H ∧ H ≤ Nat.fib (direction H + 4) ∧
    (∀ j, 1 ≤ j → H ≤ Nat.fib (j + 4) → direction H ≤ j) ∧
    ∀ (k c : ℕ), (k = direction H ∨ k = direction H + 1) →
      (weights H c).Pairwise (fun x y => y ≤ x) ∧
      (∀ i ∈ weights H c, 3 ≤ i ∧ i ≤ direction H + 3) ∧
      ((weights H c).map Nat.fib).sum = positiveLift H c ∧
      (compile H k c).count true = k ∧
      (compile H k c).count false = (weights H c).length ∧
      (compile H k c).count false ≤ graftBound H ∧
      ∀ v : ℕ × ℕ,
        R.readout () (H, k, c) v =
          quantity (replace^[k] v) + positiveLift H c ∧
        terminalGcd H (compile H k c) v =
          Nat.gcd (quantity (replace^[k] v) + c) H

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hK : direction 2 = 1 := by decide +kernel
  have htest := (h 2 (by decide)).2.2.2 1 0 (Or.inl hK.symm)
  have impossible := (htest.2.2.2.2.2.2 (1, 0)).1
  norm_num [rejected, realize, replace, quantity, positiveLift,
    Function.iterate_succ_apply] at impossible

def sourceRegistration : Registration arena
    (∀ (H : ℕ), 1 < H →
    1 ≤ direction H ∧ H ≤ Nat.fib (direction H + 4) ∧
    (∀ j, 1 ≤ j → H ≤ Nat.fib (j + 4) → direction H ≤ j) ∧
    ∀ (k c : ℕ), (k = direction H ∨ k = direction H + 1) →
      (weights H c).Pairwise (fun x y => y ≤ x) ∧
      (∀ i ∈ weights H c, 3 ≤ i ∧ i ≤ direction H + 3) ∧
      ((weights H c).map Nat.fib).sum = positiveLift H c ∧
      (compile H k c).count true = k ∧
      (compile H k c).count false = (weights H c).length ∧
      (compile H k c).count false ≤ graftBound H ∧
      ∀ v : ℕ × ℕ,
        quantity (runWord (compile H k c) v) =
          quantity (replace^[k] v) + positiveLift H c ∧
        terminalGcd H (compile H k c) v =
          Nat.gcd (quantity (replace^[k] v) + c) H) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨effective_short_compiler, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    cases i
    refine ⟨(2, 1, 0), (0, 0), (1, 0), ?_⟩
    change (0 : ℕ) ≠ 3
    decide +kernel

def registration : LeanInformationAudit.Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0}
    (@effective_short_compiler)
    (Realization signature) (Type) Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.SourceCoordinates.PositiveProbeCompiler.informationUnit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.SourceCoordinates.PositiveProbeCompiler.sourceRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨sourceRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p v => quantity (runWord (compile p.1 p.2.1 p.2.2) v)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.SourceCoordinates.PositiveProbeCompiler
    definition := none
    coordinates := #[0, 2, 3]
    readouts := #[{
      path := #["body", "body", "arg", "arg", "arg", "body", "body", "body",
        "arg", "arg", "arg", "arg", "arg", "arg", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false },
    { name := `relaxedAutoImplicit, value := .bool false }]

#print axioms direction
#print axioms compile
#print axioms sourceRegistration
#print axioms registration

end Reg.D5.S3.Arith.FibonacciAtomic.SourceCoordinates.PositiveProbeCompiler
