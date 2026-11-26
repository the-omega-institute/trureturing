import D5.S3.Arith.FactorialRatio.Compression.OptimizedEntropy
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Reg.D5.S3.Arith.FactorialRatio.Compression.OptimizedEntropy

open Finset Real Set
open LeanInformationAudit
open _root_.D5.S3.Arith.FactorialRatio.CompactFactorialGcd
open _root_.D5.S3.Arith.FactorialRatio.Compression.OptimizedEntropy
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℕ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ M b => windowLoss M b) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ M _ =>
    (Real.eulerMascheroniConstant - kappa) * (M : ℝ) ^ 2 -
      (32 + 4 * (kappa / entropyOptimizer)) * (M : ℝ) *
        (log ((M : ℝ) + 1) + 1) - 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R :=
    0 < Real.eulerMascheroniConstant - kappa ∧
      ∀ M : ℕ, 2 ≤ M →
        (∀ b : ℕ, (M + 1) * b ≤ M * (M - 1) →
          (Real.eulerMascheroniConstant - kappa) * (M : ℝ) ^ 2 -
            (32 + 4 * (kappa / entropyOptimizer)) * (M : ℝ) *
              (log ((M : ℝ) + 1) + 1) ≤ R.readout () M b) ∧
        ∃ b : ℕ, (M + 1) * b ≤ M * (M - 1) ∧ minimumLoss M = windowLoss M b ∧
          (∀ c : ℕ, (M + 1) * c ≤ M * (M - 1) → windowLoss M b ≤ windowLoss M c) ∧
          |minimumLoss M - (Real.eulerMascheroniConstant - kappa) * (M : ℝ) ^ 2| ≤
            (32 + 4 * (kappa / entropyOptimizer)) * (M : ℝ) *
              (log ((M : ℝ) + 1) + 1)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := (h.2 2 (by decide)).1 0 (by decide)
  change (Real.eulerMascheroniConstant - kappa) * (2 : ℝ) ^ 2 -
      (32 + 4 * (kappa / entropyOptimizer)) * (2 : ℝ) *
        (log ((2 : ℝ) + 1) + 1) ≤
    (Real.eulerMascheroniConstant - kappa) * (2 : ℝ) ^ 2 -
      (32 + 4 * (kappa / entropyOptimizer)) * (2 : ℝ) *
        (log ((2 : ℝ) + 1) + 1) - 1 at hh
  linarith only [hh]

def family : Registration arena (type_of% @optimized_entropy_asymptotic) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨optimized_entropy_asymptotic, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro role
    refine ⟨3, 0, 1, ?_⟩
    change windowLoss 3 0 ≠ windowLoss 3 1
    intro hh
    have he : log (selbergFactorial 4 6 0 : ℝ) = log (selbergFactorial 4 6 1 : ℝ) := by
      dsimp [windowLoss] at hh
      norm_num only [Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul, Nat.cast_ofNat] at hh
      linarith only [hh]
    have h0 : selbergFactorial 4 6 0 = 268738560000 := by decide
    have h1 : selbergFactorial 4 6 1 = 3583180800 := by decide
    rw [h0, h1] at he
    have hz := Real.log_injOn_pos (by norm_num : (0 : ℝ) < 268738560000)
      (by norm_num : (0 : ℝ) < 3583180800) he
    norm_num at hz

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@optimized_entropy_asymptotic) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Arith.FactorialRatio.Compression.OptimizedEntropy.optimized_entropy_asymptotic.__information_unit
  realizationName := `Reg.D5.S3.Arith.FactorialRatio.Compression.OptimizedEntropy.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ M b => windowLoss M b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FactorialRatio.Compression.OptimizedEntropy
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["arg", "body", "body", "fn", "arg", "body", "body", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.FactorialRatio.Compression.OptimizedEntropy
