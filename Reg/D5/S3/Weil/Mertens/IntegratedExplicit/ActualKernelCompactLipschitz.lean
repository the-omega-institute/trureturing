import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelCompactLipschitz
import Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelLocalPositivity
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelLocalPositivity
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelCompactLipschitz
open LeanInformationAudit

namespace Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelCompactLipschitz

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature := realize signature (fun _ _ t => K t) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law F := ∀ {a b : ℝ} {N : ℕ}, 0 < a → a ≤ b → Real.exp b < N →
    ∀ {u v : ℝ}, u ∈ Icc a b → v ∈ Icc a b →
      |F.readout () () u - F.readout () () v| ≤ L a b N * |u - v|

private def testN : ℕ := ⌈Real.exp 2⌉₊ + 1

private lemma testN_bound : Real.exp 2 < (testN : ℝ) := by
  have hh := Nat.le_ceil (Real.exp 2)
  dsimp only [testN]
  push_cast
  linarith

private lemma testL_nonneg : 0 ≤ L 1 2 testN := by
  have hA : 0 ≤ A testN := Finset.sum_nonneg (fun _ _ => div_nonneg
    ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg _))
  have hP : 0 ≤ P testN := Finset.sum_nonneg (fun _ _ => ArithmeticFunction.vonMangoldt_nonneg)
  dsimp only [L]
  positivity

def rejected : Realization signature := realize signature
  (fun _ _ t => (L 1 2 testN + 1) * t) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro hh
  have ht := hh (a := 1) (b := 2) (N := testN) (by norm_num) (by norm_num)
    testN_bound (u := 1) (v := 2) (by norm_num) (by norm_num)
  change |(L 1 2 testN + 1) * 1 - (L 1 2 testN + 1) * 2| ≤ L 1 2 testN * |1 - 2| at ht
  have he : (L 1 2 testN + 1) * 1 - (L 1 2 testN + 1) * 2 = -(L 1 2 testN + 1) := by ring
  rw [he, abs_neg, abs_of_nonneg (by linarith [testL_nonneg])] at ht
  norm_num at ht <;> linarith

def evidence : Registration arena (type_of% @kernel_lipschitz) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@kernel_lipschitz, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := _root_.Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelLocalPositivity.LocalFormula.kernel_dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@kernel_lipschitz) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelCompactLipschitz.kernel_lipschitz.__information_unit
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelCompactLipschitz.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ t => K t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelCompactLipschitz
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg", "fn", "arg", "fn"]
      stateBinder := 6
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg", "arg", "fn"]
      stateBinder := 7
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms registration
end Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelCompactLipschitz
