import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.Mertens.Estimates
import Reg.Support.SingleDependentReadout

/-! The complete weighted residual law with its inclusive real cutoff. -/

namespace Reg.D5.S3.Weil.Mertens.Estimates
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Real Set Filter MeasureTheory
open scoped BigOperators Topology
noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ n => ArithmeticFunction.vonMangoldt n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ n => ArithmeticFunction.vonMangoldt n + 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ x : ℝ, _root_.Mertens.E₁Λ x - _root_.Mertens.E₁p x =
    ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, if ¬n.Prime then R.readout () () n / n else 0

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have ht := h 1
  change _root_.Mertens.E₁Λ 1 - _root_.Mertens.E₁p 1 =
    ∑ n ∈ Finset.Ioc 0 ⌊(1 : ℝ)⌋₊,
      if ¬n.Prime then (ArithmeticFunction.vonMangoldt n + 1) / n else 0 at ht
  norm_num [_root_.Mertens.E₁Λ, _root_.Mertens.E₁p, Finset.sum_filter,
    Nat.not_prime_one, Nat.prime_two,
    show Finset.Ioc 0 1 = {1} by decide] at ht

def splitEvidence : Registration arena
    (type_of% @_root_.Mertens.E₁Λ.sub_E₁p_eq_sum_nonprime) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.Mertens.E₁Λ.sub_E₁p_eq_sum_nonprime, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (1 : ℕ), (4 : ℕ), ?_⟩
    change ArithmeticFunction.vonMangoldt 1 ≠ ArithmeticFunction.vonMangoldt 4
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num,
      ArithmeticFunction.vonMangoldt_apply_pow (by decide : (2 : ℕ) ≠ 0),
      ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
    simpa using (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne

def splitRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.Mertens.E₁Λ.sub_E₁p_eq_sum_nonprime) (Realization signature) Unit Unit where
  unitName := `Mertens.E₁Λ.sub_E₁p_eq_sum_nonprime.__information_unit
  realizationName := `Reg.D5.S3.Weil.Mertens.Estimates.splitEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨splitEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ n => ArithmeticFunction.vonMangoldt n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.Estimates
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "arg", "arg", "body", "fn", "arg", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms splitEvidence
#print axioms splitRegistration
end
end Reg.D5.S3.Weil.Mertens.Estimates
