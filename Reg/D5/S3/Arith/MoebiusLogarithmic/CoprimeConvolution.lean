import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.MoebiusLogarithmic.CoprimeConvolution
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.MoebiusLogarithmic
open LeanInformationAudit
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable
namespace Reg.D5.S3.Arith.MoebiusLogarithmic.CoprimeConvolution

abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ n => ArithmeticFunction.moebius n) (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ q n : ℕ,
    (∑ d ∈ n.divisors.filter (PrimeSupported q), ArithmeticFunction.moebius (n / d)) =
      if n.Coprime q then R.readout () q n else 0

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 1 1
  rw [sum_supported_moebius] at hb
  norm_num [rejected, realize] at hb

def registration : Registration arena
    (∀ q n : ℕ,
      (∑ d ∈ n.divisors.filter (PrimeSupported q), ArithmeticFunction.moebius (n / d)) =
        if n.Coprime q then ArithmeticFunction.moebius n else 0) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨sum_supported_moebius, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      cases i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      cases j
      exact (hj rfl).elim
    · intro e
      cases e
  dependence := by
    intro i
    cases i
    refine ⟨(1 : ℕ), (1 : ℕ), (2 : ℕ), ?_⟩
    change ArithmeticFunction.moebius 1 ≠ ArithmeticFunction.moebius 2
    norm_num [
      ArithmeticFunction.moebius_apply_prime (by decide : Nat.Prime 2)]

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Arith.MoebiusLogarithmic.sum_supported_moebius)
    (type_of% (realize.{0,0,0,0,0} signature
      (fun _ _ n => ArithmeticFunction.moebius n) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Arith.MoebiusLogarithmic.sum_supported_moebius.__information_unit,
  realizationName := `Reg.D5.S3.Arith.MoebiusLogarithmic.CoprimeConvolution.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature
    (fun _ _ n => ArithmeticFunction.moebius n) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.MoebiusLogarithmic.CoprimeConvolution,
    definition := none, coordinates := #[0],
    readouts := #[{ path := #["body", "body", "arg", "fn", "arg"], stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

#print axioms registration
end Reg.D5.S3.Arith.MoebiusLogarithmic.CoprimeConvolution
