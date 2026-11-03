import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.MoebiusLogarithmic.MorkenFirstDivisorSum
import Reg.Support.DependentFamily

/-! Source-bound audit of the full positive-input divisor-sum identity. -/

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Finset ArithmeticFunction
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable
namespace Reg.D5.S3.Arith.MoebiusLogarithmic.MorkenFirstDivisorSum

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ n => ∑ k ∈ (Icc 1 n).filter (fun k => k.Coprime n), moebius k)
  (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ), 0 < n → R.readout () () n =
    ∑ d ∈ n.divisors.filter (fun d => moebius d ≠ 0),
      ∑ m ∈ (Icc 1 (n / d)).filter (fun m => m.Coprime d), moebius m

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 1 (by decide)
  have ht := _root_.D5.S3.Arith.MoebiusLogarithmic.MorkenFirstDivisorSum.result 1 (by decide)
  rw [← ht] at hb
  norm_num [rejected, realize, Finset.sum_filter] at hb

def registration : Registration arena
    (∀ (n : ℕ), 0 < n →
      (∑ k ∈ (Icc 1 n).filter (fun k => k.Coprime n), moebius k) =
        ∑ d ∈ n.divisors.filter (fun d => moebius d ≠ 0),
          ∑ m ∈ (Icc 1 (n / d)).filter (fun m => m.Coprime d), moebius m) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.Arith.MoebiusLogarithmic.MorkenFirstDivisorSum.result,
    rejected, rejected_law⟩
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
    refine ⟨(), (1 : ℕ), (3 : ℕ), ?_⟩
    change (∑ k ∈ (Icc 1 1).filter (fun k => k.Coprime 1), moebius k) ≠
      ∑ k ∈ (Icc 1 3).filter (fun k => k.Coprime 3), moebius k
    rw [show (Icc 1 1).filter (fun k => k.Coprime 1) = {1} by decide,
      show (Icc 1 3).filter (fun k => k.Coprime 3) = {1, 2} by decide]
    norm_num [moebius_apply_prime (by decide : Nat.Prime 2)]

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Arith.MoebiusLogarithmic.MorkenFirstDivisorSum.result)
    (type_of% (realize.{0,0,0,0,0} signature
      (fun _ _ n => ∑ k ∈ (Icc 1 n).filter (fun k => k.Coprime n), moebius k)
      (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Arith.MoebiusLogarithmic.MorkenFirstDivisorSum.result.__information_unit,
  realizationName := `Reg.D5.S3.Arith.MoebiusLogarithmic.MorkenFirstDivisorSum.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature
    (fun _ _ n => ∑ k ∈ (Icc 1 n).filter (fun k => k.Coprime n), moebius k)
    (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.MoebiusLogarithmic.MorkenFirstDivisorSum,
    definition := none, coordinates := #[],
    readouts := #[{ path := #["body", "body", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

#print axioms registration
end Reg.D5.S3.Arith.MoebiusLogarithmic.MorkenFirstDivisorSum
