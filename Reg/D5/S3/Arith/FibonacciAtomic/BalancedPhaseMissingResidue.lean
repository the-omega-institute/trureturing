import D5.S3.Arith.FibonacciAtomic.BalancedPhaseMissingResidue
import Reg.Support.DependentFamily

set_option autoImplicit false

open _root_.D5.S3.Arith.FibonacciAtomic.BalancedPhaseMissingResidue
open _root_.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion
open _root_.D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd
open _root_.D5.S3.Arith.ZeckendorfFutureKernel (value)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Arith.FibonacciAtomic.BalancedPhaseMissingResidue

noncomputable section

abbrev responseSignature : Signature where
  Params := Nat × List Window
  State _ := ActualPrefix
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Option Nat
  Anchor := Empty
  finiteAnchor := inferInstance

def responseActual : Realization responseSignature :=
  realize responseSignature (fun _ params source => rawIndex params.1 source params.2)
    (fun e => nomatch e)

def responseRejected : Realization responseSignature :=
  realize responseSignature (fun _ _ _ => none) (fun e => nomatch e)

abbrev responseArena : Arena where
  signature := responseSignature
  Law R := ∀ H p a L : Nat, 2 ≤ H → p.Prime → 1 ≤ a → H.factorization p = a →
    1 ≤ L → envelope L + 1 < p ^ a - p ^ a / p →
    ∃ j : Nat, ∃ x y : ActualPrefix,
      x.past.length = j ∧ y.past.length = j ∧ nextRow x = nextRow y ∧
      ((nextRow x).1 : ZMod H) = Int.fib (-3 * (L / 2 : Nat)) ∧
      ((nextRow x).2 : ZMod H) = Int.fib (-3 * (L / 2 : Nat) + 1) ∧
      0 < sourceNumber x ∧ 0 < sourceNumber y ∧
      (∀ w : List Window, w.length ≤ L → R.readout () ⟨H,w⟩ x = R.readout () ⟨H,w⟩ y) ∧
      ¬ (∀ w : List Window, R.readout () ⟨H,w⟩ x = R.readout () ⟨H,w⟩ y)

theorem response_rejected_law : ¬ responseArena.Law responseRejected := by
  intro h
  have hfull : (7 : Nat).factorization 7 = 1 := Nat.Prime.factorization_self (by decide)
  have hsmall : envelope 1 + 1 < 7 ^ 1 - 7 ^ 1 / 7 := by norm_num [envelope]
  obtain ⟨j, x, y, _, _, _, _, _, _, _, _, impossible⟩ :=
    h 7 7 1 1 (by decide) (by decide) (by decide) hfull (by decide) hsmall
  exact impossible (fun _ => rfl)

def responseRegistration : Registration responseArena (responseArena.Law responseActual) where
  actual := responseActual
  bridge := Iff.rfl
  variation := ⟨result, responseRejected, response_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨responseRejected, ?_, rfl, response_rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    cases i
    exact ⟨⟨5, []⟩, ⟨true, [], rfl⟩, ⟨false, [.high], rfl⟩, by decide⟩

register_information_theorem
  _root_.D5.S3.Arith.FibonacciAtomic.BalancedPhaseMissingResidue.result in responseArena
  readout via (realize responseSignature
    (fun _ params source => rawIndex params.1 source params.2) (fun e => nomatch e))
  realizes responseRegistration
  escape from source ({
    owner := `D5.S3.Arith.FibonacciAtomic.BalancedPhaseMissingResidue
    coordinates := #[0, 13]
    readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body",
      "body", "body", "body", "arg", "body", "arg", "body", "arg", "body", "arg",
      "arg", "arg", "arg", "arg", "arg", "arg", "fn", "arg", "body", "body",
      "fn", "arg"], stateOperand := some #["fn", "arg"] }] })
  escape continues (open)

#print axioms responseRegistration

end

end Reg.D5.S3.Arith.FibonacciAtomic.BalancedPhaseMissingResidue
