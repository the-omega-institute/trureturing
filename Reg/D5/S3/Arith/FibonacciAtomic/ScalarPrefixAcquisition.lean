import D5.S3.Arith.FibonacciAtomic.ScalarPrefixAcquisition
import Reg.Support.DependentFamily

set_option autoImplicit false
open _root_.D5.S3.Arith.FibonacciAtomic.ScalarPrefixAcquisition
open _root_.D5.S3.Observer.Budget.ResidueLeafOptimality
open _root_.D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Arith.FibonacciAtomic.ScalarPrefixAcquisition

abbrev signature : Signature where
  Params := (p : ℕ) × (e : ℕ) × (levels : ℕ) × (s : ℕ) × ℕ
  State k := ZMod (k.1 ^ k.2.1)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ k := ZMod (k.1 ^ k.2.1)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature
    (fun _ k y => evaluatePrefix k.1 k.2.1
      (prefixProgram k.1 k.2.1 k.2.2.1 k.2.2.2.1 k.2.2.2.2) y)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (p e : ℕ), p.Prime → 1 ≤ e →
    ∀ levels s r : ℕ, s + levels = e →
      ∀ y : ZMod (p ^ e), y.val % p ^ s = r →
        R.readout () ⟨p, e, levels, s, r⟩ y = y ∧
          (runPassiveProtocol (residueReadout p e)
            (forgetPrefix (prefixProgram p e levels s r)) y).length ≤
              levels * (p - 1) ∧
          legalPrefixRun p e (prefixProgram p e levels s r) y

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have impossible : (0 : ZMod 2) = 1 :=
    (h 2 1 (by norm_num) (by decide) 1 0 0 rfl 1 (by decide)).1
  exact (by decide : (0 : ZMod 2) ≠ 1) impossible

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨scalar_prefix_acquisition, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨⟨2, 1, 1, 0, 0⟩, (0 : ZMod 2), (1 : ZMod 2), ?_⟩
    change evaluatePrefix 2 1 (prefixProgram 2 1 1 0 0) (0 : ZMod 2) ≠
      evaluatePrefix 2 1 (prefixProgram 2 1 1 0 0) (1 : ZMod 2)
    rw [(scalar_prefix_acquisition 2 1 (by norm_num) (by decide)
      1 0 0 rfl 0 (by decide)).1,
      (scalar_prefix_acquisition 2 1 (by norm_num) (by decide)
        1 0 0 rfl 1 (by decide)).1]
    decide

register_information_theorem scalar_prefix_acquisition in arena
  readout via (realize signature
    (fun _ k y => evaluatePrefix k.1 k.2.1
      (prefixProgram k.1 k.2.1 k.2.2.1 k.2.2.2.1 k.2.2.2.2) y)
    (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Arith.FibonacciAtomic.ScalarPrefixAcquisition
    coordinates := #[0, 1, 4, 5, 6]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 8 }] })
  escape continues (open)

#print axioms registration

end Reg.D5.S3.Arith.FibonacciAtomic.ScalarPrefixAcquisition
