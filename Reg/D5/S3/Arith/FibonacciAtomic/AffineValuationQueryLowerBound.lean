import D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound
import Reg.Support.DependentFamily

set_option autoImplicit false
open _root_.D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound
open _root_.D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound

abbrev signature : Signature where
  Params := (p : ℕ) × (e : ℕ) × (d : ℕ) ×
    PassiveProtocol (AffineQuery p e d) (fun _ => ℕ)
  State k := Point k.1 k.2.1 k.2.2.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature
    (fun _ k x =>
      (runPassiveProtocol (affineReadout k.1 k.2.1 k.2.2.1) k.2.2.2 x).length)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (p e d : ℕ) (hp : p.Prime) (he : 1 ≤ e) (hd : 1 ≤ d),
    (∀ T : PassiveProtocol (AffineQuery p e d) (fun _ => ℕ),
      Function.Injective (runPassiveProtocol (affineReadout p e d) T) →
      ∃ x : Point p e d, d * e * (p - 1) ≤ R.readout () ⟨p, e, d, T⟩ x) ∧
    (∀ (policy : List (Sigma (fun _ : AffineQuery p e d => ℕ)) →
        Sum (AffineQuery p e d) (Point p e d))
      (trace : Point p e d → List (Sigma (fun _ : AffineQuery p e d => ℕ)))
      (fuel : Point p e d → ℕ),
      (∀ x, _root_.D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization.execute
        (affineReadout p e d) policy (fuel x) [] x = some (trace x, x)) →
      ∃ x : Point p e d, d * e * (p - 1) ≤ (trace x).length)

def binaryTree : PassiveProtocol (AffineQuery 2 1 1) (fun _ => ℕ) :=
  .query ((fun _ => 1), 0) (fun _ => .stop)

theorem binary_identifies :
    Function.Injective (runPassiveProtocol (affineReadout 2 1 1) binaryTree) := by
  decide

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨x, bad⟩ := (h 2 1 1 (by norm_num) (by decide) (by decide)).1
    binaryTree binary_identifies
  norm_num [rejected, realize] at bad

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨affine_valuation_query_lower_bound, rejected, rejected_law⟩
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
    cases i
    let T : PassiveProtocol (AffineQuery 2 1 1) (fun _ => ℕ) :=
      .query ((fun _ => 1), 0) (fun r => if r = 1 then .stop else binaryTree)
    refine ⟨⟨2, 1, 1, T⟩, (0 : Point 2 1 1), (1 : Point 2 1 1), ?_⟩
    have zeroResponse : affineReadout 2 1 1 ((fun _ => 1), 0)
        (0 : Point 2 1 1) = 1 := by
      norm_num [affineReadout, affineValue,
        _root_.D5.S3.Observer.Budget.ResidueLeafOptimality.residueReadout,
        Fin.sum_univ_one, Finset.range_add_one, ZMod.val_one_eq_one_mod]
    have oneResponse : affineReadout 2 1 1 ((fun _ => 1), 0)
        (1 : Point 2 1 1) = 0 := by
      norm_num [affineReadout, affineValue,
        _root_.D5.S3.Observer.Budget.ResidueLeafOptimality.residueReadout,
        Fin.sum_univ_one, Finset.range_add_one, ZMod.val_one_eq_one_mod]
    change (runPassiveProtocol (affineReadout 2 1 1) T 0).length ≠
      (runPassiveProtocol (affineReadout 2 1 1) T 1).length
    simp [T, binaryTree, runPassiveProtocol, zeroResponse, oneResponse]

register_information_theorem affine_valuation_query_lower_bound in arena
  readout via (realize signature
    (fun _ k x =>
      (runPassiveProtocol (affineReadout k.1 k.2.1 k.2.2.1) k.2.2.2 x).length)
    (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound
    coordinates := #[0, 1, 2, 6]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg",
        "body", "body", "arg", "body", "arg"]
      stateBinder := 8 }] })
  escape continues (open)

#print axioms registration

end Reg.D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound
