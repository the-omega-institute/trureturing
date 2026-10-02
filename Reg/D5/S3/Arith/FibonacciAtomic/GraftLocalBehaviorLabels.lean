import D5.S3.Arith.FibonacciAtomic.GraftLocalBehaviorLabels
import Reg.Support.DependentFamily

open _root_.D5.S3.Arith.FibonacciAtomic.GraftLocalBehaviorLabels
open _root_.D5.S3.Arith.FibonacciAtomic.GraftAffineClosure (step)
open _root_.D5.S3.Arith.FibonacciAtomic.TimeSampling (zeroRank)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.Arith.FibonacciAtomic.GraftLocalBehaviorLabels

@[reducible] def signature : Signature where
  Params := Σ p : ℕ, Σ m : ℕ, (ZMod (p ^ m) × ZMod (p ^ m)) × ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ a k => (step^[k] a.2.2.1).1 = 0) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ (p m : ℕ) (hp : p.Prime)
    (x : ZMod (p ^ m) × ZMod (p ^ m)) (hx : IsUnit x.1 ∨ IsUnit x.2)
    (t k : ℕ) (ht : (step^[t] x).1 = 0),
    R.readout () ⟨p, m, x, t⟩ k ↔ k % zeroRank (p ^ m) = t % zeroRank (p ^ m)

theorem actual_law : arena.Law actual := primitive_hit_phase

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact (h 2 1 (by decide) (0, 1) (Or.inr isUnit_one) 0 0 rfl).mpr rfl

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨⟨2, 1, (0, 1), 0⟩, 0, 1, ?_⟩
    cases i
    norm_num [actual, realize, step]
    decide

register_information_theorem primitive_hit_phase in arena
  readout via (realize signature
    (fun _ a k => (step^[k] a.2.2.1).1 = 0) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Arith.FibonacciAtomic.GraftLocalBehaviorLabels
    coordinates := #[0, 1, 3, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 6 }] })
  escape continues (open)

#print axioms registration

end Reg.D5.S3.Arith.FibonacciAtomic.GraftLocalBehaviorLabels
