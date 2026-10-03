import D5.S3.Factorization.PrimePowers.GlobalAffineGcdBehavior
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Factorization.PrimePowers.GlobalAffineGcdBehavior

open _root_.D5.S3.Factorization.PrimePowers.AffineGcdBehavior
open _root_.D5.S3.Factorization.PrimePowers.GlobalAffineGcdBehavior
open _root_.D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality (runWord)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Σ H : Nat, Σ A : List ℕ+, List (Operation A)
  State _ := ℕ+
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Nat
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p x => Nat.gcd (runWord (update p.2.1) p.2.2 x).val p.1)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ (H : Nat) (hH : 2 ≤ H) (A : List ℕ+),
    (∀ x y : ℕ+, globalEncoding H hH A x = globalEncoding H hH A y ↔
      ∀ w : List (Operation A), R.readout () ⟨H, A, w⟩ x =
        Nat.gcd (runWord (update A) w y).val H) ∧
    (∀ x y : ℕ+, globalEncoding H hH A x = globalEncoding H hH A y ↔
      ∀ w : List (Operation A), H / Nat.gcd (runWord (update A) w x).val H =
        H / Nat.gcd (runWord (update A) w y).val H) ∧
    (∀ x y : ℕ+, globalEncoding H hH A x ≠ globalEncoding H hH A y →
      ∃ (p : H.primeFactors) (a : ℕ+) (ws : List (Fin A.length)),
        (Nat.gcd (runWord (update A) (Sum.inl a :: ws.map Sum.inr) x).val H).factorization p.val ≠
          (Nat.gcd (runWord (update A) (Sum.inl a :: ws.map Sum.inr) y).val H).factorization p.val) ∧
    Function.Surjective (globalEncoding H hH A)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hc := (h 2 (by omega) []).1 (1 : ℕ+) 1 |>.1 rfl
  have impossible := hc []
  norm_num [rejected, realize, runWord] at impossible

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨by
    intro H hH A
    exact global_encoding_complete H hH A,
    rejected, rejected_law⟩
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
    refine ⟨⟨2, [], []⟩, (1 : ℕ+), (2 : ℕ+), ?_⟩
    change (1 : Nat) ≠ 2
    decide

register_information_theorem global_encoding_complete in arena
  readout via (realize signature
    (fun _ p x => Nat.gcd (runWord (update p.2.1) p.2.2 x).val p.1)
    (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Factorization.PrimePowers.GlobalAffineGcdBehavior
    coordinates := #[0, 2, 5]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "body", "body", "arg", "body", "fn", "arg"]
      stateBinder := 0
      stateOperand := some #["fn", "arg", "arg", "arg"] }] })
  escape continues (open)

#print axioms registration

end Reg.D5.S3.Factorization.PrimePowers.GlobalAffineGcdBehavior
