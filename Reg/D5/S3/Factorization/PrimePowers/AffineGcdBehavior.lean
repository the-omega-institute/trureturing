import D5.S3.Factorization.PrimePowers.AffineGcdBehavior
import Reg.Support.DependentFamily

open _root_.D5.S3.Factorization.PrimePowers.AffineGcdBehavior
open _root_.D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality (runWord)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior

namespace Word

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
  realize signature (fun _ p x => (runWord (update p.2.1) p.2.2 x).val)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ (H : Nat) (A : List ℕ+) (w : List (Operation A)),
    ∃ a t : Nat, 0 < a ∧ libraryGcd H A ∣ t ∧
      ∀ x : ℕ+, R.readout () ⟨H, A, w⟩ x = a * (x : ℕ) + t

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨a, t, ha, _, hrun⟩ := h 2 [] []
  have h1 : 0 = a + t := by
    simpa [rejected, realize] using hrun (1 : ℕ+)
  omega

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨by
    intro H A w
    exact affine_word_translation H A w,
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

register_information_theorem affine_word_translation in arena
  readout via (realize signature
    (fun _ p x => (runWord (update p.2.1) p.2.2 x).val)
    (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Factorization.PrimePowers.AffineGcdBehavior
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "arg", "body", "arg", "body",
        "arg", "arg", "body", "fn", "arg"]
      stateBinder := 5 }] })
  escape continues (open)

end Word

namespace Action

abbrev signature : Signature where
  Params := Σ H : Nat, Σ A : List ℕ+, Σ a : ℕ+, List (Fin A.length)
  State _ := ℕ+
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Nat
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p x =>
    (runWord (update p.2.1) (Sum.inl p.2.2.1 :: p.2.2.2.map Sum.inr) x).val)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ (H : Nat) (hH : 2 ≤ H) (A : List ℕ+)
      (a : ℕ+) (t : Nat) (ht : libraryGcd H A ∣ t),
    ∃ ws : List (Fin A.length), ∀ x : ℕ+,
      ((R.readout () ⟨H, A, a, ws⟩ x : Nat) : ZMod H) =
        (((a : Nat) * (x : Nat) + t : Nat) : ZMod H)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨ws, hw⟩ := h 2 (by omega) [] 1 0 (by simp [libraryGcd])
  have hc := hw 1
  norm_num [rejected, realize] at hc

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨by
    intro H hH A a t ht
    exact affine_action_realization H hH A a t ht,
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
    refine ⟨⟨2, [], 1, []⟩, (1 : ℕ+), (2 : ℕ+), ?_⟩
    change (1 : Nat) ≠ 2
    decide

register_information_theorem affine_action_realization in arena
  readout via (realize signature (fun _ p x =>
    (runWord (update p.2.1) (Sum.inl p.2.2.1 :: p.2.2.2.map Sum.inr) x).val)
    (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Factorization.PrimePowers.AffineGcdBehavior
    coordinates := #[0, 2, 3, 6]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg",
        "body", "body", "fn", "arg", "arg"]
      stateBinder := 7 }] })
  escape continues (open)

end Action

end Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior
