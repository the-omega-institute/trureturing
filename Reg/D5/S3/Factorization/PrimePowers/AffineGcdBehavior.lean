import D5.S3.Factorization.PrimePowers.AffineGcdBehavior
import Reg.Support.DependentFamily

open _root_.D5.S3.Factorization.PrimePowers.AffineGcdBehavior
open _root_.D5.S3.Observer.Budget.PrimePowerNonadaptiveResolution (depth)
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

namespace Local

abbrev signature : Signature where
  Params := Σ _ : Nat, Nat
  State q := ZMod (q.1 ^ q.2)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Nat
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ q z => depth q.1 q.2 0 z) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨⟨2, 1⟩, (0 : ZMod 2), (1 : ZMod 2), ?_⟩
  have hzero : depth 2 1 0 (0 : ZMod 2) = 1 :=
    ((D5.S3.Observer.Budget.PrimePowerNonadaptiveResolution.result
      2 1 (by decide)).2.1 0 0).2 rfl
  have hone : depth 2 1 0 (1 : ZMod 2) ≠ 1 := by
    intro h
    have hz := ((D5.S3.Observer.Budget.PrimePowerNonadaptiveResolution.result
      2 1 (by decide)).2.1 0 1).1 h
    exact (by decide : (1 : ZMod 2) ≠ 0) hz
  change depth 2 1 0 (0 : ZMod 2) ≠ depth 2 1 0 (1 : ZMod 2)
  rw [hzero]
  exact Ne.symm hone


namespace Complete

@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ (p h e : Nat) (hp : p.Prime) (hh : 1 ≤ h) (heh : e ≤ h),
    (∀ X Y : Int,
      localEncoding p h e hp hh heh (X : ZMod (p ^ h)) =
        localEncoding p h e hp hh heh (Y : ZMod (p ^ h)) ↔
      ∀ (a : ℕ+) (b : Int),
        R.readout () ⟨p, h⟩
            ((((a : Nat) : Int) * X + (p : Int) ^ e * b : Int) : ZMod (p ^ h)) =
          depth p h 0 ((((a : Nat) : Int) * Y + (p : Int) ^ e * b : Int) : ZMod (p ^ h))) ∧
    (∀ c : LocalCode p h e, ∃ X : Int,
      localEncoding p h e hp hh heh (X : ZMod (p ^ h)) = c)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have h := ((law 2 1 0 (by decide) (by decide) (by decide)).1 0 0).1 rfl
    (1 : ℕ+) 0
  have htop : depth 2 1 0 (0 : ZMod 2) = 1 :=
    ((D5.S3.Observer.Budget.PrimePowerNonadaptiveResolution.result
      2 1 (by decide)).2.1 0 0).2 rfl
  have h' : (0 : Nat) = depth 2 1 0 (0 : ZMod 2) := by
    simpa [rejected, realize] using h
  omega

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨by
    intro p h e hp hh heh
    exact local_encoding_complete p h e hp hh heh,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := Local.dependence

register_information_theorem local_encoding_complete in arena
  readout via (realize signature (fun _ q z => depth q.1 q.2 0 z)
    (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Factorization.PrimePowers.AffineGcdBehavior
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "fn", "arg", "body", "body", "arg", "body", "body", "fn", "arg"]
      stateOperand := some #["arg"] }] })
  escape continues (open)

end Complete

end Local

end Reg.D5.S3.Factorization.PrimePowers.AffineGcdBehavior
