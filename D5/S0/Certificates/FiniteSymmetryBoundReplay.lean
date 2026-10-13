/- GID: D5/S0/Certificates/FiniteSymmetryBoundReplay
   generality: G
   mirror-B: D5/B/S0/Certificates/FiniteSymmetryBoundReplay
   mirror-E: none(waiver:finite-symbolic-certificate-replay)
   anchors: []
   utility: none
   digest: Raw exhaustive branch trees with score bounds and rank-decreasing symmetries certify a global finite score bound. -/

import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Finset.Sort
import Mathlib.Order.PiLex
import Mathlib.Tactic

/-!
The repository's finite-exhaustion and branch-atlas interfaces require checking
every full event in a branch. Inflation scores instead admit partial-assignment
bounds and symmetry cuts. This replay checks exhaustive value branches; a
symmetry cut must decrease a natural rank for every compatible completion.
No branch omitted by symmetry is accepted merely on the generator's word.

This module contains replay soundness. A concrete application must separately
prove its partial bounds and the rank and score properties of its actual
symmetries, and kernel-check the concrete raw tree. An external positive
minimum does not discharge any of those obligations.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Certificates.FiniteSymmetryBoundReplay

variable {Coord Value Sym : Type*} [Fintype Value]
  [DecidableEq Coord] [DecidableEq Value]

abbrev Event (Coord Value : Type*) := Coord → Value
abbrev Partial (Coord Value : Type*) := Coord → Option Value

/-- Every assigned coordinate must agree with the actual event. -/
def Compatible (p : Partial Coord Value) (e : Event Coord Value) : Prop :=
  ∀ i a, p i = some a → e i = a

/-- Raw proof data: a checked bound, a checked symmetry cut, or all value branches. -/
inductive Tree (Coord Value Sym : Type*) where
  | bound
  | symmetry (s : Sym)
  | split (i : Coord) (children : Value → Tree Coord Value Sym)

/-- The checker never trusts a node's asserted validity or a claimed search minimum. -/
def check (lower : Partial Coord Value → ℤ)
    (dominates : Sym → Partial Coord Value → Bool) (gap : ℤ)
    (p : Partial Coord Value) : Tree Coord Value Sym → Bool
  | .bound => decide (gap ≤ lower p)
  | .symmetry s => dominates s p
  | .split i children => decide (∀ a, check lower dominates gap
      (Function.update p i (some a)) (children a) = true)

/-- A complete partial event supplies every observed coordinate. -/
def completed (e : Event Coord Value) : Partial Coord Value := fun i => some (e i)

/-- Local monotonicity along actual unknown-coordinate fillings earns every
partial score bound. The stored partial values need not be trusted minima. -/
theorem partial_lower_bound_sound [Fintype Coord]
    (score : Event Coord Value → ℤ) (lower : Partial Coord Value → ℤ)
    (hfull : ∀ e, lower (completed e) = score e)
    (hstep : ∀ p i a, p i = none → lower p ≤ lower (Function.update p i (some a)))
    (p : Partial Coord Value) (e : Event Coord Value) (hp : Compatible p e) :
    lower p ≤ score e := by
  classical
  let fill (s : Finset Coord) : Partial Coord Value :=
    fun i => if i ∈ s then some (e i) else p i
  have h : ∀ s : Finset Coord, lower p ≤ lower (fill s) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [fill]
    | @insert i s hi ih =>
      have hupdate : fill (insert i s) = Function.update (fill s) i (some (e i)) := by
        funext j
        by_cases hj : j = i
        · subst j; simp [fill]
        · simp [fill, hj, Function.update_of_ne hj]
      rw [hupdate]
      cases hpi : p i with
      | none =>
        exact ih.trans (hstep _ i (e i) (by simp [fill, hi, hpi]))
      | some a =>
        have ha : e i = a := hp i a hpi
        have hsame : Function.update (fill s) i (some (e i)) = fill s := by
          funext j
          by_cases hj : j = i
          · subst j; simp [fill, hi, hpi, ha]
          · simp [hj]
        simpa only [hsame] using ih
  have hu : fill Finset.univ = completed e := by funext i; simp [fill, completed]
  simpa only [hu, hfull] using h Finset.univ

private theorem compatible_update (p : Partial Coord Value) (e : Event Coord Value)
    (hp : Compatible p e) (i : Coord) :
    Compatible (Function.update p i (some (e i))) e := by
  intro j a h
  by_cases hj : j = i
  · subst j
    simp only [Function.update_self, Option.some.injEq] at h
    exact h
  · rw [Function.update_of_ne hj] at h
    exact hp j a h

/-- A bad event accepted by the replay has another bad event of smaller rank.
The proof uses the actual child selected by that same event at every split. -/
theorem checked_tree_forces_smaller_bad_event
    (score : Event Coord Value → ℤ) (rank : Event Coord Value → ℕ)
    (act : Sym → Event Coord Value → Event Coord Value)
    (lower : Partial Coord Value → ℤ)
    (dominates : Sym → Partial Coord Value → Bool) (gap : ℤ)
    (hlower : ∀ p e, Compatible p e → lower p ≤ score e)
    (hscore : ∀ s e, score (act s e) = score e)
    (hdominates : ∀ s p, dominates s p = true →
      ∀ e, Compatible p e → rank (act s e) < rank e)
    (tree : Tree Coord Value Sym) (p : Partial Coord Value)
    (accepted : check lower dominates gap p tree = true)
    (e : Event Coord Value) (hp : Compatible p e) (hbad : score e < gap) :
    ∃ e', score e' < gap ∧ rank e' < rank e := by
  induction tree generalizing p with
  | bound =>
    have hg : gap ≤ lower p := of_decide_eq_true accepted
    exact False.elim ((not_lt_of_ge (hg.trans (hlower p e hp))) hbad)
  | symmetry s =>
    exact ⟨act s e, by simpa only [hscore] using hbad,
      hdominates s p accepted e hp⟩
  | split i children ih =>
    have hc : ∀ a, check lower dominates gap
        (Function.update p i (some a)) (children a) = true :=
      of_decide_eq_true accepted
    exact ih (e i) _ (hc (e i)) (compatible_update p e hp i)

/-- An accepted exhaustive tree proves the global score bound. Rank descent
excludes circular or mutually supporting symmetry cuts. -/
theorem checked_global_lower_bound
    (score : Event Coord Value → ℤ) (rank : Event Coord Value → ℕ)
    (act : Sym → Event Coord Value → Event Coord Value)
    (lower : Partial Coord Value → ℤ)
    (dominates : Sym → Partial Coord Value → Bool) (gap : ℤ)
    (hlower : ∀ p e, Compatible p e → lower p ≤ score e)
    (hscore : ∀ s e, score (act s e) = score e)
    (hdominates : ∀ s p, dominates s p = true →
      ∀ e, Compatible p e → rank (act s e) < rank e)
    (tree : Tree Coord Value Sym)
    (accepted : check lower dominates gap (fun _ => none) tree = true) :
    ∀ e, gap ≤ score e := by
  have h : ∀ k : ℕ, ∀ e : Event Coord Value, rank e = k → gap ≤ score e := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro e he
      by_contra hb
      have hbad : score e < gap := lt_of_not_ge hb
      have hp : Compatible (fun _ => none) e := by
        intro i a ha
        cases ha
      obtain ⟨e', hbad', hrank⟩ := checked_tree_forces_smaller_bad_event
        score rank act lower dominates gap hlower hscore hdominates
        tree (fun _ => none) accepted e hp hbad
      have hgood := ih (rank e') (he ▸ hrank) e' rfl
      exact (not_lt_of_ge hgood) hbad'
  intro e
  exact h (rank e) e rfl

/-! A concrete symmetry cut needs an earned descent relation. The following
partial lexicographic witness is decidable from assigned values alone. It also
recognizes coordinates fixed by the symmetry even when their values are unknown.
This covers both source-copy permutations and simultaneous outcome relabeling. -/

namespace FiniteLex

variable {n k : ℕ}

def act (σ : Fin n ≃ Fin n) (ν : Fin k ≃ Fin k)
    (e : Event (Fin n) (Fin k)) : Event (Fin n) (Fin k) := fun i => ν (e (σ i))

def dominates (σ : Fin n ≃ Fin n) (ν : Fin k ≃ Fin k)
    (p : Partial (Fin n) (Fin k)) : Bool :=
  decide (∃ i a b, p (σ i) = some a ∧ p i = some b ∧ ν a < b ∧
    ∀ j, j < i →
      (σ j = j ∧ ∀ v, ν v = v) ∨
      ∃ a b, p (σ j) = some a ∧ p j = some b ∧ ν a = b)

noncomputable def rank (e : Event (Fin n) (Fin k)) : ℕ :=
  ((Fintype.orderIsoFinOfCardEq (Lex (Event (Fin n) (Fin k))) rfl).symm
    (toLex e)).val

/-- The actual completed event, rather than a guessed representative, becomes
strictly smaller at a checked symmetry cut. -/
theorem dominates_rank_lt (σ : Fin n ≃ Fin n) (ν : Fin k ≃ Fin k)
    (p : Partial (Fin n) (Fin k)) (h : dominates σ ν p = true)
    (e : Event (Fin n) (Fin k)) (hp : Compatible p e) :
    rank (act σ ν e) < rank e := by
  obtain ⟨i, a, b, ha, hb, hab, hprefix⟩ := of_decide_eq_true h
  have hlex : toLex (act σ ν e) < toLex e := by
    refine ⟨i, ?_, ?_⟩
    · intro j hj
      rcases hprefix j hj with ⟨hσ, hν⟩ | ⟨a, b, ha, hb, hab⟩
      · simp [act, hσ, hν]
      · simpa only [act, Pi.toLex_apply, hp _ _ ha, hp _ _ hb] using hab
    · simpa only [act, Pi.toLex_apply, hp _ _ ha, hp _ _ hb] using hab
  exact (Fintype.orderIsoFinOfCardEq (Lex (Event (Fin n) (Fin k))) rfl).symm.strictMono hlex

end FiniteLex

/-- Top-level export of the finite lexicographic descent used by the replay tree.
This wrapper keeps the reusable certificate declaration addressable by the
repository's canonical module/declaration GID format. -/
theorem finite_lex_dominates_rank_lt {n k : ℕ}
    (σ : Fin n ≃ Fin n) (ν : Fin k ≃ Fin k)
    (p : Partial (Fin n) (Fin k)) (h : FiniteLex.dominates σ ν p = true)
    (e : Event (Fin n) (Fin k)) (hp : Compatible p e) :
    FiniteLex.rank (FiniteLex.act σ ν e) < FiniteLex.rank e := by
  exact FiniteLex.dominates_rank_lt σ ν p h e hp

#print axioms partial_lower_bound_sound
#print axioms checked_global_lower_bound
#print axioms FiniteLex.dominates_rank_lt
#print axioms finite_lex_dominates_rank_lt

end D5.S0.Certificates.FiniteSymmetryBoundReplay
