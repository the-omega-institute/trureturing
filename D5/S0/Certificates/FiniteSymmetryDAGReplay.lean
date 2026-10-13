/- GID: D5/S0/Certificates/FiniteSymmetryDAGReplay
   generality: G
   mirror-B: D5/B/S0/Certificates/FiniteSymmetryDAGReplay
   mirror-E: none(waiver:finite-symmetry-dag-replay)
   anchors: [D5/S0/Certificates/FiniteSymmetryBoundReplay]
   utility: none
   digest: Shared finite branch shapes are checked in each actual partial context with bounded unfolding and earned score and rank invariance. -/

import D5.S0.Certificates.FiniteSymmetryBoundReplay

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Certificates.FiniteSymmetryDAGReplay
open D5.S0.Certificates.FiniteSymmetryBoundReplay

variable {Coord Value Sym : Type*} [Fintype Value]
  [DecidableEq Coord] [DecidableEq Value] {N : ℕ}

inductive Node (N : ℕ) (Coord Value Sym : Type*) where
  | bound
  | symmetry (s : Sym)
  | split (i : Coord) (children : Value → Fin N)

/-- Fuel zero rejects. Shared shapes are evaluated separately in every reached
partial context; no arithmetic certificate is transferred between contexts. -/
def check
    (nodes : ℕ → Fin N → Node N Coord Value Sym)
    (lower : Partial Coord Value → ℤ)
    (dominates : Sym → Partial Coord Value → Bool) (gap : ℤ) :
    ℕ → Fin N → Partial Coord Value → Bool
  | 0, _, _ => false
  | fuel + 1, index, p =>
    match nodes (fuel + 1) index with
    | .bound => decide (gap ≤ lower p)
    | .symmetry s => dominates s p
    | .split i children => decide (∀ a,
        check nodes lower dominates gap fuel (children a)
          (Function.update p i (some a)) = true)

/-- The expansion is a mathematical interpretation, not a trusted imported tree. -/
def expand (nodes : ℕ → Fin N → Node N Coord Value Sym) :
    ℕ → Fin N → Tree Coord Value Sym
  | 0, _ => .bound
  | fuel + 1, index =>
    match nodes (fuel + 1) index with
    | .bound => .bound
    | .symmetry s => .symmetry s
    | .split i children => .split i (fun a => expand nodes fuel (children a))

private theorem accepted_expansion
    (nodes : ℕ → Fin N → Node N Coord Value Sym)
    (lower : Partial Coord Value → ℤ)
    (dominates : Sym → Partial Coord Value → Bool) (gap : ℤ)
    (fuel : ℕ) (index : Fin N) (p : Partial Coord Value)
    (accepted : check nodes lower dominates gap fuel index p = true) :
    FiniteSymmetryBoundReplay.check lower dominates gap p (expand nodes fuel index) = true := by
  induction fuel generalizing index p with
  | zero => simp only [check, Bool.false_eq_true] at accepted
  | succ fuel ih =>
    cases hn : nodes (fuel + 1) index with
    | bound => simpa only [check, expand, hn, FiniteSymmetryBoundReplay.check] using accepted
    | symmetry s =>
      simpa only [check, expand, hn, FiniteSymmetryBoundReplay.check] using accepted
    | split i children =>
      simp only [check, hn] at accepted
      have ha := of_decide_eq_true accepted
      simp only [expand, hn, FiniteSymmetryBoundReplay.check]
      apply decide_eq_true
      intro a
      exact ih (children a) (Function.update p i (some a)) (ha a)

/-- Bounded replay of shared shapes proves the same complete score bound as
literal exhaustive trees, while checking each actual partial context. -/
theorem checked_global_lower_bound
    (score : Event Coord Value → ℤ) (rank : Event Coord Value → ℕ)
    (act : Sym → Event Coord Value → Event Coord Value)
    (lower : Partial Coord Value → ℤ)
    (dominates : Sym → Partial Coord Value → Bool) (gap : ℤ)
    (hlower : ∀ p e, Compatible p e → lower p ≤ score e)
    (hscore : ∀ s e, score (act s e) = score e)
    (hdominates : ∀ s p, dominates s p = true →
      ∀ e, Compatible p e → rank (act s e) < rank e)
    (nodes : ℕ → Fin N → Node N Coord Value Sym) (fuel : ℕ) (root : Fin N)
    (accepted : check nodes lower dominates gap fuel root (fun _ => none) = true) :
    ∀ e, gap ≤ score e := by
  exact FiniteSymmetryBoundReplay.checked_global_lower_bound
    score rank act lower dominates gap hlower hscore hdominates
    (expand nodes fuel root)
    (accepted_expansion nodes lower dominates gap fuel root (fun _ => none) accepted)

#print axioms checked_global_lower_bound

end D5.S0.Certificates.FiniteSymmetryDAGReplay
