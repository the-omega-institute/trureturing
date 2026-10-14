/- Prepared terminal-star replay optimization. A star has all four original
children equal to the bound node. It checks their four exact updated lowers
without materializing four future caches that the original checker discards.
All other nodes follow the same actual DAG, prefix, margin and value branches.
No full-replay acceptance is asserted by this representation theorem. -/

import D5.S3.Quantum.Entanglement.EJM.EJMAggregateCachePacking
import D5.S3.Quantum.Entanglement.EJM.EJMCompactDominates

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

namespace D5.S3.Quantum.Entanglement.EJM.EJMTerminalStarReplay

open EJMCompactPartial (Coord Value PackedPartial advance checkPacked)
open EJMAggregateCachePacking (AggregateCache step lower delta)
open EJMCompactDominates (dominatesPacked checkFast)

def zeroChildren (children : Value → Fin EJMGlobalDAGData.Size) : Bool :=
  decide (∀ a, (children a).val = 0)

def star (cache : AggregateCache) (i : Coord) (gap : ℤ) : Bool :=
  decide (∀ a : Value, gap ≤ cache.total + delta cache.words i a)

private theorem bound_at_zero (fuel : ℕ) :
    EJMGlobalDAGData.nodes fuel 0 = .bound := by
  simp only [EJMGlobalDAGData.nodes, Fin.val_zero, ↓reduceIte]

theorem star_eq_children (fuel : ℕ) (children : Value → Fin EJMGlobalDAGData.Size)
    (cache : AggregateCache) (i : Coord) (gap : ℤ) (q : PackedPartial)
    (hzero : zeroChildren children = true) :
    star cache i gap =
      decide (∀ a : Value,
        checkFast step lower gap (fuel + 1) (children a)
          (step cache i a) (advance (fuel + 1) q i a) = true) := by
  have children_zero (a : Value) : children a = 0 :=
    Fin.ext (of_decide_eq_true hzero a)
  simp only [star, children_zero, checkFast, bound_at_zero, lower, step]
  apply decide_eq_decide.mpr
  constructor
  · intro h a
    exact decide_eq_true (h a)
  · intro h a
    exact of_decide_eq_true (h a)

def check (gap : ℤ) :
    ℕ → Fin EJMGlobalDAGData.Size → AggregateCache → PackedPartial → Bool
  | 0, _, _, _ => false
  | fuel + 1, index, cache, q =>
    match EJMGlobalDAGData.nodes (fuel + 1) index with
    | .bound => decide (gap ≤ lower cache)
    | .symmetry s => dominatesPacked s q
    | .split i children =>
      if 0 < fuel ∧ zeroChildren children = true then star cache i gap
      else decide (∀ a : Value,
        check gap fuel (children a) (step cache i a) (advance fuel q i a) = true)

theorem check_eq_checkFast (gap : ℤ) (fuel : ℕ) (index : Fin EJMGlobalDAGData.Size)
    (cache : AggregateCache) (q : PackedPartial) :
    check gap fuel index cache q = checkFast step lower gap fuel index cache q := by
  induction fuel generalizing index cache q with
  | zero => rfl
  | succ fuel ih =>
    cases hn : EJMGlobalDAGData.nodes (fuel + 1) index with
    | bound => simp only [check, checkFast, hn]
    | symmetry s => simp only [check, checkFast, hn]
    | split i children =>
      simp only [check, checkFast, hn]
      by_cases hstar : 0 < fuel ∧ zeroChildren children = true
      · rw [if_pos hstar]
        obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hstar.1)
        exact star_eq_children n children cache i gap q hstar.2
      · rw [if_neg hstar]
        simp only [ih]

theorem check_eq_original (fuel : ℕ) (index : Fin EJMGlobalDAGData.Size)
    (cache : AggregateCache) (h : EJMAggregateCachePacking.Valid cache) (q : PackedPartial)
    (hwell : EJMCompactPartial.WellFormed q) (hinv : q.depth + fuel = 21) :
    check EJMPartialBoundData.scale fuel index cache q =
      D5.S0.Certificates.FiniteCachedSymmetryDAGReplay.check EJMGlobalDAGData.nodes
        EJMCacheState.step EJMCacheState.lower EJMGlobalScoreSymmetry.dominates
        EJMPartialBoundData.scale fuel index (EJMCachePacking.decode cache.words)
        (EJMCompactPartial.decode q) := by
  rw [check_eq_checkFast,
    EJMCompactDominates.checkFast_eq_checkPacked step lower _ fuel index cache q hwell hinv]
  exact EJMAggregateCachePacking.replay_eq_original fuel index cache h q hwell hinv

#print axioms star_eq_children
#print axioms check_eq_checkFast
#print axioms check_eq_original

end D5.S3.Quantum.Entanglement.EJM.EJMTerminalStarReplay
