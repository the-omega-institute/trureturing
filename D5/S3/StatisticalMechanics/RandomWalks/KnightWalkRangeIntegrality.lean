/- GID: D5/S3/StatisticalMechanics/RandomWalks/KnightWalkRangeIntegrality
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/RandomWalks/KnightWalkRangeIntegrality
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: OEIS A309221: the expected range of a knight's walk times 2^(3n-3) is an integer. -/

/-
proof_shape: result: content
escape_witness: form (2): the conclusion `result` itself, produced on its live path
  by the explicit bijection `split` (walks of length k + 1 split by their first step, each class
  mapped onto the class of move 0 by a symmetry of the eight moves that preserves the number of
  visited squares), so the total over all walks is 8 times the total over walks starting with move 0
admission_basis: open-problem-resolution (issue #10116)
Direct frozen dependencies: none (pinned Mathlib only)
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality

open Finset

/-!
OEIS A309221 (N. J. A. Sloane, 2019): the expected number `E(n)` of distinct squares visited by a
knight's random walk on an infinite chessboard after `n` steps (A326954/A326955, the starting
square counted), normalized as `a(n) = E(n) · 2^(3n-3)` for `n > 0`; the entry notes "It is only a
conjecture that this is always an integer".
-/

/-- The eight knight moves; `move 0 = (1, 2)`. -/
def move : Fin 8 → ℤ × ℤ := ![(1, 2), (2, 1), (2, -1), (1, -2), (-1, -2), (-2, -1), (-2, 1), (-1, 2)]

/-- The position after the first `j` steps of the step sequence `w`. -/
def position {n : ℕ} (w : Fin n → Fin 8) (j : ℕ) : ℤ × ℤ :=
  ∑ i : Fin n, if (i : ℕ) < j then move (w i) else 0

/-- The squares visited during the `n` steps, the starting square included. -/
def visited {n : ℕ} (w : Fin n → Fin 8) : Finset (ℤ × ℤ) :=
  (range (n + 1)).image (position w)

/-- The expected number of distinct squares visited after `n` uniform knight steps. -/
def expectedRange (n : ℕ) : ℚ :=
  (∑ w : Fin n → Fin 8, ((visited w).card : ℚ)) / 8 ^ n

/-- OEIS A309221: for `n ≥ 1`, `a(n) = E(n) · 2^(3n-3)` is an integer (Sloane, 2019). -/
def claim : Prop := ∀ n : ℕ, 1 ≤ n → ∃ m : ℤ, expectedRange n * 2 ^ (3 * n - 3) = m

/-- The symmetry of the eight moves sending move `0` to move `m`. -/
private def sym (m : Fin 8) (i : Fin 8) : Fin 8 := if (m : ℕ) % 2 = 0 then m + i else m - i

/-- Its inverse. -/
private def symInv (m : Fin 8) (i : Fin 8) : Fin 8 := if (m : ℕ) % 2 = 0 then i - m else m - i

/-- The matching signed coordinate permutation of `ℤ²`. -/
private def latFun (m : Fin 8) (p : ℤ × ℤ) : ℤ × ℤ :=
  if (m : ℕ) % 2 = 0 then
    (if (m : ℕ) = 0 then p else if (m : ℕ) = 2 then (p.2, -p.1)
      else if (m : ℕ) = 4 then (-p.1, -p.2) else (-p.2, p.1))
  else
    (if (m : ℕ) = 1 then (p.2, p.1) else if (m : ℕ) = 3 then (p.1, -p.2)
      else if (m : ℕ) = 5 then (-p.2, -p.1) else (-p.1, p.2))

/-- The same map as an additive map. -/
private def lat (m : Fin 8) : ℤ × ℤ →+ ℤ × ℤ where
  toFun := latFun m
  map_zero' := by unfold latFun; split_ifs <;> simp
  map_add' p q := by
    unfold latFun
    split_ifs <;> ext <;> simp <;> ring

theorem result : claim := by
  have hsym : ∀ m i : Fin 8, move (sym m i) = lat m (move i) := by decide
  have hsym0 : ∀ m : Fin 8, sym m 0 = m := by decide
  have hinv1 : ∀ m i : Fin 8, sym m (symInv m i) = i := by decide
  have hinv2 : ∀ m i : Fin 8, symInv m (sym m i) = i := by decide
  have hlatinj : ∀ m : Fin 8, Function.Injective (lat m) := by
    intro m p q h
    have h' : latFun m p = latFun m q := h
    fin_cases m <;> simp [latFun, Prod.ext_iff] at h' ⊢ <;> omega
  -- the number of visited squares is invariant under each symmetry
  have inv : ∀ (m : Fin 8) {n : ℕ} (w : Fin n → Fin 8),
      (visited (sym m ∘ w)).card = (visited w).card := by
    intro m n w
    have hpos : ∀ j, position (sym m ∘ w) j = lat m (position w j) := by
      intro j
      unfold position
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs <;> simp [hsym]
    have : visited (sym m ∘ w) = (visited w).image (lat m) := by
      unfold visited
      rw [Finset.image_image]
      exact Finset.image_congr (fun j _ => hpos j)
    rw [this, Finset.card_image_of_injective _ (hlatinj m)]
  -- the total splits by the first step into eight equal parts
  have split : ∀ k : ℕ, ∑ w : Fin (k + 1) → Fin 8, (visited w).card =
      8 * ∑ v : Fin k → Fin 8, (visited (Fin.cons (0 : Fin 8) v : Fin (k + 1) → Fin 8)).card := by
    intro k
    rw [← (Fin.consEquiv fun _ : Fin (k + 1) => Fin 8).sum_comp, Fintype.sum_prod_type]
    have each : ∀ m : Fin 8,
        ∑ v : Fin k → Fin 8, (visited (Fin.consEquiv (fun _ : Fin (k + 1) => Fin 8) (m, v))).card =
          ∑ v : Fin k → Fin 8, (visited (Fin.cons (0 : Fin 8) v : Fin (k + 1) → Fin 8)).card := by
      intro m
      let e : (Fin k → Fin 8) ≃ (Fin k → Fin 8) :=
        { toFun := fun v => sym m ∘ v
          invFun := fun v => symInv m ∘ v
          left_inv := fun v => by funext i; simp [hinv2]
          right_inv := fun v => by funext i; simp [hinv1] }
      rw [← e.sum_comp]
      refine Finset.sum_congr rfl fun v _ => ?_
      have hc : (Fin.consEquiv (fun _ : Fin (k + 1) => Fin 8) (m, e v)) =
          sym m ∘ (Fin.cons (0 : Fin 8) v : Fin (k + 1) → Fin 8) := by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp [Fin.consEquiv, hsym0]
        · simp [Fin.consEquiv, e]
      rw [hc, inv]
    simp only [each, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  refine ⟨∑ v : Fin k → Fin 8, (visited (Fin.cons (0 : Fin 8) v : Fin (k + 1) → Fin 8)).card, ?_⟩
  unfold expectedRange
  have hs := split k
  have hq : (∑ w : Fin (k + 1) → Fin 8, ((visited w).card : ℚ)) =
      8 * ∑ v : Fin k → Fin 8, ((visited (Fin.cons (0 : Fin 8) v : Fin (k + 1) → Fin 8)).card : ℚ) := by
    exact_mod_cast hs
  rw [hq, show 3 * (k + 1) - 3 = 3 * k by omega]
  rw [Int.cast_sum]
  simp only [Int.cast_natCast]
  generalize (∑ v : Fin k → Fin 8,
    ((visited (Fin.cons (0 : Fin 8) v : Fin (k + 1) → Fin 8)).card : ℚ)) = T
  rw [pow_mul, pow_succ]
  norm_num
  field_simp

end D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality
