/- GID: D5/S1/Words/AdmissibleWords/PathCornerDefect
   generality: G
   mirror-B: D5/B/S1/Words/AdmissibleWords/PathCornerDefect
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: A path-word corner has n plus its occupied interior sites tight inequalities. -/

import D5.S1.Words.AdmissibleWords.PathStableSetPolytope

/-! The path polytope of length `m + 2` is cut out by the lower bounds `0 ≤ xᵢ` and the edge
inequalities `xᵢ + xᵢ₊₁ ≤ 1`. At the occupancy vector of a word with no two adjacent occupied
sites, the tight lower bounds are the unoccupied sites and the tight edge inequalities are the
edges touching an occupied site. Their number exceeds the dimension `m + 2` by exactly the number
of occupied interior sites, so the dimension is attained exactly when only endpoints are
occupied. -/

namespace D5.S1.Words.AdmissibleWords.PathCornerDefect

open Finset
open D5.S1.Words.AdmissibleWords.PathStableSetPolytope

private theorem occupancy_eq_zero {n : ℕ} (w : Fin n → Bool) (i : Fin n) :
    occupancy w i = 0 ↔ w i = false := by
  cases h : w i <;> simp [occupancy, h]

private theorem occupancy_edge_eq_one {n : ℕ} (w : Fin n → Bool) (a b : Fin n)
    (hab : ¬ (w a = true ∧ w b = true)) :
    occupancy w a + occupancy w b = 1 ↔ (w a = true ∨ w b = true) := by
  cases ha : w a <;> cases hb : w b <;> simp_all [occupancy]

/-- At the occupancy vector of a word of length `m + 2` with no two adjacent occupied sites, the
tight lower bounds plus the tight edge inequalities number `m + 2` plus the occupied interior
sites, which are the sites `d + 1` for `d < m`. -/
theorem tight_count_eq_add_interior (m : ℕ) (w : Fin (m + 2) → Bool)
    (hadj : ∀ e : Fin (m + 1), ¬ (w e.castSucc = true ∧ w e.succ = true)) :
    (univ.filter fun i => occupancy w i = 0).card +
        (univ.filter fun e : Fin (m + 1) =>
          occupancy w e.castSucc + occupancy w e.succ = 1).card =
      (m + 2) + (univ.filter fun d : Fin m => w d.castSucc.succ = true).card := by
  set f : Fin (m + 2) → ℕ := fun i => if w i = true then 1 else 0 with hf
  have hlow : (univ.filter fun i => occupancy w i = 0).card + ∑ i, f i = m + 2 := by
    have h1 : (univ.filter fun i => occupancy w i = 0) =
        (univ.filter fun i : Fin (m + 2) => ¬ w i = true) := by
      ext i; simp [occupancy_eq_zero]
    have h2 : ∑ i, f i = (univ.filter fun i : Fin (m + 2) => w i = true).card := by
      rw [Finset.card_filter]
    rw [h1, h2, add_comm, Finset.card_filter_add_card_filter_not]
    simp
  have hedge : (univ.filter fun e : Fin (m + 1) =>
      occupancy w e.castSucc + occupancy w e.succ = 1).card =
      ∑ e : Fin (m + 1), (f e.castSucc + f e.succ) := by
    rw [Finset.card_filter]
    refine Finset.sum_congr rfl fun e _ => ?_
    have h := hadj e
    rw [if_congr (occupancy_edge_eq_one w e.castSucc e.succ h) rfl rfl]
    cases ha : w e.castSucc <;> cases hb : w e.succ <;> simp_all
  have hcast : ∑ e : Fin (m + 1), f e.castSucc + f (Fin.last (m + 1)) = ∑ i, f i :=
    (Fin.sum_univ_castSucc f).symm
  have hsucc : f 0 + ∑ e : Fin (m + 1), f e.succ = ∑ i, f i := (Fin.sum_univ_succ f).symm
  have hint : (univ.filter fun d : Fin m => w d.castSucc.succ = true).card +
      f 0 + f (Fin.last (m + 1)) = ∑ i, f i := by
    rw [Finset.card_filter, Fin.sum_univ_succ f,
      Fin.sum_univ_castSucc (fun e : Fin (m + 1) => f e.succ)]
    have hl : (Fin.last m).succ = Fin.last (m + 1) := rfl
    rw [hl]
    simp only [hf]
    ring
  have hsplit : ∑ e : Fin (m + 1), (f e.castSucc + f e.succ) =
      ∑ e : Fin (m + 1), f e.castSucc + ∑ e : Fin (m + 1), f e.succ :=
    Finset.sum_add_distrib
  omega

end D5.S1.Words.AdmissibleWords.PathCornerDefect
