/- GID: D5/S3/Combinatorics/Graph/RankCuts/RankedBipartiteDiagonalParity
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/RankedBipartiteDiagonalParity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Relate diagonal parity to exceptional inflow and edges bypassing a rank. -/

import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

open Finset

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.RankCuts.RankedBipartiteDiagonalParity

variable {V : Type*} [Fintype V] [DecidableEq V]

private def below (rank : V → ℕ) (r : ℕ) : Finset V :=
  univ.filter fun v => rank v < r

private def atRank (rank : V → ℕ) (r : ℕ) : Finset V :=
  univ.filter fun v => rank v = r

private def through (rank : V → ℕ) (r : ℕ) : Finset V :=
  univ.filter fun v => rank v ≤ r

private def above (rank : V → ℕ) (r : ℕ) : Finset V :=
  univ.filter fun v => r < rank v

omit [DecidableEq V] in
private theorem split_sum (e : V → ℕ) (rank : V → ℕ) (r : ℕ) :
    (∑ v, e v) = (∑ v ∈ through rank r, e v) + ∑ v ∈ above rank r, e v := by
  simpa [through, above, not_le] using
    (sum_filter_add_sum_filter_not (s := (univ : Finset V))
      (p := fun v => rank v ≤ r) (f := e)).symm

omit [DecidableEq V] in
private theorem split_through (e : V → ℕ) (rank : V → ℕ) (r : ℕ) :
    (∑ v ∈ through rank r, e v) = (∑ v ∈ below rank r, e v) + ∑ v ∈ atRank rank r, e v := by
  have a : (through rank r).filter (fun v => rank v < r) = below rank r := by
    ext v
    simp [through, below]
    omega
  have b : (through rank r).filter (fun v => ¬ rank v < r) = atRank rank r := by
    ext v
    simp [through, atRank]
    omega
  rw [← a, ← b, sum_filter_add_sum_filter_not]

omit [DecidableEq V] in
/-- The diagonal at a rank is constrained by the full-prefix inflow and edges bypassing that rank. -/
theorem diagonal_parity (rank : V → ℕ) (top : V) (r : ℕ) (e : V → V → ℕ)
    (topRank : r < rank top)
    (increases : ∀ a b, a ≠ top → e a b ≠ 0 → a = b ∨ rank a < rank b)
    (rowOdd : ∀ a ∈ through rank r, (∑ b, e a b) % 2 = 1)
    (colOdd : ∀ b ∈ through rank r, (∑ a, e a b) % 2 = 1) :
    (∑ a ∈ atRank rank r, e a a) % 2 =
      ((atRank rank r).card + (∑ b ∈ through rank r, e top b) +
        ∑ a ∈ below rank r, ∑ b ∈ above rank r, e a b) % 2 := by
  let P := through rank r
  let H := above rank r
  let E := atRank rank r
  let L := below rank r
  have rowSplit :
      (∑ a ∈ P, ∑ b, e a b) =
      (∑ a ∈ P, ∑ b ∈ P, e a b) + ∑ a ∈ P, ∑ b ∈ H, e a b := by
    simp_rw [split_sum (rank := rank) (r := r)]
    rw [sum_add_distrib]
  have colSplit :
      (∑ b ∈ P, ∑ a, e a b) =
      (∑ a ∈ P, ∑ b ∈ P, e a b) + ∑ a ∈ H, ∑ b ∈ P, e a b := by
    simp_rw [split_sum (rank := rank) (r := r)]
    rw [sum_add_distrib, sum_comm (s := P) (t := P), sum_comm (s := P) (t := H)]
  have degreeMatch :
      (∑ a ∈ P, ∑ b, e a b) % 2 = (∑ b ∈ P, ∑ a, e a b) % 2 := by
    have h := Nat.ModEq.sum (s := P) fun a ha => by
      show (∑ b, e a b) ≡ (∑ b, e b a) [MOD 2]
      exact (rowOdd a ha).trans (colOdd a ha).symm
    exact h
  have incoming : (∑ a ∈ H, ∑ b ∈ P, e a b) = ∑ b ∈ P, e top b := by
    apply sum_eq_single_of_mem top (by simpa [H, above] using topRank)
    intro a ha htop
    apply sum_eq_zero
    intro b hb
    have ra : r < rank a := (mem_filter.mp ha).2
    have rb : rank b ≤ r := (mem_filter.mp hb).2
    by_contra hn
    rcases increases a b htop hn with heq | hlt
    · subst b
      omega
    · omega
  have boundary (a : V) (ha : a ∈ E) : (∑ b ∈ P, e a b) = e a a := by
    have ra : rank a = r := (mem_filter.mp ha).2
    have htop : a ≠ top := by
      rintro rfl
      omega
    apply sum_eq_single_of_mem a (by simp [P, through, ra])
    intro b hb hne
    have rb : rank b ≤ r := (mem_filter.mp hb).2
    by_contra hn
    rcases increases a b htop hn with heq | hlt
    · exact hne heq.symm
    · omega
  have atSplit :
      (∑ a ∈ E, ∑ b, e a b) = (∑ a ∈ E, e a a) + ∑ a ∈ E, ∑ b ∈ H, e a b := by
    simp_rw [split_sum (rank := rank) (r := r)]
    rw [sum_add_distrib]
    congr 1
    exact sum_congr rfl boundary
  have atOdd : (∑ a ∈ E, ∑ b, e a b) % 2 = E.card % 2 := by
    have h := Nat.ModEq.sum (s := E) fun a ha => by
      have ra : rank a = r := (mem_filter.mp ha).2
      show (∑ b, e a b) ≡ 1 [MOD 2]
      exact rowOdd a (by simp [through, ra])
    simpa [Nat.ModEq] using h
  have outgoing :
      (∑ a ∈ P, ∑ b ∈ H, e a b) =
      (∑ a ∈ L, ∑ b ∈ H, e a b) + ∑ a ∈ E, ∑ b ∈ H, e a b :=
    split_through (fun a => ∑ b ∈ H, e a b) rank r
  rw [rowSplit, colSplit, incoming, outgoing] at degreeMatch
  rw [atSplit] at atOdd
  change (∑ a ∈ E, e a a) % 2 = (E.card + (∑ b ∈ P, e top b) +
    ∑ a ∈ L, ∑ b ∈ H, e a b) % 2
  omega

end D5.S3.Combinatorics.Graph.RankCuts.RankedBipartiteDiagonalParity
