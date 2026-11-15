/- GID: D5/S3/Combinatorics/Permutation/Verkama62Count
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Permutation/Verkama62Count
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Exact inversion increments for singleton and northeast double additions. -/

import D5.S3.Combinatorics.Permutation.Verkama62Persistence
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-! Each inversion is counted in its unique increasing position order. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Permutation.Verkama62Local

/-- The number of increasing-position inversion pairs within a set of positions. -/
def inversions {n : ℕ} (π : Equiv.Perm (Fin n)) (S : Finset (Fin n)) : ℕ :=
  ∑ i ∈ S, ∑ j ∈ S, if i < j ∧ π j < π i then 1 else 0

/-- A singleton adds one inversion for each old neighbour, with no factor of two. -/
theorem inversions_insert {n : ℕ} (π : Equiv.Perm (Fin n)) (S : Finset (Fin n))
    (x : Fin n) (hx : x ∉ S) :
    inversions π (insert x S) = inversions π S + (neighbours π S x).card := by
  have hsplit : (neighbours π S x).card =
      (∑ i ∈ S, if i < x ∧ π x < π i then 1 else 0) +
      (∑ i ∈ S, if x < i ∧ π i < π x then 1 else 0) := by
    rw [neighbours, Finset.card_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases h₁ : i < x ∧ π x < π i
    · have h₂ : ¬ (x < i ∧ π i < π x) := by omega
      simp [h₁, h₂]
    · by_cases h₂ : x < i ∧ π i < π x <;> simp [h₁, h₂]
  simp only [inversions, Finset.sum_insert hx, lt_self_iff_false, false_and, ite_false,
    zero_add, Finset.sum_add_distrib]
  rw [hsplit]
  omega

/-- A northeast double ear has one old neighbour at each new point and one edge
    between its two new points. -/
theorem Double.inversion_increment {n : ℕ} {π : Equiv.Perm (Fin n)}
    {S : Finset (Fin n)} (e : Double π S) :
    inversions π (insert e.u (insert e.v S)) = inversions π S + 3 := by
  have huv : e.u ≠ e.v := ne_of_lt (e.hux.trans e.hxv)
  have hvcount : neighbours π S e.v = {e.y} := by
    ext i
    simp only [neighbours, Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hi, h | h⟩
      · by_contra hiy
        have := e.old_below i hi hiy
        omega
      · by_cases hix : i = e.x
        · have := e.hxv; subst i; omega
        · have := e.old_left i hi hix
          have := e.hux
          have := e.hxv
          omega
    · rintro rfl
      exact ⟨e.hy, Or.inl ⟨(e.old_left e.y e.hy e.hxy.symm).trans
        (e.hux.trans e.hxv), e.hvy⟩⟩
  have hucount : neighbours π (insert e.v S) e.u = {e.x, e.v} := by
    ext i
    simp only [neighbours, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨rfl | hi, h⟩
      · exact Or.inr rfl
      · left
        by_contra hix
        have hleft := e.old_left i hi hix
        have hbelow : π i < π e.u := by
          by_cases hiy : i = e.y
          · exact hiy ▸ e.hyu
          · exact (e.old_below i hi hiy).trans (e.hvy.trans e.hyu)
        rcases h with h | h <;> omega
    · rintro (rfl | rfl)
      · exact ⟨Or.inr e.hx, Or.inr ⟨e.hux,
          (e.old_below e.x e.hx e.hxy).trans (e.hvy.trans e.hyu)⟩⟩
      · exact ⟨Or.inl rfl, Or.inr ⟨e.hux.trans e.hxv, e.hvy.trans e.hyu⟩⟩
  rw [inversions_insert π (insert e.v S) e.u (by simp [huv, e.hu]),
    inversions_insert π S e.v e.hv, hvcount, hucount]
  have hxv : e.x ≠ e.v := ne_of_lt e.hxv
  simp [hxv]

end D5.S3.Combinatorics.Permutation.Verkama62Local
