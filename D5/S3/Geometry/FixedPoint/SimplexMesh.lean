/- GID: D5/S3/Geometry/FixedPoint/SimplexMesh
   generality: G
   mirror-B: D5/B/S3/Geometry/FixedPoint/SimplexMesh
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Convex.StdSimplex]
   utility: none
   digest: Coordinate minima plus one and residual mass construct an actual lattice point contradicting dominance. -/
/- proof_shape: size_bound_key: content
   admission_basis: escape-witness
   escape_witness: Coordinate minima plus one and residual mass construct an actual lattice point contradicting dominance.
   Source: https://github.com/math-xmum/Brouwer/blob/f9dc162170e8711f78059a87edcd38ffc44a1bfb/Gametheory/Brouwer.lean
   No mathematical novelty claim. -/
/-
MIT License

Copyright (c) 2025 Math_XMUM

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

import D5.S3.Combinatorics.Scarf.ColorfulCell
open Classical Finset
open D5.S3.Combinatorics.Scarf D5.S3.Combinatorics.Scarf.IndexedLOrder
noncomputable section
namespace D5.S3.Geometry.FixedPoint
variable (n l : ℕ+) (i : Fin n)
abbrev TT := {x : Πₗ (_ : Fin n), Fin (l+1) | ∑ i, (x i : ℕ)  = l}
variable {n l} in
abbrev TT.Ilt ( x y : TT n l) :=
  toLex (x.1 i, x)  < toLex (y.1 i, y)
set_option quotPrecheck false
local notation lhs "<[" i "]" rhs => (IndexedLOrder.IST i).lt lhs rhs
local notation lhs "≤[" i "]" rhs => (IndexedLOrder.IST i).le lhs rhs
lemma size_bound_key (σ : Finset (TT n l)) (C : Finset (Fin n)) (h :
    ({ IST := fun i => by
        letI : IsStrictTotalOrder (TT n l) (TT.Ilt i) := {
          trichotomous := by
            intro a b h_ab h_ba
            unfold TT.Ilt at h_ab h_ba
            have h_eq :
                toLex (a.1 i, a) = toLex (b.1 i, b) :=
              le_antisymm (le_of_not_gt h_ba) (le_of_not_gt h_ab)
            have h_pair : (a.1 i, a) = (b.1 i, b) :=
              (EquivLike.injective (toLex : (Fin (l + 1) × TT n l) ≃
                Lex (Fin (l + 1) × TT n l))) h_eq
            exact congrArg Prod.snd h_pair
          irrefl := by
            intro a
            unfold TT.Ilt
            exact lt_irrefl _
          trans := by
            intro a b c h_ab h_bc
            unfold TT.Ilt at *
            exact lt_trans h_ab h_bc }
        exact linearOrderOfSTO (TT.Ilt i) } : IndexedLOrder (Fin n) (TT n l)).isDominant σ C)
(h2 : σ.Nonempty):
  l < ∑ k ∈ C, (σ.image (fun x => (x.1 k : ℕ))).min' (h2.image _) + C.card := by
  letI meshOrders : IndexedLOrder (Fin n) (TT n l) :=
    ({ IST := fun i => by
        letI : IsStrictTotalOrder (TT n l) (TT.Ilt i) := {
          trichotomous := by
            intro a b h_ab h_ba
            unfold TT.Ilt at h_ab h_ba
            have h_eq :
                toLex (a.1 i, a) = toLex (b.1 i, b) :=
              le_antisymm (le_of_not_gt h_ba) (le_of_not_gt h_ab)
            have h_pair : (a.1 i, a) = (b.1 i, b) :=
              (EquivLike.injective (toLex : (Fin (l + 1) × TT n l) ≃
                Lex (Fin (l + 1) × TT n l))) h_eq
            exact congrArg Prod.snd h_pair
          irrefl := by
            intro a
            unfold TT.Ilt
            exact lt_irrefl _
          trans := by
            intro a b c h_ab h_bc
            unfold TT.Ilt at *
            exact lt_trans h_ab h_bc }
        exact linearOrderOfSTO (TT.Ilt i) } : IndexedLOrder (Fin n) (TT n l))
  have Ilt_keyprop (i : Fin n) (a b : TT n l) :
    a.1 i < b.1 i → a <[i] b := by
    intro h
    change toLex (a.1 i, a) < toLex (b.1 i, b)
    change Prod.Lex (· < ·) (· < ·) (a.1 i, a) (b.1 i, b)
    exact Prod.Lex.left a b h
  by_contra h_not
  push Not at h_not
  let m := fun k => (σ.image (fun x => (x.1 k : ℕ))).min' (h2.image _)
  have h_sum_bound : ∑ k ∈ C, m k + C.card ≤ l := h_not
  have h_sum_plus_one : ∑ k ∈ C, (m k + 1) ≤ l := by
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_one]
    exact h_sum_bound
  have h_exists_point : ∃ M : TT n l, ∀ k ∈ C, m k + 1 ≤ M.1 k := by
    let M' : Fin n → ℕ := fun k => if k ∈ C then m k + 1 else 0
    let S := ∑ k, M' k
    have h_S_le_l : S ≤ l := by
      simp [S, M', h_sum_plus_one]
    let R := l - S
    let M_coords : Fin n → ℕ := fun k => if k = (0 : Fin n) then M' 0 + R else M' k
    have h_M_coords_sum : ∑ k, M_coords k = l := by
      have h1 : S = M' 0 + ∑ k ∈ (Finset.univ : Finset (Fin n)).erase 0, M' k := by
        simp [S]
        rw [← Finset.sum_insert (Finset.notMem_erase 0 Finset.univ)]
        rw [Finset.insert_erase (Finset.mem_univ 0)]
      have : ∑ k, M_coords k = M_coords 0 + ∑ k ∈ (Finset.univ : Finset (Fin n)).erase 0, M_coords k := by
        rw [← Finset.sum_insert (Finset.notMem_erase 0 Finset.univ)]
        rw [Finset.insert_erase (Finset.mem_univ 0)]
      rw [this]
      simp only [M_coords, if_true]
      have sum_eq : ∑ x ∈ Finset.univ.erase 0, (if x = 0 then M' 0 + R else M' x) = ∑ x ∈ Finset.univ.erase 0, M' x := by
        apply Finset.sum_congr rfl
        intro k hk
        simp only [if_neg (Finset.ne_of_mem_erase hk)]
      rw [sum_eq, add_comm (M' 0) R, add_assoc, ← h1]
      simp only [R]
      have hM'0_le_S : M' 0 ≤ S := by
        have : M' 0 ≤ ∑ k, M' k := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ 0)
        exact this
      omega
    have h_M_coords_bound : ∀ k, M_coords k ≤ l := by
      intro k
      by_cases h_is_zero : k = 0
      · simp [h_is_zero, M_coords, R]
        have hM'0_le_S : M' 0 ≤ S := by
          have : M' 0 ≤ ∑ k, M' k := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ 0)
          exact this
        omega
      · simp [h_is_zero, M_coords]
        by_cases hk_in_C : k ∈ C
        · simp [M', hk_in_C]; exact Nat.le_trans (Finset.single_le_sum (fun k _ => Nat.zero_le (m k + 1)) hk_in_C) h_sum_plus_one
        · simp [M', hk_in_C]
    let M_val : Fin n → Fin (l + 1) := fun k => ⟨M_coords k, Nat.lt_succ_of_le (h_M_coords_bound k)⟩
    have h_M_val_sum : ∑ k, (M_val k : ℕ) = l := by
      simpa [M_val] using h_M_coords_sum
    use ⟨M_val, h_M_val_sum⟩
    intro k hk_in_C
    change m k + 1 ≤ (M_val k : ℕ)
    by_cases h_is_zero : k = 0
    · rw [h_is_zero] at hk_in_C ⊢
      simp [M_val, M_coords, M', hk_in_C]
    · simp [M_val, M_coords, h_is_zero, M', hk_in_C]
  obtain ⟨M, hM⟩ := h_exists_point
  have h_min_less : ∀ k ∈ C, ∃ x_min ∈ σ, ∀ x ∈ σ, x_min ≤[k] x := by
    intro k _
    let : LinearOrder (TT n l) := IndexedLOrder.IST k
    let x_min := σ.min' h2
    use x_min
    constructor
    · exact Finset.min'_mem σ h2
    · intro x hx
      exact Finset.min'_le σ x hx
  have h_contradiction : ∀ k ∈ C, ∃ x_min ∈ σ, x_min <[k] M := by
    intro k hk_in_C
    let : LinearOrder (TT n l) := IndexedLOrder.IST k
    let x_min := σ.min' h2
    use x_min
    constructor
    · exact Finset.min'_mem σ h2
    · apply Ilt_keyprop
      have h_min_coord : (x_min.1 k : ℕ) = (σ.image (fun x => (x.1 k : ℕ))).min' (h2.image _) := by
        symm
        apply le_antisymm
        · apply Finset.min'_le
          apply Finset.mem_image_of_mem
          exact Finset.min'_mem σ h2
        · apply Finset.le_min'
          intro y hy
          rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
          have h_x_min_le_x : x_min ≤[k] x := Finset.min'_le σ x hx
          by_cases h_case : (x_min.1 k : ℕ) ≤ (x.1 k : ℕ)
          · exact h_case
          · exfalso
            push Not at h_case
            have h_x_lt_min : x <[k] x_min := by
              apply Ilt_keyprop
              exact h_case
            exact not_lt.mpr h_x_min_le_x h_x_lt_min
      have h_nat_lt : (x_min.1 k : ℕ) < (M.1 k : ℕ) := by
        rw [h_min_coord]
        exact Nat.lt_of_succ_le (hM k hk_in_C)
      exact h_nat_lt
  have h_not_dominant : ¬ meshOrders.isDominant σ C := by
    intro h_dom
    rcases h_dom M with ⟨k, hk, h_all⟩
    rcases h_contradiction k hk with ⟨x, hx, hlt⟩
    let : LinearOrder (TT n l) := IndexedLOrder.IST k
    exact not_lt.mpr (h_all x hx) hlt
  exact h_not_dominant h
end D5.S3.Geometry.FixedPoint
