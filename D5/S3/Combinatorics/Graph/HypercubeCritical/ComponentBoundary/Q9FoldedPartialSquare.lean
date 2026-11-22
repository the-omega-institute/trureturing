/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9FoldedPartialSquare
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9FoldedPartialSquare
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.ZMod.Basic]
   utility: none
   digest: Three negative squares force four equal signs in a partially determined row. -/

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9FoldedSignedRows

/-! An exact integer obstruction obtained from the parity of three switched squares. -/

set_option autoImplicit false

open scoped BigOperators

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9FoldedPartialSquare

open Q9FoldedSignedRows

/-- Zero rows at the three opposite corners of negative squares force the four
specified centre incidences to agree. At most one other incidence can contribute. -/
theorem three_negative_squares_obstruct_row {V : Type*} [DecidableEq V]
    (neighbors : V → Finset V) (s : Signing V) (z : V → ZMod 2)
    (u b : V) (c d : Fin 3 → V) (target : ℤ)
    (undirected : ∀ i, s.bit b (d i) = s.bit (d i) b ∧ s.bit (c i) u = s.bit u (c i))
    (hb : b ∈ neighbors u) (hc : ∀ i, c i ∈ neighbors u)
    (b_ne : ∀ i, b ≠ c i) (c_injective : Function.Injective c)
    (cornerNeighbors : ∀ i, neighbors (d i) = {b, c i})
    (negative : ∀ i, s.bit u b + s.bit b (d i) + s.bit (d i) (c i) +
      s.bit (c i) u = 1)
    (cornerRows : ∀ i, rowSum neighbors s z (d i) = 0)
    (centerCard : (neighbors u).card ≤ 5) (targetBound : |target| ≤ 2) :
    rowSum neighbors s z u ≠ target := by
  have agree (i : Fin 3) : (z +ᵥ s).bit u (c i) = (z +ᵥ s).bit u b := by
    have hneg := negative i
    rw [(undirected i).1, (undirected i).2] at hneg
    have square : (z +ᵥ s).bit u b + (z +ᵥ s).bit u (c i) +
        ((z +ᵥ s).bit (d i) b + (z +ᵥ s).bit (d i) (c i)) = 1 := by
      change (s.bit u b + (z u + z b)) + (s.bit u (c i) + (z u + z (c i))) +
        ((s.bit (d i) b + (z (d i) + z b)) +
          (s.bit (d i) (c i) + (z (d i) + z (c i)))) = 1
      calc
        _ = (s.bit u b + s.bit (d i) b + s.bit (d i) (c i) + s.bit u (c i)) +
            ((z u + z u) + (z b + z b) + (z (c i) + z (c i)) +
              (z (d i) + z (d i))) := by ac_rfl
        _ = 1 := by simp only [ZModModule.add_self, add_zero, hneg]
    have corner := cornerRows i
    have hbc : b ∉ ({c i} : Finset V) := Finset.notMem_singleton.mpr (b_ne i)
    simp only [rowSum, cornerNeighbors i, Finset.sum_insert hbc, Finset.sum_singleton] at corner
    change (1 - 2 * (((z +ᵥ s).bit (d i) b).val : ℤ)) +
      (1 - 2 * (((z +ᵥ s).bit (d i) (c i)).val : ℤ)) = 0 at corner
    have oneNegative : ((z +ᵥ s).bit (d i) b).val + ((z +ᵥ s).bit (d i) (c i)).val =
        1 := by omega
    have cornerParity : (z +ᵥ s).bit (d i) b + (z +ᵥ s).bit (d i) (c i) = 1 := by
      simpa only [Nat.cast_add, Nat.cast_one, ZMod.natCast_zmod_val]
        using congrArg (fun n : ℕ => (n : ZMod 2)) oneNegative
    have centerParity : (z +ᵥ s).bit u b + (z +ᵥ s).bit u (c i) = 0 :=
      add_right_cancel (by rw [cornerParity] at square; exact square.trans (zero_add 1).symm)
    exact add_left_cancel (centerParity.trans (ZModModule.add_self _).symm)
  let others := Finset.univ.image c
  let forced := insert b others
  have b_not_mem : b ∉ others := by
    intro h
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h
    exact b_ne i hi.symm
  have forcedCard : forced.card = 4 := by
    rw [Finset.card_insert_of_notMem b_not_mem, Finset.card_image_of_injective _ c_injective]
    decide
  have included : forced ⊆ neighbors u := by
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact hb
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
      exact hc i
  let term (v : V) : ℤ := 1 - 2 * (((z +ᵥ s).bit u v).val : ℤ)
  have forcedSum : ∑ v ∈ forced, term v = 4 * term b := by
    calc
      _ = ∑ _v ∈ forced, term b := by
        apply Finset.sum_congr rfl
        intro v hv
        rcases Finset.mem_insert.mp hv with rfl | hv
        · rfl
        · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
          simp only [term, agree i]
      _ = _ := by simp [forcedCard, nsmul_eq_mul]
  have term_sign (v : V) : term v = 1 ∨ term v = -1 := by
    have h := ZMod.val_lt ((z +ᵥ s).bit u v)
    have cases : ((z +ᵥ s).bit u v).val = 0 ∨ ((z +ᵥ s).bit u v).val = 1 := by omega
    rcases cases with hv | hv <;> simp only [term, hv] <;> decide
  have term_abs (v : V) : |term v| = 1 := by
    rcases term_sign v with h | h <;> rw [h] <;> decide
  have restCard : ((neighbors u) \ forced).card ≤ 1 := by
    rw [Finset.card_sdiff_of_subset included, forcedCard]
    omega
  have restBound : |∑ v ∈ neighbors u \ forced, term v| ≤ 1 := by
    calc
      _ ≤ ∑ v ∈ neighbors u \ forced, |term v| := Finset.abs_sum_le_sum_abs _ _
      _ = (((neighbors u) \ forced).card : ℤ) := by simp [term_abs]
      _ ≤ 1 := Int.ofNat_le.mpr restCard
  have total : (∑ v ∈ neighbors u \ forced, term v) + 4 * term b =
      rowSum neighbors s z u := by
    rw [← forcedSum, Finset.sum_sdiff included]
    rfl
  intro eq
  rw [eq] at total
  obtain ⟨restLower, restUpper⟩ := abs_le.mp restBound
  obtain ⟨targetLower, targetUpper⟩ := abs_le.mp targetBound
  rcases term_sign b with h | h <;> rw [h] at total <;> omega

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9FoldedPartialSquare
