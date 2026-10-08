/- GID: D5/S3/Combinatorics/SignedDoubleRoman/PackingLabel
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SignedDoubleRoman/PackingLabel
   mirror-E: none(waiver:binary-packing-labelling)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Two-limited packings give binary signed double Roman functions and weight bounds. -/

import D5.S3.Combinatorics.SignedDoubleRoman.CubicDefs
import D5.S3.Combinatorics.SignedDoubleRoman.MixedDefs
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.SignedDoubleRoman.PackingLabel

open Finset
open MixedDefs

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Labelling a two-limited packing by minus one gives an admissible function of known weight. -/
theorem packing_labelling (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdeg : ∀ v, (G.neighborFinset v).card = 3) (B : Finset V)
    (hB : TwoLimited G B) :
    ∃ f : V → ℤ, CubicDefs.IsSDRkDF G 2 f ∧
      (∑ v, f v) = 2 * (Fintype.card V : ℤ) - 3 * (B.card : ℤ) := by
  classical
  let f : V → ℤ := fun v => if v ∈ B then -1 else 2
  have sum_formula (S : Finset V) :
      (∑ v ∈ S, f v) = 2 * (S.card : ℤ) - 3 * ((S ∩ B).card : ℤ) := by
    have hpartition := S.card_sdiff_add_card_inter B
    have hcast : ((S \ B).card : ℤ) + ((S ∩ B).card : ℤ) = (S.card : ℤ) := by
      exact_mod_cast hpartition
    have hsum : (∑ v ∈ S, f v) =
        -((S ∩ B).card : ℤ) + 2 * ((S \ B).card : ℤ) := by
      simp only [f, sum_ite, filter_mem_eq_inter, filter_notMem_eq_sdiff,
        sum_const, nsmul_eq_mul]
      ring
    rw [hsum]
    omega
  refine ⟨f, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro v
    by_cases hv : v ∈ B
    · exact Or.inl (by simp [f, hv])
    · exact Or.inr (Or.inr (Or.inl (by simp [f, hv])))
  · intro v
    have hv : v ∉ G.neighborFinset v := by simp
    have hclosed : (insert v (G.neighborFinset v)).card = 4 := by
      rw [card_insert_of_notMem hv, hdeg]
    have hsum := sum_formula (insert v (G.neighborFinset v))
    rw [sum_insert hv, hclosed] at hsum
    have hbound : (((insert v (G.neighborFinset v)) ∩ B).card : ℤ) ≤ 2 := by
      exact_mod_cast hB v
    omega
  · intro v hfv
    have hv : v ∈ B := by
      by_contra hv
      simp [f, hv] at hfv
    have hne : v ∉ G.neighborFinset v ∩ B := by simp
    have hi : (insert v (G.neighborFinset v)) ∩ B =
        insert v (G.neighborFinset v ∩ B) := by
      ext w
      simp only [mem_inter, mem_insert]
      aesop
    have hselected : (G.neighborFinset v ∩ B).card ≤ 1 := by
      have hc := hB v
      rw [hi, card_insert_of_notMem hne] at hc
      omega
    have houtside : 1 < (G.neighborFinset v \ B).card := by
      have hpartition := (G.neighborFinset v).card_sdiff_add_card_inter B
      rw [hdeg] at hpartition
      omega
    obtain ⟨u, hu, w, hw, huw⟩ := one_lt_card.mp houtside
    refine Or.inr ⟨u, w, huw, ?_, ?_, ?_, ?_⟩
    · exact (G.mem_neighborFinset _ _).mp (mem_sdiff.mp hu).1
    · exact (G.mem_neighborFinset _ _).mp (mem_sdiff.mp hw).1
    · simp [f, (mem_sdiff.mp hu).2]
    · simp [f, (mem_sdiff.mp hw).2]
  · intro v hfv
    by_cases hv : v ∈ B <;> simp [f, hv] at hfv
  · simpa using sum_formula univ

/-- The integer infimum is below the weight supplied by a large two-limited packing. -/
theorem gamma_le_of_packing (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdeg : ∀ v, (G.neighborFinset v).card = 3) (B : Finset V)
    (hB : TwoLimited G B) (hsize : Fintype.card V ≤ 3 * B.card) :
    CubicDefs.gammaSDR G 2 ≤ (Fintype.card V : ℤ) := by
  obtain ⟨f, hf, hweight⟩ := packing_labelling G hdeg B hB
  have hbounded : BddBelow {w : ℤ | ∃ g : V → ℤ,
      CubicDefs.IsSDRkDF G 2 g ∧ w = ∑ v, g v} := by
    refine ⟨-(Fintype.card V : ℤ), ?_⟩
    rintro w ⟨g, hg, rfl⟩
    have hlower : ∀ v, (-1 : ℤ) ≤ g v := by
      intro v
      rcases hg.1 v with h | h | h | h <;> omega
    calc
      -(Fintype.card V : ℤ) = ∑ _v : V, (-1 : ℤ) := by simp
      _ ≤ ∑ v, g v := sum_le_sum fun v _ => hlower v
  have hgamma : CubicDefs.gammaSDR G 2 ≤ ∑ v, f v :=
    csInf_le hbounded ⟨f, hf, rfl⟩
  have hcast : (Fintype.card V : ℤ) ≤ 3 * (B.card : ℤ) := by
    exact_mod_cast hsize
  rw [hweight] at hgamma
  omega

#print axioms packing_labelling
#print axioms gamma_le_of_packing

end D5.S3.Combinatorics.SignedDoubleRoman.PackingLabel
