/- GID: D5/S3/Combinatorics/Circle/ZeroSumSubsets
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/ZeroSumSubsets
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Combinatorics.Colex, mathlib/module/Mathlib.Data.Nat.GCD.Basic, mathlib/module/Mathlib.Data.Finset.Powerset]
   utility: none
   digest: Binary physical masks bound exact zero-sum source subsets and disjoint zero blocks by the source gcd. -/
import D5.S3.Combinatorics.Circle.SourceWidth
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Set.Pairwise.Lattice

/-! # Integer zero subsets of the labelled centered doubling source -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.ZeroSumSubsets
open SourceWidth
open scoped BigOperators

/-- All physical-label subsets with exact integer source sum zero. -/
private def zeroSubsets (k t : ℕ) : Finset (Finset (Fin k)) :=
  Finset.univ.filter (fun A => ∑ p ∈ A, actualSource k t p = 0)

private def mask {k : ℕ} (A : Finset (Fin k)) : ℕ := ∑ p ∈ A, 2 ^ p.val

private theorem mask_as_geom {k : ℕ} (A : Finset (Fin k)) :
    mask A = ∑ i ∈ A.image Fin.val, 2 ^ i := by
  rw [Finset.sum_image]
  · rfl
  · intro p hp q hq he
    exact Fin.ext he

private theorem mask_injective (k : ℕ) : Function.Injective (@mask k) := by
  intro A B he
  have hi : A.image Fin.val = B.image Fin.val :=
    Finset.geomSum_injective (by decide : 2 ≤ (2 : ℕ))
      (by simpa only [mask_as_geom] using he)
  exact Finset.image_injective Fin.val_injective hi

private theorem mask_bound {k : ℕ} (A : Finset (Fin k)) : mask A ≤ 2 ^ k - 1 := by
  have h : mask A < 2 ^ k := by
    rw [mask_as_geom]
    apply Nat.geomSum_lt (by decide)
    intro i hi
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hi
    exact p.isLt
  omega

private theorem zero_mask_dvd {k t : ℕ} (A : Finset (Fin k))
    (hA : (∑ p ∈ A, actualSource k t p) = 0) : (2 ^ k - 1) ∣ t * mask A := by
  have hs : modulus k ∣ ∑ p ∈ A,
      ((2 : ℤ) ^ p.val * (t : ℤ) - actualSource k t p) := by
    apply Finset.dvd_sum
    intro p hp
    apply Int.modEq_iff_dvd.mp
    change centered (modulus k) ((2 : ℤ) ^ p.val * (t : ℤ)) % modulus k =
      ((2 : ℤ) ^ p.val * (t : ℤ)) % modulus k
    simp only [centered, Int.emod_sub_emod, add_sub_cancel_right]
  rw [Finset.sum_sub_distrib, hA, sub_zero, ← Finset.sum_mul] at hs
  have hm : modulus k = ((2 ^ k - 1 : ℕ) : ℤ) := by
    dsimp [modulus]
    rw [Nat.cast_sub (by have := pow_pos (by decide : 0 < (2 : ℕ)) k; omega)]
    norm_cast
  rw [hm] at hs
  have hcast : (∑ p ∈ A, (2 : ℤ) ^ p.val) = (mask A : ℤ) := by
    simp [mask]
  rw [hcast, mul_comm] at hs
  exact_mod_cast hs

private theorem quotient_dvd {N t m : ℕ} (hN : 0 < N) (h : N ∣ t * m) :
    N / Nat.gcd t N ∣ m := by
  have hg := Nat.gcd_pos_of_pos_right t hN
  have hc : Nat.gcd t N * (N / Nat.gcd t N) ∣
      Nat.gcd t N * ((t / Nat.gcd t N) * m) := by
    simpa only [← mul_assoc, Nat.mul_div_cancel' (Nat.gcd_dvd_right t N),
      Nat.mul_div_cancel' (Nat.gcd_dvd_left t N)] using h
  exact (Nat.coprime_div_gcd_div_gcd hg).symm.dvd_mul_left.mp
    (Nat.dvd_of_mul_dvd_mul_left hg hc)

/-- Exact zero subsets occupy at most gcd(t,2^k-1)+1 physical binary masks. -/
theorem zero_subsets_card_le (k t : ℕ) (hk : 3 ≤ k) :
    (Finset.univ.filter (fun A : Finset (Fin k) =>
      (∑ p ∈ A, actualSource k t p) = 0)).card ≤ Nat.gcd t (2 ^ k - 1) + 1 := by
  change (zeroSubsets k t).card ≤ _
  let N := 2 ^ k - 1
  let g := Nat.gcd t N
  let Q := N / g
  have hpow : 1 < (2 : ℕ) ^ k := Nat.one_lt_two_pow (by omega)
  have hN : 0 < N := by dsimp [N]; omega
  have hQ : 0 < Q := Nat.div_gcd_pos_of_pos_right t hN
  have hQg : Q * g = N := Nat.div_mul_cancel (Nat.gcd_dvd_right t N)
  have hd (A : Finset (Fin k)) (hA : A ∈ zeroSubsets k t) : Q ∣ mask A := by
    apply quotient_dvd hN
    exact zero_mask_dvd A (Finset.mem_filter.mp hA).2
  have hbound (A : Finset (Fin k)) : mask A / Q < g + 1 := by
    have hb : mask A ≤ N := mask_bound A
    have hle := Nat.div_le_div_right hb (c := Q)
    rw [← hQg, Nat.mul_div_cancel_left g hQ] at hle
    omega
  have hi := Finset.card_le_card_of_injOn (fun A : Finset (Fin k) => mask A / Q)
    (s := zeroSubsets k t) (t := Finset.range (g + 1))
    (fun A _ => Finset.mem_range.mpr (hbound A)) (by
      intro A hA B hB he
      change mask A / Q = mask B / Q at he
      apply mask_injective k
      calc
        mask A = mask A / Q * Q := (Nat.div_mul_cancel (hd A hA)).symm
        _ = mask B / Q * Q := by rw [he]
        _ = mask B := Nat.div_mul_cancel (hd B hB))
  simpa only [Finset.card_range] using hi

/-- Any nonempty disjoint exact-zero blocks generate distinct exact-zero unions. -/
theorem disjoint_zero_blocks_bound (k t : ℕ) (hk : 3 ≤ k)
    (blocks : Finset (Finset (Fin k)))
    (hne : ∀ A ∈ blocks, A.Nonempty)
    (hdis : Set.PairwiseDisjoint (blocks : Set (Finset (Fin k))) id)
    (hzero : ∀ A ∈ blocks, (∑ p ∈ A, actualSource k t p) = 0) :
    2 ^ blocks.card ≤ Nat.gcd t (2 ^ k - 1) + 1 := by
  classical
  have hinj : Set.InjOn (fun S : Finset (Finset (Fin k)) => S.biUnion id)
      (↑blocks.powerset) := by
    intro S hS T hT he
    have hSb := Finset.mem_powerset.mp hS
    have hTb := Finset.mem_powerset.mp hT
    have hsub (U V : Finset (Finset (Fin k))) (hU : U ⊆ blocks) (hV : V ⊆ blocks)
        (hUV : U.biUnion id = V.biUnion id) : U ⊆ V := by
      have hUVdis : Set.PairwiseDisjoint ((U : Set (Finset (Fin k))) ∪ V)
          (fun A => (A : Set (Fin k))) := by
        intro A hA B hB hAB
        have hAb : A ∈ blocks := hA.elim (fun h => hU h) (fun h => hV h)
        have hBb : B ∈ blocks := hB.elim (fun h => hU h) (fun h => hV h)
        exact Finset.disjoint_coe.mpr (hdis hAb hBb hAB)
      apply hUVdis.subset_of_biUnion_subset_biUnion
      · intro A hA
        exact hne A (hU hA)
      · simpa only [Finset.coe_biUnion, id_eq] using
          (congrArg (fun A : Finset (Fin k) => (A : Set (Fin k))) hUV).subset
    exact Finset.Subset.antisymm (hsub S T hSb hTb he) (hsub T S hTb hSb he.symm)
  have hmaps : Set.MapsTo (fun S : Finset (Finset (Fin k)) => S.biUnion id)
      (↑blocks.powerset) (↑(zeroSubsets k t)) := by
    intro S hS
    have hSb := Finset.mem_powerset.mp hS
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    change (∑ p ∈ S.biUnion id, actualSource k t p) = 0
    have hdisS : Set.PairwiseDisjoint (S : Set (Finset (Fin k))) id :=
      fun A hA B hB hAB => hdis (hSb hA) (hSb hB) hAB
    rw [Finset.sum_biUnion hdisS]
    exact Finset.sum_eq_zero (fun A hA => hzero A (hSb hA))
  have hcount := Finset.card_le_card_of_injOn
    (fun S : Finset (Finset (Fin k)) => S.biUnion id) hmaps hinj
  rw [Finset.card_powerset] at hcount
  exact hcount.trans (zero_subsets_card_le k t hk)

end D5.S3.Combinatorics.Circle.ZeroSumSubsets
