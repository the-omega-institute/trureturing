/- GID: D5/S3/Arith/FibonacciAtomic/OptimalLaw/OptimalEmbedding
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/OptimalLaw/OptimalEmbedding
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Every attaining real law has one fixed label permutation and one cost-preserving triangular root path. -/

import D5.S3.Arith.FibonacciAtomic.TriangularPathNormalization
import D5.S3.Arith.FibonacciAtomic.OptimalLawStrictSlope
import Mathlib.Data.Fin.Tuple.Sort
import D5.S3.Arith.FibonacciAtomic.OptimalLaw.StrictRounding
import D5.S3.Arith.FibonacciAtomic.OptimalLaw.LeafExchange
import D5.S1.Digit.RadixFloorDigit

local notation "floorPrefix" => (fun (x : ℝ) (d : ℕ) => ⌊(2 : ℝ) ^ d * x⌋)
local notation "bit" => (fun (x : ℝ) (d : ℕ) => ⌊(2 : ℝ) ^ (d + 1) * x⌋ - 2 * ⌊(2 : ℝ) ^ d * x⌋)
local notation "tail" => (fun (x : ℝ) (d : ℕ) => Int.fract ((2 : ℝ) ^ d * x))

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace D5.S3.Arith.FibonacciAtomic.OptimalLaw.OptimalEmbedding

open D5.S3.Arith.FibonacciAtomic
open D5.S3.Arith.FibonacciAtomic.DyadicSupportLines
open D5.S3.Arith.FibonacciAtomic.OptimalLawStrictSlope
open D5.S3.Arith.FibonacciAtomic.TriangularPathNormalization

/-- An attained law is represented by one fixed
    permutation and one legal triangular root path with exact cost. -/
def HasOptimalEmbedding (m : ℕ) (p : Fin m → ℝ) (k : Fin m) : Prop :=
  ∃ σ : Equiv.Perm (Fin m), ∃ γ : RootPath m,
    (∀ i, probability γ i = p (σ i)) ∧
    anchorMass γ = p k ∧ pathCost γ = cost p


open D5.S3.Arith.FibonacciAtomic.OptimalLaw.StrictRounding

/-- The source strict-rounding formula yields the exact canonical departure
column, all earlier common prefixes, and the zero tail after departure. -/
private theorem departure_digits (x t : ℝ) (D : ℕ) (hD : 1 ≤ D)
    (hx : OnGrid x D) (hmin : ∀ d < D, ¬OnGrid x d)
    (hr : x = D5.S3.Arith.FibonacciAtomic.OptimalLaw.StrictRounding.round t D) :
    (∀ d < D, ⌊(2 : ℝ) ^ d * x⌋ = ⌊(2 : ℝ) ^ d * t⌋) ∧
    ⌊(2 : ℝ) ^ D * t⌋ = 2 * ⌊(2 : ℝ) ^ (D - 1) * t⌋ ∧
    ⌊(2 : ℝ) ^ D * x⌋ = 2 * ⌊(2 : ℝ) ^ (D - 1) * x⌋ + 1 ∧
    (∀ d, D ≤ d → ⌊(2 : ℝ) ^ (d + 1) * x⌋ = 2 * ⌊(2 : ℝ) ^ d * x⌋) := by
  have donor_bit := least_grid_bit x D hD hx hmin
  have normx : (2 : ℝ) ^ D * x = (⌊(2 : ℝ) ^ D * t⌋ : ℝ) + 1 := by
    rw [hr]
    dsimp [D5.S3.Arith.FibonacciAtomic.OptimalLaw.StrictRounding.round]
    field_simp
  have normxd : (2 : ℝ) ^ D * (x - 1 / (2 : ℝ) ^ D) =
      (⌊(2 : ℝ) ^ D * t⌋ : ℝ) := by
    have cancel : (2 : ℝ) ^ D * (1 / (2 : ℝ) ^ D) = 1 := by field_simp
    rw [mul_sub, normx, cancel]
    ring
  have commonprefix (d : ℕ) (hd : d < D) :
      ⌊(2 : ℝ) ^ d * x⌋ = ⌊(2 : ℝ) ^ d * t⌋ := by
    have scale (y : ℝ) : (2 : ℝ) ^ d * y =
        ((2 : ℝ) ^ D * y) / ((2 ^ (D - d) : ℕ) : ℝ) := by
      have hd' : D = d + (D - d) := by omega
      have po : (2 : ℝ) ^ D = (2 : ℝ) ^ d * (2 : ℝ) ^ (D - d) := by
        calc
          _ = (2 : ℝ) ^ (d + (D - d)) := congrArg (fun n : ℕ => (2 : ℝ) ^ n) hd'
          _ = _ := pow_add _ _ _
      push_cast
      rw [po]
      field_simp
    calc
      _ = ⌊(2 : ℝ) ^ d * (x - 1 / (2 : ℝ) ^ D)⌋ :=
        (D5.S3.Arith.FibonacciAtomic.OptimalLaw.LeafExchange.donor_prefix x D hD donor_bit d hd).symm
      _ = ⌊(2 : ℝ) ^ d * t⌋ := by
        rw [scale, scale, normxd, Int.floor_div_natCast, Int.floor_div_natCast,
          Int.floor_intCast]
  have floorx : ⌊(2 : ℝ) ^ D * x⌋ = ⌊(2 : ℝ) ^ D * t⌋ + 1 := by
    rw [normx]
    simp
  refine ⟨commonprefix, ?_, donor_bit, ?_⟩
  · rw [floorx, commonprefix (D - 1) (by omega)] at donor_bit
    omega
  · intro d hd
    obtain ⟨z, hz⟩ := grid_up x D d hd hx
    have next : (2 : ℝ) ^ (d + 1) * x = ((2 * z : ℤ) : ℝ) := by
      rw [pow_succ]
      push_cast
      nlinarith only [hz]
    rw [hz, next, Int.floor_intCast, Int.floor_intCast]

/-- Retained labels in the reverse construction. Minimum labels are
permanent; a larger label remains precisely while its dyadic tail is nonzero. -/
private noncomputable def retained_labels {m : ℕ} (p : Fin m → ℝ) (k : Fin m) (d : ℕ) :
    Finset (Fin m) := by
  classical
  exact Finset.univ.filter (fun i => p i = p k ∨ ¬OnGrid (p i) d)

private noncomputable def state_of_law {m : ℕ} (p : Fin m → ℝ) (k : Fin m) (d : ℕ) :
    State := ⟨((2 : ℤ) ^ d - ∑ i, ⌊(2 : ℝ) ^ d * p i⌋).toNat,
      (retained_labels p k d).card⟩

private noncomputable def departure_count {m : ℕ} (p : Fin m → ℝ) (k : Fin m) (d : ℕ) :
    ℕ := (retained_labels p k d \ retained_labels p k (d + 1)).card



/-- The order must be chosen once for the whole nested family. -/
private def FixedRetainedOrder {m : ℕ} (p : Fin m → ℝ) (k : Fin m) : Prop :=
  ∃ σ : Equiv.Perm (Fin m), ∀ (d : ℕ) (i : Fin m),
    σ i ∈ retained_labels p k d ↔ i.val < (retained_labels p k d).card

end D5.S3.Arith.FibonacciAtomic.OptimalLaw.OptimalEmbedding



set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000
open scoped BigOperators
namespace D5.S3.Arith.FibonacciAtomic.OptimalLaw.OptimalEmbedding
open D5.S3.Arith.FibonacciAtomic
open DyadicSupportLines OptimalLawStrictSlope TriangularPathNormalization
open D5.S3.Arith.FibonacciAtomic.OptimalLaw.StrictRounding D5.S3.Arith.FibonacciAtomic.OptimalLaw.OptimalEmbedding


private lemma bit_bounds' (x : ℝ) (d : ℕ) : 0 ≤ bit x d ∧ bit x d ≤ 1 := by
  have H := D5.S1.Digit.RadixFloorDigit.radix_floor_digit_bounds_and_decomposition
    2 (by decide) ((2 : ℝ) ^ d * x)
  simp only [D5.S1.Digit.RadixFloorDigit.digitInt] at H
  have scale : (2 : ℝ) ^ (d + 1) * x = 2 * ((2 : ℝ) ^ d * x) := by
    rw [pow_succ]
    ring
  dsimp only []
  rw [scale]
  norm_num only [Nat.cast_ofNat] at H
  omega

private lemma tail_bounds (x : ℝ) (d : ℕ) : 0 ≤ tail x d ∧ tail x d < 1 := by
  exact ⟨Int.fract_nonneg _,Int.fract_lt_one _⟩

private lemma tail_step (x : ℝ) (d : ℕ) : 2*tail x d = bit x d + tail x (d+1) := by
  dsimp only [Int.fract]
  push_cast
  rw [pow_succ]
  ring

private lemma grid_tail (x : ℝ) (d : ℕ) (h : OnGrid x d) : tail x d = 0 := by
  obtain ⟨z,hz⟩ := h
  simp [ Int.fract,hz]

private lemma grid_bit (x : ℝ) (d : ℕ) (h : OnGrid x d) : bit x d = 0 := by
  have H := tail_step x d
  rw [grid_tail x d h, grid_tail x (d+1) (grid_up _ d (d+1) (by omega) h)] at H
  exact_mod_cast (show (bit x d : ℝ) = 0 by linarith)

private lemma retained_mem {m : ℕ} (p : Fin m → ℝ) (k i : Fin m) (d : ℕ) :
    i ∈ retained_labels p k d ↔ p i = p k ∨ ¬OnGrid (p i) d := by
  classical
  simp [retained_labels]

private lemma retained_next {m : ℕ} (p : Fin m → ℝ) (k : Fin m) (d : ℕ) :
    retained_labels p k (d+1) ⊆ retained_labels p k d := by
  intro i hi
  rw [retained_mem] at hi ⊢
  rcases hi with hi | hi
  · exact Or.inl hi
  · exact Or.inr (fun H => hi (grid_up _ d (d+1) (by omega) H))

private lemma inactive_tail {m : ℕ} (p : Fin m → ℝ) (k i : Fin m) (d : ℕ)
    (hi : i ∉ retained_labels p k d) : tail (p i) d = 0 := by
  have hn := not_or.mp (mt (retained_mem p k i d).mpr hi)
  exact grid_tail _ _ (not_not.mp hn.2)

private lemma column_rule {m : ℕ} (p : Fin m → ℝ) (k : Fin m)
    (hk : ∀ i, p k ≤ p i) (hr : StrictlyRoundedLaw m p k) (d : ℕ) (i : Fin m) :
    bit (p i) d =
      if i ∈ retained_labels p k d then
        if bit (p k) d = 1 then 1 else
          if i ∈ retained_labels p k (d+1) then 0 else 1
      else 0 := by
  classical
  by_cases heq : p i = p k
  · have hai : i ∈ retained_labels p k d := (retained_mem _ _ _ _).mpr (Or.inl heq)
    have han : i ∈ retained_labels p k (d+1) := (retained_mem _ _ _ _).mpr (Or.inl heq)
    rw [heq,if_pos hai,if_pos han]
    have H := bit_bounds' (p k) d
    split_ifs <;> omega
  · have hlt : p k < p i := lt_of_le_of_ne (hk i) (Ne.symm heq)
    obtain ⟨D,hD,hgrid,hmin,hround⟩ := hr i hlt
    have hround' : p i = D5.S3.Arith.FibonacciAtomic.OptimalLaw.StrictRounding.round (p k) D := by
      simpa [D5.S3.Arith.FibonacciAtomic.OptimalLaw.StrictRounding.round,Int.cast_add,Int.cast_one] using hround
    obtain ⟨hfloorPrefix,hzero,hone,hafter⟩ := departure_digits (p i) (p k) D hD hgrid hmin hround'
    by_cases hd : d < D
    · have hai : i ∈ retained_labels p k d := (retained_mem _ _ _ _).mpr (Or.inr (hmin d hd))
      rw [if_pos hai]
      by_cases hnext : d+1 < D
      · have han : i ∈ retained_labels p k (d+1) :=
          (retained_mem _ _ _ _).mpr (Or.inr (hmin _ hnext))
        have hb : bit (p i) d = bit (p k) d := by simp [hfloorPrefix d hd,hfloorPrefix _ hnext]
        rw [hb,if_pos han]
        have H := bit_bounds' (p k) d
        split_ifs <;> omega
      · have he : D = d+1 := by omega
        have hm : D-1 = d := by omega
        have hba : bit (p k) d = 0 := by dsimp []; rw [← he]; rw [hm] at hzero hone; omega
        have hbi : bit (p i) d = 1 := by dsimp []; rw [← he]; rw [hm] at hzero hone; omega
        have hn : i ∉ retained_labels p k (d+1) := by
          rw [retained_mem]
          rintro (H|H)
          · exact heq H
          · apply H
            rw [← he]
            exact hgrid
        rw [hbi,hba,if_neg (by norm_num : (0:ℤ) ≠ 1),if_neg hn]
    · have hg : OnGrid (p i) d := grid_up _ D d (by omega) hgrid
      have hn : i ∉ retained_labels p k d := by rw [retained_mem]; simp [heq,hg]
      rw [if_neg hn,grid_bit _ _ hg]

private lemma departure_anchor_zero {m : ℕ} (p : Fin m → ℝ) (k : Fin m)
    (hk : ∀ i,p k ≤ p i) (hr : StrictlyRoundedLaw m p k)
    (d : ℕ) (i : Fin m) (hai : i ∈ retained_labels p k d)
    (han : i ∉ retained_labels p k (d+1)) : bit (p k) d = 0 := by
  have heq : p i ≠ p k := by
    intro H; exact han ((retained_mem _ _ _ _).mpr (Or.inl H))
  obtain ⟨D,hD,hgrid,hmin,hround⟩ := hr i (lt_of_le_of_ne (hk i) (Ne.symm heq))
  have hd : d < D := by
    by_contra H
    have hg := grid_up _ D d (by omega) hgrid
    exact (retained_mem _ _ _ _).mp hai |>.resolve_left heq <| hg
  have hDn : D ≤ d+1 := by
    by_contra H
    exact han ((retained_mem _ _ _ _).mpr (Or.inr (hmin _ (by omega))))
  have he : D = d+1 := by omega
  obtain ⟨_,hz,_,_⟩ := departure_digits (p i) (p k) D hD hgrid hmin
    (by simpa [D5.S3.Arith.FibonacciAtomic.OptimalLaw.StrictRounding.round,Int.cast_add,Int.cast_one] using hround)
  dsimp []
  have hm : D-1 = d := by omega
  rw [he,show d+1-1 = d by omega] at hz
  omega

end D5.S3.Arith.FibonacciAtomic.OptimalLaw.OptimalEmbedding

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 400000
open scoped BigOperators
namespace D5.S3.Arith.FibonacciAtomic.OptimalLaw.OptimalEmbedding
open D5.S3.Arith.FibonacciAtomic
open DyadicSupportLines OptimalLawStrictSlope TriangularPathNormalization
open D5.S3.Arith.FibonacciAtomic.OptimalLaw.StrictRounding D5.S3.Arith.FibonacciAtomic.OptimalLaw.OptimalEmbedding

private noncomputable def residual_int {m : ℕ} (p : Fin m → ℝ) (d : ℕ) : ℤ :=
  (2:ℤ)^d - ∑ i, floorPrefix (p i) d

private lemma residual_tail_sum {m : ℕ} (p : Fin m → ℝ) (hs : ∑ i,p i = 1) (d : ℕ) :
    ∑ i, tail (p i) d = (residual_int p d : ℝ) := by
  simp only [ Int.fract,Finset.sum_sub_distrib,← Finset.mul_sum,hs,mul_one,residual_int]
  push_cast
  rfl

private lemma active_tail_sum {m : ℕ} (p : Fin m → ℝ) (k : Fin m)
    (hs : ∑ i,p i=1) (d : ℕ) :
    ∑ i ∈ retained_labels p k d, tail (p i) d = (residual_int p d : ℝ) := by
  calc
    _ = ∑ i,tail (p i) d := Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => inactive_tail p k i d hi)
    _ = _ := residual_tail_sum p hs d

private lemma residual_int_nonneg {m : ℕ} (p : Fin m → ℝ) (hs : ∑ i,p i=1) (d : ℕ) :
    0 ≤ residual_int p d := by
  have H : (0:ℝ) ≤ residual_int p d := by
    rw [← residual_tail_sum p hs d]
    exact Finset.sum_nonneg (fun i _ => (tail_bounds _ _).1)
  exact_mod_cast H

private lemma state_r_cast {m : ℕ} (p : Fin m → ℝ) (k : Fin m)
    (hs : ∑ i,p i=1) (d : ℕ) : ((state_of_law p k d).r : ℤ) = residual_int p d := by
  exact Int.toNat_of_nonneg (residual_int_nonneg p hs d)

private lemma state_bounds {m : ℕ} (p : Fin m → ℝ) (k : Fin m) (hs : ∑ i,p i=1) (d : ℕ) :
    0 < (state_of_law p k d).e ∧ (state_of_law p k d).r < (state_of_law p k d).e ∧
      (state_of_law p k d).e ≤ m := by
  classical
  have hk : k ∈ retained_labels p k d := (retained_mem _ _ _ _).mpr (Or.inl rfl)
  have hn : (retained_labels p k d).Nonempty := ⟨k,hk⟩
  have upper : (residual_int p d : ℝ) < (retained_labels p k d).card := by
    rw [← active_tail_sum p k hs d]
    calc
      _ < ∑ _i ∈ retained_labels p k d, (1:ℝ) :=
        Finset.sum_lt_sum_of_nonempty hn (fun i _ => (tail_bounds _ _).2)
      _ = _ := by simp
  have upperInt : residual_int p d < ((retained_labels p k d).card : ℤ) := by exact_mod_cast upper
  refine ⟨Finset.card_pos.mpr hn, ?_, ?_⟩
  · have R := state_r_cast p k hs d
    change (state_of_law p k d).r < (retained_labels p k d).card
    exact_mod_cast (show ((state_of_law p k d).r : ℤ) < (retained_labels p k d).card by rwa [R])
  · simpa [state_of_law] using Finset.card_le_card (Finset.subset_univ (retained_labels p k d))

private lemma column_count {m : ℕ} (p : Fin m → ℝ) (k : Fin m)
    (hk : ∀ i,p k≤p i) (hr : StrictlyRoundedLaw m p k) (d : ℕ) :
    (∑ i,bit (p i) d) = if bit (p k) d = 1 then ((state_of_law p k d).e : ℤ)
      else (departure_count p k d : ℤ) := by
  classical
  have H : (∑ i,bit (p i) d) = ∑ i,
      (if i ∈ retained_labels p k d then
        if bit (p k) d = 1 then (1:ℤ) else
          if i ∈ retained_labels p k (d+1) then 0 else 1
        else 0) := Finset.sum_congr rfl (fun i _ => column_rule p k hk hr d i)
  rw [H]
  by_cases hb : bit (p k) d = 1
  · simp only [hb,ite_true]
    simp [Finset.sum_boole,state_of_law]
  · simp only [hb,ite_false]
    have eqf (i : Fin m) :
        (if i ∈ retained_labels p k d then if i ∈ retained_labels p k (d+1) then (0:ℤ) else 1 else 0) =
          if i ∈ retained_labels p k d \ retained_labels p k (d+1) then 1 else 0 := by
      simp only [Finset.mem_sdiff]
      split_ifs <;> simp_all
    simp_rw [eqf]
    simp [Finset.sum_boole,departure_count]
    congr 1
    ext i
    simp

private lemma residual_next {m : ℕ} (p : Fin m → ℝ) (d : ℕ) :
    residual_int p (d+1) = 2*residual_int p d - ∑ i,bit (p i) d := by
  simp [residual_int,pow_succ,Finset.sum_sub_distrib,← Finset.mul_sum]
  ring

private lemma one_lower {m : ℕ} (p : Fin m → ℝ) (k : Fin m) (hs : ∑ i,p i=1)
    (hk : ∀ i,p k≤p i) (hr : StrictlyRoundedLaw m p k) (d : ℕ)
    (hb : bit (p k) d = 1) : (state_of_law p k d).e ≤ 2*(state_of_law p k d).r := by
  classical
  have low (i : Fin m) (hi : i ∈ retained_labels p k d) : (1/2:ℝ) ≤ tail (p i) d := by
    have H := tail_step (p i) d
    have hz := (tail_bounds (p i) (d+1)).1
    rw [column_rule p k hk hr d i,if_pos hi,if_pos hb] at H
    norm_num at H
    linarith
  have H := Finset.sum_le_sum low
  rw [active_tail_sum p k hs d] at H
  simp only [Finset.sum_const,nsmul_eq_mul] at H
  have R := state_r_cast p k hs d
  have H' : ((state_of_law p k d).e : ℝ) ≤ 2*(residual_int p d : ℝ) := by
    change ((retained_labels p k d).card : ℝ) ≤ _
    linarith
  exact_mod_cast (show ((state_of_law p k d).e : ℤ) ≤ 2*((state_of_law p k d).r : ℤ) by
    rw [R]; exact_mod_cast H')

private lemma zero_upper {m : ℕ} (p : Fin m → ℝ) (k : Fin m) (hs : ∑ i,p i=1)
    (hk : ∀ i,p k≤p i) (hr : StrictlyRoundedLaw m p k) (d : ℕ)
    (hb : bit (p k) d ≠ 1) : 2*(state_of_law p k d).r < (state_of_law p k d).e := by
  classical
  have bound (i : Fin m) (hi : i ∈ retained_labels p k d) : tail (p i) d ≤ (1/2:ℝ) := by
    have H := tail_step (p i) d
    rw [column_rule p k hk hr d i,if_pos hi,if_neg hb] at H
    by_cases hn : i ∈ retained_labels p k (d+1)
    · rw [if_pos hn] at H
      norm_num at H
      have hh := (tail_bounds (p i) (d+1)).2
      linarith
    · rw [if_neg hn,inactive_tail p k i (d+1) hn] at H
      norm_num at H
      linarith
  have ak : k ∈ retained_labels p k d := (retained_mem _ _ _ _).mpr (Or.inl rfl)
  have ank : k ∈ retained_labels p k (d+1) := (retained_mem _ _ _ _).mpr (Or.inl rfl)
  have strict : tail (p k) d < (1/2:ℝ) := by
    have H := tail_step (p k) d
    rw [column_rule p k hk hr d k,if_pos ak,if_neg hb,if_pos ank] at H
    norm_num at H
    have hh := (tail_bounds (p k) (d+1)).2
    linarith
  have H := Finset.sum_lt_sum bound ⟨k,ak,strict⟩
  rw [active_tail_sum p k hs d] at H
  simp only [Finset.sum_const,nsmul_eq_mul] at H
  have R := state_r_cast p k hs d
  have H' : 2*(residual_int p d : ℝ) < ((state_of_law p k d).e : ℝ) := by
    change _ < ((retained_labels p k d).card : ℝ)
    linarith
  exact_mod_cast (show 2*((state_of_law p k d).r : ℤ) < ((state_of_law p k d).e : ℤ) by
    rw [R]; exact_mod_cast H')

private lemma state_ext {s t : State} (hr : s.r=t.r) (he : s.e=t.e) : s=t := by
  cases s; cases t
  simp_all

private noncomputable def action {m : ℕ} (p : Fin m → ℝ) (k : Fin m) (d : ℕ) : Action :=
  if bit (p k) d = 1 then .one else .zero (departure_count p k d)

private lemma reverse_step {m : ℕ} (p : Fin m → ℝ) (k : Fin m) (hs : ∑ i,p i=1)
    (hk : ∀ i,p k≤p i) (hr : StrictlyRoundedLaw m p k) (d : ℕ) :
    Legal m (state_of_law p k d) (action p k d) ∧
      state_of_law p k (d+1) = successor (state_of_law p k d) (action p k d) := by
  classical
  obtain ⟨epos,rlt,emax⟩ := state_bounds p k hs d
  have re := residual_next p d
  rw [column_count p k hk hr d] at re
  have R := state_r_cast p k hs d
  have Rn := state_r_cast p k hs (d+1)
  rw [← R,← Rn] at re
  have ecount : (state_of_law p k (d+1)).e = (state_of_law p k d).e - departure_count p k d := by
    have H := Finset.card_le_card (retained_next p k d)
    dsimp [state_of_law,departure_count]
    rw [Finset.card_sdiff_of_subset (retained_next p k d)]
    omega
  by_cases hb : bit (p k) d = 1
  · have he := one_lower p k hs hk hr d hb
    have hzero : departure_count p k d = 0 := by
      apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      obtain ⟨hi,hn⟩ := Finset.mem_sdiff.mp hi
      have H := departure_anchor_zero p k hk hr d i hi hn
      omega
    simp only [hb,ite_true] at re
    have rn : (state_of_law p k (d+1)).r = 2*(state_of_law p k d).r - (state_of_law p k d).e := by omega
    refine ⟨⟨epos,rlt,emax,?_⟩,?_⟩
    · simpa [action,hb] using he
    · apply state_ext <;> simp [successor,action,hb,rn,ecount,hzero]
  · have he := zero_upper p k hs hk hr d hb
    simp only [hb,ite_false] at re
    have hh : departure_count p k d ≤ 2*(state_of_law p k d).r := by omega
    have rn : (state_of_law p k (d+1)).r = 2*(state_of_law p k d).r - departure_count p k d := by omega
    refine ⟨⟨epos,rlt,emax,?_⟩,?_⟩
    · simpa [action,hb] using And.intro he hh
    · apply state_ext <;> simp [successor,action,hb,rn,ecount]




end D5.S3.Arith.FibonacciAtomic.OptimalLaw.OptimalEmbedding

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 400000
open scoped BigOperators
namespace D5.S3.Arith.FibonacciAtomic.OptimalLaw.OptimalEmbedding
open D5.S3.Arith.FibonacciAtomic
open DyadicSupportLines OptimalLawStrictSlope TriangularPathNormalization
open D5.S3.Arith.FibonacciAtomic.OptimalLaw.StrictRounding D5.S3.Arith.FibonacciAtomic.OptimalLaw.OptimalEmbedding

private lemma fixed_retained_order {m : ℕ} (p : Fin m → ℝ) (k : Fin m)
    (hk : ∀ i,p k≤p i) (hr : StrictlyRoundedLaw m p k) : FixedRetainedOrder p k := by
  classical
  have hex (i : Fin m) (hi : p k<p i) :
      ∃ D : ℕ, 1≤D ∧ OnGrid (p i) D ∧ (∀ d<D, ¬OnGrid (p i) d) ∧
        p i=D5.S3.Arith.FibonacciAtomic.OptimalLaw.StrictRounding.round (p k) D := by
    obtain ⟨D,hD,hgrid,hmin,hround⟩ := hr i hi
    exact ⟨D,hD,hgrid,hmin,by
      simpa [D5.S3.Arith.FibonacciAtomic.OptimalLaw.StrictRounding.round,Int.cast_add,Int.cast_one] using hround⟩
  let rank : Fin m → WithTop ℕ := fun i =>
    if h : p i = p k then ⊤ else
      ((Classical.choose (hex i (lt_of_le_of_ne (hk i) (Ne.symm h))) : ℕ) : WithTop ℕ)
  have memrank (i : Fin m) (d : ℕ) : i ∈ retained_labels p k d ↔ (d : WithTop ℕ) < rank i := by
    rw [retained_mem]
    by_cases heq : p i = p k
    · simp [rank,heq]
    · let hlt := lt_of_le_of_ne (hk i) (Ne.symm heq)
      let D := Classical.choose (hex i hlt)
      have H := Classical.choose_spec (hex i hlt)
      change 1 ≤ D ∧ OnGrid (p i) D ∧ (∀ d<D, ¬OnGrid (p i) d) ∧ _ at H
      have grid_iff : OnGrid (p i) d ↔ D ≤ d := by
        constructor
        · intro hg
          by_contra hd
          exact H.2.2.1 d (by omega) hg
        · intro hd
          exact grid_up _ D d hd H.2.1
      simp only [heq,false_or,grid_iff,rank,dif_neg heq,WithTop.coe_lt_coe]
      change ¬D≤d ↔ (d:WithTop ℕ)<(D:WithTop ℕ)
      constructor
      · intro hd
        exact WithTop.coe_lt_coe.mpr (show d<D by omega)
      · intro hd
        have HD : d<D := WithTop.coe_lt_coe.mp hd
        omega
  let σ : Equiv.Perm (Fin m) := Tuple.sort (α := OrderDual (WithTop ℕ)) (fun i => OrderDual.toDual (rank i))
  have hsort : Antitone (fun i => rank (σ i)) := by
    intro i j hij
    exact (Tuple.monotone_sort (α := OrderDual (WithTop ℕ)) (fun i => OrderDual.toDual (rank i))) hij
  refine ⟨σ,?_⟩
  intro d i
  let S := Finset.univ.filter (fun j : Fin m => (d : WithTop ℕ) < rank (σ j))
  have hcard : S.card = (retained_labels p k d).card :=
    Finset.card_bijective σ σ.bijective (fun j => by simp [S,memrank])
  have HH := Tuple.lt_card_gt_iff_apply_gt_of_antitone (j := i) (a := (d:WithTop ℕ)) hsort
  rw [memrank]
  have HH' : i.val < S.card ↔ (d : WithTop ℕ)<rank (σ i) := HH
  rw [hcard] at HH'
  exact HH'.symm



private lemma positive_law_small {m : ℕ} (hm : 2 ≤ m) (p : Fin m → ℝ)
    (hp : ∀ i, 0 < p i) (hs : ∑ i, p i = 1) : ∀ i, p i < 1 := by
  haveI : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr hm
  intro i
  obtain ⟨j, hj⟩ := exists_ne i
  simpa only [hs] using Finset.single_lt_sum hj (Finset.mem_univ i)
    (Finset.mem_univ j) (hp j) (fun a _ _ => (hp a).le)

private lemma root_state {m : ℕ} (hm : 2≤m) (p : Fin m → ℝ) (k : Fin m)
    (hp : ∀ i,0<p i) (hs : ∑ i,p i=1) : state_of_law p k 0 = ⟨1,m⟩ := by
  classical
  have small := positive_law_small hm p hp hs
  have floors (i : Fin m) : floorPrefix (p i) 0 = 0 := by
    simp only [pow_zero,one_mul]
    exact Int.floor_eq_zero_iff.mpr ⟨(hp i).le,small i⟩
  have all : retained_labels p k 0 = Finset.univ := by
    apply Finset.ext
    intro i
    simp only [Finset.mem_univ,iff_true]
    apply (retained_mem _ _ _ _).mpr
    right
    rintro ⟨z,hz⟩
    simp only [pow_zero,one_mul] at hz
    have Z : z=0 := by
      have F := floors i
      simp only [pow_zero,one_mul,hz,Int.floor_intCast] at F
      exact F
    rw [Z] at hz
    norm_num at hz
    linarith [hp i]
  have fzero (i : Fin m) : ⌊p i⌋=0 := by simpa [] using floors i
  simp [state_of_law,all,fzero]

private noncomputable def path {m : ℕ} (hm : 2≤m) (p : Fin m → ℝ) (k : Fin m)
    (hp : ∀ i,0<p i) (hs : ∑ i,p i=1) (hk : ∀ i,p k≤p i)
    (hr : StrictlyRoundedLaw m p k) : RootPath m where
  state := state_of_law p k
  action := action p k
  root := root_state hm p k hp hs
  legal d := (reverse_step p k hs hk hr d).1
  step d := (reverse_step p k hs hk hr d).2

private lemma path_digit {m : ℕ} (hm : 2≤m) (p : Fin m → ℝ) (k : Fin m)
    (hp : ∀ i,0<p i) (hs : ∑ i,p i=1) (hk : ∀ i,p k≤p i)
    (hr : StrictlyRoundedLaw m p k) (σ : Equiv.Perm (Fin m))
    (hσ : ∀ d i, σ i∈retained_labels p k d ↔ i.val < (retained_labels p k d).card)
    (i : Fin m) (d : ℕ) :
    ((digit (path hm p k hp hs hk hr) i d).val : ℤ) = bit (p (σ i)) d := by
  classical
  have S := (reverse_step p k hs hk hr d).2
  have eS := congrArg State.e S
  have hi := hσ d i
  have hn := hσ (d+1) i
  rw [column_rule p k hk hr d (σ i)]
  dsimp only [digit,path,action,state_of_law]
  by_cases hb : bit (p k) d = 1
  · simp only [hb,ite_true]
    by_cases hh : σ i∈retained_labels p k d
    · simp [hh,hi.mp hh]
    · simp [hh,mt hi.mpr hh]
  · simp only [hb,ite_false] at eS ⊢
    have ee : (retained_labels p k (d+1)).card = (retained_labels p k d).card - departure_count p k d := by
      simpa [action,hb,successor,state_of_law] using eS
    by_cases hh : σ i∈retained_labels p k d
    · have hhi := hi.mp hh
      by_cases hhn : σ i∈retained_labels p k (d+1)
      · have hni := hn.mp hhn
        rw [ee] at hni
        simp [hh,hhi,hhn,show ¬(retained_labels p k d).card-departure_count p k d ≤ i.val by omega]
      · have hni := mt hn.mpr hhn
        rw [ee] at hni
        simp [hh,hhi,hhn,show (retained_labels p k d).card-departure_count p k d ≤ i.val by omega]
    · simp [hh,mt hi.mpr hh]

private lemma path_prefix {m : ℕ} (hm : 2≤m) (p : Fin m → ℝ) (k : Fin m)
    (hp : ∀ i,0<p i) (hs : ∑ i,p i=1) (hk : ∀ i,p k≤p i)
    (hr : StrictlyRoundedLaw m p k) (σ : Equiv.Perm (Fin m))
    (hσ : ∀ d i, σ i∈retained_labels p k d ↔ i.val < (retained_labels p k d).card)
    (i : Fin m) (d : ℕ) :
    (binaryPrefix (path hm p k hp hs hk hr) i d : ℤ) = floorPrefix (p (σ i)) d := by
  induction d with
  | zero =>
    simp only [binaryPrefix,Nat.cast_zero,pow_zero,one_mul]
    exact (Int.floor_eq_zero_iff.mpr ⟨(hp _).le,positive_law_small hm p hp hs _⟩).symm
  | succ d ih =>
    simp only [binaryPrefix,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,ih,path_digit hm p k hp hs hk hr σ hσ]
    omega

private lemma eq_of_floor_prefix (x y : ℝ) (h : ∀ d,floorPrefix x d=floorPrefix y d) : x=y := by
  have compare (a b : ℝ) (H : ∀ d,floorPrefix a d=floorPrefix b d) : a≤b := by
    have bound (d : ℕ) : a ≤ b+(1/2:ℝ)^d := by
      have lo := Int.floor_le ((2:ℝ)^d*b)
      have hi := Int.lt_floor_add_one ((2:ℝ)^d*a)
      change (floorPrefix b d:ℝ) ≤ _ at lo
      change _ < (floorPrefix a d:ℝ)+1 at hi
      rw [H d] at hi
      have HH : (2:ℝ)^d*(a-b)<1 := by linarith
      have HH' : a-b < 1/(2:ℝ)^d := (lt_div_iff₀ (by positivity)).mpr (by nlinarith only [HH])
      have hp : (1/2:ℝ)^d = 1/(2:ℝ)^d := by rw [div_pow,one_pow]
      rw [hp]
      linarith
    have tend : Filter.Tendsto (fun d : ℕ => b+(1/2:ℝ)^d) Filter.atTop (nhds b) := by
      simpa using tendsto_const_nhds.add
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)<1))
    exact ge_of_tendsto tend (Filter.Eventually.of_forall bound)
  exact le_antisymm (compare x y h) (compare y x (fun d=>(h d).symm))

private lemma embedding_of_strict_rounding {m : ℕ} (hm : 2≤m) (p : Fin m → ℝ) (k : Fin m)
    (hp : ∀ i,0<p i) (hs : ∑ i,p i=1) (hk : ∀ i,p k≤p i)
    (hr : StrictlyRoundedLaw m p k) : HasOptimalEmbedding m p k := by
  classical
  obtain ⟨σ,hσ⟩ := fixed_retained_order p k hk hr
  let γ := path hm p k hp hs hk hr
  obtain ⟨_,_,hfloor,hmin,hcost,_⟩ := TriangularPathNormalization.result m hm γ
  have heq (i : Fin m) : probability γ i=p (σ i) := by
    apply eq_of_floor_prefix
    intro d
    exact (hfloor i d).trans (path_prefix hm p k hp hs hk hr σ hσ i d)
  refine ⟨σ,γ,heq,?_,?_⟩
  · obtain ⟨hn,hmin⟩ := hmin
    rw [← hmin]
    apply le_antisymm
    · have HH := Finset.inf'_le (probability γ) (Finset.mem_univ (σ.symm k))
      rw [heq (σ.symm k),σ.apply_symm_apply] at HH
      exact HH
    · exact Finset.le_inf' hn _ (fun i _ => by rw [heq]; exact hk _)
  · unfold pathCost cost
    apply tsum_congr
    intro d
    congr 1
    have H := state_r_cast p k hs d
    have H' : ((state_of_law p k d).r : ℝ) = (residual_int p d : ℝ) := by exact_mod_cast H
    change ((state_of_law p k d).r : ℝ) = DyadicSupportLines.residual p d
    rw [H']
    simp only [residual_int,DyadicSupportLines.residual]
    push_cast
    rfl

theorem result (m : ℕ) (hm : 2≤m) (p : Fin m → ℝ) (k : Fin m)
    (hp : ∀ i,0<p i) (hs : ∑ i,p i=1) (hk : ∀ i,p k≤p i)
    (ho : cost p / p k = alpha m) : HasOptimalEmbedding m p k :=
  embedding_of_strict_rounding hm p k hp hs hk (D5.S3.Arith.FibonacciAtomic.OptimalLaw.StrictRounding.result m hm p k hp hs hk ho)


end D5.S3.Arith.FibonacciAtomic.OptimalLaw.OptimalEmbedding
