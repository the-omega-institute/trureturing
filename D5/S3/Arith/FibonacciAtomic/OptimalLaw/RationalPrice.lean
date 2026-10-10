/- GID: D5/S3/Arith/FibonacciAtomic/OptimalLaw/RationalPrice
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/OptimalLaw/RationalPrice
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: The optimal full-real slope is a positive rational number and the unique real zero of the triangular root value. -/

import D5.S3.Arith.FibonacciAtomic.TriangularPathNormalization
import D5.S3.Arith.FibonacciAtomic.OptimalLawStrictSlope
import Mathlib.Data.Fin.Tuple.Sort
import D5.S3.Arith.FibonacciAtomic.OptimalLaw.StrictRounding
import D5.S3.Arith.FibonacciAtomic.OptimalLaw.LeafExchange
import D5.S1.Digit.RadixFloorDigit
import D5.S3.Arith.FibonacciAtomic.TriangularFirstSplitRecurrence
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Fintype.Pigeonhole

local notation "floorPrefix" => (fun (x : ℝ) (d : ℕ) => ⌊(2 : ℝ) ^ d * x⌋)
local notation "bit" => (fun (x : ℝ) (d : ℕ) => ⌊(2 : ℝ) ^ (d + 1) * x⌋ - 2 * ⌊(2 : ℝ) ^ d * x⌋)
local notation "tail" => (fun (x : ℝ) (d : ℕ) => Int.fract ((2 : ℝ) ^ d * x))

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

open scoped BigOperators
namespace D5.S3.Arith.FibonacciAtomic.OptimalLaw.RationalPrice
open D5.S3.Arith.FibonacciAtomic
open DyadicSupportLines OptimalLawStrictSlope TriangularPathNormalization TriangularFirstSplitRecurrence
open D5.S3.Arith.FibonacciAtomic.OptimalLaw.StrictRounding

/-- An attained law is represented by one fixed
    permutation and one legal triangular root path with exact cost. -/
def HasOptimalEmbedding (m : ℕ) (p : Fin m → ℝ) (k : Fin m) : Prop :=
  ∃ σ : Equiv.Perm (Fin m), ∃ γ : RootPath m,
    (∀ i, probability γ i = p (σ i)) ∧
    anchorMass γ = p k ∧ pathCost γ = cost p

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

theorem embedding_result (m : ℕ) (hm : 2≤m) (p : Fin m → ℝ) (k : Fin m)
    (hp : ∀ i,0<p i) (hs : ∑ i,p i=1) (hk : ∀ i,p k≤p i)
    (ho : cost p / p k = alpha m) : HasOptimalEmbedding m p k :=
  embedding_of_strict_rounding hm p k hp hs hk (D5.S3.Arith.FibonacciAtomic.OptimalLaw.StrictRounding.result m hm p k hp hs hk ho)

private theorem triangular_lower (m : ℕ) (hm : 2 ≤ m) (γ : RootPath m) :
    OptimalLawStrictSlope.alpha m * anchorMass γ ≤ pathCost γ := by
  classical
  obtain ⟨hnonneg, hsum, _, hmin, hcost, hpositive⟩ :=
    TriangularPathNormalization.result m hm γ
  by_cases ht : 0 < anchorMass γ
  · obtain ⟨hn, hminimum⟩ := hmin
    obtain ⟨i, hi, heq⟩ := Finset.exists_mem_eq_inf' hn (probability γ)
    have heq' : probability γ i = anchorMass γ := heq.symm.trans hminimum
    have hlow : ∀ j, probability γ i ≤ probability γ j := by
      intro j
      rw [← heq]
      exact Finset.inf'_le _ (Finset.mem_univ j)
    have H := OptimalLawStrictSlope.alpha_le m (probability γ)
      (hpositive ht) hsum i hlow
    rw [heq'] at H
    rw [hcost]
    exact (le_div_iff₀ ht).mp H
  · have ha : 0 ≤ anchorMass γ := tsum_nonneg (fun d => by positivity)
    have hz : anchorMass γ = 0 := by linarith
    rw [hz, mul_zero]
    exact tsum_nonneg (fun d => by positivity)

private def root_path (m : ℕ) (γ : TriangularFirstSplitRecurrence.Path m 1) : RootPath m where
  state := γ.state
  action := γ.action
  root := γ.start
  legal := γ.legal
  step := γ.step

private theorem below_alpha_nonnegative (m : ℕ) (hm : 2 ≤ m) (x : ℝ)
    (hx : x ≤ OptimalLawStrictSlope.alpha m) :
    0 ≤ TriangularFirstSplitRecurrence.W x m 1 := by
  apply le_csInf
  · exact ⟨_, ⟨TriangularFirstSplitRecurrence.noSplit m 1 (by omega), rfl⟩⟩
  · rintro y ⟨γ, rfl⟩
    have H := triangular_lower m hm (root_path m γ)
    have ht : 0 ≤ anchorMass (root_path m γ) := tsum_nonneg (fun d => by positivity)
    have HM := mul_le_mul_of_nonneg_right hx ht
    change 0 ≤ pathCost (root_path m γ) - x * anchorMass (root_path m γ)
    linarith

private theorem zero_if_optimum_embeds (m : ℕ) (hm : 2 ≤ m)
    (γ : RootPath m)
    (h : pathCost γ = OptimalLawStrictSlope.alpha m * anchorMass γ) :
    TriangularFirstSplitRecurrence.W (OptimalLawStrictSlope.alpha m) m 1 = 0 := by
  have low := below_alpha_nonnegative m hm _ le_rfl
  let δ : TriangularFirstSplitRecurrence.Path m 1 :=
    ⟨γ.state, γ.action, γ.root, γ.legal, γ.step⟩
  have hd : TriangularFirstSplitRecurrence.pathValue (OptimalLawStrictSlope.alpha m) δ = 0 := by
    change pathCost γ - OptimalLawStrictSlope.alpha m * anchorMass γ = 0
    linarith
  have H : TriangularFirstSplitRecurrence.W (OptimalLawStrictSlope.alpha m) m 1 ≤
      TriangularFirstSplitRecurrence.pathValue (OptimalLawStrictSlope.alpha m) δ := by
    apply csInf_le
    · refine ⟨0, ?_⟩
      rintro y ⟨η, rfl⟩
      have HH := triangular_lower m hm (root_path m η)
      change 0 ≤ pathCost (root_path m η) -
        OptimalLawStrictSlope.alpha m * anchorMass (root_path m η)
      linarith
    · exact ⟨δ, rfl⟩
  linarith

private lemma anchor_bounds (m : ℕ) (γ : RootPath m) : 0≤anchorMass γ ∧ anchorMass γ≤1 := by
  have eq : anchorMass γ = Real.ofDigits (fun d => anchorDigit (γ.action d)) := by
    simp [anchorMass,Real.ofDigits,Real.ofDigitsTerm,div_eq_mul_inv]
  rw [eq]
  exact ⟨Real.ofDigits_nonneg _,Real.ofDigits_le_one _⟩

private lemma root_cost (m : ℕ) (hm : 2≤m) (γ : RootPath m) : 1≤pathCost γ := by
  have summableR : Summable (fun d => ((γ.state d).r:ℝ)/(2:ℝ)^d) := by
    apply Summable.of_nonneg_of_le (f := fun d => (m:ℝ)*(1/2:ℝ)^d)
      (fun d => by positivity)
    · intro d
      have H : ((γ.state d).r:ℝ)≤m := by
        exact_mod_cast (Nat.le_trans (γ.legal d).2.1.le (γ.legal d).2.2.1)
      rw [div_pow,one_pow,mul_one_div]
      exact div_le_div_of_nonneg_right H (by positivity)
    · exact (summable_geometric_of_abs_lt_one (by norm_num : |(1/2:ℝ)|<1)).mul_left (m:ℝ)
  have H := summableR.sum_le_tsum ({0}:Finset ℕ) (fun d _ => by positivity)
  simpa [pathCost,γ.root] using H

private theorem at_alpha_zero (m : ℕ) (hm : 2≤m) : W (OptimalLawStrictSlope.alpha m) m 1=0 := by
  obtain ⟨p,k,hp,hs,hk,ho⟩ := OptimalLawStrictSlope.attained m hm
  obtain ⟨σ,γ,heq,hat,hcost⟩ := D5.S3.Arith.FibonacciAtomic.OptimalLaw.RationalPrice.embedding_result m hm p k hp hs hk ho
  apply zero_if_optimum_embeds m hm γ
  rw [hcost,hat]
  have H := (div_eq_iff (hp k).ne').mp ho
  simpa [mul_comm] using H

private lemma root_bdd_below (m : ℕ) (hm : 2≤m) (x : ℝ) :
    BddBelow (Set.range (fun γ : TriangularFirstSplitRecurrence.Path m 1 => pathValue x γ)) := by
  refine ⟨-(|x|),?_⟩
  rintro y ⟨γ,rfl⟩
  let δ := root_path m γ
  have hc := root_cost m hm δ
  have ht := anchor_bounds m δ
  have hprod : x*anchorMass δ≤|x| := by
    calc
      _ ≤ |x| * anchorMass δ := mul_le_mul_of_nonneg_right (le_abs_self x) ht.1
      _ ≤ |x| * 1 := mul_le_mul_of_nonneg_left ht.2 (abs_nonneg x)
      _ = _ := mul_one _
  change -|x| ≤pathCost δ-x*anchorMass δ
  linarith

/-- The triangular root value vanishes at exactly the full-real optimum. -/
theorem zero_iff_alpha (m : ℕ) (hm : 2≤m) (x : ℝ) :
    W x m 1=0 ↔ x=OptimalLawStrictSlope.alpha m := by
  constructor
  · intro hz
    rcases lt_trichotomy x (OptimalLawStrictSlope.alpha m) with hlt|heq|hgt
    · obtain ⟨γ,hγ⟩ := (TriangularFirstSplitRecurrence.result m hm x m ⟨by omega,le_rfl⟩ 1 (by omega)).2.2
      let δ := root_path m γ
      have hc := root_cost m hm δ
      have ht := (anchor_bounds m δ).1
      have lower := triangular_lower m hm δ
      have he : pathCost δ-x*anchorMass δ=0 := by
        change pathValue x γ=0
        rw [hγ,hz]
      by_cases hp : 0<anchorMass δ
      · have H := mul_lt_mul_of_pos_right hlt hp
        linarith
      · have H : anchorMass δ=0 := by linarith
        rw [H,mul_zero,sub_zero] at he
        linarith
    · exact heq
    · obtain ⟨p,k,hp,hs,hk,ho⟩ := OptimalLawStrictSlope.attained m hm
      obtain ⟨σ,γ,heq,hat,hcost⟩ := D5.S3.Arith.FibonacciAtomic.OptimalLaw.RationalPrice.embedding_result m hm p k hp hs hk ho
      let δ : TriangularFirstSplitRecurrence.Path m 1 := ⟨γ.state,γ.action,γ.root,γ.legal,γ.step⟩
      have hv : pathValue x δ<0 := by
        change pathCost γ-x*anchorMass γ<0
        rw [hat,hcost]
        have HC := (div_eq_iff (hp k).ne').mp ho
        have H := mul_lt_mul_of_pos_right hgt (hp k)
        nlinarith only [HC,H]
      have HW : W x m 1 ≤ pathValue x δ :=
        csInf_le (root_bdd_below m hm x) ⟨δ,rfl⟩
      rw [hz] at HW
      linarith
  · intro H
    rw [H]
    exact at_alpha_zero m hm

private lemma rational_of_dyadic (x : ℝ) (h : ∃ D : ℕ, ∃ z : ℤ, (2 : ℝ)^D*x=z) :
    ∃ q : ℚ, (q : ℝ)=x := by
  obtain ⟨D,z,hz⟩ := h
  refine ⟨(z:ℚ)/(2:ℚ)^D,?_⟩
  push_cast
  apply (div_eq_iff (by positivity : (2:ℝ)^D≠0)).mpr
  simpa [mul_comm] using hz.symm

private lemma normalized_rational_minimum (m : ℕ) (p : Fin m → ℝ) (k : Fin m)
    (hs : ∑ i, p i=1) (hk : ∀ i, p k≤p i)
    (hr : ∀ i, p k<p i → ∃ q:ℚ, (q:ℝ)=p i) :
    ∀ i, ∃ q:ℚ, (q:ℝ)=p i := by
  classical
  let S := Finset.univ.filter (fun i => p i=p k)
  have hS : S.Nonempty := ⟨k, by simp [S]⟩
  have hc : (S.card:ℝ)≠0 := by exact_mod_cast (Finset.card_pos.mpr hS).ne'
  let q : Fin m → ℚ := fun i => if hi : p k<p i then (hr i hi).choose else 0
  have qeq (i : Fin m) : (q i:ℝ)=if p k<p i then p i else 0 := by
    dsimp only [q]
    split_ifs with hi
    · exact (hr i hi).choose_spec
    · norm_num
  have sumS : (∑ i : Fin m, if p i=p k then p k else 0)=(S.card:ℝ)*p k := by
    rw [← Finset.sum_filter]
    simp [S]
  have sumEq : (S.card:ℝ)*p k+(∑ i, q i:ℚ)=1 := by
    rw [← sumS, Rat.cast_sum, ← Finset.sum_add_distrib, ← hs]
    apply Finset.sum_congr rfl
    intro i _
    rw [qeq]
    by_cases hi : p i=p k
    · simp [hi]
    · have hlt : p k<p i := lt_of_le_of_ne (hk i) (Ne.symm hi)
      simp [hi,hlt]
  let t : ℚ := (1-∑ i,q i)/(S.card:ℚ)
  have ht : (t:ℝ)=p k := by
    dsimp only [t]
    push_cast
    apply (div_eq_iff hc).mpr
    push_cast at sumEq
    nlinarith only [sumEq]
  intro i
  by_cases hi : p k<p i
  · exact hr i hi
  · have he : p i=p k := le_antisymm (le_of_not_gt hi) (hk i)
    exact ⟨t,ht.trans he.symm⟩

private theorem optimizer_rational (m : ℕ) (hm : 2≤m) (p : Fin m → ℝ) (k : Fin m)
    (hp : ∀ i,0<p i) (hs : ∑ i,p i=1) (hk : ∀ i,p k≤p i)
    (ho : cost p /p k=alpha m) : ∀ i, ∃ q:ℚ, (q:ℝ)=p i := by
  apply normalized_rational_minimum m p k hs hk
  intro i hi
  obtain ⟨D,hD,hz,_,_⟩ := D5.S3.Arith.FibonacciAtomic.OptimalLaw.StrictRounding.result m hm p k hp hs hk ho i hi
  exact rational_of_dyadic (p i) ⟨D,hz⟩

private lemma rational_of_equal_tails (f : ℕ → ℚ)
    (sm : Summable (fun d => (f d:ℝ)/(2:ℝ)^d))
    (a b : ℕ) (hab : a<b) (tails : ∀ n, f (n+a)=f (n+b)) :
    ∃ q:ℚ, (q:ℝ)=∑' d, (f d:ℝ)/(2:ℝ)^d := by
  let qa : ℚ := ∑ j∈Finset.range a, f j/(2:ℚ)^j
  let qb : ℚ := ∑ j∈Finset.range b, f j/(2:ℚ)^j
  have head (c : ℕ) : (∑ j∈Finset.range c, (f j:ℝ)/(2:ℝ)^j)+
      ((2:ℝ)^c)⁻¹*(∑' n, (f (n+c):ℝ)/(2:ℝ)^n)=
      ∑' d, (f d:ℝ)/(2:ℝ)^d := by
    rw [← sm.sum_add_tsum_nat_add c]
    congr 1
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    rw [pow_add]
    ring
  have hA := head a
  have hB := head b
  have castA : (qa:ℝ)=∑ j∈Finset.range a, (f j:ℝ)/(2:ℝ)^j := by
    dsimp only [qa]; push_cast; rfl
  have castB : (qb:ℝ)=∑ j∈Finset.range b, (f j:ℝ)/(2:ℝ)^j := by
    dsimp only [qb]; push_cast; rfl
  rw [← castA] at hA
  rw [← castB] at hB
  simp_rw [tails] at hA
  have denom : ((2:ℝ)^a)⁻¹-((2:ℝ)^b)⁻¹≠0 := by
    apply sub_ne_zero.mpr
    intro H
    exact (pow_lt_pow_right₀ (by norm_num : (1:ℝ)<2) hab).ne (inv_injective H)
  refine ⟨(((2:ℚ)^a)⁻¹*qb-((2:ℚ)^b)⁻¹*qa)/
    (((2:ℚ)^a)⁻¹-((2:ℚ)^b)⁻¹),?_⟩
  push_cast
  apply (div_eq_iff denom).mpr
  nlinarith [congrArg (fun y => ((2:ℝ)^b)⁻¹*y) hA,
    congrArg (fun y => ((2:ℝ)^a)⁻¹*y) hB]

private theorem rational_no_split (e r : ℕ) (hr : r<e) : ∃ q:ℚ, (q:ℝ)=U e r := by
  have bound (d : ℕ) : rho e r d<e := (noSplit e r hr).legal d |>.2.1
  have sm : Summable (fun d => (rho e r d:ℝ)/(2:ℝ)^d) := by
    apply Summable.of_nonneg_of_le (f := fun d => (e:ℝ)*(1/2:ℝ)^d)
      (fun d => by positivity)
    · intro d
      rw [div_pow, one_pow, mul_one_div]
      exact div_le_div_of_nonneg_right (by exact_mod_cast (bound d).le) (by positivity)
    · exact (summable_geometric_of_abs_lt_one (by norm_num : |(1/2:ℝ)|<1)).mul_left (e:ℝ)
  obtain ⟨a,b,hne,he⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun d : ℕ => (⟨rho e r d,bound d⟩ : Fin e))
  have eq : rho e r a=rho e r b := congrArg Fin.val he
  rcases lt_or_gt_of_ne hne with hab|hba
  · apply rational_of_equal_tails (fun d => (rho e r d:ℚ)) (by simpa using sm) a b hab
    intro n
    exact_mod_cast (show rho e r (n+a)=rho e r (n+b) from by
      simp only [rho, Function.iterate_add_apply]
      change (fun x:ℕ => 2*x%e)^[n] (rho e r a)=
        (fun x:ℕ => 2*x%e)^[n] (rho e r b)
      rw [eq])
  · apply rational_of_equal_tails (fun d => (rho e r d:ℚ)) (by simpa using sm) b a hba
    intro n
    exact_mod_cast (show rho e r (n+b)=rho e r (n+a) from by
      simp only [rho, Function.iterate_add_apply]
      change (fun x:ℕ => 2*x%e)^[n] (rho e r b)=
        (fun x:ℕ => 2*x%e)^[n] (rho e r a)
      rw [eq])

private lemma orbit_mod (e n d : ℕ) : rho e (n%e) d=(2^d*n)%e := by
  induction d with
  | zero => simp [rho]
  | succ d ih =>
    rw [rho, Function.iterate_succ_apply']
    change (2*rho e (n%e) d)%e=(2^(d+1)*n)%e
    rw [ih, pow_succ]
    rw [Nat.mul_mod_mod]
    congr 1
    ring

private lemma rational_fraction_cost (q : ℚ) (hq : 0≤q) :
    ∃ v:ℚ, (v:ℝ)=∑' d:ℕ, Int.fract ((2:ℝ)^d*(q:ℝ))/(2:ℝ)^d := by
  let n := q.num.natAbs
  let e := q.den
  have he : 0<e := Rat.pos q
  have qeq : (q:ℝ)=(n:ℝ)/(e:ℝ) := by
    have hn : (n:ℤ)=q.num := Int.natAbs_of_nonneg (Rat.num_nonneg.mpr hq)
    rw [Rat.cast_def]
    dsimp only [e]
    rw [← hn, Int.cast_natCast]
  have frac (d : ℕ) : Int.fract ((2:ℝ)^d*(q:ℝ))=(rho e (n%e) d:ℝ)/(e:ℝ) := by
    rw [qeq, ← mul_div_assoc]
    have heq : (2:ℝ)^d*(n:ℝ)=(2^d*n:ℕ) := by push_cast; rfl
    rw [heq, Int.fract_div_natCast_eq_div_natCast_mod, orbit_mod]
  obtain ⟨v,hv⟩ := rational_no_split e (n%e) (Nat.mod_lt _ he)
  refine ⟨v/(e:ℚ),?_⟩
  push_cast
  rw [hv,U,← tsum_div_const]
  apply tsum_congr
  intro d
  rw [frac]
  ring

/-- Every nonnegative normalized law with rational coordinates has rational dyadic cost. -/
theorem rational_law_cost (m : ℕ) (p : Fin m → ℝ)
    (hp : ∀ i,0≤p i) (hs : ∑ i,p i=1)
    (hr : ∀ i,∃ q:ℚ,(q:ℝ)=p i) : ∃ v:ℚ,(v:ℝ)=cost p := by
  classical
  choose q hq using hr
  have qp (i : Fin m) : 0≤q i := by exact_mod_cast (hq i).symm ▸ hp i
  choose v hv using (fun i => rational_fraction_cost (q i) (qp i))
  refine ⟨∑ i,v i,?_⟩
  rw [Rat.cast_sum]
  simp_rw [hv,hq]
  unfold cost
  rw [← Summable.tsum_finsetSum]
  · apply tsum_congr
    intro d
    simp only [Int.fract, sub_div, ← Finset.sum_div, Finset.sum_sub_distrib,
      ← Finset.mul_sum, hs,mul_one,DyadicSupportLines.residual,Int.cast_sum]
  · intro i _
    apply Summable.of_nonneg_of_le (f := fun d => (1/2:ℝ)^d)
      (fun d => div_nonneg (Int.fract_nonneg _) (by positivity))
    · intro d
      rw [div_pow,one_pow]
      exact div_le_div_of_nonneg_right (Int.fract_lt_one _).le (by positivity)
    · exact summable_geometric_of_abs_lt_one (by norm_num : |(1/2:ℝ)|<1)

/-- The full-real optimum has a positive rational representative. -/
theorem rational_alpha (m : ℕ) (hm : 2≤m) : ∃ A:ℚ, 0<A ∧ (A:ℝ)=alpha m := by
  obtain ⟨p,k,hp,hs,hk,ho⟩ := attained m hm
  have hr := D5.S3.Arith.FibonacciAtomic.OptimalLaw.RationalPrice.optimizer_rational m hm p k hp hs hk ho
  obtain ⟨q,hq⟩ := hr k
  obtain ⟨v,hv⟩ := D5.S3.Arith.FibonacciAtomic.OptimalLaw.RationalPrice.rational_law_cost m p (fun i => (hp i).le) hs hr
  have he : ((v/q:ℚ):ℝ)=alpha m := by
    push_cast
    rw [hv,hq,ho]
  refine ⟨v/q,?_,he⟩
  have ha : (0:ℝ)<alpha m := lt_of_lt_of_le
    (by exact_mod_cast (show 0<m by omega)) (alpha_ge_labels m hm)
  exact_mod_cast he.symm ▸ ha

/-- One positive rational equals the full-real optimum and is the unique real root price. -/
theorem result (m : ℕ) (hm : 2≤m) : ∃ A:ℚ,
    0<A ∧ (A:ℝ)=OptimalLawStrictSlope.alpha m ∧
    ∀ x:ℝ, TriangularFirstSplitRecurrence.W x m 1=0 ↔ x=(A:ℝ) := by
  obtain ⟨A,hA,he⟩ := D5.S3.Arith.FibonacciAtomic.OptimalLaw.RationalPrice.rational_alpha m hm
  refine ⟨A,hA,he,?_⟩
  intro x
  rw [he]
  exact D5.S3.Arith.FibonacciAtomic.OptimalLaw.RationalPrice.zero_iff_alpha m hm x

end D5.S3.Arith.FibonacciAtomic.OptimalLaw.RationalPrice
