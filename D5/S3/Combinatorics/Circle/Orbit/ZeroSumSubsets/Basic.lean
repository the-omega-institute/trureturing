/- GID: D5/S3/Combinatorics/Circle/Orbit/ZeroSumSubsets/Basic
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/Orbit/ZeroSumSubsets/Basic
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Combinatorics.Colex, mathlib/module/Mathlib.Data.Nat.GCD.Basic, mathlib/module/Mathlib.Data.Finset.Powerset]
   utility: none
   digest: Unique natural cyclic carries give sharp unit relation length and source gcd restrictions. -/
module
public import D5.S3.Combinatorics.Circle.SourceWidth
public import Mathlib.Combinatorics.Colex
public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Set.Pairwise.Lattice
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.Algebra.Ring.GeomSum

/-! # Integer zero subsets of the labelled centered doubling source -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

namespace D5.S3.Combinatorics.Circle.ZeroSumSubsets
open SourceWidth
open scoped BigOperators

/-- All physical-label subsets with exact integer source sum zero. -/
def zeroSubsets (k t : ℕ) : Finset (Finset (Fin k)) :=
  Finset.univ.filter (fun A => ∑ p ∈ A, actualSource k t p = 0)

def mask {k : ℕ} (A : Finset (Fin k)) : ℕ := ∑ p ∈ A, 2 ^ p.val

theorem mask_as_geom {k : ℕ} (A : Finset (Fin k)) :
    mask A = ∑ i ∈ A.image Fin.val, 2 ^ i := by
  rw [Finset.sum_image]
  · rfl
  · intro p hp q hq he
    exact Fin.ext he

theorem mask_injective (k : ℕ) : Function.Injective (@mask k) := by
  intro A B he
  have hi : A.image Fin.val = B.image Fin.val :=
    Finset.geomSum_injective (by decide : 2 ≤ (2 : ℕ))
      (by simpa only [mask_as_geom] using he)
  exact Finset.image_injective Fin.val_injective hi

theorem mask_bound {k : ℕ} (A : Finset (Fin k)) : mask A ≤ 2 ^ k - 1 := by
  have h : mask A < 2 ^ k := by
    rw [mask_as_geom]
    apply Nat.geomSum_lt (by decide)
    intro i hi
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hi
    exact p.isLt
  omega

theorem coefficient_weight_dvd {k t : ℕ} (n : Fin k → ℕ)
    (hzero : (∑ i, (n i : ℤ) * actualSource k t i) = 0) :
    (2 ^ k - 1) ∣ t * (∑ i, n i * 2 ^ i.val) := by
  have hs : modulus k ∣ ∑ i : Fin k,
      (n i : ℤ) * ((2 : ℤ) ^ i.val * (t : ℤ) - actualSource k t i) := by
    apply Finset.dvd_sum
    intro i _
    apply dvd_mul_of_dvd_right
    apply Int.modEq_iff_dvd.mp
    change centered (modulus k) ((2 : ℤ) ^ i.val * (t : ℤ)) % modulus k =
      ((2 : ℤ) ^ i.val * (t : ℤ)) % modulus k
    simp only [centered, Int.emod_sub_emod, add_sub_cancel_right]
  have he : (∑ i, (n i : ℤ) * ((2 : ℤ) ^ i.val * t - actualSource k t i)) =
      (t : ℤ) * ∑ i, (n i : ℤ) * 2 ^ i.val := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, hzero, sub_zero, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _; ring
  rw [he] at hs
  have hm : modulus k = ((2 ^ k - 1 : ℕ) : ℤ) := by
    dsimp [modulus]
    rw [Nat.cast_sub (by have := pow_pos (by decide : 0 < (2 : ℕ)) k; omega)]
    norm_cast
  rw [hm] at hs
  exact_mod_cast hs

theorem zero_mask_dvd {k t : ℕ} (A : Finset (Fin k))
    (hA : (∑ p ∈ A, actualSource k t p) = 0) : (2 ^ k - 1) ∣ t * mask A := by
  classical
  have he := coefficient_weight_dvd (t := t) (fun i => if i ∈ A then 1 else 0)
    (by simpa using hA)
  simpa [mask] using he

theorem quotient_dvd {N t m : ℕ} (hN : 0 < N) (h : N ∣ t * m) :
    N / Nat.gcd t N ∣ m := by
  have hg := Nat.gcd_pos_of_pos_right t hN
  have hc : Nat.gcd t N * (N / Nat.gcd t N) ∣
      Nat.gcd t N * ((t / Nat.gcd t N) * m) := by
    simpa only [← mul_assoc, Nat.mul_div_cancel' (Nat.gcd_dvd_right t N),
      Nat.mul_div_cancel' (Nat.gcd_dvd_left t N)] using h
  exact (Nat.coprime_div_gcd_div_gcd hg).symm.dvd_mul_left.mp
    (Nat.dvd_of_mul_dvd_mul_left hg hc)

/-- Surjectivity uses the already proved mask injection and the two equal finite
cardinalities. In particular both endpoints 0 and 2^r-1 remain represented. -/
theorem mask_surjective (r : ℕ) (n : ℕ) (hn : n < 2 ^ r) :
    ∃ A : Finset (Fin r), mask A = n := by
  classical
  let f : Finset (Fin r) → Fin (2 ^ r) := fun A =>
    ⟨mask A, by
      have hb := mask_bound A
      have hp : 1 ≤ (2 : ℕ) ^ r := Nat.one_le_two_pow
      omega⟩
  have hi : Function.Injective f := by
    intro A B he
    exact mask_injective r (congrArg Fin.val he)
  have hb : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr ⟨hi, by simp⟩
  obtain ⟨A, hA⟩ := hb.2 ⟨n, hn⟩
  exact ⟨A, congrArg Fin.val hA⟩

/-- Count divisible physical binary masks, including both endpoint masks.
This is the counting bijection extracted from TwoBitZeroSubsets. Its two
consumers supply their separate exact-integer-zero equivalences. -/
theorem divisible_mask_card (r t : ℕ) (hr : 0 < r) :
    (Finset.univ.filter (fun A : Finset (Fin r) =>
      (2 ^ r - 1) / Nat.gcd t (2 ^ r - 1) ∣ mask A)).card =
      Nat.gcd t (2 ^ r - 1) + 1 := by
  classical
  let N := 2 ^ r - 1
  let d := Nat.gcd t N
  let Q := N / d
  let S := Finset.univ.filter (fun A : Finset (Fin r) => Q ∣ mask A)
  have hN : 0 < N := by
    have hp := Nat.one_lt_two_pow (ne_of_gt hr)
    dsimp [N]
    omega
  have hQ : 0 < Q := Nat.div_gcd_pos_of_pos_right t hN
  have hQd : Q * d = N := Nat.div_mul_cancel (Nat.gcd_dvd_right t N)
  have hd (A : Finset (Fin r)) (hA : A ∈ S) : Q ∣ mask A :=
    (Finset.mem_filter.mp hA).2
  have hbound (A : Finset (Fin r)) : mask A / Q < d + 1 := by
    have hb : mask A ≤ N := mask_bound A
    have hle := Nat.div_le_div_right hb (c := Q)
    rw [← hQd, Nat.mul_div_cancel_left d hQ] at hle
    omega
  have hcount : S.card = (Finset.range (d + 1)).card := by
    apply Finset.card_nbij (fun A : Finset (Fin r) => mask A / Q)
    · intro A hA
      exact Finset.mem_range.mpr (hbound A)
    · intro A hA B hB he
      change mask A / Q = mask B / Q at he
      apply mask_injective r
      calc
        mask A = mask A / Q * Q := (Nat.div_mul_cancel (hd A hA)).symm
        _ = mask B / Q * Q := by rw [he]
        _ = mask B := Nat.div_mul_cancel (hd B hB)
    · intro n hn
      have hnle : n ≤ d := by
        have := Finset.mem_range.mp hn
        omega
      have hmul : Q * n ≤ N := by
        calc
          Q * n ≤ Q * d := Nat.mul_le_mul_left Q hnle
          _ = N := hQd
      have hsmall : Q * n < 2 ^ r := by
        dsimp [N] at hmul
        have hp : 1 ≤ (2 : ℕ) ^ r := Nat.one_le_two_pow
        omega
      obtain ⟨A, hmask⟩ := mask_surjective r (Q * n) hsmall
      have hA : A ∈ S := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        change Q ∣ mask A
        rw [hmask]
        exact ⟨n, rfl⟩
      refine ⟨A, hA, ?_⟩
      change mask A / Q = n
      rw [hmask, Nat.mul_div_cancel_left n hQ]
  simpa only [S, Finset.card_range] using hcount


end D5.S3.Combinatorics.Circle.ZeroSumSubsets
