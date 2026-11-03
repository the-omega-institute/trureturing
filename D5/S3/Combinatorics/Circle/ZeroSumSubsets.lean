/- GID: D5/S3/Combinatorics/Circle/ZeroSumSubsets
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/ZeroSumSubsets
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Combinatorics.Colex, mathlib/module/Mathlib.Data.Nat.GCD.Basic, mathlib/module/Mathlib.Data.Finset.Powerset]
   utility: none
   digest: Unique natural cyclic carries give sharp unit relation length and source gcd restrictions. -/
module
public import D5.S3.Combinatorics.Circle.SourceWidth
public import Mathlib.Combinatorics.Colex
public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.Data.Finset.Powerset
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
private def zeroSubsets (k t : ℕ) : Finset (Finset (Fin k)) :=
  Finset.univ.filter (fun A => ∑ p ∈ A, actualSource k t p = 0)

def mask {k : ℕ} (A : Finset (Fin k)) : ℕ := ∑ p ∈ A, 2 ^ p.val

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

private theorem coefficient_weight_dvd {k t : ℕ} (n : Fin k → ℕ)
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

private theorem zero_mask_dvd {k t : ℕ} (A : Finset (Fin k))
    (hA : (∑ p ∈ A, actualSource k t p) = 0) : (2 ^ k - 1) ∣ t * mask A := by
  classical
  have he := coefficient_weight_dvd (t := t) (fun i => if i ∈ A then 1 else 0)
    (by simpa using hA)
  simpa [mask] using he

private theorem quotient_dvd {N t m : ℕ} (hN : 0 < N) (h : N ∣ t * m) :
    N / Nat.gcd t N ∣ m := by
  have hg := Nat.gcd_pos_of_pos_right t hN
  have hc : Nat.gcd t N * (N / Nat.gcd t N) ∣
      Nat.gcd t N * ((t / Nat.gcd t N) * m) := by
    simpa only [← mul_assoc, Nat.mul_div_cancel' (Nat.gcd_dvd_right t N),
      Nat.mul_div_cancel' (Nat.gcd_dvd_left t N)] using h
  exact (Nat.coprime_div_gcd_div_gcd hg).symm.dvd_mul_left.mp
    (Nat.dvd_of_mul_dvd_mul_left hg hc)

private theorem carry_exists (k : ℕ) (n : Fin k → ℕ) (hne : n ≠ 0) :
    ∃ A : Finset (Fin k), A.Nonempty ∧ ∃ m : Fin k → ℕ,
      ∀ i, (n i : ℤ) = (if i ∈ A then (1 : ℤ) else 0) +
        2 * (m i : ℤ) - (m ((finRotate k).symm i) : ℤ) := by
  classical
  have aux : ∀ L : ℕ, ∀ n : Fin k → ℕ, (∑ i, n i) = L → n ≠ 0 →
      ∃ A : Finset (Fin k), A.Nonempty ∧ ∃ m : Fin k → ℕ,
        ∀ i, (n i : ℤ) = (if i ∈ A then (1 : ℤ) else 0) +
          2 * (m i : ℤ) - (m ((finRotate k).symm i) : ℤ) := by
    intro L
    induction L using Nat.strong_induction_on with
    | h L ih =>
      intro n hL hn
      by_cases hb : ∀ i, n i ≤ 1
      · let A := Finset.univ.filter (fun i => n i = 1)
        have hA : A.Nonempty := by
          by_contra he
          apply hn
          funext i
          have hi : i ∉ A := fun hi => he ⟨i, hi⟩
          simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hi
          have := hb i
          simpa using (show n i = 0 by omega)
        refine ⟨A, hA, 0, ?_⟩
        intro i
        have := hb i
        by_cases hi : n i = 1 <;> simp [A, hi] <;> omega
      · obtain ⟨j, hj⟩ := not_forall.mp hb
        have hj2 : 2 ≤ n j := by omega
        let n' : Fin k → ℕ := fun i =>
          (n i - (if i = j then 2 else 0)) + (if i = finRotate k j then 1 else 0)
        have hd (i : Fin k) : (n' i : ℤ) = (n i : ℤ) -
            (if i = j then 2 else 0) + (if i = finRotate k j then 1 else 0) := by
          by_cases hi : i = j
          · subst i
            simp only [n', eq_self, ite_true, Nat.cast_add, Nat.cast_sub hj2,
              Nat.cast_ofNat, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
          · simp [n', hi]
        have hsum : (∑ i, n' i) + 1 = L := by
          have he := congrArg (fun f : Fin k → ℤ => ∑ i, f i) (funext hd)
          simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib] at he
          simp at he
          exact_mod_cast (show (∑ i, (n' i : ℤ)) + 1 = L by
            have hc : (∑ i, (n i : ℤ)) = L := by exact_mod_cast hL
            linarith)
        have hn' : n' ≠ 0 := by
          intro he
          have hh := congrFun he (finRotate k j)
          have hp : 0 < n' (finRotate k j) := by
            dsimp [n']; simp only [ite_true, eq_self]; omega
          simp only [Pi.zero_apply] at hh
          omega
        obtain ⟨A, hA, m, hm⟩ := ih (∑ i, n' i) (by omega) n' rfl hn'
        refine ⟨A, hA, (fun i => m i + if i = j then 1 else 0), ?_⟩
        intro i
        have he := hm i
        have hpred : (finRotate k).symm i = j ↔ i = finRotate k j := by
          constructor
          · intro h; simpa only [Equiv.apply_symm_apply] using congrArg (finRotate k) h
          · intro h; rw [h]; exact Equiv.symm_apply_apply _ _
        simp only [Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
        simp only [hpred]
        have hh := hd i
        split_ifs at * <;> linarith
  exact aux (∑ i, n i) n rfl hne

private theorem carry_length {k : ℕ} (n m : Fin k → ℕ) (A : Finset (Fin k))
    (h : ∀ i, (n i : ℤ) = (if i ∈ A then (1 : ℤ) else 0) +
      2 * (m i : ℤ) - (m ((finRotate k).symm i) : ℤ)) :
    (∑ i, n i) = A.card + ∑ i, m i := by
  classical
  have he := congrArg (fun f : Fin k → ℤ => ∑ i, f i) (funext h)
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] at he
  have hc : (∑ i : Fin k, if i ∈ A then (1 : ℤ) else 0) = A.card := by simp
  rw [hc, (finRotate k).symm.sum_comp (fun i => (m i : ℤ))] at he
  exact_mod_cast (show (∑ i, (n i : ℤ)) = (A.card : ℤ) + ∑ i, (m i : ℤ) by linarith)

private theorem carry_injective (k : ℕ) :
    Function.Injective (fun m : Fin k → ℤ =>
      fun i => 2 * m i - m ((finRotate k).symm i)) := by
  intro m v he
  let d := fun i => m i - v i
  have hd (i) : 2 * d i = d ((finRotate k).symm i) := by
    have := congrFun he i
    dsimp [d]; linarith
  have ha (i) : 2 * |d i| = |d ((finRotate k).symm i)| := by
    rw [← hd, abs_mul]; norm_num
  have hs := congrArg (fun f : Fin k → ℤ => ∑ i, f i) (funext ha)
  simp only [← Finset.mul_sum] at hs
  rw [(finRotate k).symm.sum_comp (fun i => |d i|)] at hs
  have hz : (∑ i, |d i|) = 0 := by omega
  funext i
  have hle : |d i| ≤ ∑ j, |d j| := Finset.single_le_sum (fun j _ => abs_nonneg (d j))
    (Finset.mem_univ i)
  have : d i = 0 := abs_eq_zero.mp (by rw [hz] at hle; exact le_antisymm hle (abs_nonneg _))
  dsimp [d] at this
  linarith

theorem carry_weight {k : ℕ} (hk : 0 < k)
    (n m : Fin k → ℕ) (A : Finset (Fin k))
    (h : ∀ i, (n i : ℤ) = (if i ∈ A then (1 : ℤ) else 0) +
      2 * (m i : ℤ) - (m ((finRotate k).symm i) : ℤ)) :
    (∑ i, n i * 2 ^ i.val) = mask A +
      (2 ^ k - 1) * m ⟨k - 1, by omega⟩ := by
  classical
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hk)
  have hrot : (∑ i : Fin (r + 1), (m ((finRotate (r + 1)).symm i) : ℤ) * 2 ^ i.val) =
      ∑ i : Fin (r + 1), (m i : ℤ) * 2 ^ (finRotate (r + 1) i).val := by
    simpa only [Equiv.symm_apply_apply] using
      (Equiv.sum_comp (finRotate (r + 1))
        (fun i => (m ((finRotate (r + 1)).symm i) : ℤ) * 2 ^ i.val)).symm
  have hpoint (i : Fin (r + 1)) :
      2 * (m i : ℤ) * 2 ^ i.val - (m i : ℤ) * 2 ^ (finRotate (r + 1) i).val =
        if i = Fin.last r then ((2 : ℤ) ^ (r + 1) - 1) * m (Fin.last r) else 0 := by
    rw [coe_finRotate]
    by_cases hi : i = Fin.last r
    · subst i; simp only [eq_self, ite_true, Fin.val_last, pow_zero, mul_one, pow_succ]; ring
    · simp only [ite_eq_right hi, pow_succ]; ring
  have hsum : (∑ i : Fin (r + 1),
      (2 * (m i : ℤ) * 2 ^ i.val - (m ((finRotate (r + 1)).symm i) : ℤ) * 2 ^ i.val)) =
      ((2 : ℤ) ^ (r + 1) - 1) * m (Fin.last r) := by
    rw [Finset.sum_sub_distrib, hrot, ← Finset.sum_sub_distrib]
    simp_rw [hpoint]
    simp
  have he : (∑ i : Fin (r + 1), (n i : ℤ) * 2 ^ i.val) =
      (mask A : ℤ) + ((2 : ℤ) ^ (r + 1) - 1) * m (Fin.last r) := by
    calc
      _ = (∑ i : Fin (r + 1), (if i ∈ A then (1 : ℤ) else 0) * 2 ^ i.val) +
          ∑ i : Fin (r + 1),
            (2 * (m i : ℤ) * 2 ^ i.val - (m ((finRotate (r + 1)).symm i) : ℤ) * 2 ^ i.val) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        rw [h i]; ring
      _ = _ := by rw [hsum]; simp [mask]
  have hpow : 1 ≤ (2 : ℕ) ^ (r + 1) := Nat.succ_le_of_lt (pow_pos (by decide) _)
  have hlast : (⟨r + 1 - 1, by omega⟩ : Fin (r + 1)) = Fin.last r := by ext; simp
  rw [hlast]
  exact_mod_cast he

private theorem mask_pos {k : ℕ} {A : Finset (Fin k)} (hA : A.Nonempty) : 0 < mask A := by
  obtain ⟨i, hi⟩ := hA
  exact lt_of_lt_of_le (pow_pos (by decide : 0 < (2 : ℕ)) i.val)
    (Finset.single_le_sum (f := fun p : Fin k => 2 ^ p.val) (fun _ _ => Nat.zero_le _) hi)

private theorem mask_full (k : ℕ) : mask (Finset.univ : Finset (Fin k)) = 2 ^ k - 1 := by
  have he := Nat.geomSum_eq (by decide : 2 ≤ (2 : ℕ)) k
  rw [Finset.sum_range] at he
  simpa [mask] using he

private theorem carry_pair_unique {k : ℕ} (hk : 0 < k) (n : Fin k → ℕ)
    (A B : Finset (Fin k)) (m v : Fin k → ℕ) (hA : A.Nonempty) (hB : B.Nonempty)
    (hm : ∀ i, (n i : ℤ) = (if i ∈ A then (1 : ℤ) else 0) +
      2 * (m i : ℤ) - (m ((finRotate k).symm i) : ℤ))
    (hv : ∀ i, (n i : ℤ) = (if i ∈ B then (1 : ℤ) else 0) +
      2 * (v i : ℤ) - (v ((finRotate k).symm i) : ℤ)) : A = B ∧ m = v := by
  have hw := (carry_weight hk n m A hm).symm.trans (carry_weight hk n v B hv)
  have hmod : mask A ≡ mask B [MOD 2 ^ k - 1] := by
    have he := congrArg (fun x : ℕ => x % (2 ^ k - 1)) hw
    change mask A % (2 ^ k - 1) = mask B % (2 ^ k - 1)
    simpa [Nat.add_mod] using he
  have hAp := mask_pos hA
  have hBp := mask_pos hB
  have hAb := mask_bound A
  have hBb := mask_bound B
  have hmask : mask A = mask B := hmod.eq_of_abs_lt (by
    apply abs_lt.mpr
    have hAi : (0 : ℤ) < mask A := by exact_mod_cast hAp
    have hBi : (0 : ℤ) < mask B := by exact_mod_cast hBp
    have hAb' : (mask A : ℤ) ≤ (2 ^ k - 1 : ℕ) := by exact_mod_cast hAb
    have hBb' : (mask B : ℤ) ≤ (2 ^ k - 1 : ℕ) := by exact_mod_cast hBb
    constructor <;> omega)
  have hAB := mask_injective k hmask
  subst B
  refine ⟨rfl, ?_⟩
  have hc : (fun i => (m i : ℤ)) = (fun i => (v i : ℤ)) := carry_injective k (by
    funext i
    have hmi := hm i
    have hvi := hv i
    linarith)
  funext i
  exact_mod_cast congrFun hc i

theorem source_cycle {k : ℕ} (hk : 0 < k) (t : ℕ) :
    0 < modulus k ∧
    (∑ i : Fin k, actualSource k t i) = 0 ∧
    ∀ i : Fin k, 2 * actualSource k t i - actualSource k t (finRotate k i) =
      modulus k * (if modulus k < 4 * actualSource k t i then 1
        else if 4 * actualSource k t i < -modulus k then -1 else 0) := by
  have hp : 1 < (2 : ℕ) ^ k := Nat.one_lt_two_pow (ne_of_gt hk)
  have hpi : (1 : ℤ) < 2 ^ k := by exact_mod_cast hp
  have hN : 0 < modulus k := by unfold modulus; omega
  have hodd : modulus k % 2 = 1 := by
    obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hk)
    rw [modulus, pow_succ]; omega
  have hstep (i : Fin k) : actualSource k t (finRotate k i) =
      doubleStep (modulus k) (actualSource k t i) := by
    have hnext : actualSource k t (finRotate k i) =
        centered (modulus k) ((2 : ℤ) ^ (i.val + 1) * t) := by
      obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hk)
      by_cases hi : i = Fin.last r
      · subst i
        simp only [finRotate_last, actualSource, Fin.val_zero, pow_zero, one_mul,
          Fin.val_last, centered_full_period]
      · simp only [actualSource, coe_finRotate, ite_eq_right hi]
    rw [hnext]
    have he : (2 : ℤ) ^ (i.val + 1) * t = 2 * (2 ^ i.val * (t : ℤ)) := by
      rw [pow_succ]; ring
    rw [he, centered_double hN hodd]
    rfl
  let u := fun i : Fin k => actualSource k t i +
    if actualSource k t i < 0 then modulus k else 0
  have hpot (i : Fin k) : u (finRotate k i) - u i = actualSource k t i := by
    dsimp [u]
    rw [hstep]
    exact unsigned_step hN hodd (centered_bounds hN hodd _)
  have hzero : (∑ i : Fin k, actualSource k t i) = 0 := by
    simp_rw [← hpot]
    rw [Finset.sum_sub_distrib, Equiv.sum_comp, sub_self]
  refine ⟨hN, hzero, ?_⟩
  intro i
  rw [hstep]
  unfold doubleStep
  split_ifs <;> ring

private theorem carry_charge {k : ℕ} (n m : Fin k → ℕ) (A : Finset (Fin k))
    (s eps : Fin k → ℤ) (N : ℤ)
    (h : ∀ i, (n i : ℤ) = (if i ∈ A then (1 : ℤ) else 0) +
      2 * (m i : ℤ) - (m ((finRotate k).symm i) : ℤ))
    (hs : ∀ i, 2 * s i - s (finRotate k i) = N * eps i) :
    (∑ i, (n i : ℤ) * s i) = (∑ i ∈ A, s i) + N * ∑ i, (m i : ℤ) * eps i := by
  classical
  have hrot : (∑ i, (m ((finRotate k).symm i) : ℤ) * s i) =
      ∑ i, (m i : ℤ) * s (finRotate k i) := by
    simpa only [Equiv.symm_apply_apply] using
      (Equiv.sum_comp (finRotate k) (fun i => (m ((finRotate k).symm i) : ℤ) * s i)).symm
  calc
    _ = (∑ i, (if i ∈ A then (1 : ℤ) else 0) * s i) +
        ((∑ i, 2 * (m i : ℤ) * s i) - ∑ i, (m ((finRotate k).symm i) : ℤ) * s i) := by
      rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [h i]; ring
    _ = (∑ i ∈ A, s i) + ∑ i, (m i : ℤ) * (2 * s i - s (finRotate k i)) := by
      rw [hrot, ← Finset.sum_sub_distrib]
      congr 1
      · simp
      · apply Finset.sum_congr rfl; intro i _; ring
    _ = _ := by
      simp_rw [hs]
      rw [Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      ring

private theorem neutral_carry_selector {k : ℕ} (c : Fin k → Bool) (u : Fin k → ℕ)
    (eps : Fin k → ℤ)
    (heps : ∀ a, eps a = ((c a).toNat : ℤ) - ((c (finRotate k a)).toNat : ℤ))
    (hQ : (∑ a, (u a : ℤ) * eps a) = 0) (hu : u ≠ 0) :
    (∃ i, eps i = 0 ∧ 0 < u i ∧
      2 ≤ 1 + 2 * (u i : ℤ) - (u ((finRotate k).symm i) : ℤ)) ∨
    (∃ i j, eps i = 1 ∧ eps j = -1 ∧ i ≠ j ∧ 0 < u i ∧ 0 < u j ∧
      2 ≤ 1 + 2 * (u i : ℤ) - (u ((finRotate k).symm i) : ℤ) ∧
      2 ≤ 1 + 2 * (u j : ℤ) - (u ((finRotate k).symm j) : ℤ)) := by
  classical
  let tau := finRotate k
  let pred := tau.symm
  let T : Finset (Fin k) := Finset.univ.filter (fun a => c a = true)
  have hbool (b : Bool) : (b.toNat : ℤ) = if b = true then 1 else 0 := by
    cases b <;> simp
  have hsum_true (f : Fin k → ℤ) :
      (∑ a, f a * (c a).toNat) = (∑ a ∈ T, f a) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro a ha
    by_cases hca : c a = true <;> simp [T, hca, hbool]
  have hsum_rot (f : Fin k → ℤ) :
      (∑ a, f a * (c (tau a)).toNat) =
        (∑ a ∈ T, f (pred a)) := by
    have hrot := (Equiv.sum_comp tau (fun a => f (pred a) * (c a).toNat))
    have hrot' :
        (∑ a, f a * (c (tau a)).toNat) =
          ∑ a, f (pred a) * (c a).toNat := by
      simpa only [tau, pred, Equiv.symm_apply_apply] using hrot
    rw [hrot', hsum_true]
  have hbalance : (∑ a ∈ T, (u a : ℤ)) = (∑ a ∈ T, (u (pred a) : ℤ)) := by
    have h := hQ
    simp_rw [heps, mul_sub] at h
    rw [Finset.sum_sub_distrib] at h
    have h' := hsum_true (fun a => (u a : ℤ))
    have h'' := hsum_rot (fun a => (u a : ℤ))
    rw [h', h''] at h
    omega
  have bad : ∀ (d : Fin k → Bool) (ed : Fin k → ℤ),
      (∀ a, ed a = ((d a).toNat : ℤ) - ((d (tau a)).toNat : ℤ)) →
      (∑ a, (u a : ℤ) * ed a = 0) →
      (∀ i, ¬ (ed i = 0 ∧ 0 < u i ∧
        2 ≤ 1 + 2 * (u i : ℤ) - (u (pred i) : ℤ))) →
      (∀ i, ¬ (ed i = 1 ∧ 0 < u i ∧
        2 ≤ 1 + 2 * (u i : ℤ) - (u (pred i) : ℤ))) → False := by
    intro d ed hed hEd hno0 hno1
    let S : Finset (Fin k) := Finset.univ.filter (fun a => d a = true)
    have hsum_true_d (f : Fin k → ℤ) :
        (∑ a, f a * (d a).toNat) = (∑ a ∈ S, f a) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro a ha
      by_cases hda : d a = true <;> simp [S, hda]
    have hsum_rot_d (f : Fin k → ℤ) :
        (∑ a, f a * (d (tau a)).toNat) =
          (∑ a ∈ S, f (pred a)) := by
      have hrot := (Equiv.sum_comp tau (fun a => f (pred a) * (d a).toNat))
      have hrot' :
          (∑ a, f a * (d (tau a)).toNat) =
            ∑ a, f (pred a) * (d a).toNat := by
        have hpt : ∀ x, pred (tau x) = x := fun x => Equiv.symm_apply_apply tau x
        simpa only [hpt] using hrot
      rw [hrot', hsum_true_d]
    have hbal_d : (∑ a ∈ S, (u a : ℤ)) = (∑ a ∈ S, (u (pred a) : ℤ)) := by
      have h := hEd
      simp_rw [hed, mul_sub] at h
      rw [Finset.sum_sub_distrib] at h
      have h' := hsum_true_d (fun a => (u a : ℤ))
      have h'' := hsum_rot_d (fun a => (u a : ℤ))
      rw [h', h''] at h
      omega
    have hineqS : ∀ a ∈ S, 2 * (u a : ℤ) ≤ (u (pred a) : ℤ) := by
      intro a ha
      have hda : d a = true := by simpa [S] using ha
      by_cases hnext : d (tau a) = true
      · have he : ed a = 0 := by rw [hed a, hda, hnext]; norm_num
        by_cases hzero : u a = 0
        · simp [hzero]
        · have hnot : ¬ (2 ≤ 1 + 2 * (u a : ℤ) - (u (pred a) : ℤ)) := by
            intro hq
            exact hno0 a ⟨he, Nat.pos_of_ne_zero hzero, hq⟩
          have hq : 1 + 2 * (u a : ℤ) - (u (pred a) : ℤ) < 2 :=
            lt_of_not_ge hnot
          omega
      · have hnext' : d (tau a) = false := Bool.eq_false_iff.mpr hnext
        have he : ed a = 1 := by rw [hed a, hda, hnext']; norm_num
        by_cases hzero : u a = 0
        · simp [hzero]
        · have hnot : ¬ (2 ≤ 1 + 2 * (u a : ℤ) - (u (pred a) : ℤ)) := by
            intro hq
            exact hno1 a ⟨he, Nat.pos_of_ne_zero hzero, hq⟩
          have hq : 1 + 2 * (u a : ℤ) - (u (pred a) : ℤ) < 2 :=
            lt_of_not_ge hnot
          omega
    have hsumS : (∑ a ∈ S, (u a : ℤ)) = 0 := by
      have hs := Finset.sum_le_sum hineqS
      rw [← Finset.mul_sum, hbal_d] at hs
      have hn : 0 ≤ ∑ a ∈ S, (u a : ℤ) := by
        exact Finset.sum_nonneg fun a ha => by positivity
      omega
    have hSzero : ∀ a ∈ S, u a = 0 := by
      intro a ha
      have hleNat : u a ≤ ∑ b ∈ S, u b :=
        Finset.single_le_sum (f := fun b : Fin k => u b) (fun b _ => Nat.zero_le _) ha
      have hle : (u a : ℤ) ≤ ∑ b ∈ S, (u b : ℤ) := by
        exact_mod_cast hleNat
      have : (u a : ℤ) = 0 := by rw [hsumS] at hle; omega
      exact_mod_cast this
    have hpredsum : (∑ a ∈ S, (u (pred a) : ℤ)) = 0 := by rw [← hbal_d, hsumS]
    have hpredzero : ∀ a ∈ S, u (pred a) = 0 := by
      intro a ha
      have hleNat : u (pred a) ≤ ∑ b ∈ S, u (pred b) :=
        Finset.single_le_sum (f := fun b : Fin k => u (pred b))
          (fun b _ => Nat.zero_le _) ha
      have hle : (u (pred a) : ℤ) ≤ ∑ b ∈ S, (u (pred b) : ℤ) := by
        exact_mod_cast hleNat
      have : (u (pred a) : ℤ) = 0 := by rw [hpredsum] at hle; omega
      exact_mod_cast this
    have hall : ∀ a, 2 * (u a : ℤ) ≤ (u (pred a) : ℤ) := by
      intro a
      by_cases ha : a ∈ S
      · rw [hSzero a ha]
        positivity
      by_cases hpa : tau a ∈ S
      · have hzero : u a = 0 := by
          have hp := hpredzero (tau a) hpa
          simpa [pred] using hp
        simp [hzero]
      by_cases hda : d a = true
      · exfalso
        apply ha
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hda⟩
      · by_cases hnext : d (tau a) = true
        · have hzero : u a = 0 := by
            have hp := hpredzero (tau a)
              (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnext⟩)
            simpa [pred] using hp
          simp [hzero]
        · have hda' : d a = false := Bool.eq_false_iff.mpr hda
          have hnext' : d (tau a) = false := Bool.eq_false_iff.mpr hnext
          have he : ed a = 0 := by rw [hed a, hda', hnext']; norm_num
          by_cases hzero : u a = 0
          · simp [hzero]
          · have hnot : ¬ (2 ≤ 1 + 2 * (u a : ℤ) - (u (pred a) : ℤ)) := by
              intro hq
              exact hno0 a ⟨he, Nat.pos_of_ne_zero hzero, hq⟩
            have hq : 1 + 2 * (u a : ℤ) - (u (pred a) : ℤ) < 2 :=
              lt_of_not_ge hnot
            omega
    have hs := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin k))) (fun a _ => hall a)
    have hpred_total : (∑ a, (u (pred a) : ℤ)) = ∑ a, (u a : ℤ) := by
      simpa [pred] using (Equiv.sum_comp pred (fun a => (u a : ℤ)))
    rw [← Finset.mul_sum, hpred_total] at hs
    have hn : 0 ≤ ∑ a, (u a : ℤ) := by
      exact Finset.sum_nonneg fun a ha => by positivity
    have hz : ∑ a, (u a : ℤ) = 0 := by omega
    apply hu
    funext a
    have hle : (u a : ℤ) ≤ ∑ b, (u b : ℤ) := by
      exact_mod_cast Finset.single_le_sum (fun b _ => Nat.zero_le _) (Finset.mem_univ a)
    have : (u a : ℤ) = 0 := by rw [hz] at hle; omega
    exact_mod_cast this
  by_cases h0 : ∃ i, eps i = 0 ∧ 0 < u i ∧
      2 ≤ 1 + 2 * (u i : ℤ) - (u ((finRotate k).symm i) : ℤ)
  · exact Or.inl h0
  have hpos : ∃ i, eps i = 1 ∧ 0 < u i ∧
      2 ≤ 1 + 2 * (u i : ℤ) - (u ((finRotate k).symm i) : ℤ) := by
    by_contra hp
    apply bad c eps (by simpa [tau] using heps) hQ
    · intro i hi
      exact h0 ⟨i, hi⟩
    · intro i hi
      exact hp ⟨i, hi⟩
  have hneg : ∃ j, eps j = -1 ∧ 0 < u j ∧
      2 ≤ 1 + 2 * (u j : ℤ) - (u ((finRotate k).symm j) : ℤ) := by
    let d : Fin k → Bool := fun a => !c a
    let ed : Fin k → ℤ := fun a => -eps a
    have hed : ∀ a, ed a = ((d a).toNat : ℤ) - ((d (tau a)).toNat : ℤ) := by
      intro a
      dsimp [ed, d]
      rw [heps a]
      cases hca : c a <;> cases hct : c (tau a) <;> simp [hca, hct]
    have hEd : (∑ a, (u a : ℤ) * ed a) = 0 := by
      calc
        (∑ a, (u a : ℤ) * ed a) = - (∑ a, (u a : ℤ) * eps a) := by
          simp [ed, Finset.sum_neg_distrib]
        _ = 0 := by rw [hQ]; simp
    by_contra hn
    exfalso
    apply bad d ed hed hEd
    · intro i hi
      apply h0
      refine ⟨i, ?_, hi.2.1, hi.2.2⟩
      simpa [ed] using hi.1
    · intro i hi
      apply hn
      refine ⟨i, ?_, hi.2.1, hi.2.2⟩
      have hsign : eps i = -1 := by
        have := hi.1
        simp [ed] at this
        omega
      exact hsign
  obtain ⟨i, hi0, hio, hiq⟩ := hpos
  obtain ⟨j, hj0, hjo, hjq⟩ := hneg
  exact Or.inr ⟨i, j, hi0, hj0, by intro hij; subst j; omega, hio, hjo, hiq, hjq⟩

/-- A zero-charge natural coefficient vector admits an atomic neutral carry path.

The packet at each edge is either one neutral carry or one opposite-charge pair;
this is an algebraic coefficient path and carries no geometric ordering claim. -/
theorem neutral_carry_path
    (k : ℕ) (c : Fin k → Bool) (s : Fin k → ℤ) (N : ℤ)
    (hsum : (∑ a, s a) = 0)
    (hstep : ∀ a, 2 * s a - s (finRotate k a) =
      N * (((c a).toNat : ℤ) - ((c (finRotate k a)).toNat : ℤ)))
    (m : Fin k → ℕ)
    (hphysical : ∀ a, 0 ≤ 1 + 2 * (m a : ℤ) - (m ((finRotate k).symm a) : ℤ))
    (hcharge : (∑ a, (m a : ℤ) *
      (((c a).toNat : ℤ) - ((c (finRotate k a)).toNat : ℤ))) = 0) :
    ∃ P : List (Fin k → ℕ),
      P.head? = some m ∧ P.getLast? = some 0 ∧
      List.IsChain
        (fun u v =>
          (∃ i, ((c i).toNat : ℤ) - ((c (finRotate k i)).toNat : ℤ) = 0 ∧
            0 < u i ∧
            2 ≤ 1 + 2 * (u i : ℤ) - (u ((finRotate k).symm i) : ℤ) ∧
            (∀ a, v a + (if a = i then 1 else 0) = u a) ∧
            (∑ a, v a + 1 = ∑ a, u a)) ∨
          (∃ i j,
            ((c i).toNat : ℤ) - ((c (finRotate k i)).toNat : ℤ) = 1 ∧
            ((c j).toNat : ℤ) - ((c (finRotate k j)).toNat : ℤ) = -1 ∧
            i ≠ j ∧ 0 < u i ∧ 0 < u j ∧
            2 ≤ 1 + 2 * (u i : ℤ) - (u ((finRotate k).symm i) : ℤ) ∧
            2 ≤ 1 + 2 * (u j : ℤ) - (u ((finRotate k).symm j) : ℤ) ∧
            (∀ a, v a + (if a = i then 1 else 0) + (if a = j then 1 else 0) = u a) ∧
            (∑ a, v a + 2 = ∑ a, u a))) P ∧
      (∀ u ∈ P,
        (∀ a, 0 ≤ 1 + 2 * (u a : ℤ) - (u ((finRotate k).symm a) : ℤ)) ∧
        (∑ a, (u a : ℤ) *
          (((c a).toNat : ℤ) - ((c (finRotate k a)).toNat : ℤ))) = 0 ∧
        (∑ a, (1 + 2 * (u a : ℤ) - (u ((finRotate k).symm a) : ℤ)) * s a) = 0) := by
  classical
  let tau := finRotate k
  let pred := tau.symm
  let eps : Fin k → ℤ := fun a => ((c a).toNat : ℤ) - ((c (tau a)).toNat : ℤ)
  let q : (Fin k → ℕ) → Fin k → ℤ := fun u a =>
    1 + 2 * (u a : ℤ) - (u (pred a) : ℤ)
  let Q : (Fin k → ℕ) → ℤ := fun u => ∑ a, (u a : ℤ) * eps a
  have hstep' : ∀ a, 2 * s a - s (tau a) = N * eps a := by
    intro a
    simpa [eps, tau] using hstep a
  have hcharge' : Q m = 0 := by simpa [Q, eps, tau] using hcharge
  have hphysical' : ∀ a, 0 ≤ q m a := by simpa [q, pred, tau] using hphysical
  have source_zero : ∀ (u : Fin k → ℕ), (∀ a, 0 ≤ q u a) → Q u = 0 →
      (∑ a, q u a * s a) = 0 := by
    intro u huq huQ
    have hcarry : ∀ a, ((q u a).toNat : ℤ) =
        (if a ∈ (Finset.univ : Finset (Fin k)) then (1 : ℤ) else 0) +
          2 * (u a : ℤ) - (u (pred a) : ℤ) := by
      intro a
      have hcast : ((q u a).toNat : ℤ) = q u a := Int.toNat_of_nonneg (huq a)
      rw [hcast]
      simp [q, pred]
    have hc := carry_charge (fun a => (q u a).toNat) u
      (Finset.univ : Finset (Fin k)) s eps N hcarry hstep'
    have hcast_sum : (∑ a, ((q u a).toNat : ℤ) * s a) = ∑ a, q u a * s a := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Int.toNat_of_nonneg (huq a)]
    rw [hcast_sum] at hc
    have hsum' : (∑ a ∈ (Finset.univ : Finset (Fin k)), s a) = 0 := by simpa using hsum
    simpa [Q, hsum', huQ] using hc
  have aux : ∀ L : ℕ, ∀ u : Fin k → ℕ, (∑ a, u a) = L →
      (∀ a, 0 ≤ q u a) → Q u = 0 →
      ∃ P : List (Fin k → ℕ),
        P.head? = some u ∧ P.getLast? = some 0 ∧
        List.IsChain
          (fun x y =>
            (∃ i, eps i = 0 ∧ 0 < x i ∧ 2 ≤ q x i ∧
              (∀ a, y a + (if a = i then 1 else 0) = x a) ∧
              (∑ a, y a + 1 = ∑ a, x a)) ∨
            (∃ i j, eps i = 1 ∧ eps j = -1 ∧ i ≠ j ∧ 0 < x i ∧ 0 < x j ∧
              2 ≤ q x i ∧ 2 ≤ q x j ∧
              (∀ a, y a + (if a = i then 1 else 0) + (if a = j then 1 else 0) = x a) ∧
              (∑ a, y a + 2 = ∑ a, x a))) P ∧
        (∀ x ∈ P, (∀ a, 0 ≤ q x a) ∧ Q x = 0 ∧ (∑ a, q x a * s a) = 0) := by
    intro L
    induction L using Nat.strong_induction_on with
    | h L ih =>
      intro u hu hq hQ
      by_cases hu0 : u = 0
      · subst u
        refine ⟨[0], by simp, by simp, by simp, ?_⟩
        intro x hx
        simp only [List.mem_singleton] at hx
        subst x
        exact ⟨hq, hQ, source_zero 0 hq hQ⟩
      · obtain hsel | hpair := neutral_carry_selector c u eps
          (by intro a; rfl) hQ hu0
        · obtain ⟨i, hi0, hiu, hiq⟩ := hsel
          let r : Fin k → ℕ := fun a => if a = i then 1 else 0
          let v : Fin k → ℕ := fun a => u a - r a
          have hrle : ∀ a, r a ≤ u a := by
            intro a
            by_cases ha : a = i
            · subst a
              have h1 : 1 ≤ u i := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hiu)
              simp [r, h1]
            · simp [r, ha]
          have hvadd : ∀ a, v a + r a = u a := by
            intro a
            exact Nat.sub_add_cancel (hrle a)
          have hsumv : (∑ a, v a) + 1 = L := by
            have hs := congrArg (fun f : Fin k → ℕ => ∑ a, f a) (funext hvadd)
            have hr : (∑ a, r a) = 1 := by simp [r]
            rw [Finset.sum_add_distrib, hr] at hs
            omega
          have hiq' : 2 ≤ q u i := by
            change 2 ≤ 1 + 2 * (u i : ℤ) - (u ((finRotate k).symm i) : ℤ)
            exact hiq
          have hqv : ∀ a, 0 ≤ q v a := by
            intro a
            have hqeq : q v a = q u a - 2 * (r a : ℤ) + (r (pred a) : ℤ) := by
              have hcast := congrArg (fun n : ℕ => (n : ℤ)) (hvadd a)
              dsimp [q, v]
              have hpredcast : (v (pred a) : ℤ) =
                  (u (pred a) : ℤ) - (r (pred a) : ℤ) := by
                have hp := congrArg (fun n : ℕ => (n : ℤ)) (hvadd (pred a))
                omega
              have : (v a : ℤ) = (u a : ℤ) - (r a : ℤ) := by omega
              rw [this, hpredcast]
              ring
            rw [hqeq]
            by_cases ha : a = i
            · subst a
              have : r i = 1 := by simp [r]
              rw [this]
              have hrp : 0 ≤ (r (pred i) : ℤ) := by positivity
              omega
            · have hra : r a = 0 := by simp [r, ha]
              rw [hra]
              have hqu := hq a
              have hrp : 0 ≤ (r (pred a) : ℤ) := by positivity
              omega
          have hrQ : (∑ a, (r a : ℤ) * eps a) = 0 := by simp [r, hi0]
          have hQv : Q v = 0 := by
            have hvQ : (∑ a, (v a : ℤ) * eps a) =
                (∑ a, (u a : ℤ) * eps a) - ∑ a, (r a : ℤ) * eps a := by
              rw [← Finset.sum_sub_distrib]
              apply Finset.sum_congr rfl
              intro a ha
              have hcast := congrArg (fun n : ℕ => (n : ℤ)) (hvadd a)
              have : (v a : ℤ) = (u a : ℤ) - (r a : ℤ) := by omega
              rw [this]
              ring
            simpa [Q, hvQ, hQ, hrQ]
          obtain ⟨P, hhead, hlast, hchain, hinv⟩ := ih (∑ a, v a) (by omega) v rfl hqv hQv
          refine ⟨u :: P, by simp, ?_, ?_, ?_⟩
          · cases P with
            | nil => simp at hhead
            | cons p ps => simpa using hlast
          · cases P with
            | nil => simp
            | cons p ps =>
              have hp : p = v := by
                simpa using hhead
              subst p
              simp only [List.isChain_cons_cons]
              refine ⟨?_, hchain⟩
              have hsumEdge : (∑ a, v a + 1 = ∑ a, u a) := by omega
              exact Or.inl ⟨i, hi0, hiu, hiq, (by intro a; simpa [r] using hvadd a), hsumEdge⟩
          · intro x hx
            simp only [List.mem_cons] at hx
            rcases hx with hx | hx
            · subst x
              exact ⟨hq, hQ, source_zero _ hq hQ⟩
            · exact hinv x hx
        · obtain ⟨i, j, hi1, hjm, hij, hiu, hju, hiq, hjq⟩ := hpair
          let r : Fin k → ℕ := fun a => (if a = i then 1 else 0) + (if a = j then 1 else 0)
          let v : Fin k → ℕ := fun a => u a - r a
          have hrle : ∀ a, r a ≤ u a := by
            intro a
            by_cases hai : a = i
            · subst a
              have h1 : 1 ≤ u i := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hiu)
              simp [r, hij, h1]
            · by_cases haj : a = j
              · subst a
                have h1 : 1 ≤ u j := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hju)
                have hji : j ≠ i := Ne.symm hij
                simp [r, hji, h1]
              · simp [r, hai, haj]
          have hvadd : ∀ a, v a + r a = u a := by
            intro a
            exact Nat.sub_add_cancel (hrle a)
          have hsumv : (∑ a, v a) + 2 = L := by
            have hs := congrArg (fun f : Fin k → ℕ => ∑ a, f a) (funext hvadd)
            have hr : (∑ a, r a) = 2 := by
              simp [r, Finset.sum_add_distrib, hij]
            rw [Finset.sum_add_distrib, hr] at hs
            omega
          have hiq' : 2 ≤ q u i := by
            change 2 ≤ 1 + 2 * (u i : ℤ) - (u ((finRotate k).symm i) : ℤ)
            exact hiq
          have hjq' : 2 ≤ q u j := by
            change 2 ≤ 1 + 2 * (u j : ℤ) - (u ((finRotate k).symm j) : ℤ)
            exact hjq
          have hqv : ∀ a, 0 ≤ q v a := by
            intro a
            have hqeq : q v a = q u a - 2 * (r a : ℤ) + (r (pred a) : ℤ) := by
              have hcast := congrArg (fun n : ℕ => (n : ℤ)) (hvadd a)
              dsimp [q, v]
              have hpredcast : (v (pred a) : ℤ) =
                  (u (pred a) : ℤ) - (r (pred a) : ℤ) := by
                have hp := congrArg (fun n : ℕ => (n : ℤ)) (hvadd (pred a))
                omega
              have : (v a : ℤ) = (u a : ℤ) - (r a : ℤ) := by omega
              rw [this, hpredcast]
              ring
            rw [hqeq]
            by_cases hai : a = i
            · subst a
              simp [r, hij]
              have hrp : 0 ≤ (r (pred i) : ℤ) := by positivity
              omega
            · by_cases haj : a = j
              · subst a
                simp [r, Ne.symm hij]
                have hrp : 0 ≤ (r (pred j) : ℤ) := by positivity
                omega
              · simp [r, hai, haj]
                have hqu := hq a
                have hrp : 0 ≤ (r (pred a) : ℤ) := by positivity
                omega
          have hrQ : (∑ a, (r a : ℤ) * eps a) = 0 := by
            simp only [r, Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
            simp_rw [add_mul]
            rw [Finset.sum_add_distrib]
            simp [hi1, hjm, hij]
          have hQv : Q v = 0 := by
            have hvQ : (∑ a, (v a : ℤ) * eps a) =
                (∑ a, (u a : ℤ) * eps a) - ∑ a, (r a : ℤ) * eps a := by
              rw [← Finset.sum_sub_distrib]
              apply Finset.sum_congr rfl
              intro a ha
              have hcast := congrArg (fun n : ℕ => (n : ℤ)) (hvadd a)
              have : (v a : ℤ) = (u a : ℤ) - (r a : ℤ) := by omega
              rw [this]
              ring
            simpa [Q, hvQ, hQ, hrQ]
          obtain ⟨P, hhead, hlast, hchain, hinv⟩ := ih (∑ a, v a) (by omega) v rfl hqv hQv
          refine ⟨u :: P, by simp, ?_, ?_, ?_⟩
          · cases P with
            | nil => simp at hhead
            | cons p ps => simpa using hlast
          · cases P with
            | nil => simp
            | cons p ps =>
              have hp : p = v := by
                simpa using hhead
              subst p
              simp only [List.isChain_cons_cons]
              refine ⟨?_, hchain⟩
              have hsumEdge : (∑ a, v a + 2 = ∑ a, u a) := by omega
              exact Or.inr ⟨i, j, hi1, hjm, hij, hiu, hju, hiq, hjq,
                (by intro a; simpa [r, Nat.add_assoc] using hvadd a), hsumEdge⟩
          · intro x hx
            simp only [List.mem_cons] at hx
            rcases hx with hx | hx
            · subst x
              exact ⟨hq, hQ, source_zero _ hq hQ⟩
            · exact hinv x hx
  obtain ⟨P, hhead, hlast, hchain, hinv⟩ := aux (∑ a, m a) m rfl hphysical' hcharge'
  refine ⟨P, hhead, hlast, ?_, ?_⟩
  · simpa [eps, q, tau, pred] using hchain
  · intro u hu
    obtain ⟨huq, huQ, hus⟩ := hinv u hu
    exact ⟨by simpa [q, pred, tau] using huq,
      by simpa [Q, eps, tau] using huQ,
      by simpa [q, pred, tau] using hus⟩

/-- A nonzero natural coefficient vector has one nonempty binary endpoint and one
natural carry vector. Their exact source charge controls unit relation length. -/
theorem cyclic_binary_normal_form
    (k : ℕ) (hk : 0 < k) (t : ℕ)
    (n : Fin k → ℕ) (hne : n ≠ 0) :
    ∃! z : Finset (Fin k) × (Fin k → ℕ),
      let A := z.1
      let m := z.2
      let N : ℕ := 2 ^ k - 1
      let s := actualSource k t
      let eps : Fin k → ℤ := fun i =>
        if modulus k < 4 * s i then 1
        else if 4 * s i < -modulus k then -1 else 0
      A.Nonempty ∧
      (∀ i : Fin k, (n i : ℤ) =
        (if i ∈ A then (1 : ℤ) else 0) +
          2 * (m i : ℤ) - (m ((finRotate k).symm i) : ℤ)) ∧
      (∑ i : Fin k, n i) = A.card + (∑ i : Fin k, m i) ∧
      (∑ i : Fin k, n i * 2 ^ i.val) =
        (∑ i ∈ A, 2 ^ i.val) + N * m ⟨k - 1, by omega⟩ ∧
      (∑ i : Fin k, (n i : ℤ) * s i) =
        (∑ i ∈ A, s i) + modulus k *
          (∑ i : Fin k, (m i : ℤ) * eps i) ∧
      ((∑ i : Fin k, (n i : ℤ) * s i) = 0 →
        N / Nat.gcd t N ∣ (∑ i ∈ A, 2 ^ i.val)) ∧
      (Nat.Coprime t N →
        (∑ i : Fin k, (n i : ℤ) * s i) = 0 →
        A = Finset.univ ∧
        (∑ i : Fin k, (m i : ℤ) * eps i) = 0 ∧
        (∑ i : Fin k, n i) = k + (∑ i : Fin k, m i) ∧
        k ≤ (∑ i : Fin k, n i) ∧
        ((∑ i : Fin k, n i) = k ↔ ∀ i : Fin k, n i = 1)) := by
  classical
  obtain ⟨A, hA, m, hm⟩ := carry_exists k n hne
  have hlen := carry_length n m A hm
  have hweight := carry_weight hk n m A hm
  obtain ⟨hN, hsum, hstep⟩ := source_cycle hk t
  let eps : Fin k → ℤ := fun i => if modulus k < 4 * actualSource k t i then 1
    else if 4 * actualSource k t i < -modulus k then -1 else 0
  have hcharge := carry_charge n m A (actualSource k t) eps (modulus k) hm hstep
  have hNnat : 0 < 2 ^ k - 1 := by have := Nat.one_lt_two_pow (ne_of_gt hk); omega
  have hd (hz : (∑ i, (n i : ℤ) * actualSource k t i) = 0) :
      (2 ^ k - 1) / Nat.gcd t (2 ^ k - 1) ∣ mask A := by
    apply quotient_dvd hNnat
    have he := coefficient_weight_dvd n hz
    rw [hweight, Nat.mul_add] at he
    have hmul : (2 ^ k - 1) ∣ t * ((2 ^ k - 1) * m ⟨k - 1, by omega⟩) :=
      dvd_mul_of_dvd_right (dvd_mul_right (2 ^ k - 1) _) t
    exact (Nat.dvd_add_iff_left hmul).mpr he
  refine ⟨(A, m), ?_, ?_⟩
  · refine ⟨hA, hm, hlen, hweight, hcharge, hd, ?_⟩
    intro hunit hz
    have hdiv := hd hz
    rw [hunit.gcd_eq_one, Nat.div_one] at hdiv
    have hmask : mask A = 2 ^ k - 1 :=
      le_antisymm (mask_bound A) (Nat.le_of_dvd (mask_pos hA) hdiv)
    have hfull : A = Finset.univ := mask_injective k (hmask.trans (mask_full k).symm)
    have hbalance : (∑ i, (m i : ℤ) * eps i) = 0 := by
      rw [hz, hfull, hsum, zero_add] at hcharge
      exact (mul_eq_zero.mp hcharge.symm).resolve_left (ne_of_gt hN)
    have hlength : (∑ i, n i) = k + ∑ i, m i := by simpa [hfull] using hlen
    refine ⟨hfull, hbalance, hlength, by omega, ?_⟩
    constructor
    · intro he
      have hmzero : ∑ i, m i = 0 := by omega
      have hall : ∀ i, m i = 0 := by
        intro i
        have hle : m i ≤ ∑ j, m j := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
        omega
      intro i
      have hi := hm i
      simp only [hfull, Finset.mem_univ, ite_true, hall, Nat.cast_zero, mul_zero,
        add_zero, sub_zero] at hi
      exact_mod_cast hi
    · intro hall
      simp [hall]
  · intro z hz
    obtain ⟨B, v⟩ := z
    have he := carry_pair_unique hk n B A v m hz.1 hA hz.2.1 hm
    exact Prod.ext he.1 he.2

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
