/- GID: D5/S3/Combinatorics/Circle/Orbit/TwoBitZeroSubsets
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/Orbit/TwoBitZeroSubsets
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Data.Nat.GCD.Basic]
   utility: none
   digest: Complement rotation classifies and counts physical two-bit integer-zero subsets. -/
module

public import D5.S3.Combinatorics.Circle.Orbit.ZeroSumSubsets
import all D5.S3.Combinatorics.Circle.Orbit.ZeroSumSubsets
public import Batteries.Tactic.OpenPrivate
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Nat.Prime.Basic

/-! # Integer-zero subsets of the labelled two-bit centered source -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

namespace D5.S3.Combinatorics.Circle.TwoBitZeroSubsets

open SourceWidth ZeroSumSubsets
open scoped BigOperators

open private mask_pos from D5.S3.Combinatorics.Circle.Orbit.ZeroSumSubsets
open D5.S3.Combinatorics.Circle.ZeroSumSubsets (mask_as_geom)

private theorem modulus_nat (r : ℕ) :
    modulus r = ((2 ^ r - 1 : ℕ) : ℤ) := by
  have hp : 1 ≤ (2 : ℕ) ^ r := Nat.one_le_two_pow
  simp only [modulus, Nat.cast_sub hp, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]

private theorem modulus_half {r : ℕ} (hr : 2 ≤ r) :
    0 < modulus r ∧ modulus r % 2 = 1 ∧
      modulus r / 2 = (2 : ℤ) ^ (r - 1) - 1 := by
  have hp : 0 < (2 : ℤ) ^ (r - 1) := by positivity
  have he : modulus r = 2 * (2 : ℤ) ^ (r - 1) - 1 := by
    have hpR := congrArg (fun n : ℕ => (2 : ℤ) ^ n)
      (show r = (r - 1) + 1 by omega)
    rw [pow_succ] at hpR
    rw [modulus, hpR]
    ring
  rw [he]
  omega

private theorem rotate_val {r a : ℕ} (hr : 0 < r) (ha : a < r) (i : Fin r) :
    (((finRotate r : Equiv.Perm (Fin r)) ^ a) i).val = (i.val + a) % r := by
  let : NeZero r := ⟨ne_of_gt hr⟩
  have he : (finRotate r : Fin r → Fin r)^[a] = finCycle (⟨a, ha⟩ : Fin r) :=
    (finCycle_eq_finRotate_iterate (k := (⟨a, ha⟩ : Fin r))).symm
  simp only [Equiv.Perm.coe_pow, he, finCycle_apply, Fin.val_add]

private theorem rotate_ne {r a : ℕ} (hr : 2 ≤ r) (ha : 0 < a) (har : a < r)
    (i : Fin r) : i ≠ ((finRotate r : Equiv.Perm (Fin r)) ^ a) i := by
  intro he
  have hv := congrArg Fin.val he
  rw [rotate_val (by omega) har] at hv
  have hi := i.isLt
  by_cases h : i.val + a < r
  · rw [Nat.mod_eq_of_lt h] at hv
    omega
  · have hmod : (i.val + a) % r = i.val + a - r := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [hmod] at hv
    omega

private theorem pow_rotate_mod {r a : ℕ} (hr : 2 ≤ r) (har : a < r) (i : Fin r) :
    (2 : ℤ) ^ (((finRotate r : Equiv.Perm (Fin r)) ^ a) i).val ≡
      (2 : ℤ) ^ a * 2 ^ i.val [ZMOD modulus r] := by
  have hi := i.isLt
  rw [rotate_val (by omega) har]
  by_cases h : i.val + a < r
  · rw [Nat.mod_eq_of_lt h, pow_add]
    rw [mul_comm]
  · have hmod : (i.val + a) % r = i.val + a - r := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [hmod]
    apply Int.modEq_iff_dvd.mpr
    refine ⟨(2 : ℤ) ^ (i.val + a - r), ?_⟩
    have hexp : a + i.val = (i.val + a - r) + r := by omega
    rw [← pow_add, hexp, pow_add, modulus]
    ring

private theorem mask_compl_add {r : ℕ} (A : Finset (Fin r)) :
    mask A + mask Aᶜ = 2 ^ r - 1 := by
  classical
  have he := Finset.sum_add_sum_compl A (fun i : Fin r => (2 : ℕ) ^ i.val)
  change mask A + mask Aᶜ = mask (Finset.univ : Finset (Fin r)) at he
  exact he.trans (mask_full r)

private theorem mask_lt_of_ne_univ {r : ℕ} (A : Finset (Fin r))
    (hA : A ≠ Finset.univ) : mask A < 2 ^ r - 1 := by
  have hb := mask_bound A
  have hne : mask A ≠ 2 ^ r - 1 := by
    intro he
    exact hA (mask_injective r (he.trans (mask_full r).symm))
  omega

private theorem image_proper {r : ℕ} (ρ : Equiv.Perm (Fin r))
    (A : Finset (Fin r)) (hA : A ≠ Finset.univ) : A.image ρ ≠ Finset.univ := by
  classical
  intro he
  apply hA
  apply Finset.eq_univ_of_forall
  intro i
  have hi : ρ i ∈ A.image ρ := by rw [he]; exact Finset.mem_univ _
  obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp hi
  exact ρ.injective hji ▸ hj

private theorem mask_image_cast {r : ℕ} (ρ : Equiv.Perm (Fin r))
    (A : Finset (Fin r)) :
    (mask (A.image ρ) : ℤ) = ∑ i ∈ A, (2 : ℤ) ^ (ρ i).val := by
  classical
  simp only [mask, Nat.cast_sum, Nat.cast_pow, Nat.cast_ofNat]
  rw [Finset.sum_image]
  exact fun _ _ _ _ h => ρ.injective h

private theorem pair_centered {r : ℕ} (hr : 2 ≤ r) (i j : Fin r) (hij : i ≠ j) :
    centered (modulus r) ((2 : ℤ) ^ i.val + 2 ^ j.val) =
      (2 : ℤ) ^ i.val + 2 ^ j.val - modulus r *
        ((if i.val = r - 1 then (1 : ℤ) else 0) +
          (if j.val = r - 1 then (1 : ℤ) else 0)) := by
  classical
  let T : Finset (Fin r) := {i, j}
  let t : Fin r := ⟨r - 1, by omega⟩
  have hbit : (mask T : ℤ) = (2 : ℤ) ^ i.val + 2 ^ j.val := by
    simp [mask, T, hij]
  have hit : i.val = r - 1 ↔ i = t := by
    constructor
    · intro he; exact Fin.ext he
    · rintro rfl; rfl
  have hjt : j.val = r - 1 ↔ j = t := by
    constructor
    · intro he; exact Fin.ext he
    · rintro rfl; rfl
  have hind : ((if i.val = r - 1 then (1 : ℤ) else 0) +
      (if j.val = r - 1 then (1 : ℤ) else 0)) =
      if t ∈ T then (1 : ℤ) else 0 := by
    simp only [hit, hjt]
    by_cases hi : i = t <;> by_cases hj : j = t <;> simp_all [T, eq_comm]
  rw [← hbit, hind]
  obtain ⟨hN, hodd, hhalf⟩ := modulus_half hr
  apply centered_unique hN hodd (centered_bounds hN hodd _) ?_ ?_
  · have hb : (mask T : ℤ) ≤ modulus r := by
      rw [modulus_nat]
      exact_mod_cast mask_bound T
    have hp : 0 < (2 : ℤ) ^ (r - 1) := by positivity
    by_cases ht : t ∈ T
    · rw [ite_eq_left ht]
      have hlo : (2 : ℤ) ^ (r - 1) ≤ (mask T : ℤ) := by
        have hh := Finset.single_le_sum (f := fun p : Fin r => (2 : ℕ) ^ p.val)
          (fun _ _ => Nat.zero_le _) ht
        exact_mod_cast hh
      have he : modulus r = 2 * (2 : ℤ) ^ (r - 1) - 1 := by
        have hh := Int.emod_add_mul_ediv (modulus r) 2
        omega
      rw [hhalf]
      constructor <;> nlinarith
    · rw [ite_eq_right ht, mul_zero, sub_zero, hhalf]
      have hlow : mask T < (2 : ℕ) ^ (r - 1) := by
        rw [mask_as_geom]
        apply Nat.geomSum_lt (by decide)
        intro n hn
        obtain ⟨p, hpT, rfl⟩ := Finset.mem_image.mp hn
        have hne : p.val ≠ r - 1 := by
          intro he
          have hpt : p = t := Fin.ext he
          exact ht (hpt ▸ hpT)
        have := p.isLt
        omega
      have hlowI : (mask T : ℤ) < (2 : ℤ) ^ (r - 1) := by exact_mod_cast hlow
      have hnonneg : 0 ≤ (mask T : ℤ) := by positivity
      constructor <;> omega
  · rw [centered_mod]
    exact (Int.modEq_iff_dvd.mpr (by
      refine ⟨-(if t ∈ T then (1 : ℤ) else 0), ?_⟩
      ring) : (mask T : ℤ) ≡
        (mask T : ℤ) - modulus r * (if t ∈ T then (1 : ℤ) else 0)
          [ZMOD modulus r])

private theorem actual_two_bit {r a : ℕ} (hr : 2 ≤ r) (ha : 0 < a) (har : a < r)
    (i : Fin r) :
    actualSource r (1 + 2 ^ a) i =
      (2 : ℤ) ^ i.val + 2 ^ (((finRotate r : Equiv.Perm (Fin r)) ^ a) i).val -
        modulus r * ((if i.val = r - 1 then (1 : ℤ) else 0) +
          (if (((finRotate r : Equiv.Perm (Fin r)) ^ a) i).val = r - 1
            then (1 : ℤ) else 0)) := by
  rw [actualSource]
  have hc : ((2 : ℤ) ^ i.val * ((1 + 2 ^ a : ℕ) : ℤ)) ≡
      (2 : ℤ) ^ i.val + 2 ^ (((finRotate r : Equiv.Perm (Fin r)) ^ a) i).val
        [ZMOD modulus r] := by
    have h := (Int.ModEq.refl (n := modulus r) ((2 : ℤ) ^ i.val)).add
      (pow_rotate_mod hr har i).symm
    convert h using 1
    push_cast
    ring
  rw [centered_congr hc]
  exact pair_centered hr i _ (rotate_ne hr ha har i)

private theorem actual_sum_formula {r a : ℕ} (hr : 2 ≤ r) (ha : 0 < a) (har : a < r)
    (A : Finset (Fin r)) :
    let ρ := (finRotate r : Equiv.Perm (Fin r)) ^ a
    let t : Fin r := ⟨r - 1, by omega⟩
    (∑ i ∈ A, actualSource r (1 + 2 ^ a) i) =
      (mask A : ℤ) + mask (A.image ρ) - modulus r *
        ((if t ∈ A then (1 : ℤ) else 0) +
          (if t ∈ A.image ρ then (1 : ℤ) else 0)) := by
  classical
  dsimp only
  let ρ := (finRotate r : Equiv.Perm (Fin r)) ^ a
  let t : Fin r := ⟨r - 1, by omega⟩
  have hval (i : Fin r) : i.val = r - 1 ↔ i = t := by
    constructor
    · intro he; exact Fin.ext he
    · rintro rfl; rfl
  have hiA : (∑ i ∈ A, if i.val = r - 1 then (1 : ℤ) else 0) =
      if t ∈ A then (1 : ℤ) else 0 := by simp [hval]
  have hiB : (∑ i ∈ A, if (ρ i).val = r - 1 then (1 : ℤ) else 0) =
      if t ∈ A.image ρ then (1 : ℤ) else 0 := by
    have he : (∑ j ∈ A.image ρ, if j.val = r - 1 then (1 : ℤ) else 0) =
        ∑ i ∈ A, if (ρ i).val = r - 1 then (1 : ℤ) else 0 := by
      rw [Finset.sum_image]
      exact fun _ _ _ _ h => ρ.injective h
    rw [← he]
    simp [hval]
  simp_rw [actual_two_bit hr ha har]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_add_distrib, hiA, hiB]
  rw [mask_image_cast ρ A]
  simp only [mask, Nat.cast_sum, Nat.cast_pow, Nat.cast_ofNat]
  rfl

private theorem masks_eq_modulus {r : ℕ} (hr : 2 ≤ r) (ρ : Equiv.Perm (Fin r))
    (A : Finset (Fin r)) (hne : A.Nonempty) (hproper : A ≠ Finset.univ)
    (hd : modulus r ∣ (mask A : ℤ) + mask (A.image ρ)) :
    (mask A : ℤ) + mask (A.image ρ) = modulus r := by
  have hneB : (A.image ρ).Nonempty := hne.image _
  have hpA : (0 : ℤ) < mask A := by exact_mod_cast mask_pos hne
  have hpB : (0 : ℤ) < mask (A.image ρ) := by exact_mod_cast mask_pos hneB
  have hbA : (mask A : ℤ) < modulus r := by
    rw [modulus_nat]; exact_mod_cast mask_lt_of_ne_univ A hproper
  have hbB : (mask (A.image ρ) : ℤ) < modulus r := by
    rw [modulus_nat]; exact_mod_cast mask_lt_of_ne_univ _ (image_proper ρ A hproper)
  have hN := (modulus_half hr).1
  obtain ⟨q, hq⟩ := hd
  have hqpos : 0 < q := by nlinarith
  have hqlt : q < 2 := by nlinarith
  have hqone : q = 1 := by omega
  rw [hqone, mul_one] at hq
  exact hq

private theorem image_compl_of_masks {r : ℕ} (ρ : Equiv.Perm (Fin r))
    (A : Finset (Fin r))
    (he : (mask A : ℤ) + mask (A.image ρ) = modulus r) : A.image ρ = Aᶜ := by
  have hc := mask_compl_add A
  have hcI : (mask A : ℤ) + mask Aᶜ = modulus r := by
    rw [modulus_nat]; exact_mod_cast hc
  apply mask_injective r
  exact_mod_cast (show (mask (A.image ρ) : ℤ) = mask Aᶜ by omega)

/-- The exact integer zero subsets of the actual two-bit source are precisely the
empty/full subsets and the physical subsets whose cyclic translate is their complement. -/
theorem actual_zero_iff (r a : ℕ) (hr : 2 ≤ r) (ha : 0 < a) (har : a < r)
    (A : Finset (Fin r)) :
    (∑ i ∈ A, SourceWidth.actualSource r (1 + 2 ^ a) i) = 0 ↔
      A = ∅ ∨ A = Finset.univ ∨
        A.image ((finRotate r : Equiv.Perm (Fin r)) ^ a) = Aᶜ := by
  classical
  let ρ := (finRotate r : Equiv.Perm (Fin r)) ^ a
  let t : Fin r := ⟨r - 1, by omega⟩
  have hf := actual_sum_formula hr ha har A
  change (∑ i ∈ A, actualSource r (1 + 2 ^ a) i) =
    (mask A : ℤ) + mask (A.image ρ) - modulus r *
      ((if t ∈ A then (1 : ℤ) else 0) + (if t ∈ A.image ρ then (1 : ℤ) else 0)) at hf
  constructor
  · intro hz
    by_cases he : A = ∅
    · exact Or.inl he
    by_cases hu : A = Finset.univ
    · exact Or.inr (Or.inl hu)
    refine Or.inr (Or.inr ?_)
    apply image_compl_of_masks ρ A
    apply masks_eq_modulus hr ρ A (Finset.nonempty_iff_ne_empty.mpr he) hu
    refine ⟨(if t ∈ A then (1 : ℤ) else 0) + (if t ∈ A.image ρ then 1 else 0), ?_⟩
    omega
  · rintro (rfl | rfl | he)
    · simp
    · simpa using (source_cycle (by omega : 0 < r) (1 + 2 ^ a)).2.1
    · have hm : (mask A : ℤ) + mask (A.image ρ) = modulus r := by
        change A.image ρ = Aᶜ at he
        rw [he, modulus_nat]
        exact_mod_cast mask_compl_add A
      have ht : (if t ∈ A then (1 : ℤ) else 0) +
          (if t ∈ A.image ρ then (1 : ℤ) else 0) = 1 := by
        change A.image ρ = Aᶜ at he
        rw [he]
        by_cases h : t ∈ A <;> simp [h]
      rw [hf, hm, ht, mul_one, sub_self]

private theorem rotate_mask_dvd {r a : ℕ} (hr : 2 ≤ r) (har : a < r)
    (A : Finset (Fin r)) :
    modulus r ∣ (((1 + 2 ^ a) * mask A : ℕ) : ℤ) -
      ((mask A : ℤ) + mask (A.image ((finRotate r : Equiv.Perm (Fin r)) ^ a))) := by
  classical
  have hd : modulus r ∣ ∑ i ∈ A,
      ((2 : ℤ) ^ a * 2 ^ i.val -
        2 ^ (((finRotate r : Equiv.Perm (Fin r)) ^ a) i).val) := by
    apply Finset.dvd_sum
    intro i hi
    exact Int.modEq_iff_dvd.mp (pow_rotate_mod hr har i)
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← mask_image_cast ((finRotate r : Equiv.Perm (Fin r)) ^ a) A] at hd
  convert hd using 1
  simp only [mask, Nat.cast_sum, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
    Nat.cast_pow, Nat.cast_ofNat]
  ring

/-- For two-bit sources modular zero is sufficient for exact integer zero, on the
entire parameter range; no physical ordering certificate is assumed. -/
theorem actual_zero_iff_dvd (r a : ℕ) (hr : 2 ≤ r) (ha : 0 < a) (har : a < r)
    (A : Finset (Fin r)) :
    (∑ i ∈ A, SourceWidth.actualSource r (1 + 2 ^ a) i) = 0 ↔
      (2 ^ r - 1) ∣ (1 + 2 ^ a) * ZeroSumSubsets.mask A := by
  classical
  constructor
  · exact zero_mask_dvd A
  · intro hd
    by_cases he : A = ∅
    · subst A; simp
    by_cases hu : A = Finset.univ
    · subst A
      simpa using (source_cycle (by omega : 0 < r) (1 + 2 ^ a)).2.1
    apply (actual_zero_iff r a hr ha har A).mpr
    refine Or.inr (Or.inr ?_)
    apply image_compl_of_masks
    apply masks_eq_modulus hr _ A (Finset.nonempty_iff_ne_empty.mpr he) hu
    have hdI : modulus r ∣ (((1 + 2 ^ a) * mask A : ℕ) : ℤ) := by
      rw [modulus_nat]; exact_mod_cast hd
    have hs := dvd_sub hdI (rotate_mask_dvd hr har A)
    convert hs using 1
    ring

/-- The exact divisibility parameter is the modulus divided by the actual gcd. -/
private theorem actual_zero_iff_reduced_dvd (r a : ℕ) (hr : 2 ≤ r) (ha : 0 < a)
    (har : a < r) (A : Finset (Fin r)) :
    (∑ i ∈ A, SourceWidth.actualSource r (1 + 2 ^ a) i) = 0 ↔
      (2 ^ r - 1) / Nat.gcd (1 + 2 ^ a) (2 ^ r - 1) ∣ ZeroSumSubsets.mask A := by
  rw [actual_zero_iff_dvd r a hr ha har A]
  have hN : 0 < 2 ^ r - 1 := by
    have hp := Nat.one_lt_two_pow (show r ≠ 0 by omega)
    omega
  constructor
  · exact quotient_dvd hN
  · intro hd
    let g := Nat.gcd (1 + 2 ^ a) (2 ^ r - 1)
    change (2 ^ r - 1) / g ∣ mask A at hd
    have hNg : g ∣ 2 ^ r - 1 := Nat.gcd_dvd_right _ _
    have hqg : g ∣ 1 + 2 ^ a := Nat.gcd_dvd_left _ _
    obtain ⟨m, hm⟩ := hd
    obtain ⟨q, hq⟩ := hqg
    refine ⟨q * m, ?_⟩
    rw [hm, hq]
    have hmul : g * ((2 ^ r - 1) / g) = 2 ^ r - 1 := Nat.mul_div_cancel' hNg
    change g * q * ((2 ^ r - 1) / g * m) = (2 ^ r - 1) * (q * m)
    calc
      g * q * ((2 ^ r - 1) / g * m) =
          (g * ((2 ^ r - 1) / g)) * (q * m) := by ring
      _ = (2 ^ r - 1) * (q * m) := by rw [hmul]

/- The remaining helpers are consumed by the single exact-count result below.
   They connect the classification to the binary-mask bijection and gcd formula. -/

private theorem square_sub_one_factor {x : ℕ} (hx : 1 ≤ x) :
    x ^ 2 - 1 = (x - 1) * (x + 1) := by
  have hs : x - 1 + 1 = x := Nat.sub_add_cancel hx
  have hp : 1 ≤ x ^ 2 := by nlinarith
  have ht : x ^ 2 - 1 + 1 = x ^ 2 := Nat.sub_add_cancel hp
  nlinarith

/-- Surjectivity uses the already proved mask injection and the two equal finite
cardinalities. In particular both endpoints 0 and 2^r-1 remain represented. -/
private theorem mask_surjective (r : ℕ) (n : ℕ) (hn : n < 2 ^ r) :
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

/-- The actual physical-zero bridge is used in both directions of the counting
bijection; modular zero alone is not substituted for integer zero. -/
private theorem actual_zero_card_gcd (r a : ℕ) (hr : 2 ≤ r)
    (ha : 0 < a) (har : a < r) :
    (Finset.univ.filter (fun A : Finset (Fin r) =>
      (∑ i ∈ A, SourceWidth.actualSource r (1 + 2 ^ a) i) = 0)).card =
      Nat.gcd (1 + 2 ^ a) (2 ^ r - 1) + 1 := by
  classical
  let N := 2 ^ r - 1
  let d := Nat.gcd (1 + 2 ^ a) N
  let Q := N / d
  let S := Finset.univ.filter (fun A : Finset (Fin r) =>
    (∑ i ∈ A, SourceWidth.actualSource r (1 + 2 ^ a) i) = 0)
  have hN : 0 < N := by
    have hp := Nat.one_lt_two_pow (show r ≠ 0 by omega)
    dsimp [N]
    omega
  have hQ : 0 < Q := Nat.div_gcd_pos_of_pos_right (1 + 2 ^ a) hN
  have hQd : Q * d = N := Nat.div_mul_cancel (Nat.gcd_dvd_right (1 + 2 ^ a) N)
  have hd (A : Finset (Fin r)) (hA : A ∈ S) : Q ∣ mask A := by
    exact (actual_zero_iff_reduced_dvd r a hr ha har A).mp
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
        apply (actual_zero_iff_reduced_dvd r a hr ha har A).mpr
        change Q ∣ mask A
        rw [hmask]
        exact ⟨n, rfl⟩
      refine ⟨A, hA, ?_⟩
      change mask A / Q = n
      rw [hmask, Nat.mul_div_cancel_left n hQ]
  simpa only [S, Finset.card_range] using hcount

/-- This arithmetic proof does not assume a cycle-count formula. It derives the
same parity obstruction using the gcd of the two exponent periods. -/
private theorem binary_gcd (r a : ℕ) (hr : 0 < r) (ha : 0 < a) :
    Nat.gcd (1 + 2 ^ a) (2 ^ r - 1) =
      if Even (r / Nat.gcd a r) then 2 ^ (Nat.gcd a r) + 1 else 1 := by
  let g := Nat.gcd a r
  let u := a / g
  let v := r / g
  let d := Nat.gcd (1 + 2 ^ a) (2 ^ r - 1)
  have hg : 0 < g := Nat.gcd_pos_of_pos_right a hr
  have hga : g ∣ a := Nat.gcd_dvd_left a r
  have hgr : g ∣ r := Nat.gcd_dvd_right a r
  have hau : g * u = a := Nat.mul_div_cancel' hga
  have hrv : g * v = r := Nat.mul_div_cancel' hgr
  have hcop : Nat.Coprime u v := Nat.coprime_div_gcd_div_gcd hg
  have hodd : Odd (1 + 2 ^ a) := by
    have hp : (2 : ℕ) ^ a = 2 ^ (a - 1) * 2 := by
      rw [← pow_succ]
      congr 1
      omega
    refine ⟨2 ^ (a - 1), ?_⟩
    omega
  have hdplus : d ∣ 1 + 2 ^ a := Nat.gcd_dvd_left _ _
  have hdminus : d ∣ 2 ^ r - 1 := Nat.gcd_dvd_right _ _
  have hsub : 2 ^ g - 1 ∣ 2 ^ a - 1 :=
    Nat.pow_sub_one_dvd_pow_sub_one 2 hga
  have hc : Nat.Coprime d (2 ^ g - 1) := by
    let c := Nat.gcd d (2 ^ g - 1)
    have hcplus : c ∣ 1 + 2 ^ a := (Nat.gcd_dvd_left _ _).trans hdplus
    have hcminus : c ∣ 2 ^ a - 1 := (Nat.gcd_dvd_right _ _).trans hsub
    have hp : 1 ≤ (2 : ℕ) ^ a := Nat.one_le_two_pow
    have hci1 : (c : ℤ) ∣ (1 : ℤ) + (2 : ℤ) ^ a := by
      exact_mod_cast hcplus
    have hci2 : (c : ℤ) ∣ (2 : ℤ) ^ a - 1 := by
      have hcast : (c : ℤ) ∣ ((2 ^ a - 1 : ℕ) : ℤ) := by
        exact_mod_cast hcminus
      simpa only [Nat.cast_sub hp, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
        using hcast
    have hci : (c : ℤ) ∣ (2 : ℤ) := by
      convert dvd_sub hci1 hci2 using 1
      ring
    have hc2 : c ∣ 2 := by exact_mod_cast hci
    have hc1 : c = 1 := Nat.eq_one_of_dvd_coprimes
      (Nat.coprime_two_left.mpr hodd) hc2 hcplus
    exact hc1
  have hdouble : d ∣ 2 ^ (2 * a) - 1 := by
    have hf : 1 + 2 ^ a ∣ 2 ^ (2 * a) - 1 := by
      refine ⟨2 ^ a - 1, ?_⟩
      rw [show 2 * a = a * 2 by omega, pow_mul,
        square_sub_one_factor Nat.one_le_two_pow]
      ring
    exact hdplus.trans hf
  have hdg : d ∣ 2 ^ Nat.gcd (2 * a) r - 1 := by
    rw [← Nat.pow_sub_one_gcd_pow_sub_one]
    exact Nat.dvd_gcd hdouble hdminus
  have hperiod : Nat.gcd (2 * a) r = g * Nat.gcd 2 v := by
    calc
      Nat.gcd (2 * a) r = Nat.gcd (g * (u * 2)) (g * v) := by
        congr 1 <;> nlinarith [hau, hrv]
      _ = g * Nat.gcd (u * 2) v := by rw [Nat.gcd_mul_left]
      _ = g * Nat.gcd 2 v := by
        rw [Nat.Coprime.gcd_mul_left_cancel 2 hcop]
  change d = if Even v then 2 ^ g + 1 else 1
  by_cases hv : Even v
  · rw [ite_eq_left hv]
    have h2v : 2 ∣ v := even_iff_two_dvd.mp hv
    have hg2 : Nat.gcd 2 v = 2 := Nat.gcd_eq_left_iff_dvd.mpr h2v
    have hdf : d ∣ (2 ^ g - 1) * (2 ^ g + 1) := by
      rw [hperiod, hg2, pow_mul,
        square_sub_one_factor Nat.one_le_two_pow] at hdg
      exact hdg
    have hdright : d ∣ 2 ^ g + 1 := hc.dvd_mul_left.mp hdf
    have hu : Odd u := Nat.coprime_two_right.mp
      (Nat.Coprime.of_dvd_right h2v hcop)
    have hrighta : 2 ^ g + 1 ∣ 1 + 2 ^ a := by
      have h := hu.nat_add_dvd_pow_add_pow (2 ^ g) 1
      rw [one_pow, ← pow_mul, hau] at h
      simpa only [Nat.add_comm 1] using h
    have htwog : 2 * g ∣ r := by
      obtain ⟨k, hk⟩ := h2v
      refine ⟨k, ?_⟩
      nlinarith [hrv]
    have hright2g : 2 ^ g + 1 ∣ 2 ^ (2 * g) - 1 := by
      refine ⟨2 ^ g - 1, ?_⟩
      rw [show 2 * g = g * 2 by omega, pow_mul,
        square_sub_one_factor Nat.one_le_two_pow]
      ring
    have hrightr : 2 ^ g + 1 ∣ 2 ^ r - 1 := hright2g.trans
      (Nat.pow_sub_one_dvd_pow_sub_one 2 htwog)
    exact Nat.dvd_antisymm hdright (Nat.dvd_gcd hrighta hrightr)
  · rw [ite_eq_right hv]
    have hg1 : Nat.gcd 2 v = 1 :=
      (Nat.coprime_two_left.mpr (Nat.not_even_iff_odd.mp hv)).gcd_eq_one
    rw [hperiod, hg1, mul_one] at hdg
    exact Nat.eq_one_of_dvd_coprimes hc dvd_rfl hdg

/-- Exact count of all physical integer-zero subsets of every actual two-bit
source, including r=2,a=1 and the empty and full subsets. The classification
`actual_zero_iff` is consumed through `actual_zero_iff_dvd` and the reduced
physical-zero bridge on both sides of the binary-mask bijection. -/
theorem actual_zero_subsets_card (r a : ℕ) (hr : 2 ≤ r) (ha : 0 < a) (har : a < r) :
    (Finset.univ.filter (fun A : Finset (Fin r) =>
      (∑ i ∈ A, SourceWidth.actualSource r (1 + 2 ^ a) i) = 0)).card =
      if Even (r / Nat.gcd a r) then 2 ^ (Nat.gcd a r) + 2 else 2 := by
  rw [actual_zero_card_gcd r a hr ha har, binary_gcd r a (by omega) ha]
  split_ifs <;> omega

end D5.S3.Combinatorics.Circle.TwoBitZeroSubsets
