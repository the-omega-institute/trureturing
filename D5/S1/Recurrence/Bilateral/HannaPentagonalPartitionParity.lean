/- GID: D5/S1/Recurrence/Bilateral/HannaPentagonalPartitionParity
   generality: I
   mirror-B: D5/B/S1/Recurrence/Bilateral/HannaPentagonalPartitionParity
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: The literal Hanna pentagonal unit equation and ordinary partition parity. -/

import Mathlib.Combinatorics.Enumerative.Pentagonal.PowerSeries
import Mathlib.Combinatorics.Enumerative.Partition.Glaisher
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Topology.Instances.ZMod

open PowerSeries
open scoped PowerSeries.WithPiTopology
namespace D5.S1.Recurrence.Bilateral.HannaPentagonalPartitionParity

variable {R : Type*} [CommRing R]

/-- The original nonnegative integer exponent, with no rounding change. -/
def exponent (k : ℤ) : ℕ := pentagonal (-k)

/-- Every positive and negative power is taken in the unit group. -/
noncomputable def term (A : (PowerSeries R)ˣ) (k : ℤ) : PowerSeries R :=
  X ^ exponent k * ((↑(A ^ (3 * k)) : PowerSeries R) - (↑(A ^ (-(3 * k + 1))) : PowerSeries R))

noncomputable def bilateral (A : (PowerSeries R)ˣ) : PowerSeries R :=
  mk fun N => ∑ k ∈ Finset.Icc (-(N : ℤ)) N, coeff N (term A k)

/-- This is the literal coefficientwise original equation. -/
def Original (A : (PowerSeries R)ˣ) : Prop := bilateral A = 2 * X

private theorem exponent_exact (k : ℤ) :
    (exponent k : ℤ) = k * (3 * k + 1) / 2 ∧
    2 * (exponent k : ℤ) = k * (3 * k + 1) := by
  constructor
  · rw [exponent, natCast_pentagonal]; congr 1; ring
  · exact two_mul_natCast_pentagonal_neg k

private theorem exponent_bound (k : ℤ) : k.natAbs ≤ exponent k := by
  have he := (exponent_exact k).2
  have ha := Int.natCast_natAbs k
  rcases le_or_gt 0 k with hk | hk
  · rw [abs_of_nonneg hk] at ha
    have : (k.natAbs : ℤ) ≤ (exponent k : ℤ) := by nlinarith
    exact_mod_cast this
  · rw [abs_of_neg hk] at ha
    have : (k.natAbs : ℤ) ≤ (exponent k : ℤ) := by
      have : k ≤ -1 := by omega
      nlinarith
    exact_mod_cast this

private theorem outside_zero (A : (PowerSeries R)ˣ) (N : ℕ) (k : ℤ)
    (hk : k ∉ Finset.Icc (-(N : ℤ)) N) : coeff N (term A k) = 0 := by
  unfold term
  apply X_pow_dvd_iff.mp (dvd_mul_right (X ^ exponent k) _) N
  have hb := exponent_bound k
  simp only [Finset.mem_Icc] at hk
  omega

private theorem window (A : (PowerSeries R)ˣ) (N K : ℕ) (hNK : N ≤ K) :
    coeff N (bilateral A) =
      ∑ k ∈ Finset.Icc (-(K : ℤ)) K, coeff N (term A k) := by
  simp only [bilateral, coeff_mk]
  apply Finset.sum_subset
  · intro k hk; simp only [Finset.mem_Icc] at hk ⊢; omega
  · intro k hk hn; exact outside_zero A N k hn

private theorem term_zero (A : (PowerSeries R)ˣ) : term A 0 = 1 - ↑A⁻¹ := by
  simp [term, exponent, pentagonal]

private theorem bilateral_constant (A : (PowerSeries R)ˣ) :
    constantCoeff (bilateral A) = 1 - constantCoeff (↑A⁻¹ : PowerSeries R) := by
  rw [← coeff_zero_eq_constantCoeff, window A 0 0 le_rfl]
  simp [term_zero, coeff_zero_eq_constantCoeff]

private theorem original_constant (A : (PowerSeries R)ˣ) (h : Original A) :
    constantCoeff (A : PowerSeries R) = 1 := by
  have hc := congrArg constantCoeff h
  change constantCoeff (bilateral A) = constantCoeff (2 * X) at hc
  rw [bilateral_constant] at hc
  have hi : constantCoeff (↑A⁻¹ : PowerSeries R) = 1 := by
    have hz : 1 - constantCoeff (↑A⁻¹ : PowerSeries R) = 0 := by simpa using hc
    exact (sub_eq_zero.mp hz).symm
  have hu : constantCoeff (A : PowerSeries R) * constantCoeff (↑A⁻¹ : PowerSeries R) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  simpa only [hi, mul_one] using hu

private noncomputable def nonzeroSum (A : (PowerSeries R)ˣ) : PowerSeries R :=
  mk fun N => ∑ k ∈ (Finset.Icc (-(N : ℤ)) N).erase 0, coeff N (term A k)

private theorem nonzero_constant (A : (PowerSeries R)ˣ) :
    constantCoeff (nonzeroSum A) = 0 := by
  rw [← coeff_zero_eq_constantCoeff]
  simp [nonzeroSum]

private theorem bilateral_split (A : (PowerSeries R)ˣ) :
    bilateral A = 1 - ↑A⁻¹ + nonzeroSum A := by
  ext N
  simp only [bilateral, nonzeroSum, map_add, coeff_mk]
  rw [← Finset.add_sum_erase (Finset.Icc (-(N : ℤ)) N)
    (fun k => coeff N (term A k)) (a := 0) (by simp), term_zero]

private noncomputable def denominator (A : (PowerSeries R)ˣ) : PowerSeries R :=
  1 - 2 * X + nonzeroSum A

private theorem denominator_constant (A : (PowerSeries R)ˣ) :
    constantCoeff (denominator A) = 1 := by simp [denominator, nonzero_constant]

private noncomputable def step (A : (PowerSeries R)ˣ) : (PowerSeries R)ˣ :=
  ⟨invOfUnit (denominator A) 1, denominator A,
    invOfUnit_mul _ 1 (denominator_constant A),
    mul_invOfUnit _ 1 (denominator_constant A)⟩

private def Agree (d : ℕ) (A B : (PowerSeries R)ˣ) : Prop :=
  (X : PowerSeries R) ^ d ∣ (A : PowerSeries R) - B

private theorem agree_coeff {d : ℕ} {A B : (PowerSeries R)ˣ}
    (h : Agree d A B) (N : ℕ) (hN : N < d) : coeff N (A : PowerSeries R) = coeff N B := by
  have := X_pow_dvd_iff.mp h N hN
  simpa only [map_sub, sub_eq_zero] using this

private theorem term_agree {d : ℕ} {A B : (PowerSeries R)ˣ}
    (h : Agree d A B) (k : ℤ) (hk : k ≠ 0) :
    (X : PowerSeries R) ^ (d + 1) ∣ term A k - term B k := by
  let I : Ideal (PowerSeries R) := Ideal.span {X ^ d}
  let q := Ideal.Quotient.mk I
  have hab : Units.map q.toMonoidHom A = Units.map q.toMonoidHom B := by
    apply Units.ext
    exact (Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton.mpr h))
  have hd : X ^ d ∣
      ((↑(A ^ (3 * k)) : PowerSeries R) - (↑(A ^ (-(3 * k + 1))) : PowerSeries R)) -
      ((↑(B ^ (3 * k)) : PowerSeries R) - (↑(B ^ (-(3 * k + 1))) : PowerSeries R)) := by
    apply Ideal.mem_span_singleton.mp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change q _ = 0
    simp only [map_sub]
    have hp (j : ℤ) : q (↑(A ^ j) : PowerSeries R) = q (↑(B ^ j) : PowerSeries R) := by
      have hh := congrArg (fun U : ((PowerSeries R) ⧸ I)ˣ =>
        ((U ^ j : ((PowerSeries R) ⧸ I)ˣ) : (PowerSeries R) ⧸ I)) hab
      rw [← (Units.map q.toMonoidHom).map_zpow A j,
        ← (Units.map q.toMonoidHom).map_zpow B j] at hh
      exact hh
    rw [hp, hp, sub_self]
  have hx : (X : PowerSeries R) ∣ X ^ exponent k := by
    simpa only [pow_one] using pow_dvd_pow (X : PowerSeries R)
      (show 1 ≤ exponent k by have := exponent_bound k; omega)
  rw [term, term, ← mul_sub]
  simpa only [pow_succ'] using mul_dvd_mul hx hd

private theorem nonzero_agree {d : ℕ} {A B : (PowerSeries R)ˣ}
    (h : Agree d A B) : X ^ (d + 1) ∣ nonzeroSum A - nonzeroSum B := by
  apply X_pow_dvd_iff.mpr
  intro N hN
  simp only [map_sub, nonzeroSum, coeff_mk, ← Finset.sum_sub_distrib]
  apply Finset.sum_eq_zero
  intro k hk
  have ht := X_pow_dvd_iff.mp (term_agree h k (Finset.ne_of_mem_erase hk)) N hN
  simpa only [map_sub] using ht

private theorem step_agree {d : ℕ} {A B : (PowerSeries R)ˣ}
    (h : Agree d A B) : Agree (d + 1) (step A) (step B) := by
  let I : Ideal (PowerSeries R) := Ideal.span {X ^ (d + 1)}
  let q := Ideal.Quotient.mk I
  have hd : q (denominator A) = q (denominator B) := by
    apply Ideal.Quotient.eq.mpr
    apply Ideal.mem_span_singleton.mpr
    simpa only [denominator, add_sub_add_left_eq_sub] using nonzero_agree h
  have hi : Units.map q.toMonoidHom (step A)⁻¹ =
      Units.map q.toMonoidHom (step B)⁻¹ := by
    apply Units.ext
    exact hd
  have he : Units.map q.toMonoidHom (step A) = Units.map q.toMonoidHom (step B) := by
    simpa using congrArg (fun U => U⁻¹) hi
  exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp (congrArg Units.val he))

private noncomputable def approximation : ℕ → (PowerSeries R)ˣ
  | 0 => 1
  | d + 1 => step (approximation d)

private theorem approximation_stable {d e : ℕ} (h : d ≤ e) :
    Agree d (approximation (R := R) d) (approximation e) := by
  induction d generalizing e with
  | zero => exact one_dvd _
  | succ d ih =>
    cases e with
    | zero => omega
    | succ e => exact step_agree (ih (by omega))

noncomputable def generatingSeries : PowerSeries R :=
  mk fun n => coeff n (approximation (R := R) (n + 1) : PowerSeries R)

private theorem generating_constant : constantCoeff (generatingSeries (R := R)) = 1 := by
  rw [← coeff_zero_eq_constantCoeff]
  simp [generatingSeries, approximation, step, coeff_zero_eq_constantCoeff]

noncomputable def generatingUnit : (PowerSeries R)ˣ :=
  ⟨generatingSeries, invOfUnit generatingSeries 1,
    mul_invOfUnit _ 1 generating_constant, invOfUnit_mul _ 1 generating_constant⟩

private theorem generating_agree (d : ℕ) :
    Agree d (generatingUnit (R := R)) (approximation d) := by
  apply X_pow_dvd_iff.mpr
  intro n hn
  simp only [map_sub, generatingUnit, generatingSeries, coeff_mk, sub_eq_zero]
  exact agree_coeff (approximation_stable (R := R) (by omega : n + 1 ≤ d)) n (by omega)

private theorem generating_fixed : generatingUnit (R := R) = step generatingUnit := by
  apply Units.ext
  ext n
  exact (agree_coeff (generating_agree (n + 2)) n (by omega)).trans
    (agree_coeff (step_agree (generating_agree (n + 1))) n (by omega)).symm

private theorem original_iff (A : (PowerSeries R)ˣ) : Original A ↔ A = step A := by
  unfold Original
  rw [bilateral_split]
  constructor
  · intro h
    have hd : (↑A⁻¹ : PowerSeries R) = denominator A := by
      unfold denominator; linear_combination -h
    apply inv_injective
    apply Units.ext
    exact hd
  · intro h
    have hi := congrArg (fun U : (PowerSeries R)ˣ => (↑U⁻¹ : PowerSeries R)) h
    change (↑A⁻¹ : PowerSeries R) = denominator A at hi
    unfold denominator at hi
    linear_combination -hi

private theorem original_unique (A : (PowerSeries R)ˣ) (h : Original A) :
    A = generatingUnit := by
  have hf := (original_iff A).mp h
  have ha : ∀ d, Agree d A generatingUnit := by
    intro d
    induction d with
    | zero => exact one_dvd _
    | succ d ih => simpa only [← hf, ← generating_fixed] using step_agree ih
  apply Units.ext
  ext n
  exact agree_coeff (ha (n + 1)) n (by omega)

private theorem hasSum_bilateral [TopologicalSpace R] (A : (PowerSeries R)ˣ) :
    HasSum (term A) (bilateral A) := by
  apply (WithPiTopology.hasSum_iff_hasSum_coeff R).mpr
  intro N
  rw [window A N N le_rfl]
  exact hasSum_sum_of_ne_finset_zero (fun k hk => outside_zero A N k hk)

private theorem map_term {S : Type*} [CommRing S] (f : R →+* S)
    (A : (PowerSeries R)ˣ) (k : ℤ) :
    (term A k).map f = term (Units.map (PowerSeries.map f).toMonoidHom A) k := by
  simp only [term, map_mul, map_sub, map_pow, map_X]
  congr 2 <;> exact (congrArg Units.val ((Units.map (PowerSeries.map f).toMonoidHom).map_zpow A _))

private theorem map_bilateral {S : Type*} [CommRing S] (f : R →+* S)
    (A : (PowerSeries R)ˣ) :
    (bilateral A).map f = bilateral (Units.map (PowerSeries.map f).toMonoidHom A) := by
  ext N
  simp only [bilateral, coeff_map, coeff_mk, map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← coeff_map, map_term]

private theorem map_original {S : Type*} [CommRing S] (f : R →+* S)
    (A : (PowerSeries R)ˣ) (h : Original A) :
    Original (Units.map (PowerSeries.map f).toMonoidHom A) := by
  unfold Original at h ⊢
  rw [← map_bilateral, h]
  simp only [map_mul, map_ofNat, map_X]

private theorem even_series (A : (PowerSeries ℤ)ˣ) (h : Original A) :
    (A : PowerSeries ℤ).map (Int.castRingHom (ZMod 2)) = 1 := by
  have hm := map_original (Int.castRingHom (ZMod 2)) A h
  have ho : Original (1 : (PowerSeries (ZMod 2))ˣ) := by
    unfold Original
    have h2 : (2 : PowerSeries (ZMod 2)) = 0 := by
      rw [show (2 : PowerSeries (ZMod 2)) = C (2 : ZMod 2) from (map_ofNat C 2).symm]
      rw [show (2 : ZMod 2) = 0 by decide, map_zero]
    ext N
    simp [bilateral, term, h2]
  have he := (original_unique _ hm).trans (original_unique _ ho).symm
  exact congrArg Units.val he

/-- Ordinary integer partitions, including the unique empty partition. -/
noncomputable def partitionCount (n : ℕ) : ℕ := Fintype.card (Nat.Partition n)

noncomputable def partitionSeries : PowerSeries ℤ := mk fun n => (partitionCount n : ℤ)


theorem partition_reciprocal : pentagonalSeries ℤ * partitionSeries = 1 := by
  have hp : HasProd (fun i : ℕ => ∑' j : ℕ, (X : PowerSeries ℤ) ^ ((i + 1) * j))
      partitionSeries := by
    simpa [Nat.Partition.restricted, partitionSeries, partitionCount] using
      Nat.Partition.hasProd_powerSeriesMk_card_restricted ℤ (fun _ => True)
  have he := WithPiTopology.hasProd_one_sub_X_pow ℤ
  have h := he.mul hp
  have hg (i : ℕ) : (1 - X ^ (i + 1) : PowerSeries ℤ) *
      (∑' j : ℕ, (X : PowerSeries ℤ) ^ ((i + 1) * j)) = 1 := by
    simpa only [pow_mul] using
      WithPiTopology.one_sub_mul_tsum_pow_of_constantCoeff_eq_zero
        (f := (X : PowerSeries ℤ) ^ (i + 1)) (by simp)
  simp only [hg] at h
  exact h.unique (hasProd_one (β := ℕ) (α := PowerSeries ℤ))

private noncomputable def halfSeries (A : (PowerSeries ℤ)ˣ) : PowerSeries ℤ :=
  mk fun n => (coeff n (A : PowerSeries ℤ) - coeff n (1 : PowerSeries ℤ)) / 2

private theorem half_spec (A : (PowerSeries ℤ)ˣ) (h : Original A) :
    (A : PowerSeries ℤ) = 1 + 2 * halfSeries A := by
  ext n
  have he := congrArg (coeff n) (even_series A h)
  simp only [coeff_map, eq_intCast] at he
  have hz : ((coeff n (A : PowerSeries ℤ) - coeff n (1 : PowerSeries ℤ) : ℤ) : ZMod 2) = 0 := by
    simpa [Int.cast_sub, coeff_one] using (sub_eq_zero.mpr he)
  have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp hz
  have hc := Int.mul_ediv_cancel' hd
  rw [map_add, show (2 : PowerSeries ℤ) = C 2 from (map_ofNat C 2).symm, coeff_C_mul]
  simp only [halfSeries, coeff_mk]
  omega

private theorem mod_four_term (A : (PowerSeries ℤ)ˣ) (h : Original A) (k : ℤ) :
    (term A k).map (Int.castRingHom (ZMod 4)) =
      2 * (halfSeries A).map (Int.castRingHom (ZMod 4)) *
        ((Int.negOnePow (-k) : PowerSeries (ZMod 4)) * X ^ exponent k) := by
  have hfour : (4 : PowerSeries (ZMod 4)) = 0 := by
    rw [← map_ofNat C 4, show (4 : ZMod 4) = 0 by decide, map_zero]
  let U := Units.map (PowerSeries.map (Int.castRingHom (ZMod 4))).toMonoidHom A
  let B := (halfSeries A).map (Int.castRingHom (ZMod 4))
  have hv : (U : PowerSeries (ZMod 4)) = 1 + 2 * B := by
    change (A : PowerSeries ℤ).map (Int.castRingHom (ZMod 4)) = 1 + 2 * B
    rw [half_spec A h]
    simp only [B, map_add, map_one, map_mul, map_ofNat]
  have hu : U ^ (2 : ℤ) = 1 := by
    apply Units.ext
    simp only [zpow_ofNat, Units.val_pow_eq_pow_val, Units.val_one, hv]
    linear_combination B ^ 2 * hfour + B * hfour
  have hp (j : ℤ) : U ^ j = U ^ (j % 2) := by
    have hd : j = 2 * (j / 2) + j % 2 := by omega
    conv_lhs => rw [hd, zpow_add, zpow_mul, hu, one_zpow, one_mul]
  rw [map_term]
  change X ^ exponent k * ((↑(U ^ (3 * k)) : PowerSeries (ZMod 4)) -
    (↑(U ^ (-(3 * k + 1))) : PowerSeries (ZMod 4))) = _
  rw [hp (3 * k), hp (-(3 * k + 1))]
  rcases Int.even_or_odd (-k) with he | ho
  · rw [Int.negOnePow_even _ he]
    have hke : (3 * k) % 2 = 0 := by obtain ⟨j, hj⟩ := he; omega
    have hkne : (-(3 * k + 1)) % 2 = 1 := by omega
    rw [hke, hkne]
    simp only [zpow_zero, zpow_one, Units.val_one, hv, Int.cast_one, one_mul]
    linear_combination -X ^ exponent k * B * hfour
  · rw [Int.negOnePow_odd _ ho]
    have hko : (3 * k) % 2 = 1 := by obtain ⟨j, hj⟩ := ho; omega
    have hkno : (-(3 * k + 1)) % 2 = 0 := by omega
    rw [hko, hkno]
    simp only [zpow_zero, zpow_one, Units.val_one, hv]
    change X ^ exponent k * ((1 + 2 * B) - 1) =
      2 * B * ((-1) * X ^ exponent k)
    linear_combination X ^ exponent k * B * hfour

private theorem map_pentagonal (m : ℕ) :
    (pentagonalSeries ℤ).map (Int.castRingHom (ZMod m)) = pentagonalSeries (ZMod m) := by
  ext n
  simp only [coeff_map, pentagonalSeries, coeff_mk, eq_intCast]
  split_ifs
  · simp
  · simp

private theorem mod_four_equation (A : (PowerSeries ℤ)ˣ) (h : Original A) :
    (2 * (halfSeries A * pentagonalSeries ℤ - X)).map (Int.castRingHom (ZMod 4)) = 0 := by
  have ht := hasSum_bilateral (Units.map (PowerSeries.map (Int.castRingHom (ZMod 4))).toMonoidHom A)
  have he := WithPiTopology.hasSum_pentagonalSeries (ZMod 4)
  have hn : HasSum (fun k : ℤ => (Int.negOnePow (-k) : PowerSeries (ZMod 4)) * X ^ exponent k)
      (pentagonalSeries (ZMod 4)) := by
    change HasSum ((fun k : ℤ => (Int.negOnePow k : PowerSeries (ZMod 4)) *
      X ^ pentagonal k) ∘ (Equiv.neg ℤ)) (pentagonalSeries (ZMod 4))
    exact (Equiv.neg ℤ).hasSum_iff.mpr he
  have hb := hn.mul_left (2 * (halfSeries A).map (Int.castRingHom (ZMod 4)))
  have hf : term (Units.map (PowerSeries.map (Int.castRingHom (ZMod 4))).toMonoidHom A) =
      (fun k => 2 * (halfSeries A).map (Int.castRingHom (ZMod 4)) *
        ((Int.negOnePow (-k) : PowerSeries (ZMod 4)) * X ^ exponent k)) := by
    funext k
    rw [← map_term, mod_four_term A h]
  rw [hf] at ht
  have hx := ht.unique hb
  rw [← map_bilateral, h] at hx
  simp only [map_mul, map_ofNat, map_X] at hx
  simp only [map_mul, map_sub, map_ofNat, map_X, map_pentagonal]
  linear_combination -hx

private theorem mod_two_equation (A : (PowerSeries ℤ)ˣ) (h : Original A) :
    (halfSeries A * pentagonalSeries ℤ).map (Int.castRingHom (ZMod 2)) = X := by
  have he := mod_four_equation A h
  ext n
  have hc := congrArg (coeff n) he
  rw [coeff_map, map_zero, show (2 : PowerSeries ℤ) = C 2 from (map_ofNat C 2).symm,
    coeff_C_mul, map_sub] at hc
  have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mp hc
  have hd2 : 2 ∣ coeff n (halfSeries A * pentagonalSeries ℤ) - coeff n (X : PowerSeries ℤ) := by
    omega
  have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mpr hd2
  rw [coeff_map, eq_intCast]
  have hx : ((coeff n (X : PowerSeries ℤ) : ℤ) : ZMod 2) = coeff n (X : PowerSeries (ZMod 2)) := by
    simp [coeff_X]
  rw [← hx]
  simpa only [Int.cast_sub, sub_eq_zero] using hz

private theorem half_partition (A : (PowerSeries ℤ)ˣ) (h : Original A) :
    (halfSeries A).map (Int.castRingHom (ZMod 2)) =
      X * partitionSeries.map (Int.castRingHom (ZMod 2)) := by
  have he := mod_two_equation A h
  have hp := congrArg (PowerSeries.map (Int.castRingHom (ZMod 2))) partition_reciprocal
  simp only [map_mul, map_one] at he hp
  calc
    (halfSeries A).map (Int.castRingHom (ZMod 2)) =
        (halfSeries A).map (Int.castRingHom (ZMod 2)) *
        ((pentagonalSeries ℤ).map (Int.castRingHom (ZMod 2)) *
          partitionSeries.map (Int.castRingHom (ZMod 2))) := by rw [hp, mul_one]
    _ = X * partitionSeries.map (Int.castRingHom (ZMod 2)) := by rw [← mul_assoc, he]

/-- Integer-index correspondence for the coefficients of the original series. -/
noncomputable def a (n : ℤ) : ℤ := if 0 ≤ n then coeff n.toNat (generatingSeries (R := ℤ)) else 0

private theorem coefficient_parity (A : (PowerSeries ℤ)ˣ) (h : Original A)
    (n : ℤ) (hn : 1 ≤ n) :
    2 ∣ coeff n.toNat (A : PowerSeries ℤ) ∧
    (coeff n.toNat (A : PowerSeries ℤ) / 2) % 2 =
      (partitionCount (n - 1).toNat : ℤ) % 2 := by
  have hi : 0 < n.toNat := by omega
  have he := congrArg (coeff n.toNat) (even_series A h)
  simp only [coeff_map, eq_intCast, coeff_one, if_neg (by omega : n.toNat ≠ 0)] at he
  refine ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp he, ?_⟩
  have hp := congrArg (coeff n.toNat) (half_partition A h)
  have hs : n.toNat = (n - 1).toNat + 1 := by omega
  rw [coeff_map, eq_intCast, hs, coeff_succ_X_mul, coeff_map,
    eq_intCast] at hp
  simp only [halfSeries, coeff_mk, coeff_one,
    if_neg (by omega : (n - 1).toNat + 1 ≠ 0), sub_zero,
    partitionSeries, coeff_mk] at hp
  rw [← hs] at hp
  exact (ZMod.intCast_eq_intCast_iff' _ _ 2).mp hp

/-- The complete original-domain assertion, with its full-sum interpretation. -/
def LiteralResolution : Prop :=
  (∀ k : ℤ, (exponent k : ℤ) = k * (3 * k + 1) / 2 ∧
    0 ≤ (exponent k : ℤ) ∧ 2 * (exponent k : ℤ) = k * (3 * k + 1)) ∧
  (∀ (A : (PowerSeries ℤ)ˣ) (N : ℕ) (k : ℤ),
    k ∉ Finset.Icc (-(N : ℤ)) N →
    coeff N (X ^ exponent k * (↑(A ^ (3 * k)) : PowerSeries ℤ)) = 0 ∧
    coeff N (X ^ exponent k * (↑(A ^ (-(3 * k + 1))) : PowerSeries ℤ)) = 0) ∧
  (∀ A : (PowerSeries ℤ)ˣ, HasSum (term A) (bilateral A)) ∧
  Original (generatingUnit (R := ℤ)) ∧
  (∀ A : (PowerSeries ℤ)ˣ, Original A →
    constantCoeff (A : PowerSeries ℤ) = 1 ∧ A = generatingUnit ∧
    ∀ n : ℤ, 1 ≤ n → 2 ∣ coeff n.toNat (A : PowerSeries ℤ) ∧
      (coeff n.toNat (A : PowerSeries ℤ) / 2) % 2 =
        (partitionCount (n - 1).toNat : ℤ) % 2) ∧
  partitionCount 0 = 1 ∧
  (∀ n : ℤ, 0 ≤ n → a n = coeff n.toNat (generatingSeries (R := ℤ)))

/-- Hanna's literal A361552 conjecture for the unique integral unit solution. -/
theorem result : LiteralResolution := by
  refine ⟨?_, ?_, hasSum_bilateral, (original_iff _).mpr generating_fixed, ?_, ?_, ?_⟩
  · intro k
    exact ⟨(exponent_exact k).1, Int.natCast_nonneg _, (exponent_exact k).2⟩
  · intro A N k hk
    have hb : N < exponent k := by
      have h := exponent_bound k
      simp only [Finset.mem_Icc] at hk
      omega
    exact ⟨X_pow_dvd_iff.mp (dvd_mul_right (X ^ exponent k) _) N hb,
      X_pow_dvd_iff.mp (dvd_mul_right (X ^ exponent k) _) N hb⟩
  · intro A h
    exact ⟨original_constant A h, original_unique A h, coefficient_parity A h⟩
  · unfold partitionCount
    exact Fintype.card_unique
  · intro n hn
    simp only [a, if_pos hn]

end D5.S1.Recurrence.Bilateral.HannaPentagonalPartitionParity
