/- GID: D5/S1/Recurrence/Bilateral/BilateralQuarterDoubleShiftThetaModFour
   generality: I
   mirror-B: D5/B/S1/Recurrence/Bilateral/BilateralQuarterDoubleShiftThetaModFour
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Doubled-square support follows from integral bilateral cancellation. -/

import D5.S1.Recurrence.Parity.ThetaSelfCompositionModFour
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Data.Int.Interval

open PowerSeries
open scoped Classical
open D5.S1.Recurrence.Parity
namespace D5.S1.Recurrence.Bilateral.BilateralQuarterDoubleShiftThetaModFour

variable {R : Type*} [CommRing R]

private noncomputable def positiveTerm (A : PowerSeries R) (m : ℕ) : PowerSeries R :=
  (-1) ^ (m + 1) * X ^ (m + 1) * (4 * A + X ^ (2 * m + 1)) ^ (m + 2)

private noncomputable def reciprocal (A : PowerSeries R) (m : ℕ) : PowerSeries R :=
  invOfUnit (1 + 4 * A * X ^ (2 * m + 5)) 1

private theorem reciprocal_spec (A : PowerSeries R) (m : ℕ) :
    reciprocal A m * (1 + 4 * A * X ^ (2 * m + 5)) = 1 :=
  invOfUnit_mul _ 1 (by simp)

private noncomputable def negativeTerm (A : PowerSeries R) (m : ℕ) : PowerSeries R :=
  (-1) ^ (m + 2) * X ^ (2 * m ^ 2 + 6 * m + 3) * reciprocal A m ^ (m + 1)

private noncomputable def pairedTerm (A : PowerSeries R) (m : ℕ) : PowerSeries R :=
  positiveTerm A m + negativeTerm A m

-- The n=0 and n=-1 Laurent monomials cancel before this power-series definition.
noncomputable def bilateralTerm (A : PowerSeries ℤ) (n : ℤ) : PowerSeries ℤ :=
  if n = 0 then 4 * A else if n = -1 then 0 else
    if 0 < n then positiveTerm A (n.toNat - 1) else negativeTerm A (-n - 2).toNat

private theorem positive_order (A : PowerSeries R) (m : ℕ) :
    (X : PowerSeries R) ^ (m + 1) ∣ positiveTerm A m := by
  unfold positiveTerm
  exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _

private theorem negative_order (A : PowerSeries R) (m : ℕ) :
    (X : PowerSeries R) ^ (m + 1) ∣ negativeTerm A m := by
  unfold negativeTerm
  exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right
    (pow_dvd_pow _ (by nlinarith : m + 1 ≤ 2 * m ^ 2 + 6 * m + 3)) _) _

theorem bilateralTerm_coeff_eq_zero (A : PowerSeries ℤ) (N : ℕ) (n : ℤ)
    (hn : n < -(N : ℤ) - 2 ∨ (N : ℤ) < n) : coeff N (bilateralTerm A n) = 0 := by
  have h0 : n ≠ 0 := by omega
  have h1 : n ≠ -1 := by omega
  simp only [bilateralTerm, if_neg h0, if_neg h1]
  split_ifs with hp
  · exact X_pow_dvd_iff.mp (positive_order A _) N (by omega)
  · exact X_pow_dvd_iff.mp (negative_order A _) N (by omega)

private def Agree (d : ℕ) (A B : PowerSeries R) : Prop :=
  ∀ n < d, coeff n A = coeff n B

private theorem agree_iff (d : ℕ) (A B : PowerSeries R) :
    Agree d A B ↔ (X : PowerSeries R) ^ d ∣ A - B := by
  simp [Agree, X_pow_dvd_iff, map_sub, sub_eq_zero]

private theorem reciprocal_sub (A B : PowerSeries R) (m : ℕ) :
    reciprocal A m - reciprocal B m =
      -4 * X ^ (2 * m + 5) * reciprocal A m * reciprocal B m * (A - B) := by
  have ha := reciprocal_spec A m
  have hb := reciprocal_spec B m
  linear_combination reciprocal B m * ha - reciprocal A m * hb

private theorem paired_agree {d : ℕ} {A B : PowerSeries R} (h : Agree d A B) (m : ℕ) :
    Agree (d + 1) (pairedTerm A m) (pairedTerm B m) := by
  have hab := (agree_iff _ _ _).mp h
  have hp : X ^ d ∣ (4 * A + X ^ (2 * m + 1)) ^ (m + 2) - (4 * B + X ^ (2 * m + 1)) ^ (m + 2) := by
    apply dvd_trans _ (sub_dvd_pow_sub_pow _ _ _)
    simpa only [add_sub_add_right_eq_sub, ← mul_sub] using dvd_mul_of_dvd_right hab 4
  have hn : X ^ d ∣ reciprocal A m ^ (m + 1) - reciprocal B m ^ (m + 1) := by
    apply dvd_trans _ (sub_dvd_pow_sub_pow _ _ _)
    rw [reciprocal_sub]
    exact dvd_mul_of_dvd_right hab _
  have hx : (X : PowerSeries R) ∣ (-1) ^ (m + 1) * X ^ (m + 1) :=
    dvd_mul_of_dvd_right (by simpa only [pow_one] using
      (pow_dvd_pow (X : PowerSeries R) (by omega : 1 ≤ m + 1))) _
  have hy : (X : PowerSeries R) ∣ (-1) ^ (m + 2) * X ^ (2 * m ^ 2 + 6 * m + 3) :=
    dvd_mul_of_dvd_right (by simpa only [pow_one] using
      (pow_dvd_pow (X : PowerSeries R) (by omega : 1 ≤ 2 * m ^ 2 + 6 * m + 3))) _
  apply (agree_iff _ _ _).mpr
  have hd := dvd_add (mul_dvd_mul hx hp) (mul_dvd_mul hy hn)
  rw [← pow_succ'] at hd
  convert hd using 1
  simp only [pairedTerm, positiveTerm, negativeTerm]
  ring

private theorem paired_zero (m : ℕ) : pairedTerm (0 : PowerSeries R) m = 0 := by
  have hi : reciprocal (0 : PowerSeries R) m = 1 := by
    simpa using reciprocal_spec (0 : PowerSeries R) m
  have he : m + 1 + (2 * m + 1) * (m + 2) = 2 * m ^ 2 + 6 * m + 3 := by ring
  simp only [pairedTerm, positiveTerm, negativeTerm, mul_zero, zero_add, hi, one_pow,
    mul_one, ← pow_mul, mul_assoc, ← pow_add, he]
  rw [show m + 2 = (m + 1) + 1 by omega, pow_succ]
  ring

private theorem paired_four_dvd (A : PowerSeries ℤ) (m : ℕ) : 4 ∣ pairedTerm A m := by
  have hp : (4 : PowerSeries ℤ) ∣
      (4 * A + X ^ (2 * m + 1)) ^ (m + 2) - (4 * 0 + X ^ (2 * m + 1)) ^ (m + 2) := by
    apply dvd_trans _ (sub_dvd_pow_sub_pow _ _ _)
    simp
  have hn : (4 : PowerSeries ℤ) ∣ reciprocal A m ^ (m + 1) - reciprocal 0 m ^ (m + 1) := by
    apply dvd_trans _ (sub_dvd_pow_sub_pow _ _ _)
    rw [reciprocal_sub]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left
      (dvd_mul_of_dvd_left (dvd_neg.mpr dvd_rfl) _) _) _) _
  have he : pairedTerm A m =
      (-1) ^ (m + 1) * X ^ (m + 1) *
        ((4 * A + X ^ (2 * m + 1)) ^ (m + 2) - (4 * 0 + X ^ (2 * m + 1)) ^ (m + 2)) +
      (-1) ^ (m + 2) * X ^ (2 * m ^ 2 + 6 * m + 3) *
        (reciprocal A m ^ (m + 1) - reciprocal 0 m ^ (m + 1)) := by
    have hz := paired_zero (R := ℤ) m
    dsimp only [pairedTerm, positiveTerm, negativeTerm] at hz ⊢
    linear_combination hz
  rw [he]
  exact dvd_add (dvd_mul_of_dvd_right hp _) (dvd_mul_of_dvd_right hn _)

private noncomputable def remainder (A : PowerSeries ℤ) : PowerSeries ℤ :=
  mk fun N => ∑ m ∈ Finset.range (N + 1), coeff N (pairedTerm A m)

private theorem remainder_four_dvd (A : PowerSeries ℤ) (N : ℕ) :
    4 ∣ coeff N (remainder A) := by
  simp only [remainder, coeff_mk]
  apply Finset.dvd_sum
  intro m hm
  obtain ⟨B, hb⟩ := paired_four_dvd A m
  refine ⟨coeff N B, ?_⟩
  rw [hb, show (4 : PowerSeries ℤ) = C 4 from (map_ofNat C 4).symm, coeff_C_mul]

private noncomputable def step (A : PowerSeries ℤ) : PowerSeries ℤ :=
  1 - mk fun N => coeff N (remainder A) / 4

private theorem step_agree {d : ℕ} {A B : PowerSeries ℤ} (h : Agree d A B) :
    Agree (d + 1) (step A) (step B) := by
  intro N hN
  simp only [step, map_sub, coeff_mk, remainder]
  congr 2
  exact Finset.sum_congr rfl fun m _ => paired_agree h m N hN

private theorem step_constant (A : PowerSeries ℤ) : constantCoeff (step A) = 1 := by
  have h : coeff 0 (remainder A) = 0 := by
    simp only [remainder, coeff_mk]
    apply Finset.sum_eq_zero
    intro m hm
    rw [pairedTerm, map_add,
      X_pow_dvd_iff.mp (positive_order A m) 0 (by omega),
      X_pow_dvd_iff.mp (negative_order A m) 0 (by omega), add_zero]
  simp only [step, map_sub, constantCoeff_one, ← coeff_zero_eq_constantCoeff,
    coeff_mk, h, Int.zero_ediv, sub_zero]

private noncomputable def approximation : ℕ → PowerSeries ℤ
  | 0 => 1
  | d + 1 => step (approximation d)

private theorem approximation_stable {d e : ℕ} (h : d ≤ e) :
    Agree d (approximation d) (approximation e) := by
  induction d generalizing e with
  | zero => intro n hn; omega
  | succ d ih =>
    cases e with
    | zero => omega
    | succ e => exact step_agree (ih (by omega))

noncomputable def a (n : ℕ) : ℤ := coeff n (approximation (n + 1))

noncomputable def generatingSeries : PowerSeries ℤ := mk a

private theorem generating_agree (d : ℕ) : Agree d generatingSeries (approximation d) := by
  intro n hn
  simpa only [generatingSeries, coeff_mk, a] using
    approximation_stable (by omega : n + 1 ≤ d) n (by omega)

private theorem generating_fixed : generatingSeries = step generatingSeries := by
  ext n
  exact (generating_agree (n + 2) n (by omega)).trans
    (step_agree (generating_agree (n + 1)) n (by omega)).symm

private theorem window_pair (f : ℤ → R) (K : ℕ) :
    (∑ j ∈ Finset.Icc (-(K : ℤ) - 2) (K + 1), f j) =
      f 0 + f (-1) + ∑ m ∈ Finset.range (K + 1), (f (m + 1) + f (-(m : ℤ) - 2)) := by
  induction K with
  | zero =>
    have hs : Finset.Icc (-2 : ℤ) 1 = {-2, -1, 0, 1} := by decide
    norm_num [hs]
    ring
  | succ K ih =>
    have hs : Finset.Icc (-((K + 1 : ℕ) : ℤ) - 2) ((K + 1 : ℕ) + 1) =
        insert (-(K : ℤ) - 3) (insert ((K : ℤ) + 2) (Finset.Icc (-(K : ℤ) - 2) (K + 1))) := by
      ext j
      simp only [Finset.mem_Icc, Finset.mem_insert, Nat.cast_add, Nat.cast_one]
      omega
    rw [hs, Finset.sum_insert (by simp; omega), Finset.sum_insert (by simp), ih]
    conv_rhs => rw [Finset.sum_range_succ]
    push_cast
    rw [show -((K : ℤ) + 1) - 2 = -K - 3 by omega,
      show (K : ℤ) + 1 + 1 = K + 2 by omega]
    ring

private theorem window_remainder (A : PowerSeries ℤ) (N : ℕ) :
    coeff N (∑ j ∈ Finset.Icc (-(N : ℤ) - 2) N, bilateralTerm A j) =
      4 * coeff N A + coeff N (remainder A) := by
  have hp (m : ℕ) : bilateralTerm A (m + 1) = positiveTerm A m := by
    simp [bilateralTerm, show (m : ℤ) + 1 ≠ 0 by omega,
      show ¬ (m : ℤ) + 1 = -1 by omega]
  have hn (m : ℕ) : bilateralTerm A (-(m : ℤ) - 2) = negativeTerm A m := by
    simp [bilateralTerm, show -(m : ℤ) - 2 ≠ 0 by omega,
      show -(m : ℤ) - 2 ≠ -1 by omega]
  have he := window_pair (fun j => coeff N (bilateralTerm A j)) N
  have hs : Finset.Icc (-(N : ℤ) - 2) (N + 1) =
      insert ((N : ℤ) + 1) (Finset.Icc (-(N : ℤ) - 2) N) := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  rw [hs, Finset.sum_insert (by simp), hp,
    X_pow_dvd_iff.mp (positive_order A N) N (by omega), zero_add] at he
  have hzero : bilateralTerm A 0 = 4 * A := by simp [bilateralTerm]
  have hone : bilateralTerm A (-1) = 0 := by simp [bilateralTerm]
  simpa only [map_sum, hp, hn, hzero, hone, map_zero, add_zero,
    remainder, coeff_mk, pairedTerm, map_add,
    show (4 : PowerSeries ℤ) = C 4 from (map_ofNat C 4).symm, coeff_C_mul] using he

private theorem equation_iff (A : PowerSeries ℤ) :
    (∀ N, coeff N (4 : PowerSeries ℤ) =
      coeff N (∑ j ∈ Finset.Icc (-(N : ℤ) - 2) N, bilateralTerm A j)) ↔ A = step A := by
  simp only [window_remainder]
  constructor
  · intro h
    ext N
    have hd := Int.mul_ediv_cancel' (remainder_four_dvd A N)
    have he := h N
    have hc : coeff N (4 : PowerSeries ℤ) = 4 * coeff N (1 : PowerSeries ℤ) := by
      rw [show (4 : PowerSeries ℤ) = C 4 * 1 by simp,
        coeff_C_mul]
    rw [hc] at he
    simp only [step, map_sub, coeff_mk]
    omega
  · intro h N
    have he := congrArg (coeff N) h
    simp only [step, map_sub, coeff_mk] at he
    have hd := Int.mul_ediv_cancel' (remainder_four_dvd A N)
    rw [show (4 : PowerSeries ℤ) = C 4 * 1 by simp, coeff_C_mul]
    omega

theorem generating_equation : constantCoeff generatingSeries = 1 ∧
    ∀ N, coeff N (4 : PowerSeries ℤ) =
      coeff N (∑ n ∈ Finset.Icc (-(N : ℤ) - 2) N, bilateralTerm generatingSeries n) := by
  refine ⟨?_, (equation_iff _).mpr generating_fixed⟩
  rw [generating_fixed, step_constant]

theorem generating_unique (B : PowerSeries ℤ) (_h0 : constantCoeff B = 1)
    (hB : ∀ N, coeff N (4 : PowerSeries ℤ) =
      coeff N (∑ n ∈ Finset.Icc (-(N : ℤ) - 2) N, bilateralTerm B n)) :
    B = generatingSeries := by
  have hb := (equation_iff B).mp hB
  have ha : ∀ d, Agree d B generatingSeries := by
    intro d
    induction d with
    | zero => intro n hn; omega
    | succ d ih => simpa only [← hb, ← generating_fixed] using step_agree ih
  ext n
  exact ha (n + 1) n (by omega)

theorem a_zero : a 0 = 1 := by
  simpa only [a, zero_add, approximation, coeff_zero_eq_constantCoeff] using
    step_constant (1 : PowerSeries ℤ)

private theorem map_reciprocal {S : Type*} [CommRing S] (f : R →+* S)
    (A : PowerSeries R) (m : ℕ) :
    (reciprocal A m).map f = reciprocal (A.map f) m := by
  have he := congrArg (PowerSeries.map f) (reciprocal_spec A m)
  simp only [map_mul, map_add, map_one, map_ofNat, map_pow, map_X] at he
  have hf := reciprocal_spec (A.map f) m
  linear_combination reciprocal (A.map f) m * he - (reciprocal A m).map f * hf

private theorem map_paired {S : Type*} [CommRing S] (f : R →+* S)
    (A : PowerSeries R) (m : ℕ) :
    (pairedTerm A m).map f = pairedTerm (A.map f) m := by
  simp only [pairedTerm, positiveTerm, negativeTerm, map_add, map_mul, map_pow,
    map_neg, map_one, map_ofNat, map_X, map_reciprocal]

private theorem square_zero_pow (u v : R) (hv : v ^ 2 = 0) (k : ℕ) :
    (u + v) ^ (k + 1) = u ^ (k + 1) + (k + 1 : R) * u ^ k * v := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih]
    push_cast
    simp only [pow_succ]
    linear_combination (k + 1 : R) * u ^ k * hv

private theorem paired_linear (A : PowerSeries R) (h16 : (16 : PowerSeries R) = 0) (m : ℕ) :
    pairedTerm A m =
      (-1) ^ (m + 1) * 4 * (m + 2 : PowerSeries R) * X ^ (2 * (m + 1) ^ 2) * A +
      (-1) ^ (m + 1) * 4 * (m + 1 : PowerSeries R) * X ^ (2 * (m + 2) ^ 2) * A := by
  have ha : (4 * A) ^ 2 = 0 := by linear_combination A ^ 2 * h16
  have hb : (4 * A * X ^ (2 * m + 5)) ^ 2 = 0 := by rw [mul_pow, ha, zero_mul]
  have hi : reciprocal A m = 1 - 4 * A * X ^ (2 * m + 5) := by
    linear_combination (1 - 4 * A * X ^ (2 * m + 5)) * reciprocal_spec A m +
      reciprocal A m * hb
  have hip : reciprocal A m ^ (m + 1) =
      1 - (m + 1 : PowerSeries R) * (4 * A * X ^ (2 * m + 5)) := by
    rw [hi, sub_eq_add_neg, square_zero_pow _ _ (by simpa using hb) m]
    simp [sub_eq_add_neg]
  have hbase : (X : PowerSeries R) ^ (m + 1) * (X ^ (2 * m + 1)) ^ (m + 2) =
      X ^ (2 * m ^ 2 + 6 * m + 3) := by
    rw [← pow_mul, ← pow_add]
    congr 1
    ring
  have hlin : (X : PowerSeries R) ^ (m + 1) * (X ^ (2 * m + 1)) ^ (m + 1) =
      X ^ (2 * (m + 1) ^ 2) := by
    rw [← pow_mul, ← pow_add]
    congr 1
    ring
  have hneg : (X : PowerSeries R) ^ (2 * m ^ 2 + 6 * m + 3) * X ^ (2 * m + 5) =
      X ^ (2 * (m + 2) ^ 2) := by
    rw [← pow_add]
    congr 1
    ring
  have hp : positiveTerm A m =
      (-1) ^ (m + 1) * X ^ (2 * m ^ 2 + 6 * m + 3) +
      (-1) ^ (m + 1) * 4 * (m + 2 : PowerSeries R) * X ^ (2 * (m + 1) ^ 2) * A := by
    calc
      _ = (-1) ^ (m + 1) * (X ^ (m + 1) * (X ^ (2 * m + 1)) ^ (m + 2)) +
          (-1) ^ (m + 1) * 4 * (m + 2 : PowerSeries R) *
            (X ^ (m + 1) * (X ^ (2 * m + 1)) ^ (m + 1)) * A := by
        unfold positiveTerm
        rw [add_comm (4 * A), square_zero_pow _ _ ha (m + 1)]
        push_cast
        ring
      _ = _ := by rw [hbase, hlin]
  have hn : negativeTerm A m =
      (-1) ^ (m + 2) * X ^ (2 * m ^ 2 + 6 * m + 3) -
      (-1) ^ (m + 2) * 4 * (m + 1 : PowerSeries R) * X ^ (2 * (m + 2) ^ 2) * A := by
    unfold negativeTerm
    rw [hip, ← hneg]
    ring
  rw [pairedTerm, hp, hn, show m + 2 = (m + 1) + 1 by omega, pow_succ (-1)]
  ring

private noncomputable def squareSupport : PowerSeries R :=
  mk fun n => if ∃ k : ℕ, 0 < k ∧ n = 2 * k ^ 2 then 1 else 0

private theorem square_approximation (N : ℕ) :
    Agree (N + 1) (squareSupport : PowerSeries R)
      (∑ m ∈ Finset.range (N + 1), X ^ (2 * (m + 1) ^ 2)) := by
  classical
  intro n hn
  simp only [squareSupport, coeff_mk, map_sum, coeff_X_pow]
  by_cases hs : ∃ k : ℕ, 0 < k ∧ n = 2 * k ^ 2
  · obtain ⟨k, hk, he⟩ := hs
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    have hm : m ∈ Finset.range (N + 1) := by
      simp only [Finset.mem_range]
      nlinarith
    rw [if_pos ⟨m + 1, by omega, he⟩, Finset.sum_eq_single m]
    · simp [he]
    · intro j hj hjm
      rw [if_neg (by intro h; apply hjm; nlinarith)]
    · exact fun h => (h hm).elim
  · rw [if_neg hs]
    symm
    apply Finset.sum_eq_zero
    intro m hm
    rw [if_neg (by intro he; apply hs; exact ⟨m + 1, by omega, he⟩)]

private theorem square_mul_coeff (A : PowerSeries R) (N : ℕ) :
    coeff N (squareSupport * A) =
      ∑ m ∈ Finset.range (N + 1), coeff N (X ^ (2 * (m + 1) ^ 2) * A) := by
  have hd := dvd_mul_of_dvd_left ((agree_iff _ _ _).mp (square_approximation (R := R) N)) A
  rw [sub_mul] at hd
  have he := (agree_iff _ _ _).mpr hd N (by omega : N < N + 1)
  simpa only [Finset.sum_mul, map_sum] using he

private theorem coeff_double_theta (n : ℕ) :
    coeff n (expand 2 (by omega) ThetaSelfCompositionModFour.thetaSeries) =
      if n = 0 then 1 else if ∃ k : ℕ, 0 < k ∧ n = 2 * k ^ 2 then 2 else 0 := by
  classical
  rw [coeff_expand]
  by_cases h0 : n = 0
  · subst n
    simp [ThetaSelfCompositionModFour.coeff_thetaSeries]
  · rw [if_neg h0]
    by_cases hd : 2 ∣ n
    · obtain ⟨r, rfl⟩ := hd
      have hr : r ≠ 0 := by omega
      have hs : IsSquare r ↔ ∃ k : ℕ, 0 < k ∧ 2 * r = 2 * k ^ 2 := by
        constructor
        · rintro ⟨k, hk⟩
          have hkpos : 0 < k := by
            by_contra h
            have hz : k = 0 := by omega
            simp_all
          exact ⟨k, hkpos, by nlinarith [hk]⟩
        · rintro ⟨k, hk, he⟩
          exact ⟨k, by nlinarith [he]⟩
      simp only [dvd_mul_right, if_true, Nat.mul_div_cancel_left _ (by omega : 0 < 2),
        ThetaSelfCompositionModFour.coeff_thetaSeries, if_neg hr, hs]
    · have hs : ¬ ∃ k : ℕ, 0 < k ∧ n = 2 * k ^ 2 := by
        rintro ⟨k, hk, rfl⟩
        exact hd ⟨k ^ 2, rfl⟩
      rw [if_neg hd, if_neg hs]

private theorem theta_expansion :
    expand 2 (by omega) ThetaSelfCompositionModFour.thetaSeries =
      1 + 2 * (squareSupport : PowerSeries ℤ) := by
  classical
  ext n
  simp only [coeff_double_theta, map_add,
    show (2 : PowerSeries ℤ) = C 2 from (map_ofNat C 2).symm, coeff_C_mul,
    squareSupport, coeff_mk, coeff_one]
  split_ifs with h0 hs hs <;> try norm_num
  · subst n
    obtain ⟨k, hk, he⟩ := hs
    nlinarith

private theorem map_squareSupport {S : Type*} [CommRing S] (f : R →+* S) :
    (squareSupport : PowerSeries R).map f = squareSupport := by
  classical
  ext n
  simp only [coeff_map, squareSupport, coeff_mk]
  split_ifs <;> simp

private theorem weighted_telescope (t : ℕ → R) (K : ℕ) :
    (∑ m ∈ Finset.range K, (4 * (m + 2 : R) * t m - 4 * (m + 1 : R) * t (m + 1))) =
      8 * (∑ m ∈ Finset.range K, t m) - 4 * (K : R) * t K := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
    push_cast
    ring

private theorem remainder_mod_sixteen (A : PowerSeries ℤ) :
    (remainder A).map (Int.castRingHom (ZMod 16)) =
      8 * squareSupport * A.map (Int.castRingHom (ZMod 16)) := by
  let f := Int.castRingHom (ZMod 16)
  let B := A.map f
  have h16 : (16 : PowerSeries (ZMod 16)) = 0 := by
    rw [← map_ofNat C 16, show (16 : ZMod 16) = 0 by decide, map_zero]
  let t (m : ℕ) : PowerSeries (ZMod 16) := (-1) ^ (m + 1) * X ^ (2 * (m + 1) ^ 2) * B
  have ht (m : ℕ) : pairedTerm B m =
      4 * (m + 2 : PowerSeries (ZMod 16)) * t m -
        4 * (m + 1 : PowerSeries (ZMod 16)) * t (m + 1) := by
    rw [paired_linear B h16]
    dsimp only [t]
    rw [show m + 1 + 1 = (m + 1) + 1 by omega, pow_succ (-1)]
    ring
  have hsign (m : ℕ) : (8 : PowerSeries (ZMod 16)) * (-1) ^ (m + 1) = 8 := by
    rcases neg_one_pow_eq_or (PowerSeries (ZMod 16)) (m + 1) with h | h <;> rw [h]
    · ring
    · linear_combination -h16
  ext N
  have hz : coeff N (t (N + 1)) = 0 := by
    apply (X_pow_dvd_iff (n := 2 * (N + 1 + 1) ^ 2)).mp ?_ N (by nlinarith)
    exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _
  have he := congrArg (coeff N) (weighted_telescope t (N + 1))
  push_cast at he
  have htail : coeff N (4 * (N + 1 : PowerSeries (ZMod 16)) * t (N + 1)) = 0 := by
    rw [show (4 * (N + 1 : PowerSeries (ZMod 16))) = C (4 * (N + 1 : ZMod 16)) by
      simp only [map_mul, map_add, map_natCast, map_ofNat, map_one],
      coeff_C_mul, hz, mul_zero]
  rw [map_sub, htail, sub_zero, show (8 : PowerSeries (ZMod 16)) = C 8 from
    (map_ofNat C 8).symm, coeff_C_mul, map_sum] at he
  have hleft : coeff N ((remainder A).map f) =
      coeff N (∑ m ∈ Finset.range (N + 1), pairedTerm B m) := by
    simp only [coeff_map, remainder, coeff_mk, map_sum]
    apply Finset.sum_congr rfl
    intro m hm
    exact (coeff_map f N (pairedTerm A m)).symm.trans
      (congrArg (coeff N) (map_paired f A m))
  rw [hleft]
  simp only [ht, map_sum]
  simp only [map_sum] at he
  rw [he]
  rw [Finset.mul_sum]
  have hs (m : ℕ) : (8 : ZMod 16) * coeff N (t m) =
      8 * coeff N (X ^ (2 * (m + 1) ^ 2) * B) := by
    have hh : (8 : PowerSeries (ZMod 16)) * t m = 8 * (X ^ (2 * (m + 1) ^ 2) * B) := by
      dsimp only [t]
      rw [← mul_assoc, ← mul_assoc, hsign]
      ring
    have hc := congrArg (coeff N) hh
    simpa only [show (8 : PowerSeries (ZMod 16)) = C 8 from (map_ofNat C 8).symm,
      coeff_C_mul] using hc
  simp only [hs]
  rw [← Finset.mul_sum, ← square_mul_coeff B N]
  rw [mul_assoc, show (8 : PowerSeries (ZMod 16)) = C 8 from (map_ofNat C 8).symm,
    coeff_C_mul]

-- The quotient is taken over the integers, before reduction modulo four.
theorem cancellation_identity : ∃ Q : PowerSeries ℤ,
    1 = generatingSeries * (expand 2 (by omega) ThetaSelfCompositionModFour.thetaSeries) + 4 * Q := by
  let H := remainder generatingSeries -
    4 * generatingSeries * ((expand 2 (by omega) ThetaSelfCompositionModFour.thetaSeries) - 1)
  have hm : H.map (Int.castRingHom (ZMod 16)) = 0 := by
    dsimp only [H]
    rw [map_sub, remainder_mod_sixteen, theta_expansion]
    simp only [map_mul, map_sub, map_add, map_ofNat, map_one, map_squareSupport]
    ring
  have hd (N : ℕ) : (16 : ℤ) ∣ coeff N H := by
    have hc := congrArg (coeff N) hm
    simp only [coeff_map, map_zero, Int.coe_castRingHom] at hc
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 16).mp hc
  let Q : PowerSeries ℤ := mk fun N => coeff N H / 16
  have hq : H = 16 * Q := by
    ext N
    rw [show (16 : PowerSeries ℤ) = C 16 from (map_ofNat C 16).symm, coeff_C_mul]
    simpa only [Q, coeff_mk] using (Int.mul_ediv_cancel' (hd N)).symm
  have he : (4 : PowerSeries ℤ) = 4 * generatingSeries + remainder generatingSeries := by
    ext N
    have hh := generating_equation.2 N
    rw [window_remainder] at hh
    simpa only [map_add, show (4 : PowerSeries ℤ) = C 4 from (map_ofNat C 4).symm,
      coeff_C_mul] using hh
  have hc : (4 : PowerSeries ℤ) =
      4 * (generatingSeries * (expand 2 (by omega) ThetaSelfCompositionModFour.thetaSeries) + 4 * Q) := by
    dsimp only [H] at hq
    linear_combination he + hq
  refine ⟨Q, ?_⟩
  have h4 : (4 : PowerSeries ℤ) ≠ 0 := by
    intro h
    have hz := congrArg constantCoeff h
    norm_num only [map_ofNat, map_zero] at hz
  exact mul_left_cancel₀ h4
    (by simpa only [mul_one] using hc)

theorem mod_four_identity : generatingSeries.map (Int.castRingHom (ZMod 4)) =
    (expand 2 (by omega) ThetaSelfCompositionModFour.thetaSeries).map (Int.castRingHom (ZMod 4)) := by
  let f := Int.castRingHom (ZMod 4)
  let T := (expand 2 (by omega) ThetaSelfCompositionModFour.thetaSeries).map f
  have h4 : (4 : PowerSeries (ZMod 4)) = 0 := by
    rw [← map_ofNat C 4, show (4 : ZMod 4) = 0 by decide, map_zero]
  have ht : T ^ 2 = 1 := by
    dsimp only [T]
    rw [theta_expansion]
    simp only [map_add, map_mul, map_ofNat, map_one, map_squareSupport]
    linear_combination ((squareSupport : PowerSeries (ZMod 4)) + squareSupport ^ 2) * h4
  obtain ⟨Q, hQ⟩ := cancellation_identity
  have he := congrArg (PowerSeries.map f) hQ
  simp only [map_one, map_add, map_mul, map_ofNat, h4, zero_mul, add_zero] at he
  change 1 = generatingSeries.map f * T at he
  change generatingSeries.map f = T
  calc
    generatingSeries.map f = generatingSeries.map f * (T * T) := by rw [← pow_two, ht, mul_one]
    _ = (generatingSeries.map f * T) * T := by ring
    _ = T := by rw [← he, one_mul]

theorem hanna_conjecture (n : ℕ) (hn : 1 ≤ n) :
    (a n % 4 = 2 ↔ ∃ k : ℕ, 0 < k ∧ n = 2 * k ^ 2) ∧
      (a n % 4 = 0 ↔ ¬ ∃ k : ℕ, 0 < k ∧ n = 2 * k ^ 2) := by
  have hc := congrArg (coeff n) mod_four_identity
  simp only [coeff_map, generatingSeries, coeff_mk] at hc
  change (a n : ZMod 4) =
    ((coeff n (expand 2 (by omega) ThetaSelfCompositionModFour.thetaSeries) : ℤ) : ZMod 4) at hc
  rw [coeff_double_theta, if_neg (by omega : n ≠ 0)] at hc
  by_cases hs : ∃ k : ℕ, 0 < k ∧ n = 2 * k ^ 2
  · rw [if_pos hs] at hc
    have ha : a n % 4 = 2 := (ZMod.intCast_eq_intCast_iff' (a n) 2 4).mp hc
    simp [hs, ha]
  · rw [if_neg hs] at hc
    have ha : a n % 4 = 0 := (ZMod.intCast_eq_intCast_iff' (a n) 0 4).mp hc
    simp [hs, ha]

theorem hanna_conjecture_floor (n : ℕ) (hn : 1 ≤ n) (h : ¬ IsSquare (n / 2)) :
    a n % 4 = 0 := by
  apply (hanna_conjecture n hn).2.mpr
  rintro ⟨k, hk, rfl⟩
  apply h
  refine ⟨k, ?_⟩
  simp [pow_two]

#print axioms bilateralTerm_coeff_eq_zero
#print axioms generating_equation
#print axioms generating_unique
#print axioms a_zero
#print axioms cancellation_identity
#print axioms mod_four_identity
#print axioms hanna_conjecture
#print axioms hanna_conjecture_floor

end D5.S1.Recurrence.Bilateral.BilateralQuarterDoubleShiftThetaModFour
