/- GID: D5/S1/Recurrence/Residue/DiagonalVanishingIndexDivisibility
   generality: I
   mirror-B: D5/B/S1/Recurrence/Residue/DiagonalVanishingIndexDivisibility
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Normalized vanishing diagonals inherit index-power divisibility from their exponents. -/

import D5.S1.Recurrence.Residue.NegativePowerDiagonalModPrime
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Data.Nat.Factorization.Basic

/-!
For an arbitrary natural exponent function e, construct the unique integer series
with constant and linear coefficients one and vanishing degree-n coefficient of
A(x/A(x)^(e n)) for n > 1. Quotients use the formal unit inverse.
Source: `Library/ArithSums/hanna2016diagonalindex.md`.

The quoted NAMEs of A300732 and A300733 say n >= 1, which conflicts with their
initial coefficients 1,1: the degree-one substituted coefficient is one.
Their instances below use the normalized n > 1 condition specified here.
-/

open PowerSeries
namespace D5.S1.Recurrence.Residue.DiagonalVanishingIndexDivisibility
variable {R : Type*} [CommRing R]

private def Agree (n : ℕ) (A B : PowerSeries R) : Prop :=
  ∀ k < n, coeff k A = coeff k B

private theorem agree_iff (n : ℕ) (A B : PowerSeries R) :
    Agree n A B ↔ (X : PowerSeries R) ^ n ∣ A - B := by
  simp [Agree, X_pow_dvd_iff, map_sub, sub_eq_zero]

private theorem agree_pow {n : ℕ} {A B : PowerSeries R}
    (h : Agree n A B) (m : ℕ) : Agree n (A ^ m) (B ^ m) :=
  (agree_iff _ _ _).mpr (((agree_iff _ _ _).mp h).trans (sub_dvd_pow_sub_pow A B m))

private theorem inverse_difference (A B : PowerSeries R)
    (hA : constantCoeff A = 1) (hB : constantCoeff B = 1) :
    invOfUnit A 1 - invOfUnit B 1 =
      (A - B) * (-(invOfUnit A 1 * invOfUnit B 1)) := by
  have hAI := mul_invOfUnit A 1 hA
  have hBI := mul_invOfUnit B 1 hB
  calc
    _ = (B * invOfUnit B 1) * invOfUnit A 1 -
        (A * invOfUnit A 1) * invOfUnit B 1 := by rw [hAI, hBI]; ring
    _ = _ := by ring

private theorem agree_inv {n : ℕ} {A B : PowerSeries R}
    (hA : constantCoeff A = 1) (hB : constantCoeff B = 1)
    (h : Agree n A B) : Agree n (invOfUnit A 1) (invOfUnit B 1) := by
  apply (agree_iff _ _ _).mpr
  rw [inverse_difference A B hA hB]
  exact dvd_mul_of_dvd_left ((agree_iff _ _ _).mp h) _

private noncomputable def tail (e : ℕ → ℕ) (A : PowerSeries R) (n : ℕ) : R :=
  ∑ j ∈ Finset.range n, coeff j A *
    coeff (n - j) (invOfUnit A 1 ^ (e n * j))

private noncomputable def step (e : ℕ → ℕ) (A : PowerSeries R) : PowerSeries R :=
  mk fun n => if n ≤ 1 then 1 else -tail e A n

private theorem step_zero (e : ℕ → ℕ) (A : PowerSeries R) : constantCoeff (step e A) = 1 := by
  simp [step]

-- Positive outer degrees leave strictly lower degrees in every inverse power.
private theorem step_contract (e : ℕ → ℕ) {n : ℕ} {A B : PowerSeries R}
    (hA : constantCoeff A = 1) (hB : constantCoeff B = 1)
    (h : Agree n A B) : Agree (n + 1) (step e A) (step e B) := by
  intro k hk
  simp only [step, coeff_mk]
  split_ifs with hk1
  · rfl
  · congr 1
    apply Finset.sum_congr rfl
    intro j hj
    have hjk := Finset.mem_range.mp hj
    by_cases hj0 : j = 0
    · subst j
      simp [show k ≠ 0 by omega]
    · rw [h j (by omega), agree_pow (agree_inv hA hB h) _ (k - j) (by omega)]

private noncomputable def approximation (e : ℕ → ℕ) : ℕ → PowerSeries R
  | 0 => 1
  | d + 1 => step e (approximation e d)

private theorem approximation_zero (e : ℕ → ℕ) (d : ℕ) :
    constantCoeff (approximation (R := R) e d) = 1 := by
  cases d with
  | zero => simp [approximation]
  | succ d => exact step_zero _ _

private theorem approximation_stable (e : ℕ → ℕ) {d s : ℕ} (h : d ≤ s) :
    Agree d (approximation (R := R) e d) (approximation e s) := by
  induction d generalizing s with
  | zero => intro k hk; omega
  | succ d ih =>
    cases s with
    | zero => omega
    | succ s =>
      exact step_contract e (approximation_zero e d) (approximation_zero e s) (ih (by omega))

noncomputable def a (e : ℕ → ℕ) (n : ℕ) : ℤ := coeff n (approximation e (n + 1))

noncomputable def generatingSeries (e : ℕ → ℕ) : PowerSeries ℤ := mk (a e)

private theorem generating_agree (e : ℕ → ℕ) (d : ℕ) :
    Agree d (generatingSeries e) (approximation e d) := by
  intro n hn
  simpa only [generatingSeries, coeff_mk, a] using
    approximation_stable (R := ℤ) e (by omega : n + 1 ≤ d) n (by omega)

private theorem generating_fixed (e : ℕ → ℕ) : generatingSeries e = step e (generatingSeries e) := by
  have h0 : constantCoeff (generatingSeries e) = 1 := by
    rw [← coeff_zero_eq_constantCoeff, generating_agree e 1 0 (by omega),
      coeff_zero_eq_constantCoeff, approximation_zero]
  ext n
  exact (generating_agree e (n + 2) n (by omega)).trans
    (step_contract e h0 (approximation_zero e (n + 1))
      (generating_agree e (n + 1)) n (by omega)).symm

-- The outer degree n contributes a_n with multiplier one; all larger degrees vanish.
private theorem coeff_diagonal (A : PowerSeries R) (e n : ℕ) :
    coeff n (A.subst (X * invOfUnit A 1 ^ e)) =
      coeff n A + ∑ j ∈ Finset.range n,
        coeff j A * coeff (n - j) (invOfUnit A 1 ^ (e * j)) := by
  have hz : constantCoeff (X * invOfUnit A 1 ^ e) = 0 := by simp
  rw [coeff_subst' (.of_constantCoeff_zero hz)]
  have ht (j : ℕ) :
      coeff j A • coeff n ((X * invOfUnit A 1 ^ e) ^ j) =
        if j ≤ n then coeff j A * coeff (n - j) (invOfUnit A 1 ^ (e * j)) else 0 := by
    rw [mul_pow, ← pow_mul, coeff_X_pow_mul']
    split_ifs <;> simp [smul_eq_mul]
  simp_rw [ht]
  rw [finsum_eq_sum_of_support_subset (s := Finset.range (n + 1))]
  · rw [Finset.sum_range_succ]
    have he : coeff n A * coeff (n - n) (invOfUnit A 1 ^ (e * n)) = coeff n A := by
      simp
    simp only [le_refl, if_true, he]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [if_pos (by have := Finset.mem_range.mp hj; omega)]
  · intro j hj
    simp only [Function.mem_support, ne_eq] at hj
    have hjn : j ≤ n := by
      by_contra h
      simp [h] at hj
    exact Finset.mem_range.mpr (by omega)


private theorem equation_iff (e : ℕ → ℕ) (A : PowerSeries R) :
    (coeff 0 A = 1 ∧ coeff 1 A = 1 ∧ ∀ n : ℕ, 1 < n →
      coeff n (A.subst (X * invOfUnit A 1 ^ (e n))) = 0) ↔
      A = step e A := by
  constructor
  · rintro ⟨h0, h1, he⟩
    ext n
    simp only [step, coeff_mk]
    split_ifs with hn
    · have h : n = 0 ∨ n = 1 := by omega
      rcases h with rfl | rfl <;> assumption
    · have h := he n (by omega)
      rw [coeff_diagonal] at h
      exact eq_neg_of_add_eq_zero_left h
  · intro hf
    have hc (n : ℕ) := congrArg (coeff n) hf
    refine ⟨?_, ?_, ?_⟩
    · simpa [step] using hc 0
    · simpa [step] using hc 1
    · intro n hn
      rw [coeff_diagonal]
      have h := hc n
      simp only [step, coeff_mk, if_neg (by omega : ¬ n ≤ 1)] at h
      change coeff n A + tail e A n = 0
      rw [h, neg_add_cancel]

theorem generating_equation (e : ℕ → ℕ) : coeff 0 (generatingSeries e) = 1 ∧
    coeff 1 (generatingSeries e) = 1 ∧ ∀ n : ℕ, 1 < n →
      coeff n ((generatingSeries e).subst
        (X * invOfUnit (generatingSeries e) 1 ^ (e n))) = 0 :=
  (equation_iff e _).mpr (generating_fixed e)

private theorem fixed_unique (e : ℕ → ℕ) {A B : PowerSeries R}
    (hA : A = step e A) (hB : B = step e B) : A = B := by
  have hA0 : constantCoeff A = 1 := by rw [hA, step_zero]
  have hB0 : constantCoeff B = 1 := by rw [hB, step_zero]
  have ha : ∀ n, Agree n A B := by
    intro n
    induction n with
    | zero => intro k hk; omega
    | succ n ih => simpa only [← hA, ← hB] using step_contract e hA0 hB0 ih
  ext n
  exact ha (n + 1) n (by omega)

theorem generating_unique (e : ℕ → ℕ) (B : PowerSeries ℤ) (h0 : coeff 0 B = 1)
    (h1 : coeff 1 B = 1)
    (he : ∀ n : ℕ, 1 < n →
      coeff n (B.subst (X * invOfUnit B 1 ^ (e n))) = 0) :
    B = generatingSeries e :=
  fixed_unique e ((equation_iff e B).mp ⟨h0, h1, he⟩) (generating_fixed e)


private theorem unit_shift (U : (PowerSeries ℤ)ˣ) (i : ℤ) :
    (↑(U ^ (i - 1)) : PowerSeries ℤ) * (U : PowerSeries ℤ) = ↑(U ^ i) := by
  simpa using (congrArg (fun u : (PowerSeries ℤ)ˣ => (u : PowerSeries ℤ))
    (zpow_add U (i - 1) 1)).symm

-- Unit cancellation extends the derivative rule to negative integer exponents.
private theorem unit_derivative (U : (PowerSeries ℤ)ˣ) (N : ℤ) :
    derivative ℤ (↑(U ^ N) : PowerSeries ℤ) =
      C N * ((↑(U ^ (N - 1)) : PowerSeries ℤ) * derivative ℤ (U : PowerSeries ℤ)) := by
  induction N using Int.induction_on with
  | zero => simp
  | succ N ih =>
    have he : (↑(U ^ ((N : ℤ) + 1)) : PowerSeries ℤ) =
        ↑(U ^ (N : ℤ)) * (U : PowerSeries ℤ) := by
      simpa using (unit_shift U ((N : ℤ) + 1)).symm
    rw [he, (derivative ℤ).leibniz, ih]
    simp only [smul_eq_mul, Int.add_sub_cancel, map_add, map_one]
    linear_combination C (N : ℤ) * derivative ℤ (U : PowerSeries ℤ) * unit_shift U N
  | pred N ih =>
    have he := congrArg (derivative ℤ) (unit_shift U (-(N : ℤ)))
    rw [(derivative ℤ).leibniz, ih] at he
    simp only [smul_eq_mul] at he
    apply U.isUnit.mul_right_cancel
    simp only [map_sub, map_one]
    linear_combination he -
      (C (-(N : ℤ)) - 1) * derivative ℤ (U : PowerSeries ℤ) *
        unit_shift U (-(N : ℤ) - 1)

theorem power_coefficient_identity (U : (PowerSeries ℤ)ˣ) (N : ℤ)
    (j : ℕ) (hj : 0 < j) :
    (j : ℤ) * coeff j (↑(U ^ N) : PowerSeries ℤ) =
      N * coeff (j - 1) ((↑(U ^ (N - 1)) : PowerSeries ℤ) *
        derivative ℤ (U : PowerSeries ℤ)) := by
  have h := congrArg (coeff (j - 1)) (unit_derivative U N)
  rw [coeff_derivative, Nat.sub_add_cancel hj, coeff_C_mul] at h
  have hjcast : ((j - 1 : ℕ) : ℤ) + 1 = j := by omega
  simpa only [hjcast, mul_comm] using h

-- If m has fewer factors of p than n, subtraction preserves its exact multiplicity.
private theorem sub_factorization (p n m : ℕ) (hp : p.Prime)
    (hm : 0 < m) (hmn : m < n) (hlt : m.factorization p < n.factorization p) :
    (n - m).factorization p = m.factorization p := by
  have hn0 : n ≠ 0 := by omega
  have hm0 : m ≠ 0 := by omega
  have hj0 : n - m ≠ 0 := by omega
  apply Nat.le_antisymm
  · by_contra h
    have hj : p ^ (m.factorization p + 1) ∣ n - m :=
      (hp.pow_dvd_iff_le_factorization hj0).mpr (by omega)
    have hn : p ^ (m.factorization p + 1) ∣ n :=
      (hp.pow_dvd_iff_le_factorization hn0).mpr hlt
    have hd : p ^ (m.factorization p + 1) ∣ m := by
      simpa only [Nat.sub_sub_self (by omega : m ≤ n)] using Nat.dvd_sub hn hj
    have := (hp.pow_dvd_iff_le_factorization hm0).mp hd
    omega
  · apply (hp.pow_dvd_iff_le_factorization hj0).mp
    exact Nat.dvd_sub
      ((hp.pow_dvd_iff_le_factorization hn0).mpr (by omega))
      ((hp.pow_dvd_iff_le_factorization hm0).mpr le_rfl)

-- The low-multiplicity case uses the power coefficient; the other case uses induction.
private theorem summand_dvd (n m k E b c : ℕ)
    (hm : 0 < m) (hmn : m < n) (he : n ^ k ∣ E)
    (hb : m ^ k ∣ b) (hc : E * m ∣ (n - m) * c) : n ^ k ∣ b * c := by
  by_cases hb0 : b = 0
  · simp [hb0]
  by_cases hc0 : c = 0
  · simp [hc0]
  have hn0 : n ≠ 0 := by omega
  have hm0 : m ≠ 0 := by omega
  have hj0 : n - m ≠ 0 := by omega
  have he0 : E ≠ 0 := by
    intro h
    rw [h, zero_mul, zero_dvd_iff] at hc
    exact (mul_ne_zero hj0 hc0) hc
  apply (Nat.factorization_prime_le_iff_dvd (pow_ne_zero k hn0)
    (mul_ne_zero hb0 hc0)).mp
  intro p hp
  simp only [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
    Nat.factorization_mul hb0 hc0, Finsupp.add_apply]
  by_cases hlt : m.factorization p < n.factorization p
  · have hsub := sub_factorization p n m hp hm hmn hlt
    have hE := (Nat.factorization_le_iff_dvd (pow_ne_zero k hn0) he0).mpr he p
    have hC := (Nat.factorization_le_iff_dvd (mul_ne_zero he0 hm0)
      (mul_ne_zero hj0 hc0)).mpr hc p
    simp only [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul] at hE
    simp only [Nat.factorization_mul he0 hm0, Nat.factorization_mul hj0 hc0,
      Finsupp.add_apply, hsub] at hC
    omega
  · have hB := (Nat.factorization_le_iff_dvd (pow_ne_zero k hm0) hb0).mpr hb p
    simp only [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul] at hB
    have := Nat.mul_le_mul_left k (by omega : n.factorization p ≤ m.factorization p)
    omega

private theorem inverse_power_dvd (A : PowerSeries ℤ) (hA : constantCoeff A = 1)
    (N j : ℕ) (hj : 0 < j) :
    (N : ℤ) ∣ (j : ℤ) * coeff j (invOfUnit A 1 ^ N) := by
  let U := Units.mkOfMulEqOne (invOfUnit A 1) A (invOfUnit_mul A 1 hA)
  have h := power_coefficient_identity U (N : ℤ) j hj
  have hd : (N : ℤ) ∣ (j : ℤ) * coeff j (↑(U ^ (N : ℤ)) : PowerSeries ℤ) :=
    ⟨_, h⟩
  simpa [U] using hd

theorem index_power_divisibility (e : ℕ → ℕ) (k : ℕ)
    (he : ∀ n : ℕ, n ^ k ∣ e n) (n : ℕ) (hn : 1 ≤ n) :
    (n : ℤ) ^ k ∣ a e n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn1 : n = 1
    · subst n
      simp
    have hn2 : 1 < n := by omega
    have hrec : a e n = -tail e (generatingSeries e) n := by
      have h := congrArg (coeff n) (generating_fixed e)
      simpa only [generatingSeries, coeff_mk, step,
        if_neg (by omega : ¬ n ≤ 1)] using h
    rw [hrec]
    apply dvd_neg.mpr
    apply Finset.dvd_sum
    intro m hm
    have hmn := Finset.mem_range.mp hm
    by_cases hm0 : m = 0
    · subst m
      simp [show n ≠ 0 by omega]
    · have hA : constantCoeff (generatingSeries e) = 1 := by
        simpa only [coeff_zero_eq_constantCoeff] using (generating_equation e).1
      have hd := inverse_power_dvd (generatingSeries e) hA (e n * m) (n - m) (by omega)
      have hc : e n * m ∣ (n - m) *
          (coeff (n - m) (invOfUnit (generatingSeries e) 1 ^ (e n * m))).natAbs := by
        simpa only [Int.natAbs_mul, Int.natAbs_natCast] using Int.natCast_dvd.mp hd
      have hb : m ^ k ∣ (a e m).natAbs := by
        apply Int.natCast_dvd.mp
        simpa only [Nat.cast_pow] using ih m hmn (by omega)
      have hs := summand_dvd n m k (e n) (a e m).natAbs
        (coeff (n - m) (invOfUnit (generatingSeries e) 1 ^ (e n * m))).natAbs
        (by omega) hmn (he n) hb hc
      rw [← Nat.cast_pow]
      apply Int.natCast_dvd.mpr
      simpa only [Int.natAbs_mul, generatingSeries, coeff_mk] using hs

theorem hanna_conjecture_a300732 (n : ℕ) (hn : 1 ≤ n) :
    (n : ℤ) ∣ a (fun m => 2 * m) n := by
  simpa only [pow_one] using index_power_divisibility (fun m => 2 * m) 1
    (fun m => by simpa only [pow_one] using dvd_mul_left m 2) n hn

theorem hanna_conjecture_a300733 (n : ℕ) (hn : 1 ≤ n) :
    (n : ℤ) ∣ a (fun m => 3 * m) n := by
  simpa only [pow_one] using index_power_divisibility (fun m => 3 * m) 1
    (fun m => by simpa only [pow_one] using dvd_mul_left m 3) n hn

theorem hanna_conjecture_a292394 (n : ℕ) (hn : 1 ≤ n) :
    (n : ℤ) ^ 2 ∣ a (fun m => m ^ 2) n :=
  index_power_divisibility (fun m => m ^ 2) 2 (fun _ => dvd_rfl) n hn

theorem hanna_conjecture_a300734 (n : ℕ) (hn : 1 ≤ n) :
    (n : ℤ) ^ 2 ∣ a (fun m => 2 * m ^ 2) n :=
  index_power_divisibility (fun m => 2 * m ^ 2) 2 (fun m => dvd_mul_left (m ^ 2) 2) n hn

theorem agreement_a266489 (n : ℕ) :
    a (fun m => m) n = NegativePowerDiagonalModPrime.a 2 n := by
  have h := generating_equation (fun m => m)
  have he : generatingSeries (fun m => m) =
      NegativePowerDiagonalModPrime.generatingSeries 2 := by
    apply NegativePowerDiagonalModPrime.generating_unique 2 _ h.1 h.2.1
    intro m hm
    have hexp : (2 - 1) * (m - 1) + 1 = m := by omega
    simpa only [hexp] using h.2.2 m hm
  simpa only [generatingSeries, NegativePowerDiagonalModPrime.generatingSeries,
    coeff_mk] using congrArg (coeff n) he

theorem hanna_conjecture_a266489 (n : ℕ) (hn : 1 ≤ n) :
    (n : ℤ) ∣ NegativePowerDiagonalModPrime.a 2 n := by
  rw [← agreement_a266489]
  simpa only [pow_one] using index_power_divisibility (fun m => m) 1
    (fun m => by simp only [pow_one, dvd_refl]) n hn

#print axioms a
#print axioms generatingSeries
#print axioms generating_equation
#print axioms generating_unique
#print axioms power_coefficient_identity
#print axioms index_power_divisibility
#print axioms hanna_conjecture_a300732
#print axioms hanna_conjecture_a300733
#print axioms hanna_conjecture_a292394
#print axioms hanna_conjecture_a300734
#print axioms agreement_a266489
#print axioms hanna_conjecture_a266489

end D5.S1.Recurrence.Residue.DiagonalVanishingIndexDivisibility
