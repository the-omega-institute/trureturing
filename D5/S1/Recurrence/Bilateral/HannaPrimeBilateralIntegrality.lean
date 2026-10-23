/- GID: D5/S1/Recurrence/Bilateral/HannaPrimeBilateralIntegrality
   generality: G
   mirror-B: D5/B/S1/Recurrence/Bilateral/HannaPrimeBilateralIntegrality
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Bilateral cancellation and Frobenius characterize prime integral solutions. -/

/-
admission_basis: open-problem-resolution (#18831; Proved)
escape_witness: none
Direct frozen dependencies (declaration statement_id, not module pins):
D5/S1/Recurrence/Bilateral/BilateralProductModFour.symmetric_pair
  sha256:ec2ce3acb9c693250b8c1744ab57b32dfa6f8e22a0268b5edce1f5d12206504e
D5/S1/Recurrence/Residue/NegativePowerDiagonalModPrime.inverse_difference
  sha256:de95009be8a3f6b4675b86334f6afe96cbcfe4cc07412482ab82bb4431065824
D5/S1/Recurrence/Bilateral/BilateralProductModFour.ofSeries_inverse
  sha256:6c9f94677b0c4cdb1baddca0a042a6a268121bc80d543b562f3b0b0d63f3a0de
D5/S1/Recurrence/Invariants/CubicFifteenSubstitutionParity.prime_power_subst
  sha256:4b665513911f58443c7679757dc619d66730344174351ea1f23cedc92766f795
D5/S1/Recurrence/Residue/ContinuedFractionOddSquare.inverse_one
  sha256:8ca570fd0828804ac28c81ca1d9d398e6ba7713278e53cc37fc6ceef601ca498
D5/S1/Recurrence/Residue/ContinuedFractionOddSquare.Agree
  sha256:0cfab65b024a4c7d2f5bc7d6e6be07138094ddfd564eb763453963e9a8086943
D5/S1/Recurrence/Residue/ContinuedFractionOddSquare.agree_inv
  sha256:de19fffc8f3d74728f66568fc7247763986c9362a7f4436c196537010031ee4d
D5/S1/Recurrence/Invariants/PowerSeriesNormalizedContraction.exists_unique_fixed
  sha256:bd62df5aa141eaff1ceec9e8af00309b4a8e194b4354ad180a51862599cef981
D5/S1/Recurrence/Invariants/UnitReversionSquareParity.Agree
  sha256:76d7ce5ef0f66968d4516f93f05e27e9125f8f29944ffacca0d95b580f786d34
D5/S1/Recurrence/Invariants/UnitReversionSquareParity.agree_iff
  sha256:b8236ebf1419cfde429c1b9ba55a7c2c22195bd600685feda80fdbf0688cd6d6
D5/S1/Recurrence/Residue/ContinuedFractionOddSquare.map_inverse
  sha256:514cac370bcaca2ab772ee68d2f70f9768dcdff53acb4e2a4df3e5420df06e90
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19820
The literal Laurent-series summand and finite-window predicate express OEIS A380681.
The claim restricts p to p >= 2; nonpositive parameters are outside its scope.
utility: none because no declaration certifies a finite instance or enumeration.
negative_factorization: proof_shape: bind-only; consumers: term_normalization
ofSeries_inverse: proof_shape: bind-only; consumers: term_normalization
term_normalization: proof_shape: bind-only; consumers: isSolution_iff
normalized_outside: proof_shape: bind-only; consumers: finite_window
finite_window: proof_shape: bind-only; consumers: isSolution_iff, psi_one_zero, psi_difference_dvd, psi_constant, psi_zero_first, prime_divisibility_of_pairing, low_inverse_equation
isSolution_iff: proof_shape: bind-only; consumers: step_fixed_iff, low_inverse_equation
negative_binomial_coeff: proof_shape: bind-only; consumers: negative_expansion
inverse_power_subst: proof_shape: bind-only; consumers: negative_expansion
shifted_subst_coeff: proof_shape: bind-only; consumers: negative_expansion
negative_expansion: proof_shape: bind-only; consumers: psi_one_zero
positive_expansion: proof_shape: bind-only; consumers: psi_one_zero
psi_one_zero: proof_shape: content; consumers: result
contracting_series_fixedpoint: proof_shape: bind-only; consumers: exists_solution
inverse_difference_dvd: proof_shape: bind-only; consumers: normalized_difference_dvd
shifted_difference_dvd: proof_shape: bind-only; consumers: normalized_difference_dvd
normalized_difference_dvd: proof_shape: bind-only; consumers: psi_difference_dvd
exceptional_difference_dvd: proof_shape: bind-only; consumers: psi_difference_dvd
psi_difference_dvd: proof_shape: bind-only; consumers: psi_first, step_contract
psi_constant: proof_shape: bind-only; consumers: step_fixed_iff
psi_zero_first: proof_shape: bind-only; consumers: psi_first
psi_first: proof_shape: bind-only; consumers: step_constant
step_constant: proof_shape: bind-only; consumers: step_fixed_iff
step_contract: proof_shape: bind-only; consumers: exists_solution, prime_solution_integral
step_fixed_iff: proof_shape: bind-only; consumers: exists_solution, prime_solution_integral
exists_solution: proof_shape: content; consumers: result
normalizedTerm_map: proof_shape: bind-only; consumers: psi_map
psi_map: proof_shape: bind-only; consumers: prime_divisibility_of_pairing, step_preserves_integral
normalizedTerm_frobenius: proof_shape: bind-only; consumers: prime_divisibility_of_pairing
prime_divisibility_of_pairing: proof_shape: bind-only; consumers: step_preserves_integral
binomial_obstruction: proof_shape: bind-only; consumers: integral_implies_prime
composite_minFac_lt: proof_shape: bind-only; consumers: integral_implies_prime
normalized_tail_dvd: proof_shape: bind-only; consumers: low_inverse_equation
low_inverse_equation: proof_shape: bind-only; consumers: low_power_equation
low_power_equation: proof_shape: bind-only; consumers: low_differential_equation
derivative_order: proof_shape: bind-only; consumers: low_differential_equation
low_differential_equation: proof_shape: bind-only; consumers: low_coefficient_recurrence
low_coefficient_recurrence: proof_shape: bind-only; consumers: factorial_coefficient_identity
factorial_coefficient_identity: proof_shape: content; consumers: integral_implies_prime
integral_implies_prime: proof_shape: content; consumers: result
step_preserves_integral: proof_shape: bind-only; consumers: prime_solution_integral
prime_solution_integral: proof_shape: content; consumers: result
result: proof_shape: content; consumers: settling result
-/

import Mathlib.RingTheory.PowerSeries.Derivative
import D5.S1.Recurrence.Bilateral.BilateralProductModFour
import D5.S1.Recurrence.Invariants.CubicFifteenSubstitutionParity
import D5.S1.Recurrence.Invariants.PowerSeriesNormalizedContraction
import D5.S1.Recurrence.Invariants.UnitReversionSquareParity
import Mathlib.RingTheory.PowerSeries.Binomial
import D5.S1.Recurrence.Residue.ContinuedFractionOddSquare
import D5.S1.Recurrence.Residue.NegativePowerDiagonalModPrime
set_option autoImplicit false
namespace D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality
open PowerSeries
/-- The summand `(-1)^n * x^(p*n) * (F(x) + x^n)^(p*n)` as a Laurent series (integer exponents). -/
noncomputable def term (p : ℕ) (F : PowerSeries ℚ) (n : ℤ) : LaurentSeries ℚ :=
  let x : LaurentSeries ℚ := HahnSeries.ofPowerSeries ℤ ℚ X
  let G : LaurentSeries ℚ := HahnSeries.ofPowerSeries ℤ ℚ F
  (-1 : LaurentSeries ℚ) ^ n * x ^ ((p : ℤ) * n) * (G + x ^ n) ^ ((p : ℤ) * n)
/-- "F(x) satisfies p*x = Sum_{n=-oo..+oo} (-1)^n * x^(p*n) * (F(x) + x^n)^(p*n) with F(0) = 1", the
bilateral sum read coefficientwise through the symmetric windows [-K, K], K > N. -/
def IsSolution (p : ℕ) (F : PowerSeries ℚ) : Prop :=
  constantCoeff F = 1 ∧
    ∀ N K : ℕ, N + 1 ≤ K →
      (∑ j ∈ Finset.Icc (-(K : ℤ)) K, (term p F j).coeff (N : ℤ)) = if N = 1 then (p : ℚ) else 0
/-- OEIS A380681–A380686 (P. D. Hanna), conjecture: "if F(x) satisfies p*x = Sum_{n=-oo..+oo} (-1)^n *
x^(p*n) * (F(x) + x^n)^(p*n) with F(0) = 1 for some fixed integer p, then F(x) is an integer series in x
iff p is prime." Here p >= 2 (for p = 1 there is no solution). -/
def claim : Prop :=
  ∀ p : ℕ, 2 ≤ p →
    (∃ F, IsSolution p F) ∧
      ∀ F, IsSolution p F → ((∀ n, ∃ z : ℤ, coeff n F = z) ↔ p.Prime)
open PowerSeries
private noncomputable def normalizedTerm {R : Type*} [CommRing R]
    (p : ℕ) (F : PowerSeries R) (j : ℤ) : PowerSeries R :=
  if j = 0 then 1 else if 0 < j then
    (-1) ^ j.natAbs * X ^ (p * j.natAbs) * (F + X ^ j.natAbs) ^ (p * j.natAbs)
  else
    (-1) ^ j.natAbs * X ^ (p * j.natAbs * (j.natAbs - 1)) *
      invOfUnit (1 + X ^ j.natAbs * F) 1 ^ (p * j.natAbs)
private theorem negative_factorization {L : Type*} [Field L]
    (x u : L) (hx : x ≠ 0) (p m : ℕ) (hm : 1 ≤ m) :
    x ^ (-((p * m : ℕ) : ℤ)) * (u + x ^ (-(m : ℤ))) ^ (-((p * m : ℕ) : ℤ)) =
      x ^ (p * m * (m - 1)) * (1 + x ^ m * u)⁻¹ ^ (p * m) := by
  have he : u + x ^ (-(m : ℤ)) = x ^ (-(m : ℤ)) * (1 + x ^ m * u) := by
    rw [zpow_neg, zpow_natCast]
    field_simp
    ring
  rw [he, mul_zpow, ← zpow_mul]
  have hexp : -((p * m : ℕ) : ℤ) + -(m : ℤ) * -((p * m : ℕ) : ℤ) =
      ((p * m * (m - 1) : ℕ) : ℤ) := by
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hm]
    push_cast
    ring
  rw [← mul_assoc, ← zpow_add₀ hx, hexp]
  simp only [zpow_natCast, zpow_neg, inv_pow]
private theorem ofSeries_inverse (B : PowerSeries ℚ) (hB : constantCoeff B = 1) :
    HahnSeries.ofPowerSeries ℤ ℚ (invOfUnit B 1) =
      (HahnSeries.ofPowerSeries ℤ ℚ B)⁻¹ := by
  rw [PowerSeries.invOfUnit_eq' B 1 hB]
  apply D5.S1.Recurrence.Bilateral.BilateralProductModFour.ofSeries_inverse
  rw [hB]
  norm_num
private theorem term_normalization (p : ℕ) (F : PowerSeries ℚ) (j : ℤ) :
    term p F j = HahnSeries.ofPowerSeries ℤ ℚ (normalizedTerm p F j) := by
  let E := HahnSeries.ofPowerSeries ℤ ℚ
  have hx : E X ≠ 0 := by
    intro h
    apply PowerSeries.X_ne_zero (R := ℚ)
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ℚ)
    exact h.trans (map_zero E).symm
  cases j with
  | ofNat m =>
    change term p F (m : ℤ) = E (normalizedTerm p F (m : ℤ))
    by_cases hm : m = 0
    · subst m
      simp [term, normalizedTerm, E]
    · have hp : (0 : ℤ) < m := by
        exact Int.natCast_pos.mpr (Nat.pos_of_ne_zero hm)
      have hn : (m : ℤ) ≠ 0 := by
        exact Ne.symm (Int.ne_of_lt hp)
      simp only [normalizedTerm, hn, ite_false, hp, ite_true,
        Int.natAbs_natCast, term, ← Nat.cast_mul, zpow_natCast,
        map_mul, map_pow, map_neg, map_one, map_add, E]
  | negSucc m =>
    change term p F (-((m+1 : ℕ) : ℤ)) = E (normalizedTerm p F (-((m+1 : ℕ) : ℤ)))
    have hp : ¬ (0 : ℤ) < -((m+1 : ℕ) : ℤ) := by
      exact not_lt_of_ge (neg_nonpos.mpr (Int.natCast_nonneg (m+1)))
    have hn : -((m+1 : ℕ) : ℤ) ≠ 0 := by
      exact Ne.symm (not_eq_of_beq_eq_false rfl)
    simp only [normalizedTerm, hn, ite_false, hp, Int.natAbs_neg, Int.natAbs_natCast]
    unfold term
    rw [show (p : ℤ) * -((m + 1 : ℕ) : ℤ) = -((p * (m+1) : ℕ) : ℤ) by push_cast; ring]
    rw [mul_assoc, negative_factorization _ _ hx p (m+1) (by omega)]
    simp only [map_mul, map_pow, map_neg, map_one]
    rw [ofSeries_inverse _ (by simp)]
    simp only [map_add, map_one, map_mul, map_pow, E, zpow_neg, zpow_natCast,
      ← inv_pow, inv_neg, inv_one]
    ring
private theorem normalized_outside {R : Type*} [CommRing R]
    (p : ℕ) (hp : 1 ≤ p) (F : PowerSeries R) (N : ℕ) (j : ℤ)
    (hj : j < -((N + 1 : ℕ) : ℤ) ∨ ((N + 1 : ℕ) : ℤ) < j) :
    coeff N (normalizedTerm p F j) = 0 := by
  have hm : N + 1 < j.natAbs := by
    rcases hj with hj | hj
    · simpa only [Int.natAbs_natCast, Int.natAbs_neg] using
        Int.natAbs_lt_natAbs_of_nonneg_of_lt (Int.natCast_nonneg (N+1))
          (show ((N+1 : ℕ) : ℤ) < -j by simpa only [neg_neg] using neg_lt_neg hj)
    · simpa only [Int.natAbs_natCast] using
        Int.natAbs_lt_natAbs_of_nonneg_of_lt (Int.natCast_nonneg (N+1)) hj
  unfold normalizedTerm
  rw [if_neg (by omega : j ≠ 0)]
  split_ifs
  · apply X_pow_dvd_iff.mp (dvd_mul_of_dvd_left
      (dvd_mul_left (X ^ (p * j.natAbs)) _) _) N
    nlinarith
  · apply X_pow_dvd_iff.mp (dvd_mul_of_dvd_left
      (dvd_mul_left (X ^ (p * j.natAbs * (j.natAbs - 1))) _) _) N
    have hm' : 1 ≤ j.natAbs - 1 := by
      exact Nat.le_sub_one_of_lt (lt_of_le_of_lt (Nat.succ_le_succ (Nat.zero_le N)) hm)
    calc N < j.natAbs := by omega
         _ ≤ p * j.natAbs := by nlinarith
         _ ≤ p * j.natAbs * (j.natAbs - 1) := by
           simpa using Nat.mul_le_mul_left (p * j.natAbs) hm'
private noncomputable def psi {R : Type*} [CommRing R] (p : ℕ) (F : PowerSeries R) :
    PowerSeries R := mk fun N =>
  ∑ j ∈ Finset.Icc (-((N + 1 : ℕ) : ℤ)) (N + 1), coeff N (normalizedTerm p F j)
private theorem finite_window {R : Type*} [CommRing R]
    (p : ℕ) (hp : 1 ≤ p) (F : PowerSeries R) (N K : ℕ) (hNK : N + 1 ≤ K) :
    coeff N (psi p F) =
      ∑ j ∈ Finset.Icc (-(K : ℤ)) K, coeff N (normalizedTerm p F j) := by
  simp only [psi, coeff_mk]
  apply Finset.sum_subset
  · intro j hj
    simp only [Finset.mem_Icc] at hj ⊢
    omega
  · intro j _ hnot
    apply normalized_outside p hp F N j
    simp only [Finset.mem_Icc] at hnot
    omega
private theorem isSolution_iff (p : ℕ) (hp : 1 ≤ p) (F : PowerSeries ℚ) :
    IsSolution p F ↔ constantCoeff F = 1 ∧ psi p F = C (p : ℚ) * X := by
  have he (N K : ℕ) (hNK : N + 1 ≤ K) :
      (∑ j ∈ Finset.Icc (-(K : ℤ)) K, (term p F j).coeff (N : ℤ)) =
        coeff N (psi p F) := by
    rw [finite_window p hp F N K hNK]
    apply Finset.sum_congr rfl
    intro j _
    rw [term_normalization, HahnSeries.ofPowerSeries_apply_coeff]
  constructor
  · rintro ⟨h0, hs⟩
    refine ⟨h0, ?_⟩
    ext N
    rw [← he N (N+1) le_rfl, hs N (N+1) le_rfl]
    simp [coeff_C_mul, coeff_X]
  · rintro ⟨h0, hs⟩
    refine ⟨h0, fun N K hNK => ?_⟩
    rw [he N K hNK, hs]
    simp [coeff_C_mul, coeff_X]
open PowerSeries Finset
section Pairing
variable {R : Type*} [CommRing R]
private theorem negative_binomial_coeff (r b : ℕ) (hr : 1 ≤ r) :
    coeff b (binomialSeries R (-(r : ℤ))) =
      (-1 : R) ^ b * (Nat.choose (r + b - 1) b : R) := by
  rw [binomialSeries_coeff, Ring.choose_neg]
  have he : (r : ℤ) + b - 1 = ((r + b - 1 : ℕ) : ℤ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ r + b)]
    push_cast
    rfl
  rw [he, Ring.choose_natCast]
  simp [Units.smul_def, zsmul_eq_mul, Int.cast_negOnePow_natCast]
private theorem inverse_power_subst (r : ℕ) (F : PowerSeries R) (hr : 1 ≤ r) :
    (binomialSeries R (-(r : ℤ))).subst (X ^ r * F) =
      invOfUnit (1 + X ^ r * F) 1 ^ r := by
  have ht : HasSubst (X ^ r * F) := .of_constantCoeff_zero (by
    change constantCoeff ((X : PowerSeries R)^r*F) = 0
    simp [show r ≠ 0 by omega])
  have h := congrArg (substAlgHom (R := R) ht)
    (binomialSeries_add (A := R) (-(r : ℤ)) (r : ℤ))
  simp only [neg_add_cancel, binomialSeries_zero, map_one, map_mul,
    binomialSeries_nat, map_pow, map_add, substAlgHom_X] at h
  have hi : (1 + X ^ r * F) ^ r * invOfUnit (1 + X ^ r * F) 1 ^ r = 1 := by
    rw [← mul_pow, mul_invOfUnit _ 1 (by simp [show r ≠ 0 by omega]), one_pow]
  rw [← coe_substAlgHom ht]
  change substAlgHom (R := R) ht (binomialSeries R (-(r : ℤ))) = _
  calc
    _ = substAlgHom ht (binomialSeries R (-(r : ℤ))) *
        ((1 + X ^ r * F)^r * invOfUnit (1 + X ^ r * F) 1 ^ r) := by rw [hi, mul_one]
    _ = (substAlgHom ht (binomialSeries R (-(r : ℤ))) * (1 + X ^ r * F)^r) *
        invOfUnit (1 + X ^ r * F) 1 ^ r := by ring
    _ = _ := by rw [← h, one_mul]
private theorem shifted_subst_coeff (f F : PowerSeries R) (a r N d : ℕ) (hr : 1 ≤ r)
    (hd : N < a + r * d) :
    coeff N (X ^ a * f.subst (X ^ r * F)) =
      ∑ b ∈ range d, coeff b f * coeff N (X ^ (a + r * b) * F ^ b) := by
  by_cases ha : a ≤ N
  · rw [coeff_X_pow_mul', if_pos ha, coeff_subst' (.of_constantCoeff_zero
      (by
        change constantCoeff ((X : PowerSeries R)^r*F) = 0
        simp [show r ≠ 0 by omega]))]
    simp only [smul_eq_mul]
    have he : ∑ᶠ b : ℕ, coeff b f * coeff (N - a) ((X ^ r * F) ^ b) =
        ∑ b ∈ range d, coeff b f * coeff (N - a) ((X ^ r * F) ^ b) := by
      apply finsum_eq_sum_of_support_subset
      intro b hb
      apply mem_range.mpr
      by_contra hbd
      have hzero : coeff (N - a) ((X ^ r * F) ^ b) = 0 := by
        have hdiv : (X : PowerSeries R)^(r*b) ∣ (X^r*F)^b := by
          simpa only [mul_pow, ← pow_mul] using
            (dvd_mul_right (X ^ (r * b) : PowerSeries R) (F ^ b))
        apply X_pow_dvd_iff.mp hdiv (N-a)
        have hab : a + (N-a) = N := by
          exact Nat.add_sub_of_le ha
        have hbd' : d ≤ b := by
          exact Nat.le_of_not_lt hbd
        nlinarith [Nat.mul_le_mul_left r hbd']
      exact hb (by dsimp; rw [hzero, mul_zero])
    rw [he]
    apply sum_congr rfl
    intro b hb
    congr 1
    rw [mul_pow, ← pow_mul, coeff_X_pow_mul', coeff_X_pow_mul']
    by_cases hb' : r*b ≤ N-a
    · rw [if_pos hb', if_pos (by omega : a+r*b ≤ N)]
      simp only [Nat.sub_sub]
    · rw [if_neg hb', if_neg (by omega : ¬ a+r*b ≤ N)]
  · have hz : N < a := by exact Nat.lt_of_not_ge ha
    rw [coeff_X_pow_mul', if_neg ha]
    symm
    apply sum_eq_zero
    intro b hb
    rw [coeff_X_pow_mul', if_neg (by omega : ¬ a + r*b ≤ N), mul_zero]
private theorem negative_expansion (F : PowerSeries R) (N r : ℕ) (hr : 1 ≤ r) (hrN : r ≤ N+1) :
    coeff N (normalizedTerm 1 F (-(r : ℤ))) =
      ∑ b ∈ range (N+2-r),
        ((-1 : R) ^ (r+b) * (Nat.choose (r+b-1) b : R)) *
          coeff N (X ^ (r * (r+b-1)) * F ^ b) := by
  have hn : -(r : ℤ) ≠ 0 := by exact neg_ne_zero.mpr (Int.natCast_ne_zero_iff_pos.mpr hr)
  have hp : ¬ (0 : ℤ) < -(r : ℤ) := by
    exact not_lt_of_ge (neg_nonpos.mpr (Int.natCast_nonneg r))
  simp only [normalizedTerm, hn, ite_false, hp, Int.natAbs_neg, Int.natAbs_natCast, one_mul]
  have ha : N < r * (r-1) + r * (N+2-r) := by
    have hsub : r-1 + (N+2-r) = N+1 := by omega
    calc N < N+1 := by omega
         _ ≤ r * (N+1) := by nlinarith
         _ = _ := by rw [← mul_add, hsub]
  rw [mul_assoc, show (-1 : PowerSeries R)^r = C ((-1 : R)^r) by simp,
    coeff_C_mul, ← inverse_power_subst r F hr,
    shifted_subst_coeff _ F _ r N (N+2-r) hr ha, mul_sum]
  apply sum_congr rfl
  intro b hb
  rw [negative_binomial_coeff r b hr]
  have he : r * (r-1) + r*b = r * (r+b-1) := by
    have hh : r-1+b = r+b-1 := by exact (Nat.sub_add_comm hr).symm
    rw [← mul_add, hh]
  rw [he, pow_add]
  ring
private theorem positive_expansion (F : PowerSeries R) (N m : ℕ) (hm : 1 ≤ m) :
    coeff N (normalizedTerm 1 F (m : ℤ)) =
      ∑ b ∈ range (m+1),
        ((-1 : R)^m * (Nat.choose m b : R)) *
          coeff N (X ^ (m * (m-b+1)) * F^b) := by
  have hn : (m : ℤ) ≠ 0 := by
    exact Int.natCast_ne_zero_iff_pos.mpr hm
  have hp : (0 : ℤ) < m := by
    exact Int.natCast_pos.mpr hm
  simp only [normalizedTerm, hn, ite_false, hp, ite_true, Int.natAbs_natCast, one_mul]
  rw [add_pow, mul_sum, map_sum]
  apply sum_congr rfl
  intro b hb
  have he : (X : PowerSeries R)^m * (X^m)^(m-b) = X^(m*(m-b+1)) := by
    rw [← pow_mul, ← pow_add]
    congr 1
    ring
  have ht : (-1 : PowerSeries R)^m * X^m *
      (F^b * (X^m)^(m-b) * (Nat.choose m b : PowerSeries R)) =
      C ((-1:R)^m * (Nat.choose m b:R)) * X^(m*(m-b+1)) * F^b := by
    rw [show C ((-1:R)^m * (Nat.choose m b:R)) =
      (-1 : PowerSeries R)^m * (Nat.choose m b : PowerSeries R) by simp]
    rw [← he]
    ring
  rw [ht, mul_assoc, coeff_C_mul]
end Pairing
open PowerSeries Finset
private theorem psi_one_zero {R : Type*} [CommRing R] (F : PowerSeries R) : psi 1 F = 0 := by
  ext N
  let P (m b : ℕ) : R := ((-1:R)^m * (Nat.choose m b : R)) *
    coeff N (X^(m*(m-b+1))*F^b)
  let Q (i b : ℕ) : R := ((-1:R)^(i+1+b) * (Nat.choose (i+b) b : R)) *
    coeff N (X^((i+1)*(i+b))*F^b)
  have hP (m : ℕ) : coeff N (normalizedTerm 1 F (m : ℤ)) =
      ∑ b ∈ range (m+1), P m b := by
    by_cases hm : m = 0
    · subst m
      simp [P, normalizedTerm]
    · exact positive_expansion F N m (by omega)
  have hQ (i : ℕ) (hi : i < N+1) :
      coeff N (normalizedTerm 1 F (-((i+1 : ℕ) : ℤ))) =
      ∑ b ∈ range (N+1-i), Q i b := by
    rw [negative_expansion F N (i+1) (by omega) (by omega)]
    have hd : N+2-(i+1) = N+1-i := by
      exact Nat.succ_sub_succ_eq_sub (N + 1) i
    simp only [hd]
    apply sum_congr rfl
    intro b hb
    simp only [Q, show i+1+b-1=i+b by omega]
  have hp0 : coeff N (normalizedTerm 1 F ((N+1 : ℕ) : ℤ)) = 0 := by
    simp only [normalizedTerm, Int.natCast_eq_zero, Nat.add_eq_zero_iff,
      Nat.add_one_ne_zero, ite_false, show (0 : ℤ) < (N+1 : ℕ) by omega, ite_true,
      Int.natAbs_natCast, one_mul]
    rw [mul_assoc, show (-1 : PowerSeries R)^(N+1) = C ((-1:R)^(N+1)) by simp,
      coeff_C_mul, coeff_X_pow_mul', if_neg (by omega), mul_zero]
  have hpair : (∑ m ∈ range (N+1), ∑ b ∈ range (m+1), P m b) =
      -(∑ i ∈ range (N+1), ∑ b ∈ range (N+1-i), Q i b) := by
    rw [sum_sigma', sum_sigma', ← sum_neg_distrib]
    refine sum_bij (fun a _ => Sigma.mk (a.1-a.2) a.2) ?_ ?_ ?_ ?_
    · rintro ⟨m,b⟩ ha
      simp only [mem_sigma, mem_range] at ha ⊢
      constructor <;> omega
    · rintro ⟨m,b⟩ ha ⟨m',b'⟩ hb he
      have h1 := congrArg (fun a : (Σ _ : ℕ, ℕ) => a.1) he
      have h2 := congrArg (fun a : (Σ _ : ℕ, ℕ) => a.2) he
      simp only [mem_sigma, mem_range] at ha hb
      dsimp at h1 h2
      have hm : m=m' := by omega
      have hb' : b=b' := by
        exact Nat.add_right_cancel (congrFun (congrArg HAdd.hAdd h2) N)
      subst m'; subst b'; rfl
    · rintro ⟨i,b⟩ hb
      refine ⟨⟨i+b,b⟩, ?_, ?_⟩
      · simp only [mem_sigma, mem_range] at hb ⊢
        constructor <;> omega
      · simp
    · rintro ⟨m,b⟩ ha
      simp only [mem_sigma, mem_range] at ha
      have hb : b ≤ m := by exact Nat.le_of_lt_succ ha.2
      have h1 : m-b+b=m := by exact Nat.sub_add_cancel hb
      have h2 : m-b+1+b=m+1 := by
        simpa only [Nat.add_right_comm] using congrArg (fun k : ℕ => k + 1) h1
      have h3 : (m-b+1)*(m-b+b) = m*(m-b+1) := by rw [h1, mul_comm]
      dsimp [P,Q]
      rw [h2, h3, h1, pow_succ]
      ring
  have he : coeff N (psi 1 F) =
      (∑ m ∈ range (N+1), ∑ b ∈ range (m+1), P m b) +
      (∑ i ∈ range (N+1), ∑ b ∈ range (N+1-i), Q i b) := by
    rw [finite_window 1 (by decide) F N (N+1) le_rfl, D5.S1.Recurrence.Bilateral.BilateralProductModFour.symmetric_pair, sum_add_distrib]
    have hpos : coeff N (normalizedTerm 1 F 0) +
        ∑ m ∈ range (N+1), coeff N (normalizedTerm 1 F (m+1)) =
        ∑ m ∈ range (N+1), coeff N (normalizedTerm 1 F (m : ℤ)) := by
      have hs := sum_range_succ' (fun m => coeff N (normalizedTerm 1 F (m : ℤ))) (N+1)
      rw [sum_range_succ, hp0, add_zero] at hs
      push_cast at hs
      linear_combination -hs
    rw [← add_assoc, hpos]
    congr 1
    · exact sum_congr rfl fun m _ => hP m
    · apply sum_congr rfl
      intro i hi
      rw [show -(i : ℤ) - 1 = -(i + 1 : ℤ) by omega]
      simpa only [Nat.cast_add, Nat.cast_one] using hQ i (mem_range.mp hi)
  rw [he, hpair]
  simp
open PowerSeries
private theorem contracting_series_fixedpoint {R : Type*} [CommRing R]
    (Phi : PowerSeries R → PowerSeries R)
    (hc : ∀ d (f g : PowerSeries R),
      (∀ n < d, coeff n f = coeff n g) →
      ∀ n < d+1, coeff n (Phi f) = coeff n (Phi g)) :
    ∃! f, Phi f = f := by
  let E : PowerSeries R → PowerSeries R := fun f => 1 + X * f
  let D : PowerSeries R → PowerSeries R := fun f => mk fun n => coeff (n+1) f
  have de (f : PowerSeries R) : D (E f) = f := by
    ext n
    simp [D,E]
  have e0 (f : PowerSeries R) : constantCoeff (E f) = 1 := by simp [E]
  have contract {d : ℕ} {f g : PowerSeries R} (hd : 1 ≤ d)
      (h : D5.S1.Recurrence.Invariants.UnitReversionSquareParity.Agree d f g) :
      D5.S1.Recurrence.Invariants.UnitReversionSquareParity.Agree (d+1)
        (E (Phi (D f))) (E (Phi (D g))) := by
    intro n hn
    cases n with
    | zero => simp [E, coeff_zero_eq_constantCoeff]
    | succ n =>
      have he := hc (d-1) (D f) (D g) (by
        intro k hk
        simpa only [D, coeff_mk] using h (k+1) (by omega)) n (by omega)
      simpa [E] using he
  obtain ⟨f,hf0,hf,unique⟩ :=
    D5.S1.Recurrence.Invariants.PowerSeriesNormalizedContraction.exists_unique_fixed
      (fun f => E (Phi (D f))) (fun f _ => e0 _)
      (fun hd _ _ h => contract hd h)
  refine ⟨D f, ?_, ?_⟩
  · have hh := congrArg D hf
    simpa only [de] using hh.symm
  · intro g hg
    have hencoded : E g = E (Phi (D (E g))) := by rw [de,hg]
    have hh := congrArg D (unique (E g) (e0 g) hencoded)
    simpa only [de] using hh
open PowerSeries Finset
section Linearization
variable {R : Type*} [CommRing R]
private theorem inverse_difference_dvd (A B : PowerSeries R) (d : ℕ)
    (hA : constantCoeff A = 1) (hB : constantCoeff B = 1)
    (hd : (X : PowerSeries R)^d ∣ A-B) :
    (X : PowerSeries R)^d ∣ invOfUnit A 1 - invOfUnit B 1 := by
  have h : D5.S1.Recurrence.Residue.ContinuedFractionOddSquare.Agree d A B := by
    intro n hn
    have he := X_pow_dvd_iff.mp hd n hn
    simpa only [map_sub, sub_eq_zero] using he
  have hi := D5.S1.Recurrence.Residue.ContinuedFractionOddSquare.agree_inv hA hB h
  apply X_pow_dvd_iff.mpr
  intro n hn
  rw [map_sub, sub_eq_zero]
  exact hi n hn
private theorem shifted_difference_dvd (d a : ℕ) (ha : 2 ≤ a) (U V : PowerSeries R)
    (hd : (X : PowerSeries R)^d ∣ U-V) (S : PowerSeries R) :
    (X : PowerSeries R)^(d+2) ∣ S * X^a * U - S * X^a * V := by
  have he := mul_dvd_mul (pow_dvd_pow (X : PowerSeries R) ha) hd
  rw [← pow_add, Nat.add_comm 2 d] at he
  convert dvd_mul_of_dvd_right he S using 1 <;> ring
private theorem normalized_difference_dvd (p : ℕ) (hp : 2 ≤ p) (d : ℕ)
    (F G : PowerSeries R) (hd : (X : PowerSeries R)^d ∣ F-G)
    (j : ℤ) (hj : j ≠ -1) :
    (X : PowerSeries R)^(d+2) ∣ normalizedTerm p F j - normalizedTerm p G j := by
  unfold normalizedTerm
  split_ifs with h0 hpos
  · simp
  · have hm : 1 ≤ j.natAbs := by exact Int.natAbs_pos.mpr h0
    have ha : 2 ≤ p * j.natAbs := by
      exact le_mul_of_le_of_one_le hp hm
    apply shifted_difference_dvd d _ ha _ _ _ _
    apply dvd_trans _ (sub_dvd_pow_sub_pow _ _ (p*j.natAbs))
    convert hd using 1 <;> ring
  · have hm : 2 ≤ j.natAbs := by omega
    have hconst (A : PowerSeries R) : constantCoeff (1+X^j.natAbs*A) = 1 := by
      simp [show j.natAbs ≠ 0 from Int.natAbs_ne_zero.mpr h0]
    have hin : (X : PowerSeries R)^d ∣ (1+X^j.natAbs*F)-(1+X^j.natAbs*G) := by
      convert dvd_mul_of_dvd_right hd (X^j.natAbs) using 1 <;> ring
    have hu := inverse_difference_dvd _ _ d (hconst F) (hconst G) hin
    have hpow := dvd_trans hu (sub_dvd_pow_sub_pow
      (invOfUnit (1+X^j.natAbs*F) 1) (invOfUnit (1+X^j.natAbs*G) 1) (p*j.natAbs))
    apply shifted_difference_dvd d _ _ _ _ hpow _
    have hsub : 1 ≤ j.natAbs-1 := by
      exact Nat.le_sub_one_of_lt hm
    calc 2 ≤ p*j.natAbs := le_mul_of_le_of_one_le hp (Nat.le_of_lt hm)
         _ ≤ p*j.natAbs*(j.natAbs-1) := by
           simpa using Nat.mul_le_mul_left (p*j.natAbs) hsub
private theorem exceptional_difference_dvd (p d : ℕ) (F G : PowerSeries R)
    (hd : (X : PowerSeries R)^d ∣ F-G) :
    (X : PowerSeries R)^(d+2) ∣
      normalizedTerm p F (-1) - normalizedTerm p G (-1) - (p : PowerSeries R)*X*(F-G) := by
  let U := invOfUnit (1+X*F) 1
  let V := invOfUnit (1+X*G) 1
  let S := ∑ i ∈ range p, U^i * V^(p-1-i)
  have hU : constantCoeff U = 1 := by simp [U, constantCoeff_invOfUnit]
  have hV : constantCoeff V = 1 := by simp [V, constantCoeff_invOfUnit]
  have hgeom : (U-V)*S = U^p - V^p := by
    exact (Commute.all U V).mul_geom_sum₂ p
  have hinv : U-V = -X*(F-G)*U*V := by
    dsimp only [U,V]
    rw [D5.S1.Recurrence.Residue.NegativePowerDiagonalModPrime.inverse_difference _ _ (by simp) (by simp)]
    ring
  have hS : constantCoeff (U*V*S-(p : PowerSeries R)) = 0 := by
    simp [S, hU, hV]
  have hX := X_dvd_iff.mpr hS
  have he : normalizedTerm p F (-1) - normalizedTerm p G (-1) -
      (p : PowerSeries R)*X*(F-G) = X*(F-G)*(U*V*S-(p : PowerSeries R)) := by
    simp only [normalizedTerm, Int.reduceNeg, show (-1 : ℤ) ≠ 0 by decide, ite_false,
      show ¬ (0 : ℤ) < -1 by omega, Int.natAbs_neg, Int.natAbs_one, pow_one,
      mul_one, Nat.sub_self, mul_zero, pow_zero, mul_neg, mul_one, neg_mul, one_mul]
    change -U^p - -V^p - (p : PowerSeries R)*X*(F-G) = _
    linear_combination hgeom - S*hinv
  rw [he]
  have hD : (X : PowerSeries R)^(d+1) ∣ X*(F-G) := by
    simpa only [pow_succ', pow_one] using mul_dvd_mul (dvd_refl X) hd
  simpa only [pow_succ] using mul_dvd_mul hD hX
private theorem psi_difference_dvd (p : ℕ) (hp : 2 ≤ p) (d : ℕ)
    (F G : PowerSeries R) (hd : (X : PowerSeries R)^d ∣ F-G) :
    (X : PowerSeries R)^(d+2) ∣ psi p F - psi p G - (p : PowerSeries R)*X*(F-G) := by
  apply X_pow_dvd_iff.mpr
  intro n hn
  have he : coeff n (psi p F - psi p G) =
      coeff n (normalizedTerm p F (-1) - normalizedTerm p G (-1)) := by
    rw [map_sub, finite_window p (by omega) F n (n+1) le_rfl,
      finite_window p (by omega) G n (n+1) le_rfl, ← sum_sub_distrib]
    simp only [← map_sub]
    apply sum_eq_single (-1)
    · intro j _ hj
      exact X_pow_dvd_iff.mp (normalized_difference_dvd p hp d F G hd j hj) n hn
    · intro hnot
      exfalso
      apply hnot
      simp only [mem_Icc]
      constructor <;> omega
  rw [map_sub, he]
  exact X_pow_dvd_iff.mp (exceptional_difference_dvd p d F G hd) n hn
end Linearization
open PowerSeries Finset
private theorem psi_constant (p : ℕ) (hp : 2 ≤ p) (F : PowerSeries ℚ) :
    constantCoeff (psi p F) = 0 := by
  rw [← coeff_zero_eq_constantCoeff, finite_window p (by omega) F 0 1 (by omega)]
  have hi : Icc (-((1 : ℕ) : ℤ)) ((1 : ℕ) : ℤ) = {-1,0,1} := by
    exact (fun {α} {s t} => val_inj.mp) rfl
  rw [hi]
  simp [normalizedTerm, coeff_zero_eq_constantCoeff, constantCoeff_invOfUnit, show p ≠ 0 by omega]
private theorem psi_zero_first (p : ℕ) (hp : 2 ≤ p) : coeff 1 (psi p (0 : PowerSeries ℚ)) = 0 := by
  rw [finite_window p (by omega) 0 1 2 (by omega)]
  have hi : Icc (-((2 : ℕ) : ℤ)) ((2 : ℕ) : ℤ) = {-2,-1,0,1,2} := by
    exact (fun {α} {s t} => val_inj.mp) rfl
  have hinv : invOfUnit (1 : PowerSeries ℚ) 1 = 1 :=
    D5.S1.Recurrence.Residue.ContinuedFractionOddSquare.inverse_one
  have hp1 : ¬ p ≤ 1 := by
    exact Nat.not_le_of_lt hp
  have hp2 : ¬ p*2 ≤ 1 := by omega
  rw [hi]
  simp [normalizedTerm, hinv, coeff_X_pow_mul', hp1, hp2] <;> omega
private theorem psi_first (p : ℕ) (hp : 2 ≤ p) (F : PowerSeries ℚ) :
    coeff 1 (psi p F) = (p : ℚ)*constantCoeff F := by
  have hd := psi_difference_dvd p hp 0 F 0 (by simp)
  have he := X_pow_dvd_iff.mp hd 1 (by omega)
  simp only [map_sub, sub_zero, psi_zero_first p hp, sub_zero] at he
  have hc : coeff 1 ((p : PowerSeries ℚ)*X*F) = (p : ℚ)*constantCoeff F := by
    rw [show (p : PowerSeries ℚ) = C (p : ℚ) by simp, mul_assoc,
      coeff_C_mul, coeff_one_mul]
    simp
  rw [hc] at he
  exact sub_eq_zero.mp he
private noncomputable def step (p : ℕ) (F : PowerSeries ℚ) : PowerSeries ℚ :=
  mk fun n => coeff n F + (if n=0 then 1 else 0) - coeff (n+1) (psi p F)/(p : ℚ)
private theorem step_constant (p : ℕ) (hp : 2 ≤ p) (F : PowerSeries ℚ) :
    constantCoeff (step p F) = 1 := by
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
  simp [step, constantCoeff_mk, psi_first p hp, hpq]
private theorem step_contract (p : ℕ) (hp : 2 ≤ p) (d : ℕ) (F G : PowerSeries ℚ)
    (hd : ∀ n < d, coeff n F = coeff n G) :
    ∀ n < d+1, coeff n (step p F) = coeff n (step p G) := by
  have hdiv : (X : PowerSeries ℚ)^d ∣ F-G := by
    exact (D5.S1.Recurrence.Invariants.UnitReversionSquareParity.agree_iff d F G).mp hd
  have he := psi_difference_dvd p hp d F G hdiv
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
  intro n hn
  have hc := X_pow_dvd_iff.mp he (n+1) (by omega)
  have hm : coeff (n+1) ((p : PowerSeries ℚ)*X*(F-G)) =
      (p : ℚ)*(coeff n F-coeff n G) := by
    rw [show (p : PowerSeries ℚ) = C (p : ℚ) by simp, mul_assoc, coeff_C_mul,
      coeff_succ_X_mul, map_sub]
  rw [map_sub, map_sub, hm] at hc
  simp only [step, coeff_mk]
  field_simp
  linear_combination -hc
private theorem step_fixed_iff (p : ℕ) (hp : 2 ≤ p) (F : PowerSeries ℚ) :
    step p F = F ↔ IsSolution p F := by
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
  rw [isSolution_iff p (by omega) F]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · rw [← h, step_constant p hp]
    · ext n
      cases n with
      | zero => simpa [coeff_zero_eq_constantCoeff, psi_constant p hp]
      | succ n =>
        have he := congrArg (coeff n) h
        simp only [step, coeff_mk] at he
        simp only [coeff_C_mul, coeff_X]
        by_cases hn : n = 0
        · subst n
          norm_num at he ⊢
          field_simp at he
          linarith
        · simp only [if_neg hn] at he
          have hn1 : n+1 ≠ 1 := by
            exact Ne.symm ((fun {a b} => Nat.add_one_ne_add_one_iff.mpr) fun a => hn (id (Eq.symm a)))
          simp only [if_neg hn1]
          field_simp at he
          linarith
  · rintro ⟨h0,h⟩
    ext n
    simp only [step, coeff_mk, h, coeff_C_mul, coeff_X]
    by_cases hn : n = 0 <;> simp [hn, hpq]
private theorem exists_solution (p : ℕ) (hp : 2 ≤ p) : ∃ F, IsSolution p F := by
  obtain ⟨F,hF,_⟩ := contracting_series_fixedpoint (step p) (step_contract p hp)
  exact ⟨F, (step_fixed_iff p hp F).mp hF⟩
open PowerSeries Finset
section Prime
private theorem normalizedTerm_map {R S : Type*} [CommRing R] [CommRing S]
    (h : R →+* S) (p : ℕ) (F : PowerSeries R) (j : ℤ) :
    (normalizedTerm p F j).map h = normalizedTerm p (F.map h) j := by
  unfold normalizedTerm
  split_ifs with hj hp
  · simp
  · simp
  · have hm : j.natAbs ≠ 0 := by
      exact Int.natAbs_ne_zero.mpr hj
    have hi : (invOfUnit (1+X^j.natAbs*F) 1).map h =
        invOfUnit (1+X^j.natAbs*F.map h) 1 := by
      rw [D5.S1.Recurrence.Residue.ContinuedFractionOddSquare.map_inverse h
        (1+X^j.natAbs*F) (by simp [hm])]
      rw [map_add (PowerSeries.map h), map_one (PowerSeries.map h),
        map_mul (PowerSeries.map h), map_pow (PowerSeries.map h), PowerSeries.map_X]
    simp only [map_mul, map_pow, map_neg, map_one, map_X, hi]
private theorem psi_map {R S : Type*} [CommRing R] [CommRing S]
    (h : R →+* S) (p : ℕ) (F : PowerSeries R) :
    (psi p F).map h = psi p (F.map h) := by
  ext n
  simp only [coeff_map, psi, coeff_mk, map_sum]
  apply sum_congr rfl
  intro j _
  rw [← coeff_map, normalizedTerm_map]
private theorem normalizedTerm_frobenius (p : ℕ) [Fact p.Prime]
    (F : PowerSeries (ZMod p)) (j : ℤ) :
    normalizedTerm p F j = normalizedTerm 1 F j ^ p := by
  letI : CharP (PowerSeries (ZMod p)) p :=
    charP_of_injective_ringHom (PowerSeries.C_injective (R := ZMod p)) p
  have hs (m : ℕ) : ((-1 : PowerSeries (ZMod p))^m)^p = (-1)^m := by
    rw [pow_right_comm, neg_one_pow_char]
  unfold normalizedTerm
  split_ifs <;> simp only [one_pow, one_mul, mul_pow, hs, ← pow_mul]
  all_goals congr 2 <;> ring
private theorem prime_divisibility_of_pairing (p : ℕ) [Fact p.Prime]
    (hpair : ∀ F : PowerSeries (ZMod p), psi 1 F = 0)
    (F : PowerSeries ℤ) (N : ℕ) : (p : ℤ) ∣ coeff N (psi p F) := by
  let G := F.map (Int.castRingHom (ZMod p))
  have hz : coeff N (psi p G) = 0 := by
    let S := ∑ j ∈ Icc (-((N+1 : ℕ) : ℤ)) ((N+1 : ℕ) : ℤ), normalizedTerm 1 G j
    have hS : (X : PowerSeries (ZMod p))^(N+1) ∣ S := by
      apply X_pow_dvd_iff.mpr
      intro n hn
      dsimp only [S]
      rw [map_sum]
      rw [← finite_window 1 (by decide) G n (N+1) (by omega), hpair G, map_zero]
    have hSp : (X : PowerSeries (ZMod p))^(N+1) ∣ S^p :=
      hS.trans (dvd_pow_self _ (by exact (Fact.out : p.Prime).ne_zero))
    have hfrob (A : PowerSeries (ZMod p)) : A^p = A.subst (X^p) := by
      exact D5.S1.Recurrence.Invariants.CubicFifteenSubstitutionParity.prime_power_subst p A
    have ht : HasSubst (X^p : PowerSeries (ZMod p)) :=
      .of_constantCoeff_zero (by
        change constantCoeff ((X : PowerSeries (ZMod p))^p) = 0
        simp [(Fact.out : p.Prime).ne_zero])
    have hsum : S^p = ∑ j ∈ Icc (-((N+1 : ℕ) : ℤ)) ((N+1 : ℕ) : ℤ),
        normalizedTerm 1 G j ^ p := by
      rw [hfrob, ← coe_substAlgHom ht]
      dsimp only [S]
      rw [map_sum]
      apply sum_congr rfl
      intro j _
      simpa only [coe_substAlgHom ht] using (hfrob (normalizedTerm 1 G j)).symm
    rw [finite_window p (Fact.out : p.Prime).one_lt.le G N (N+1) le_rfl]
    simp only [normalizedTerm_frobenius]
    rw [← map_sum, ← hsum]
    exact X_pow_dvd_iff.mp hSp N (by omega)
  have hm := congrArg (coeff N) (psi_map (Int.castRingHom (ZMod p)) p F)
  rw [coeff_map] at hm
  have hc : ((coeff N (psi p F) : ℤ) : ZMod p) = 0 := hm.trans hz
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hc
end Prime
open Finset
private theorem binomial_obstruction (p q : ℕ) (hq : q.Prime) (hqp : q ∣ p) :
    ¬ ∃ z : ℤ, (∏ j ∈ range q, (1 + (j : ℚ) * p)) / (q.factorial : ℚ) = z := by
  letI : Fact q.Prime := ⟨hq⟩
  rintro ⟨z, hz⟩
  have hf : (q.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero q
  have he : (∏ j ∈ range q, (1 + j * p) : ℕ) = (q.factorial : ℤ) * z := by
    exact_mod_cast (show (∏ j ∈ range q, (1 + (j : ℚ) * p)) = (q.factorial : ℚ) * z by
      simpa only [mul_comm] using (div_eq_iff hf).mp hz)
  have hm := congrArg (Int.castRingHom (ZMod q)) he
  have hp : (p : ZMod q) = 0 := by
    exact (fun a b => (ZMod.natCast_eq_zero_iff a b).mpr) p q hqp
  have hfac : (q.factorial : ZMod q) = 0 :=
    (ZMod.natCast_eq_zero_iff q.factorial q).mpr
      (Nat.dvd_factorial hq.pos le_rfl)
  simp [hp, hfac] at hm
private theorem composite_minFac_lt (p : ℕ) (hp : 2 ≤ p) (hnp : ¬ p.Prime) : p.minFac < p := by
  exact (Nat.not_prime_iff_minFac_lt hp).mp hnp
open PowerSeries Finset
private theorem normalized_tail_dvd {R : Type*} [CommRing R]
    (p : ℕ) (F : PowerSeries R) (j : ℤ) (hj0 : j ≠ 0) (hj1 : j ≠ -1) :
    (X : PowerSeries R)^p ∣ normalizedTerm p F j := by
  unfold normalizedTerm
  rw [if_neg hj0]
  split_ifs with hpos
  · have hm : 1 ≤ j.natAbs := by exact Int.natAbs_pos.mpr hj0
    have ha : p ≤ p*j.natAbs := by
      exact Nat.le_mul_of_pos_right p hm
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (pow_dvd_pow X ha) _) _
  · have hm : 2 ≤ j.natAbs := by omega
    have hsub : 1 ≤ j.natAbs-1 := by
      exact Nat.le_sub_one_of_lt hm
    have ha : p ≤ p*j.natAbs*(j.natAbs-1) := by
      calc p ≤ p*j.natAbs := Nat.le_mul_of_pos_right p (Nat.lt_of_succ_lt hm)
           _ ≤ p*j.natAbs*(j.natAbs-1) := by
             simpa using Nat.mul_le_mul_left (p*j.natAbs) hsub
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (pow_dvd_pow X ha) _) _
private theorem low_inverse_equation (p : ℕ) (hp : 2 ≤ p) (F : PowerSeries ℚ)
    (hF : IsSolution p F) :
    (X : PowerSeries ℚ)^p ∣ invOfUnit (1+X*F) 1 ^ p - (1-(p : PowerSeries ℚ)*X) := by
  have hs := ((isSolution_iff p (by omega) F).mp hF).2
  apply X_pow_dvd_iff.mpr
  intro n hn
  have he : coeff n (psi p F) = coeff n (1-invOfUnit (1+X*F) 1 ^ p) := by
    rw [finite_window p (by omega) F n (n+1) le_rfl]
    have h0 : (0 : ℤ) ∈ Icc (-((n+1 : ℕ) : ℤ)) ((n+1 : ℕ) : ℤ) := by
      simp only [mem_Icc]
      constructor <;> omega
    rw [← sum_erase_add _ _ h0]
    have hm : (-1 : ℤ) ∈ (Icc (-((n+1 : ℕ) : ℤ)) ((n+1 : ℕ) : ℤ)).erase 0 := by
      simp only [mem_erase, mem_Icc]
      constructor
      · decide
      · constructor <;> omega
    rw [← sum_erase_add _ _ hm]
    have htail : ∑ j ∈ ((Icc (-((n+1 : ℕ) : ℤ)) ((n+1 : ℕ) : ℤ)).erase 0).erase (-1),
        coeff n (normalizedTerm p F j) = 0 := by
      apply sum_eq_zero
      intro j hj
      have hj0 := (mem_erase.mp (mem_erase.mp hj).2).1
      have hj1 := (mem_erase.mp hj).1
      exact X_pow_dvd_iff.mp (normalized_tail_dvd p F j hj0 hj1) n hn
    rw [htail]
    simp [normalizedTerm, sub_eq_add_neg, add_comm]
  rw [hs] at he
  have hc : C (p : ℚ) = (p : PowerSeries ℚ) := by
    exact map_natCast' C rfl p
  rw [hc] at he
  simp only [map_sub, map_mul] at he ⊢
  linear_combination he
private theorem low_power_equation (p : ℕ) (hp : 2 ≤ p) (F : PowerSeries ℚ)
    (hF : IsSolution p F) :
    (X : PowerSeries ℚ)^p ∣ (1-(p : PowerSeries ℚ)*X)*(1+X*F)^p-1 := by
  have hd := dvd_mul_of_dvd_right (low_inverse_equation p hp F hF) ((1+X*F)^p)
  have he : (1+X*F)^p * invOfUnit (1+X*F) 1 ^ p = (1 : PowerSeries ℚ) := by
    rw [← mul_pow, mul_invOfUnit _ 1 (by simp), one_pow]
  convert dvd_neg.mpr hd using 1
  linear_combination he
private theorem derivative_order {R : Type*} [CommRing R] (p : ℕ) (A : PowerSeries R)
    (hd : (X : PowerSeries R)^p ∣ A) :
    (X : PowerSeries R)^(p-1) ∣ derivative A := by
  obtain ⟨T, rfl⟩ := hd
  rw [Derivation.leibniz, derivative_pow, derivative_X, mul_one]
  simp only [smul_eq_mul]
  apply dvd_add
  · exact dvd_mul_of_dvd_left (pow_dvd_pow (X : PowerSeries R) (by omega : p-1 ≤ p)) _
  · exact dvd_mul_of_dvd_right (dvd_mul_left (X^(p-1)) (p : PowerSeries R)) T
private theorem low_differential_equation (p : ℕ) (hp : 2 ≤ p) (F : PowerSeries ℚ)
    (hF : IsSolution p F) :
    (X : PowerSeries ℚ)^(p-1) ∣
      (1-(p : PowerSeries ℚ)*X)*derivative (1+X*F) - (1+X*F) := by
  let H := (1+X*F : PowerSeries ℚ)
  have hd := derivative_order p _ (low_power_equation p hp F hF)
  have he : derivative ((1-(p : PowerSeries ℚ)*X)*H^p-1) =
      ((p : PowerSeries ℚ)*H^(p-1)) * ((1-(p : PowerSeries ℚ)*X)*derivative H-H) := by
    have hc : derivative (p : PowerSeries ℚ) = 0 := by
      exact Derivation.map_natCast d⁄dX p
    have h1 : derivative (1 : PowerSeries ℚ) = 0 := derivative_one
    simp only [map_sub, Derivation.leibniz, h1, hc, derivative_X, derivative_pow,
      smul_eq_mul, mul_zero, zero_mul, zero_add, sub_zero, mul_one]
    have hpow : H^p = H^(p-1)*H := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ p)]
    rw [hpow]
    ring
  have hu : IsUnit ((p : PowerSeries ℚ)*H^(p-1)) := by
    apply isUnit_iff_constantCoeff.mpr
    have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
    simpa [H] using isUnit_iff_ne_zero.mpr hpq
  change (X : PowerSeries ℚ)^(p-1) ∣ (1-(p : PowerSeries ℚ)*X)*derivative H-H
  apply (hu.dvd_mul_left).mp
  rw [← he]
  exact hd
private theorem low_coefficient_recurrence (p : ℕ) (hp : 2 ≤ p) (F : PowerSeries ℚ)
    (hF : IsSolution p F) (r : ℕ) (hr : r < p-1) :
    (r+1 : ℚ)*coeff (r+1) (1+X*F) = (1+(r : ℚ)*p)*coeff r (1+X*F) := by
  let H := (1+X*F : PowerSeries ℚ)
  have he := X_pow_dvd_iff.mp (low_differential_equation p hp F hF) r hr
  change coeff r ((1-(p : PowerSeries ℚ)*X)*derivative H-H) = 0 at he
  rw [sub_mul, one_mul, map_sub, map_sub, coeff_derivative] at he
  by_cases hr0 : r = 0
  · subst r
    simp only [coeff_zero_eq_constantCoeff, map_mul, constantCoeff_X, mul_zero,
      zero_mul, sub_zero, Nat.cast_zero, zero_add, zero_mul, one_mul] at he ⊢
    linear_combination he
  · have hrp : 0 < r := by exact Nat.zero_lt_of_ne_zero hr0
    have hcast : ((r-1 : ℕ) : ℚ)+1 = (r : ℚ) := by
      exact_mod_cast Nat.sub_add_cancel hrp
    have hc : coeff r ((p : PowerSeries ℚ)*X*derivative H) =
        (p : ℚ)*(r : ℚ)*coeff r H := by
      rw [show (p : PowerSeries ℚ) = C (p : ℚ) by simp, mul_assoc, coeff_C_mul, ← pow_one (X : PowerSeries ℚ),
        coeff_X_pow_mul' (derivative H) 1 r, if_pos (by omega), coeff_derivative]
      simp only [show r-1+1 = r from Nat.sub_add_cancel hrp]
      rw [hcast]
      ring
    rw [hc] at he
    linear_combination he
private theorem factorial_coefficient_identity (p : ℕ) (hp : 2 ≤ p) (F : PowerSeries ℚ)
    (hF : IsSolution p F) (r : ℕ) (hr : r < p) :
    (r.factorial : ℚ)*coeff r (1+X*F) = ∏ j ∈ range r, (1+(j : ℚ)*p) := by
  induction r with
  | zero => simp
  | succ r ih =>
    have hi := ih (by omega)
    have he := low_coefficient_recurrence p hp F hF r (by omega)
    rw [prod_range_succ, Nat.factorial_succ]
    push_cast
    linear_combination (r.factorial : ℚ)*he + (1+(r : ℚ)*p)*hi
private theorem integral_implies_prime (p : ℕ) (hp : 2 ≤ p) (F : PowerSeries ℚ)
    (hF : IsSolution p F) (hint : ∀ n, ∃ z : ℤ, coeff n F = z) : p.Prime := by
  by_contra hnp
  let q := p.minFac
  have hq : q.Prime := Nat.minFac_prime (by omega)
  have hqp : q ∣ p := Nat.minFac_dvd p
  have hqlt : q < p := composite_minFac_lt p hp hnp
  have he := factorial_coefficient_identity p hp F hF q hqlt
  obtain ⟨z,hz⟩ := hint (q-1)
  have hc : coeff q (1+X*F : PowerSeries ℚ) = (z : ℚ) := by
    rw [map_add, coeff_one, if_neg (Nat.ne_of_gt hq.pos), zero_add]
    rw [← pow_one (X : PowerSeries ℚ), coeff_X_pow_mul', if_pos (Nat.succ_le_of_lt hq.pos), hz]
  rw [hc] at he
  apply binomial_obstruction p q hq hqp
  refine ⟨z, ?_⟩
  apply (div_eq_iff (show (q.factorial : ℚ) ≠ 0 by exact_mod_cast Nat.factorial_ne_zero q)).mpr
  linear_combination -he
open PowerSeries
private theorem step_preserves_integral (p : ℕ) [Fact p.Prime]
    (hpair : ∀ F : PowerSeries (ZMod p), psi 1 F = 0)
    (F : PowerSeries ℚ) (hF : ∀ n, ∃ z : ℤ, coeff n F = z) :
    ∀ n, ∃ z : ℤ, coeff n (step p F) = z := by
  let A : PowerSeries ℤ := mk fun n => Classical.choose (hF n)
  have hA : A.map (Int.castRingHom ℚ) = F := by
    ext n
    simp only [coeff_map, A, coeff_mk, Int.coe_castRingHom]
    exact (Classical.choose_spec (hF n)).symm
  have hpsi : psi p F = (psi p A).map (Int.castRingHom ℚ) := by
    rw [psi_map, hA]
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  intro n
  obtain ⟨w, hw⟩ := prime_divisibility_of_pairing p hpair A (n+1)
  refine ⟨coeff n A + (if n=0 then 1 else 0) - w, ?_⟩
  have hc : coeff n F = ((coeff n A : ℤ) : ℚ) := by rw [← hA, coeff_map]; rfl
  simp only [step, coeff_mk, hc, hpsi, coeff_map, Int.coe_castRingHom, hw]
  push_cast
  by_cases hn : n=0 <;> simp [hn, hpq]
private theorem prime_solution_integral (p : ℕ) [Fact p.Prime]
    (hpair : ∀ F : PowerSeries (ZMod p), psi 1 F = 0)
    (F : PowerSeries ℚ) (hF : IsSolution p F) :
    ∀ n, ∃ z : ℤ, coeff n F = z := by
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hf := (step_fixed_iff p hp F).mpr hF
  let A : ℕ → PowerSeries ℚ := fun d => (step p)^[d] 0
  have hs (d : ℕ) : A (d+1) = step p (A d) := by
    exact Function.iterate_succ_apply' (step p) d 0
  have hAi : ∀ d n, ∃ z : ℤ, coeff n (A d) = z := by
    intro d
    induction d with
    | zero => intro n; exact ⟨0, by simp [A]⟩
    | succ d ih => rw [hs]; exact step_preserves_integral p hpair (A d) ih
  have hAg : ∀ d, ∀ n < d, coeff n F = coeff n (A d) := by
    intro d
    induction d with
    | zero => intro n hn; omega
    | succ d ih =>
      rw [hs, ← hf]
      exact step_contract p hp d F (A d) ih
  intro n
  obtain ⟨z,hz⟩ := hAi (n+1) n
  exact ⟨z, (hAg (n+1) n (by omega)).trans hz⟩
theorem result : D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.claim := by
  intro p hp
  refine ⟨exists_solution p hp, ?_⟩
  intro F hF
  refine ⟨integral_implies_prime p hp F hF, ?_⟩
  intro hprime
  letI : Fact p.Prime := ⟨hprime⟩
  exact prime_solution_integral p (fun G => psi_one_zero G) F hF
end D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality
