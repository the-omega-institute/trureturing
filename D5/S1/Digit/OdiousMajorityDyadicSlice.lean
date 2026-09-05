/- GID: D5/S1/Digit/OdiousMajorityDyadicSlice
   generality: I
   mirror-B: D5/B/S1/Digit/OdiousMajorityDyadicSlice
   mirror-E: none(waiver:exact-finite-state-arithmetic)
   anchors: [PZG-6.217, PZG-6.218, PZG-6.219, PZG-6.220]
   digest: A 21-state transfer certificate proves odious majority on every six-bit dyadic slice. -/

import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators Matrix

namespace D5.S1.Digit.OdiousMajorityDyadicSlice

/-- The residue-state index set for arithmetic modulo 21. -/
abbrev Ix := Fin 21

/-- The number of nonzero binary digits of a natural number. -/
def popcount (m : Nat) : Nat :=
  (Nat.bits m).count true

/-- The Prouhet-Thue-Morse sign attached to a natural number. -/
def sign (m : Nat) : Int :=
  (-1 : Int) ^ popcount m

/-- The standard column basis of the 21-coordinate state space. -/
def basis (j : Ix) : Ix -> Int :=
  fun i => if i = j then 1 else 0

/-- The binary digit transfer matrix on signed residue counts modulo 21. -/
def T : Matrix Ix Ix Int :=
  fun i j => (if i = 2 * j then 1 else 0) - (if i = 2 * j + 1 then 1 else 0)

private theorem T_mulVec_basis (j : Ix) :
    T *ᵥ basis j = basis (2 * j) - basis (2 * j + 1) := by
  ext i
  simp only [Matrix.mulVec, dotProduct]
  simp [T, basis]

private theorem popcount_double (m : Nat) : popcount (2 * m) = popcount m := by
  by_cases hm : m = 0
  · subst m
    simp [popcount]
  · simp [popcount, Nat.bit0_bits m hm]

private theorem popcount_double_add_one (m : Nat) :
    popcount (2 * m + 1) = popcount m + 1 := by
  simp [popcount, Nat.bit1_bits]

private theorem sign_double (m : Nat) : sign (2 * m) = sign m := by
  simp [sign, popcount_double]

private theorem sign_double_add_one (m : Nat) : sign (2 * m + 1) = -sign m := by
  simp [sign, popcount_double_add_one, pow_succ]

private theorem sum_range_two {M : Type*} [AddCommMonoid M] (f : Nat -> M) :
    forall n : Nat,
      (∑ m ∈ Finset.range (2 * n), f m) =
        ∑ m ∈ Finset.range n, (f (2 * m) + f (2 * m + 1)) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.mul_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, ih]
      simp [add_assoc]

/-- The residue class of a natural number, represented in `Fin 21`. -/
def residue (m : Nat) : Ix :=
  ⟨m % 21, Nat.mod_lt _ (by norm_num)⟩

private theorem residue_double (m : Nat) : residue (2 * m) = 2 * residue m := by
  apply Fin.ext
  change (2 * m) % 21 = (2 * (m % 21)) % 21
  omega

private theorem residue_double_add_one (m : Nat) :
    residue (2 * m + 1) = 2 * residue m + 1 := by
  apply Fin.ext
  change (2 * m + 1) % 21 = (2 * (m % 21) % 21 + 1) % 21
  omega

/-- The signed residue-count column below the binary cutoff `2 ^ n`. -/
def state (n : Nat) : Ix -> Int :=
  ∑ m ∈ Finset.range (2 ^ n), sign m • basis (residue m)

private theorem state_zero : state 0 = basis 0 := by
  ext i
  simp [state, sign, popcount, residue, basis]

private theorem state_succ (n : Nat) : state (n + 1) = T *ᵥ state n := by
  rw [state, pow_succ']
  change (∑ m ∈ Finset.range (2 * 2 ^ n), sign m • basis (residue m)) = _
  rw [sum_range_two]
  rw [state, Matrix.mulVec_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Matrix.mulVec_smul, T_mulVec_basis]
  simp [sign_double, sign_double_add_one, residue_double, residue_double_add_one,
    sub_eq_add_neg]

/-- The one-bit transition and its iterated form for signed residue counts. -/
theorem state_eq_transfer_pow (n : Nat) :
    state (n + 1) = T *ᵥ state n ∧ state n = T ^ n *ᵥ basis 0 := by
  constructor
  · exact state_succ n
  · induction n with
    | zero => simp [state_zero]
    | succ n ih =>
        rw [state_succ, ih, Matrix.mulVec_mulVec, ← pow_succ']

/-- The selector row for the two eligible residue classes modulo 21. -/
def ell : Ix -> Int :=
  fun i => if i = 7 ∨ i = 14 then 1 else 0

/-- The six-binary-digit block transfer matrix. -/
def A : Matrix Ix Ix Int :=
  T ^ 6

/-- The signed eligible count below the six-bit dyadic cutoff `2 ^ (6 * k)`. -/
def D (k : Nat) : Int :=
  ∑ m ∈ Finset.range (2 ^ (6 * k)),
    if 7 ∣ m ∧ ¬3 ∣ m then sign m else 0

/-- The number of eligible odious integers below `2 ^ (6 * k)`. -/
def odiousCount (k : Nat) : Nat :=
  ((Finset.range (2 ^ (6 * k))).filter fun m =>
    (7 ∣ m ∧ ¬3 ∣ m) ∧ Odd (popcount m)).card

/-- The number of eligible evil integers below `2 ^ (6 * k)`. -/
def evilCount (k : Nat) : Nat :=
  ((Finset.range (2 ^ (6 * k))).filter fun m =>
    (7 ∣ m ∧ ¬3 ∣ m) ∧ Even (popcount m)).card

private theorem eligible_iff_residue (m : Nat) :
    (7 ∣ m ∧ ¬3 ∣ m) ↔ residue m = 7 ∨ residue m = 14 := by
  have h7 : residue m = 7 ↔ m % 21 = 7 := by
    constructor
    · intro h
      exact congrArg Fin.val h
    · intro h
      apply Fin.ext
      exact h
  have h14 : residue m = 14 ↔ m % 21 = 14 := by
    constructor
    · intro h
      exact congrArg Fin.val h
    · intro h
      apply Fin.ext
      exact h
  rw [h7, h14]
  omega

private theorem ell_dot_basis (j : Ix) :
    ell ⬝ᵥ basis j = if j = 7 ∨ j = 14 then 1 else 0 := by
  simp [dotProduct, ell, basis]

private theorem ell_dot_state (n : Nat) :
    ell ⬝ᵥ state n =
      ∑ m ∈ Finset.range (2 ^ n),
        if residue m = 7 ∨ residue m = 14 then sign m else 0 := by
  rw [state, dotProduct_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [dotProduct_smul, ell_dot_basis]
  split <;> simp_all

private theorem D_eq_transfer (k : Nat) :
    D k = ell ⬝ᵥ (A ^ k *ᵥ basis 0) := by
  rw [D]
  have hsum :
      (∑ m ∈ Finset.range (2 ^ (6 * k)),
          if 7 ∣ m ∧ ¬3 ∣ m then sign m else 0) =
        ∑ m ∈ Finset.range (2 ^ (6 * k)),
          if residue m = 7 ∨ residue m = 14 then sign m else 0 := by
    apply Finset.sum_congr rfl
    intro m hm
    simp only [eligible_iff_residue]
  rw [hsum, ← ell_dot_state, (state_eq_transfer_pow (6 * k)).2]
  simp [A, pow_mul]

/-- Eligibility is exactly membership in residues 7 or 14, and the dyadic
difference is the corresponding six-bit transfer-matrix coefficient. -/
theorem eligibility_iff_residue_and_D_eq_transfer :
    (forall m : Nat, (7 ∣ m ∧ ¬3 ∣ m) ↔ residue m = 7 ∨ residue m = 14) ∧
      forall k : Nat, D k = ell ⬝ᵥ (A ^ k *ᵥ basis 0) := by
  exact ⟨eligible_iff_residue, D_eq_transfer⟩

private def row (k : Nat) : Ix -> Int :=
  ell ᵥ* A ^ k

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem annihilating_row :
    row 4 = (19 : Int) • row 3 + (209 : Int) • row 2 + (189 : Int) • row 1 := by
  funext i
  fin_cases i <;> decide

private def annihilator : Matrix Ix Ix Int :=
  A ^ 3 - (19 : Int) • A ^ 2 - (209 : Int) • A - (189 : Int) • 1

private theorem annihilating_identity : (ell ᵥ* A) ᵥ* annihilator = 0 := by
  have hpow (n : Nat) : (ell ᵥ* A) ᵥ* A ^ n = row (n + 1) := by
    simp [row, pow_succ']
  have hA : (ell ᵥ* A) ᵥ* A = row 2 := by simpa using hpow 1
  have hOne : (ell ᵥ* A) ᵥ* (1 : Matrix Ix Ix Int) = row 1 := by simp [row]
  simp only [annihilator, Matrix.vecMul_sub, Matrix.vecMul_smul, hpow, hA, hOne,
    Nat.reduceAdd]
  rw [annihilating_row]
  module

private theorem row_add (p q : Nat) : row (p + q) = row p ᵥ* A ^ q := by
  simp [row, pow_add]

private theorem row_recurrence (k : Nat) (hk : 1 ≤ k) :
    row (k + 3) =
      (19 : Int) • row (k + 2) + (209 : Int) • row (k + 1) + (189 : Int) • row k := by
  let t := k - 1
  have h := congrArg (fun v : Ix -> Int => v ᵥ* A ^ t) annihilating_row
  simp only [Matrix.add_vecMul, Matrix.smul_vecMul] at h
  rw [← row_add 4 t, ← row_add 3 t, ← row_add 2 t, ← row_add 1 t] at h
  rw [show k + 3 = 4 + t by omega, show k + 2 = 3 + t by omega,
    show k + 1 = 2 + t by omega, show k = 1 + t by omega]
  exact h

private theorem D_eq_row_dot (k : Nat) : D k = row k ⬝ᵥ basis 0 := by
  rw [D_eq_transfer, Matrix.dotProduct_mulVec]
  rfl

private theorem D_recurrence (k : Nat) (hk : 1 ≤ k) :
    D (k + 3) = 19 * D (k + 2) + 209 * D (k + 1) + 189 * D k := by
  have h := congrArg (fun v : Ix -> Int => v ⬝ᵥ basis 0) (row_recurrence k hk)
  simp only [add_dotProduct, smul_dotProduct, smul_eq_mul] at h
  simpa only [D_eq_row_dot] using h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem D_one_direct : D 1 = -6 := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem D_two_direct : D 2 = -42 := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem D_three_matrix : D 3 = -2070 := by
  rw [D_eq_transfer]
  decide

/-- The exact annihilator certificate, its three initial values, and the
resulting third-order recurrence for the signed dyadic difference. -/
theorem annihilating_identity_and_D_recurrence :
    (ell ᵥ* A) ᵥ*
        (A ^ 3 - (19 : Int) • A ^ 2 - (209 : Int) • A - (189 : Int) • 1) = 0 ∧
      D 1 = -6 ∧ D 2 = -42 ∧ D 3 = -2070 ∧
      forall k : Nat, 1 ≤ k ->
        D (k + 3) = 19 * D (k + 2) + 209 * D (k + 1) + 189 * D k := by
  exact ⟨annihilating_identity, D_one_direct, D_two_direct, D_three_matrix, D_recurrence⟩

private theorem sign_eq_one_of_even {m : Nat} (h : Even (popcount m)) : sign m = 1 := by
  simpa [sign] using (h.neg_one_pow : (-1 : Int) ^ popcount m = 1)

private theorem sign_eq_neg_one_of_odd {m : Nat} (h : Odd (popcount m)) : sign m = -1 := by
  simpa [sign] using (h.neg_one_pow : (-1 : Int) ^ popcount m = -1)

private theorem D_eq_count_difference (k : Nat) :
    D k = (evilCount k : Int) - (odiousCount k : Int) := by
  classical
  rw [D, evilCount, odiousCount]
  generalize Finset.range (2 ^ (6 * k)) = s
  induction s using Finset.induction_on with
  | empty => simp
  | @insert m s hm ih =>
      by_cases heligible : 7 ∣ m ∧ ¬3 ∣ m
      · rcases Nat.even_or_odd (popcount m) with heven | hodd
        · have hnotOdd : ¬Odd (popcount m) := Nat.not_odd_iff_even.mpr heven
          simp [Finset.sum_insert, Finset.filter_insert, hm, heligible, heven, hnotOdd,
            sign_eq_one_of_even heven, ih]
          ring
        · have hnotEven : ¬Even (popcount m) := Nat.not_even_iff_odd.mpr hodd
          simp [Finset.sum_insert, Finset.filter_insert, hm, heligible, hodd, hnotEven,
            sign_eq_neg_one_of_odd hodd, ih]
          ring
      · simp [Finset.sum_insert, Finset.filter_insert, hm, heligible, ih]

private theorem D_strictly_negative (k : Nat) (hk : 1 ≤ k) : D k < 0 := by
  revert hk
  induction k using Nat.strong_induction_on with
  | h k ih =>
      intro hk
      by_cases h1 : k = 1
      · rw [h1, D_one_direct]
        norm_num
      by_cases h2 : k = 2
      · rw [h2, D_two_direct]
        norm_num
      by_cases h3 : k = 3
      · rw [h3, D_three_matrix]
        norm_num
      have hk4 : 4 ≤ k := by omega
      have hrec0 := D_recurrence (k - 3) (by omega)
      have hrec :
          D k = 19 * D (k - 1) + 209 * D (k - 2) + 189 * D (k - 3) := by
        rw [show k - 3 + 3 = k by omega, show k - 3 + 2 = k - 1 by omega,
          show k - 3 + 1 = k - 2 by omega] at hrec0
        exact hrec0
      have hkm1 : D (k - 1) < 0 := ih (k - 1) (by omega) (by omega)
      have hkm2 : D (k - 2) < 0 := ih (k - 2) (by omega) (by omega)
      have hkm3 : D (k - 3) < 0 := ih (k - 3) (by omega) (by omega)
      omega

/-- On every nonzero six-bit dyadic slice the signed difference is negative,
so eligible odious integers strictly outnumber eligible evil integers. -/
theorem D_negative (k : Nat) (hk : 1 ≤ k) :
    D k < 0 ∧ evilCount k < odiousCount k := by
  have hnegative := D_strictly_negative k hk
  constructor
  · exact hnegative
  · rw [D_eq_count_difference] at hnegative
    exact_mod_cast sub_neg.mp hnegative

#print axioms state_eq_transfer_pow
#print axioms eligibility_iff_residue_and_D_eq_transfer
#print axioms annihilating_identity_and_D_recurrence
#print axioms D_negative

end D5.S1.Digit.OdiousMajorityDyadicSlice
