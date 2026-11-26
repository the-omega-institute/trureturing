/- GID: D5/S3/Combinatorics/BinomialBases/HussainA402341CentralCoefficientValuation
   generality: G
   mirror-B: D5/B/S3/Combinatorics/BinomialBases/HussainA402341CentralCoefficientValuation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Exact binary valuations of central coefficients of even geometric powers. -/

import OmegaBuild.Commands
import Mathlib.Algebra.Polynomial.Homogenize
import Mathlib.Data.Nat.Choose.Central
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Binary valuation of the even central coefficients of OEIS A402341 -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Polynomial Finset
open scoped BigOperators Nat

namespace D5.S3.Combinatorics.BinomialBases.HussainA402341CentralCoefficientValuation

private local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- The binary digit sum. -/
private def weight (n : ℕ) : ℕ := (Nat.digits 2 n).sum

@[simp] private theorem weight_zero : weight 0 = 0 := by simp [weight]

private theorem weight_double (n : ℕ) : weight (2 * n) = weight n := by
  by_cases hn : n = 0
  · simp [hn]
  · simp [weight, Nat.digits_base_mul (by decide : 1 < (2 : ℕ)) (Nat.pos_of_ne_zero hn)]

private theorem factorial_val (n : ℕ) : padicValNat 2 n ! + weight n = n := by
  have h := sub_one_mul_padicValNat_factorial (p := 2) n
  have hle := Nat.digit_sum_le 2 n
  have heq : padicValNat 2 n ! = n - weight n := by simpa [weight] using h
  change weight n ≤ n at hle
  omega

private theorem weight_pos {n : ℕ} (hn : 0 < n) : 0 < weight n := by
  have hlt := padicValNat_factorial_lt_of_ne_zero 2 hn.ne'
  have heq := factorial_val n
  omega

/-- The unsaturated binary carry identity, obtained from the factorial identity. -/
private theorem carry (a b : ℕ) :
    padicValNat 2 ((a + b).choose b) + weight (a + b) = weight a + weight b := by
  have hchoose := Nat.choose_ne_zero (Nat.le_add_left b a)
  have h := congrArg (padicValNat 2) (Nat.add_choose_mul_factorial_mul_factorial a b)
  rw [padicValNat.mul (mul_ne_zero hchoose (Nat.factorial_ne_zero a)) (Nat.factorial_ne_zero b),
    padicValNat.mul hchoose (Nat.factorial_ne_zero a)] at h
  have ha := factorial_val a
  have hb := factorial_val b
  have hab := factorial_val (a + b)
  omega

private theorem weight_add_le (a b : ℕ) : weight (a + b) ≤ weight a + weight b := by
  have := carry a b
  omega

private theorem central_val (m : ℕ) : padicValNat 2 m.centralBinom = weight m := by
  have h := carry m m
  rw [← two_mul, weight_double, ← Nat.centralBinom_eq_two_mul_choose] at h
  omega

private theorem int_pow_dvd_of_le {a b : ℕ} (h : a ≤ b) : (2 : ℤ) ^ a ∣ 2 ^ b :=
  pow_dvd_pow _ h

private theorem int_two_pow_dvd_cast (e n : ℕ) :
    ((2 : ℤ) ^ e ∣ (n : ℤ)) ↔ (2 : ℕ) ^ e ∣ n := by
  exact_mod_cast (Int.natCast_dvd_natCast (m := 2 ^ e) (n := n))

/-- A polynomial whose positive coefficients have one extra factor of two. -/
private def Strong (f : ℤ[X]) : Prop := ∀ j : ℕ, 0 < j → (2 : ℤ) ^ (1 + weight j) ∣ f.coeff j

/-- The square of a polynomial with the digit-sum divisibility has the extra factor. -/
private theorem strong_square (f : ℤ[X]) (hf : ∀ j : ℕ, (2 : ℤ) ^ weight j ∣ f.coeff j) :
    Strong (f ^ 2) := by
  intro j hj
  rw [pow_two, coeff_mul]
  let term (p : ℕ × ℕ) : ℤ := f.coeff p.1 * f.coeff p.2
  let paired (p : ℕ × ℕ) : ℤ :=
    if p.1 < p.2 then 2 * term p else if p.1 = p.2 then term p else 0
  have hsplit : ∀ p : ℕ × ℕ, paired p + paired p.swap = term p + term p := by
    intro p
    rcases lt_trichotomy p.1 p.2 with h | h | h
    · simp [paired, term, h, h.ne', h.not_gt, two_mul]
    · simp [paired, term, h]
    · simp [paired, term, h, h.ne', h.not_gt, two_mul, mul_comm]
  have hsum : (∑ p ∈ antidiagonal j, paired p) = ∑ p ∈ antidiagonal j, term p := by
    have h := Finset.sum_congr (rfl : antidiagonal j = antidiagonal j)
      (fun p _ => hsplit p)
    simp only [Finset.sum_add_distrib, Finset.Nat.sum_antidiagonal_swap] at h
    omega
  change (2 : ℤ) ^ (1 + weight j) ∣ ∑ p ∈ antidiagonal j, term p
  rw [← hsum]
  apply Finset.dvd_sum
  intro p hp
  have hdeg : p.1 + p.2 = j := Finset.mem_antidiagonal.mp hp
  have hproduct : (2 : ℤ) ^ (weight p.1 + weight p.2) ∣ term p := by
    rw [pow_add]
    exact mul_dvd_mul (hf p.1) (hf p.2)
  by_cases hlt : p.1 < p.2
  · rw [show paired p = 2 * term p by simp [paired, hlt]]
    have hle : weight j ≤ weight p.1 + weight p.2 := by
      simpa [hdeg] using weight_add_le p.1 p.2
    refine (int_pow_dvd_of_le (Nat.add_le_add_left hle 1)).trans ?_
    rw [pow_add, pow_one]
    exact mul_dvd_mul_left 2 hproduct
  by_cases heq : p.1 = p.2
  · rw [show paired p = term p by simp [paired, heq]]
    refine (int_pow_dvd_of_le ?_).trans hproduct
    have hj' : 2 * p.1 = j := by omega
    have hw : weight j = weight p.1 := by rw [← hj', weight_double]
    have hpos := weight_pos (n := p.1) (by omega)
    have hweights := congrArg weight heq
    omega
  · simp [paired, hlt, heq]

private theorem strong_mul {f g : ℤ[X]} (hf : Strong f) (hg : Strong g) : Strong (f * g) := by
  intro j hj
  rw [coeff_mul]
  apply Finset.dvd_sum
  intro p hp
  have hdeg : p.1 + p.2 = j := Finset.mem_antidiagonal.mp hp
  by_cases ha : p.1 = 0
  · have hb : p.2 = j := by omega
    rw [ha, hb]
    exact dvd_mul_of_dvd_right (hg j hj) _
  by_cases hb : p.2 = 0
  · have ha' : p.1 = j := by omega
    rw [ha', hb]
    exact dvd_mul_of_dvd_left (hf j hj) _
  have hle : 1 + weight j ≤ (1 + weight p.1) + (1 + weight p.2) := by
    have := weight_add_le p.1 p.2
    rw [hdeg] at this
    omega
  apply dvd_trans (int_pow_dvd_of_le hle)
  rw [pow_add]
  exact mul_dvd_mul (hf _ (Nat.pos_of_ne_zero ha)) (hg _ (Nat.pos_of_ne_zero hb))

private theorem strong_pow {f : ℤ[X]} (hf : Strong f) (k : ℕ) : Strong (f ^ k) := by
  induction k with
  | zero =>
    intro j hj
    simp [Polynomial.coeff_one, hj.ne']
  | succ k ih => rw [pow_succ]; exact strong_mul ih hf

/-- The ordinary polynomial obtained by substituting X and (1 + X)^2
    into the degree-m homogenization of f. -/
private noncomputable def lift (m : ℕ) (f : ℤ[X]) : ℤ[X] :=
  MvPolynomial.aeval ![X, (1 + X) ^ 2] (f.homogenize m)

private theorem lift_mul {a b : ℕ} {f g : ℤ[X]}
    (hf : f.natDegree ≤ a) (hg : g.natDegree ≤ b) :
    lift (a + b) (f * g) = lift a f * lift b g := by
  rw [lift, homogenize_mul _ _ hf hg, map_mul]
  rfl

private theorem lift_pow {a : ℕ} {f : ℤ[X]} (hf : f.natDegree ≤ a) (k : ℕ) :
    lift (a * k) (f ^ k) = (lift a f) ^ k := by
  induction k with
  | zero => simp [lift]
  | succ k ih =>
    rw [Nat.mul_succ, pow_succ f, lift_mul ?_ hf, ih, pow_succ]
    simpa [Nat.mul_comm] using natDegree_pow_le_of_le k hf

private theorem lift_expansion (m : ℕ) (f : ℤ[X]) :
    lift m f = ∑ j ∈ range (m + 1), C (f.coeff j) * X ^ j * (1 + X) ^ (2 * (m - j)) := by
  rw [lift, homogenize, map_sum, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply Finset.sum_congr rfl
  intro j hj
  rw [MvPolynomial.aeval_monomial, Finsupp.prod_fintype, Fin.prod_univ_two] <;>
    simp [← pow_mul, mul_assoc]

private theorem lift_pad (m : ℕ) (f : ℤ[X]) (hf : f.natDegree ≤ m) :
    lift (m + 1) f = (1 + X) ^ 2 * lift m f := by
  have h : lift 1 (1 : ℤ[X]) = (1 + X) ^ 2 := by simp [lift]
  rw [← h, mul_comm, ← lift_mul hf (by simp), mul_one]

private theorem lift_central_coeff (m : ℕ) (f : ℤ[X]) :
    (lift m f).coeff m = ∑ j ∈ range (m + 1), f.coeff j * ((m - j).centralBinom : ℤ) := by
  rw [lift_expansion, finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro j hj
  have hjm : j ≤ m := by simpa using hj
  rw [mul_assoc, coeff_C_mul, coeff_X_pow_mul', ite_eq_left hjm, coeff_one_add_X_pow,
    Nat.centralBinom_eq_two_mul_choose]

/-- The coefficient of the lifted polynomial has the central binomial valuation
    whenever it is the cast of a natural number, the constant coefficient is one,
    and the other coefficients satisfy the digit-sum divisibility. -/
private theorem valuation_of_lift (m c : ℕ) (f : ℤ[X]) (hf₀ : f.coeff 0 = 1)
    (hf : Strong f) (hc : (c : ℤ) = (lift m f).coeff m) :
    0 < c ∧ padicValNat 2 c = weight m := by
  let term (j : ℕ) := f.coeff j * ((m - j).centralBinom : ℤ)
  let remainder := ∑ j ∈ (range (m + 1)).erase 0, term j
  have hsplit : (c : ℤ) = (m.centralBinom : ℤ) + remainder := by
    rw [hc, lift_central_coeff]
    change ∑ j ∈ range (m + 1), term j = _
    rw [← Finset.sum_erase_add _ _ (by simp : 0 ∈ range (m + 1)), add_comm]
    simp [term, hf₀, remainder]
  have hbinom (k : ℕ) : (2 : ℤ) ^ weight k ∣ (k.centralBinom : ℤ) := by
    rw [int_two_pow_dvd_cast, padicValNat_dvd_iff_le (Nat.centralBinom_ne_zero k), central_val]
  have hrest : (2 : ℤ) ^ (1 + weight m) ∣ remainder := by
    apply Finset.dvd_sum
    intro j hj
    have hjpos := Nat.pos_of_ne_zero (Finset.mem_erase.mp hj).1
    have hjle : j ≤ m := by simpa using (Finset.mem_erase.mp hj).2
    have hle : 1 + weight m ≤ (1 + weight j) + weight (m - j) := by
      have h := weight_add_le j (m - j)
      rw [Nat.add_sub_of_le hjle] at h
      omega
    apply dvd_trans (int_pow_dvd_of_le hle)
    rw [pow_add]
    exact mul_dvd_mul (hf j hjpos) (hbinom (m - j))
  have hlo : (2 : ℕ) ^ weight m ∣ c := by
    rw [← int_two_pow_dvd_cast, hsplit]
    exact dvd_add (hbinom m) (dvd_trans (int_pow_dvd_of_le (by omega)) hrest)
  have hhi : ¬ (2 : ℕ) ^ (1 + weight m) ∣ c := by
    rw [← int_two_pow_dvd_cast, hsplit]
    intro h
    have h' := dvd_sub h hrest
    rw [add_sub_cancel_right, int_two_pow_dvd_cast,
      padicValNat_dvd_iff_le (Nat.centralBinom_ne_zero m), central_val] at h'
    omega
  have hc' : c ≠ 0 := by
    intro hz
    exact hhi (hz ▸ dvd_zero _)
  rw [padicValNat_dvd_iff_le hc'] at hlo hhi
  exact ⟨Nat.pos_of_ne_zero hc', by omega⟩

private def h (j : ℕ) : ℤ := ([1, -14, 78, -220, 330, -252, 84, -8] : List ℤ)[j]?.getD 0

private noncomputable def H : ℤ[X] := ∑ j ∈ range 8, monomial j (h j)

private theorem H_coeff (j : ℕ) :
    H.coeff j = if j < 8 then h j else 0 := by
  simp only [H, finsetSum_coeff, coeff_monomial]
  rw [Finset.sum_ite_eq']
  simp

private theorem H_degree : H.natDegree ≤ 7 := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro j hj
  simp [H_coeff, show ¬ j < 8 by omega]

private theorem H_pow_degree (n : ℕ) : (H ^ n).natDegree ≤ 7 * n := by
  simpa [Nat.mul_comm] using natDegree_pow_le_of_le n H_degree

private theorem H_weak (j : ℕ) : (2 : ℤ) ^ weight j ∣ H.coeff j := by
  rw [H_coeff]
  split
  next hj =>
    interval_cases j <;> decide
  next => exact dvd_zero _

private theorem H_coeff_zero : H.coeff 0 = 1 := by norm_num [H_coeff, h]

private theorem geometric_basis :
    (∑ j ∈ range 16, (X : ℤ[X]) ^ j) =
      ∑ j ∈ range 8, C (h j) * X ^ j * (1 + X) ^ (15 - 2 * j) := by
  simp [Finset.sum_range_succ, h]
  ring

private theorem geometric_identity :
    (∑ j ∈ range 16, (X : ℤ[X]) ^ j) = (1 + X) * lift 7 H := by
  rw [geometric_basis, lift_expansion, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Finset.mem_range.mp hj
  have hexp : 15 - 2 * j = 2 * (7 - j) + 1 := by omega
  rw [H_coeff, ite_eq_left hj', hexp, pow_succ]
  ring

private theorem geometric_square :
    (∑ j ∈ range 16, (X : ℤ[X]) ^ j) ^ 2 = lift 15 (H ^ 2) := by
  have hd : (H ^ 2).natDegree ≤ 14 := H_pow_degree 2
  have hl : lift 14 (H ^ 2) = (lift 7 H) ^ 2 := lift_pow H_degree 2
  rw [geometric_identity, mul_pow, show 15 = 14 + 1 by decide, lift_pad _ _ hd, hl]

/-- The literal coefficient at index 15*n/2 is positive and has the conjectured valuation
    for every even natural n, including zero. -/
theorem result (n : ℕ) (hn : Even n) :
    0 < (((∑ j ∈ range 16, (X : ℕ[X]) ^ j) ^ n).coeff (15 * n / 2)) ∧
    padicValNat 2 (((∑ j ∈ range 16, (X : ℕ[X]) ^ j) ^ n).coeff (15 * n / 2)) =
      (Nat.digits 2 (15 * n / 2)).sum := by
  obtain ⟨k, hk⟩ := hn
  have hnk : n = 2 * k := by omega
  have hm : 15 * n / 2 = 15 * k := by omega
  rw [hm, hnk]
  -- The support of H^(2*k) ends by 14*k, within the lifting degree 15*k.
  have hd : (H ^ 2).natDegree ≤ 15 := (H_pow_degree 2).trans (by decide)
  have hs : Strong ((H ^ 2) ^ k) := strong_pow (strong_square H H_weak) k
  have hc₀ : (((H ^ 2) ^ k).coeff 0) = 1 := by
    change Polynomial.constantCoeff ((H ^ 2) ^ k) = 1
    simp [map_pow, show Polynomial.constantCoeff H = 1 from H_coeff_zero]
  apply valuation_of_lift (15 * k) _ ((H ^ 2) ^ k) hc₀ hs
  let natToInt : ℕ →+* ℤ := Nat.castRingHom ℤ
  change natToInt _ = _
  rw [← coeff_map]
  simp only [Polynomial.map_pow, Polynomial.map_sum, Polynomial.map_X]
  rw [pow_mul, geometric_square, ← lift_pow hd]

end D5.S3.Combinatorics.BinomialBases.HussainA402341CentralCoefficientValuation
