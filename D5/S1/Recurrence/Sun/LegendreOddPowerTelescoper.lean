/- GID: D5/S1/Recurrence/Sun/LegendreOddPowerTelescoper
   generality: G
   mirror-B: D5/B/S1/Recurrence/Sun/LegendreOddPowerTelescoper
   mirror-E: none(waiver:polynomial-identity)
   anchors: []
   utility: none
   digest: Integral telescopers for every odd-power Legendre sum in Cui-Sun Conjecture 2.1. -/

/-
result:
  proof_shape: content
  escape_witness: op_identity_monomial and c_telescoping, both used by g_sum and result.
  admission_basis: open-problem-resolution (#12574; Proved)
Direct frozen dependencies: none; only pinned Mathlib declarations are imported.
Private theorem judgement:
  op_identity_monomial: content; binomial expansion with an inductive pairing of all terms.
  A_iter_degree: content; induction constructs the exact nonzero degree-lowering iterates.
  c_telescoping: content; finite inverse cancellation with a proved terminating coefficient.
  g_sum: content; the operator identity and inverse yield the Legendre telescoping induction.
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Tactic.LinearCombination

namespace D5.S1.Recurrence.Sun.LegendreOddPowerTelescoper

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open Polynomial

/-- The Legendre polynomials defined by Cui-Sun equation (1.1). -/
noncomputable def P : ℕ → ℚ[X]
  | 0 => 1
  | 1 => X
  | n + 2 =>
      ((C (((2 * (n + 1) + 1 : ℕ) : ℚ)) * X * P (n + 1) - C (((n + 1 : ℕ) : ℚ)) * P n) * C (1 / ((n + 2 : ℕ) : ℚ)))

private def aCoeff (i j : ℕ) : ℤ :=
  4 ^ j * (Nat.choose (2 * i) (2 * j)) +
    2 ^ (2 * j - 1) * (Nat.choose (2 * i) (2 * j - 1))

private noncomputable def monoA (i : ℕ) : ℤ[X] :=
  ∑ j ∈ Finset.range i, monomial (i - (j + 1)) (aCoeff i (j + 1))

private noncomputable def A (f : ℤ[X]) : ℤ[X] := f.sum (fun i a => C a * monoA i)

private lemma op_identity_monomial (i : ℕ) (r : ℤ) :
    2 * (r : ℚ) * eval₂ (Int.castRingHom ℚ) ((r : ℚ) ^ 2) (A (monomial i 1)) =
      ((r + 1 : ℤ) : ℚ) * ((r + 2 : ℤ) : ℚ) ^ (2 * i) +
        ((r - 1 : ℤ) : ℚ) * ((r - 2 : ℤ) : ℚ) ^ (2 * i) -
          2 * (r : ℚ) * ((r : ℚ) ^ 2) ^ i := by
  have A_monomial (i : ℕ) : A (monomial i 1) = monoA i := by
    simp [A]
  have eval_monoA (i : ℕ) (r : ℤ) :
      eval₂ (Int.castRingHom ℚ) ((r : ℚ) ^ 2) (monoA i) =
        ∑ j ∈ Finset.range i,
          ((aCoeff i (j + 1) : ℤ) : ℚ) * ((r : ℚ) ^ 2) ^ (i - (j + 1)) := by
    rw [show monoA i = ∑ j ∈ Finset.range i, monomial (i - (j + 1)) (aCoeff i (j + 1)) by rfl]
    rw [eval₂_finsetSum]
    simp [eval₂_monomial]
  have A_eval_monomial (i : ℕ) (r : ℤ) :
      eval₂ (Int.castRingHom ℚ) ((r : ℚ) ^ 2) (A (monomial i 1)) =
        ∑ j ∈ Finset.range i,
          ((aCoeff i (j + 1) : ℤ) : ℚ) * ((r : ℚ) ^ 2) ^ (i - (j + 1)) := by
    rw [A_monomial, eval_monoA]
  have sum_range_pair (F : ℕ → ℚ) (i : ℕ) :
      ∑ k ∈ Finset.range (2 * i + 1), F k =
        F 0 + ∑ j ∈ Finset.range i, (F (2 * (j + 1) - 1) + F (2 * (j + 1))) := by
    induction i with
    | zero => simp
    | succ i ih =>
        have h : 2 * (Nat.succ i) + 1 = (2 * i + 1) + 2 := by omega
        rw [h, Finset.sum_range_succ, Finset.sum_range_succ, ih]
        simp only [Finset.sum_range_succ]
        have h1 : 2 * i + 1 = 2 * (i + 1) - 1 := by omega
        have h2 : 2 * i + 2 = 2 * (i + 1) := by omega
        rw [h1, h2]
        ac_rfl
  rw [A_eval_monomial]
  let rr : ℚ := (r : ℚ)
  have hp : (rr + 2) ^ (2 * i) =
      ∑ k ∈ Finset.range (2 * i + 1),
        ((Nat.choose (2 * i) k : ℚ) * rr ^ (2 * i - k) * (2 : ℚ) ^ k) := by
    rw [add_comm, add_pow]
    congr 1
    funext k
    ring
  have hm : (rr - 2) ^ (2 * i) =
      ∑ k ∈ Finset.range (2 * i + 1),
        ((Nat.choose (2 * i) k : ℚ) * rr ^ (2 * i - k) * (-2 : ℚ) ^ k) := by
    rw [sub_eq_add_neg, add_comm, add_pow]
    congr 1
    funext k
    ring
  simp only [Int.cast_add, Int.cast_sub, Int.cast_one, Int.cast_ofNat]
  change 2 * rr * (∑ j ∈ Finset.range i,
      ((aCoeff i (j + 1) : ℤ) : ℚ) * (rr ^ 2) ^ (i - (j + 1))) =
    (rr + 1) * (rr + 2) ^ (2 * i) + (rr - 1) * (rr - 2) ^ (2 * i) -
      2 * rr * (rr ^ 2) ^ i
  rw [hp, hm]
  rw [sum_range_pair (fun k => (Nat.choose (2 * i) k : ℚ) * rr ^ (2 * i - k) * (2 : ℚ) ^ k) i,
    sum_range_pair (fun k => (Nat.choose (2 * i) k : ℚ) * rr ^ (2 * i - k) * (-2 : ℚ) ^ k) i]
  simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, Nat.sub_zero]
  have hne (j : ℕ) : (-2 : ℚ) ^ (2 * (j + 1)) = (2 : ℚ) ^ (2 * (j + 1)) := by
    norm_num [pow_mul]
  have hno (j : ℕ) : (-2 : ℚ) ^ (2 * (j + 1) - 1) = - (2 : ℚ) ^ (2 * (j + 1) - 1) := by
    have hj : 2 * (j + 1) - 1 = 2 * j + 1 := by omega
    rw [hj]
    norm_num [pow_succ, pow_mul]
  simp_rw [hne, hno]
  have hterm (j : ℕ) (hj : j < i) :
      (rr + 1) *
          (↑((2 * i).choose (2 * (j + 1) - 1)) * rr ^ (2 * i - (2 * (j + 1) - 1)) *
              2 ^ (2 * (j + 1) - 1) +
            ↑((2 * i).choose (2 * (j + 1))) * rr ^ (2 * i - 2 * (j + 1)) *
              2 ^ (2 * (j + 1))) +
        (rr - 1) *
          (↑((2 * i).choose (2 * (j + 1) - 1)) * rr ^ (2 * i - (2 * (j + 1) - 1)) *
              (-2) ^ (2 * (j + 1) - 1) +
            ↑((2 * i).choose (2 * (j + 1))) * rr ^ (2 * i - 2 * (j + 1)) *
              (-2) ^ (2 * (j + 1))) =
      2 * rr * ((aCoeff i (j + 1) : ℤ) : ℚ) * (rr ^ 2) ^ (i - (j + 1)) := by
    have he : 2 * i - 2 * (j + 1) = 2 * (i - (j + 1)) := by omega
    have ho : 2 * i - (2 * (j + 1) - 1) = 2 * (i - (j + 1)) + 1 := by omega
    rw [he, ho, hno j, hne j]
    simp [aCoeff, pow_mul]
    ring
  simp only [one_mul, mul_add, add_mul, sub_mul,
    Finset.mul_sum, Finset.sum_add_distrib]
  repeat rw [← Finset.sum_add_distrib]
  ring_nf
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  convert (hterm j (by simpa using hj)).symm using 1
  · rw [pow_mul]
    simp [Nat.add_comm]
    ring
  · simp [Nat.mul_comm, pow_mul]
    have hne' : (-2 : ℚ) ^ (j * 2) = (2 : ℚ) ^ (j * 2) := by
      calc
        (-2 : ℚ) ^ (j * 2) = (-2 : ℚ) ^ (2 * j) := by congr 1; omega
        _ = ((-2 : ℚ) ^ 2) ^ j := by rw [pow_mul]
        _ = ((2 : ℚ) ^ 2) ^ j := by norm_num
        _ = (2 : ℚ) ^ (2 * j) := by rw [← pow_mul]
        _ = (2 : ℚ) ^ (j * 2) := by congr 1; omega
    have hno' : (-2 : ℚ) ^ (2 + j * 2 - 1) = -(2 : ℚ) ^ (2 + j * 2 - 1) := by
      have hj' : 2 + j * 2 - 1 = 2 * j + 1 := by omega
      rw [hj']
      norm_num [pow_succ, pow_mul]
    have hsq : ((-2 : ℚ) ^ (j + 1)) ^ 2 = ((2 : ℚ) ^ (j + 1)) ^ 2 := by
      rw [← pow_mul, ← pow_mul]
      norm_num
    have hodd : (-2 : ℚ) ^ ((j + 1) * 2 - 1) = -(2 : ℚ) ^ ((j + 1) * 2 - 1) := by
      have hh : (j + 1) * 2 - 1 = 2 * j + 1 := by omega
      rw [hh]
      norm_num [pow_succ, pow_mul]
    rw [hsq, hodd]
    ring

private lemma A_iter_degree (m k : ℕ) (hk : k ≤ m) :
    (A^[k]) (monomial m 1) ≠ 0 ∧
      ((A^[k]) (monomial m 1)).natDegree = m - k := by
  have aCoeff_one_pos {i : ℕ} (hi : 1 ≤ i) : 0 < aCoeff i 1 := by
    have hc : 0 < Nat.choose (2 * i) 2 := Nat.choose_pos (by omega)
    have hc' : 0 < Nat.choose (2 * i) 1 := Nat.choose_pos (by omega)
    have hcZ : 0 < (Nat.choose (2 * i) 2 : ℤ) := by exact_mod_cast hc
    have hcZ' : 0 < (Nat.choose (2 * i) 1 : ℤ) := by exact_mod_cast hc'
    norm_num [aCoeff]
    positivity
  have monoA_coeff_top {i : ℕ} (hi : 1 ≤ i) : (monoA i).coeff (i - 1) = aCoeff i 1 := by
    classical
    rw [monoA]
    simp only [← Polynomial.toFinsupp_apply]
    rw [Polynomial.toFinsupp_sum]
    have hcoeff := AddMonoidAlgebra.coeff_sum (R := ℤ) (M := ℕ) (Finset.range i)
      (fun j => (monomial (i - (j + 1)) (aCoeff i (j + 1))).toFinsupp)
    have hpoint := congrArg (fun q : ℕ →₀ ℤ => q (i - 1)) hcoeff
    rw [hpoint]
    have hsum := map_sum (Finsupp.lapply (R := ℤ) (M := ℤ) (i - 1))
      (fun j => (monomial (i - (j + 1)) (aCoeff i (j + 1))).toFinsupp.coeff)
      (Finset.range i)
    rw [show (∑ j ∈ Finset.range i,
        (monomial (i - (j + 1)) (aCoeff i (j + 1))).toFinsupp.coeff) (i - 1) =
        ∑ j ∈ Finset.range i,
          ((monomial (i - (j + 1)) (aCoeff i (j + 1))).toFinsupp.coeff (i - 1)) by
      simp]
    rw [Finset.sum_eq_single 0]
    · simp
    · intro b hb hne
      have hb' : 1 ≤ b := by omega
      have hb_lt : b < i := Finset.mem_range.mp hb
      have hidx : i - (b + 1) ≠ i - 1 := by omega
      have hidx' : i - 1 ≠ i - (b + 1) := Ne.symm hidx
      simp [Polynomial.toFinsupp_monomial, hidx']
    · intro hzero
      exact False.elim (hzero (Finset.mem_range.mpr hi))
  have monoA_coeff_above {i n : ℕ} (h : i ≤ n) : (monoA i).coeff n = 0 := by
    classical
    rw [monoA]
    simp only [← Polynomial.toFinsupp_apply]
    rw [Polynomial.toFinsupp_sum]
    have hcoeff := AddMonoidAlgebra.coeff_sum (R := ℤ) (M := ℕ) (Finset.range i)
      (fun j => (monomial (i - (j + 1)) (aCoeff i (j + 1))).toFinsupp)
    have hpoint := congrArg (fun q : ℕ →₀ ℤ => q n) hcoeff
    rw [hpoint]
    have hsum := map_sum (Finsupp.lapply (R := ℤ) (M := ℤ) n)
      (fun j => (monomial (i - (j + 1)) (aCoeff i (j + 1))).toFinsupp.coeff)
      (Finset.range i)
    rw [show (∑ j ∈ Finset.range i,
        (monomial (i - (j + 1)) (aCoeff i (j + 1))).toFinsupp.coeff) n =
        ∑ j ∈ Finset.range i,
          ((monomial (i - (j + 1)) (aCoeff i (j + 1))).toFinsupp.coeff n) by
      simp]
    apply Finset.sum_eq_zero
    intro j hj
    simp only [Polynomial.toFinsupp_monomial]
    by_cases hji : i - (j + 1) = n
    · have hj_lt : j < i := Finset.mem_range.mp hj
      have hi_pos : 0 < i := by omega
      have hsub : i - (j + 1) < i := Nat.sub_lt hi_pos (by omega)
      omega
    · simp [hji]
  have A_coeff (f : ℤ[X]) (n : ℕ) :
      (A f).coeff n = ∑ i ∈ f.support, f.coeff i * (monoA i).coeff n := by
    simp [A, Polynomial.sum]
  have support_le_natDegree {f : ℤ[X]} {i : ℕ} (hi : i ∈ f.support) :
      i ≤ f.natDegree := by
    by_contra h
    have hlt : f.natDegree < i := lt_of_not_ge h
    exact (Polynomial.mem_support_iff.mp hi) (Polynomial.coeff_eq_zero_of_natDegree_lt hlt)
  have A_coeff_above (f : ℤ[X]) {n : ℕ} (h : f.natDegree ≤ n) :
      (A f).coeff n = 0 := by
    rw [A_coeff]
    apply Finset.sum_eq_zero
    intro i hi
    rw [monoA_coeff_above (le_trans (support_le_natDegree hi) h)]
    simp
  have A_coeff_top {f : ℤ[X]} (hf : f ≠ 0) (hd : 1 ≤ f.natDegree) :
      (A f).coeff (f.natDegree - 1) =
        f.coeff f.natDegree * aCoeff f.natDegree 1 := by
    rw [A_coeff]
    have htop : f.natDegree ∈ f.support := by
      rw [Polynomial.mem_support_iff]
      rw [Polynomial.coeff_natDegree]
      exact Polynomial.leadingCoeff_ne_zero.mpr hf
    rw [Finset.sum_eq_single f.natDegree]
    · rw [monoA_coeff_top hd]
    · intro i hi hne
      have hil : i ≤ f.natDegree := support_le_natDegree hi
      have hil' : i ≤ f.natDegree - 1 := by omega
      rw [monoA_coeff_above hil']
      simp
    · intro hzero
      exact False.elim (hzero htop)
  have A_natDegree {f : ℤ[X]} (hf : f ≠ 0) (hd : 1 ≤ f.natDegree) :
      (A f).natDegree = f.natDegree - 1 := by
    apply natDegree_eq_of_le_of_coeff_ne_zero
    · rw [natDegree_le_iff_coeff_eq_zero]
      intro n hn
      apply A_coeff_above
      omega
    · rw [A_coeff_top hf hd]
      have hfc : f.coeff f.natDegree ≠ 0 := by
        rw [Polynomial.coeff_natDegree]
        exact Polynomial.leadingCoeff_ne_zero.mpr hf
      exact mul_ne_zero hfc (Int.ne_of_gt (aCoeff_one_pos hd))
  induction k with
  | zero =>
      simp [Function.iterate_zero_apply]
  | succ k ih =>
      have hkm : k ≤ m := le_trans (Nat.le_succ k) hk
      have ih' := ih hkm
      have hdeg : 1 ≤ ((A^[k]) (monomial m 1)).natDegree := by
        rw [ih'.2]
        omega
      have hAdeg := A_natDegree ih'.1 hdeg
      have hne : A ((A^[k]) (monomial m 1)) ≠ 0 := by
        have hc : (A ((A^[k]) (monomial m 1))).coeff
            (((A^[k]) (monomial m 1)).natDegree - 1) ≠ 0 := by
          rw [A_coeff_top ih'.1 hdeg]
          exact mul_ne_zero (by
            rw [Polynomial.coeff_natDegree]
            exact Polynomial.leadingCoeff_ne_zero.mpr ih'.1)
            (Int.ne_of_gt (aCoeff_one_pos hdeg))
        intro hz
        exact hc (by rw [hz]; simp)
      rw [Function.iterate_succ_apply']
      constructor
      · exact hne
      · have harith : m - k - 1 = m - (k + 1) := by omega
        rw [ih'.2, harith] at hAdeg
        exact hAdeg

private noncomputable def c (m k : ℕ) : ℤ[X] :=
  if k ≤ m then (-1 : ℤ) ^ (m - k) • ((A^[m - k]) (monomial m 1)) else 0

private noncomputable def evalZ (r : ℤ) (f : ℤ[X]) : ℚ :=
  eval₂ (Int.castRingHom ℚ) ((r : ℚ) ^ 2) f

private noncomputable def evaluatedL (m : ℕ) (r : ℤ) (t : ℚ[X]) : ℚ[X] :=
  ∑ k ∈ Finset.range (m + 1), C (evalZ r (c m k)) * t ^ k

private lemma c_telescoping (m N : ℕ) (hN : N ≤ m) (r : ℤ) (t : ℚ[X]) :
    ∑ k ∈ Finset.range (N + 1),
        (C (evalZ r (A (c m k))) * t ^ k +
          C (evalZ r (c m k)) * t ^ (k + 1)) =
      C (evalZ r (c m N)) * t ^ (N + 1) := by
  have A_add (f g : ℤ[X]) : A (f + g) = A f + A g := by
    apply Polynomial.sum_add_index
    · intro i
      simp
    · intro i a b
      rw [C_add, add_mul]
  have A_C (a : ℤ) : A (C a) = 0 := by
    change (C a).sum (fun i b => C b * monoA i) = 0
    rw [sum_C_index (by simp [monoA])]
    simp [monoA]
  have A_C_mul (a : ℤ) (f : ℤ[X]) : A (C a * f) = C a * A f := by
    induction f using Polynomial.induction_on' with
    | add p q hp hq =>
        calc
          A (C a * (p + q)) = A (C a * p + C a * q) := by rw [mul_add]
          _ = A (C a * p) + A (C a * q) := A_add _ _
          _ = C a * A p + C a * A q := by rw [hp, hq]
          _ = C a * A (p + q) := by rw [A_add, mul_add]
    | monomial n b =>
        rw [Polynomial.C_mul_monomial]
        simp [A]
        ring
  have c_eq (m k : ℕ) (h : k ≤ m) :
      c m k = (-1 : ℤ) ^ (m - k) • ((A^[m - k]) (monomial m 1)) := by
    simp [c, h]
  have A_c_succ (m k : ℕ) (hk : k < m) : A (c m (k + 1)) = - c m k := by
    have h1 : k + 1 ≤ m := by omega
    rw [c_eq m (k + 1) h1, c_eq m k (by omega)]
    rw [show m - k = (m - (k + 1)) + 1 by omega,
      Function.iterate_succ_apply', Polynomial.smul_eq_C_mul]
    rw [A_C_mul]
    have hp : (-1 : ℤ) ^ (m - (k + 1) + 1) =
        -((-1 : ℤ) ^ (m - (k + 1))) := by
      rw [pow_succ]
      ring
    rw [hp]
    simp
  have A_c_zero (m : ℕ) : A (c m 0) = 0 := by
    rw [c_eq m 0 (by omega), show m - 0 = m by omega]
    rw [show (-1 : ℤ) ^ m • ((A^[m]) (monomial m 1)) =
        C (((-1 : ℤ) ^ m) * ((A^[m]) (monomial m 1)).coeff 0) by
        rw [Polynomial.smul_eq_C_mul]
        rw [show C ((-1 : ℤ) ^ m) * (A^[m]) (monomial m 1) =
            C (((-1 : ℤ) ^ m) * ((A^[m]) (monomial m 1)).coeff 0) by
          have hm := (A_iter_degree m m (le_refl _)).2
          have hle : ((A^[m]) (monomial m 1)).natDegree ≤ 0 := by rw [hm]; omega
          rw [Polynomial.eq_C_of_natDegree_le_zero hle]
          simp]]
    exact A_C _
  induction N with
  | zero =>
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
        pow_zero, mul_one]
      rw [A_c_zero]
      simp [evalZ]
  | succ N ih =>
      have hNm : N ≤ m := le_trans (Nat.le_succ N) hN
      rw [Finset.sum_range_succ, ih hNm]
      rw [A_c_succ m N (by omega)]
      simp only [evalZ]
      simp

private noncomputable def g (m n : ℕ) (t : ℚ[X]) : ℚ[X] :=
    C (n : ℚ) * evaluatedL m (2 * (n : ℤ) + 1) t * P (n - 1) -
      C (n : ℚ) * evaluatedL m (1 - 2 * (n : ℤ)) t * P n

private lemma g_sum (m p : ℕ) :
    (1 - X) ^ (m + 1) *
        (∑ n ∈ Finset.range p,
          C ((2 * n + 1 : ℕ) : ℚ) ^ (2 * m + 1) * P n) =
      g m p (1 - X) := by
  have P_recurrence (n : ℕ) :
      C ((n + 1 : ℕ) : ℚ) * P (n + 1) =
        C ((2 * n + 1 : ℕ) : ℚ) * X * P n - C ((n : ℕ) : ℚ) * P (n - 1) := by
    cases n with
    | zero => simp [P]
    | succ n =>
        rw [show n.succ + 1 = n + 2 by omega]
        change C ((n + 2 : ℕ) : ℚ) *
            (((C (((2 * (n + 1) + 1 : ℕ) : ℚ)) * X * P (n + 1) -
                C (((n + 1 : ℕ) : ℚ)) * P n) *
              C (1 / ((n + 2 : ℕ) : ℚ)))) = _
        have hn : ((n + 2 : ℕ) : ℚ) ≠ 0 := by positivity
        have hc : C ((n + 2 : ℕ) : ℚ) * C (1 / ((n + 2 : ℕ) : ℚ)) = (1 : ℚ[X]) := by
          calc
            C ((n + 2 : ℕ) : ℚ) * C (1 / ((n + 2 : ℕ) : ℚ)) =
                C (((n + 2 : ℕ) : ℚ) * (1 / ((n + 2 : ℕ) : ℚ))) := by rw [C_mul]
            _ = 1 := by rw [one_div, mul_inv_cancel₀ hn, C_1]
        calc
          _ = (C (((2 * (n + 1) + 1 : ℕ) : ℚ)) * X * P (n + 1) -
                C (((n + 1 : ℕ) : ℚ)) * P n) *
              (C ((n + 2 : ℕ) : ℚ) * C (1 / ((n + 2 : ℕ) : ℚ))) := by ring
          _ = _ := by rw [hc]; simp
  have A_monomial (i : ℕ) : A (monomial i 1) = monoA i := by
    simp [A]
  have op_identity (f : ℤ[X]) (r : ℤ) :
      2 * (r : ℚ) * eval₂ (Int.castRingHom ℚ) ((r : ℚ) ^ 2) (A f) =
        ((r + 1 : ℤ) : ℚ) * eval₂ (Int.castRingHom ℚ) (((r + 2 : ℤ) : ℚ) ^ 2) f +
          ((r - 1 : ℤ) : ℚ) * eval₂ (Int.castRingHom ℚ) (((r - 2 : ℤ) : ℚ) ^ 2) f -
            2 * (r : ℚ) * eval₂ (Int.castRingHom ℚ) ((r : ℚ) ^ 2) f := by
    simp only [A, eval₂_sum]
    rw [eval₂_eq_sum, eval₂_eq_sum, eval₂_eq_sum]
    simp only [eval₂_mul, eval₂_C]
    have hmono (n : ℕ) (a : ℤ) :
        2 * (r : ℚ) * ((a : ℚ) * eval₂ (Int.castRingHom ℚ) ((r : ℚ) ^ 2) (monoA n)) =
          ((r + 1 : ℤ) : ℚ) * ((a : ℚ) * ((r + 2 : ℤ) : ℚ) ^ (2 * n)) +
            ((r - 1 : ℤ) : ℚ) * ((a : ℚ) * ((r - 2 : ℤ) : ℚ) ^ (2 * n)) -
              2 * (r : ℚ) * ((a : ℚ) * ((r : ℚ) ^ 2) ^ n) := by
      have h := op_identity_monomial n r
      rw [A_monomial] at h
      calc
        2 * (r : ℚ) * ((a : ℚ) * eval₂ (Int.castRingHom ℚ) ((r : ℚ) ^ 2) (monoA n)) =
            (a : ℚ) * (2 * (r : ℚ) * eval₂ (Int.castRingHom ℚ) ((r : ℚ) ^ 2) (monoA n)) := by ring
        _ = (a : ℚ) * (((r + 1 : ℤ) : ℚ) * ((r + 2 : ℤ) : ℚ) ^ (2 * n) +
            ((r - 1 : ℤ) : ℚ) * ((r - 2 : ℤ) : ℚ) ^ (2 * n) -
              2 * (r : ℚ) * ((r : ℚ) ^ 2) ^ n) := by rw [h]
        _ = _ := by ring
    have hs :
        (∑ n ∈ f.support, 2 * (r : ℚ) * ((f.coeff n : ℚ) *
          eval₂ (Int.castRingHom ℚ) ((r : ℚ) ^ 2) (monoA n))) =
        ∑ n ∈ f.support,
          (((r + 1 : ℤ) : ℚ) * ((f.coeff n : ℚ) * ((r + 2 : ℤ) : ℚ) ^ (2 * n)) +
            ((r - 1 : ℤ) : ℚ) * ((f.coeff n : ℚ) * ((r - 2 : ℤ) : ℚ) ^ (2 * n)) -
              2 * (r : ℚ) * ((f.coeff n : ℚ) * ((r : ℚ) ^ 2) ^ n)) := by
      apply Finset.sum_congr rfl
      intro n hn
      exact hmono n (f.coeff n)
    simpa [Polynomial.sum_def, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul,
      sub_eq_add_neg, add_assoc, add_left_comm, add_comm, pow_mul, Int.cast_add, Int.cast_sub] using hs
  have c_eq (m k : ℕ) (h : k ≤ m) :
      c m k = (-1 : ℤ) ^ (m - k) • ((A^[m - k]) (monomial m 1)) := by
    simp [c, h]
  have c_top (m : ℕ) : c m m = monomial m 1 := by
    rw [c_eq m m (le_refl _)]
    simp [Function.iterate_zero_apply]
  have evalZ_A (r : ℤ) (f : ℤ[X]) :
      2 * (r : ℚ) * evalZ r (A f) =
        ((r + 1 : ℤ) : ℚ) * evalZ (r + 2) f +
          ((r - 1 : ℤ) : ℚ) * evalZ (r - 2) f -
            2 * (r : ℚ) * evalZ r f := by
    simpa [evalZ] using op_identity f r
  have L_bracket (m : ℕ) (r : ℤ) (t : ℚ[X]) :
      C ((r + 1 : ℤ) : ℚ) * evaluatedL m (r + 2) t +
          C ((r - 1 : ℤ) : ℚ) * evaluatedL m (r - 2) t -
            C (2 * (r : ℚ)) * (1 - t) * evaluatedL m r t =
        C (2 * (r : ℚ) * ((r : ℚ) ^ 2) ^ m) * t ^ (m + 1) := by
    have hterm (k : ℕ) :
        C ((r + 1 : ℤ) : ℚ) *
            (C (evalZ (r + 2) (c m k)) * t ^ k) +
          C ((r - 1 : ℤ) : ℚ) *
            (C (evalZ (r - 2) (c m k)) * t ^ k) -
          C (2 * (r : ℚ)) * (1 - t) *
            (C (evalZ r (c m k)) * t ^ k) =
        C (2 * (r : ℚ) * evalZ r (A (c m k))) * t ^ k +
          C (2 * (r : ℚ) * evalZ r (c m k)) * t ^ (k + 1) := by
      rw [evalZ_A]
      simp only [C_add, C_sub, C_mul, pow_succ]
      ring
    simp only [evaluatedL, Finset.mul_sum]
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    calc
      _ = ∑ x ∈ Finset.range (m + 1),
          (C ((2 : ℚ) * (r : ℚ) * evalZ r (A (c m x))) * t ^ x +
            C ((2 : ℚ) * (r : ℚ) * evalZ r (c m x)) * t ^ (x + 1)) := by
            apply Finset.sum_congr rfl
            intro x hx
            exact hterm x
      _ = C (2 * (r : ℚ)) *
          (∑ x ∈ Finset.range (m + 1),
            (C (evalZ r (A (c m x))) * t ^ x +
              C (evalZ r (c m x)) * t ^ (x + 1))) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro x hx
            simp only [C_mul]
            ring
      _ = C (2 * (r : ℚ)) * (C (evalZ r (c m m)) * t ^ (m + 1)) := by
            rw [c_telescoping m m (le_refl _) r t]
      _ = C (2 * (r : ℚ) * ((r : ℚ) ^ 2) ^ m) * t ^ (m + 1) := by
            rw [c_top]
            simp only [evalZ, eval₂_monomial, map_one, one_mul, C_mul]
            ring
  have evalZ_neg (r : ℤ) (f : ℤ[X]) : evalZ (-r) f = evalZ r f := by
    simp [evalZ, pow_two]
  have L_neg (m : ℕ) (r : ℤ) (t : ℚ[X]) : evaluatedL m (-r) t = evaluatedL m r t := by
    simp [evaluatedL, evalZ_neg]
  have g_succ_sub (m n : ℕ) (t : ℚ[X]) :
      (ht : t = 1 - X) →
        g m (n + 1) t - g m n t =
        C ((2 * n + 1 : ℕ) : ℚ) * t ^ (m + 1) *
          C (((2 * n + 1 : ℕ) : ℚ) ^ (2 * m)) * P n := by
    intro ht
    have hX : X = 1 - t := by rw [ht]; ring
    unfold g
    have hrec := P_recurrence n
    have heven1 : evaluatedL m (-(2 * (n : ℤ) + 1)) t = evaluatedL m (2 * (n : ℤ) + 1) t := by
      rw [L_neg]
    have heven2 : evaluatedL m (-(2 * (n : ℤ) - 1)) t = evaluatedL m (2 * (n : ℤ) - 1) t := by
      rw [L_neg]
    have hB := L_bracket m (2 * (n : ℤ) + 1) t
    have hL1 : evaluatedL m (1 - 2 * ((n + 1 : ℕ) : ℤ)) t =
        evaluatedL m (2 * (n : ℤ) + 1) t := by
      have heq : 1 - 2 * ((n + 1 : ℕ) : ℤ) = -(2 * (n : ℤ) + 1) := by push_cast; ring
      rw [heq, heven1]
    have hL2 : evaluatedL m (1 - 2 * (n : ℤ)) t = evaluatedL m (2 * (n : ℤ) - 1) t := by
      have heq : 1 - 2 * (n : ℤ) = -(2 * (n : ℤ) - 1) := by ring
      rw [heq, heven2]
    rw [hL1, hL2] at *
    rw [show 2 * ((n + 1 : ℕ) : ℤ) + 1 = 2 * (n : ℤ) + 3 by push_cast; ring]
    rw [show (n + 1 : ℕ) - 1 = n by omega]
    have hrec_mul := congrArg (fun q : ℚ[X] => evaluatedL m (2 * (n : ℤ) + 1) t * q) hrec
    rw [show C ((n + 1 : ℕ) : ℚ) * evaluatedL m (2 * (n : ℤ) + 1) t * P (n + 1) =
        evaluatedL m (2 * (n : ℤ) + 1) t * (C ((n + 1 : ℕ) : ℚ) * P (n + 1)) by ring]
    rw [hrec_mul]
    apply (mul_left_cancel₀ (show (2 : ℚ[X]) ≠ 0 by norm_num))
    rw [hX]
    ring_nf at hB ⊢
    push_cast at hB ⊢
    norm_num [C_ofNat] at hB ⊢
    have hBmul := congrArg (fun q : ℚ[X] => q * P n) hB
    linear_combination hBmul
  induction p with
  | zero =>
      simp [g]
  | succ p ih =>
      rw [Finset.sum_range_succ]
      calc
        (1 - X) ^ (m + 1) *
            (∑ n ∈ Finset.range p, C ((2 * n + 1 : ℕ) : ℚ) ^ (2 * m + 1) * P n +
              C ((2 * p + 1 : ℕ) : ℚ) ^ (2 * m + 1) * P p) =
            g m p (1 - X) +
              (1 - X) ^ (m + 1) *
                C ((2 * p + 1 : ℕ) : ℚ) ^ (2 * m + 1) * P p := by
                  rw [mul_add, ih]
                  ring
        _ = g m (p + 1) (1 - X) := by
          have h := g_succ_sub m p (1 - X) rfl
          have hpw : C ((2 * p + 1 : ℕ) : ℚ) ^ (2 * m + 1) =
              C ((2 * p + 1 : ℕ) : ℚ) *
                C (((2 * p + 1 : ℕ) : ℚ) ^ (2 * m)) := by
                rw [show 2 * m + 1 = 1 + 2 * m by omega, pow_add, pow_one,
                  ← map_pow, ← C_mul]
          have hterm :
              (1 - X) ^ (m + 1) * C ((2 * p + 1 : ℕ) : ℚ) ^ (2 * m + 1) * P p =
                C ((2 * p + 1 : ℕ) : ℚ) * (1 - X) ^ (m + 1) *
                  C (((2 * p + 1 : ℕ) : ℚ) ^ (2 * m)) * P p := by
            rw [hpw]
            ring
          rw [hterm]
          calc
            g m p (1 - X) +
                C ((2 * p + 1 : ℕ) : ℚ) * (1 - X) ^ (m + 1) *
                  C (((2 * p + 1 : ℕ) : ℚ) ^ (2 * m)) * P p =
                C ((2 * p + 1 : ℕ) : ℚ) * (1 - X) ^ (m + 1) *
                  C (((2 * p + 1 : ℕ) : ℚ) ^ (2 * m)) * P p +
                    g m p (1 - X) := by ring
            _ = g m (p + 1) (1 - X) := (sub_eq_iff_eq_add.mp h).symm

private noncomputable def fcan (m : ℕ) : Fin m → ℤ[X] := fun i => c m i.1

/-- The source-shaped polynomial L_m(p,t), with p in the integers. -/
noncomputable def L (m : ℕ) (f : Fin m → ℤ[X]) (p : ℤ) (t : ℚ[X]) : ℚ[X] :=
  C (((2 * p + 1 : ℤ) : ℚ) ^ (2 * m)) * t ^ m +
    ∑ i ∈ (Finset.range m).attach,
      C (eval₂ (Int.castRingHom ℚ) (((2 * p + 1 : ℤ) : ℚ) ^ 2)
        (f ⟨i.1, Finset.mem_range.mp i.2⟩)) * t ^ i.1

/-- Conjecture 2.1 with the same integral coefficients for every positive p. -/
def claim : Prop := ∀ m : ℕ, 1 ≤ m →
  ∃ f : Fin m → ℤ[X],
    (∀ i, (f i).natDegree = i.1 ∧ f i ≠ 0) ∧
      ∀ p : ℕ, 1 ≤ p →
        (1 - X) ^ (m + 1) *
            (∑ n ∈ Finset.range p,
              C ((2 * n + 1 : ℕ) : ℚ) ^ (2 * m + 1) * P n) =
          C (p : ℚ) * L m f (p : ℤ) (1 - X) * P (p - 1) -
            C (p : ℚ) * L m f (-(p : ℤ)) (1 - X) * P p

/-- Cui-Sun Conjecture 2.1 holds for every positive m and p. -/
theorem result : claim := by
  have c_eq (m k : ℕ) (h : k ≤ m) :
      c m k = (-1 : ℤ) ^ (m - k) • ((A^[m - k]) (monomial m 1)) := by
    simp [c, h]
  have c_top (m : ℕ) : c m m = monomial m 1 := by
    rw [c_eq m m (le_refl _)]
    simp [Function.iterate_zero_apply]
  have c_degree (m k : ℕ) (hkm : k ≤ m) :
      (c m k).natDegree = k := by
    rw [c_eq m k hkm]
    have hsc : (-1 : ℤ) ^ (m - k) ≠ 0 := by norm_num
    rw [Polynomial.natDegree_smul _ hsc, (A_iter_degree m (m - k) (by omega)).2]
    omega
  have c_ne_zero (m k : ℕ) (hkm : k ≤ m) : c m k ≠ 0 := by
    rw [c_eq m k hkm]
    exact smul_ne_zero (by norm_num) (A_iter_degree m (m - k) (by omega)).1
  have evalZ_neg (r : ℤ) (f : ℤ[X]) : evalZ (-r) f = evalZ r f := by
    simp [evalZ, pow_two]
  have L_neg (m : ℕ) (r : ℤ) (t : ℚ[X]) : evaluatedL m (-r) t = evaluatedL m r t := by
    simp [evaluatedL, evalZ_neg]
  have L_eq_Lsrc (m : ℕ) (p : ℤ) (t : ℚ[X]) :
      evaluatedL m (2 * p + 1) t = L m (fcan m) p t := by
    rw [evaluatedL, L, Finset.sum_range_succ]
    rw [c_top]
    have htop : C (evalZ (2 * p + 1) (monomial m 1)) * t ^ m =
        C (((2 * p + 1 : ℤ) : ℚ) ^ (2 * m)) * t ^ m := by
      simp [evalZ, eval₂_monomial, pow_mul]
    rw [htop]
    rw [← Finset.sum_attach]
    simp only [fcan]
    ac_rfl
  have fcan_degree (m : ℕ) (i : Fin m) :
      (fcan m i).natDegree = i.1 ∧ fcan m i ≠ 0 := by
    exact ⟨c_degree m i.1 (by omega), c_ne_zero m i.1 (by omega)⟩
  intro m _hm
  refine ⟨fcan m, fcan_degree m, ?_⟩
  intro p _hp
  have hs := g_sum m p
  unfold g at hs
  rw [L_eq_Lsrc m (p : ℤ)] at hs
  have hneg : 1 - 2 * (p : ℤ) = 2 * (-(p : ℤ)) + 1 := by ring
  rw [hneg, L_eq_Lsrc m (-(p : ℤ))] at hs
  simpa [show (2 * (p : ℤ) + 1) = (2 * p + 1 : ℤ) by rfl,
    show 1 - 2 * (p : ℤ) = -(2 * (p : ℤ) - 1) by ring,
    L_neg] using hs

end D5.S1.Recurrence.Sun.LegendreOddPowerTelescoper
