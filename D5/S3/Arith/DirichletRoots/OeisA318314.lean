/- GID: D5/S3/Arith/DirichletRoots/OeisA318314
   generality: G
   mirror-B: D5/B/S3/Arith/DirichletRoots/OeisA318314
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: [mathlib/module/Mathlib.NumberTheory.ArithmeticFunction.Misc]
   utility: none
   digest: The rational Dirichlet square root of the odd unitary divisor count. -/

import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Tactic

/-! # The source recurrence of OEIS A318314 -/

open scoped BigOperators

namespace D5.S3.Arith.DirichletRoots.OeisA318314

/-- A068068 counts the positive odd unitary divisors. -/
def oddUnitaryCount (n : ℕ) : ℕ :=
  (n.divisors.filter fun d => Odd d ∧ Nat.Coprime d (n / d)).card

/-- The interior divisors in the published recurrence. -/
def interior (n : ℕ) : Finset ℕ :=
  n.divisors.filter fun d => 1 < d ∧ d < n

private lemma interior_bounds {n d : ℕ} (hd : d ∈ interior n) :
    1 < d ∧ d < n ∧ n / d < n := by
  have h := (Finset.mem_filter.mp hd).2
  exact ⟨h.1, h.2, Nat.div_lt_self (by omega) h.1⟩

/-- The actual rational recurrence, extended by zero at index zero. -/
def f (n : ℕ) : ℚ :=
  if hn : 1 < n then
    ((oddUnitaryCount n : ℚ) - ∑ d : interior n,
      f d.val * f (n / d.val)) / 2
  else if n = 1 then 1 else 0
termination_by n
decreasing_by
  all_goals
    have hd := interior_bounds d.property
    omega

/-- The source specification imposes no multiplicativity or nonzero premise. -/
def SourceSpec (u : ℕ → ℚ) : Prop :=
  u 1 = 1 ∧ ∀ n, 1 < n →
    u n = ((oddUnitaryCount n : ℚ) -
      ∑ d ∈ interior n, u d * u (n / d)) / 2

private lemma f_spec : SourceSpec f := by
  constructor
  · rw [f]
    norm_num
  · intro n hn
    rw [f, dite_eq_left hn]
    congr 2
    exact Finset.sum_coe_sort (s := interior n) (f := fun d => f d * f (n / d))

private lemma source_unique {u v : ℕ → ℚ} (hu : SourceSpec u)
    (hv : SourceSpec v) : ∀ n, 0 < n → u n = v n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    by_cases h1 : n = 1
    · subst n
      rw [hu.1, hv.1]
    have hn1 : 1 < n := by omega
    rw [hu.2 n hn1, hv.2 n hn1]
    congr 2
    apply Finset.sum_congr rfl
    intro d hd
    have hb := interior_bounds hd
    have hdiv := (Nat.mem_divisors.mp (Finset.mem_filter.mp hd).1).1
    rw [ih d hb.2.1 (by omega), ih (n / d) hb.2.2]
    exact Nat.div_pos (Nat.le_of_dvd hn hdiv) (by omega)

/-- The recurrence is inhabited, and determines every positive-index value uniquely. -/
theorem source_solution_unique : SourceSpec f ∧
    ∀ u : ℕ → ℚ, SourceSpec u → ∀ n, 0 < n → u n = f n := by
  exact ⟨f_spec, fun _ hu => source_unique hu f_spec⟩

/-- Central-binomial coefficients divided by their unreduced dyadic denominators. -/
def central (e : ℕ) : ℚ := (Nat.centralBinom e : ℚ) / 4 ^ e

private noncomputable def binomialCoefficient (e : ℕ) : ℚ :=
  (-1) ^ e * Ring.choose (-(1 / 2) : ℚ) e

private lemma binomialCoefficient_step (e : ℕ) :
    ((e : ℚ) + 1) * binomialCoefficient (e + 1) =
      ((e : ℚ) + 1 / 2) * binomialCoefficient e := by
  have h := Ring.choose_smul_choose (-(1 / 2) : ℚ) (Nat.le_succ e)
  simp only [Nat.choose_succ_self_right, nsmul_eq_mul, Nat.cast_add,
    Nat.cast_one, Nat.succ_eq_add_one, Nat.add_sub_cancel_left, Ring.choose_one_right] at h
  dsimp [binomialCoefficient]
  rw [pow_succ]
  linear_combination (-((-1 : ℚ) ^ e)) * h

private lemma central_step (e : ℕ) :
    ((e : ℚ) + 1) * central (e + 1) =
      ((e : ℚ) + 1 / 2) * central e := by
  have h : ((e : ℚ) + 1) * (Nat.centralBinom (e + 1) : ℚ) =
      2 * (2 * e + 1) * Nat.centralBinom e := by
    exact_mod_cast Nat.succ_mul_centralBinom_succ e
  dsimp [central]
  rw [pow_succ]
  field_simp
  nlinarith [h]

private lemma central_eq_binomialCoefficient (e : ℕ) :
    central e = binomialCoefficient e := by
  induction e with
  | zero => simp [central, binomialCoefficient]
  | succ e ih =>
    have hc := central_step e
    have hb := binomialCoefficient_step e
    rw [ih] at hc
    have he : (e : ℚ) + 1 ≠ 0 := by positivity
    exact mul_left_cancel₀ he (hc.trans hb.symm)

private lemma negative_one_choose (e : ℕ) :
    Ring.choose (-1 : ℚ) e = (-1 : ℚ) ^ e := by
  simpa [Units.smul_def, Int.cast_negOnePow_natCast] using (Ring.choose_neg' (1 : ℚ) e)

private lemma central_convolution (e : ℕ) :
    (∑ ij ∈ Finset.antidiagonal e, central ij.1 * central ij.2) = 1 := by
  simp_rw [central_eq_binomialCoefficient, binomialCoefficient]
  calc
    _ = (-1 : ℚ) ^ e *
        ∑ ij ∈ Finset.antidiagonal e,
          Ring.choose (-(1 / 2) : ℚ) ij.1 *
          Ring.choose (-(1 / 2) : ℚ) ij.2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ij hij
      have h := Finset.mem_antidiagonal.mp hij
      rw [← h, pow_add]
      ring
    _ = (-1 : ℚ) ^ e * Ring.choose (-1 : ℚ) e := by
      congr 1
      have h := Ring.add_choose_eq e (Commute.all (-(1 / 2) : ℚ) (-(1 / 2)))
      norm_num at h
      exact h.symm
    _ = 1 := by rw [negative_one_choose, ← mul_pow]; norm_num

/-- The central coefficients are positive and have the required local square. -/
theorem central_local_square (e : ℕ) : 0 < central e ∧
    (∑ ij ∈ Finset.antidiagonal e, central ij.1 * central ij.2) = 1 := by
  constructor
  · dsimp [central]
    exact div_pos (by exact_mod_cast Nat.centralBinom_pos e) (by positivity)
  · exact central_convolution e

/-- A000120, including its zero value. -/
def binaryWeight (e : ℕ) : ℕ := (Nat.digits 2 e).sum

private lemma binaryWeight_le (e : ℕ) : binaryWeight e ≤ e :=
  Nat.digit_sum_le 2 e

private lemma binaryWeight_double (e : ℕ) : binaryWeight (2 * e) = binaryWeight e := by
  by_cases he : e = 0
  · subst e; simp [binaryWeight]
  · simp [binaryWeight, Nat.digits_base_mul (by decide : 1 < 2) (Nat.pos_of_ne_zero he)]

private lemma central_valuation (e : ℕ) :
    padicValNat 2 (Nat.centralBinom e) = binaryWeight e := by
  have h := sub_one_mul_padicValNat_choose_eq_sub_sum_digits'
    (p := 2) (n := e) (k := e)
  change (2 - 1) * padicValNat 2 ((e + e).choose e) =
    binaryWeight e + binaryWeight e - binaryWeight (e + e) at h
  rw [← two_mul, binaryWeight_double] at h
  simpa [Nat.centralBinom, Nat.add_sub_cancel_left] using h

private lemma central_reduced (e : ℕ) :
    ∃ q : ℕ, ¬ 2 ∣ q ∧
      central e = (q : ℚ) / 2 ^ (2 * e - binaryWeight e) := by
  have hc : Nat.centralBinom e ≠ 0 := (Nat.centralBinom_pos e).ne'
  have hd : 2 ^ binaryWeight e ∣ Nat.centralBinom e := by
    rw [padicValNat_dvd_iff_le hc, central_valuation]
  let q := Nat.centralBinom e / 2 ^ binaryWeight e
  have hq : q ≠ 0 := by
    intro hz
    have hmul := Nat.div_mul_cancel hd
    change q * 2 ^ binaryWeight e = Nat.centralBinom e at hmul
    rw [hz, zero_mul] at hmul
    exact hc hmul.symm
  have hv : padicValNat 2 q = 0 := by
    dsimp [q]
    rw [padicValNat.div_pow hd, central_valuation, Nat.sub_self]
  refine ⟨q, ?_, ?_⟩
  · intro ht
    have h := (dvd_iff_padicValNat_ne_zero hq).mp ht
    exact h hv
  · have hmul : q * 2 ^ binaryWeight e = Nat.centralBinom e := Nat.div_mul_cancel hd
    have hexp : binaryWeight e + (2 * e - binaryWeight e) = 2 * e := by
      have := binaryWeight_le e
      omega
    have hcast : (q : ℚ) * 2 ^ binaryWeight e = (Nat.centralBinom e : ℚ) := by
      exact_mod_cast hmul
    dsimp [central]
    rw [show (4 : ℚ) ^ e = 2 ^ (2 * e) by rw [pow_mul]; norm_num]
    apply (div_eq_div_iff (by positivity) (by positivity)).mpr
    rw [← hcast, mul_assoc, ← pow_add, hexp]

/-- The reduced central coefficient has exactly the predicted denominator. -/
theorem central_denominator (e : ℕ) :
    (central e).den = 2 ^ (2 * e - binaryWeight e) ∧
    ((2 * e - binaryWeight e : ℕ) : ℤ) = 2 * (e : ℤ) - binaryWeight e := by
  constructor
  · obtain ⟨q, hq, hr⟩ := central_reduced e
    rw [hr]
    have hcop := Nat.prime_two.coprime_pow_of_not_dvd
      (m := 2 * e - binaryWeight e) hq
    have hh := Rat.den_div_eq_of_coprime
      (a := (q : ℤ)) (b := ((2 ^ (2 * e - binaryWeight e) : ℕ) : ℤ))
      (by positivity) (by simpa using hcop)
    have hcast : (((q : ℚ) / 2 ^ (2 * e - binaryWeight e)).den : ℤ) =
        ((2 ^ (2 * e - binaryWeight e) : ℕ) : ℤ) := by
      simpa only [Int.cast_natCast, Int.cast_pow, Int.cast_ofNat,
        Nat.cast_pow, Nat.cast_ofNat] using hh
    exact Int.ofNat_inj.mp hcast
  · rw [Nat.cast_sub (by have := binaryWeight_le e; omega)]
    norm_cast

private lemma binaryWeight_split (e : ℕ) :
    binaryWeight e = e % 2 + binaryWeight (e / 2) := by
  by_cases he : e = 0
  · subst e; simp [binaryWeight]
  · unfold binaryWeight
    rw [Nat.digits_eq_cons_digits_div (by decide : 1 < 2) he, List.sum_cons]

/-- A005187 is defined by its own halving recurrence. -/
def halvingSum (e : ℕ) : ℕ :=
  if he : e = 0 then 0 else e + halvingSum (e / 2)
termination_by e
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero he) (by decide)

private lemma halvingSum_eq (e : ℕ) : halvingSum e = 2 * e - binaryWeight e := by
  induction e using Nat.strong_induction_on with
  | h e ih =>
    by_cases he : e = 0
    · subst e; simp [halvingSum, binaryWeight]
    · rw [halvingSum, dif_neg he, ih (e / 2)
        (Nat.div_lt_self (Nat.pos_of_ne_zero he) (by decide))]
      have hs := binaryWeight_split e
      have hle := binaryWeight_le (e / 2)
      have hle' := binaryWeight_le e
      omega

/-- Local rational coefficients in the global Euler-product construction. -/
def localCoefficient (p e : ℕ) : ℚ :=
  if p = 2 then central e else central (e / 2)

private lemma odd_exponent (e : ℕ) :
    2 * (e / 2) - binaryWeight (e / 2) = e - binaryWeight e := by
  have hs := binaryWeight_split e
  have hle := binaryWeight_le (e / 2)
  omega

/-- All local denominator formulas, with faithful integer subtraction. -/
theorem local_denominators :
    (∀ e, (localCoefficient 2 e).den = 2 ^ halvingSum e) ∧
    (∀ p e, Nat.Prime p → p ≠ 2 →
      (localCoefficient p e).den = 2 ^ (e - binaryWeight e)) ∧
    (∀ p e, Nat.Prime p →
      (localCoefficient p e).den = 2 ^ ((2 - p % 2) * e - binaryWeight e) ∧
      (((2 - p % 2) * e - binaryWeight e : ℕ) : ℤ) =
        (2 - (p : ℤ) % 2) * e - binaryWeight e) := by
  have htwo (e : ℕ) : (localCoefficient 2 e).den = 2 ^ (2 * e - binaryWeight e) := by
    simpa [localCoefficient] using (central_denominator e).1
  have hodd (p e : ℕ) (hp : p ≠ 2) :
      (localCoefficient p e).den = 2 ^ (e - binaryWeight e) := by
    simpa [localCoefficient, hp, odd_exponent] using (central_denominator (e / 2)).1
  refine ⟨?_, ?_, ?_⟩
  · intro e
    rw [htwo, halvingSum_eq]
  · intro p e _ hp
    exact hodd p e hp
  · intro p e hp
    by_cases hp2 : p = 2
    · subst p
      constructor
      · simpa using htwo e
      · simpa using (central_denominator e).2
    · have hm : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
      have hmi : (p : ℤ) % 2 = 1 := by exact_mod_cast hm
      rw [hm, hmi]
      norm_num
      refine ⟨hodd p e hp2, ?_⟩
      exact Nat.cast_sub (binaryWeight_le e)

end D5.S3.Arith.DirichletRoots.OeisA318314
