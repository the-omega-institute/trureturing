/- GID: D5/S3/Arith/DirichletRoots/OeisA318314
   generality: G
   mirror-B: D5/B/S3/Arith/DirichletRoots/OeisA318314
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: [mathlib/module/Mathlib.NumberTheory.ArithmeticFunction.Misc]
   utility: none
   digest: The rational Dirichlet square root of the odd unitary divisor count. -/


/-
The external question is the whole proposition WholeBlock, preregistered in
https://github.com/the-omega-institute/trureturing/issues/27584#issuecomment-6703336229.
Admission basis for a completed whole result: open-problem-resolution.
The current component declarations do not constitute that result.

Provisional proof_shape and actual consumers:
source_solution_unique: content; source_convolution (unit head).
central_local_square: content; root_positive (positivity).
central_denominator: bind-only; local_denominators.
local_denominators: bind-only; whole-block assembly remains unfinished.
root_structure: bind-only; whole-block assembly remains unfinished.
root_denominator: content; whole-block assembly remains unfinished.
odd_local_square: content; root_square_prime_power.
source_convolution: bind-only; global source identification remains unfinished.
auxiliary_structure: bind-only; whole-block assembly remains unfinished.
root_square_prime_power: content; global source identification remains unfinished.
The unfinished assembly does not grant admission to unconsumed bind-only components.

Direct pre-existing suppliers are pinned Mathlib declarations; no D5 frozen
mathematical declaration is imported. The new induction identifying central
coefficients with generalized binomial coefficients and the finite-product
odd-numerator invariant are candidate live content; no independent form approval
or whole-result escape witness is asserted.
-/

import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
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
    · rw [halvingSum, dite_eq_right he, ih (e / 2)
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

/-- Independently prescribed A317934, as its Euler product. -/
def auxiliary (n : ℕ) : ℕ :=
  n.factorization.prod fun _ e => 2 ^ (e - binaryWeight e)

/-- A006519 on positive indices. -/
def twoPart (n : ℕ) : ℕ := 2 ^ n.factorization 2

/-- The denominator is taken from the rational recurrence, never defined by a formula. -/
def a (n : ℕ) : ℕ := (f n).den

/-- The full published block, including every endpoint and integer-exponent correspondence. -/
def WholeBlock : Prop :=
  SourceSpec f ∧
  (∀ u : ℕ → ℚ, SourceSpec u → ∀ n, 0 < n → u n = f n) ∧
  (∀ n, 0 < n → a n = twoPart n * auxiliary n) ∧
  a 1 = 1 ∧
  (∀ m n, 0 < m → 0 < n → Nat.Coprime m n → a (m * n) = a m * a n) ∧
  (∀ e, a (2 ^ e) = 2 ^ halvingSum e) ∧
  (∀ p e, Nat.Prime p → p ≠ 2 → a (p ^ e) = 2 ^ (e - binaryWeight e)) ∧
  (∀ p e, Nat.Prime p →
    a (p ^ e) = 2 ^ ((2 - p % 2) * e - binaryWeight e) ∧
    (((2 - p % 2) * e - binaryWeight e : ℕ) : ℤ) =
      (2 - (p : ℤ) % 2) * e - binaryWeight e)

/-- A rational Euler product, independent of the source recurrence. -/
def root : ArithmeticFunction ℚ where
  toFun n := if n = 0 then 0 else n.factorization.prod localCoefficient
  map_zero' := by simp

private lemma localCoefficient_zero (p : ℕ) : localCoefficient p 0 = 1 := by
  simp [localCoefficient, central]

private lemma root_multiplicative : root.IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  constructor
  · simp [root]
  · intro m n hm hn hmn
    change (if m * n = 0 then 0 else (m * n).factorization.prod localCoefficient) =
      (if m = 0 then 0 else m.factorization.prod localCoefficient) *
      (if n = 0 then 0 else n.factorization.prod localCoefficient)
    rw [ite_eq_right (mul_ne_zero hm hn), ite_eq_right hm, ite_eq_right hn,
      Nat.factorization_mul_of_coprime hmn,
      Finsupp.prod_add_index_of_disjoint hmn.disjoint_primeFactors]

private lemma root_prime_power {p e : ℕ} (hp : Nat.Prime p) :
    root (p ^ e) = localCoefficient p e := by
  change (if p ^ e = 0 then 0 else (p ^ e).factorization.prod localCoefficient) = _
  rw [ite_eq_right (pow_ne_zero _ hp.ne_zero), hp.factorization_pow,
    Finsupp.prod_single_index (localCoefficient_zero p)]

private lemma root_positive {n : ℕ} (hn : 0 < n) : 0 < root n := by
  change 0 < if n = 0 then 0 else n.factorization.prod localCoefficient
  rw [ite_eq_right (Nat.ne_of_gt hn)]
  apply Finset.prod_pos
  intro p _
  dsimp [localCoefficient]
  split_ifs
  · exact (central_local_square _).1
  · exact (central_local_square _).1

/-- The independently constructed rational root is multiplicative and strictly positive. -/
theorem root_structure : root.IsMultiplicative ∧
    (∀ p e, Nat.Prime p → root (p ^ e) = localCoefficient p e) ∧
    (∀ n, 0 < n → 0 < root n) := by
  exact ⟨root_multiplicative, fun _ _ hp => root_prime_power hp,
    fun _ hn => root_positive hn⟩

private def localExponent (p e : ℕ) : ℕ :=
  if p = 2 then 2 * e - binaryWeight e else e - binaryWeight e

private lemma local_reduced (p e : ℕ) : ∃ q : ℕ, ¬ 2 ∣ q ∧
    localCoefficient p e = (q : ℚ) / 2 ^ localExponent p e := by
  by_cases hp : p = 2
  · subst p
    simpa [localCoefficient, localExponent] using central_reduced e
  · simpa [localCoefficient, localExponent, hp, odd_exponent] using central_reduced (e / 2)

private lemma product_reduced (s : Finset ℕ) (k : ℕ → ℕ) :
    ∃ q : ℕ, ¬ 2 ∣ q ∧
      (∏ p ∈ s, localCoefficient p (k p)) =
        (q : ℚ) / 2 ^ (∑ p ∈ s, localExponent p (k p)) := by
  induction s using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, by simp⟩
  | @insert p s hp ih =>
    obtain ⟨q, hq, hqr⟩ := ih
    obtain ⟨r, hr, hrr⟩ := local_reduced p (k p)
    refine ⟨r * q, ?_, ?_⟩
    · intro h
      exact (Nat.prime_two.dvd_mul.mp h).elim hr hq
    · rw [Finset.prod_insert hp, Finset.sum_insert hp, hqr, hrr,
        div_mul_div_comm, ← pow_add, Nat.cast_mul]

private lemma product_denominator {n : ℕ} (hn : 0 < n) :
    (root n).den = 2 ^ n.factorization.sum localExponent := by
  obtain ⟨q, hq, hr⟩ := product_reduced n.factorization.support n.factorization
  have hroot : root n = (q : ℚ) / 2 ^ n.factorization.sum localExponent := by
    change (if n = 0 then 0 else n.factorization.prod localCoefficient) = _
    rw [ite_eq_right (Nat.ne_of_gt hn)]
    exact hr
  rw [hroot]
  have hcop := Nat.prime_two.coprime_pow_of_not_dvd
    (m := n.factorization.sum localExponent) hq
  have hh := Rat.den_div_eq_of_coprime
    (a := (q : ℤ)) (b := ((2 ^ n.factorization.sum localExponent : ℕ) : ℤ))
    (by positivity) (by simpa using hcop)
  have hcast : (((q : ℚ) / 2 ^ n.factorization.sum localExponent).den : ℤ) =
      ((2 ^ n.factorization.sum localExponent : ℕ) : ℤ) := by
    simpa only [Int.cast_natCast, Int.cast_pow, Int.cast_ofNat,
      Nat.cast_pow, Nat.cast_ofNat] using hh
  exact Int.ofNat_inj.mp hcast

private lemma exponent_split (n : ℕ) :
    n.factorization.sum localExponent = n.factorization 2 +
      n.factorization.sum (fun _ e => e - binaryWeight e) := by
  have hlocal (p e : ℕ) : localExponent p e =
      (if p = 2 then e else 0) + (e - binaryWeight e) := by
    dsimp [localExponent]
    split_ifs <;> have := binaryWeight_le e <;> omega
  simp_rw [Finsupp.sum, hlocal, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · exact (Finsupp.notMem_support_iff.mp h).symm

/-- The global Euler product has no cross-cancellation of its dyadic denominators. -/
theorem root_denominator {n : ℕ} (hn : 0 < n) :
    (root n).den = twoPart n * auxiliary n := by
  rw [product_denominator hn, exponent_split, pow_add]
  congr 1
  dsimp [auxiliary]
  rw [Finsupp.prod, Finsupp.sum, Finset.prod_pow_eq_pow_sum]

private noncomputable def centralSeries : PowerSeries ℚ := PowerSeries.mk central

private noncomputable def oddSeries : PowerSeries ℚ :=
  (1 + PowerSeries.X) * (PowerSeries.expand 2 (by decide) centralSeries)

private lemma centralSeries_square : centralSeries * centralSeries =
    PowerSeries.mk (fun _ => (1 : ℚ)) := by
  ext e
  simpa [centralSeries, PowerSeries.coeff_mul] using central_convolution e

private lemma oddSeries_coeff (e : ℕ) :
    PowerSeries.coeff e oddSeries = central (e / 2) := by
  cases e with
  | zero => simp [oddSeries, centralSeries, central]
  | succ e =>
    simp only [oddSeries, add_mul, one_mul, map_add, PowerSeries.coeff_succ_X_mul,
      PowerSeries.coeff_expand, centralSeries, PowerSeries.coeff_mk]
    by_cases he : 2 ∣ e
    · have hn : ¬ 2 ∣ e + 1 := by omega
      simp only [he, hn, ite_true, ite_false, zero_add]
      exact congrArg central (by omega)
    · have hn : 2 ∣ e + 1 := by omega
      simp [he, hn]

private lemma oddSeries_square : oddSeries * oddSeries =
    1 + (2 : PowerSeries ℚ) * PowerSeries.X * PowerSeries.mk (fun _ => (1 : ℚ)) := by
  let P : PowerSeries ℚ := PowerSeries.mk (fun _ => (1 : ℚ))
  let Q := PowerSeries.expand 2 (by decide) P
  have hp : P * (1 - PowerSeries.X) = 1 :=
    PowerSeries.mk_one_mul_one_sub_eq_one ℚ
  have hq : Q * (1 - PowerSeries.X ^ 2) = 1 := by
    have hh := congrArg (PowerSeries.expand 2 (by decide)) hp
    simpa [Q, map_mul, map_sub] using hh
  have hx : (1 - PowerSeries.X : PowerSeries ℚ) ≠ 0 := by
    intro h
    have hh := congrArg PowerSeries.constantCoeff h
    simpa using hh
  have hy : (1 + PowerSeries.X : PowerSeries ℚ) ≠ 0 := by
    intro h
    have hh := congrArg PowerSeries.constantCoeff h
    simpa using hh
  have hs : oddSeries * oddSeries = (1 + PowerSeries.X) ^ 2 * Q := by
    have hh := congrArg (PowerSeries.expand 2 (by decide)) centralSeries_square
    dsimp [oddSeries]
    rw [map_mul] at hh
    change _ = Q at hh
    rw [show (1 + PowerSeries.X) * PowerSeries.expand 2 (by decide) centralSeries *
        ((1 + PowerSeries.X) * PowerSeries.expand 2 (by decide) centralSeries) =
        (1 + PowerSeries.X) ^ 2 *
        (PowerSeries.expand 2 (by decide) centralSeries *
          PowerSeries.expand 2 (by decide) centralSeries) by ring, hh]
  have hsx : (oddSeries * oddSeries) * (1 - PowerSeries.X) = 1 + PowerSeries.X := by
    apply mul_left_cancel₀ hy
    rw [hs]
    calc
      _ = (1 + PowerSeries.X) ^ 2 * (Q * (1 - PowerSeries.X ^ 2)) := by ring
      _ = _ := by rw [hq]; ring
  apply mul_right_cancel₀ hx
  rw [hsx]
  change 1 + PowerSeries.X = (1 + 2 * PowerSeries.X * P) * (1 - PowerSeries.X)
  calc
    _ = 1 - PowerSeries.X + 2 * PowerSeries.X * (P * (1 - PowerSeries.X)) := by rw [hp]; ring
    _ = _ := by ring

/-- The coefficients for odd primes square to one at zero and two thereafter. -/
theorem odd_local_square (e : ℕ) :
    (∑ ij ∈ Finset.antidiagonal e,
      central (ij.1 / 2) * central (ij.2 / 2)) = if e = 0 then 1 else 2 := by
  have h := congrArg (PowerSeries.coeff e) oddSeries_square
  rw [PowerSeries.coeff_mul] at h
  simp_rw [oddSeries_coeff] at h
  rw [h]
  cases e with
  | zero => simp
  | succ e => simp [PowerSeries.coeff_succ_X_mul, mul_assoc, mul_comm, mul_left_comm]

private lemma interior_erase {n : ℕ} (hn : 1 < n) :
    interior n = (n.divisors.erase 1).erase n := by
  ext d
  simp only [interior, Finset.mem_filter, Finset.mem_erase]
  constructor
  · rintro ⟨hd, hd1, hdn⟩
    exact ⟨by omega, by omega, hd⟩
  · rintro ⟨hdn, hd1, hd⟩
    have hdiv := (Nat.mem_divisors.mp hd).1
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdiv (by omega)
    have hdle : d ≤ n := Nat.le_of_dvd (by omega) hdiv
    exact ⟨hd, by omega, by omega⟩

/-- The published proper-divisor recurrence is the full divisor-square equation. -/
theorem source_convolution (n : ℕ) (hn : 0 < n) :
    (∑ d ∈ n.divisors, f d * f (n / d)) = (oddUnitaryCount n : ℚ) := by
  by_cases h1 : n = 1
  · subst n
    norm_num [oddUnitaryCount, Nat.odd_iff, source_solution_unique.1.1] <;> decide
  have hn1 : 1 < n := by omega
  have htail := f_spec.2 n hn1
  have hone : 1 ∈ n.divisors := Nat.one_mem_divisors.mpr (Nat.ne_of_gt hn)
  have hself : n ∈ n.divisors.erase 1 :=
    Finset.mem_erase.mpr ⟨h1, Nat.mem_divisors_self n (Nat.ne_of_gt hn)⟩
  have hs1 := Finset.sum_erase_add (n.divisors)
    (fun d => f d * f (n / d)) hone
  have hs2 := Finset.sum_erase_add (n.divisors.erase 1)
    (fun d => f d * f (n / d)) hself
  rw [← interior_erase hn1] at hs2
  simp only [Nat.div_one, Nat.div_self hn, f_spec.1, one_mul, mul_one] at hs1 hs2
  linarith

/-- A317934 has the independently prescribed multiplicative values. -/
theorem auxiliary_structure : auxiliary 1 = 1 ∧
    (∀ m n, Nat.Coprime m n → auxiliary (m * n) = auxiliary m * auxiliary n) ∧
    (∀ p e, Nat.Prime p → auxiliary (p ^ e) = 2 ^ (e - binaryWeight e)) := by
  refine ⟨by simp [auxiliary], ?_, ?_⟩
  · intro m n hmn
    unfold auxiliary
    rw [Nat.factorization_mul_of_coprime hmn,
      Finsupp.prod_add_index_of_disjoint hmn.disjoint_primeFactors]
  · intro p e hp
    simp [auxiliary, hp.factorization_pow, Finsupp.prod_single_index, binaryWeight]

private lemma unitary_prime_power {p e d : ℕ} (hp : Nat.Prime p)
    (hd : d ∈ (p ^ e).divisors) :
    Nat.Coprime d (p ^ e / d) ↔ d = 1 ∨ d = p ^ e := by
  constructor
  · intro hc
    obtain ⟨i, hi, rfl⟩ := (Nat.mem_divisors_prime_pow hp e).mp hd
    rw [Nat.pow_div hi hp.pos] at hc
    by_cases hi0 : i = 0
    · simp [hi0]
    · have hrest : e - i = 0 := by
        by_contra hn
        have hpi : p ∣ p ^ i := dvd_pow_self p hi0
        have hpr : p ∣ p ^ (e - i) := dvd_pow_self p hn
        have hpp : Nat.Coprime p p := hc.of_dvd hpi hpr
        exact hp.ne_one (by simpa [Nat.Coprime] using hpp)
      right
      have : i = e := by omega
      rw [this]
  · rintro (rfl | rfl)
    · simp
    · simp [Nat.div_self (pow_pos hp.pos e)]

private lemma oddUnitaryCount_prime_power {p e : ℕ} (hp : Nat.Prime p) :
    oddUnitaryCount (p ^ e) = if e = 0 ∨ p = 2 then 1 else 2 := by
  by_cases he : e = 0
  · subst e
    norm_num [oddUnitaryCount, Nat.odd_iff] <;> decide
  have hpowe : p ^ e ≠ 1 := by
    have : 1 < p ^ e := one_lt_pow₀ hp.one_lt he
    omega
  have hset : (p ^ e).divisors.filter (fun d => Odd d ∧ Nat.Coprime d (p ^ e / d)) =
      if p = 2 then {1} else {1, p ^ e} := by
    ext d
    by_cases hp2 : p = 2
    · simp only [hp2, ite_true, Finset.mem_singleton, Finset.mem_filter]
      constructor
      · rintro ⟨hd, ho, hc⟩
        rcases (unitary_prime_power (hp2 ▸ hp) hd).mp hc with h | h
        · exact h
        · subst d
          have hnot : ¬ Odd ((2 : ℕ) ^ e) := by
            rw [Nat.odd_pow_iff he]
            norm_num [Nat.odd_iff]
          exact False.elim (hnot ho)
      · intro hd
        subst d
        simp [Nat.one_mem_divisors, pow_ne_zero, hp.ne_zero]
    · have ho := (hp.odd_of_ne_two hp2).pow (n := e)
      simp only [hp2, ite_false, Finset.mem_insert, Finset.mem_singleton, Finset.mem_filter]
      constructor
      · rintro ⟨hd, _, hc⟩
        exact (unitary_prime_power hp hd).mp hc
      · rintro (rfl | rfl)
        · simp [Nat.one_mem_divisors, pow_ne_zero, hp.ne_zero]
        · exact ⟨Nat.mem_divisors_self _ (pow_ne_zero _ hp.ne_zero), ho,
            by simp [Nat.div_self (pow_pos hp.pos e)]⟩
  unfold oddUnitaryCount
  rw [hset]
  by_cases hp2 : p = 2 <;> simp [hp2, he, hpowe, Ne.symm hpowe]

/-- The constructed rational square matches the actual source at every prime power. -/
theorem root_square_prime_power {p e : ℕ} (hp : Nat.Prime p) :
    (root * root) (p ^ e) = (oddUnitaryCount (p ^ e) : ℚ) := by
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal (fun x y => root x * root y),
    Nat.sum_divisors_prime_pow hp]
  have hs : (∑ i ∈ Finset.range (e + 1), root (p ^ i) * root (p ^ e / p ^ i)) =
      ∑ ij ∈ Finset.antidiagonal e, localCoefficient p ij.1 * localCoefficient p ij.2 := by
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    apply Finset.sum_congr rfl
    intro i hi
    have hie : i ≤ e := by simpa using hi
    rw [Nat.pow_div hie hp.pos, root_prime_power hp, root_prime_power hp]
  rw [hs, oddUnitaryCount_prime_power hp]
  by_cases hp2 : p = 2
  · simp [localCoefficient, hp2, central_convolution]
  · simp only [localCoefficient, hp2, ite_false]
    rw [odd_local_square]
    split_ifs <;> simp_all

end D5.S3.Arith.DirichletRoots.OeisA318314
