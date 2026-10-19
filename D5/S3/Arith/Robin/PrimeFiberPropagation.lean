/- GID: D5/S3/Arith/Robin/PrimeFiberPropagation
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/PrimeFiberPropagation
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: Edge tests, first prime layers and prime replacement carry Robin's inequality. -/

import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Factorization.Basic
import D5.S3.Arith.ExponentExchange.IntegerSwap

/-! The edge test compares the relative divisor-sum increase of `n → n * m` with the
increase of `log log`. It uses no global estimate on `σ`; the fibre statement is a
purely local comparison along one prime direction. The prime-replacement statement
reuses the normalized divisor-sum factorization of `ExponentExchange.IntegerSwap`. -/

namespace D5.S3.Arith.Robin.PrimeFiberPropagation

noncomputable section

/-- The normalized divisor sum `σ(n)/n`. -/
def divisorRatio (n : ℕ) : ℝ := (ArithmeticFunction.sigma 1 n : ℝ) / n

/-- Robin's strict inequality at `n`. -/
def RobinAt (n : ℕ) : Prop :=
  divisorRatio n < Real.exp Real.eulerMascheroniConstant * Real.log (Real.log n)

/-- The edge test for the step `n → n * m`: the relative increase of `σ(n)/n`, weighted by
`log log n`, is at most the increase of `log log`. -/
def EdgeTest (n m : ℕ) : Prop :=
  (divisorRatio (n * m) / divisorRatio n - 1) * Real.log (Real.log n) ≤
    Real.log (1 + Real.log m / Real.log n)

theorem divisorRatio_pos {n : ℕ} (hn : n ≠ 0) : 0 < divisorRatio n := by
  unfold divisorRatio
  have h1 : (0 : ℝ) < ArithmeticFunction.sigma 1 n := by
    exact_mod_cast ArithmeticFunction.sigma_pos_iff.mpr (Nat.pos_of_ne_zero hn)
  have h2 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  exact div_pos h1 h2

private theorem loglog_mul {n m : ℕ} (hn : 1 < n) (hm : 0 < m) :
    Real.log (Real.log ((n * m : ℕ) : ℝ)) =
      Real.log (Real.log n) + Real.log (1 + Real.log m / Real.log n) := by
  have hnR : (1 : ℝ) < n := by exact_mod_cast hn
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hL : 0 < Real.log n := Real.log_pos hnR
  have hlm : 0 ≤ Real.log m := Real.log_nonneg (by exact_mod_cast hm)
  have hsplit : Real.log ((n * m : ℕ) : ℝ) = Real.log n * (1 + Real.log m / Real.log n) := by
    push_cast
    rw [Real.log_mul (by linarith) hmR.ne']
    field_simp
  rw [hsplit, Real.log_mul hL.ne' (by positivity)]

/-- An edge passing the test carries Robin's inequality from `n` to `n * m`. -/
theorem robinAt_mul_of_edgeTest {n m : ℕ} (hn : 1 < n) (hm : 0 < m)
    (hR : RobinAt n) (hE : EdgeTest n m) :
    divisorRatio (n * m) <
      Real.exp Real.eulerMascheroniConstant * Real.log (Real.log ((n * m : ℕ) : ℝ)) := by
  unfold RobinAt at hR
  unfold EdgeTest at hE
  have hZ := divisorRatio_pos (n := n) (by omega)
  have hZm := divisorRatio_pos (n := n * m) (by positivity)
  have hg := Real.exp_pos Real.eulerMascheroniConstant
  set Z := divisorRatio n
  set ρ := divisorRatio (n * m) / Z with hρ
  have hZm' : divisorRatio (n * m) = ρ * Z := by rw [hρ]; field_simp
  have hρpos : 0 < ρ := div_pos hZm hZ
  set ℓℓ := Real.log (Real.log n)
  have hℓℓ : 0 < ℓℓ := by
    by_contra h
    have h' : ℓℓ ≤ 0 := not_lt.mp h
    nlinarith
  rw [loglog_mul hn hm, hZm']
  have hstep : ρ * ℓℓ ≤ ℓℓ + Real.log (1 + Real.log m / Real.log n) := by linarith
  calc ρ * Z < ρ * (Real.exp Real.eulerMascheroniConstant * ℓℓ) :=
        mul_lt_mul_of_pos_left hR hρpos
    _ = Real.exp Real.eulerMascheroniConstant * (ρ * ℓℓ) := by ring
    _ ≤ Real.exp Real.eulerMascheroniConstant *
          (ℓℓ + Real.log (1 + Real.log m / Real.log n)) :=
        mul_le_mul_of_nonneg_left hstep hg.le

private theorem sigma_prime_pow_succ {q : ℕ} (hq : q.Prime) (a : ℕ) :
    ArithmeticFunction.sigma 1 (q ^ (a + 1)) = q * ArithmeticFunction.sigma 1 (q ^ a) + 1 := by
  rw [ArithmeticFunction.sigma_one_apply_prime_pow hq,
    ArithmeticFunction.sigma_one_apply_prime_pow hq, Finset.sum_range_succ', Finset.mul_sum]
  simp [pow_succ, mul_comm]

private theorem sigma_mul_prime {q n : ℕ} (hq : q.Prime) (hn : n ≠ 0) :
    ArithmeticFunction.sigma 1 (n * q) * ArithmeticFunction.sigma 1 (q ^ n.factorization q) =
      ArithmeticFunction.sigma 1 n *
        (q * ArithmeticFunction.sigma 1 (q ^ n.factorization q) + 1) := by
  have hcop : ∀ k, Nat.Coprime (q ^ k) (n / q ^ n.factorization q) := fun k =>
    (Nat.coprime_ordCompl hq hn).pow_left k
  have hdecomp : n = q ^ n.factorization q * (n / q ^ n.factorization q) :=
    (Nat.ordProj_mul_ordCompl_eq_self n q).symm
  generalize n.factorization q = a at hcop hdecomp ⊢
  generalize n / q ^ a = m at hcop hdecomp ⊢
  subst hdecomp
  have hmul : q ^ a * m * q = q ^ (a + 1) * m := by ring
  rw [hmul, (ArithmeticFunction.isMultiplicative_sigma (k := 1)).map_mul_of_coprime (hcop (a + 1)),
    (ArithmeticFunction.isMultiplicative_sigma (k := 1)).map_mul_of_coprime (hcop a),
    sigma_prime_pow_succ hq a]
  ring

/-- The excess of one more factor `q` is `1 / (q σ(q^a))`, where `a` is the current exponent. -/
private theorem edge_excess {q n : ℕ} (hq : q.Prime) (hn : n ≠ 0) :
    divisorRatio (n * q) / divisorRatio n - 1 =
      1 / ((q : ℝ) * ArithmeticFunction.sigma 1 (q ^ n.factorization q)) := by
  have key := sigma_mul_prime hq hn
  set s := ArithmeticFunction.sigma 1 (q ^ n.factorization q)
  have keyR : (ArithmeticFunction.sigma 1 (n * q) : ℝ) * s =
      (ArithmeticFunction.sigma 1 n : ℝ) * ((q : ℝ) * s + 1) := by exact_mod_cast key
  have hs : (0 : ℝ) < s := by
    exact_mod_cast ArithmeticFunction.sigma_pos_iff.mpr (pow_pos hq.pos _)
  have hσ : (0 : ℝ) < ArithmeticFunction.sigma 1 n := by
    exact_mod_cast ArithmeticFunction.sigma_pos_iff.mpr (Nat.pos_of_ne_zero hn)
  have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq.pos
  unfold divisorRatio
  push_cast
  rw [div_sub_one (by positivity), div_eq_div_iff (by positivity) (by positivity)]
  field_simp
  nlinarith [keyR]

/-- The real comparison behind one fibre step: with `L = log n ≥ 3`, `ℓ = log q > 0` and a next
excess `c'` at most `c / q`, the first-layer test at scale `L` implies the test at `L + ℓ`. -/
private theorem fiber_analytic {L ℓ c c' : ℝ} (hL : 3 ≤ L) (hℓ : 0 < ℓ) (hc' : 0 ≤ c')
    (hcc : Real.exp ℓ * c' ≤ c) (h : c * Real.log L ≤ Real.log (1 + ℓ / L)) :
    c' * Real.log (L + ℓ) ≤ Real.log (1 + ℓ / (L + ℓ)) := by
  have hL0 : 0 < L := by linarith
  have hlogL : 1 ≤ Real.log L := by
    rw [Real.le_log_iff_exp_le hL0]
    have := Real.exp_one_lt_d9
    norm_num at this
    linarith
  have hE := Real.quadratic_le_exp_of_nonneg hℓ.le
  have hEpos := Real.exp_pos ℓ
  have h1 : Real.log (1 + ℓ / L) ≤ ℓ / L := by
    have := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + ℓ / L)
    linarith
  have h2 : Real.log (L + ℓ) ≤ Real.log L + ℓ / L := by
    have e : L + ℓ = L * (1 + ℓ / L) := by field_simp
    rw [e, Real.log_mul hL0.ne' (by positivity)]
    linarith
  have h3 : ℓ / (L + 2 * ℓ) ≤ Real.log (1 + ℓ / (L + ℓ)) := by
    have := Real.one_sub_inv_le_log_of_pos (by positivity : 0 < 1 + ℓ / (L + ℓ))
    have e : 1 - (1 + ℓ / (L + ℓ))⁻¹ = ℓ / (L + 2 * ℓ) := by
      field_simp
      ring
    linarith
  set A := c' * Real.log L with hA
  have hA0 : 0 ≤ A := mul_nonneg hc' (by linarith)
  -- `exp ℓ * A ≤ c * log L ≤ ℓ / L`
  have hEA : Real.exp ℓ * A * L ≤ ℓ := by
    have h4 : Real.exp ℓ * A ≤ ℓ / L := by
      calc Real.exp ℓ * A = (Real.exp ℓ * c') * Real.log L := by rw [hA]; ring
        _ ≤ c * Real.log L := mul_le_mul_of_nonneg_right hcc (by linarith)
        _ ≤ ℓ / L := h.trans h1
    have := mul_le_mul_of_nonneg_right h4 hL0.le
    rwa [div_mul_cancel₀ _ hL0.ne'] at this
  -- `(L + ℓ)(L + 2ℓ) ≤ L² exp ℓ`, using `L ≥ 3`
  have hpoly : (L + ℓ) * (L + 2 * ℓ) ≤ L ^ 2 * Real.exp ℓ := by
    have hq1 : (L + ℓ) * (L + 2 * ℓ) ≤ L ^ 2 * (1 + ℓ + ℓ ^ 2 / 2) := by
      nlinarith [mul_pos hℓ hL0, sq_nonneg ℓ, mul_le_mul_of_nonneg_left hL hℓ.le]
    calc (L + ℓ) * (L + 2 * ℓ) ≤ L ^ 2 * (1 + ℓ + ℓ ^ 2 / 2) := hq1
      _ ≤ L ^ 2 * Real.exp ℓ := mul_le_mul_of_nonneg_left hE (sq_nonneg L)
  have hfin : A * (L + ℓ) * (L + 2 * ℓ) ≤ ℓ * L := by
    calc A * (L + ℓ) * (L + 2 * ℓ) = A * ((L + ℓ) * (L + 2 * ℓ)) := by ring
      _ ≤ A * (L ^ 2 * Real.exp ℓ) := mul_le_mul_of_nonneg_left hpoly hA0
      _ = L * (Real.exp ℓ * A * L) := by ring
      _ ≤ L * ℓ := mul_le_mul_of_nonneg_left hEA hL0.le
      _ = ℓ * L := by ring
  have hmid : c' * Real.log (L + ℓ) ≤ A * (L + ℓ) / L := by
    have hc1 : c' * Real.log (L + ℓ) ≤ c' * (Real.log L + ℓ / L) :=
      mul_le_mul_of_nonneg_left h2 hc'
    have hc2 : c' * (ℓ / L) ≤ c' * Real.log L * (ℓ / L) := by
      have : 0 ≤ c' * (ℓ / L) := mul_nonneg hc' (by positivity)
      nlinarith
    have e : A * (L + ℓ) / L = c' * Real.log L * (1 + ℓ / L) := by
      rw [hA]
      field_simp
    rw [e]
    nlinarith
  have hlast : A * (L + ℓ) / L ≤ ℓ / (L + 2 * ℓ) := by
    rw [div_le_div_iff₀ hL0 (by positivity)]
    nlinarith
  linarith

private theorem log_le_log_mul_pow {n q : ℕ} (hq : q.Prime) (hn : n ≠ 0) (k : ℕ) :
    Real.log n ≤ Real.log ((n * q ^ k : ℕ) : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  apply Real.log_le_log hnR
  exact_mod_cast Nat.le_mul_of_pos_right n (pow_pos hq.pos k)

private theorem ne_zero_of_log {n : ℕ} (hL : 3 ≤ Real.log n) : n ≠ 0 := by
  intro h
  subst h
  simp at hL
  linarith

private theorem edgeTest_mul_prime {n q : ℕ} (hq : q.Prime) (hL : 3 ≤ Real.log n)
    (hE : EdgeTest n q) : EdgeTest (n * q) q := by
  have hn := ne_zero_of_log hL
  have hnq : n * q ≠ 0 := mul_ne_zero hn hq.ne_zero
  have ha : (n * q).factorization q = n.factorization q + 1 := by
    rw [Nat.factorization_mul hn hq.ne_zero, Finsupp.add_apply, hq.factorization_self]
  unfold EdgeTest at hE ⊢
  rw [edge_excess hq hn] at hE
  rw [edge_excess hq hnq, ha]
  have hqR : (1 : ℝ) < q := by exact_mod_cast hq.one_lt
  have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hlog : Real.log ((n * q : ℕ) : ℝ) = Real.log n + Real.log q := by
    push_cast
    exact Real.log_mul hnR.ne' (by linarith)
  rw [hlog]
  set s := ArithmeticFunction.sigma 1 (q ^ n.factorization q)
  have hs : (0 : ℝ) < s := by
    exact_mod_cast ArithmeticFunction.sigma_pos_iff.mpr (pow_pos hq.pos _)
  have hsucc : (ArithmeticFunction.sigma 1 (q ^ (n.factorization q + 1)) : ℝ) = q * s + 1 := by
    exact_mod_cast sigma_prime_pow_succ hq (n.factorization q)
  rw [hsucc]
  apply fiber_analytic hL (Real.log_pos hqR) (by positivity) _ hE
  rw [Real.exp_log (by linarith)]
  have hqpos : (0 : ℝ) < q := by linarith
  rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- Along one prime fibre `n, nq, nq², …`, the edge test at the first layer implies the test at
every later layer, once `log n ≥ 3`. -/
theorem edgeTest_mul_prime_pow {n q : ℕ} (hq : q.Prime) (hL : 3 ≤ Real.log n)
    (hE : EdgeTest n q) : ∀ k : ℕ,
      (divisorRatio (n * q ^ k * q) / divisorRatio (n * q ^ k) - 1) *
          Real.log (Real.log ((n * q ^ k : ℕ) : ℝ)) ≤
        Real.log (1 + Real.log (q : ℝ) / Real.log ((n * q ^ k : ℕ) : ℝ)) := by
  have hn := ne_zero_of_log hL
  intro k
  change EdgeTest (n * q ^ k) q
  induction k with
  | zero => simpa using hE
  | succ k ih =>
    rw [pow_succ, ← mul_assoc]
    exact edgeTest_mul_prime hq (hL.trans (log_le_log_mul_pow hq hn k)) ih

/-- Robin's inequality at `n`, with `log n ≥ 3` and a passing first-layer test in the prime
direction `q`, holds at every `n q^k`. -/
theorem robinAt_mul_prime_pow {n q : ℕ} (hq : q.Prime) (hL : 3 ≤ Real.log n)
    (hR : RobinAt n) (hE : EdgeTest n q) : ∀ k : ℕ,
      divisorRatio (n * q ^ k) <
        Real.exp Real.eulerMascheroniConstant * Real.log (Real.log ((n * q ^ k : ℕ) : ℝ)) := by
  have hn := ne_zero_of_log hL
  intro k
  change RobinAt (n * q ^ k)
  induction k with
  | zero => simpa using hR
  | succ k ih =>
    have hgt : 1 < n * q ^ k := by
      by_contra h
      have h : n * q ^ k ≤ 1 := not_lt.mp h
      have hle : ((n * q ^ k : ℕ) : ℝ) ≤ 1 := by exact_mod_cast h
      have := (hL.trans (log_le_log_mul_pow hq hn k)).trans (Real.log_le_sub_one_of_pos
        (by exact_mod_cast Nat.pos_of_ne_zero (mul_ne_zero hn (pow_ne_zero k hq.ne_zero))))
      linarith
    rw [pow_succ, ← mul_assoc]
    exact robinAt_mul_of_edgeTest hgt hq.pos ih (edgeTest_mul_prime_pow hq hL hE k)

private theorem reciprocalGeomSum_anti {p q : ℕ} (hp : p.Prime) (hpq : p ≤ q) (a : ℕ) :
    D5.S3.Arith.RobinExponentSwap.reciprocalGeomSum q a ≤
      D5.S3.Arith.RobinExponentSwap.reciprocalGeomSum p a := by
  unfold D5.S3.Arith.RobinExponentSwap.reciprocalGeomSum
  apply Finset.sum_le_sum
  intro i _
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpqR : (p : ℝ) ≤ q := by exact_mod_cast hpq
  exact pow_le_pow_left₀ (inv_nonneg.mpr (Nat.cast_nonneg q)) (inv_anti₀ hpR hpqR) i

/-- Replacing the prime `p` of a full prime-power factor `p^a` by a prime `q ≥ p` keeps
Robin's inequality: the divisor ratio does not increase and the integer does not decrease. -/
theorem robinAt_prime_replace {p q a m : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≤ q)
    (hpm : ¬ p ∣ m) (hqm : ¬ q ∣ m) (hR : RobinAt (p ^ a * m)) :
    divisorRatio (q ^ a * m) <
      Real.exp Real.eulerMascheroniConstant * Real.log (Real.log ((q ^ a * m : ℕ) : ℝ)) := by
  open D5.S3.Arith.ExponentExchange.IntegerSwap in
  by_cases hm : m = 0
  · subst hm
    simp [RobinAt, divisorRatio] at hR
  have hcop : ∀ {r : ℕ}, r.Prime → ¬ r ∣ m → Nat.Coprime (r ^ a) m := fun hr hrm =>
    Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd hr).mpr hrm)
  have hsplit : ∀ {r : ℕ}, r.Prime → ¬ r ∣ m →
      divisorRatio (r ^ a * m) =
        D5.S3.Arith.RobinExponentSwap.reciprocalGeomSum r a * divisorRatio m := by
    intro r hr hrm
    unfold divisorRatio
    rw [normalized_sigma_mul (hcop hr hrm), normalized_sigma_prime_pow hr]
  have hm0 : 0 ≤ divisorRatio m := by
    unfold divisorRatio
    positivity
  have hle : divisorRatio (q ^ a * m) ≤ divisorRatio (p ^ a * m) := by
    rw [hsplit hq hqm, hsplit hp hpm]
    exact mul_le_mul_of_nonneg_right (reciprocalGeomSum_anti hp hpq a) hm0
  unfold RobinAt at hR
  have hpos : 0 < divisorRatio (p ^ a * m) := divisorRatio_pos
    (mul_ne_zero (pow_ne_zero a hp.ne_zero) hm)
  have hg := Real.exp_pos Real.eulerMascheroniConstant
  have hll : 0 < Real.log (Real.log ((p ^ a * m : ℕ) : ℝ)) := by
    by_contra h
    have h' : Real.log (Real.log ((p ^ a * m : ℕ) : ℝ)) ≤ 0 := not_lt.mp h
    nlinarith
  have hnat : p ^ a * m ≤ q ^ a * m := Nat.mul_le_mul_right m (Nat.pow_le_pow_left hpq a)
  have hlog0 : 0 ≤ Real.log ((p ^ a * m : ℕ) : ℝ) := Real.log_natCast_nonneg _
  have hlog1 : 0 < Real.log ((p ^ a * m : ℕ) : ℝ) := by
    rcases hlog0.lt_or_eq with h | h
    · exact h
    · rw [← h, Real.log_zero] at hll
      exact absurd hll (lt_irrefl 0)
  have hpm0 : (0 : ℝ) < ((p ^ a * m : ℕ) : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (mul_ne_zero (pow_ne_zero a hp.ne_zero) hm)
  have hmono : Real.log (Real.log ((p ^ a * m : ℕ) : ℝ)) ≤
      Real.log (Real.log ((q ^ a * m : ℕ) : ℝ)) :=
    Real.log_le_log hlog1 (Real.log_le_log hpm0 (by exact_mod_cast hnat))
  calc divisorRatio (q ^ a * m) ≤ divisorRatio (p ^ a * m) := hle
    _ < Real.exp Real.eulerMascheroniConstant * Real.log (Real.log ((p ^ a * m : ℕ) : ℝ)) := hR
    _ ≤ Real.exp Real.eulerMascheroniConstant * Real.log (Real.log ((q ^ a * m : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left hmono hg.le

end

end D5.S3.Arith.Robin.PrimeFiberPropagation
