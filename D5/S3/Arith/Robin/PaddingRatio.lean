/- GID: D5/S3/Arith/Robin/PaddingRatio
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/PaddingRatio
   mirror-E: none(waiver:qualitative-asymptotic-estimate)
   anchors: []
   utility: none
   digest: Raising a bounded prime exponent gives an eventual strict relative sigma gain. -/

import D5.S3.Arith.RobinExponentSwap
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.FieldSimp

/- Search and restricted-reproof receipts are attached to the implementation PR.
The geometric sum definition, sigma factorization, and logarithmic limit are
reused from their existing owners. No absolute Robin or Gronwall bound is used. -/

open Filter
open scoped Topology
open D5.S3.Arith.RobinExponentSwap

namespace D5.S3.Arith.Robin.PaddingRatio

noncomputable section

/-- The normalized divisor sum occurring in the full-wave weights. -/
def robinRatio (n : ℕ) : ℝ :=
  (ArithmeticFunction.sigma 1 n : ℝ) /
    (Real.exp Real.eulerMascheroniConstant * n * Real.log (Real.log n))

/-- Increase the exponent of `p` to `A + 1` when its current exponent is at most `A`. -/
def padding (p A n : ℕ) : ℕ := p ^ (A + 1 - n.factorization p) * n

/-- The exact local ratio before logarithmic distortion. -/
def paddingRho (p A : ℕ) : ℝ :=
  reciprocalGeomSum p A / reciprocalGeomSum p (A + 1)

/-- A strict contraction with room for the eventual logarithmic distortion. -/
def paddingQ (p A : ℕ) : ℝ := (1 + paddingRho p A) / 2

private theorem geom_pos {p : ℕ} (hp : p.Prime) (a : ℕ) :
    0 < reciprocalGeomSum p a := by
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  apply Finset.sum_pos'
  · intro i _
    exact (pow_pos (inv_pos.mpr hpR) i).le
  · exact ⟨0, by simp, by simp⟩

theorem geom_mono {p a b : ℕ} (hab : a ≤ b) :
    reciprocalGeomSum p a ≤ reciprocalGeomSum p b := by
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
  intro i _ _
  exact pow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg p)) i

/-- Both local ratios are strictly between zero and one. -/
theorem padding_constants {p : ℕ} (hp : p.Prime) (A : ℕ) :
    0 < paddingRho p A ∧ paddingRho p A < paddingQ p A ∧
      0 < paddingQ p A ∧ paddingQ p A < 1 := by
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hstrict : reciprocalGeomSum p A < reciprocalGeomSum p (A + 1) := by
    unfold reciprocalGeomSum
    rw [Finset.sum_range_succ _ (A + 1)]
    exact lt_add_of_pos_right _ (pow_pos (inv_pos.mpr hpR) _)
  have hr0 : 0 < paddingRho p A := div_pos (geom_pos hp A) (geom_pos hp (A + 1))
  have hr1 : paddingRho p A < 1 := (div_lt_one (geom_pos hp (A + 1))).mpr hstrict
  dsimp [paddingQ]
  exact ⟨hr0, by linarith, by linarith, by linarith⟩

private theorem sigma_prime_power_normalized {p : ℕ} (hp : p.Prime) (a : ℕ) :
    (ArithmeticFunction.sigma 1 (p ^ a) : ℝ) / (p : ℝ) ^ a =
      reciprocalGeomSum p a := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp1 : (p : ℝ) ≠ 1 := by exact_mod_cast hp.ne_one
  rw [ArithmeticFunction.sigma_one_apply_prime_pow hp]
  push_cast
  unfold reciprocalGeomSum
  rw [geom_sum_eq hp1, geom_sum_inv hp1 hp0]
  simp only [inv_pow, pow_succ]
  field_simp

private theorem sigma_pow_mul_normalized {p m : ℕ} (hp : p.Prime)
    (hm : p.Coprime m) (a : ℕ) :
    (ArithmeticFunction.sigma 1 (p ^ a * m) : ℝ) / (p ^ a * m : ℕ) =
      reciprocalGeomSum p a * ((ArithmeticFunction.sigma 1 m : ℝ) / m) := by
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (hm.pow_left a)]
  simp only [Nat.cast_mul, Nat.cast_pow]
  rw [mul_div_mul_comm, sigma_prime_power_normalized hp a]

/-- Padding changes only the prime-power part of the factorization. -/
theorem padding_eq_prime_power_mul {p A n : ℕ} (ha : n.factorization p ≤ A) :
    padding p A n = p ^ (A + 1) * (ordCompl[p] n) := by
  unfold padding
  conv_lhs =>
    arg 2
    rw [← Nat.ordProj_mul_ordCompl_eq_self n p]
  rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel (by omega)]

/-- The padding multiplier lies between one and `p ^ (A + 1)`. -/
theorem padding_bounds {p : ℕ} (hp : p.Prime) (A n : ℕ) :
    n ≤ padding p A n ∧ padding p A n ≤ p ^ (A + 1) * n := by
  constructor
  · exact Nat.le_mul_of_pos_left n (pow_pos hp.pos _)
  · exact Nat.mul_le_mul_right n (Nat.pow_le_pow_right hp.pos (Nat.sub_le _ _))

/-- Local sigma factorization gives a uniform relative abundancy gain. -/
theorem padding_abundancy {p A n : ℕ} (hp : p.Prime) (hn : n ≠ 0)
    (ha : n.factorization p ≤ A) :
    (ArithmeticFunction.sigma 1 n : ℝ) / n ≤
      paddingRho p A * ((ArithmeticFunction.sigma 1 (padding p A n) : ℝ) /
        padding p A n) := by
  have hcop := Nat.coprime_ordCompl hp hn
  have hn' : n = p ^ n.factorization p * (ordCompl[p] n) :=
    (Nat.ordProj_mul_ordCompl_eq_self n p).symm
  have hleft : (ArithmeticFunction.sigma 1 n : ℝ) / n =
      reciprocalGeomSum p (n.factorization p) *
        ((ArithmeticFunction.sigma 1 (ordCompl[p] n) : ℝ) / (ordCompl[p] n : ℕ)) := by
    conv_lhs => rw [hn']
    exact sigma_pow_mul_normalized hp hcop _
  rw [hleft, padding_eq_prime_power_mul ha, sigma_pow_mul_normalized hp hcop]
  have hnonneg : 0 ≤ (ArithmeticFunction.sigma 1 (ordCompl[p] n) : ℝ) /
      (ordCompl[p] n : ℕ) :=
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  calc
    _ ≤ reciprocalGeomSum p A *
        ((ArithmeticFunction.sigma 1 (ordCompl[p] n) : ℝ) / (ordCompl[p] n : ℕ)) :=
      mul_le_mul_of_nonneg_right (geom_mono ha) hnonneg
    _ = _ := by
      unfold paddingRho
      field_simp [(geom_pos hp (A + 1)).ne']

/-- The logarithmic normalization is positive on the full-wave support. -/
theorem loglog_pos {n : ℕ} (hn : 5041 ≤ n) : 0 < Real.log (Real.log (n : ℝ)) := by
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast (show 3 ≤ n by omega)
  exact Real.log_pos ((Real.lt_log_iff_exp_lt (by linarith)).mpr
    (Real.exp_one_lt_three.trans_le hnR))

/-- In particular the actual Robin ratio is nonnegative on its support. -/
theorem robinRatio_nonneg {n : ℕ} (hn : 5041 ≤ n) : 0 ≤ robinRatio n := by
  exact div_nonneg (Nat.cast_nonneg _)
    (mul_nonneg (mul_nonneg (Real.exp_pos _).le (Nat.cast_nonneg _)) (loglog_pos hn).le)

private theorem tendsto_loglog_scale {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ => Real.log (Real.log (c * n)) / Real.log (Real.log n))
      atTop (𝓝 1) := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglog := Real.tendsto_log_atTop.comp hlog
  have hdiff := (Real.tendsto_log_comp_add_sub_log (Real.log c)).comp hlog
  have hlim := (hdiff.div_atTop hloglog).add_const 1
  simp only [zero_add] at hlim
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop 5041] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  dsimp only [Function.comp_def]
  rw [Real.log_mul hc.ne' hn0, add_comm (Real.log c) (Real.log (n : ℝ))]
  field_simp [(loglog_pos hn).ne']
  ring

/-- With `q = (1 + rho) / 2`, all sufficiently large bounded-exponent integers
gain a factor of at least `1 / q` under padding. The Euler constant cancels. -/
theorem padding_ratio {p : ℕ} (hp : p.Prime) (A : ℕ) :
    ∃ N ≥ 5041, ∀ n ≥ N, n.factorization p ≤ A →
      robinRatio n ≤ paddingQ p A * robinRatio (padding p A n) := by
  have hconst := padding_constants hp A
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hlim := (tendsto_loglog_scale (pow_pos hpR (A + 1))).const_mul (paddingRho p A)
  simp only [mul_one] at hlim
  have he := (tendsto_order.1 hlim).2 (paddingQ p A) hconst.2.1
  obtain ⟨N, hN⟩ := eventually_atTop.1 he
  refine ⟨max N 5041, le_max_right _ _, ?_⟩
  intro n hn ha
  have hnlarge : 5041 ≤ n := le_trans (le_max_right _ _) hn
  have hn0 : n ≠ 0 := by omega
  have hpad := padding_bounds hp A n
  have hTlarge : 5041 ≤ padding p A n := hnlarge.trans hpad.1
  have hLn := loglog_pos hnlarge
  have hLT := loglog_pos hTlarge
  have hT0 : 0 < (padding p A n : ℝ) := by exact_mod_cast (show 0 < padding p A n by omega)
  have hT1 : (1 : ℝ) < padding p A n := by exact_mod_cast (show 1 < padding p A n by omega)
  have hscale : (padding p A n : ℝ) ≤ (p : ℝ) ^ (A + 1) * n := by
    exact_mod_cast hpad.2
  have hlogs : Real.log (Real.log (padding p A n : ℝ)) ≤
      Real.log (Real.log ((p : ℝ) ^ (A + 1) * n)) :=
    Real.log_le_log (Real.log_pos hT1) (Real.log_le_log hT0 hscale)
  have hnear := hN n (le_trans (le_max_left _ _) hn)
  have hdist : paddingRho p A * Real.log (Real.log (padding p A n : ℝ)) ≤
      paddingQ p A * Real.log (Real.log (n : ℝ)) := by
    rw [← mul_div_assoc] at hnear
    have h := (div_lt_iff₀ hLn).mp hnear
    exact (mul_le_mul_of_nonneg_left hlogs hconst.1.le).trans h.le
  have hgamma := Real.exp_pos Real.eulerMascheroniConstant
  have hdiv : paddingRho p A /
        (Real.exp Real.eulerMascheroniConstant * Real.log (Real.log (n : ℝ))) ≤
      paddingQ p A /
        (Real.exp Real.eulerMascheroniConstant * Real.log (Real.log (padding p A n : ℝ))) := by
    apply (div_le_div_iff₀ (mul_pos hgamma hLn) (mul_pos hgamma hLT)).mpr
    convert mul_le_mul_of_nonneg_left hdist hgamma.le using 1 <;> ring
  have hsig : 0 ≤ (ArithmeticFunction.sigma 1 (padding p A n) : ℝ) / padding p A n :=
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  calc
    robinRatio n = ((ArithmeticFunction.sigma 1 n : ℝ) / n) /
        (Real.exp Real.eulerMascheroniConstant * Real.log (Real.log (n : ℝ))) := by
      simp only [robinRatio, div_eq_mul_inv, mul_inv_rev]
      ring
    _ ≤ (paddingRho p A *
        ((ArithmeticFunction.sigma 1 (padding p A n) : ℝ) / padding p A n)) /
        (Real.exp Real.eulerMascheroniConstant * Real.log (Real.log (n : ℝ))) :=
      div_le_div_of_nonneg_right (padding_abundancy hp hn0 ha) (mul_pos hgamma hLn).le
    _ = ((ArithmeticFunction.sigma 1 (padding p A n) : ℝ) / padding p A n) *
        (paddingRho p A /
          (Real.exp Real.eulerMascheroniConstant * Real.log (Real.log (n : ℝ)))) := by ring
    _ ≤ ((ArithmeticFunction.sigma 1 (padding p A n) : ℝ) / padding p A n) *
        (paddingQ p A /
          (Real.exp Real.eulerMascheroniConstant *
            Real.log (Real.log (padding p A n : ℝ)))) := mul_le_mul_of_nonneg_left hdiv hsig
    _ = paddingQ p A * robinRatio (padding p A n) := by
      simp only [robinRatio, div_eq_mul_inv, mul_inv_rev]
      ring

#print axioms robinRatio
#print axioms padding
#print axioms paddingRho
#print axioms paddingQ
#print axioms geom_pos
#print axioms geom_mono
#print axioms padding_constants
#print axioms sigma_prime_power_normalized
#print axioms sigma_pow_mul_normalized
#print axioms padding_eq_prime_power_mul
#print axioms padding_bounds
#print axioms padding_abundancy
#print axioms loglog_pos
#print axioms robinRatio_nonneg
#print axioms tendsto_loglog_scale
#print axioms padding_ratio

end
end D5.S3.Arith.Robin.PaddingRatio
