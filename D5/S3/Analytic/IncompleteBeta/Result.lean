/- GID: D5/S3/Analytic/IncompleteBeta/Result
   generality: G
   mirror-B: D5/B/S3/Analytic/IncompleteBeta/Result
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Algebra.BigOperators.NatAntidiagonal, mathlib/module/Mathlib.Analysis.SpecialFunctions.Pow.Deriv]
   utility: none
   digest: The incomplete beta Turanian has strictly positive coefficients. -/

import D5.S3.Analytic.IncompleteBeta.Comparison
import D5.S3.Analytic.IncompleteBeta.Moment
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! A fixed sum of beta shapes gives a common positive moment factor. -/

noncomputable section
open Set MeasureTheory
open D5.S3.Analytic.IncompleteBeta.Comparison

namespace D5.S3.Analytic.IncompleteBeta.Result

private lemma convolution_symm (a s t : ℝ) (n : ℕ) :
    convolution a s t n = convolution a t s n := by
  have H := Finset.Nat.sum_antidiagonal_swap (n := n)
    (f := fun p : ℕ × ℕ => coeff a s p.1 * coeff a t p.2)
  change (∑ p ∈ Finset.antidiagonal n, coeff a s p.2 * coeff a t p.1) =
    ∑ p ∈ Finset.antidiagonal n, coeff a s p.1 * coeff a t p.2 at H
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at H
  unfold convolution
  exact H.symm.trans (Finset.sum_congr rfl (fun k _ => mul_comm _ _))

private lemma W_continuousOn {a : ℝ} (ha : 0 < a) (n : ℕ) :
    ContinuousOn (W a n) (Icc 0 1) := by
  unfold W
  apply continuousOn_finsetSum
  intro k hk
  have hk' : (k:ℝ) ≤ n := by exact_mod_cast (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
  exact ((continuous_id.continuousOn.rpow_const (fun _ _ => Or.inr (by positivity))).mul
    ((continuous_const.sub continuous_id).continuousOn.rpow_const
      (fun _ _ => Or.inr (by linarith)))).div_const _

private lemma W_symm (n : ℕ) (u : ℝ) {a : ℝ} : W a n (1-u) = W a n u := by
  unfold W
  rw [← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hcast : ((n+1-1-k:ℕ):ℝ) = (n:ℝ)-k := by
    rw [Nat.add_sub_cancel, Nat.cast_sub hk']
  simp only [sub_sub_cancel, hcast]
  rw [show a + ((n:ℝ)-k) = a+n-k by ring,
    show a+(n:ℝ)-((n:ℝ)-k) = a+k by ring]
  ring

private lemma weighted_term_eq {a s t u : ℝ} {n k : ℕ}
    (hu : u ∈ Ioo 0 1) :
    u^(s-1)*(1-u)^(t-1) *
        (u^(a+k)*(1-u)^(a+n-k) /
          (Real.Gamma (a+k+1)*Real.Gamma (a+n-k+1))) =
      (u^(a+s+k-1)*(1-u)^(a+t+n-k-1)) /
        (Real.Gamma (a+k+1)*Real.Gamma (a+n-k+1)) := by
  have hv := sub_pos.mpr hu.2
  calc
    _ = (u^(s-1)*u^(a+k))*((1-u)^(t-1)*(1-u)^(a+n-k)) /
        (Real.Gamma (a+k+1)*Real.Gamma (a+n-k+1)) := by ring
    _ = _ := by
      rw [← Real.rpow_add hu.1, ← Real.rpow_add hv]
      rw [show s-1+(a+(k:ℝ)) = a+s+k-1 by ring,
        show t-1+(a+(n:ℝ)-k) = a+t+n-k-1 by ring]

private lemma convolution_eq_betaMean {a s t : ℝ}
    (ha : 0 < a) (hs : 0 < s) (ht : 0 < t) (n : ℕ) :
    convolution a s t n =
      Real.Gamma (2*a+s+t+n) / (Real.Gamma s * Real.Gamma t) *
        ∫ u in (0:ℝ)..1, u^(s-1)*(1-u)^(t-1)*W a n u := by
  let F := fun k : ℕ => fun u : ℝ =>
    u^(s-1)*(1-u)^(t-1) *
      (u^(a+k)*(1-u)^(a+n-k) /
        (Real.Gamma (a+k+1)*Real.Gamma (a+n-k+1)))
  have hki (k : ℕ) (hk : k ∈ Finset.range (n+1)) :
      IntervalIntegrable (F k) volume 0 1 := by
    have hk' : (k:ℝ) ≤ n := by exact_mod_cast (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
    have H := (D5.S3.Analytic.KummerRatio.BetaIntegral.intervalIntegrable_beta
      (by positivity : 0<a+s+k) (by linarith : 0<a+t+n-k)).div_const
        (Real.Gamma (a+k+1)*Real.Gamma (a+n-k+1))
    apply H.congr_uIoo
    intro u hu
    rw [Set.uIoo_of_le zero_le_one] at hu
    exact (weighted_term_eq hu).symm
  have hterm (k : ℕ) (hk : k ∈ Finset.range (n+1)) :
      Real.Gamma (2*a+s+t+n) / (Real.Gamma s * Real.Gamma t) *
        (∫ u in (0:ℝ)..1, F k u) = coeff a s k * coeff a t (n-k) := by
    have hkN := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    have hk' : (k:ℝ) ≤ n := by exact_mod_cast hkN
    have hI : (∫ u in (0:ℝ)..1, F k u) =
        (Real.Gamma (a+s+k)*Real.Gamma (a+t+n-k)/
          Real.Gamma (2*a+s+t+n)) /
          (Real.Gamma (a+k+1)*Real.Gamma (a+n-k+1)) := by
      calc
        _ = ∫ u in (0:ℝ)..1,
            (u^(a+s+k-1)*(1-u)^(a+t+n-k-1)) /
              (Real.Gamma (a+k+1)*Real.Gamma (a+n-k+1)) := by
          apply intervalIntegral.integral_congr_Ioo_of_le zero_le_one
          intro u hu
          exact weighted_term_eq hu
        _ = _ := by
          rw [intervalIntegral.integral_div,
            D5.S3.Analytic.KummerRatio.BetaIntegral.integral_beta
              (by positivity : 0<a+s+k) (by linarith : 0<a+t+n-k)]
          congr 3
          ring
    rw [hI]
    unfold coeff
    rw [Nat.cast_sub hkN]
    have hG := (Real.Gamma_pos_of_pos
      (by positivity : 0<2*a+s+t+n)).ne'
    rw [show a+t+((n:ℝ)-k)=a+t+n-k by ring,
      show a+((n:ℝ)-k)+1=a+n-k+1 by ring]
    field_simp
  unfold convolution
  rw [show (fun u => u^(s-1)*(1-u)^(t-1)*W a n u) =
    (fun u => ∑ k ∈ Finset.range (n+1), F k u) by
      funext u; simp only [W, Finset.mul_sum]; rfl,
    intervalIntegral.integral_finsetSum hki, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun k hk => (hterm k hk).symm)

private lemma term_deriv {p q u : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hu : u ∈ Ioo 0 1) :
    HasDerivAt (fun x : ℝ => x^p*(1-x)^q / (Real.Gamma (p+1)*Real.Gamma (q+1)))
      (u^(p-1)*(1-u)^q / (Real.Gamma p*Real.Gamma (q+1)) -
        u^p*(1-u)^(q-1) / (Real.Gamma (p+1)*Real.Gamma q)) u := by
  have H := (((hasDerivAt_id u).rpow_const (p := p) (Or.inl hu.1.ne')).mul
    (((hasDerivAt_const u (1:ℝ)).sub (hasDerivAt_id u)).rpow_const (p := q)
      (Or.inl (sub_pos.mpr hu.2).ne'))).div_const
        (Real.Gamma (p+1)*Real.Gamma (q+1))
  convert H using 1
  · rfl
  · simp only [id_eq, Pi.sub_apply, one_mul, zero_sub, neg_mul, mul_neg]
    rw [Real.Gamma_add_one hp.ne', Real.Gamma_add_one hq.ne']
    field_simp
    <;> ring

private lemma W_hasDerivAt {a u : ℝ} (ha : 0 < a) (n : ℕ) (hu : u ∈ Ioo 0 1) :
    HasDerivAt (W a n)
      (u^(a-1)*(1-u)^(a+n) / (Real.Gamma a*Real.Gamma (a+n+1)) -
        u^(a+n)*(1-u)^(a-1) / (Real.Gamma (a+n+1)*Real.Gamma a)) u := by
  let F := fun k : ℕ => u^(a+k-1)*(1-u)^(a+n-k) /
    (Real.Gamma (a+k)*Real.Gamma (a+n-k+1))
  have hterm (k : ℕ) (hk : k ∈ Finset.range (n+1)) :
      HasDerivAt (fun x : ℝ => x^(a+k)*(1-x)^(a+n-k) /
          (Real.Gamma (a+k+1)*Real.Gamma (a+n-k+1)))
        (F k - F (k+1)) u := by
    have hk' : (k:ℝ) ≤ n := by exact_mod_cast (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
    convert term_deriv (by positivity : 0 < a+k) (by linarith : 0 < a+n-k) hu using 1
    dsimp [F]
    push_cast
    rw [show a+((k:ℝ)+1)-1=a+k by ring,
      show a+(n:ℝ)-((k:ℝ)+1)=a+n-k-1 by ring,
      show a+((k:ℝ)+1)=a+k+1 by ring,
      show a+(n:ℝ)-k-1+1=a+n-k by ring]
  have H := HasDerivAt.fun_sum hterm
  have hsum : (∑ k ∈ Finset.range (n+1), (F k - F (k+1))) = F 0 - F (n+1) := by
    have H := Finset.sum_range_sub F (n+1)
    rw [Finset.sum_sub_distrib] at H ⊢
    linarith
  rw [hsum] at H
  change HasDerivAt (W a n) (F 0 - F (n+1)) u at H
  convert H using 1
  dsimp [F]
  push_cast
  simp only [add_zero, sub_zero]
  rw [show a+((n:ℝ)+1)-1 = a+n by ring,
    show a+(n:ℝ)-(n+1)=a-1 by ring,
    show a+((n:ℝ)+1)=a+n+1 by ring, sub_add_cancel]

private lemma W_strictMonoOn {a : ℝ} (ha : 0 < a) (n : ℕ) :
    StrictMonoOn (W a n) (Icc 0 (1/2)) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    ((W_continuousOn ha n).mono (by intro x hx; constructor <;> linarith [hx.1, hx.2]))
  intro u hu
  rw [interior_Icc] at hu
  have hu1 : u ∈ Ioo 0 1 := ⟨hu.1, by linarith [hu.2]⟩
  rw [(W_hasDerivAt ha n hu1).deriv]
  have hv := sub_pos.mpr hu1.2
  have hG : 0 < Real.Gamma a*Real.Gamma (a+n+1) :=
    mul_pos (Real.Gamma_pos_of_pos ha) (Real.Gamma_pos_of_pos (by positivity))
  rw [mul_comm (Real.Gamma (a+n+1)) (Real.Gamma a)]
  apply sub_pos.mpr
  apply (div_lt_div_iff_of_pos_right hG).mpr
  rw [show a+(n:ℝ) = (a-1)+((n:ℝ)+1) by ring,
    Real.rpow_add hu.1, Real.rpow_add hv]
  have H := Real.rpow_lt_rpow hu.1.le (by linarith [hu.2] : u < 1-u)
    (by positivity : (0:ℝ)<(n:ℝ)+1)
  nlinarith [mul_pos (Real.rpow_pos_of_pos hu.1 (a-1)) (Real.rpow_pos_of_pos hv (a-1))]

/-- At fixed positive mean shape, the coefficient convolution strictly decreases
with the nonnegative half-difference of its two shape parameters. -/
theorem convolution_strictAnti_imbalance {a m : ℝ} (ha : 0 < a) (hm : 0 < m)
    (n : ℕ) :
    StrictAntiOn (fun d => convolution a (m + d) (m - d) n) (Ico 0 m) := by
  have hW : ContinuousOn (W a n) (Icc 0 1) := W_continuousOn ha n
  have hsymm : ∀ u ∈ Icc 0 1, W a n (1 - u) = W a n u :=
    fun u _ => W_symm n u
  have hmono : StrictMonoOn (W a n) (Ioc 0 (1 / 2)) :=
    (W_strictMonoOn ha n).mono Ioc_subset_Icc_self
  have H := betaMean_strictAntiOn hW hsymm hmono hm
  have hG : 0 < Real.Gamma (2 * a + 2 * m + n) / Real.Gamma (2 * m) :=
    div_pos (Real.Gamma_pos_of_pos (by positivity)) (Real.Gamma_pos_of_pos (by positivity))
  have hEq (d : ℝ) (hd : d ∈ Ico 0 m) :
      convolution a (m + d) (m - d) n =
        (Real.Gamma (2 * a + 2 * m + n) / Real.Gamma (2 * m)) *
          betaMean (W a n) m d := by
    have hp : 0 < m + d := by linarith [hd.1]
    have hq : 0 < m - d := sub_pos.mpr hd.2
    have hgp := (Real.Gamma_pos_of_pos hp).ne'
    have hgq := (Real.Gamma_pos_of_pos hq).ne'
    have hgm := (Real.Gamma_pos_of_pos (by positivity : (0:ℝ) < 2 * m)).ne'
    rw [convolution_eq_betaMean ha hp hq]
    unfold betaMean
    rw [show 2 * a + (m + d) + (m - d) + (n:ℝ) = 2 * a + 2 * m + n by ring]
    field_simp
  intro d hd e he hde
  change convolution a (m + e) (m - e) n < convolution a (m + d) (m - d) n
  rw [hEq d hd, hEq e he]
  exact mul_lt_mul_of_pos_left (H hd he hde) hG

/-- Every Turanian coefficient is strictly positive for positive real parameters. -/
theorem result : claim := by
  intro a b α β ha hb hα hβ n
  let m := b + (α + β) / 2
  let d := |α - β| / 2
  let e := (α + β) / 2
  have hm : 0 < m := by dsimp [m]; positivity
  have hde : d < e := by
    dsimp [d, e]
    have H : |α - β| < α + β := abs_lt.mpr ⟨by linarith, by linarith⟩
    linarith
  have he : e ∈ Ico 0 m := by
    dsimp [e, m]
    constructor <;> linarith
  have hd : d ∈ Ico 0 m := ⟨by dsimp [d]; positivity, hde.trans he.2⟩
  have H := convolution_strictAnti_imbalance ha hm n hd he hde
  have hleft : convolution a (m + e) (m - e) n = convolution a b (b + α + β) n := by
    have hp : m + e = b + α + β := by dsimp [m, e]; ring
    have hq : m - e = b := by dsimp [m, e]; ring
    rw [hp, hq, convolution_symm]
  have hright : convolution a (m + d) (m - d) n =
      convolution a (b + α) (b + β) n := by
    rcases le_total β α with hβα | hαβ
    · have hp : m + d = b + α := by
        dsimp [m, d]
        rw [abs_of_nonneg (sub_nonneg.mpr hβα)]
        ring
      have hq : m - d = b + β := by
        dsimp [m, d]
        rw [abs_of_nonneg (sub_nonneg.mpr hβα)]
        ring
      rw [hp, hq]
    · have hp : m + d = b + β := by
        dsimp [m, d]
        rw [abs_of_nonpos (sub_nonpos.mpr hαβ)]
        ring
      have hq : m - d = b + α := by
        dsimp [m, d]
        rw [abs_of_nonpos (sub_nonpos.mpr hαβ)]
        ring
      rw [hp, hq, convolution_symm]
  change convolution a (m + e) (m - e) n < convolution a (m + d) (m - d) n at H
  rw [hleft, hright] at H
  unfold phi
  rw [Finset.sum_sub_distrib]
  exact sub_pos.mpr H

end D5.S3.Analytic.IncompleteBeta.Result
