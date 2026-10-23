/- GID: D5/S3/Analytic/IncompleteBeta/Moment
   generality: G
   mirror-B: D5/B/S3/Analytic/IncompleteBeta/Moment
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.Pow.Deriv]
   utility: none
   digest: Finite coefficient convolution and its beta moment kernel. -/

import D5.S3.Analytic.IncompleteBeta.Defs
import D5.S3.Analytic.KummerRatio.BetaIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

noncomputable section

open scoped BigOperators
open Set MeasureTheory

namespace D5.S3.Analytic.IncompleteBeta

def convolution (a s t : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), coeff a s k * coeff a t (n - k)

def W (a : ℝ) (n : ℕ) (u : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    u ^ (a + k) * (1 - u) ^ (a + n - k) /
      (Real.Gamma (a + k + 1) * Real.Gamma (a + n - k + 1))

namespace Moment

theorem W_continuousOn {a : ℝ} (ha : 0 < a) (n : ℕ) :
    ContinuousOn (W a n) (Icc 0 1) := by
  unfold W
  apply continuousOn_finsetSum
  intro k hk
  have hk' : (k:ℝ) ≤ n := by exact_mod_cast (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
  exact ((continuous_id.continuousOn.rpow_const (fun _ _ => Or.inr (by positivity))).mul
    ((continuous_const.sub continuous_id).continuousOn.rpow_const
      (fun _ _ => Or.inr (by linarith)))).div_const _

theorem W_symm (n : ℕ) (u : ℝ) {a : ℝ} : W a n (1-u) = W a n u := by
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

theorem convolution_eq_betaMean {a s t : ℝ}
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
    field_simp (disch := assumption)
  unfold convolution
  rw [show (fun u => u^(s-1)*(1-u)^(t-1)*W a n u) =
    (fun u => ∑ k ∈ Finset.range (n+1), F k u) by
      funext u; dsimp only [W]; rw [Finset.mul_sum],
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

theorem W_hasDerivAt {a u : ℝ} (ha : 0 < a) (n : ℕ) (hu : u ∈ Ioo 0 1) :
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

theorem W_strictMonoOn {a : ℝ} (ha : 0 < a) (n : ℕ) :
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

end Moment

end D5.S3.Analytic.IncompleteBeta
