/- GID: D5/S3/Analytic/IncompleteBetaShape/Result
   generality: I
   mirror-B: D5/B/S3/Analytic/IncompleteBetaShape/Result
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Algebra.BigOperators.NatAntidiagonal]
   utility: none
   digest: Strict coefficient signs for real shifts of the first incomplete beta parameter. -/

import D5.S3.Analytic.IncompleteBetaShape.Mixture
import D5.S3.Analytic.IncompleteBetaShape.Kernel
import D5.S3.Analytic.IncompleteBeta.Comparison
import Mathlib.Algebra.BigOperators.NatAntidiagonal

/-! Equal-sum convolution comparison settles both strict coefficient signs. -/

noncomputable section
open Set
open D5.S3.Analytic.IncompleteBeta (coeff)
open D5.S3.Analytic.IncompleteBeta.Comparison
open D5.S3.Analytic.IncompleteBetaShape.Defs
open D5.S3.Analytic.IncompleteBetaShape.Mixture
open D5.S3.Analytic.IncompleteBetaShape.Kernel

namespace D5.S3.Analytic.IncompleteBetaShape.Result

private lemma mixtureFactor_pos {c b : ℝ} (hc : 0 < c) (hb : 0 < b) (n : ℕ) :
    0 < mixtureFactor c n b := by
  unfold mixtureFactor
  exact div_pos (mul_pos (by positivity) (Real.Gamma_pos_of_pos (by positivity)))
    (mul_pos (sq_pos_of_pos (Real.Gamma_pos_of_pos hb))
      (Real.Gamma_pos_of_pos (by positivity)))

private lemma convolution_eq_centeredMean {m b d : ℝ} (hm : 0 < m) (hb : 0 < b)
    (n : ℕ) (hd : d ∈ Ico 0 m) :
    convolution (m+d) (m-d) b n = mixtureFactor (2*m) n b *
      betaMean (H (2*m) n b) m d := by
  have hp : 0 < m+d := by linarith [hd.1]
  have hq : 0 < m-d := by linarith [hd.2]
  rw [convolution_eq_betaMean_H hp hq hb n]
  simp only [show m+d+(m-d) = 2*m by ring,
    show (2*m)/2 = m by ring, show (m+d-(m-d))/2 = d by ring]

/-- At fixed sum, the convolution strictly decreases with shape imbalance for b above one. -/
theorem convolution_strictAnti_imbalance {m b : ℝ} (hm : 0 < m) (hb : 1 < b) (n : ℕ) :
    StrictAntiOn (fun d => convolution (m+d) (m-d) b n) (Ico 0 m) := by
  have hc : 0 < 2*m := by positivity
  have hb0 : 0 < b := by linarith
  have hcompare := betaMean_strictAntiOn (H_continuousOn hc hb0 n)
    (fun v _ => H_symm (2*m) n b v) (H_strictMonoOn_of_one_lt hc hb n) hm
  intro d hd e he hde
  change convolution (m+e) (m-e) b n < convolution (m+d) (m-d) b n
  rw [convolution_eq_centeredMean hm hb0 n he, convolution_eq_centeredMean hm hb0 n hd]
  exact mul_lt_mul_of_pos_left (hcompare hd he hde) (mixtureFactor_pos hc hb0 n)

/-- At fixed sum, the convolution strictly increases with shape imbalance for b below one. -/
theorem convolution_strictMono_imbalance {m b : ℝ} (hm : 0 < m) (hb : 0 < b)
    (hb1 : b < 1) (n : ℕ) :
    StrictMonoOn (fun d => convolution (m+d) (m-d) b n) (Ico 0 m) := by
  have hc : 0 < 2*m := by positivity
  have hcompare := betaMean_strictAntiOn (H_continuousOn hc hb n).neg
    (fun v _ => congrArg Neg.neg (H_symm (2*m) n b v))
    (H_strictAntiOn_of_lt_one hc hb hb1 n).neg hm
  have hneg (d : ℝ) : betaMean (fun v => -H (2*m) n b v) m d =
      -betaMean (H (2*m) n b) m d := by
    unfold betaMean
    simp only [mul_neg, intervalIntegral.integral_neg]
  intro d hd e he hde
  change convolution (m+d) (m-d) b n < convolution (m+e) (m-e) b n
  rw [convolution_eq_centeredMean hm hb n hd, convolution_eq_centeredMean hm hb n he]
  apply mul_lt_mul_of_pos_left _ (mixtureFactor_pos hc hb n)
  have hh := hcompare hd he hde
  change betaMean (fun v => -H (2*m) n b v) m e <
    betaMean (fun v => -H (2*m) n b v) m d at hh
  rw [hneg, hneg] at hh
  linarith

/-- All coefficients have the strict sign determined by the position of b relative to one. -/
theorem result : claim := by
  intro a b α β ha hb hα hβ n
  let m := a+(α+β)/2
  let d := |α-β|/2
  let e := (α+β)/2
  have hm : 0 < m := by dsimp [m]; positivity
  have hde : d < e := by
    have hh : |α-β| < α+β := abs_lt.mpr ⟨by linarith,by linarith⟩
    dsimp [d,e]
    linarith
  have he : e ∈ Ico 0 m := by dsimp [e,m]; constructor <;> linarith
  have hd : d ∈ Ico 0 m := ⟨by dsimp [d]; positivity, hde.trans he.2⟩
  have hsymm (p q : ℝ) : convolution p q b n = convolution q p b n := by
    have hh := Finset.Nat.sum_antidiagonal_swap (n := n)
      (f := fun ij : ℕ × ℕ => coeff p b ij.1 * coeff q b ij.2)
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hh
    exact hh.symm.trans (Finset.sum_congr rfl (fun k _ => mul_comm _ _))
  have hleft : convolution (m+e) (m-e) b n = convolution a (a+α+β) b n := by
    rw [show m+e = a+α+β by dsimp [m,e]; ring,
      show m-e = a by dsimp [m,e]; ring, hsymm]
  have hright : convolution (m+d) (m-d) b n = convolution (a+α) (a+β) b n := by
    rcases le_total β α with hβα | hαβ
    · rw [show m+d = a+α by dsimp [m,d]; rw [abs_of_nonneg (sub_nonneg.mpr hβα)]; ring,
        show m-d = a+β by dsimp [m,d]; rw [abs_of_nonneg (sub_nonneg.mpr hβα)]; ring]
    · rw [show m+d = a+β by dsimp [m,d]; rw [abs_of_nonpos (sub_nonpos.mpr hαβ)]; ring,
        show m-d = a+α by dsimp [m,d]; rw [abs_of_nonpos (sub_nonpos.mpr hαβ)]; ring,
        hsymm]
  constructor
  · intro hb1
    have hh := convolution_strictMono_imbalance hm hb hb1 n hd he hde
    change convolution (m+d) (m-d) b n < convolution (m+e) (m-e) b n at hh
    rw [hleft,hright] at hh
    unfold psi
    rw [Finset.sum_sub_distrib]
    exact sub_neg.mpr hh
  · intro hb1
    have hh := convolution_strictAnti_imbalance hm hb1 n hd he hde
    change convolution (m+e) (m-e) b n < convolution (m+d) (m-d) b n at hh
    rw [hleft,hright] at hh
    unfold psi
    rw [Finset.sum_sub_distrib]
    exact sub_pos.mpr hh

end D5.S3.Analytic.IncompleteBetaShape.Result
