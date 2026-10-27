import D5.S3.Weil.ZetaGamma.FormCore.ThetaLogFourthCheck
import Mathlib.Tactic
noncomputable section
/- Uncompiled continuation of ThetaLogFourthCertificate.fragment.lean. -/

namespace RhTransient.ThetaLogFourthCertificate

open Real

private theorem abs_mul_perturbation
    {a b r s A B R S : ℝ}
    (ha : |a| ≤ A) (hb : |b| ≤ B) (hr : |r| ≤ R) (hs : |s| ≤ S) :
    |(a+r)*(b+s)-a*b| ≤ (A+R)*(B+S)-A*B := by
  have hA := (abs_nonneg a).trans ha
  have hB := (abs_nonneg b).trans hb
  have hR := (abs_nonneg r).trans hr
  have hS := (abs_nonneg s).trans hs
  have h1 : |a*s| ≤ A*S := by
    rw [abs_mul]
    exact mul_le_mul ha hs (abs_nonneg _) hA
  have h2 : |r*b| ≤ R*B := by
    rw [abs_mul]
    exact mul_le_mul hr hb (abs_nonneg _) hR
  have h3 : |r*s| ≤ R*S := by
    rw [abs_mul]
    exact mul_le_mul hr hs (abs_nonneg _) hR
  calc
    _ = |a*s+r*b+r*s| := by congr 1; ring
    _ ≤ |a*s+r*b|+|r*s| := abs_add_le _ _
    _ ≤ |a*s|+|r*b|+|r*s| := by linarith [abs_add_le (a*s) (r*b)]
    _ ≤ A*S+R*B+R*S := by linarith
    _ = _ := by ring

private theorem abs_four_mul_perturbation
    {a b c d r s t u A B C D R S T U : ℝ}
    (ha : |a| ≤ A) (hb : |b| ≤ B) (hc : |c| ≤ C) (hd : |d| ≤ D)
    (hr : |r| ≤ R) (hs : |s| ≤ S) (ht : |t| ≤ T) (hu : |u| ≤ U) :
    |(a+r)*(b+s)*(c+t)*(d+u)-a*b*c*d| ≤
      (A+R)*(B+S)*(C+T)*(D+U)-A*B*C*D := by
  have hA := (abs_nonneg a).trans ha
  have hC := (abs_nonneg c).trans hc
  have hab : |a*b| ≤ A*B := by
    rw [abs_mul]
    exact mul_le_mul ha hb (abs_nonneg _) hA
  have hcd : |c*d| ≤ C*D := by
    rw [abs_mul]
    exact mul_le_mul hc hd (abs_nonneg _) hC
  have hrs := abs_mul_perturbation ha hb hr hs
  have htu := abs_mul_perturbation hc hd ht hu
  have h := abs_mul_perturbation hab hcd hrs htu
  convert h using 1 <;> (try congr 1) <;> ring

private theorem abs_add_five (a b c d e : ℝ) :
    |a+b+c+d+e| ≤ |a|+|b|+|c|+|d|+|e| := by
  calc
    _ ≤ |a+b+c+d|+|e| := abs_add_le _ _
    _ ≤ |a+b+c|+|d|+|e| := by linarith [abs_add_le (a+b+c) d]
    _ ≤ |a+b|+|c|+|d|+|e| := by linarith [abs_add_le (a+b) c]
    _ ≤ _ := by linarith [abs_add_le a b]

/-- The full quartic perturbation is bounded by the increment of its
    coefficientwise absolute polynomial, with no sign premise on the jets. -/
theorem fourthNumerator_perturbation
    {a b c d e r s t u v A B C D E R S T U V : ℝ}
    (ha : |a| ≤ A) (hb : |b| ≤ B) (hc : |c| ≤ C)
    (hd : |d| ≤ D) (he : |e| ≤ E)
    (hr : |r| ≤ R) (hs : |s| ≤ S) (ht : |t| ≤ T)
    (hu : |u| ≤ U) (hv : |v| ≤ V) :
    |fourthNumerator (a+r) (b+s) (c+t) (d+u) (e+v)-
      fourthNumerator a b c d e| ≤
      absoluteFourth (A+R) (B+S) (C+T) (D+U) (E+V)-absoluteFourth A B C D E := by
  have h1 := abs_four_mul_perturbation ha ha ha he hr hr hr hv
  have h2 := abs_four_mul_perturbation ha ha hb hd hr hr hs hu
  have h3 := abs_four_mul_perturbation ha ha hc hc hr hr ht ht
  have h4 := abs_four_mul_perturbation ha hb hb hc hr hs hs ht
  have h5 := abs_four_mul_perturbation hb hb hb hb hs hs hs hs
  let d1 := (a+r)^3*(e+v)-a^3*e
  let d2 := (a+r)^2*(b+s)*(d+u)-a^2*b*d
  let d3 := (a+r)^2*(c+t)^2-a^2*c^2
  let d4 := (a+r)*(b+s)^2*(c+t)-a*b^2*c
  let d5 := (b+s)^4-b^4
  have hsum := abs_add_five d1 (-4*d2) (-3*d3) (12*d4) (-6*d5)
  norm_num only [abs_mul] at hsum
  have hnormalized :
      |fourthNumerator (a+r) (b+s) (c+t) (d+u) (e+v)-
        fourthNumerator a b c d e| ≤ |d1|+4*|d2|+3*|d3|+12*|d4|+6*|d5| := by
    convert hsum using 1 <;> dsimp [d1,d2,d3,d4,d5,fourthNumerator] <;>
      (try congr 1) <;> ring
  have h1' : |d1| ≤ (A+R)^3*(E+V)-A^3*E := by
    convert h1 using 1 <;> (try dsimp [d1]) <;> (try congr 1) <;> ring
  have h2' : |d2| ≤ (A+R)^2*(B+S)*(D+U)-A^2*B*D := by
    convert h2 using 1 <;> (try dsimp [d2]) <;> (try congr 1) <;> ring
  have h3' : |d3| ≤ (A+R)^2*(C+T)^2-A^2*C^2 := by
    convert h3 using 1 <;> (try dsimp [d3]) <;> (try congr 1) <;> ring
  have h4' : |d4| ≤ (A+R)*(B+S)^2*(C+T)-A*B^2*C := by
    convert h4 using 1 <;> (try dsimp [d4]) <;> (try congr 1) <;> ring
  have h5' : |d5| ≤ (B+S)^4-B^4 := by
    convert h5 using 1 <;> (try dsimp [d5]) <;> (try congr 1) <;> ring
  dsimp [absoluteFourth]
  linarith

/-- The whole positive-coefficient perturbation polynomial, at every
    0 <= s <= 1, stays below s/2. This retains all degrees up to four. -/
theorem scaled_rational_perturbation {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    absoluteFourth
      (frontBudget 0 + tailBudget 0/tailExponentialDenominator*s)
      (frontBudget 1 + tailBudget 1/tailExponentialDenominator*s)
      (frontBudget 2 + tailBudget 2/tailExponentialDenominator*s)
      (frontBudget 3 + tailBudget 3/tailExponentialDenominator*s)
      (frontBudget 4 + tailBudget 4/tailExponentialDenominator*s) -
    absoluteFourth (frontBudget 0) (frontBudget 1) (frontBudget 2)
      (frontBudget 3) (frontBudget 4) ≤ s/2 := by
  let deltaOne : ℝ :=
    absoluteFourth
      (frontBudget 0 + tailBudget 0/tailExponentialDenominator)
      (frontBudget 1 + tailBudget 1/tailExponentialDenominator)
      (frontBudget 2 + tailBudget 2/tailExponentialDenominator)
      (frontBudget 3 + tailBudget 3/tailExponentialDenominator)
      (frontBudget 4 + tailBudget 4/tailExponentialDenominator) -
    absoluteFourth (frontBudget 0) (frontBudget 1) (frontBudget 2)
      (frontBudget 3) (frontBudget 4)
  have hdeltaOne : deltaOne < 1/2 := rational_perturbation_certificate
  have hs2 : s^2 ≤ s := by nlinarith [mul_nonneg hs0 (sub_nonneg.mpr hs1)]
  have hs3 : s^3 ≤ s := by
    calc s^3 = s^2*s := by ring
         _ ≤ s*s := mul_le_mul_of_nonneg_right hs2 hs0
         _ ≤ s := by nlinarith
  have hs4 : s^4 ≤ s := by
    calc s^4 = s^3*s := by ring
         _ ≤ s*s := mul_le_mul_of_nonneg_right hs3 hs0
         _ ≤ s := by nlinarith
  have hscale :
      absoluteFourth
        (frontBudget 0 + tailBudget 0/tailExponentialDenominator*s)
        (frontBudget 1 + tailBudget 1/tailExponentialDenominator*s)
        (frontBudget 2 + tailBudget 2/tailExponentialDenominator*s)
        (frontBudget 3 + tailBudget 3/tailExponentialDenominator*s)
        (frontBudget 4 + tailBudget 4/tailExponentialDenominator*s) -
      absoluteFourth (frontBudget 0) (frontBudget 1) (frontBudget 2)
        (frontBudget 3) (frontBudget 4) ≤ s*deltaOne := by
    norm_num [deltaOne,absoluteFourth,frontBudget,tailBudget,tailExponentialDenominator]
    nlinarith
  exact hscale.trans (by
    simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hdeltaOne.le hs0)

end RhTransient.ThetaLogFourthCertificate
