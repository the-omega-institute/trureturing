/- GID: D5/S3/Arith/CharacterSums/PascadiActualQuadraticResultant
   generality: G
   mirror-B: D5/B/S3/Arith/CharacterSums/PascadiActualQuadraticResultant
   mirror-E: none(waiver:actual-prime-cube-quadratic-stratum)
   anchors: []
   utility: none
   digest: Actual quadratic pencils need a seventh-power height gap, including zero leading baselines. -/

import D5.S3.Arith.CharacterSums.PascadiQuadraticPrimitiveDirection
import D5.S3.Arith.CharacterSums.PascadiQuadraticDirection
import D5.S3.Arith.CharacterSums.PascadiQuadraticConstantBase

/-! The actual LQ pencil supplies a common integer direction whenever its
baseline leading pair is nonzero. The constant-leading baseline is retained
as a separate exact quotient. Both branches use the seventh area weight. -/

open Polynomial

namespace D5.S3.Arith.CharacterSums.PrimeCube

noncomputable section

/-- The complete actual quadratic pair has zero resultant under the seventh
weighted height gap. The proof includes the baseline whose two leading
coefficients vanish and does not assume a selected lattice or counting bound. -/
theorem actual_quadratic_pair_resultant_zero (l m q r s : Fin 3 → ℤ)
    (p : ℕ) [Fact p.Prime] (b : ℤ) (I J : ℝ) (hI : 1 ≤ I) (hJ : 1 ≤ J)
    (hl : ∀ i, |(l i : ℝ)| ≤ 3*I) (hm : ∀ i, |(m i : ℝ)| ≤ 3*J)
    (hq : ∀ i, |(q i : ℝ)| ≤ I^2) (hr : ∀ i, |(r i : ℝ)| ≤ 2*I*J)
    (hs : ∀ i, |(s i : ℝ)| ≤ J^2)
    (h₁ : (pair l m q r s 1).natDegree = 2)
    (h₂ : (pair l m q r s 2).natDegree = 2)
    (hv₁ : (p : ℤ)^3 ∣ (pair l m q r s 1).eval b)
    (hv₂ : (p : ℤ)^3 ∣ (pair l m q r s 2).eval b)
    (hd₁ : (p : ℤ) ∣ (pair l m q r s 1).derivative.eval b)
    (hd₂ : (p : ℤ) ∣ (pair l m q r s 2).derivative.eval b)
    (hlead : ((pair l m q r s 1).coeff 2 : ZMod p) ≠ 0)
    (hL : IsUnit ((l 0+b*m 0 : ℤ) : ZMod p))
    (hgap : 14256*(I*J)^7 < (p : ℝ)^5) :
    (pair l m q r s 1).resultant (pair l m q r s 2) 2 2 = 0 := by
  have hI0 : 0 ≤ I := le_trans (by norm_num) hI
  have hJ0 : 0 ≤ J := le_trans (by norm_num) hJ
  have hJ47 : J^4 ≤ J^7 := pow_le_pow_right₀ hJ (by decide : 4 ≤ 7)
  have hI67 : I^6 ≤ I^7 := pow_le_pow_right₀ hI (by decide : 6 ≤ 7)
  have hgconst : 14256*I^7*J^4 < (p : ℝ)^5 := by
    calc
      _ ≤ 14256*I^7*J^7 := mul_le_mul_of_nonneg_left hJ47 (by positivity)
      _ = 14256*(I*J)^7 := by rw [mul_pow]; ring
      _ < _ := hgap
  by_cases hz : m 0 = 0 ∧ s 0 = 0
  · have hLc : IsUnit ((l 0 : ℤ) : ZMod p) := by simpa [hz.1] using hL
    exact constant_base_quadratic_singular_resultant_zero l m q r s p b I J
      hI hJ hl hm hq hr hs hz.1 hz.2 hLc h₁ h₂ hv₁ hv₂ hd₁ hd₂ hgconst
  · have hn : m 0 ≠ 0 ∨ s 0 ≠ 0 := by tauto
    have hc (i : Fin 3) : m 0*s i-m i*s 0 = 0 := by
      have hcoeff (j : Fin 3) :
          (pair l m q r s j).coeff 3 = m 0*s j-m j*s 0 := by
        rw [pair_coefficients]
        simp
      fin_cases i
      · ring
      · rw [← hcoeff 1]
        exact coeff_eq_zero_of_natDegree_lt (by omega)
      · rw [← hcoeff 2]
        exact coeff_eq_zero_of_natDegree_lt (by omega)
    obtain ⟨d,n,k,D,_,hmd,hns,hD,hk,hd,hn,hDu⟩ :=
      quadratic_coefficient_primitive_direction m s J hJ hn hc hm hs
    have hmeq : m = fun i => d*k i := funext hmd
    have hseq : s = fun i => n*k i := funext hns
    have hgd : 6804*I^6*J^4 < (p : ℝ)^5 := by
      calc
        _ ≤ 6804*I^7*J^4 := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hI67 (by norm_num)) (by positivity)
        _ ≤ 14256*I^7*J^4 := by nlinarith [mul_nonneg (pow_nonneg hI0 7)
          (pow_nonneg hJ0 4)]
        _ < _ := hgconst
    rw [hmeq,hseq] at h₁ h₂ hv₁ hv₂ hd₁ hd₂ hlead ⊢
    have hL' : IsUnit ((l 0+b*(d*k 0) : ℤ) : ZMod p) := by
      simpa only [hmeq] using hL
    exact quadratic_direction_resultant_zero l q r k d n p b I J D hI0 hJ0 hD
      hq hr hl hk hd hn hDu h₁ h₂ hv₁ hv₂ hd₁ hd₂ hlead hL' hgd

end
end D5.S3.Arith.CharacterSums.PrimeCube
