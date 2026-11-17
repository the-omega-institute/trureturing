/- GID: D5/S3/Arith/CharacterSums/PascadiOriginalRangeEstimates
   generality: G
   mirror-B: D5/B/S3/Arith/CharacterSums/PascadiOriginalRangeEstimates
   mirror-E: none(waiver:open-original-total-count)
   anchors: []
   utility: none
   digest: The original area range absorbs chart powers and logarithms into A times p epsilon. -/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Real.Sqrt

/-! The analytic final step retains the exact original area exponent. Its
logarithmic bound is proved from the real logarithm, not supplied by a caller. -/

namespace D5.S3.Arith.CharacterSums.Original

/-- The original area cap absorbs the weighted chart errors and the square-root
moment term into A p^epsilon, uniformly in all real p>=2 and actual areas A. -/
theorem original_range_error_absorption (ε C K : ℝ)
    (hε : 0 < ε) (hC : 1 ≤ C) (hK : 0 < K) :
    ∃ D : ℝ, 0 < D ∧ ∀ (p A : ℝ), 2 ≤ p → 0 ≤ A → A ≤ C*p^((18 : ℝ)/5) →
      let L := 1+Real.log (2*p)/Real.log 2
      K*p^(ε/2)*(A*(1+L)+A^2/p^4)+
        Real.sqrt (K*p^(ε/2)*A^6/p^15*L) ≤ D*A*p^ε := by
  have hhalf : 0 < ε/2 := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC0 : 0 ≤ C := by linarith
  let B := 2+1/((ε/2)*Real.log 2)
  have hB : 0 < B := by dsimp [B]; positivity
  let E := 1+K*B*C^4
  have hE : 0 < E := by dsimp [E]; positivity
  have hE2 : K*B*C^4 ≤ E^2 := by
    have hh : 0 ≤ K*B*C^4 := by positivity
    dsimp [E]
    nlinarith [sq_nonneg (K*B*C^4)]
  let D := K*(1+B+C)+E
  refine ⟨D, by dsimp [D]; positivity, ?_⟩
  intro p A hp hA harea
  dsimp only
  have hp1 : 1 ≤ p := by linarith
  have hp0 : 0 < p := by linarith
  let T := p^(ε/2)
  let L := 1+Real.log (2*p)/Real.log 2
  have hT : 0 < T := Real.rpow_pos_of_pos hp0 _
  have hT1 : 1 ≤ T := Real.one_le_rpow hp1 hhalf.le
  have hT2 : T^2 = p^ε := by
    dsimp [T]
    rw [← Real.rpow_mul_natCast hp0.le]
    congr 1
    ring
  have hTle : T ≤ T^2 := by
    calc
      T = T*1 := by ring
      _ ≤ T*T := mul_le_mul_of_nonneg_left hT1 hT.le
      _ = T^2 := by ring
  have hLexact : L = 2+Real.log p/Real.log 2 := by
    dsimp [L]
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hp0.ne', add_div, div_self hlog2.ne']
    ring
  have hL : L ≤ B*T := by
    have hd := div_le_div_of_nonneg_right (Real.log_le_rpow_div hp0.le hhalf) hlog2.le
    have he : p^(ε/2)/(ε/2)/Real.log 2 = (1/((ε/2)*Real.log 2))*T := by
      dsimp [T]
      simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
      ring
    rw [he] at hd
    rw [hLexact]
    dsimp [B]
    nlinarith only [hd, hT1]
  have hL0 : 0 ≤ L := by
    have hlog : 0 ≤ Real.log (2*p) := Real.log_nonneg (by linarith)
    dsimp [L]
    positivity
  have hp18 : p^((18 : ℝ)/5) ≤ p^4 := by
    simpa only [Real.rpow_ofNat] using
      Real.rpow_le_rpow_of_exponent_le hp1 (by norm_num : (18 : ℝ)/5 ≤ 4)
  have hAp4 : A/p^4 ≤ C := by
    apply (div_le_iff₀ (pow_pos hp0 4)).mpr
    exact harea.trans (mul_le_mul_of_nonneg_left hp18 hC0)
  have hA2p4 : A^2/p^4 ≤ C*A := by
    calc
      _ = A*(A/p^4) := by ring
      _ ≤ A*C := mul_le_mul_of_nonneg_left hAp4 hA
      _ = _ := by ring
  have hp72 : (p^((18 : ℝ)/5))^4 ≤ p^15 := by
    rw [← Real.rpow_mul_natCast hp0.le]
    simpa only [Real.rpow_ofNat, Nat.cast_ofNat] using
      Real.rpow_le_rpow_of_exponent_le hp1 (by norm_num : (18 : ℝ)/5*4 ≤ 15)
  have hA4p15 : A^4/p^15 ≤ C^4 := by
    apply (div_le_iff₀ (pow_pos hp0 15)).mpr
    calc
      A^4 ≤ (C*p^((18 : ℝ)/5))^4 := pow_le_pow_left₀ hA harea 4
      _ = C^4*(p^((18 : ℝ)/5))^4 := mul_pow _ _ _
      _ ≤ C^4*p^15 := mul_le_mul_of_nonneg_left hp72 (pow_nonneg hC0 4)
  have hA6p15 : A^6/p^15 ≤ C^4*A^2 := by
    calc
      _ = A^2*(A^4/p^15) := by ring
      _ ≤ A^2*C^4 := mul_le_mul_of_nonneg_left hA4p15 (sq_nonneg A)
      _ = _ := by ring
  have hbase : A*(1+L)+A^2/p^4 ≤ (1+B+C)*A*T := by
    calc
      _ ≤ A*(1+B*T)+C*A := add_le_add
        (mul_le_mul_of_nonneg_left (add_le_add le_rfl hL) hA) hA2p4
      _ = A*(1+C)+A*B*T := by ring
      _ ≤ (A*(1+C))*T+A*B*T := add_le_add
        (le_mul_of_one_le_right (by positivity : 0 ≤ A*(1+C)) hT1) le_rfl
      _ = _ := by ring
  have hfirst : K*T*(A*(1+L)+A^2/p^4) ≤ K*(1+B+C)*A*T^2 := by
    calc
      _ ≤ K*T*((1+B+C)*A*T) := mul_le_mul_of_nonneg_left hbase (by positivity)
      _ = _ := by ring
  have hrad : K*T*A^6/p^15*L ≤ (E*A*T)^2 := by
    calc
      _ = K*T*(A^6/p^15)*L := by ring
      _ ≤ K*T*(C^4*A^2)*L := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hA6p15 (by positivity)) hL0
      _ ≤ K*T*(C^4*A^2)*(B*T) :=
        mul_le_mul_of_nonneg_left hL (by positivity)
      _ = (K*B*C^4)*(A*T)^2 := by ring
      _ ≤ E^2*(A*T)^2 := mul_le_mul_of_nonneg_right hE2 (sq_nonneg (A*T))
      _ = _ := by ring
  have hsqrt : Real.sqrt (K*T*A^6/p^15*L) ≤ E*A*T :=
    Real.sqrt_le_iff.mpr ⟨by positivity, hrad⟩
  have hsqrt' : Real.sqrt (K*T*A^6/p^15*L) ≤ E*A*T^2 :=
    hsqrt.trans (mul_le_mul_of_nonneg_left hTle (by positivity : 0 ≤ E*A))
  change K*T*(A*(1+L)+A^2/p^4)+Real.sqrt (K*T*A^6/p^15*L) ≤ D*A*p^ε
  calc
    _ ≤ K*(1+B+C)*A*T^2+E*A*T^2 := add_le_add hfirst hsqrt'
    _ = _ := by rw [← hT2]; dsimp [D]; ring

end D5.S3.Arith.CharacterSums.Original
