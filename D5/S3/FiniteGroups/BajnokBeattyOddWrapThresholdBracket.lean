/- GID: D5/S3/FiniteGroups/BajnokBeattyOddWrapThresholdBracket
   generality: I
   mirror-B: D5/B/S3/FiniteGroups/BajnokBeattyOddWrapThresholdBracket
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Finite Gaussian errors bracket the same unique original threshold with every original sign. -/



import D5.S3.FiniteGroups.BajnokBeattyOddWrapGaussianUpperEnvelope
import D5.S3.FiniteGroups.BajnokBeattyOddWrapGaussianRoot

/-! The scale is fixed by the existing order-nine Perron instance. -/

set_option autoImplicit false

namespace D5.S3.FiniteGroups.BajnokBeattyOddWrapThresholdBracket

open BajnokBeattyOddWrapSingleCrossing BajnokBeattyOddWrapPositiveCone
open BajnokBeattyOddWrapReturnCounts BajnokBeattyOddWrapGaussianEnvelope
open BajnokBeattyOddWrapGaussianRoot BajnokBeattyOddWrapGaussianUpperEnvelope

/-- Positivity comes from the exact original binomial readout; it is not
an additional premise on the original return counts. -/
private theorem original_second_pos (p t : ℤ) (hp3 : 3 ≤ p) (hpo : Odd p)
    (ht2 : 2 ≤ t) : 0 < (original_return_pair p t).2 := by
  have hp : 0 < p := by omega
  have hc := actual_odd_wrap_counts p t hp3 hpo ht2
  have hhalf3 : p*((6*t-1)+3)/2 = 3*p*t+p := by
    have hh : p*((6*t-1)+3) = 2*(3*p*t+p) := by ring
    omega
  have hW33 : (original_return_pair p t).2 =
      4*Nat.choose (p*(6*t-1)).toNat (3*p*t+p).toNat := by
    calc
      (original_return_pair p t).2 =
          4*Nat.choose (p*(6*t-1)).toNat (p*((6*t-1)+3)/2).toNat := hc.2
      _ = _ := by rw [hhalf3]
  have hindex : 3*p*t+p ≤ p*(6*t-1) := by
    have hmul := mul_nonneg hp.le (show 0 ≤ 3*t-2 by omega)
    nlinarith only [hmul]
  have hindexNat : (3*p*t+p).toNat ≤ (p*(6*t-1)).toNat := by
    omega
  rw [hW33]
  exact mul_pos (by norm_num) (Nat.choose_pos hindexNat)

private theorem alpha_pos : 0 < alpha := by
  linarith only [alpha_gt_twentyfour_twentyfive]

private theorem alpha_root_identity : 3*alpha*s_star = 2 := by
  have hs : 0 < s_star := by linarith only [two_thirds_lt_s_star]
  unfold alpha
  field_simp [hs.ne'] <;> ring

private theorem root_as_alpha : s_star = 2/(3*alpha) := by
  apply (eq_div_iff (show 3*alpha ≠ 0 from (mul_pos (by norm_num) alpha_pos).ne')).2
  nlinarith only [alpha_root_identity]

/-- Algebraic coordinates used in both finite comparisons. -/
private theorem centered_gaussian_parameter (P t : ℝ) (hP : 0 < P)
    (hv : 0 < t-1/6+1/(6*P)) :
    4*P^2/(P*(6*t-1)+1) = 2*P/(3*(t-1/6+1/(6*P))) := by
  have hR : P*(6*t-1)+1 = 6*P*(t-1/6+1/(6*P)) := by
    field_simp [hP.ne'] <;> ring
  have hR0 : P*(6*t-1)+1 ≠ 0 := by
    rw [hR]
    exact mul_ne_zero (mul_ne_zero (by norm_num) hP.ne') hv.ne'
  apply (div_eq_div_iff hR0 (mul_ne_zero (by norm_num) hv.ne')).2
  rw [hR]
  ring

/-- Bound a threshold satisfying exactly the original full sign criterion. -/
private theorem original_threshold_bounds (p : ℤ) (hp5 : 5 ≤ p) (hpo : Odd p)
    (T : ℕ)
    (hT : 2 < T ∧
      (∀ t : ℕ, 2 ≤ t → t < T →
        (original_return_pair p t).2 < (original_return_pair p t).1) ∧
      (original_return_pair p T).1 ≤ (original_return_pair p T).2 ∧
      (∀ t : ℕ, T < t →
        (original_return_pair p t).1 < (original_return_pair p t).2)) :
    alpha*(p : ℝ)+1/6-1/(6*(p : ℝ)) < (T : ℝ) ∧
      (T : ℤ) ≤ Int.ceil (alpha*(p : ℝ)+1/6-1/(25*(p : ℝ))) := by
  have hp3 : 3 ≤ p := by omega
  have hpR5 : (5 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp5
  have hpR : 0 < (p : ℝ) := by linarith only [hpR5]
  have hpR2 : 0 < (p : ℝ)^2 := pow_pos hpR 2
  have hTP : (T : ℤ) ≤ p := by
    let P : ℕ := p.toNat
    have hP : (P : ℤ) = p := Int.toNat_of_nonneg (by omega)
    have hP2 : 2 ≤ P := by omega
    have hpos := actual_positive_odd_wrap_cone p p hp5 hpo le_rfl
    have hposP : (original_return_pair p (P : ℤ)).1 <
        (original_return_pair p (P : ℤ)).2 := by simpa only [hP] using hpos
    have hTPNat : T ≤ P := by
      by_contra h
      have hbefore := hT.2.1 P hP2 (by omega)
      omega
    have hh : (T : ℤ) ≤ (P : ℤ) := by exact_mod_cast hTPNat
    simpa only [hP] using hh
  have hlower : alpha*(p : ℝ)+1/6-1/(6*(p : ℝ)) < (T : ℝ) := by
    by_contra h
    have hTlow : (T : ℝ) ≤ alpha*(p : ℝ)+1/6-1/(6*(p : ℝ)) :=
      le_of_not_gt h
    let v : ℝ := (T : ℝ)-1/6+1/(6*(p : ℝ))
    let s : ℝ := 4*(p : ℝ)^2/((p : ℝ)*(6*(T : ℝ)-1)+1)
    have hTR : (2 : ℝ) < (T : ℝ) := by exact_mod_cast hT.1
    have hinv : 0 ≤ 1/(6*(p : ℝ)) := by positivity
    have hv : 0 < v := by dsimp only [v]; linarith only [hTR, hinv]
    have hvle : v ≤ alpha*(p : ℝ) := by dsimp only [v]; linarith only [hTlow]
    have hsform : s = 2*(p : ℝ)/(3*v) :=
      centered_gaussian_parameter (p : ℝ) (T : ℝ) hpR hv
    have hsroot : s_star ≤ s := by
      rw [hsform]
      apply (le_div_iff₀ (show 0 < 3*v by positivity)).2
      have hmul := mul_le_mul_of_nonneg_left hvle
        (show 0 ≤ 3*s_star by linarith only [two_thirds_lt_s_star])
      have hid := congrArg (fun x : ℝ => x*(p : ℝ)) alpha_root_identity
      nlinarith only [hmul, hid]
    have hsec := gaussian_secant two_thirds_lt_s_star.le hsroot
    rw [gaussian_s_star] at hsec
    have hG : (2 : ℝ) ≤ gaussian s := by linarith only [hsec, hsroot]
    have henv : gaussian s <
        2*((original_return_pair p (T : ℤ)).1 : ℝ)/
          ((original_return_pair p (T : ℤ)).2 : ℝ) := by
      simpa only [gaussian, s, Int.cast_natCast] using
        actual_gaussian_envelope p (T : ℤ) hp3 hpo (by omega) hTP
    have hden : (0 : ℝ) < ((original_return_pair p (T : ℤ)).2 : ℝ) := by
      exact_mod_cast original_second_pos p (T : ℤ) hp3 hpo (by omega)
    have hat : ((original_return_pair p (T : ℤ)).1 : ℝ) ≤
        ((original_return_pair p (T : ℤ)).2 : ℝ) := by
      exact_mod_cast hT.2.2.1
    have hratio : 2*((original_return_pair p (T : ℤ)).1 : ℝ)/
        ((original_return_pair p (T : ℤ)).2 : ℝ) ≤ 2 := by
      apply (div_le_iff₀ hden).2
      linarith only [hat]
    linarith only [hG, henv, hratio]
  refine ⟨hlower, ?_⟩
  let q : ℝ := alpha*(p : ℝ)+1/6-1/(25*(p : ℝ))
  let U : ℤ := Int.ceil q
  change (T : ℤ) ≤ U
  have hqU : q ≤ (U : ℝ) := Int.le_ceil q
  have hinv25 : 1/(25*(p : ℝ)) ≤ 1/125 := by
    apply (div_le_iff₀ (show 0 < 25*(p : ℝ) by positivity)).2
    linarith only [hpR5]
  have hoffset : 0 < 1/6-1/(25*(p : ℝ)) := by linarith only [hinv25]
  have halphaP : (24/25 : ℝ)*(p : ℝ) < alpha*(p : ℝ) :=
    mul_lt_mul_of_pos_right alpha_gt_twentyfour_twentyfive hpR
  have hq2 : (2 : ℝ) < q := by
    dsimp only [q]
    linarith only [halphaP, hpR5, hoffset]
  have hU2 : (2 : ℤ) ≤ U := by
    have hh : (2 : ℝ) ≤ (U : ℝ) := by linarith only [hq2, hqU]
    exact_mod_cast hh
  by_cases hpU : p ≤ U
  · exact hTP.trans hpU
  · have hUp : U < p := lt_of_not_ge hpU
    let u : ℕ := U.toNat
    have hu : (u : ℤ) = U := Int.toNat_of_nonneg (by omega)
    have hu2 : 2 ≤ u := by omega
    have huR : (u : ℝ) = (U : ℝ) := by exact_mod_cast hu
    have hup : (u : ℤ) ≤ p := by omega
    have hqur : alpha*(p : ℝ)+1/6-1/(25*(p : ℝ)) ≤ (u : ℝ) := by
      simpa only [q, huR] using hqU
    have hbandR : 24*(p : ℝ) ≤ 25*(u : ℝ) := by
      linarith only [hqur, halphaP, hoffset]
    have hband : 24*p ≤ 25*(u : ℤ) := by exact_mod_cast hbandR
    let v : ℝ := (u : ℝ)-1/6+1/(6*(p : ℝ))
    let s : ℝ := 4*(p : ℝ)^2/((p : ℝ)*(6*(u : ℝ)-1)+1)
    have hcorrection : -(1/(25*(p : ℝ)))+1/(6*(p : ℝ)) =
        19/(150*(p : ℝ)) := by
      field_simp [hpR.ne'] <;> ring
    have hvlow : alpha*(p : ℝ)+19/(150*(p : ℝ)) ≤ v := by
      dsimp only [v]
      linarith only [hqur, hcorrection]
    have hv : 0 < v := by
      have hmain : 0 < alpha*(p : ℝ) := mul_pos alpha_pos hpR
      have hsmall : 0 < 19/(150*(p : ℝ)) := by positivity
      linarith only [hvlow, hmain, hsmall]
    have hvP : v ≤ (p : ℝ) := by
      have hupZ : (u : ℤ) ≤ p-1 := by omega
      have hupR : (u : ℝ) ≤ (p : ℝ)-1 := by exact_mod_cast hupZ
      have hinv6 : 1/(6*(p : ℝ)) ≤ 1/6 := by
        apply (div_le_iff₀ (show 0 < 6*(p : ℝ) by positivity)).2
        linarith only [hpR5]
      dsimp only [v]
      linarith only [hupR, hinv6]
    have hsform : s = 2*(p : ℝ)/(3*v) :=
      centered_gaussian_parameter (p : ℝ) (u : ℝ) hpR hv
    have hs : (2/3 : ℝ) ≤ s := by
      rw [hsform]
      apply (le_div_iff₀ (show 0 < 3*v by positivity)).2
      linarith only [hvP]
    have hvroot : alpha*(p : ℝ) ≤ v := by
      have hsmall : 0 ≤ 19/(150*(p : ℝ)) := by positivity
      linarith only [hvlow, hsmall]
    have hsroot : s ≤ s_star := by
      rw [hsform]
      apply (div_le_iff₀ (show 0 < 3*v by positivity)).2
      have hmul := mul_le_mul_of_nonneg_left hvroot
        (show 0 ≤ 3*s_star by linarith only [two_thirds_lt_s_star])
      have hid := congrArg (fun x : ℝ => x*(p : ℝ)) alpha_root_identity
      nlinarith only [hmul, hid]
    have hgapform : s_star-s = 2*(v-alpha*(p : ℝ))/(3*alpha*v) := by
      rw [root_as_alpha, hsform]
      field_simp [alpha_pos.ne', hv.ne'] <;> ring
    have hgap : 19/(225*(p : ℝ)^2) ≤ s_star-s := by
      rw [hgapform]
      apply (le_div_iff₀ (show 0 < 3*alpha*v from mul_pos (mul_pos (by norm_num) alpha_pos) hv)).2
      have halphav : alpha*v ≤ v := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right alpha_lt_one.le hv.le
      have hdenle : 3*alpha*v ≤ 3*(p : ℝ) := by
        linarith only [halphav, hvP]
      have hvdiff : 19/(150*(p : ℝ)) ≤ v-alpha*(p : ℝ) := by
        linarith only [hvlow]
      calc
        (19/(225*(p : ℝ)^2))*(3*alpha*v) ≤
            (19/(225*(p : ℝ)^2))*(3*(p : ℝ)) :=
          mul_le_mul_of_nonneg_left hdenle (by positivity)
        _ = 2*(19/(150*(p : ℝ))) := by
          field_simp [hpR.ne'] <;> ring
        _ ≤ 2*(v-alpha*(p : ℝ)) :=
          mul_le_mul_of_nonneg_left hvdiff (by norm_num)
    have hsec := gaussian_secant hs hsroot
    rw [gaussian_s_star] at hsec
    have hmarginEq : (98/75 : ℝ)*(19/(225*(p : ℝ)^2))-1/(10*(p : ℝ)^2) =
        (349/33750 : ℝ)/(p : ℝ)^2 := by
      field_simp [hpR.ne'] <;> ring
    have hmargin : 1/(10*(p : ℝ)^2) < (98/75 : ℝ)*(19/(225*(p : ℝ)^2)) := by
      have hpos : 0 < (349/33750 : ℝ)/(p : ℝ)^2 := by positivity
      linarith only [hmarginEq, hpos]
    have hG : gaussian s+1/(10*(p : ℝ)^2) < 2 := by
      have hmul := mul_le_mul_of_nonneg_left hgap (by norm_num : (0 : ℝ) ≤ 98/75)
      linarith only [hsec, hmul, hmargin]
    have henv : 2*((original_return_pair p (u : ℤ)).1 : ℝ)/
        ((original_return_pair p (u : ℤ)).2 : ℝ) <
          gaussian s+1/(10*(p : ℝ)^2) := by
      simpa only [gaussian, s, Int.cast_natCast] using
        actual_gaussian_upper_envelope p (u : ℤ) hp5 hpo (by omega) hup hband
    have hratio : 2*((original_return_pair p (u : ℤ)).1 : ℝ)/
        ((original_return_pair p (u : ℤ)).2 : ℝ) < 2 := henv.trans hG
    have hden : (0 : ℝ) < ((original_return_pair p (u : ℤ)).2 : ℝ) := by
      exact_mod_cast original_second_pos p (u : ℤ) hp3 hpo (by omega)
    have hcountR : ((original_return_pair p (u : ℤ)).1 : ℝ) <
        ((original_return_pair p (u : ℤ)).2 : ℝ) := by
      have hh := (div_lt_iff₀ hden).mp hratio
      linarith only [hh]
    have hcount : (original_return_pair p (u : ℤ)).1 <
        (original_return_pair p (u : ℤ)).2 := by exact_mod_cast hcountR
    have hTu : T ≤ u := by
      by_contra h
      have hbefore := hT.2.1 u hu2 (by omega)
      omega
    have hh : (T : ℤ) ≤ (u : ℤ) := by exact_mod_cast hTu
    simpa only [hu] using hh

/-- The SAME unique original odd-wrap threshold, with all original signs
and a finite quantitative bracket. The domain includes odd composites. -/
theorem actual_odd_wrap_threshold_bracket (p : ℤ) (hp5 : 5 ≤ p) (hpo : Odd p) :
    ∃! T : ℕ, 2 < T ∧
      (∀ t : ℕ, 2 ≤ t → t < T →
        (original_return_pair p t).2 < (original_return_pair p t).1) ∧
      (original_return_pair p T).1 ≤ (original_return_pair p T).2 ∧
      (∀ t : ℕ, T < t →
        (original_return_pair p t).1 < (original_return_pair p t).2) ∧
      alpha*(p : ℝ)+1/6-1/(6*(p : ℝ)) < (T : ℝ) ∧
      (T : ℤ) ≤ Int.ceil (alpha*(p : ℝ)+1/6-1/(25*(p : ℝ))) := by
  obtain ⟨T, hT, huniq⟩ := actual_odd_wrap_single_crossing p (by omega) hpo
  have hb := original_threshold_bounds p hp5 hpo T hT
  refine ⟨T, ⟨hT.1, hT.2.1, hT.2.2.1, hT.2.2.2, hb.1, hb.2⟩, ?_⟩
  intro U hU
  exact huniq U ⟨hU.1, hU.2.1, hU.2.2.1, hU.2.2.2.1⟩

end D5.S3.FiniteGroups.BajnokBeattyOddWrapThresholdBracket
