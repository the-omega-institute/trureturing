/- GID: D5/S3/FiniteGroups/BajnokBeattySquareDisplacementLogTwoBracket
   generality: I
   mirror-B: D5/B/S3/FiniteGroups/BajnokBeattySquareDisplacementLogTwoBracket
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: The actual all-odd square-displacement threshold lies strictly above its log-two coordinate and below the log-two ceiling. -/

/- Reuse the FourthEnvelope finite-log data and ScaleEnvelope.
Consumed unchanged-proof visibility: ThresholdBracket.state_data and
binomial_signs, FourthEnvelope.weighted_moments, FourthCoefficient.quartic_tail.
ThresholdBracket.scalar_coordinates is the shared coordinate bridge. No private Model
or finite-product implementation is reproduced. Source binding: issue 25856.
-/
import D5.S3.FiniteGroups.BajnokBeattySquareDisplacementScaleEnvelope
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
namespace D5.S3.FiniteGroups.BajnokBeattySquareDisplacementLogTwoBracket
open BajnokBeattySquareDisplacementSingleCrossing
open BajnokBeattyOddWrapGaussianUpperEnvelope

private def centered (P Q t : ℝ) : ℝ := t-1/(2*Q)+1/(2*Q*P)
private def kap (Q : ℝ) : ℝ := (Q^2-1)/(4*Q)
private def parameter (P Q t : ℝ) : ℝ := kap Q*P/centered P Q t
private def H (v s : ℝ) : ℝ :=
  (2*(v+1)/(3*(v-1)^2))*s^3*(Real.exp s-v^2*Real.exp (-v*s))
private def K (v s : ℝ) : ℝ :=
  -(4/(3*(v-1)^2))*s^3*(Real.exp s-v*Real.exp (-v*s))+
  (16*(v^2+v+1)/(15*(v-1)^4))*s^5*(Real.exp s-v^3*Real.exp (-v*s))+
  ((2*(v+1)/(3*(v-1)^2))^2/2)*s^6*(Real.exp s+v^4*Real.exp (-v*s))
private def remainder (v : ℝ) : ℝ :=
  17/(v-1)^3+(8*v+27*v^2/100+4*v^3/375)*Real.exp (-2*v/3)

private theorem log_two_bounds : (2/3 : ℝ) < Real.log 2 ∧ Real.log 2 < 7/10 := by
  constructor
  · linarith only [Real.log_two_gt_d9]
  · linarith only [Real.log_two_lt_d9]

/-- The shared moments, including the quartic tail, on the whole ray. -/
private theorem moments {v s : ℝ} (hv : 9 ≤ v) (hs : 2/3 ≤ s) :
    v*Real.exp (-v*s) ≤ 9/400 ∧ v^2*Real.exp (-v*s) ≤ 81/400 ∧
    v^3*Real.exp (-v*s) ≤ 729/400 ∧ v^4*Real.exp (-v*s) ≤ 6561/400 := by
  have h₁ := BajnokBeattySquareDisplacementFourthEnvelope.weighted_moments hv hs 1
    (by norm_num) (by norm_num)
  have h₂ := BajnokBeattySquareDisplacementFourthEnvelope.weighted_moments hv hs 2
    (by norm_num) (by norm_num)
  have h₃ := BajnokBeattySquareDisplacementFourthEnvelope.weighted_moments hv hs 3
    (by norm_num) (by norm_num)
  have hv0 : 0 ≤ v := by linarith only [hv]
  have he : Real.exp (-v*s) ≤ Real.exp (-2*v/3) := by
    apply Real.exp_le_exp.mpr
    nlinarith only [mul_nonneg hv0 (sub_nonneg.mpr hs)]
  have h₄ := (mul_le_mul_of_nonneg_left he (pow_nonneg hv0 4)).trans
    (BajnokBeattySquareDisplacementFourthCoefficient.quartic_tail hv).le
  norm_num at h₁ h₂ h₃
  exact ⟨by simpa only [neg_mul] using h₁,
    by simpa only [neg_mul] using h₂,
    by simpa only [neg_mul] using h₃,h₄⟩

/-- Scalar rational certificates; no binomial products occur here. -/
private theorem coefficients {v : ℝ} (hv : 9 ≤ v) :
    let N := v-1
    let C := 2*(v+1)/(3*N^2)
    let B := 16*(v^2+v+1)/(15*N^4)
    0 ≤ C ∧ C ≤ 5/(6*N) ∧ 0 ≤ B ∧ B ≤ 91/(60*N^2) := by
  dsimp only
  have hN : 0 < v-1 := by linarith only [hv]
  have hv0 : 0 ≤ v := by linarith only [hv]
  refine ⟨by positivity,?_,by positivity,?_⟩
  · apply (div_le_div_iff₀ (by positivity : 0 < 3*(v-1)^2)
      (by positivity : 0 < 6*(v-1))).2
    have hh := mul_nonneg hN.le (sub_nonneg.mpr hv)
    nlinarith only [hh]
  · apply (div_le_div_iff₀ (by positivity : 0 < 15*(v-1)^4)
      (by positivity : 0 < 60*(v-1)^2)).2
    have hh : 0 ≤ (v-1)^2*((v-9)*(9*v-1)) := by
      have h₁ : 0 ≤ v-9 := sub_nonneg.mpr hv
      have h₂ : 0 ≤ 9*v-1 := by linarith only [hv]
      positivity
    nlinarith only [hh]

private theorem abs_sub_bound {a b A B : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : a ≤ A) (hB : b ≤ B) : |a-b| ≤ A+B := by
  apply abs_le.mpr
  constructor <;> linarith only [ha,hb,hA,hB]

/-- The exact fourth-order coefficients retain their powers of N. -/
private theorem coefficient_estimates {v s : ℝ} (hv : 9 ≤ v)
    (hslo : 2/3 ≤ s) (hshi : s ≤ 5/7) :
    let N := v-1
    0 ≤ H v s ∧ H v s ≤ (1875/2744)/N ∧
      |K v s| ≤ (46876315/15059072)/N^2 := by
  dsimp only
  let N := v-1
  let C := 2*(v+1)/(3*N^2)
  let E := 4/(3*N^2)
  let B := 16*(v^2+v+1)/(15*N^4)
  have hN : 0 < N := by dsimp [N]; linarith only [hv]
  have hv0 : 0 ≤ v := by linarith only [hv]
  have hs0 : 0 ≤ s := by linarith only [hslo]
  obtain ⟨hC0,hC,hB0,hB⟩ := coefficients hv
  change 0 ≤ C at hC0
  change C ≤ 5/(6*N) at hC
  change 0 ≤ B at hB0
  change B ≤ 91/(60*N^2) at hB
  have hE0 : 0 ≤ E := by dsimp [E]; positivity
  obtain ⟨h₁,h₂,h₃,h₄⟩ := moments hv hslo
  have hexp : Real.exp s ≤ 9/4 :=
    (Real.exp_le_exp.mpr (by linarith only [hshi] : s ≤ 3/4)).trans exp_three_quarters_lt.le
  have hexp1 : 1 ≤ Real.exp s := by linarith only [Real.add_one_le_exp s,hs0]
  have hneg : 0 ≤ Real.exp (-v*s) := (Real.exp_pos _).le
  have hdiff0 : 0 ≤ Real.exp s-v^2*Real.exp (-v*s) := by
    linarith only [hexp1,h₂]
  have hs3 := pow_le_pow_left₀ hs0 hshi 3
  have hs5 := pow_le_pow_left₀ hs0 hshi 5
  have hs6 := pow_le_pow_left₀ hs0 hshi 6
  have hCs : C*s^3 ≤ (5/(6*N))*(5/7)^3 :=
    mul_le_mul hC hs3 (pow_nonneg hs0 3) (by positivity)
  have hH : H v s ≤ (1875/2744)/N := by
    have hdrop : H v s ≤ C*s^3*Real.exp s := by
      change C*s^3*(Real.exp s-v^2*Real.exp (-v*s)) ≤ _
      have hh := mul_nonneg (show 0 ≤ C*s^3 by positivity)
        (show 0 ≤ v^2*Real.exp (-v*s) by positivity)
      nlinarith only [hh]
    have hh := mul_le_mul hCs hexp (Real.exp_pos s).le (by positivity)
    apply hdrop.trans
    convert hh using 1 <;> field_simp [hN.ne'] <;> ring
  have hH0 : 0 ≤ H v s := by change 0 ≤ C*s^3*(Real.exp s-v^2*Real.exp (-v*s)); positivity
  have hd₁ : |Real.exp s-v*Real.exp (-v*s)| ≤ 9/4+9/400 :=
    abs_sub_bound (Real.exp_pos s).le (by positivity) hexp h₁
  have hd₃ : |Real.exp s-v^3*Real.exp (-v*s)| ≤ 9/4+729/400 :=
    abs_sub_bound (Real.exp_pos s).le (by positivity) hexp h₃
  have hd₄ : Real.exp s+v^4*Real.exp (-v*s) ≤ 9/4+6561/400 := add_le_add hexp h₄
  have hEs : E*s^3 ≤ (4/(3*N^2))*(5/7)^3 :=
    mul_le_mul_of_nonneg_left hs3 hE0
  have hBs : B*s^5 ≤ (91/(60*N^2))*(5/7)^5 :=
    mul_le_mul hB hs5 (pow_nonneg hs0 5) (by positivity)
  have hC2 : C^2/2 ≤ (25/72)/N^2 := by
    have hh := pow_le_pow_left₀ hC0 hC 2
    have hh' := div_le_div_of_nonneg_right hh (by norm_num : (0:ℝ) ≤ 2)
    convert hh' using 1 <;> field_simp [hN.ne'] <;> ring
  have hC6 : (C^2/2)*s^6 ≤ ((25/72)/N^2)*(5/7)^6 :=
    mul_le_mul hC2 hs6 (pow_nonneg hs0 6) (by positivity)
  have hk₁ : E*s^3*|Real.exp s-v*Real.exp (-v*s)| ≤
      ((4/3:ℝ)*(5/7)^3*(9/4+9/400))/N^2 := by
    have hh := mul_le_mul hEs hd₁ (abs_nonneg _) (by positivity)
    convert hh using 1 <;> field_simp [hN.ne'] <;> ring
  have hk₃ : B*s^5*|Real.exp s-v^3*Real.exp (-v*s)| ≤
      ((91/60:ℝ)*(5/7)^5*(9/4+729/400))/N^2 := by
    have hh := mul_le_mul hBs hd₃ (abs_nonneg _) (by positivity)
    convert hh using 1 <;> field_simp [hN.ne'] <;> ring
  have hk₄ : (C^2/2)*s^6*(Real.exp s+v^4*Real.exp (-v*s)) ≤
      ((25/72:ℝ)*(5/7)^6*(9/4+6561/400))/N^2 := by
    have hh := mul_le_mul hC6 hd₄ (by positivity) (by positivity)
    convert hh using 1 <;> field_simp [hN.ne'] <;> ring
  have htriangle : |K v s| ≤ E*s^3*|Real.exp s-v*Real.exp (-v*s)|+
      B*s^5*|Real.exp s-v^3*Real.exp (-v*s)|+
      (C^2/2)*s^6*(Real.exp s+v^4*Real.exp (-v*s)) := by
    change |-E*s^3*(Real.exp s-v*Real.exp (-v*s))+
      B*s^5*(Real.exp s-v^3*Real.exp (-v*s))+
      (C^2/2)*s^6*(Real.exp s+v^4*Real.exp (-v*s))| ≤ _
    have hh : |-E*s^3*(Real.exp s-v*Real.exp (-v*s))+
        B*s^5*(Real.exp s-v^3*Real.exp (-v*s))+
        (C^2/2)*s^6*(Real.exp s+v^4*Real.exp (-v*s))| ≤
        |-E*s^3*(Real.exp s-v*Real.exp (-v*s))|+
        |B*s^5*(Real.exp s-v^3*Real.exp (-v*s))|+
        |(C^2/2)*s^6*(Real.exp s+v^4*Real.exp (-v*s))| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    simpa only [abs_mul,abs_neg,abs_of_nonneg hE0,abs_of_nonneg hB0,
        abs_of_nonneg (pow_nonneg hs0 3),abs_of_nonneg (pow_nonneg hs0 5),
        abs_of_nonneg (pow_nonneg hs0 6),
        abs_of_nonneg (show 0 ≤ C^2/2 by positivity),
        abs_of_nonneg (show 0 ≤ Real.exp s+v^4*Real.exp (-v*s) by positivity)] using hh
  refine ⟨hH0,hH,htriangle.trans ?_⟩
  have hh := add_le_add (add_le_add hk₁ hk₃) hk₄
  change _ ≤ (46876315/15059072)/N^2
  convert hh using 1 <;> ring

/-- The negative exponential and the damped sixth-order remainder. -/
private theorem tail_estimates {v s : ℝ} (hv : 9 ≤ v) (hs : 2/3 ≤ s) :
    Real.exp (-v*s) ≤ (9/400)/(v-1) ∧
      remainder v ≤ (17/64+457407/200000)/(v-1) := by
  let N := v-1
  have hN8 : 8 ≤ N := by dsimp [N]; linarith only [hv]
  have hN : 0 < N := by linarith only [hN8]
  have hv0 : 0 ≤ v := by linarith only [hv]
  have hNv : N ≤ v := by dsimp [N]; linarith
  have hneg := (moments hv hs).1
  have hNz : N*Real.exp (-v*s) ≤ 9/400 :=
    (mul_le_mul_of_nonneg_right hNv (Real.exp_pos _).le).trans hneg
  have hm := moments hv (show (2/3:ℝ) ≤ 2/3 by rfl)
  have heq : -v*(2/3:ℝ) = -2*v/3 := by ring
  rw [heq] at hm
  have hpoly0 : 0 ≤ 8*v+27*v^2/100+4*v^3/375 := by positivity
  have hweighted : N*((8*v+27*v^2/100+4*v^3/375)*Real.exp (-2*v/3)) ≤
      457407/200000 := by
    have hh := mul_le_mul_of_nonneg_right hNv
      (show 0 ≤ (8*v+27*v^2/100+4*v^3/375)*Real.exp (-2*v/3) by positivity)
    have hsum : v*((8*v+27*v^2/100+4*v^3/375)*Real.exp (-2*v/3)) ≤
        457407/200000 := by
      have h₂ := mul_le_mul_of_nonneg_left hm.2.1 (by norm_num : (0:ℝ) ≤ 8)
      have h₃ := mul_le_mul_of_nonneg_left hm.2.2.1 (by norm_num : (0:ℝ) ≤ 27/100)
      have h₄ := mul_le_mul_of_nonneg_left hm.2.2.2 (by norm_num : (0:ℝ) ≤ 4/375)
      nlinarith only [h₂,h₃,h₄]
    exact hh.trans hsum
  have hN2 : (64:ℝ) ≤ N^2 := by nlinarith only [hN8,sq_nonneg (N-8)]
  have hfirst : 17/N^3 ≤ (17/64)/N := by
    apply (div_le_div_iff₀ (by positivity : 0 < N^3) hN).2
    have hh := mul_le_mul_of_nonneg_left hN2 (show 0 ≤ N by positivity)
    nlinarith only [hh]
  have hsecond : (8*v+27*v^2/100+4*v^3/375)*Real.exp (-2*v/3) ≤
      (457407/200000)/N := (le_div_iff₀ hN).2 (by nlinarith only [hweighted])
  constructor
  · exact (le_div_iff₀ hN).2 (by nlinarith only [hNz])
  · change 17/N^3+(8*v+27*v^2/100+4*v^3/375)*Real.exp (-2*v/3) ≤ _
    exact (add_le_add hfirst hsecond).trans_eq (by ring)

/-- Pure scalar consumption of the completed ScaleEnvelope inequality. -/
private theorem ratio_upper {P v s R : ℝ} (hP5 : 5 ≤ P) (hv : 9 ≤ v)
    (hslo : 2/3 ≤ s) (hshi : s ≤ 5/7)
    (hE : |R-(Real.exp s+Real.exp (-v*s))-H v s/P^2-K v s/P^4| ≤
      remainder v/P^6) : R-Real.exp s ≤ 1/(10*(v-1)) := by
  let N := v-1
  have hP : 0 < P := by linarith only [hP5]
  have hN8 : 8 ≤ N := by dsimp [N]; linarith only [hv]
  have hN : 0 < N := by linarith only [hN8]
  have hp2 : (25:ℝ) ≤ P^2 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 5) hP5 2
    norm_num at hh; exact hh
  have hp4 : (625:ℝ) ≤ P^4 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 5) hP5 4
    norm_num at hh; exact hh
  have hp6 : (15625:ℝ) ≤ P^6 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 5) hP5 6
    norm_num at hh; exact hh
  obtain ⟨_,hH,hK⟩ := coefficient_estimates hv hslo hshi
  obtain ⟨hz,hr⟩ := tail_estimates hv hslo
  have hHt : H v s/P^2 ≤ ((1875/2744)/25)/N := by
    apply (div_le_div_of_nonneg_right hH (pow_nonneg hP.le 2)).trans
    have hh := div_le_div_of_nonneg_left (show 0 ≤ (1875/2744:ℝ)/N by positivity)
      (by norm_num : (0:ℝ) < 25) hp2
    convert hh using 1 <;> ring
  have hKt : K v s/P^4 ≤ ((46876315/15059072)/(8*625))/N := by
    have hh₁ := (div_le_div_of_nonneg_right (le_abs_self (K v s)) (pow_nonneg hP.le 4)).trans
      (div_le_div_of_nonneg_right hK (pow_nonneg hP.le 4))
    have hh₂ := div_le_div_of_nonneg_left
      (show 0 ≤ (46876315/15059072:ℝ)/N^2 by positivity)
      (by norm_num : (0:ℝ) < 625) hp4
    have hh₃ : ((46876315/15059072:ℝ)/N^2)/625 ≤
        ((46876315/15059072)/(8*625))/N := by
      apply (le_div_iff₀ hN).2
      have hrecip : 1/N ≤ (1/8:ℝ) := (div_le_iff₀ hN).2 (by linarith only [hN8])
      have hm := mul_le_mul_of_nonneg_left hrecip
        (by norm_num : (0:ℝ) ≤ (46876315/15059072)/625)
      convert hm using 1 <;> field_simp [hN.ne'] <;> ring
    exact (hh₁.trans hh₂).trans hh₃
  have hRt : remainder v/P^6 ≤ ((17/64+457407/200000)/15625)/N := by
    apply (div_le_div_of_nonneg_right hr (pow_nonneg hP.le 6)).trans
    have hh := div_le_div_of_nonneg_left
      (show 0 ≤ (17/64+457407/200000:ℝ)/N by positivity)
      (by norm_num : (0:ℝ) < 15625) hp6
    convert hh using 1 <;> ring
  have hnum : (9/400:ℝ)+(1875/2744)/25+(46876315/15059072)/(8*625)+
      (17/64+457407/200000)/15625 = 297759604377663/5882450000000000 := by norm_num
  have htotal : R-Real.exp s ≤ (297759604377663/5882450000000000)/N := by
    have hh := (abs_le.mp hE).2
    have hid : (9/400:ℝ)/N+((1875/2744)/25)/N+
        ((46876315/15059072)/(8*625))/N+((17/64+457407/200000)/15625)/N =
        (297759604377663/5882450000000000)/N := by
      calc
        _ = ((9/400:ℝ)+(1875/2744)/25+(46876315/15059072)/(8*625)+
          (17/64+457407/200000)/15625)/N := by ring
        _ = _ := by rw [hnum]
    linarith only [hh,hHt,hKt,hRt,hz,hid]
  apply htotal.trans
  apply (div_le_div_iff₀ hN (by positivity : 0 < 10*N)).2
  nlinarith only [hN.le]

/-- Actual quotient counts, with the shared finite log and existing outside-band signs. -/
private theorem actual_estimates (p q : ℤ) (t : ℕ)
    (hp5 : 5 ≤ p) (hpo : Odd p) (hq3 : 3 ≤ q) (hqo : Odd q)
    (ht : ((q+1)/2).toNat ≤ t) :
    let s := parameter p q t
    0 < centered p q t ∧ 0 < ((square_return_pair p q t).2 : ℝ) ∧
    (5/7 < s → (square_return_pair p q t).2 < (square_return_pair p q t).1) ∧
    (2/5 ≤ s → s ≤ 2/3 → (square_return_pair p q t).1 < (square_return_pair p q t).2) ∧
    (2/3 ≤ s → s ≤ 5/7 →
      0 < 2*((square_return_pair p q t).1 : ℝ)/((square_return_pair p q t).2 : ℝ)-Real.exp s ∧
      2*((square_return_pair p q t).1 : ℝ)/((square_return_pair p q t).2 : ℝ)-Real.exp s ≤
        1/(10*((q : ℝ)^2-1))) ∧
    (t ≤ ((q*p+1)/2).toNat → 2/5 < s) := by
  dsimp only
  obtain ⟨n,a,r,hN,hna,hr,hfit,hWa,hWq⟩ :=
    BajnokBeattySquareDisplacementThresholdBracket.state_data p q t hp5 hpo hq3 hqo ht
  have hp : (0:ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hq : (0:ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hpN : 5 ≤ p.toNat := by omega
  have hqN : 3 ≤ q.toNat := by omega
  have hPn : (p.toNat : ℝ) = (p : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (show 0 ≤ p by omega)
  have hQn : (q.toNat : ℝ) = (q : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (show 0 ≤ q by omega)
  have hNR : (n : ℝ) = (p : ℝ)*(2*(q : ℝ)*(t : ℝ)-1) := by exact_mod_cast hN
  obtain ⟨hv,hlate⟩ :=
    BajnokBeattySquareDisplacementThresholdBracket.scalar_coordinates p q t hp5 hpo hq3 hqo ht
  change 0 < centered p q t at hv
  change (t ≤ ((q*p+1)/2).toNat → 2/5 < parameter p q t) at hlate
  have hR : (n : ℝ)+1 = 2*(q : ℝ)*(p : ℝ)*centered p q t := by
    rw [hNR]; dsimp [centered]; field_simp [hp.ne',hq.ne'] <;> ring
  have hs : parameter p q t = (((q : ℝ)^2-1)*(p : ℝ)^2)/(2*((n : ℝ)+1)) := by
    rw [hR]; dsimp [parameter,kap]; field_simp [hp.ne',hq.ne',hv.ne'] <;> ring
  obtain ⟨hB,hhi,hlo⟩ := BajnokBeattySquareDisplacementThresholdBracket.binomial_signs
    p.toNat q.toNat n a r hpN hqN hr hna hfit
  rw [hPn,hQn,← hs] at hhi hlo
  have hW : (0:ℝ) < (square_return_pair p q t).2 := by rw [hWq]; push_cast; positivity
  refine ⟨hv,hW,?_,?_,?_,hlate⟩
  · intro h
    have hh := hhi h
    have hhN : 2*Nat.choose n (a+r) < Nat.choose n a+Nat.choose n (a+(q.toNat+1)*r) := by
      exact_mod_cast hh
    rw [hWa,hWq]; omega
  · intro hl hu
    have hh := hlo hl hu
    have hhN : Nat.choose n a+Nat.choose n (a+(q.toNat+1)*r) < 2*Nat.choose n (a+r) := by
      exact_mod_cast hh
    rw [hWa,hWq]; omega
  · intro hl hu
    have hlogs := BajnokBeattySquareDisplacementFourthEnvelope.finite_log_data
      p.toNat q.toNat n a r hpN hqN hr hna hfit
    dsimp only at hlogs
    rw [hPn,hQn,← hs] at hlogs
    obtain ⟨Lx,Ly,rx,ry,Tx,hexpL,hexpM,hL0,_⟩ := hlogs hl hu
    have hratio : 2*((square_return_pair p q t).1 : ℝ)/((square_return_pair p q t).2 : ℝ) =
        Real.exp Lx+Real.exp (-Ly) := by
      rw [hexpL,hexpM,hWa,hWq]; push_cast
      field_simp [hB.ne'] <;> ring
    have hstrict : Real.exp (parameter p q t) <
        2*((square_return_pair p q t).1 : ℝ)/((square_return_pair p q t).2 : ℝ) := by
      have hh := Real.exp_le_exp.mpr (show parameter p q t ≤ Lx by linarith only [hL0])
      rw [hratio]; linarith only [hh,Real.exp_pos (-Ly)]
    refine ⟨sub_pos.mpr hstrict,?_⟩
    have hscale := BajnokBeattySquareDisplacementScaleEnvelope.actual_square_displacement_scale_envelope
      p q t hp5 hpo hq3 hqo ht
    dsimp only at hscale
    rw [← hNR,← hs] at hscale
    have hv9 : (9:ℝ) ≤ (q : ℝ)^2 := by
      have hh : (3:ℝ) ≤ q := by exact_mod_cast hq3
      nlinarith only [hh,sq_nonneg ((q : ℝ)-3)]
    apply ratio_upper (P := (p : ℝ)) (v := (q : ℝ)^2)
      (s := parameter p q t) (by exact_mod_cast hp5) hv9 hl hu
    simpa only [H,K,remainder] using hscale hl hu

private theorem exp_gap {L s : ℝ} (hs : 0 ≤ s) (hLs : s ≤ L) :
    L-s ≤ Real.exp L-Real.exp s := by
  have h₁ := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (L-s)) (Real.exp_pos s).le
  have h₂ : 1 ≤ Real.exp s := by linarith only [Real.add_one_le_exp s,hs]
  have h₃ := mul_le_mul_of_nonneg_right h₂ (sub_nonneg.mpr hLs)
  have hid : Real.exp s*Real.exp (L-s) = Real.exp L := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hid] at h₁
  nlinarith only [h₁,h₃]

/-- The analytic coordinate is evaluated at a real scalar, not at interpolated counts. -/
private theorem analytic_test {P Q L : ℝ} (hP5 : 5 ≤ P) (hQ3 : 3 ≤ Q)
    (hLlo : 2/3 < L) (hLhi : L < 7/10) :
    let x := P*Q/(4*L)
    0 < centered P Q x ∧ parameter P Q x < L ∧
      1/(10*(Q^2-1)) < L-parameter P Q x := by
  dsimp only
  have hP : 0 < P := by linarith only [hP5]
  have hQ : 0 < Q := by linarith only [hQ3]
  have hL : 0 < L := by linarith only [hLlo]
  let v := Q^2
  let N := v-1
  let a := 2*L*(P-1)/P^2
  let s₀ := L*N/(v-a)
  have hv : 9 ≤ v := by dsimp [v]; nlinarith only [hQ3,sq_nonneg (Q-3)]
  have hv0 : 0 < v := by linarith only [hv]
  have hN8 : 8 ≤ N := by dsimp [N]; linarith only [hv]
  have hN : 0 < N := by linarith only [hN8]
  have ha0 : 0 < a := by
    dsimp [a]
    have hPm : 0 < P-1 := by linarith only [hP5]
    positivity
  have ha : a ≤ 28/125 := by
    apply (div_le_iff₀ (by positivity : 0 < P^2)).2
    have hprod := mul_nonneg (show 0 ≤ P-5 by linarith only [hP5])
      (show 0 ≤ 4*P-5 by linarith only [hP5])
    have hLprod := mul_le_mul_of_nonneg_right hLhi.le (show 0 ≤ P-1 by linarith only [hP5])
    nlinarith only [hprod,hLprod]
  have hden : 0 < v-a := by linarith only [hv,ha]
  have hcoord : centered P Q (P*Q/(4*L)) = P*(v-a)/(4*Q*L) := by
    dsimp [centered,v,a]; field_simp [hP.ne',hQ.ne',hL.ne'] <;> ring
  have hcoord0 : 0 < centered P Q (P*Q/(4*L)) := by rw [hcoord]; positivity
  have hs₀ : parameter P Q (P*Q/(4*L)) = s₀ := by
    dsimp only [parameter,kap,s₀,N]
    rw [hcoord]
    dsimp [v]
    field_simp [hP.ne',hQ.ne',hL.ne',hden.ne'] <;> ring
  have hgap : L-s₀ = L*(1-a)/(v-a) := by
    dsimp [s₀,N]; field_simp [hden.ne'] <;> ring
  have hnum : (194/375:ℝ) ≤ L*(1-a) := by
    have hh := mul_le_mul hLlo.le (show (97/125:ℝ) ≤ 1-a by linarith only [ha])
      (by norm_num : (0:ℝ) ≤ 97/125) hL.le
    norm_num at hh; exact hh
  have hgaplo : 194/(375*v) ≤ L-s₀ := by
    rw [hgap]
    have hh₁ := div_le_div_of_nonneg_right hnum hv0.le
    have hh₂ := div_le_div_of_nonneg_left
      (show 0 ≤ L*(1-a) by nlinarith only [hnum]) hden
      (show v-a ≤ v by linarith only [ha0])
    convert hh₁.trans hh₂ using 1 <;> field_simp [hv0.ne'] <;> ring
  have hnormalized : (1552/3375:ℝ) ≤ N*(194/(375*v)) := by
    rw [← mul_div_assoc]
    apply (le_div_iff₀ (by positivity : 0 < 375*v)).2
    dsimp [N]
    nlinarith only [hv]
  have hmargin : (1/10:ℝ) < N*(L-s₀) := by
    have hh := mul_le_mul_of_nonneg_left hgaplo hN.le
    linarith only [hnormalized,hh]
  have hmargin' : 1/(10*N) < L-s₀ := by
    apply (div_lt_iff₀ (by positivity : 0 < 10*N)).2
    nlinarith only [hmargin]
  refine ⟨hcoord0,?_,?_⟩
  · rw [hs₀]
    have hh : 0 < 1/(10*N) := by positivity
    linarith only [hmargin',hh]
  · rw [hs₀]
    exact hmargin'

private theorem threshold_bounds (p q : ℤ) (hp5 : 5 ≤ p) (hpo : Odd p)
    (hq3 : 3 ≤ q) (hqo : Odd q) (T : ℕ)
    (hmin : ((q+1)/2).toNat < T)
    (hbefore : ∀ t : ℕ, ((q+1)/2).toNat ≤ t → t < T →
      (square_return_pair p q t).2 < (square_return_pair p q t).1)
    (hat : (square_return_pair p q T).1 ≤ (square_return_pair p q T).2)
    (hlate : T ≤ ((q*p+1)/2).toNat) :
    ((q : ℝ)^2-1)*(p : ℝ)/(4*(q : ℝ)*Real.log 2)+1/(2*(q : ℝ))-
      1/(2*(q : ℝ)*(p : ℝ)) < (T : ℝ) ∧
    (T : ℤ) ≤ Int.ceil ((p : ℝ)*(q : ℝ)/(4*Real.log 2)) := by
  have hp5R : (5:ℝ) ≤ p := by exact_mod_cast hp5
  have hq3R : (3:ℝ) ≤ q := by exact_mod_cast hq3
  have hp : (0:ℝ) < p := by linarith only [hp5R]
  have hq : (0:ℝ) < q := by linarith only [hq3R]
  obtain ⟨hLlo,hLhi⟩ := log_two_bounds
  have hL : 0 < Real.log 2 := by linarith only [hLlo]
  have hκ : 0 < kap (q : ℝ) := by
    have hsq : (9:ℝ) ≤ (q : ℝ)^2 := by nlinarith only [hq3R,sq_nonneg ((q : ℝ)-3)]
    dsimp [kap]
    have hsq' : 0 < (q : ℝ)^2-1 := by linarith only [hsq]
    positivity
  constructor
  · by_contra hn
    have htR : (T : ℝ) ≤ ((q : ℝ)^2-1)*(p : ℝ)/(4*(q : ℝ)*Real.log 2)+
        1/(2*(q : ℝ))-1/(2*(q : ℝ)*(p : ℝ)) := le_of_not_gt hn
    obtain ⟨hv,hW,hhigh,_,hband,_⟩ := actual_estimates p q T hp5 hpo hq3 hqo hmin.le
    have hsplit : ((q : ℝ)^2-1)*(p : ℝ)/(4*(q : ℝ)*Real.log 2) =
        kap (q : ℝ)*(p : ℝ)/Real.log 2 := by
      dsimp [kap]; field_simp [hq.ne',hL.ne'] <;> ring
    have hvle : centered p q T ≤ kap (q : ℝ)*(p : ℝ)/Real.log 2 := by
      rw [hsplit] at htR
      dsimp [centered]; linarith only [htR]
    have hsge : Real.log 2 ≤ parameter p q T := by
      apply (le_div_iff₀ hv).2
      have hh := (le_div_iff₀ hL).mp hvle
      nlinarith only [hh]
    by_cases hs : parameter p q T ≤ 5/7
    · have hslo : 2/3 ≤ parameter p q T := hLlo.le.trans hsge
      have hh := (hband hslo hs).1
      have he : (2:ℝ) ≤ Real.exp (parameter p q T) := by
        have he' := Real.exp_le_exp.mpr hsge
        simpa only [Real.exp_log (by norm_num : (0:ℝ) < 2)] using he'
      have hr : (2:ℝ) < 2*((square_return_pair p q T).1 : ℝ)/((square_return_pair p q T).2 : ℝ) := by
        linarith only [hh,he]
      have hc := (lt_div_iff₀ hW).mp hr
      have hatR : ((square_return_pair p q T).1 : ℝ) ≤ (square_return_pair p q T).2 := by exact_mod_cast hat
      linarith only [hc,hatR]
    · have hh := hhigh (lt_of_not_ge hs)
      omega
  · let x : ℝ := (p : ℝ)*(q : ℝ)/(4*Real.log 2)
    let U : ℤ := Int.ceil x
    have hminpos : 0 ≤ (q+1)/2 := Int.ediv_nonneg (by omega) (by norm_num)
    have hminZ : (((q+1)/2).toNat : ℤ) = (q+1)/2 := Int.toNat_of_nonneg hminpos
    have hmin2 : 2*((((q+1)/2).toNat : ℕ) : ℝ) = (q : ℝ)+1 := by
      have hh : 2*((((q+1)/2).toNat : ℕ) : ℤ) = q+1 := by
        rw [hminZ]; obtain ⟨e,he⟩ := hqo; omega
      exact_mod_cast hh
    have hqx : (q : ℝ) < x := by
      apply (lt_div_iff₀ (show 0 < 4*Real.log 2 by positivity)).2
      have hh := mul_pos hq (show 0 < (p : ℝ)-4*Real.log 2 by linarith only [hp5R,hLhi])
      nlinarith only [hh]
    have hbase : ((((q+1)/2).toNat : ℕ) : ℝ) < x := by
      linarith only [hqx,hmin2,hq3R]
    have hceil : x ≤ (U : ℝ) := Int.le_ceil x
    have hU0 : 0 ≤ U := by
      exact_mod_cast (show (0:ℝ) ≤ U by linarith only [hceil,hqx,hq3R])
    let u := U.toNat
    have huZ : (u : ℤ) = U := Int.toNat_of_nonneg hU0
    have huR : (u : ℝ) = (U : ℝ) := by exact_mod_cast huZ
    have hubase : ((q+1)/2).toNat ≤ u := by
      exact_mod_cast (show ((((q+1)/2).toNat : ℕ) : ℝ) ≤ u by rw [huR]; linarith only [hbase,hceil])
    suffices T ≤ u by
      change (T : ℤ) ≤ U
      rw [← huZ]
      exact_mod_cast this
    by_cases hul : ((q*p+1)/2).toNat ≤ u
    · exact hlate.trans hul
    have hult : u < ((q*p+1)/2).toNat := lt_of_not_ge hul
    obtain ⟨hv,hW,_,hcone,hband,hslow⟩ := actual_estimates p q u hp5 hpo hq3 hqo hubase
    obtain ⟨hv0,hs0,hmargin⟩ := analytic_test hp5R hq3R hLlo hLhi
    change 0 < centered p q x at hv0
    change parameter p q x < Real.log 2 at hs0
    change 1/(10*((q : ℝ)^2-1)) < Real.log 2-parameter p q x at hmargin
    have hvge : centered p q x ≤ centered p q u := by
      dsimp [centered]; rw [huR]; linarith only [hceil]
    have hsle : parameter p q u ≤ parameter p q x :=
      div_le_div_of_nonneg_left (mul_pos hκ hp).le hv0 hvge
    have hsU : parameter p q u ≤ 5/7 := by linarith only [hsle,hs0,hLhi]
    have hsign : (square_return_pair p q u).1 < (square_return_pair p q u).2 := by
      by_cases hs : 2/3 ≤ parameter p q u
      · have he := (hband hs hsU).2
        have hgap := exp_gap (L := Real.log 2) (s := parameter p q u)
          (show 0 ≤ parameter p q u by linarith only [hs])
          (show parameter p q u ≤ Real.log 2 by linarith only [hsle,hs0])
        rw [Real.exp_log (by norm_num : (0:ℝ) < 2)] at hgap
        have hr : 2*((square_return_pair p q u).1 : ℝ)/((square_return_pair p q u).2 : ℝ) < 2 := by
          linarith only [he,hgap,hmargin,hsle]
        have hc := (div_lt_iff₀ hW).mp hr
        have hcR : ((square_return_pair p q u).1 : ℝ) < (square_return_pair p q u).2 := by
          linarith only [hc]
        exact_mod_cast hcR
      · exact hcone (hslow hult.le).le (le_of_not_ge hs)
    by_contra hn
    have hh := hbefore u hubase (lt_of_not_ge hn)
    omega

/-- The complete original single-crossing predicate, with two unconditional
log-two bounds, for every signed odd p>=5 and q>=3, including composites. -/
theorem actual_square_displacement_log_two_bracket (p q : ℤ)
    (hp5 : 5 ≤ p) (hpo : Odd p) (hq3 : 3 ≤ q) (hqo : Odd q) :
    let tG : ℝ := ((q : ℝ)^2-1)*(p : ℝ)/(4*(q : ℝ)*Real.log 2)+
      1/(2*(q : ℝ))-1/(2*(q : ℝ)*(p : ℝ))
    let tmin : ℕ := ((q+1)/2).toNat
    let tlate : ℕ := ((q*p+1)/2).toNat
    ∃! T : ℕ, tmin < T ∧
      (∀ t : ℕ, tmin ≤ t → t < T → (square_return_pair p q t).2 < (square_return_pair p q t).1) ∧
      (square_return_pair p q T).1 ≤ (square_return_pair p q T).2 ∧
      (∀ t : ℕ, T < t → (square_return_pair p q t).1 < (square_return_pair p q t).2) ∧
      T ≤ tlate ∧ tG < (T : ℝ) ∧
      (T : ℤ) ≤ Int.ceil ((p : ℝ)*(q : ℝ)/(4*Real.log 2)) := by
  obtain ⟨T,hT,huniq⟩ := actual_square_displacement_single_crossing p q (by omega) hpo hq3 hqo
  obtain ⟨hmin,hbefore,hat,hafter,hlate⟩ := hT
  have hb := threshold_bounds p q hp5 hpo hq3 hqo T hmin hbefore hat hlate
  refine ⟨T,⟨hmin,hbefore,hat,hafter,hlate,hb.1,hb.2⟩,?_⟩
  intro U hU
  exact huniq U ⟨hU.1,hU.2.1,hU.2.2.1,hU.2.2.2.1,hU.2.2.2.2.1⟩

end D5.S3.FiniteGroups.BajnokBeattySquareDisplacementLogTwoBracket
