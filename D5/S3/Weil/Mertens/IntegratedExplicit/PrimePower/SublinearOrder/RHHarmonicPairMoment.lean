/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHHarmonicPairMoment
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHHarmonicPairMoment
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Separated positive zero bands control the harmonic weighted pair fourth moment ratio. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.RHRootWeightedSine
import D5.S3.Fourier.Asymptotics.FinitePairGaussianLimit

/-! The actual positive zero counting asymptotic gives a lower bound on the variance. -/

open Finset Filter
open scoped Topology
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder
open D5.S3.Weil.ZeroData.ZetaOrdinatePhaseStiffness (PositiveZetaZero ordinate)
open D5.S3.Weil.ZeroData.PositiveOrdinateSpectrum
open D5.S3.Analytic.Oscillation.OrdinateCounting
open D5.S3.Fourier.Asymptotics.FinitePairGaussianLimit

noncomputable section

namespace D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.RHHarmonicPairMoment

theorem weight_nonneg (j : PositiveZetaZero) : 0 ≤ harmonicWeight j := by
  have hp : 0 < ordinate j := j.property.2
  unfold harmonicWeight
  positivity

theorem cutoff_mem (rh : RiemannHypothesis) (T : ℝ) (j : PositiveZetaZero) :
    j ∈ positiveCutoff rh T ↔ ordinate j ≤ T := by
  simp [positiveCutoff,Spectrum.cut,zetaSpectrum,ordinate]

theorem cutoff_mono (rh : RiemannHypothesis) {T U : ℝ} (h : T ≤ U) :
    positiveCutoff rh T ⊆ positiveCutoff rh U := fun j hj =>
  (cutoff_mem rh U j).mpr (((cutoff_mem rh T j).mp hj).trans h)

private theorem upper_weight (rh : RiemannHypothesis) {T : ℝ} (hT : 1 ≤ T)
    {j : PositiveZetaZero} (hj : j ∈ positiveCutoff rh T \ positiveCutoff rh (T * (3 / 4))) :
    ((zetaSpectrum rh).mult j : ℝ)/(2*T) ≤ harmonicWeight j := by
  have hi := Finset.mem_sdiff.mp hj
  have hhigh : T*(3/4) < ordinate j := lt_of_not_ge (fun h => hi.2 ((cutoff_mem rh _ _).mpr h))
  have hlo : 1/2 ≤ ordinate j := by linarith
  have hT' := (cutoff_mem rh T j).mp hi.1
  have hg : 0 < ordinate j := j.property.2
  have ht : 0 < T := by linarith
  have hratio : 1/(2*T) ≤ ordinate j/(1/4+(ordinate j)^2) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hT') hg.le,
      mul_nonneg (sub_nonneg.mpr hlo) (add_nonneg hg.le (by norm_num : (0:ℝ)≤1/2))]
  have h := mul_le_mul_of_nonneg_left hratio (Nat.cast_nonneg ((zetaSpectrum rh).mult j))
  change (Zeta23.zeroMult j.val : ℝ)*(1/(2*T)) ≤ _ at h
  unfold harmonicWeight
  convert h using 1 <;> simp [zetaSpectrum,div_eq_mul_inv,mul_assoc]

private theorem harmonic_pair_bounds (rh : RiemannHypothesis) :
    ∀ᶠ T : ℝ in atTop,
      let logHeight := Real.log
      let W := harmonicMass rh T
      let g : ↥(positiveCutoff rh T) → ℝ := fun j => ordinate j.1
      let w : ↥(positiveCutoff rh T) → ℝ := fun j => harmonicWeight j.1/W
      let P := fun k => pairMoment g w k
      0 < W ∧ (∀ j, 0 ≤ w j) ∧ (∑ j,w j=1) ∧
      (1/(2*Real.pi))*(Real.log T)^2/16 ≤ W ∧
      W ≤ (1/(2*Real.pi))*(Real.log T)^2 ∧
      T^2/(4096*logHeight T) ≤ P 2 ∧ P 4 ≤ T^2*P 2 := by
  classical
  let S := zetaSpectrum rh
  let c : ℝ := 1/(2*Real.pi)
  have hc : 0 < c := by dsimp [c]; positivity
  have hN : CountAsymptotic S := zetaSpectrum_countAsymptotic rh
  have hscaled := count_scaled_limit S hN (u := 3/4) (by norm_num)
  have hdiff : Tendsto (fun T : ℝ => (S.N T-S.N (T*(3/4)) : ℝ)/(T*Real.log T)) atTop (𝓝 (c/4)) := by
    have h := hN.sub hscaled
    convert h using 1
    · ext T; ring
    · dsimp [c]; ring
  have hmass : Tendsto (fun T : ℝ => harmonicMass rh T/(Real.log T)^2) atTop (𝓝 (c/2)) := by
    convert harmonic_mass_limit rh using 2 <;> dsimp [c] <;> ring
  have hhalf := hmass.comp (tendsto_id.atTop_mul_const (by norm_num : (0:ℝ)<1/2))
  filter_upwards [eventually_ge_atTop (4:ℝ),hdiff.eventually_const_lt (show c/8<c/4 by linarith),
    hmass.eventually_lt_const (show c/2<c by linarith),hhalf.eventually_const_lt (show c/4<c/2 by linarith)] with T hT hcount hWup hWlow
  intro logHeight W g w P
  have hT0 : 0 < T := by linarith
  have hlog : 0 < Real.log T := Real.log_pos (by linarith)
  let s := positiveCutoff rh T
  let A := positiveCutoff rh (T*(1/2))
  let B := s \ positiveCutoff rh (T*(3/4))
  let a := harmonicWeight
  have hAs : A ⊆ s := cutoff_mono rh (by linarith)
  have hBs : B ⊆ s := sdiff_subset
  have hcut : positiveCutoff rh (T*(3/4)) ⊆ s := cutoff_mono rh (by linarith)
  have hcount' : (c/8)*(T*Real.log T) ≤ (S.N T : ℝ)-(S.N (T*(3/4)) : ℝ) :=
    (lt_div_iff₀ (by positivity)).mp hcount |>.le
  let mult (j : PositiveZetaZero) : ℕ := Zeta23.zeroMult j.val
  have hsumB : (∑ j ∈ B, (mult j : ℝ)) = (S.N T : ℝ)-(S.N (T*(3/4)) : ℝ) := by
    have he := Finset.sum_sdiff hcut (f := fun j : PositiveZetaZero => (mult j : ℝ))
    have e (U : ℝ) : (∑ j ∈ positiveCutoff rh U, (mult j : ℝ)) = (S.N U : ℝ) := by
      change (∑ j ∈ positiveCutoff rh U, (mult j : ℝ)) =
        ((∑ j ∈ positiveCutoff rh U, mult j : ℕ) : ℝ)
      rw [Nat.cast_sum]
    have he' : (∑ j ∈ B,(mult j : ℝ)) + (∑ j ∈ positiveCutoff rh (T*(3/4)),(mult j : ℝ)) =
        (∑ j ∈ s,(mult j : ℝ)) := by exact he
    rw [e (T*(3/4)),show (∑ j ∈ s,(mult j : ℝ)) = (S.N T : ℝ) from e T] at he'
    linarith
  have hBmass : c*Real.log T/16 ≤ ∑ j ∈ B,a j := by
    calc
      _ = ((c/8)*(T*Real.log T))/(2*T) := by field_simp; ring
      _ ≤ (∑ j ∈ B,(mult j : ℝ))/(2*T) := by rw [hsumB]; exact div_le_div_of_nonneg_right hcount' (by positivity)
      _ = ∑ j ∈ B,(mult j : ℝ)/(2*T) := by rw [Finset.sum_div]
      _ ≤ _ := Finset.sum_le_sum fun j hj => upper_weight rh (by linarith) hj
  have hloghalf : Real.log T/2 ≤ Real.log (T*(1/2)) := by
    have hl := Real.log_le_log (by norm_num : 0 < (4:ℝ)) hT
    rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow] at hl
    rw [Real.log_mul hT0.ne' (by norm_num : (1/2:ℝ)≠0),Real.log_div (by norm_num) (by norm_num),Real.log_one,zero_sub]
    norm_num at hl
    linarith
  have hAraw : c/4*(Real.log (T*(1/2)))^2 ≤ harmonicMass rh (T*(1/2)) := by
    exact (lt_div_iff₀ (sq_pos_of_pos (by linarith : 0 < Real.log (T*(1/2))))).mp hWlow |>.le
  have hAmass : c*(Real.log T)^2/16 ≤ ∑ j ∈ A,a j := by
    have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ Real.log T/2) hloghalf 2
    have h := mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ c/4)
    calc
      _ = c/4*(Real.log T/2)^2 := by ring
      _ ≤ _ := h.trans hAraw
  have hWsum : W = ∑ j ∈ s,a j := rfl
  have hWbound : W ≤ c*(Real.log T)^2 :=
    (div_lt_iff₀ (sq_pos_of_pos hlog)).mp hWup |>.le
  have hWpos : 0 < W := by
    have hs := sum_le_sum_of_subset_of_nonneg hAs (fun j _ _ => weight_nonneg j)
    rw [← hWsum] at hs
    exact (show 0 < c*(Real.log T)^2/16 by positivity).trans_le (hAmass.trans hs)
  let aw : PositiveZetaZero → ℝ := fun j => a j/W
  have hw : ∀ j, 0 ≤ aw j := fun j => div_nonneg (weight_nonneg j) hWpos.le
  have hWnorm : (∑ j,w j)=1 := by
    change (∑ j : ↥s, aw j.1)=1
    rw [Finset.sum_coe_sort s aw]
    dsimp [aw]
    rw [← Finset.sum_div,← hWsum,div_self hWpos.ne']
  have hpairs (k : ℕ) : P k = ∑ i ∈ s, ∑ j ∈ s, aw i*aw j*(ordinate i-ordinate j)^k := by
    change (∑ i : ↥s, ∑ j : ↥s, aw i.1*aw j.1*(ordinate i.1-ordinate j.1)^k)=_
    calc
      _ = ∑ i ∈ s, ∑ j : ↥s, aw i*aw j.1*(ordinate i-ordinate j.1)^k :=
        Finset.sum_coe_sort s _
      _ = _ := sum_congr rfl fun i _ =>
        Finset.sum_coe_sort s (fun j : PositiveZetaZero => aw i*aw j*(ordinate i-ordinate j)^k)
  have hP2low : T^2/(4096*Real.log T) ≤ P 2 := by
    have hprod : (∑ i ∈ A, aw i)*(∑ j ∈ B, aw j)*(T/4)^2 ≤ P 2 := by
      rw [hpairs]
      have he : (∑ i ∈ A,aw i)*(∑ j ∈ B,aw j)*(T/4)^2 =
          ∑ i ∈ A,∑ j ∈ B,aw i*aw j*(T/4)^2 := by
        rw [sum_mul,sum_mul]
        refine sum_congr rfl fun i _ => ?_
        rw [mul_sum,sum_mul]
      rw [he]
      calc
        _ ≤ ∑ i ∈ A,∑ j ∈ B,aw i*aw j*(ordinate i-ordinate j)^2 := by
          refine sum_le_sum fun i hi => sum_le_sum fun j hj => ?_
          have hi' := (cutoff_mem rh _ _).mp hi
          have hj' : T*(3/4) < ordinate j := lt_of_not_ge fun h => (Finset.mem_sdiff.mp hj).2 ((cutoff_mem rh _ _).mpr h)
          have hgap : T/4 ≤ ordinate j-ordinate i := by linarith
          have hsq := pow_le_pow_left₀ (by positivity : 0≤T/4) hgap 2
          rw [show (ordinate j-ordinate i)^2=(ordinate i-ordinate j)^2 by ring] at hsq
          exact mul_le_mul_of_nonneg_left hsq (mul_nonneg (hw i) (hw j))
        _ ≤ _ := by
          apply (sum_le_sum fun i hi => sum_le_sum_of_subset_of_nonneg hBs (fun j _ _ => mul_nonneg (mul_nonneg (hw i) (hw j)) (sq_nonneg _))).trans
          exact sum_le_sum_of_subset_of_nonneg hAs (fun i _ _ => sum_nonneg fun j _ => mul_nonneg (mul_nonneg (hw i) (hw j)) (sq_nonneg _))
    have ha : (c*(Real.log T)^2/16)/W ≤ ∑ i ∈ A, aw i := by
      dsimp [aw]; rw [← Finset.sum_div]; exact div_le_div_of_nonneg_right hAmass hWpos.le
    have hb : (c*Real.log T/16)/W ≤ ∑ i ∈ B, aw i := by
      dsimp [aw]; rw [← Finset.sum_div]; exact div_le_div_of_nonneg_right hBmass hWpos.le
    have ha' : 1/16 ≤ ∑ i ∈ A, aw i := by
      apply le_trans _ ha
      apply (le_div_iff₀ hWpos).mpr
      linarith
    have hb' : 1/(16*Real.log T) ≤ ∑ i ∈ B, aw i := by
      apply le_trans _ hb
      apply (le_div_iff₀ hWpos).mpr
      rw [one_div,mul_comm,← div_eq_mul_inv]
      apply (div_le_iff₀ (show 0 < 16*Real.log T by positivity)).mpr
      nlinarith only [hWbound]
    calc
      _ = (1/16)*(1/(16*Real.log T))*(T/4)^2 := by field_simp; ring
      _ ≤ _ := (mul_le_mul_of_nonneg_right (mul_le_mul ha' hb' (by positivity) (sum_nonneg fun i _ => hw i)) (sq_nonneg _)).trans hprod
  have hP4 : P 4 ≤ T^2*P 2 := by
    rw [hpairs,hpairs,mul_sum]
    refine sum_le_sum fun i hi => ?_
    rw [mul_sum]
    refine sum_le_sum fun j hj => ?_
    have hi' := (cutoff_mem rh T i).mp hi
    have hj' := (cutoff_mem rh T j).mp hj
    have hip : 0 < ordinate i := i.property.2
    have hjp : 0 < ordinate j := j.property.2
    have hdiff : |ordinate i-ordinate j| ≤ T := abs_le.mpr ⟨by linarith,by linarith⟩
    have hsq : (ordinate i-ordinate j)^2 ≤ T^2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hdiff 2
    have hh := mul_le_mul_of_nonneg_left hsq (sq_nonneg (ordinate i-ordinate j))
    have hh' := mul_le_mul_of_nonneg_left hh (mul_nonneg (hw i) (hw j))
    nlinarith only [hh']
  have hWlower : c*(Real.log T)^2/16 ≤ W := hAmass.trans
    (sum_le_sum_of_subset_of_nonneg hAs (fun j _ _ => weight_nonneg j))
  exact ⟨hWpos,fun j => hw j.1,hWnorm,hWlower,hWbound,hP2low,hP4⟩

/-- For growing positive zeta cutoffs the normalized pair fourth-to-second
moment ratio is bounded by a constant times the logarithm of the height. -/
theorem harmonic_pair_ratio (rh : RiemannHypothesis) :
    ∀ᶠ T : ℝ in atTop,
      let logHeight := Real.log
      let W := harmonicMass rh T
      let g : ↥(positiveCutoff rh T) → ℝ := fun j => ordinate j.1
      let w : ↥(positiveCutoff rh T) → ℝ := fun j => harmonicWeight j.1/W
      let P := fun k => pairMoment g w k
      0 < W ∧ (∀ j, 0 ≤ w j) ∧ (∑ j,w j=1) ∧ 0 < P 2 ∧ P 4/(P 2)^2 ≤ 4096*logHeight T := by
  filter_upwards [harmonic_pair_bounds rh, eventually_gt_atTop (1:ℝ)] with T h hT
  intro logHeight W g w P
  obtain ⟨hWpos, hw, hw1, _, _, hP2low, hP4⟩ := h
  have hlog : 0 < Real.log T := Real.log_pos hT
  have hP2pos : 0 < P 2 := (show 0 < T^2/(4096*Real.log T) by positivity).trans_le hP2low
  refine ⟨hWpos,hw,hw1,hP2pos,?_⟩
  apply (div_le_iff₀ (sq_pos_of_pos hP2pos)).mpr
  have h := (div_le_iff₀ (show 0 < 4096*Real.log T by positivity)).mp hP2low
  have h' := mul_le_mul_of_nonneg_right h hP2pos.le
  exact hP4.trans (by nlinarith only [h'])

/-- A moving reciprocal-height cutoff gives a uniform score deficit on the
short noncentral time range, with the original harmonic weights. -/
theorem harmonic_reciprocal_time_deficit (rh : RiemannHypothesis) :
    ∃ L : ℝ, 1 < L ∧ ∀ T t : ℝ, L ≤ T → 1/T ≤ |t| → |t| ≤ 1/L →
      let g : ↥(positiveCutoff rh T) → ℝ := fun j => ordinate j.1
      let w : ↥(positiveCutoff rh T) → ℝ := fun j => harmonicWeight j.1 / harmonicMass rh T
      1 - ‖D5.S3.Fourier.Concentration.FiniteTailMomentMissingWindow.complexScore g w t‖
        ≥ Real.log (|t|⁻¹) / (524288 * (Real.log T)^2) := by
  classical
  obtain ⟨A, hA⟩ := eventually_atTop.1 (harmonic_pair_bounds rh)
  let L := max A 4
  have hL : 1 < L := (by norm_num : (1:ℝ)<4).trans_le (le_max_right A 4)
  refine ⟨L,hL,?_⟩
  intro T t hLT htlo hthi g w
  have hT : 1 < T := hL.trans_le hLT
  have ht : 0 < |t| := (by positivity : 0 < 1/T).trans_le htlo
  let X := |t|⁻¹
  have hXpos : 0 < X := inv_pos.mpr ht
  have hLX : L ≤ X := by
    apply (le_inv_comm₀ (by linarith) ht).mpr
    simpa only [one_div] using hthi
  have hXT : X ≤ T := by
    apply (inv_le_comm₀ ht (by linarith)).mpr
    simpa only [one_div] using htlo
  have hX : 1 < X := hL.trans_le hLX
  have hlogX : 0 < Real.log X := Real.log_pos hX
  have hlogT : 0 < Real.log T := Real.log_pos hT
  let W := harmonicMass rh
  let gU (U : ℝ) : ↥(positiveCutoff rh U) → ℝ := fun j => ordinate j.1
  let wU (U : ℝ) : ↥(positiveCutoff rh U) → ℝ := fun j => harmonicWeight j.1 / W U
  let P (U : ℝ) := pairMoment (gU U) (wU U)
  let Z (U : ℝ) := D5.S3.Fourier.Concentration.FiniteTailMomentMissingWindow.complexScore
    (gU U) (wU U) t
  obtain ⟨hWX, hwX, hwX1, hWXlow, _, hP2, hP4⟩ :=
    hA X ((le_max_left A 4).trans hLX)
  obtain ⟨hWT, _, _, _, hWTup, _, _⟩ :=
    hA T ((le_max_left A 4).trans hLT)
  change 0 < W X at hWX
  change 0 < W T at hWT
  change (∀ j, 0 ≤ wU X j) at hwX
  change (∑ j,wU X j)=1 at hwX1
  change (1/(2*Real.pi))*(Real.log X)^2/16 ≤ W X at hWXlow
  change W T ≤ (1/(2*Real.pi))*(Real.log T)^2 at hWTup
  change X^2/(4096*Real.log X) ≤ P X 2 at hP2
  change P X 4 ≤ X^2*P X 2 at hP4
  have hquart := (score_quartic (gU X) (wU X)
    (fun i j => mul_nonneg (hwX i) (hwX j)) t).2
  change ‖Z X‖^2-((∑ j,wU X j)^2-P X 2*t^2/2) ≤ P X 4*t^4/24 at hquart
  rw [hwX1,one_pow] at hquart
  have hxt : X^2*t^2 = 1 := by
    dsimp [X]
    rw [inv_pow,← sq_abs t]
    field_simp
  have hp2scale : 1/(4096*Real.log X) ≤ P X 2*t^2 := by
    have h := mul_le_mul_of_nonneg_right hP2 (sq_nonneg t)
    calc
      _ = X^2/(4096*Real.log X)*t^2 := by
        rw [div_mul_eq_mul_div,hxt]
      _ ≤ _ := h
  have hquartScale : P X 4*t^4 ≤ P X 2*t^2 := by
    calc
      _ ≤ (X^2*P X 2)*t^4 := mul_le_mul_of_nonneg_right hP4 (by positivity)
      _ = (X^2*t^2)*(P X 2*t^2) := by ring
      _ = _ := by rw [hxt,one_mul]
  have hdefX : 1/(32768*Real.log X) ≤ 1 - ‖Z X‖ := by
    have he : 1/(32768*Real.log X) = (1/(4096*Real.log X))/8 := by ring
    rw [he]
    have hp2pos : 0 ≤ P X 2*t^2 :=
      (by positivity : 0 ≤ 1/(4096*Real.log X)).trans hp2scale
    have hweak : (1/(4096*Real.log X))/4 ≤ 1-‖Z X‖^2 := by
      linarith only [hquart,hquartScale,hp2scale,hp2pos]
    nlinarith only [hweak,sq_nonneg (1-‖Z X‖)]
  let z (U : ℝ) : ℂ := ∑ j ∈ positiveCutoff rh U, (harmonicWeight j : ℂ) *
    D5.S3.Weil.DirichletPolynomialMeanSquare.phase (ordinate j) t
  have hz (U : ℝ) : Z U = z U / (W U : ℂ) := by
    unfold Z D5.S3.Fourier.Concentration.FiniteTailMomentMissingWindow.complexScore
    change (∑ j : ↥(positiveCutoff rh U), ((harmonicWeight j.1/W U : ℝ):ℂ) *
      D5.S3.Weil.DirichletPolynomialMeanSquare.phase (ordinate j.1) t) = _
    rw [Finset.sum_coe_sort (positiveCutoff rh U) (fun j =>
      ((harmonicWeight j/W U : ℝ):ℂ) *
        D5.S3.Weil.DirichletPolynomialMeanSquare.phase (ordinate j) t)]
    dsimp [z]
    simp_rw [Complex.ofReal_div, div_mul_eq_mul_div]
    rw [Finset.sum_div]
  have hnormz {U : ℝ} (hWU : 0 < W U) : ‖z U‖ = W U * ‖Z U‖ := by
    rw [hz,Complex.norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hWU]
    field_simp
  have hsub := cutoff_mono rh hXT
  let tail := positiveCutoff rh T \ positiveCutoff rh X
  let f (j : PositiveZetaZero) : ℂ := (harmonicWeight j : ℂ) *
    D5.S3.Weil.DirichletPolynomialMeanSquare.phase (ordinate j) t
  have hsplit : (∑ j ∈ tail,f j)+z X=z T := Finset.sum_sdiff hsub
  have htailMass : (∑ j ∈ tail,harmonicWeight j)+W X=W T := Finset.sum_sdiff hsub
  have htailBound : ‖∑ j ∈ tail,f j‖ ≤ ∑ j ∈ tail,harmonicWeight j := by
    apply (norm_sum_le tail f).trans
    apply sum_le_sum
    intro j hj
    simp [f, D5.S3.Weil.DirichletPolynomialMeanSquare.norm_phase,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (weight_nonneg j)]
  have hwhole : ‖z T‖ ≤ W T-W X+‖z X‖ := by
    rw [← hsplit]
    have h := norm_add_le (∑ j ∈ tail,f j) (z X)
    linarith
  rw [hnormz hWT,hnormz hWX] at hwhole
  have hhead : W X*(1 - ‖Z X‖) ≤ W T*(1 - ‖Z T‖) := by linarith
  let c : ℝ := 1/(2*Real.pi)
  have hc : 0 < c := by dsimp [c]; positivity
  change c*(Real.log X)^2/16 ≤ W X at hWXlow
  change W T ≤ c*(Real.log T)^2 at hWTup
  have hmain : c*Real.log X/524288 ≤ W T*(1 - ‖Z T‖) := by
    calc
      _ = (c*(Real.log X)^2/16)*(1/(32768*Real.log X)) := by
        field_simp; ring
      _ ≤ W X*(1 - ‖Z X‖) := mul_le_mul hWXlow hdefX (by positivity) (by positivity)
      _ ≤ _ := hhead
  have hpos : 0 ≤ 1 - ‖Z T‖ := by
    have h := (show 0 ≤ c*Real.log X/524288 by positivity).trans hmain
    exact nonneg_of_mul_nonneg_right h hWT
  have hfinal : c*Real.log X/524288 ≤ (c*(Real.log T)^2)*(1 - ‖Z T‖) :=
    hmain.trans (mul_le_mul_of_nonneg_right hWTup hpos)
  change Real.log X/(524288*(Real.log T)^2) ≤ 1 - ‖Z T‖
  apply (div_le_iff₀ (by positivity)).mpr
  apply (mul_le_mul_iff_left₀ hc).mp
  nlinarith only [hfinal]

#print axioms harmonic_reciprocal_time_deficit

#print axioms harmonic_pair_ratio

end D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.RHHarmonicPairMoment
