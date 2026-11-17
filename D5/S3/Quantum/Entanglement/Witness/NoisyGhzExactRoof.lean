/- GID: D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Actual noisy-GHZ exact roof and strict gaps in the original finite-ensemble semantics. -/


import D5.S3.Quantum.Entanglement.Witness.NoisyGhzExactRoof.Foundations
import D5.S3.Quantum.Entanglement.Witness.NoisyGhzExactRoof.TwoMeanBound
import D5.S3.Quantum.Entanglement.Witness.NoisyGhzExactRoof.ObservableOptimum
import D5.S3.Quantum.Entanglement.Witness.NoisyGhzExactRoof.CutStates
import D5.S3.Quantum.Entanglement.Witness.NoisyGhzExactRoof.MatrixAverages
import D5.S3.Quantum.Entanglement.Witness.NoisyGhzExactRoof.NoisyEnsembles


/-! The complete noisy-GHZ result uses the original complex matrices,
    arbitrary-cut biseparable pure states and actual finite-ensemble roof.
    Universal density bounds and attained two-mean optima are joined to full
    finite matrix reconstructions in both noise regimes. The original hatE
    conjugate supplies the single-witness optimum and its strict gaps.

    Scientific source: Haobo Ma, then Wenlin Zhang; CC BY 4.0. The scalar and
    multiple-observable antecedents of Xu et al. are retained. No priority
    claim is made. The released phase wording is resolved by characters on
    independent (Fin d → ZMod 3) coordinates, with no scalar-difference
    shortcut. The literal all-real-slope antecedent formula is not used.
    The d=2 operator identity is preserved separately from the d≥3 roof. -/

open scoped BigOperators ComplexOrder MatrixOrder
open _root_.Matrix
open D5.S3.Quantum.PureState.PureStateHandshake (rankOneDensity)
open D5.S3.Quantum.Entanglement.OccupancyWordSectors (Word)
open D5.S3.Quantum.Information.MultiEntropyPositivityRefutation (IsUnitState)
open D5.S3.Quantum.Recovery.ProductPrefixRigidity (readout)
open D5.S3.Quantum.Entanglement.Witness.NoisyGhzWitnessBoundGap

namespace D5.S3.Quantum.Entanglement.Witness.NoisyGhzExactRoof

noncomputable section

/-- The complete all-parameter noisy-GHZ convex roof in the original finite
matrix-ensemble semantics, obtained by the two explicit finite regimes. -/
theorem noisy_exact_roof {n d : ℕ} (hn : 3 ≤ n) (hd : 3 ≤ d)
    {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    geometricMeasure (noisyGhz n d p) = twoMeanOptimum d (noisyF n d p) (noisyY n d p) ∧
      geometricMeasure (noisyGhz n d p) =
        (max (Real.sqrt ((d-1 : ℝ)*(1-p+p/(wordCount n d : ℝ)))-
          Real.sqrt (p*(supportRank n d-1 : ℝ)/(wordCount n d : ℝ))) 0)^2/d := by
  have he : geometricMeasure (noisyGhz n d p) = twoMeanOptimum d (noisyF n d p) (noisyY n d p) := by
    by_cases h : p ≤ witnessZeroProbability n d
    · exact (low_noise_attainment hn hd hp h).2.2.2.2.2
    · rw [(high_noise_attainment hn hd (le_of_not_ge h) hp1).2.2.2.2,noisy_optimum_zero hn hd (le_of_not_ge h)]
  refine ⟨he,?_⟩
  obtain ⟨hf,hfy,_,_⟩ := noisy_triangle hn hd hp hp1
  rw [he,twoMeanOptimum_max (by omega : 2 ≤ d) hf hfy]
  congr 4
  unfold noisyY noisyF
  ring

def starDenominator (d : ℕ) : ℝ := (d : ℝ)^2-3*d+3
def starProbability (n d : ℕ) : ℝ := (d-2 : ℝ)^2/(starDenominator d*witnessSlope n d)
def starWitness (d : ℕ) : ℝ := -(2*d-3 : ℝ)/((d : ℝ)*starDenominator d)
def starValue (d : ℕ) : ℝ := 1/((d-1 : ℝ)^3+1)

private lemma star_value_formula (d : ℕ) : starValue d = 1/((d : ℝ)*starDenominator d) := by
  unfold starValue starDenominator
  congr 1
  ring

private lemma star_denominator_pos {d : ℕ} (hd : 3 ≤ d) : 0 < starDenominator d := by
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have h : starDenominator d = (d-1 : ℝ)*(d-2 : ℝ)+1 := by unfold starDenominator; ring
  rw [h]
  exact add_pos_of_nonneg_of_pos (mul_nonneg (by linarith) (by linarith)) (by norm_num)

/-- Exact source noise threshold, including strict physical probability bounds. -/
theorem witness_threshold_formula {n d : ℕ} (hn : 3 ≤ n) (hd : 3 ≤ d) :
    witnessZeroProbability n d = (wordCount n d : ℝ)*(d-1 : ℝ)/
      ((wordCount n d : ℝ)*(d-1 : ℝ)+supportRank n d-d) ∧
      0 < witnessZeroProbability n d ∧ witnessZeroProbability n d < 1 := by
  obtain ⟨hM,hR,hRM,hk,hpW0,hpW1⟩ := noisy_parameter_data hn hd
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (d : ℝ) ≠ 0 := by linarith
  have hden : 0 < (wordCount n d : ℝ)*(d-1 : ℝ)+supportRank n d-d := by
    have hpos := mul_pos hM (show 0 < (d-1 : ℝ) by linarith)
    linarith
  refine ⟨?_,hpW0,hpW1⟩
  unfold witnessZeroProbability witnessSlope
  field_simp
  <;> ring

private lemma star_probability_bounds {n d : ℕ} (hn : 3 ≤ n) (hd : 3 ≤ d) :
    0 < starProbability n d ∧ starProbability n d < witnessZeroProbability n d := by
  obtain ⟨hM,hR,hRM,hk,hpW0,hpW1⟩ := noisy_parameter_data hn hd
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith
  have hT := star_denominator_pos hd
  have hpoly : (d : ℝ)*(d-2 : ℝ)^2 < (d-1 : ℝ)*starDenominator d := by
    unfold starDenominator
    nlinarith
  refine ⟨div_pos (sq_pos_of_pos (by linarith)) (mul_pos hT hk),?_⟩
  unfold starProbability witnessZeroProbability
  have he : ((d-1 : ℝ)/d)/witnessSlope n d = (d-1 : ℝ)/(d*witnessSlope n d) := by field_simp
  rw [he]
  apply (div_lt_div_iff₀ (mul_pos hT hk) (mul_pos hdpos hk)).mpr
  have h := mul_lt_mul_of_pos_right hpoly hk
  nlinarith

private lemma star_witness_value {n d : ℕ} (hn : 3 ≤ n) (hd : 3 ≤ d) :
    witnessValue n d (starProbability n d) = starWitness d := by
  obtain ⟨hM,hR,hRM,hk,_,_⟩ := noisy_parameter_data hn hd
  have hT := star_denominator_pos hd
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  rw [witness_value_affine (by omega) (by omega)]
  unfold starProbability starWitness
  field_simp [hT.ne',hk.ne',hdpos.ne']
  unfold starDenominator
  ring

private lemma star_optimum_value {d : ℕ} (hd : 3 ≤ d) :
    twoMeanOptimum d ((d-1 : ℝ)/starDenominator d) 1 = starValue d := by
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hT := star_denominator_pos hd
  have hhigh : 1 < (d : ℝ)*((d-1 : ℝ)/starDenominator d) := by
    rw [← mul_div_assoc]
    apply (lt_div_iff₀ hT).mpr
    unfold starDenominator
    nlinarith
  have hrad : (d-1 : ℝ)*((d-1 : ℝ)/starDenominator d)*(1-(d-1 : ℝ)/starDenominator d) =
      ((d-1 : ℝ)*(d-2 : ℝ)/starDenominator d)^2 := by
    unfold starDenominator
    field_simp
    <;> ring
  have hrad0 : 0 ≤ (d-1 : ℝ)*(d-2 : ℝ)/starDenominator d :=
    div_nonneg (mul_nonneg (by linarith) (by linarith)) hT.le
  rw [twoMeanOptimum,if_neg (not_le.mpr hhigh),twoMeanValue,hrad,Real.sqrt_sq hrad0]
  rw [star_value_formula]
  field_simp [hT.ne',show (d : ℝ) ≠ 0 by linarith]
  unfold starDenominator
  ring

/-- The original single-witness conjugate has the exact source value at
the strict interior probability p_star. -/
theorem star_single_witness {n d : ℕ} (hn : 3 ≤ n) (hd : 3 ≤ d) :
    0 < starProbability n d ∧ starProbability n d < witnessZeroProbability n d ∧
      witnessZeroProbability n d < 1 ∧
      witnessValue n d (starProbability n d) = starWitness d ∧
      epsilonO n d (starProbability n d) = starValue d := by
  obtain ⟨hp,hpW⟩ := star_probability_bounds hn hd
  have hpW1 := (noisy_parameter_data hn hd).2.2.2.2.2
  refine ⟨hp,hpW,hpW1,star_witness_value hn hd,?_⟩
  have hε := noisy_witness_optimum hn hd hp.le (hpW.trans hpW1).le
  have hw := noisy_witness_means (by omega : 0 < n) (by omega : 0 < d) (starProbability n d)
  have harg : noisyF n d (starProbability n d)+(1-noisyY n d (starProbability n d))/d =
      (d-1 : ℝ)/starDenominator d := by
    rw [star_witness_value hn hd] at hw
    have he : 1/(d : ℝ)-starWitness d = (d-1 : ℝ)/starDenominator d := by
      have hT := star_denominator_pos hd
      unfold starWitness
      field_simp [hT.ne',show (d : ℝ) ≠ 0 by positivity]
      unfold starDenominator
      ring
    calc
      _ = 1/(d : ℝ)-(noisyY n d (starProbability n d)/d-noisyF n d (starProbability n d)) := by ring
      _ = 1/(d : ℝ)-starWitness d := by rw [← hw]
      _ = _ := he
  rw [harg] at hε
  exact hε.trans (star_optimum_value hd)

/-- Strict failure of the complete original single-witness optimum throughout
the open negative-witness noisy interval. -/
theorem noisy_strict_gap {n d : ℕ} (hn : 3 ≤ n) (hd : 3 ≤ d)
    {p : ℝ} (hp : 0 < p) (hpW : p < witnessZeroProbability n d) :
    epsilonO n d p < twoMeanOptimum d (noisyF n d p) (noisyY n d p) ∧
      twoMeanOptimum d (noisyF n d p) (noisyY n d p) = geometricMeasure (noisyGhz n d p) := by
  obtain ⟨hM,_,hRM,hk,_,hW1⟩ := noisy_parameter_data hn hd
  have hp1 := (hpW.trans hW1).le
  obtain ⟨hf,hfy,hy0,hy1⟩ := noisy_triangle hn hd hp.le hp1
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith
  have hy : noisyY n d p < 1 := by
    have hr := (div_lt_one hM).mpr hRM
    have hprod := mul_pos hp (sub_pos.mpr hr)
    have he : 1-noisyY n d p = p*(1-(supportRank n d : ℝ)/wordCount n d) := by
      unfold noisyY
      ring
    rw [← he] at hprod
    linarith
  have hw : witnessValue n d p < 0 := by
    rw [witness_value_affine (by omega) (by omega)]
    have h := (lt_div_iff₀ hk).mp hpW
    change p*witnessSlope n d < (d-1 : ℝ)/d at h
    rw [neg_div]
    nlinarith
  rw [noisy_witness_means (by omega) (by omega)] at hw
  have hneg : noisyY n d p < (d : ℝ)*noisyF n d p := by
    have h := (div_lt_iff₀ hdpos).mp (show noisyY n d p/d < noisyF n d p by linarith)
    linarith
  rw [noisy_witness_optimum hn hd hp.le hp1]
  exact ⟨two_mean_strict_witness_gap hd hf hfy hy hneg,(noisy_exact_roof hn hd hp.le hp1).1.symm⟩

/-- The common zero region and the noiseless endpoint retain equality;
the strict gap excludes both endpoints of its stated interval. -/
theorem noisy_gap_endpoints {n d : ℕ} (hn : 3 ≤ n) (hd : 3 ≤ d) :
    epsilonO n d 0 = geometricMeasure (noisyGhz n d 0) ∧
      ∀ p : ℝ, witnessZeroProbability n d ≤ p → p ≤ 1 →
        epsilonO n d p = 0 ∧ geometricMeasure (noisyGhz n d p) = 0 := by
  constructor
  · rw [noisy_witness_optimum hn hd (le_refl 0) (by norm_num),
      (noisy_exact_roof hn hd (le_refl 0) (by norm_num)).1]
    simp [noisyF,noisyY]
  · intro p hpW hp1
    have hp := (witness_threshold_formula hn hd).2.1.le.trans hpW
    have hz := noisy_optimum_zero hn hd hpW
    have hDF : (d : ℝ)*noisyF n d p ≤ noisyY n d p := by
      by_contra h
      obtain ⟨hf,hfy,_,_⟩ := noisy_triangle hn hd hp hp1
      have hpos := twoMeanOptimum_pos (by omega : 2 ≤ d) hf hfy (lt_of_not_ge h)
      linarith
    have hdpos : (0 : ℝ) < d := by positivity
    have he : (d : ℝ)*(noisyF n d p+(1-noisyY n d p)/d) ≤ 1 := by
      field_simp
      nlinarith
    rw [noisy_witness_optimum hn hd hp hp1]
    exact ⟨by simp [twoMeanOptimum,he],(high_noise_attainment hn hd hpW hp1).2.2.2.2⟩

/-- At p_star the universal affine certificate itself strictly exceeds the
entire original witness optimum by the source's positive Q correction. -/
theorem star_certificate_gap {n d : ℕ} (hn : 3 ≤ n) (hd : 3 ≤ d) :
    starValue d < starValue d+1/((d : ℝ)^2*(d-2 : ℝ))*starProbability n d*
        (1-(supportRank n d : ℝ)/wordCount n d) ∧
      starValue d+1/((d : ℝ)^2*(d-2 : ℝ))*starProbability n d*
        (1-(supportRank n d : ℝ)/wordCount n d) ≤
        geometricMeasure (noisyGhz n d (starProbability n d)) := by
  obtain ⟨hM,_,hRM,_,_,hW1⟩ := noisy_parameter_data hn hd
  obtain ⟨hp,hpW⟩ := star_probability_bounds hn hd
  have hp1 := (hpW.trans hW1).le
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hT := star_denominator_pos hd
  have hh : 0 < 1/((d : ℝ)^2*(d-2 : ℝ)) :=
    div_pos (by norm_num) (mul_pos (sq_pos_of_pos (by linarith)) (by linarith))
  have hq : 0 < 1-(supportRank n d : ℝ)/wordCount n d := sub_pos.mpr ((div_lt_one hM).mpr hRM)
  refine ⟨lt_add_of_pos_right _ (mul_pos (mul_pos hh hp) hq),?_⟩
  have hc := affine_certificate hn hd (noisyDensity (by omega) (by omega) (starProbability n d) hp.le hp1)
  rw [noisyDensity_matrix] at hc
  have hQ : observableMean (noisyGhz n d (starProbability n d)) (complementProjector n d) =
      starProbability n d*(1-(supportRank n d : ℝ)/wordCount n d) := by
    have h := (observable_correspondence
      (noisyDensity (n := n) (d := d) (by omega) (by omega)
        (starProbability n d) hp.le hp1)).1
    rw [noisyDensity_matrix,(noisy_means (by omega) (by omega) _).2] at h
    unfold noisyY at h
    linear_combination h
  change -(d-1 : ℝ)/(d*(d-2 : ℝ))*witnessValue n d (starProbability n d)+
    1/((d : ℝ)^2*(d-2 : ℝ))*observableMean (noisyGhz n d (starProbability n d)) (complementProjector n d)-
    1/((d : ℝ)^2*(d-2 : ℝ)) ≤ _ at hc
  rw [star_witness_value hn hd,hQ] at hc
  have he : -(d-1 : ℝ)/(d*(d-2 : ℝ))*starWitness d-1/((d : ℝ)^2*(d-2 : ℝ)) = starValue d := by
    rw [star_value_formula]
    unfold starWitness
    field_simp [hT.ne',show (d : ℝ) ≠ 0 by linarith,show (d : ℝ)-2 ≠ 0 by linarith]
    unfold starDenominator
    ring
  linarith

/-- The actual two-symbol projector has the manuscript's binomial trace.
The support bijection supplies the counting fact; arithmetic only changes its form. -/
theorem support_rank_binomial {n d : ℕ} (hn : 0 < n) (hd : 0 < d) :
    trace (supportProjector n d) = ((d+Nat.choose d 2*(2^n-2) : ℕ) : ℂ) := by
  rw [support_trace hn]
  congr 1
  have hchoose : d*(d-1) = Nat.choose d 2*2 := by
    simpa only [Nat.sub_add_cancel hd,Nat.choose_one_right] using
      Nat.add_one_mul_choose_eq (d-1) 1
  have hpow : 2^n = 2^(n-1)*2 := by
    conv_lhs => rw [← Nat.sub_add_cancel hn]
    rw [pow_succ]
  have hpos : 1 ≤ 2^(n-1) := Nat.one_le_pow _ _ (by norm_num)
  have hsub : 2^n-2 = 2*(2^(n-1)-1) := by omega
  unfold supportRank cutCount
  calc
    _ = d+(2^(n-1)-1)*(d*(d-1)) := by ring
    _ = d+(2^(n-1)-1)*(Nat.choose d 2*2) := by rw [hchoose]
    _ = d+Nat.choose d 2*(2*(2^(n-1)-1)) := by ring
    _ = _ := by rw [← hsub]


end
end D5.S3.Quantum.Entanglement.Witness.NoisyGhzExactRoof
