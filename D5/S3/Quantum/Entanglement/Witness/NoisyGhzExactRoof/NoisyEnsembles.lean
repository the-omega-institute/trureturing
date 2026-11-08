/- GID: D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/NoisyEnsembles
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/NoisyEnsembles
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Actual noisy-GHZ NoisyEnsembles in the original finite-ensemble semantics. -/


import D5.S3.Quantum.Entanglement.Witness.NoisyGhzExactRoof.Foundations
import D5.S3.Quantum.Entanglement.Witness.NoisyGhzExactRoof.TwoMeanBound
import D5.S3.Quantum.Entanglement.Witness.NoisyGhzExactRoof.ObservableOptimum
import D5.S3.Quantum.Entanglement.Witness.NoisyGhzExactRoof.CutStates
import D5.S3.Quantum.Entanglement.Witness.NoisyGhzExactRoof.MatrixAverages


open scoped BigOperators ComplexOrder MatrixOrder
open _root_.Matrix
open D5.S3.Quantum.PureState.PureStateHandshake (rankOneDensity)
open D5.S3.Quantum.Entanglement.OccupancyWordSectors (Word)
open D5.S3.Quantum.Information.MultiEntropyPositivityRefutation (IsUnitState)
open D5.S3.Quantum.Recovery.ProductPrefixRigidity (readout)
open D5.S3.Quantum.Entanglement.Witness.NoisyGhzWitnessBoundGap

namespace D5.S3.Quantum.Entanglement.Witness.NoisyGhzExactRoof

noncomputable section

private lemma at_least_three_pos {k : ℕ} (h : 3 ≤ k) : 0 < k := by omega

def noisyF (n d : ℕ) (p : ℝ) : ℝ := 1-p+p/(wordCount n d : ℝ)
def noisyY (n d : ℕ) (p : ℝ) : ℝ := 1-p+p*(supportRank n d : ℝ)/(wordCount n d : ℝ)

/-- Exact real trace readouts of the actual noisy matrix. -/
theorem noisy_means {n d : ℕ} (hn : 0 < n) (hd : 0 < d) (p : ℝ) :
    observableMean (noisyGhz n d p) (rankOneDensity (ghz n d)) = noisyF n d p ∧
      observableMean (noisyGhz n d p) (supportProjector n d) = noisyY n d p := by
  obtain ⟨_,_,hgp,hgg⟩ := projector_data hn hd
  have ht : trace (rankOneDensity (ghz n d)) = 1 := by
    rw [trace_rank_one,ghz_unit hn hd]
    rfl
  constructor
  · simp only [observableMean,noisyGhz,add_mul,Matrix.smul_mul,one_mul,trace_add,
      trace_smul,hgg,ht,Complex.real_smul,Complex.add_re,Complex.ofReal_re,mul_one]
    simp [noisyF,wordCount]
    ring
  · simp only [observableMean,noisyGhz,add_mul,Matrix.smul_mul,one_mul,trace_add,
      trace_smul,hgp,ht,support_trace hn,Complex.real_smul,Complex.add_re,
      Complex.ofReal_re,mul_one]
    simp [noisyY,wordCount, ← Complex.ofReal_pow, ← Complex.ofReal_mul]
    ring

/-- The source witness value is the exact affine trace of the noisy state. -/
theorem witness_value_affine {n d : ℕ} (hn : 0 < n) (hd : 0 < d) (p : ℝ) :
    witnessValue n d p = -(d-1 : ℝ)/d+witnessSlope n d*p := by
  have hM : (0 : ℝ) < wordCount n d := by unfold wordCount; exact_mod_cast pow_pos hd n
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  change observableMean (noisyGhz n d p) (witnessOp n d) = _
  rw [witnessOp,mean_sub,mean_smul,(noisy_means hn hd p).1,(noisy_means hn hd p).2]
  unfold noisyF noisyY witnessSlope
  field_simp
  <;> ring

lemma noisy_parameter_data {n d : ℕ} (hn : 3 ≤ n) (hd : 3 ≤ d) :
    0 < (wordCount n d : ℝ) ∧ (d : ℝ) < supportRank n d ∧
      (supportRank n d : ℝ) < wordCount n d ∧ 0 < witnessSlope n d ∧
      0 < witnessZeroProbability n d ∧ witnessZeroProbability n d < 1 := by
  obtain ⟨hR,hRM⟩ := support_rank_bounds hn hd
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hR' : (d : ℝ) < supportRank n d := by exact_mod_cast hR
  have hRM' : (supportRank n d : ℝ) < wordCount n d := by exact_mod_cast hRM
  have hM : (0 : ℝ) < wordCount n d := by linarith
  have ha : 0 < (d-1 : ℝ)/d := div_pos (by linarith) (by linarith)
  have hk : (d-1 : ℝ)/d < witnessSlope n d := by
    unfold witnessSlope
    have hq : 0 < (supportRank n d : ℝ)/d-1 := by
      apply sub_pos.mpr
      exact (lt_div_iff₀ (by linarith : (0 : ℝ) < d)).mpr (by simpa)
    exact lt_add_of_pos_right _ (div_pos hq hM)
  have hk0 : 0 < witnessSlope n d := ha.trans hk
  refine ⟨hM,hR',hRM',hk0,?_,?_⟩
  · exact div_pos ha hk0
  · exact (div_lt_one hk0).mpr hk

lemma noisy_triangle {n d : ℕ} (hn : 3 ≤ n) (hd : 3 ≤ d)
    {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ noisyF n d p ∧ noisyF n d p ≤ noisyY n d p ∧
      0 < noisyY n d p ∧ noisyY n d p ≤ 1 := by
  obtain ⟨hM,hR,hRM,_,_,_⟩ := noisy_parameter_data hn hd
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hratio : 0 < (supportRank n d : ℝ)/wordCount n d := div_pos (by linarith) hM
  have hratio1 : (supportRank n d : ℝ)/wordCount n d < 1 := (div_lt_one hM).mpr hRM
  have hF := add_nonneg (sub_nonneg.mpr hp1) (div_nonneg hp hM.le)
  have hfy : noisyY n d p-noisyF n d p = p*((supportRank n d : ℝ)-1)/wordCount n d := by
    unfold noisyF noisyY
    field_simp
    <;> ring
  have hy : noisyY n d p = (supportRank n d : ℝ)/wordCount n d+
      (1-p)*(1-(supportRank n d : ℝ)/wordCount n d) := by
    unfold noisyY
    ring
  refine ⟨hF,?_,?_,?_⟩
  · apply sub_nonneg.mp
    rw [hfy]
    exact div_nonneg (mul_nonneg hp (by linarith)) hM.le
  · rw [hy]
    exact add_pos_of_pos_of_nonneg hratio (mul_nonneg (sub_nonneg.mpr hp1) (sub_nonneg.mpr hratio1.le))
  · unfold noisyY
    have hq := mul_nonneg hp (sub_nonneg.mpr hratio1.le)
    have he : p*(1-(supportRank n d : ℝ)/wordCount n d) =
        p-p*(supportRank n d : ℝ)/wordCount n d := by ring
    rw [he] at hq
    linarith

lemma noisy_witness_means {n d : ℕ} (hn : 0 < n) (hd : 0 < d) (p : ℝ) :
    witnessValue n d p = noisyY n d p/d-noisyF n d p := by
  change observableMean (noisyGhz n d p) (witnessOp n d) = _
  rw [witnessOp,mean_sub,mean_smul,(noisy_means hn hd p).1,(noisy_means hn hd p).2]
  ring

/-- Exact original epsilonO on every physical noise probability, obtained
from the actual hatE conjugate and the actual matrix trace. -/
theorem noisy_witness_optimum {n d : ℕ} (hn : 3 ≤ n) (hd : 3 ≤ d)
    {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    epsilonO n d p = twoMeanOptimum d (noisyF n d p+(1-noisyY n d p)/d) 1 := by
  obtain ⟨hf,hfy,hy0,hy1⟩ := noisy_triangle hn hd hp hp1
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith
  have hdf := mul_le_mul_of_nonneg_left hfy hdpos.le
  have hdf0 := mul_nonneg hdpos.le hf
  have hwm := noisy_witness_means (at_least_three_pos hn) (by omega : 0 < d) p
  have hw0 : -(d-1 : ℝ)/d ≤ witnessValue n d p := by
    rw [hwm]
    apply (div_le_iff₀ hdpos).mpr
    have hy := mul_nonneg (sub_nonneg.mpr hy1) (show (0 : ℝ) ≤ d-1 by linarith)
    field_simp
    nlinarith
  have hw1 : witnessValue n d p ≤ 1/(d : ℝ) := by
    rw [hwm]
    apply (le_div_iff₀ hdpos).mpr
    field_simp
    nlinarith
  rw [epsilonO_bridge,witness_optimum hn hd hw0 hw1,hwm]
  congr 1
  ring

private lemma low_noise_ratio {n d : ℕ} (hn : 3 ≤ n) (hd : 3 ≤ d)
    {p : ℝ} (hp : 0 ≤ p) (hpW : p ≤ witnessZeroProbability n d) :
    0 < noisyY n d p ∧ 1/(d : ℝ) ≤ noisyF n d p/noisyY n d p ∧
      noisyF n d p/noisyY n d p ≤ 1 := by
  obtain ⟨hM,hR,hRM,hk,hpW0,hpW1⟩ := noisy_parameter_data hn hd
  have hp1 : p ≤ 1 := hpW.trans hpW1.le
  obtain ⟨hf,hfy,hy0,hy1⟩ := noisy_triangle hn hd hp hp1
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith
  have hw : witnessValue n d p ≤ 0 := by
    rw [witness_value_affine (by omega) (by omega)]
    have h := (le_div_iff₀ hk).mp hpW
    change p*witnessSlope n d ≤ (d-1 : ℝ)/d at h
    rw [neg_div]
    nlinarith
  rw [noisy_witness_means (by omega) (by omega)] at hw
  refine ⟨hy0,?_,(div_le_one hy0).mpr hfy⟩
  apply (div_le_div_iff₀ hdpos hy0).mpr
  have h := (div_le_iff₀ hdpos).mp (show noisyY n d p/d ≤ noisyF n d p by linarith)
  simpa only [one_mul,mul_comm] using h

lemma twoMeanOptimum_pos {d : ℕ} (hd : 2 ≤ d) {f y : ℝ}
    (hf : 0 ≤ f) (hfy : f ≤ y) (h : y < (d : ℝ) * f) :
    0 < twoMeanOptimum d f y := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hB : 0 ≤ y - f := sub_nonneg.mpr hfy
  have hA : 0 ≤ (d - 1 : ℝ) * f := mul_nonneg (by linarith) hf
  have hr : Real.sqrt (y - f) < Real.sqrt ((d - 1 : ℝ) * f) :=
    Real.sqrt_lt_sqrt hB (by nlinarith)
  rw [twoMeanOptimum_max hd hf hfy,max_eq_left (sub_nonneg.mpr hr.le)]
  exact div_pos (sq_pos_of_pos (sub_pos.mpr hr)) (by linarith)

/-- A nonzero Q-readout gives a strict advantage over the entire original
single-witness optimum whenever the witness is negative. This comparison
uses the exact radicals, with no endpoint slope assigned a singular value. -/
theorem two_mean_strict_witness_gap {d : ℕ} (hd : 3 ≤ d) {f y : ℝ}
    (hf : 0 ≤ f) (hfy : f ≤ y) (hy : y < 1) (hneg : y < (d : ℝ) * f) :
    twoMeanOptimum d (f + (1-y) / d) 1 < twoMeanOptimum d f y := by
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith
  let q : ℝ := 1-y
  let c : ℝ := (d-1 : ℝ) * q / d
  let F : ℝ := f+q/d
  have hq : 0 < q := sub_pos.mpr hy
  have hc : 0 < c := div_pos (mul_pos (by linarith) hq) hdpos
  have hF0 : 0 ≤ F := add_nonneg hf (div_nonneg hq.le hdpos.le)
  have hF1 : F ≤ 1 := by
    have hq' : q / (d : ℝ) ≤ q := div_le_self hq.le (by linarith)
    dsimp [F]
    dsimp [q] at hq'
    linarith
  have hFdef : (d : ℝ)*F = (d : ℝ)*f+q := by
    dsimp [F]
    field_simp
    <;> ring
  have hFneg : 1 < (d : ℝ) * F := by
    rw [hFdef]
    dsimp [q]
    linarith
  have hA : 0 ≤ (d-1 : ℝ)*f*(y-f) := mul_nonneg (mul_nonneg (by linarith) hf) (sub_nonneg.mpr hfy)
  have hA' : 0 ≤ (d-1 : ℝ)*F*(1-F) := mul_nonneg (mul_nonneg (by linarith) hF0) (sub_nonneg.mpr hF1)
  have hpos := twoMeanOptimum_pos (by omega : 2 ≤ d) hf hfy hneg
  rw [twoMeanOptimum,if_neg (not_le.mpr hneg),twoMeanValue] at hpos
  have hL : 0 < y+(d-2 : ℝ)*f-2*Real.sqrt ((d-1 : ℝ)*f*(y-f)) :=
    (div_pos_iff_of_pos_right hdpos).mp hpos
  have hident : (d-1 : ℝ)*F*(1-F) = (d-1 : ℝ)*f*(y-f)+c^2+c*(y+(d-2 : ℝ)*f) := by
    dsimp [F,c,q]
    field_simp
    <;> ring
  have hsq : (Real.sqrt ((d-1 : ℝ)*f*(y-f))+c)^2 <
      (Real.sqrt ((d-1 : ℝ)*F*(1-F)))^2 := by
    rw [Real.sq_sqrt hA']
    have hs := Real.sq_sqrt hA
    have hprod := mul_pos hc hL
    nlinarith [hident]
  have hr := (sq_lt_sq₀ (add_nonneg (Real.sqrt_nonneg _) hc.le) (Real.sqrt_nonneg _)).mp hsq
  change twoMeanOptimum d F 1 < twoMeanOptimum d f y
  rw [twoMeanOptimum,if_neg (not_le.mpr hFneg),twoMeanOptimum,if_neg (not_le.mpr hneg)]
  unfold twoMeanValue
  apply (div_lt_div_iff_of_pos_right hdpos).mpr
  have hconst : y+(d-2 : ℝ)*f-(1+(d-2 : ℝ)*F) = -2*c := by
    dsimp [F,c,q]
    field_simp
    <;> ring
  linarith

/-- The finite source combination of its basis and anchored-cut phase averages. -/
def sourceAverage {n d : ℕ} (hn : 0 < n) (F : ℝ) :
    Matrix (Word (Fin d) n) (Word (Fin d) n) ℂ :=
  ((d-1 : ℝ)/(supportRank n d-1 : ℝ)) • basisAverage hn F +
    ((d : ℝ)*(d-1 : ℝ)/(supportRank n d-1 : ℝ)) •
      ∑ s : SourceCut n hn, phaseAverage s.1ᶜ (sourceCut_complement hn s)
        (by simpa only [compl_compl] using sourceCut_nonempty hn s) F

/-- Full source matrix identity for S_F, using the actual disjoint support
and finite averages, in arbitrary allowed n,d. -/
theorem source_average_matrix {n d : ℕ} (hn : 3 ≤ n) (hd : 3 ≤ d)
    {F : ℝ} (hF : 1/(d : ℝ) ≤ F) (hF1 : F ≤ 1) :
    sourceAverage (at_least_three_pos hn) F = F • rankOneDensity (ghz n d) +
      ((1-F)/(supportRank n d-1 : ℝ)) • (supportProjector n d-rankOneDensity (ghz n d)) := by
  classical
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hR : (supportRank n d : ℝ) = (d : ℝ)+(cutCount n : ℝ)*d*(d-1 : ℝ) := by
    simp [supportRank,Nat.cast_sub (by omega : 1 ≤ d)]
  have hR0 : (supportRank n d-1 : ℝ) ≠ 0 := by
    have h := (support_rank_bounds hn hd).1
    have h' : (d : ℝ) < supportRank n d := by exact_mod_cast h
    linarith
  have hT := support_projector_decomposition (d := d) (at_least_three_pos hn)
  have hT' : (∑ s : SourceCut n (at_least_three_pos hn),
      cutOffProjector s.1ᶜ (sourceCut_complement (by omega) s)
        (by simpa only [compl_compl] using sourceCut_nonempty (by omega) s)) =
      supportProjector n d-constantProjector n d := by rw [hT]; abel
  rw [sourceAverage,basis_average_matrix (by omega) hd hF hF1]
  simp_rw [phase_average_matrix hd _ _ _ hF hF1]
  rw [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,sourceCut_card,
    ← Nat.cast_smul_eq_nsmul ℝ,← Finset.smul_sum,hT']
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast (show (d : ℝ) ≠ 0 by linarith)
  have hdC1 : (d : ℂ)-1 ≠ 0 := by exact_mod_cast (show (d : ℝ)-1 ≠ 0 by linarith)
  have hRC0 : (supportRank n d : ℂ)-1 ≠ 0 := by exact_mod_cast hR0
  have hRC : (supportRank n d : ℂ) = (d : ℂ)+(cutCount n : ℂ)*d*(d-1 : ℂ) := by
    exact_mod_cast hR
  ext x y
  simp only [Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,Complex.real_smul]
  push_cast
  field_simp [hdC,hdC1,hRC0]
  rw [hRC]
  ring

/-- The actual computational Q sector, not an assumed cardinality. -/
def QIndex (n d : ℕ) := {x : Word (Fin d) n // ¬ (Finset.univ.image x).card ≤ 2}

instance qIndexFintype (n d : ℕ) : Fintype (QIndex n d) := by
  classical
  unfold QIndex
  infer_instance

/-- The source's d basis, K*3^d phase, and M-R Q components. -/
abbrev LowNoiseIndex (n d : ℕ) (hn : 0 < n) :=
  Fin d ⊕ ((SourceCut n hn × (Fin d → ZMod 3)) ⊕ QIndex n d)

instance lowNoiseIndexFintype (n d : ℕ) (hn : 0 < n) : Fintype (LowNoiseIndex n d hn) := by
  unfold LowNoiseIndex
  infer_instance

def lowNoiseWeights {n d : ℕ} (hn : 0 < n) (p : ℝ) : LowNoiseIndex n d hn → ℝ
  | .inl _ => noisyY n d p*(d-1 : ℝ)/((supportRank n d-1 : ℝ)*d)
  | .inr (.inl _) => noisyY n d p*(d : ℝ)*(d-1 : ℝ)/((supportRank n d-1 : ℝ)*(3^d : ℕ))
  | .inr (.inr _) => p/(wordCount n d : ℝ)

def lowNoiseStates {n d : ℕ} (hn : 0 < n) (p : ℝ) :
    LowNoiseIndex n d hn → Word (Fin d) n → ℂ
  | .inl j => chiVector hn j
      (optimalAlpha d (noisyF n d p/noisyY n d p)) (optimalBeta d (noisyF n d p/noisyY n d p))
  | .inr (.inl (s,θ)) => cutState s.1ᶜ (sourceCut_complement hn s)
      (by simpa only [compl_compl] using sourceCut_nonempty hn s)
      (optimalAlpha d (noisyF n d p/noisyY n d p)) (optimalBeta d (noisyF n d p/noisyY n d p))
      (phaseVector θ)
  | .inr (.inr x) => Pi.single x.1 1

lemma qIndex_card {n d : ℕ} (hn : 0 < n) :
    Fintype.card (QIndex n d) = wordCount n d-supportRank n d := by
  classical
  unfold QIndex
  rw [Fintype.card_subtype_compl,support_rank_card hn]
  simp [wordCount,Word]

private lemma complementProjector_basis {n d : ℕ} :
    complementProjector n d = ∑ x : QIndex n d, rankOneDensity (Pi.single x.1 (1 : ℂ)) := by
  classical
  have he : complementProjector n d =
      diagonal (fun x : Word (Fin d) n => if ¬ (Finset.univ.image x).card ≤ 2 then (1 : ℂ) else 0) := by
    ext x y
    by_cases h : (Finset.univ.image x).card ≤ 2
    · simp [complementProjector,supportProjector,diagonal_apply,Matrix.one_apply,h]
    · have h' : 2 < (Finset.univ.image x).card := Nat.lt_of_not_ge h
      simp [complementProjector,supportProjector,diagonal_apply,Matrix.one_apply,h,h']
  rw [he,diagonal_projector_sum,← Finset.sum_filter]
  exact Finset.sum_subtype _ (by simp) _

private lemma twoMeanOptimum_scaling {d : ℕ} {f y : ℝ} (hy : 0 < y) :
    y*twoMeanOptimum d (f/y) 1 = twoMeanOptimum d f y :=
  (twoMean_scaling hy).symm

private lemma low_noise_weight_sums {n d : ℕ} (hn : 3 ≤ n) (hd : 3 ≤ d)
    {p : ℝ} (hp : 0 ≤ p) (hpW : p ≤ witnessZeroProbability n d) :
    ((∑ j : Fin d, lowNoiseWeights (d := d) (at_least_three_pos hn) p (.inl j))+
      (∑ z : SourceCut n (at_least_three_pos hn) × (Fin d → ZMod 3),
        lowNoiseWeights (d := d) (at_least_three_pos hn) p (.inr (.inl z)))) = noisyY n d p ∧
      (∑ x : QIndex n d, lowNoiseWeights (d := d) (at_least_three_pos hn) p (.inr (.inr x))) = 1-noisyY n d p := by
  classical
  obtain ⟨hM,hR,hRM,hk,hpW0,hpW1⟩ := noisy_parameter_data hn hd
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (d : ℝ) ≠ 0 := by linarith
  have hR0 : (supportRank n d-1 : ℝ) ≠ 0 := by linarith
  have hN : ((3^d : ℕ) : ℝ) ≠ 0 := by positivity
  have hRank : (supportRank n d : ℝ) = (d : ℝ)+(cutCount n : ℝ)*d*(d-1 : ℝ) := by
    simp [supportRank,Nat.cast_sub (by omega : 1 ≤ d)]
  constructor
  · simp only [lowNoiseWeights,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
      Fintype.card_prod,Fintype.card_fun,ZMod.card,sourceCut_card,nsmul_eq_mul]
    push_cast
    field_simp [hd0,hR0,hN]
    rw [hRank]
    ring
  · have hRMnat : supportRank n d ≤ wordCount n d := (support_rank_bounds hn hd).2.le
    simp only [lowNoiseWeights,Finset.sum_const,Finset.card_univ,qIndex_card (at_least_three_pos hn),nsmul_eq_mul]
    push_cast [Nat.cast_sub hRMnat]
    unfold noisyY
    field_simp
    <;> ring

private lemma low_noise_weights_normalized {n d : ℕ} (hn : 3 ≤ n) (hd : 3 ≤ d)
    {p : ℝ} (hp : 0 ≤ p) (hpW : p ≤ witnessZeroProbability n d) :
    (∀ i, 0 ≤ lowNoiseWeights (d := d) (at_least_three_pos hn) p i) ∧
      (∑ i, lowNoiseWeights (d := d) (at_least_three_pos hn) p i) = 1 := by
  classical
  obtain ⟨hM,hR,hRM,hk,hpW0,hpW1⟩ := noisy_parameter_data hn hd
  obtain ⟨hy,hF,hF1⟩ := low_noise_ratio hn hd hp hpW
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith
  have hRpos : 0 < (supportRank n d-1 : ℝ) := by linarith
  constructor
  · intro i
    cases i with
    | inl j => exact div_nonneg (mul_nonneg hy.le (by linarith)) (mul_pos hRpos hdpos).le
    | inr z =>
      cases z with
      | inl z =>
        exact div_nonneg (mul_nonneg (mul_nonneg hy.le hdpos.le) (by linarith))
          (mul_pos hRpos (by positivity)).le
      | inr z => exact div_nonneg hp hM.le
  · obtain ⟨hs,hq⟩ := low_noise_weight_sums hn hd hp hpW
    change (∑ i : Fin d ⊕ ((SourceCut n (at_least_three_pos hn) × (Fin d → ZMod 3)) ⊕ QIndex n d), _) = 1
    rw [Fintype.sum_sum_type,Fintype.sum_sum_type]
    linarith

private lemma low_noise_states_unit {n d : ℕ} (hn : 3 ≤ n) (hd : 3 ≤ d)
    {p : ℝ} (hp : 0 ≤ p) (hpW : p ≤ witnessZeroProbability n d) :
    ∀ i, IsUnitState (lowNoiseStates (d := d) (at_least_three_pos hn) p i) := by
  obtain ⟨hy,hF,hF1⟩ := low_noise_ratio hn hd hp hpW
  intro i
  cases i with
  | inl j => exact (chi_attainment hn hd j hF hF1).1
  | inr z =>
    cases z with
    | inl z => exact (cutState_attainment hn hd _ _ _ (phaseVector z.2)
        (phaseVector_unit (by omega : 0 < d) z.2) hF hF1).1
    | inr x => exact basis_unit x.1

private lemma low_noise_matrix {n d : ℕ} (hn : 3 ≤ n) (hd : 3 ≤ d) (p : ℝ) :
    (∑ i, lowNoiseWeights (d := d) (at_least_three_pos hn) p i •
      rankOneDensity (lowNoiseStates (d := d) (at_least_three_pos hn) p i)) =
      noisyY n d p • sourceAverage (at_least_three_pos hn) (noisyF n d p/noisyY n d p) +
        (p/(wordCount n d : ℝ)) • complementProjector n d := by
  classical
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hR : (d : ℝ) < supportRank n d := by exact_mod_cast (support_rank_bounds hn hd).1
  have hd0 : (d : ℝ) ≠ 0 := by linarith
  have hR0 : (supportRank n d-1 : ℝ) ≠ 0 := by linarith
  have hN : ((3^d : ℕ) : ℝ) ≠ 0 := by positivity
  change (∑ i : Fin d ⊕ ((SourceCut n (at_least_three_pos hn) × (Fin d → ZMod 3)) ⊕ QIndex n d), _) = _
  simp only [Fintype.sum_sum_type,Fintype.sum_prod_type,lowNoiseWeights,lowNoiseStates]
  simp_rw [← Finset.smul_sum]
  rw [← complementProjector_basis]
  unfold sourceAverage basisAverage phaseAverage
  simp_rw [← Finset.smul_sum]
  simp only [smul_add,smul_smul]
  have ha : noisyY n d p*(d-1 : ℝ)/((supportRank n d-1 : ℝ)*d) =
      noisyY n d p*((d-1 : ℝ)/(supportRank n d-1 : ℝ))*(1/d) := by field_simp <;> ring
  have hb : noisyY n d p*(d : ℝ)*(d-1 : ℝ)/((supportRank n d-1 : ℝ)*(3^d : ℕ)) =
      noisyY n d p*((d : ℝ)*(d-1 : ℝ)/(supportRank n d-1 : ℝ))*(1/((3^d : ℕ) : ℝ)) := by
    field_simp
    <;> ring
  rw [ha,hb]
  module

/-- The complete original noisy matrix is reconstructed by the displayed
finite source ensemble, for the full closed low-noise interval. -/
theorem low_noise_reconstruction {n d : ℕ} (hn : 3 ≤ n) (hd : 3 ≤ d)
    {p : ℝ} (hp : 0 ≤ p) (hpW : p ≤ witnessZeroProbability n d) :
    noisyGhz n d p = ∑ i, lowNoiseWeights (d := d) (at_least_three_pos hn) p i •
      rankOneDensity (lowNoiseStates (d := d) (at_least_three_pos hn) p i) := by
  obtain ⟨hy,hF,hF1⟩ := low_noise_ratio hn hd hp hpW
  obtain ⟨hM,hR,_,_,_,_⟩ := noisy_parameter_data hn hd
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hR0 : (supportRank n d-1 : ℝ) ≠ 0 := by linarith
  have hyF : noisyY n d p*(noisyF n d p/noisyY n d p) = noisyF n d p := mul_div_cancel₀ _ hy.ne'
  have hc : noisyY n d p*((1-noisyF n d p/noisyY n d p)/(supportRank n d-1 : ℝ)) =
      p/(wordCount n d : ℝ) := by
    calc
      _ = (noisyY n d p-noisyY n d p*(noisyF n d p/noisyY n d p))/(supportRank n d-1 : ℝ) := by ring
      _ = (noisyY n d p-noisyF n d p)/(supportRank n d-1 : ℝ) := by rw [hyF]
      _ = _ := by unfold noisyY noisyF; field_simp <;> ring
  rw [low_noise_matrix hn hd,source_average_matrix hn hd hF hF1,
    smul_add,smul_smul,smul_smul,hyF,hc]
  unfold noisyGhz complementProjector noisyF wordCount
  ext x y
  simp only [Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,Complex.real_smul]
  push_cast
  ring

private lemma low_noise_average {n d : ℕ} (hn : 3 ≤ n) (hd : 3 ≤ d)
    {p : ℝ} (hp : 0 ≤ p) (hpW : p ≤ witnessZeroProbability n d) :
    (∑ i, lowNoiseWeights (d := d) (at_least_three_pos hn) p i *
      geometricMeasurePure (lowNoiseStates (d := d) (at_least_three_pos hn) p i)) =
      twoMeanOptimum d (noisyF n d p) (noisyY n d p) := by
  classical
  obtain ⟨hy,hF,hF1⟩ := low_noise_ratio hn hd hp hpW
  let e := twoMeanOptimum d (noisyF n d p/noisyY n d p) 1
  have hEb (j : Fin d) : geometricMeasurePure
      (lowNoiseStates (d := d) (at_least_three_pos hn) p (.inl j)) = e :=
    (chi_attainment hn hd j hF hF1).2.2.2
  have hEp (z : SourceCut n (at_least_three_pos hn) × (Fin d → ZMod 3)) :
      geometricMeasurePure (lowNoiseStates (d := d) (at_least_three_pos hn) p (.inr (.inl z))) = e :=
    (cutState_attainment hn hd _ _ _ (phaseVector z.2)
      (phaseVector_unit (by omega : 0 < d) z.2) hF hF1).2.2.2
  have hEq (x : QIndex n d) : geometricMeasurePure
      (lowNoiseStates (d := d) (at_least_three_pos hn) p (.inr (.inr x))) = 0 :=
    biseparable_measure_zero (by omega : 2 ≤ n) (by omega : 0 < d) _
      (computational_biseparable (by omega) x.1)
  have hs := (low_noise_weight_sums hn hd hp hpW).1
  calc
    _ = ((∑ j : Fin d, lowNoiseWeights (d := d) (at_least_three_pos hn) p (.inl j))+
        (∑ z : SourceCut n (at_least_three_pos hn) × (Fin d → ZMod 3),
          lowNoiseWeights (d := d) (at_least_three_pos hn) p (.inr (.inl z))))*e := by
      simp only [Fintype.sum_sum_type]
      simp_rw [hEb,hEp,hEq]
      simp only [mul_zero,Finset.sum_const_zero,add_zero]
      rw [← Finset.sum_mul,← Finset.sum_mul]
      ring
    _ = noisyY n d p*e := by rw [hs]
    _ = _ := twoMeanOptimum_scaling hy

/-- All finite weights, amplitudes, full matrix reconstruction and mean
entanglement of the low-noise ensemble, with its attained actual roof. -/
theorem low_noise_attainment {n d : ℕ} (hn : 3 ≤ n) (hd : 3 ≤ d)
    {p : ℝ} (hp : 0 ≤ p) (hpW : p ≤ witnessZeroProbability n d) :
    (∀ i, 0 ≤ lowNoiseWeights (d := d) (at_least_three_pos hn) p i) ∧
      (∑ i, lowNoiseWeights (d := d) (at_least_three_pos hn) p i) = 1 ∧
      (∀ i, IsUnitState (lowNoiseStates (d := d) (at_least_three_pos hn) p i)) ∧
      noisyGhz n d p = ∑ i, lowNoiseWeights (d := d) (at_least_three_pos hn) p i •
        rankOneDensity (lowNoiseStates (d := d) (at_least_three_pos hn) p i) ∧
      (∑ i, lowNoiseWeights (d := d) (at_least_three_pos hn) p i *
        geometricMeasurePure (lowNoiseStates (d := d) (at_least_three_pos hn) p i)) =
        twoMeanOptimum d (noisyF n d p) (noisyY n d p) ∧
      geometricMeasure (noisyGhz n d p) = twoMeanOptimum d (noisyF n d p) (noisyY n d p) := by
  obtain ⟨hweights,hsum⟩ := low_noise_weights_normalized hn hd hp hpW
  have hunit := low_noise_states_unit hn hd hp hpW
  have hmatrix := low_noise_reconstruction hn hd hp hpW
  have havg := low_noise_average hn hd hp hpW
  refine ⟨hweights,hsum,hunit,hmatrix,havg,?_⟩
  apply le_antisymm
  · rw [hmatrix]
    exact (finite_ensemble_upper (by omega) (by omega) _ _ hweights hsum hunit).trans_eq havg
  · have hp1 := hpW.trans (noisy_parameter_data hn hd).2.2.2.2.2.le
    have h := two_mean_lower hn hd (noisyDensity (by omega) (by omega) p hp hp1)
    rw [noisyDensity_matrix,(noisy_means (by omega) (by omega) p).1,
      (noisy_means (by omega) (by omega) p).2] at h
    exact h

private lemma optimal_threshold_amplitudes {d : ℕ} (hd : 3 ≤ d) :
    optimalAlpha d (1/(d : ℝ)) = 1 ∧ optimalBeta d (1/(d : ℝ)) = 0 := by
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith
  have hd0 : (d : ℝ) ≠ 0 := hdpos.ne'
  have hF1 : 1/(d : ℝ) ≤ 1 := (div_le_one hdpos).mpr (by linarith)
  obtain ⟨hb,hba,hnorm,hmean,_⟩ := optimal_amplitudes (by omega : 2 ≤ d) (le_refl (1/(d : ℝ))) hF1
  have ha := hb.trans hba
  have hm : (optimalAlpha d (1/(d : ℝ))+(d-1 : ℝ)*optimalBeta d (1/(d : ℝ)))^2 = 1 := by
    have h := congrArg (fun x : ℝ => x*(d : ℝ)) hmean
    simpa [hd0] using h
  have he : (d-1 : ℝ)*(d-2 : ℝ)*(optimalBeta d (1/(d : ℝ)))^2+
      2*(d-1 : ℝ)*optimalAlpha d (1/(d : ℝ))*optimalBeta d (1/(d : ℝ)) = 0 := by
    linear_combination hm-hnorm
  have hcross : 0 ≤ 2*(d-1 : ℝ)*optimalAlpha d (1/(d : ℝ))*optimalBeta d (1/(d : ℝ)) := by
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by linarith)) ha) hb
  have hcoeff : 0 < (d-1 : ℝ)*(d-2 : ℝ) := mul_pos (by linarith) (by linarith)
  have hsq : (optimalBeta d (1/(d : ℝ)))^2 ≤ 0 := by
    nlinarith [sq_nonneg (optimalBeta d (1/(d : ℝ)))]
  have hβ : optimalBeta d (1/(d : ℝ)) = 0 := by nlinarith [sq_nonneg (optimalBeta d (1/(d : ℝ)))]
  refine ⟨?_,hβ⟩
  rw [hβ] at hnorm
  nlinarith

private lemma cutState_one_zero {n d : ℕ} (a : Finset (Fin n)) (ha : a.Nonempty)
    (hc : aᶜ.Nonempty) (u : Fin d → ℂ) : cutState a ha hc 1 0 u = cutProduct a ha hc u := by
  unfold cutState cutProduct
  congr 1
  funext ij
  simp

private lemma chi_one_zero {n d : ℕ} (hn : 0 < n) (j : Fin d) :
    chiVector hn j 1 0 = Pi.single (fun _ : Fin n => j) (1 : ℂ) := by
  classical
  ext x
  by_cases hx : ∃ i : Fin d, ∀ k, x k = i
  · obtain ⟨i,hi⟩ := hx
    have he := funext hi
    subst x
    have hconst : ((fun _ : Fin n => i) = fun _ : Fin n => j) ↔ i = j :=
      ⟨fun h => constant_word_injective hn h,fun h => h ▸ rfl⟩
    simp [chiVector,constantVector_apply,Pi.single_apply,hconst,eq_comm]
  · have hne : (fun _ : Fin n => j) ≠ x := by
      intro h
      exact hx ⟨j,fun k => (congrFun h k).symm⟩
    rw [chiVector,constantVector_off hn _ _ hx]
    simp [Pi.single_apply,hne,Ne.symm hne]

private lemma noisy_threshold_ratio {n d : ℕ} (hn : 3 ≤ n) (hd : 3 ≤ d) :
    noisyF n d (witnessZeroProbability n d)/noisyY n d (witnessZeroProbability n d) = 1/(d : ℝ) := by
  obtain ⟨hM,hR,hRM,hk,hpW0,hpW1⟩ := noisy_parameter_data hn hd
  obtain ⟨_,_,hy,_⟩ := noisy_triangle hn hd hpW0.le hpW1.le
  have hd0 : (d : ℝ) ≠ 0 := by positivity
  have hw : witnessValue n d (witnessZeroProbability n d) = 0 := by
    rw [witness_value_affine (by omega) (by omega),witnessZeroProbability]
    field_simp
    <;> ring
  rw [noisy_witness_means (by omega) (by omega)] at hw
  have h := (div_eq_iff hd0).mp (show noisyY n d (witnessZeroProbability n d)/d =
    noisyF n d (witnessZeroProbability n d) by linarith)
  apply (div_eq_div_iff hy.ne' hd0).mpr
  nlinarith

/-- Every finite constituent at the threshold is genuinely biseparable
across its displayed cut; this does not infer factorization from a zero roof. -/
theorem threshold_constituents_biseparable {n d : ℕ} (hn : 3 ≤ n) (hd : 3 ≤ d) :
    ∀ i, IsBiseparable (lowNoiseStates (d := d) (at_least_three_pos hn) (witnessZeroProbability n d) i) := by
  obtain ⟨hα,hβ⟩ := optimal_threshold_amplitudes hd
  intro i
  cases i with
  | inl j =>
    simp only [lowNoiseStates,noisy_threshold_ratio hn hd,hα,hβ,chi_one_zero]
    exact computational_biseparable (by omega) _
  | inr z =>
    cases z with
    | inl z =>
      simp only [lowNoiseStates,noisy_threshold_ratio hn hd,hα,hβ,cutState_one_zero]
      exact cutProduct_biseparable _ _ _ _ (phaseVector_unit (by omega) z.2)
    | inr x => exact computational_biseparable (by omega) x.1


def highNoiseLambda (n d : ℕ) (p : ℝ) : ℝ :=
  (1-p)/(1-witnessZeroProbability n d)

abbrev HighNoiseIndex (n d : ℕ) (hn : 0 < n) := LowNoiseIndex n d hn ⊕ Word (Fin d) n

instance highNoiseIndexFintype (n d : ℕ) (hn : 0 < n) : Fintype (HighNoiseIndex n d hn) := by
  unfold HighNoiseIndex
  infer_instance

def highNoiseWeights {n d : ℕ} (hn : 0 < n) (p : ℝ) : HighNoiseIndex n d hn → ℝ
  | .inl i => highNoiseLambda n d p*lowNoiseWeights (d := d) hn (witnessZeroProbability n d) i
  | .inr _ => (1-highNoiseLambda n d p)/(wordCount n d : ℝ)

def highNoiseStates {n d : ℕ} (hn : 0 < n) : HighNoiseIndex n d hn → Word (Fin d) n → ℂ
  | .inl i => lowNoiseStates (d := d) hn (witnessZeroProbability n d) i
  | .inr x => Pi.single x 1

private lemma high_noise_lambda_bounds {n d : ℕ} (hn : 3 ≤ n) (hd : 3 ≤ d)
    {p : ℝ} (hpW : witnessZeroProbability n d ≤ p) (hp1 : p ≤ 1) :
    0 ≤ highNoiseLambda n d p ∧ highNoiseLambda n d p ≤ 1 := by
  have hW := (noisy_parameter_data hn hd).2.2.2.2.2
  have hden : 0 < 1-witnessZeroProbability n d := sub_pos.mpr hW
  exact ⟨div_nonneg (sub_nonneg.mpr hp1) hden.le,
    (div_le_one hden).mpr (by linarith)⟩

private lemma high_noise_weights_normalized {n d : ℕ} (hn : 3 ≤ n) (hd : 3 ≤ d)
    {p : ℝ} (hpW : witnessZeroProbability n d ≤ p) (hp1 : p ≤ 1) :
    (∀ i, 0 ≤ highNoiseWeights (d := d) (at_least_three_pos hn) p i) ∧
      (∑ i, highNoiseWeights (d := d) (at_least_three_pos hn) p i) = 1 := by
  classical
  obtain ⟨hM,_,_,_,hW0,_⟩ := noisy_parameter_data hn hd
  obtain ⟨hl,hl1⟩ := high_noise_lambda_bounds hn hd hpW hp1
  obtain ⟨hw,hs⟩ := low_noise_weights_normalized hn hd hW0.le (le_refl _)
  constructor
  · intro i
    cases i with
    | inl i => exact mul_nonneg hl (hw i)
    | inr x => exact div_nonneg (sub_nonneg.mpr hl1) hM.le
  · change (∑ i : LowNoiseIndex n d (at_least_three_pos hn) ⊕ Word (Fin d) n, _) = 1
    simp only [Fintype.sum_sum_type,highNoiseWeights,← Finset.mul_sum,hs,mul_one,
      Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    have hcard : (Fintype.card (Word (Fin d) n) : ℝ) = wordCount n d := by simp [Word,wordCount]
    rw [hcard,mul_div_cancel₀ _ hM.ne']
    ring

private lemma high_noise_states_biseparable {n d : ℕ} (hn : 3 ≤ n) (hd : 3 ≤ d) :
    ∀ i, IsBiseparable (highNoiseStates (d := d) (at_least_three_pos hn) i) := by
  intro i
  cases i with
  | inl i => exact threshold_constituents_biseparable hn hd i
  | inr x => exact computational_biseparable (by omega) x

/-- Exact actual high-noise reconstruction from the threshold cut products
and the finite computational ensemble for I/M. -/
theorem high_noise_reconstruction {n d : ℕ} (hn : 3 ≤ n) (hd : 3 ≤ d)
    {p : ℝ} (hpW : witnessZeroProbability n d ≤ p) (hp1 : p ≤ 1) :
    noisyGhz n d p = ∑ i, highNoiseWeights (d := d) (at_least_three_pos hn) p i •
      rankOneDensity (highNoiseStates (d := d) (at_least_three_pos hn) i) := by
  classical
  obtain ⟨hM,_,_,_,hW0,hW1⟩ := noisy_parameter_data hn hd
  have hl : highNoiseLambda n d p*(1-witnessZeroProbability n d) = 1-p := by
    unfold highNoiseLambda
    exact div_mul_cancel₀ _ (ne_of_gt (sub_pos.mpr hW1))
  change noisyGhz n d p = ∑ i : LowNoiseIndex n d (at_least_three_pos hn) ⊕ Word (Fin d) n, _
  rw [Fintype.sum_sum_type]
  simp only [highNoiseWeights,highNoiseStates,mul_smul,← Finset.smul_sum]
  rw [← low_noise_reconstruction hn hd hW0.le (le_refl _),basis_projector_sum]
  unfold noisyGhz wordCount
  simp only [Nat.cast_pow]
  rw [smul_add,smul_smul,smul_smul,hl]
  have he : highNoiseLambda n d p*(witnessZeroProbability n d/(d^n : ℝ))+
      (1-highNoiseLambda n d p)/(d^n : ℝ) = p/(d^n : ℝ) := by
    have hM0 : (d^n : ℝ) ≠ 0 := by positivity
    field_simp
    nlinarith [hl]
  rw [add_assoc,add_comm ((1-p) • rankOneDensity (ghz n d)),← add_assoc,← add_smul,he]

/-- The high-noise interval has an explicit normalized finite biseparable
ensemble and hence zero actual convex roof, including p=1. -/
theorem high_noise_attainment {n d : ℕ} (hn : 3 ≤ n) (hd : 3 ≤ d)
    {p : ℝ} (hpW : witnessZeroProbability n d ≤ p) (hp1 : p ≤ 1) :
    (∀ i, 0 ≤ highNoiseWeights (d := d) (at_least_three_pos hn) p i) ∧
      (∑ i, highNoiseWeights (d := d) (at_least_three_pos hn) p i) = 1 ∧
      (∀ i, IsBiseparable (highNoiseStates (d := d) (at_least_three_pos hn) i)) ∧
      noisyGhz n d p = ∑ i, highNoiseWeights (d := d) (at_least_three_pos hn) p i •
        rankOneDensity (highNoiseStates (d := d) (at_least_three_pos hn) i) ∧
      geometricMeasure (noisyGhz n d p) = 0 := by
  obtain ⟨hw,hs⟩ := high_noise_weights_normalized hn hd hpW hp1
  have hb := high_noise_states_biseparable hn hd
  have hm := high_noise_reconstruction hn hd hpW hp1
  refine ⟨hw,hs,hb,hm,?_⟩
  rw [hm]
  exact biseparable_ensemble_zero (by omega) (by omega) _ _ hw hs hb

lemma noisy_optimum_zero {n d : ℕ} (hn : 3 ≤ n) (hd : 3 ≤ d)
    {p : ℝ} (hpW : witnessZeroProbability n d ≤ p) :
    twoMeanOptimum d (noisyF n d p) (noisyY n d p) = 0 := by
  obtain ⟨_,_,_,hk,_,_⟩ := noisy_parameter_data hn hd
  have hw : 0 ≤ witnessValue n d p := by
    rw [witness_value_affine (by omega) (by omega)]
    have h := (div_le_iff₀ hk).mp hpW
    change (d-1 : ℝ)/d ≤ p*witnessSlope n d at h
    rw [neg_div]
    nlinarith
  rw [noisy_witness_means (by omega) (by omega)] at hw
  have hdpos : (0 : ℝ) < d := by positivity
  have h : (d : ℝ)*noisyF n d p ≤ noisyY n d p := by
    have h' := (le_div_iff₀ hdpos).mp (show noisyF n d p ≤ noisyY n d p/d by linarith)
    linarith
  simp [twoMeanOptimum,h]

end
end D5.S3.Quantum.Entanglement.Witness.NoisyGhzExactRoof
