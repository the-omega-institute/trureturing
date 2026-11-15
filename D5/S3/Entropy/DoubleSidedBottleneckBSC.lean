/- GID: D5/S3/Entropy/DoubleSidedBottleneckBSC
   generality: G
   mirror-B: D5/B/S3/Entropy/DoubleSidedBottleneckBSC
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Exact BSC optimality for every finite channel at low correlation. -/

/-
proof_shape: content
escape_witness: none
admission_basis: open-problem-resolution (#26680; Proved)
Direct frozen dependencies: identities pending extraction from the merged-base report.
-/

import D5.S3.Divergence.ChainRule
import D5.S3.Entropy.RenyiCombining.BinaryRenyiCombining
import D5.S3.Divergence.ClassicalDPI
import D5.S3.Entropy.MaxEntropy
import D5.S3.Entropy.DoubleSidedBottleneckMoments
import D5.S3.Entropy.Observation.ExpectedPosteriorEntropyReduction
import D5.S3.Entropy.MutualInformationSymm
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Data.EReal.Basic
import Mathlib.Logic.Function.Basic
import D5.S3.Entropy.MutualInformation
import D5.S3.Quantum.CloningMachine
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Topology.Order.IntermediateValue
import D5.S3.Entropy.MutualInformationProduct
import D5.S3.Entropy.RenyiCombining.HircheCachinCombiningConcavity
import D5.S3.Entropy.Submodularity.MarkovDataProcessing
import D5.S3.Entropy.Submodularity.StrongSubadditivity



namespace D5.S3.Entropy.DoubleSidedBottleneckBSC

open scoped BigOperators

noncomputable def hbInv (y : ℝ) : (Set.Icc (0 : ℝ) (1 / 2 : ℝ)) :=
  letI : Nonempty (Set.Icc (0 : ℝ) (1 / 2 : ℝ)) := ⟨⟨0, by norm_num⟩⟩
  Function.invFun (fun a : (Set.Icc (0 : ℝ) (1 / 2 : ℝ)) => D5.S3.Quantum.CloningMachine.binaryEntropyBits a.val) y

noncomputable def dsbs (p : ℝ) (xy : Bool × Bool) : ℝ :=
  (if xy.1 = xy.2 then 1 - p else p) / 2

noncomputable def bsc (a : (Set.Icc (0 : ℝ) (1 / 2 : ℝ))) : (Bool → PMF (Fin 2)) :=
  let q : NNReal := ⟨a.val, a.property.1⟩
  have hq : q ≤ 1 := by
    change a.val ≤ 1
    linarith [a.property.2]
  fun x => (PMF.ofFintype (fun z : Bool => (↑(cond z q (1 - q)) : ENNReal))
    (by simp [hq])).map (fun z => if Bool.xor x z then (1 : Fin 2) else 0)

noncomputable def mutualInformationBits {A B : Type} [Fintype A] [Fintype B]
    (q : A × B → ℝ) : ℝ :=
  D5.S3.Entropy.MutualInformation.mutualInformation q / Real.log 2

noncomputable def rate {n : ℕ} (K : (Bool → PMF (Fin n))) : ℝ :=
  mutualInformationBits (fun xu : Bool × Fin n => (K xu.1 xu.2).toReal / 2)

noncomputable def outputJoint {n m : ℕ} (p : ℝ)
    (K : (Bool → PMF (Fin n))) (L : (Bool → PMF (Fin m))) (uv : Fin n × Fin m) : ℝ :=
  ∑ x : Bool, ∑ y : Bool,
    dsbs p (x, y) * (K x uv.1).toReal * (L y uv.2).toReal

noncomputable def objective {n m : ℕ} (p : ℝ)
    (K : (Bool → PMF (Fin n))) (L : (Bool → PMF (Fin m))) : ℝ :=
  mutualInformationBits (outputJoint p K L)

noncomputable def achievable (Cu Cv p : ℝ) : Set EReal :=
  {r | ∃ (n m : ℕ) (K : (Bool → PMF (Fin n))) (L : (Bool → PMF (Fin m))),
    rate K ≤ Cu ∧ rate L ≤ Cv ∧ r = (objective p K L : EReal)}

noncomputable def R (Cu Cv p : ℝ) : EReal := sSup (achievable Cu Cv p)

noncomputable def bscOptimal (Cu Cv p : ℝ) : Prop :=
  rate (bsc (hbInv (1 - Cu))) ≤ Cu ∧
  rate (bsc (hbInv (1 - Cv))) ≤ Cv ∧
  R Cu Cv p =
    (objective p (bsc (hbInv (1 - Cu))) (bsc (hbInv (1 - Cv))) : EReal)

def claim : Prop :=
  ∀ Cu : ℝ, 0 ≤ Cu → Cu ≤ 1 →
    ∀ Cv : ℝ, 0 ≤ Cv → Cv ≤ 1 →
      D5.S3.Quantum.CloningMachine.binaryEntropyBits (hbInv (1 - Cu)).val = 1 - Cu ∧
      D5.S3.Quantum.CloningMachine.binaryEntropyBits (hbInv (1 - Cv)).val = 1 - Cv ∧
      ∃ θ : ℝ, 0 ≤ θ ∧ θ < 1 / 2 ∧
        ∀ p : ℝ, 0 ≤ p → p ≤ 1 / 2 → θ < p → bscOptimal Cu Cv p

end D5.S3.Entropy.DoubleSidedBottleneckBSC

namespace D5.S3.Entropy.DoubleSidedBottleneckBSC

private noncomputable def outputMass {n : ℕ} (K : (Bool → PMF (Fin n))) (u : Fin n) : ℝ :=
  ((K false u).toReal + (K true u).toReal) / 2

private noncomputable def posteriorBias {n : ℕ} (K : (Bool → PMF (Fin n))) (u : Fin n) : ℝ :=
  ((K false u).toReal - (K true u).toReal) /
    ((K false u).toReal + (K true u).toReal)

private theorem kernel_real_sum {n : ℕ} (K : (Bool → PMF (Fin n))) (x : Bool) :
    ∑ u, (K x u).toReal = 1 := by
  have h := (K x).tsum_coe
  rw [tsum_fintype] at h
  have h' := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_sum (fun i _ => (K x).apply_ne_top i)] at h'
  simpa using h'

private theorem output_mass_probability {n : ℕ} (K : (Bool → PMF (Fin n))) :
    (∀ u, 0 ≤ outputMass K u) ∧ ∑ u, outputMass K u = 1 := by
  constructor
  · intro u; exact div_nonneg (add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg) (by norm_num)
  · simp only [outputMass, ← Finset.sum_div, Finset.sum_add_distrib,
      kernel_real_sum]
    norm_num

private theorem posterior_bias_mem {n : ℕ} (K : (Bool → PMF (Fin n))) (u : Fin n) :
    posteriorBias K u ∈ Set.Icc (-1 : ℝ) 1 := by
  have ha : 0 ≤ (K false u).toReal := ENNReal.toReal_nonneg
  have hbHyp : 0 ≤ (K true u).toReal := ENNReal.toReal_nonneg
  by_cases hzero : (K false u).toReal + (K true u).toReal = 0
  · simp [posteriorBias, hzero]
  · have hpos : 0 < (K false u).toReal + (K true u).toReal :=
      lt_of_le_of_ne (add_nonneg ha hbHyp) (Ne.symm hzero)
    constructor
    · exact (le_div_iff₀ hpos).mpr (by linarith)
    · exact (div_le_iff₀ hpos).mpr (by linarith)

private theorem mass_mul_bias {n : ℕ} (K : (Bool → PMF (Fin n))) (u : Fin n) :
    outputMass K u * posteriorBias K u =
      ((K false u).toReal - (K true u).toReal) / 2 := by
  have ha : 0 ≤ (K false u).toReal := ENNReal.toReal_nonneg
  have hbHyp : 0 ≤ (K true u).toReal := ENNReal.toReal_nonneg
  by_cases hzero : (K false u).toReal + (K true u).toReal = 0
  · have ha0 : (K false u).toReal = 0 := by linarith
    have hb0 : (K true u).toReal = 0 := by exact (eq_zero_iff_eq_zero_of_add_eq_zero hzero).mp ha0
    simp [outputMass, posteriorBias, ha0, hb0]
  · dsimp [outputMass, posteriorBias]
    field_simp [hzero]

private theorem posterior_bias_centered {n : ℕ} (K : (Bool → PMF (Fin n))) :
    ∑ u, outputMass K u * posteriorBias K u = 0 := by
  simp only [mass_mul_bias, ← Finset.sum_div, Finset.sum_sub_distrib, kernel_real_sum]
  norm_num

private theorem output_joint_posterior {n m : ℕ} (p : ℝ)
    (K : (Bool → PMF (Fin n))) (L : (Bool → PMF (Fin m))) (u : Fin n) (v : Fin m) :
    outputJoint p K L (u, v) = outputMass K u * outputMass L v *
      (1 + (1 - 2 * p) * posteriorBias K u * posteriorBias L v) := by
  have hK := mass_mul_bias K u
  have hL := mass_mul_bias L v
  calc
    outputJoint p K L (u, v) = outputMass K u * outputMass L v +
        (1 - 2 * p) *
          (((K false u).toReal - (K true u).toReal) / 2) *
          (((L false v).toReal - (L true v).toReal) / 2) := by
      simp [outputJoint, dsbs, outputMass]
      ring
    _ = _ := by rw [← hK, ← hL]; ring

private theorem output_joint_row_sum {n m : ℕ} (p : ℝ)
    (K : (Bool → PMF (Fin n))) (L : (Bool → PMF (Fin m))) (u : Fin n) :
    ∑ v, outputJoint p K L (u, v) = outputMass K u := by
  simp_rw [output_joint_posterior]
  have hf (v : Fin m) : outputMass K u * outputMass L v *
      (1 + (1 - 2 * p) * posteriorBias K u * posteriorBias L v) =
      outputMass K u * outputMass L v +
      ((1 - 2 * p) * outputMass K u * posteriorBias K u) *
        (outputMass L v * posteriorBias L v) := by ring
  simp_rw [hf]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    (output_mass_probability L).2, posterior_bias_centered L]
  ring

private theorem output_joint_col_sum {n m : ℕ} (p : ℝ)
    (K : (Bool → PMF (Fin n))) (L : (Bool → PMF (Fin m))) (v : Fin m) :
    ∑ u, outputJoint p K L (u, v) = outputMass L v := by
  simp_rw [output_joint_posterior]
  have hf (u : Fin n) : outputMass K u * outputMass L v *
      (1 + (1 - 2 * p) * posteriorBias K u * posteriorBias L v) =
      outputMass L v * outputMass K u +
      ((1 - 2 * p) * outputMass L v * posteriorBias L v) *
        (outputMass K u * posteriorBias K u) := by ring
  simp_rw [hf]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    (output_mass_probability K).2, posterior_bias_centered K]
  ring

private theorem objective_product_formula {n m : ℕ} (p : ℝ)
    (K : (Bool → PMF (Fin n))) (L : (Bool → PMF (Fin m))) :
    objective p K L =
      (∑ u, ∑ v, outputMass K u * outputMass L v *
        (1 + (1 - 2 * p) * posteriorBias K u * posteriorBias L v) *
        Real.log (1 + (1 - 2 * p) * posteriorBias K u * posteriorBias L v)) / Real.log 2 := by
  unfold objective mutualInformationBits
    D5.S3.Entropy.MutualInformation.mutualInformation
    D5.S3.Divergence.ClassicalDPI.klDivergence
  simp only [D5.S3.Divergence.ChainRule.marginal, output_joint_row_sum,
    output_joint_col_sum, Fintype.sum_prod_type]
  congr 1
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  rw [output_joint_posterior]
  by_cases h : outputMass K u * outputMass L v = 0
  · simp [h]
  · rw [mul_div_cancel_left₀ _ h]

end D5.S3.Entropy.DoubleSidedBottleneckBSC

namespace D5.S3.Entropy.DoubleSidedBottleneckBSC
open D5.S3.Divergence.ClassicalDPI
open D5.S3.Entropy.MaxEntropy
open D5.S3.Entropy.Observation.ExpectedPosteriorEntropyReduction
open D5.S3.Entropy.MutualInformationSymm

private theorem rate_posterior_formula {n : ℕ} (K : (Bool → PMF (Fin n))) :
    rate K = (∑ u, outputMass K u *
      (Real.log 2 - Real.binEntropy ((1 + posteriorBias K u) / 2))) / Real.log 2 := by
  let c : Bool → Fin n → ℝ := fun x u => (K x u).toReal
  let prior : Bool → ℝ := fun _ => 1 / 2
  have hmass (u : Fin n) : channelOutput c prior u = outputMass K u := by
    simp [channelOutput, prior, c, outputMass]
    ring
  have hgain : informationGain c prior =
      D5.S3.Entropy.MutualInformation.mutualInformation
        (fun xu : Bool × Fin n => (K xu.1 xu.2).toReal / 2) := by
    unfold informationGain experimentJointLaw
    convert mutual_information_symm
      (fun xu : Bool × Fin n => (K xu.1 xu.2).toReal / 2) using 1
    congr 1
    funext ux
    dsimp [c, prior]
    ring
  have hprior : shannonEntropy prior = Real.log 2 := by
    calc
      _ = Real.binEntropy (2⁻¹ : ℝ) := by
        norm_num [shannonEntropy, prior, Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
        <;> ring
      _ = _ := Real.binEntropy_two_inv
  have hpoint (u : Fin n) : outputMass K u * shannonEntropy (posterior c prior u) =
      outputMass K u * Real.binEntropy ((1 + posteriorBias K u) / 2) := by
    by_cases hz : outputMass K u = 0
    · simp [hz]
    · have hd : (K false u).toReal + (K true u).toReal ≠ 0 := by
        intro h
        apply hz
        simp [outputMass, h]
      have hfalse : posterior c prior u false = (1 + posteriorBias K u) / 2 := by
        simp only [posterior, hmass, c, prior, outputMass, posteriorBias]
        field_simp [hd]
        <;> ring
      have htrue : posterior c prior u true = 1 - (1 + posteriorBias K u) / 2 := by
        simp only [posterior, hmass, c, prior, outputMass, posteriorBias]
        field_simp [hd]
        <;> ring
      simp only [shannonEntropy, Fintype.sum_bool, hfalse, htrue,
        Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
      ring
  have h := information_gain_eq_expected_entropy_reduction c prior
    (fun u x => mul_nonneg (by norm_num [prior]) ENNReal.toReal_nonneg)
    (fun x => kernel_real_sum K x)
  rw [hgain, hprior] at h
  unfold expectedPosteriorEntropy at h
  simp_rw [hmass, hpoint] at h
  unfold rate mutualInformationBits
  congr 1
  rw [h]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, (output_mass_probability K).2, one_mul]

end D5.S3.Entropy.DoubleSidedBottleneckBSC

namespace D5.S3.Entropy.DoubleSidedBottleneckBSC

private theorem hb_inv_spec (y : ℝ) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    D5.S3.Quantum.CloningMachine.binaryEntropyBits (hbInv y).val = y := by
  have hf (a : ℝ) : D5.S3.Quantum.CloningMachine.binaryEntropyBits a = Real.binEntropy a / Real.log 2 := by
    simp only [D5.S3.Quantum.CloningMachine.binaryEntropyBits, D5.S3.Quantum.CloningMachine.binaryEntropyBits,
      Real.logb, Real.binEntropy, Real.log_inv]
    ring
  have hc : Continuous D5.S3.Quantum.CloningMachine.binaryEntropyBits := by
    simp_rw [show D5.S3.Quantum.CloningMachine.binaryEntropyBits = fun a => Real.binEntropy a / Real.log 2 by funext a; exact hf a]
    exact Real.binEntropy_continuous.div_const _
  have h0 : D5.S3.Quantum.CloningMachine.binaryEntropyBits 0 = 0 := by rw [hf]; simp
  have h1 : D5.S3.Quantum.CloningMachine.binaryEntropyBits (1 / 2) = 1 := by
    rw [hf]
    rw [show (1 / 2 : ℝ) = 2⁻¹ by norm_num, Real.binEntropy_two_inv]
    exact div_self (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  have hy' : y ∈ Set.Icc (D5.S3.Quantum.CloningMachine.binaryEntropyBits 0) (D5.S3.Quantum.CloningMachine.binaryEntropyBits (1 / 2)) := by rwa [h0, h1]
  obtain ⟨a, ha, he⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1 / 2)
    hc.continuousOn hy'
  letI : Nonempty (Set.Icc (0 : ℝ) (1 / 2 : ℝ)) := ⟨⟨0, by norm_num⟩⟩
  unfold hbInv
  exact Function.invFun_eq (f := fun a : (Set.Icc (0 : ℝ) (1 / 2 : ℝ)) => D5.S3.Quantum.CloningMachine.binaryEntropyBits a.val) ⟨⟨a, ha⟩, he⟩

end D5.S3.Entropy.DoubleSidedBottleneckBSC

namespace D5.S3.Entropy.DoubleSidedBottleneckBSC

private theorem bsc_apply_formula (a : (Set.Icc (0 : ℝ) (1 / 2 : ℝ))) (x : Bool) (u : Fin 2) :
    (bsc a x u).toReal = if u = (if x then (1 : Fin 2) else 0) then 1 - a.val else a.val := by
  have hq : (⟨a.val, a.property.1⟩ : NNReal) ≤ 1 := by
    change a.val ≤ 1
    linarith [a.property.2]
  cases x <;> fin_cases u <;>
    simp [bsc, PMF.map_apply, tsum_fintype, Finset.sum_filter, Bool.cond_true, Bool.cond_false, hq, NNReal.coe_sub] <;>
    first | rfl | exact NNReal.coe_sub hq

private theorem rate_bsc (a : (Set.Icc (0 : ℝ) (1 / 2 : ℝ))) : rate (bsc a) = 1 - D5.S3.Quantum.CloningMachine.binaryEntropyBits a.val := by
  have hloga : a.val = 0 ∨ 0 < a.val := Or.imp Eq.symm id (eq_or_lt_of_le a.property.1)
  have hcomp : 0 < 1 - a.val := by linarith [a.property.2]
  unfold rate mutualInformationBits
    D5.S3.Entropy.MutualInformation.mutualInformation
    D5.S3.Divergence.ClassicalDPI.klDivergence D5.S3.Divergence.ChainRule.marginal
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_two, bsc_apply_formula]
  norm_num
  have hhalf1 : a.val / 2 + (1 - a.val) / 2 = 1 / 2 := by ring
  have hhalf2 : (1 - a.val) / 2 + a.val / 2 = 1 / 2 := by ring
  simp only [hhalf1, hhalf2,
    show a.val / 2 / ((1 / 2 : ℝ) * (1 / 2)) = 2 * a.val by ring,
    show (1 - a.val) / 2 / ((1 / 2 : ℝ) * (1 / 2)) = 2 * (1 - a.val) by ring]
  rcases hloga with ha | ha
  · simp [ha, D5.S3.Quantum.CloningMachine.binaryEntropyBits, D5.S3.Quantum.CloningMachine.binaryEntropyBits, Real.logb]
    field_simp
    <;> ring
  · have hlog2 : Real.log (2 : ℝ) ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) ha.ne',
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hcomp.ne']
    simp only [D5.S3.Quantum.CloningMachine.binaryEntropyBits, D5.S3.Quantum.CloningMachine.binaryEntropyBits, Real.logb]
    field_simp
    <;> ring

end D5.S3.Entropy.DoubleSidedBottleneckBSC

namespace D5.S3.Entropy.DoubleSidedBottleneckBSC

private theorem candidate_rate {C : ℝ} (hC0 : 0 ≤ C) (hC1 : C ≤ 1) :
    rate (bsc (hbInv (1 - C))) = C := by
  rw [rate_bsc, hb_inv_spec (1 - C) ⟨by linarith, by linarith⟩]
  ring

private theorem bscOptimal_of_upper_bound {Cu Cv p : ℝ}
    (hCu0 : 0 ≤ Cu) (hCu1 : Cu ≤ 1) (hCv0 : 0 ≤ Cv) (hCv1 : Cv ≤ 1)
    (hupper : ∀ (n m : ℕ) (K : (Bool → PMF (Fin n))) (L : (Bool → PMF (Fin m))),
      rate K ≤ Cu → rate L ≤ Cv →
      objective p K L ≤ objective p (bsc (hbInv (1 - Cu))) (bsc (hbInv (1 - Cv)))) :
    bscOptimal Cu Cv p := by
  have hK := (candidate_rate hCu0 hCu1).le
  have hL := (candidate_rate hCv0 hCv1).le
  refine ⟨hK, hL, le_antisymm ?_ ?_⟩
  · apply sSup_le
    rintro r ⟨n, m, K, L, hKr, hLr, rfl⟩
    exact_mod_cast hupper n m K L hKr hLr
  · apply le_sSup
    exact ⟨2, 2, bsc (hbInv (1 - Cu)), bsc (hbInv (1 - Cv)), hK, hL, rfl⟩

end D5.S3.Entropy.DoubleSidedBottleneckBSC

namespace D5.S3.Entropy.DoubleSidedBottleneckBSC
open D5.S3.Entropy.DoubleSidedBottleneckMoments
open Moments Curvature Series
open scoped BigOperators

private theorem phi_bias (s : ℝ) :
    phi (s ^ 2) = Real.log 2 - Real.binEntropy ((1 + s) / 2) := by
  rw [phi, Real.sqrt_sq_eq_abs]
  by_cases hs : 0 ≤ s
  · rw [abs_of_nonneg hs]
  · rw [abs_of_neg (lt_of_not_ge hs),
      show (1 + -s) / 2 = 1 - (1 + s) / 2 by ring, Real.binEntropy_one_sub]

private theorem rate_phi {n : ℕ} (K : (Bool → PMF (Fin n))) :
    rate K = avg (outputMass K) (fun u => phi (posteriorBias K u ^ 2)) / Real.log 2 := by
  simp only [rate_posterior_formula, avg, phi_bias]

private theorem hb_binEntropy (a : ℝ) : D5.S3.Quantum.CloningMachine.binaryEntropyBits a = Real.binEntropy a / Real.log 2 := by
  simp only [D5.S3.Quantum.CloningMachine.binaryEntropyBits, D5.S3.Quantum.CloningMachine.binaryEntropyBits,
    Real.logb, Real.binEntropy, Real.log_inv]
  ring

private theorem phi_crossover (a : ℝ) :
    phi ((1 - 2 * a) ^ 2) = (1 - D5.S3.Quantum.CloningMachine.binaryEntropyBits a) * Real.log 2 := by
  rw [phi_bias, show (1 + (1 - 2 * a)) / 2 = 1 - a by ring,
    Real.binEntropy_one_sub, hb_binEntropy]
  field_simp [(Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne']

private theorem output_mass_bsc (a : (Set.Icc (0 : ℝ) (1 / 2 : ℝ))) (u : Fin 2) : outputMass (bsc a) u = 1 / 2 := by
  fin_cases u <;> norm_num [outputMass, bsc_apply_formula] <;> ring

private theorem posterior_bias_bsc (a : (Set.Icc (0 : ℝ) (1 / 2 : ℝ))) (u : Fin 2) :
    posteriorBias (bsc a) u = if u = 0 then 1 - 2 * a.val else -(1 - 2 * a.val) := by
  have h := mass_mul_bias (bsc a) u
  rw [output_mass_bsc] at h
  fin_cases u <;> norm_num [bsc_apply_formula] at * <;> linarith

private theorem objective_productValue {n m : ℕ} (p : ℝ) (K : (Bool → PMF (Fin n))) (L : (Bool → PMF (Fin m))) :
    objective p K L =
      productValue (1 - 2 * p) (outputMass K) (posteriorBias K) (outputMass L) (posteriorBias L) /
        Real.log 2 := by
  rw [objective_product_formula]
  congr 1
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  dsimp [productValue, Series.f]
  ring

private theorem objective_bsc_productValue (p : ℝ) (a b : (Set.Icc (0 : ℝ) (1 / 2 : ℝ))) :
    objective p (bsc a) (bsc b) =
      productValue (1 - 2 * p) half (signed (1 - 2 * a.val)) half (signed (1 - 2 * b.val)) /
        Real.log 2 := by
  rw [objective_productValue]
  congr 1
  simp only [productValue, Fin.sum_univ_two, output_mass_bsc, posterior_bias_bsc,
    Fintype.sum_bool, half, signed]
  norm_num <;> ring_nf

private theorem candidate_bias_interior {C : ℝ} (hC0 : 0 < C) (hC1 : C < 1) :
    (1 - 2 * (hbInv (1 - C)).val) ^ 2 ∈ Set.Ioo (0 : ℝ) 1 := by
  let a := hbInv (1 - C)
  have ha := a.property
  have he : D5.S3.Quantum.CloningMachine.binaryEntropyBits a.val = 1 - C := hb_inv_spec _ ⟨by linarith, by linarith⟩
  have hzero : D5.S3.Quantum.CloningMachine.binaryEntropyBits (0 : ℝ) = 0 := by rw [hb_binEntropy]; simp
  have hhalf : D5.S3.Quantum.CloningMachine.binaryEntropyBits (1 / 2 : ℝ) = 1 := by
    rw [hb_binEntropy, show (1 / 2 : ℝ) = 2⁻¹ by norm_num, Real.binEntropy_two_inv]
    exact div_self (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  have ha0 : 0 < a.val := by
    by_contra h
    have hz : a.val = 0 := by linarith [ha.1]
    rw [hz, hzero] at he
    linarith
  have ha1 : a.val < 1 / 2 := by
    by_contra h
    have hz : a.val = 1 / 2 := by linarith [ha.2]
    rw [hz, hhalf] at he
    linarith
  change (1 - 2 * a.val) ^ 2 ∈ Set.Ioo (0 : ℝ) 1
  constructor
  · exact sq_pos_of_pos (by linarith)
  · nlinarith [mul_pos ha0 (sub_pos.mpr ha1)]

end D5.S3.Entropy.DoubleSidedBottleneckBSC

namespace D5.S3.Entropy.DoubleSidedBottleneckBSC
open D5.S3.Entropy.DoubleSidedBottleneckMoments
open Moments Curvature Series
open scoped BigOperators

private theorem interior_bscOptimal {Cu Cv : ℝ}
    (hCu0 : 0 < Cu) (hCu1 : Cu < 1) (hCv0 : 0 < Cv) (hCv1 : Cv < 1) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ < 1 / 2 ∧
      ∀ p : ℝ, 0 ≤ p → p ≤ 1 / 2 → θ < p → bscOptimal Cu Cv p := by
  let α := hbInv (1 - Cu)
  let β := hbInv (1 - Cv)
  let a := 1 - 2 * α.val
  let b := 1 - 2 * β.val
  let M := max (Curvature.slope (a ^ 2)) (Curvature.slope (b ^ 2))
  have ha : a ^ 2 ∈ Set.Ioo (0 : ℝ) 1 := candidate_bias_interior hCu0 hCu1
  have hbHyp : b ^ 2 ∈ Set.Ioo (0 : ℝ) 1 := candidate_bias_interior hCv0 hCv1
  have hM : 0 ≤ M := (slope_nonneg ha).trans (le_max_left _ _)
  have hd : 0 < 1 + 6 * M := by positivity
  let θ := 3 * M / (1 + 6 * M)
  have hθ0 : 0 ≤ θ := by positivity
  have hθ1 : θ < 1 / 2 := by
    apply (div_lt_iff₀ hd).mpr
    linarith
  refine ⟨θ, hθ0, hθ1, ?_⟩
  intro p hp0 hp1 hθp
  have hδ0 : 0 ≤ 1 - 2 * p := by linarith
  have hδ1 : 1 - 2 * p < 1 := by linarith
  have hsmall : 1 - 2 * p ≤ 1 / (1 + 6 * M) := by
    have hh : 3 * M < p * (1 + 6 * M) := (div_lt_iff₀ hd).mp hθp
    apply (le_div_iff₀ hd).mpr
    nlinarith
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hφa : phi (a ^ 2) = Cu * Real.log 2 := by
    dsimp [a]
    rw [phi_crossover, hb_inv_spec (1 - Cu) ⟨by linarith, by linarith⟩]
    ring
  have hφb : phi (b ^ 2) = Cv * Real.log 2 := by
    dsimp [b]
    rw [phi_crossover, hb_inv_spec (1 - Cv) ⟨by linarith, by linarith⟩]
    ring
  apply bscOptimal_of_upper_bound hCu0.le hCu1.le hCv0.le hCv1.le
  intro n m K L hK hL
  have hs (u : Fin n) : |posteriorBias K u| ≤ 1 :=
    abs_le.mpr (posterior_bias_mem K u)
  have ht (v : Fin m) : |posteriorBias L v| ≤ 1 :=
    abs_le.mpr (posterior_bias_mem L v)
  have hsc : avg (outputMass K) (posteriorBias K) = 0 := posterior_bias_centered K
  have htc : avg (outputMass L) (posteriorBias L) = 0 := posterior_bias_centered L
  have hmb : avg (outputMass K) (fun u => phi (posteriorBias K u ^ 2)) ≤ phi (a ^ 2) := by
    rw [rate_phi] at hK
    rw [hφa]
    exact (div_le_iff₀ hlog).mp hK
  have hnb : avg (outputMass L) (fun v => phi (posteriorBias L v ^ 2)) ≤ phi (b ^ 2) := by
    rw [rate_phi] at hL
    rw [hφb]
    exact (div_le_iff₀ hlog).mp hL
  have hpost := posterior_local_optimality (outputMass K) (posteriorBias K)
    (outputMass L) (posteriorBias L) (output_mass_probability K).1 (output_mass_probability K).2
    (output_mass_probability L).1 (output_mass_probability L).2 hs ht hsc htc
    a b ha hbHyp hmb hnb hδ0 hδ1 hsmall
  calc
    objective p K L =
        productValue (1 - 2 * p) (outputMass K) (posteriorBias K) (outputMass L) (posteriorBias L) /
          Real.log 2 := objective_productValue p K L
    _ ≤ productValue (1 - 2 * p) half (signed a) half (signed b) / Real.log 2 :=
      div_le_div_of_nonneg_right hpost hlog.le
    _ = objective p (bsc (hbInv (1 - Cu))) (bsc (hbInv (1 - Cv))) :=
      (objective_bsc_productValue p α β).symm

end D5.S3.Entropy.DoubleSidedBottleneckBSC

namespace D5.S3.Entropy.DoubleSidedBottleneckBSC
open D5.S3.Entropy.DoubleSidedBottleneckMoments
open Moments Curvature Series
open scoped BigOperators

private theorem bias_zero_of_rate_nonpos {n : ℕ} (K : (Bool → PMF (Fin n))) (hK : rate K ≤ 0) :
    ∀ u, outputMass K u * posteriorBias K u = 0 := by
  let p := outputMass K
  let s := posteriorBias K
  have hp0 := (output_mass_probability K).1
  have hp1 := (output_mass_probability K).2
  have hx (u : Fin n) : s u ^ 2 ∈ Set.Icc (0 : ℝ) 1 := by
    have hh := posterior_bias_mem K u
    exact ⟨sq_nonneg _, by dsimp [s]; nlinarith [hh.1, hh.2]⟩
  have hv : avg p (fun u => s u ^ 2) ∈ Set.Icc (0 : ℝ) 1 := by
    simpa only [avg, smul_eq_mul] using (convex_Icc (0 : ℝ) 1).sum_mem
      (t := Finset.univ) (w := p) (z := fun u => s u ^ 2)
      (fun u _ => hp0 u) hp1 (fun u _ => hx u)
  rw [rate_phi] at hK
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hbudget : avg p (fun u => phi (s u ^ 2)) ≤ 0 := by
    have hh := (div_le_iff₀ hlog).mp hK
    simpa using hh
  have hj := phi_convex.map_sum_le (t := Finset.univ) (w := p) (p := fun u => s u ^ 2)
    (fun u _ => hp0 u) hp1 (fun u _ => hx u)
  simp only [smul_eq_mul] at hj
  change phi (avg p (fun u => s u ^ 2)) ≤ avg p (fun u => phi (s u ^ 2)) at hj
  have hphi0 : phi (0 : ℝ) = 0 := by norm_num [phi, Real.binEntropy] <;> ring
  have hv0 : avg p (fun u => s u ^ 2) = 0 := by
    apply le_antisymm _ hv.1
    apply (phi_strictMono.le_iff_le hv (by norm_num)).mp
    rw [hphi0]
    exact hj.trans hbudget
  have hterm (u : Fin n) : p u * s u ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => mul_nonneg (hp0 i) (sq_nonneg _))).mp hv0 u
      (Finset.mem_univ u)
  intro u
  change p u * s u = 0
  rcases mul_eq_zero.mp (hterm u) with h | h
  · simp [h]
  · rw [sq_eq_zero_iff] at h
    simp [h]

private theorem objective_zero_of_bias_zero {n m : ℕ} (p : ℝ) (K : (Bool → PMF (Fin n))) (L : (Bool → PMF (Fin m)))
    (hzero : (∀ u, outputMass K u * posteriorBias K u = 0) ∨
      (∀ v, outputMass L v * posteriorBias L v = 0)) : objective p K L = 0 := by
  have hprod : outputJoint p K L = fun uv => outputMass K uv.1 * outputMass L uv.2 := by
    funext uv
    rcases uv with ⟨u, v⟩
    rw [output_joint_posterior]
    calc
      _ = outputMass K u * outputMass L v + (1 - 2 * p) *
          (outputMass K u * posteriorBias K u) * (outputMass L v * posteriorBias L v) := by ring
      _ = _ := by rcases hzero with h | h <;> simp [h]
  unfold objective mutualInformationBits
  rw [hprod, D5.S3.Entropy.MutualInformationProduct.mutual_information_product_eq_zero
    (outputMass K) (outputMass L) (output_mass_probability K) (output_mass_probability L)]
  exact zero_div _

private theorem zero_budget_bscOptimal {Cu Cv p : ℝ}
    (hCu0 : 0 ≤ Cu) (hCu1 : Cu ≤ 1) (hCv0 : 0 ≤ Cv) (hCv1 : Cv ≤ 1)
    (hz : Cu = 0 ∨ Cv = 0) : bscOptimal Cu Cv p := by
  apply bscOptimal_of_upper_bound hCu0 hCu1 hCv0 hCv1
  intro n m K L hK hL
  rcases hz with hz | hz
  · have hzero := objective_zero_of_bias_zero p K L
      (Or.inl (bias_zero_of_rate_nonpos K (by simpa [hz] using hK)))
    have hcand := objective_zero_of_bias_zero p (bsc (hbInv (1 - Cu))) (bsc (hbInv (1 - Cv)))
      (Or.inl (bias_zero_of_rate_nonpos _ (by rw [candidate_rate hCu0 hCu1, hz])))
    rw [hzero, hcand]
  · have hzero := objective_zero_of_bias_zero p K L
      (Or.inr (bias_zero_of_rate_nonpos L (by simpa [hz] using hL)))
    have hcand := objective_zero_of_bias_zero p (bsc (hbInv (1 - Cu))) (bsc (hbInv (1 - Cv)))
      (Or.inr (bias_zero_of_rate_nonpos _ (by rw [candidate_rate hCv0 hCv1, hz])))
    rw [hzero, hcand]

end D5.S3.Entropy.DoubleSidedBottleneckBSC

namespace D5.S3.Entropy.DoubleSidedBottleneckBSC.Boundary
open D5.S3.Entropy.DoubleSidedBottleneckMoments
open Moments Curvature
open D5.S3.Entropy.RenyiCombining.HircheCachinCombiningConcavity
open scoped BigOperators

private theorem combining_monotone {y : ℝ} (hy : y ∈ Set.Icc (0 : ℝ) (Real.log 2)) :
    MonotoneOn (fun x => G 1 x y) (Set.Icc (0 : ℝ) (Real.log 2)) := by
  intro x hx z hz hxz
  have hv := (D5.S3.Entropy.RenyiCombining.HircheCachinCombiningConcavity.inverseBias_spec (by norm_num : (0 : ℝ) < 1) hy).1
  have hu := (D5.S3.Entropy.RenyiCombining.HircheCachinCombiningConcavity.inverseBias_spec (by norm_num : (0 : ℝ) < 1) hx).1
  have hw := (D5.S3.Entropy.RenyiCombining.HircheCachinCombiningConcavity.inverseBias_spec (by norm_num : (0 : ℝ) < 1) hz).1
  have horder := D5.S3.Entropy.RenyiCombining.HircheCachinCombiningConcavity.inverseBias_anti (by norm_num : (0 : ℝ) < 1) hx hz hxz
  change G 1 x y ≤ G 1 z y
  rw [D5.S3.Entropy.RenyiCombining.HircheCachinCombiningConcavity.bias_combining, D5.S3.Entropy.RenyiCombining.HircheCachinCombiningConcavity.bias_combining]
  apply (D5.S3.Entropy.RenyiCombining.HircheCachinCombiningConcavity.psi_strictAntiOn (by norm_num : (0 : ℝ) < 1)).antitoneOn
    ⟨mul_nonneg hv.1 hw.1, mul_le_one₀ hv.2 hw.1 hw.2⟩
    ⟨mul_nonneg hv.1 hu.1, mul_le_one₀ hv.2 hu.1 hu.2⟩
  exact mul_le_mul_of_nonneg_left horder hv.1

private theorem combining_bias {u v : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) (hv : v ∈ Set.Icc (0 : ℝ) 1) :
    G 1 (psi 1 u) (psi 1 v) = psi 1 (v * u) := by
  have hpu : (1 - u) / 2 ∈ Set.Icc (0 : ℝ) (1 / 2) := by constructor <;> linarith [hu.1, hu.2]
  have hpv : (1 - v) / 2 ∈ Set.Icc (0 : ℝ) (1 / 2) := by constructor <;> linarith [hv.1, hv.2]
  change h 1 (star (hInv 1 (h 1 ((1 - u) / 2))) (hInv 1 (h 1 ((1 - v) / 2)))) =
    h 1 ((1 - v * u) / 2)
  rw [hInv_h (by norm_num : (0 : ℝ) < 1) hpu, hInv_h (by norm_num : (0 : ℝ) < 1) hpv]
  congr 1
  dsimp [D5.S3.Entropy.RenyiCombining.HircheCachinCombiningConcavity.star, D5.S3.Entropy.RenyiCombining.BinaryRenyiCombining.bconv]
  ring

private theorem phi_psi (s : ℝ) : phi (s ^ 2) = Real.log 2 - psi 1 |s| := by
  simp [phi, psi, h, Real.sqrt_sq_eq_abs]
  rw [← Real.binEntropy_one_sub ((1 + |s|) / 2),
    show 1 - (1 + |s|) / 2 = (1 - |s|) / 2 by ring]

private theorem scalar_mgl {B : Type*} [Fintype B] (q t : B → ℝ)
    (hq0 : ∀ j, 0 ≤ q j) (hq1 : ∑ j, q j = 1) (ht : ∀ j, |t j| ≤ 1)
    {b δ : ℝ} (hbHyp : b ∈ Set.Icc (0 : ℝ) 1) (hδ : δ ∈ Set.Icc (0 : ℝ) 1)
    (hbudget : avg q (fun j => phi (t j ^ 2)) ≤ phi (b ^ 2)) :
    avg q (fun j => phi ((δ * t j) ^ 2)) ≤ phi ((δ * b) ^ 2) := by
  have hmem {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) :
      psi 1 u ∈ Set.Icc (0 : ℝ) (Real.log 2) := by
    simpa [psi, h] using (show Real.binEntropy ((1 - u) / 2) ∈ Set.Icc (0 : ℝ) (Real.log 2) from
      ⟨Real.binEntropy_nonneg (by linarith [hu.2]) (by linarith [hu.1]), Real.binEntropy_le_log_two⟩)
  let x : B → ℝ := fun j => psi 1 |t j|
  let y : ℝ := psi 1 δ
  have hx (j : B) : x j ∈ Set.Icc (0 : ℝ) (Real.log 2) := hmem ⟨abs_nonneg _, ht j⟩
  have hy : y ∈ Set.Icc (0 : ℝ) (Real.log 2) := hmem hδ
  have hxbar : avg q x ∈ Set.Icc (0 : ℝ) (Real.log 2) := by
    simpa only [avg, smul_eq_mul] using (convex_Icc (0 : ℝ) (Real.log 2)).sum_mem
      (t := Finset.univ) (w := q) (z := x) (fun j _ => hq0 j) hq1 (fun j _ => hx j)
  obtain ⟨αhat, hhat, _, hc, _⟩ :=
    D5.S3.Entropy.RenyiCombining.HircheCachinCombiningConcavity.result
  have hconv := hc 1 (by norm_num) hhat y hy
  have hj := hconv.map_sum_le (t := Finset.univ) (w := q) (p := x)
    (fun j _ => hq0 j) hq1 (fun j _ => hx j)
  simp only [smul_eq_mul] at hj
  change G 1 (avg q x) y ≤ avg q (fun j => G 1 (x j) y) at hj
  have hpoint (j : B) : x j = Real.log 2 - phi (t j ^ 2) := by
    dsimp [x]
    rw [phi_psi]
    ring
  have hbar : avg q x = Real.log 2 - avg q (fun j => phi (t j ^ 2)) := by
    rw [show x = (fun j => Real.log 2 - phi (t j ^ 2)) from funext hpoint,
      avg_sub, avg_const q _ hq1]
  have hbase : psi 1 b = Real.log 2 - phi (b ^ 2) := by
    rw [phi_psi, abs_of_nonneg hbHyp.1]
    ring
  have hmin : psi 1 b ≤ avg q x := by rw [hbase, hbar]; linarith
  have hm := combining_monotone hy (hmem hbHyp) hxbar hmin
  have htarget : G 1 (psi 1 b) y = Real.log 2 - phi ((δ * b) ^ 2) := by
    rw [combining_bias hbHyp hδ, phi_psi, abs_of_nonneg (mul_nonneg hδ.1 hbHyp.1)]
    ring
  have hgpoint (j : B) : G 1 (x j) y = Real.log 2 - phi ((δ * t j) ^ 2) := by
    rw [combining_bias ⟨abs_nonneg _, ht j⟩ hδ, phi_psi, abs_mul, abs_of_nonneg hδ.1]
    ring
  change G 1 (psi 1 b) y ≤ G 1 (avg q x) y at hm
  rw [htarget] at hm
  have hgsum : avg q (fun j => G 1 (x j) y) =
      Real.log 2 - avg q (fun j => phi ((δ * t j) ^ 2)) := by
    simp_rw [hgpoint]
    rw [avg_sub, avg_const q _ hq1]
  rw [hgsum] at hj
  linarith

end D5.S3.Entropy.DoubleSidedBottleneckBSC.Boundary

namespace D5.S3.Entropy.DoubleSidedBottleneckBSC
open D5.S3.Entropy.DoubleSidedBottleneckMoments
open Moments Curvature Series
open D5.S3.Entropy.Submodularity.MarkovDataProcessing
open D5.S3.Entropy.Submodularity.StrongSubadditivity
open D5.S3.Entropy.MutualInformationSymm
open scoped BigOperators

private theorem phi_f (z : ℝ) : phi (z ^ 2) = (Series.f z + Series.f (-z)) / 2 := by
  rw [phi_bias, Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub,
    show 1 - (1 + z) / 2 = (1 - z) / 2 by ring]
  rw [div_eq_mul_inv, div_eq_mul_inv, Real.negMulLog_mul, Real.negMulLog_mul]
  simp only [Real.negMulLog, Real.log_inv, Series.f]
  ring

private theorem output_joint_nonneg {n m : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (K : (Bool → PMF (Fin n))) (L : (Bool → PMF (Fin m))) (uv : Fin n × Fin m) :
    0 ≤ outputJoint p K L uv := by
  apply Finset.sum_nonneg
  intro x _
  apply Finset.sum_nonneg
  intro y _
  apply mul_nonneg _ ENNReal.toReal_nonneg
  apply mul_nonneg _ ENNReal.toReal_nonneg
  dsimp [dsbs]
  have hcomp : 0 ≤ 1 - p := sub_nonneg.mpr hp1
  split_ifs <;> positivity

private theorem objective_symm {n m : ℕ} (p : ℝ) (K : (Bool → PMF (Fin n))) (L : (Bool → PMF (Fin m))) :
    objective p K L = objective p L K := by
  have heq : outputJoint p K L = fun uv => outputJoint p L K (uv.2, uv.1) := by
    funext uv
    rcases uv with ⟨u, v⟩
    rw [output_joint_posterior, output_joint_posterior]
    ring
  unfold objective mutualInformationBits
  rw [heq, mutual_information_symm]

private noncomputable def noiseless : (Set.Icc (0 : ℝ) (1 / 2 : ℝ)) := ⟨0, by norm_num⟩

private theorem objective_le_noiseless {n m : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (K : (Bool → PMF (Fin n))) (L : (Bool → PMF (Fin m))) :
    objective p K L ≤ objective p (bsc noiseless) L := by
  let j : Fin m × Fin 2 → ℝ := fun vi => outputJoint p (bsc noiseless) L (vi.2, vi.1)
  let W : Fin 2 → Fin n → ℝ := fun i u => if i = 0 then (K false u).toReal else (K true u).toReal
  let triple : Fin m × (Fin 2 × Fin n) → ℝ := fun q => j (q.1, q.2.1) * W q.2.1 q.2.2
  have hW (i : Fin 2) : ∑ u, W i u = 1 := by
    fin_cases i
    · simpa [W] using kernel_real_sum K false
    · simpa [W] using kernel_real_sum K true
  have hW0 (i : Fin 2) (u : Fin n) : 0 ≤ W i u := by
    dsimp [W]
    split_ifs <;> exact ENNReal.toReal_nonneg
  have hj0 (vi : Fin m × Fin 2) : 0 ≤ j vi := output_joint_nonneg hp0 hp1 _ _ _
  have hj1 : ∑ vi, j vi = 1 := by
    dsimp [j]
    rw [Fintype.sum_prod_type]
    simp only [output_joint_col_sum]
    exact (output_mass_probability L).2
  have hprob : (∀ q, 0 ≤ triple q) ∧ ∑ q, triple q = 1 := by
    refine ⟨fun q => mul_nonneg (hj0 _) (hW0 _ _), ?_⟩
    simp only [triple, Fintype.sum_prod_type, ← Finset.mul_sum, hW, mul_one]
    simpa only [Fintype.sum_prod_type] using hj1
  have hxy : xyProjection triple = j := by
    funext vi
    simp [xyProjection, triple, ← Finset.mul_sum, hW]
  have hxz : xzProjection triple = fun vu => outputJoint p K L (vu.2, vu.1) := by
    funext vu
    rcases vu with ⟨v, u⟩
    simp [xzProjection, triple, j, W, Fin.sum_univ_two, outputJoint, dsbs,
      bsc_apply_formula, noiseless]
    ring
  have hmarkov := markov_of_channel j W hW
  have hDPI := mutual_information_le_of_markov triple hprob hmarkov
  rw [hxy, hxz, mutual_information_symm] at hDPI
  have hjMI : D5.S3.Entropy.MutualInformation.mutualInformation j =
      D5.S3.Entropy.MutualInformation.mutualInformation (outputJoint p (bsc noiseless) L) :=
    mutual_information_symm _
  rw [hjMI] at hDPI
  exact div_le_div_of_nonneg_right hDPI (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le

private theorem objective_noiseless_formula {m : ℕ} (p : ℝ) (L : (Bool → PMF (Fin m))) :
    objective p (bsc noiseless) L =
      avg (outputMass L) (fun v => phi (((1 - 2 * p) * posteriorBias L v) ^ 2)) / Real.log 2 := by
  rw [objective_productValue]
  congr 1
  dsimp [productValue, avg]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  simp only [Fin.sum_univ_two, output_mass_bsc, posterior_bias_bsc, noiseless]
  norm_num
  rw [phi_f]
  simp only [Series.f]
  ring_nf

private theorem hbInv_zero : hbInv 0 = noiseless := by
  have he := hb_inv_spec 0 (by norm_num)
  rw [hb_binEntropy] at he
  have hlog : Real.log (2 : ℝ) ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  have hz : Real.binEntropy (hbInv 0).val = 0 := (div_eq_zero_iff.mp he).resolve_right hlog
  rcases Real.binEntropy_eq_zero.mp hz with hz | hz
  · exact Subtype.ext hz
  · have hh := (hbInv 0).property.2
    rw [hz] at hh
    norm_num at hh

private theorem full_budget_upper {Cv p : ℝ} (hCv0 : 0 ≤ Cv) (hCv1 : Cv ≤ 1)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2)
    {n m : ℕ} (K : (Bool → PMF (Fin n))) (L : (Bool → PMF (Fin m))) (hL : rate L ≤ Cv) :
    objective p K L ≤ objective p (bsc (hbInv (1 - 1))) (bsc (hbInv (1 - Cv))) := by
  let β := hbInv (1 - Cv)
  let b := 1 - 2 * β.val
  have hbHyp : b ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> dsimp [b] <;> linarith [β.property.1, β.property.2]
  have hδ : 1 - 2 * p ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> linarith
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hbudget : avg (outputMass L) (fun v => phi (posteriorBias L v ^ 2)) ≤ phi (b ^ 2) := by
    rw [rate_phi] at hL
    have hh := (div_le_iff₀ hlog).mp hL
    have he : phi (b ^ 2) = Cv * Real.log 2 := by
      dsimp [b]
      rw [phi_crossover, hb_inv_spec _ ⟨by linarith, by linarith⟩]
      ring
    rwa [he]
  have hmgl := Boundary.scalar_mgl (outputMass L) (posteriorBias L)
    (output_mass_probability L).1 (output_mass_probability L).2
    (fun v => abs_le.mpr (posterior_bias_mem L v)) hbHyp hδ hbudget
  have hcand : objective p (bsc noiseless) (bsc β) = phi (((1 - 2 * p) * b) ^ 2) / Real.log 2 := by
    rw [objective_noiseless_formula]
    congr 1
    simp only [avg, Fin.sum_univ_two, output_mass_bsc, posterior_bias_bsc]
    norm_num
    rw [show ((1 - 2 * p) * (2 * β.val - 1)) ^ 2 = ((1 - 2 * p) * b) ^ 2 by dsimp [b]; ring]
    ring
  simp only [sub_self, hbInv_zero]
  calc
    objective p K L ≤ objective p (bsc noiseless) L := objective_le_noiseless hp0 (by linarith) K L
    _ = avg (outputMass L) (fun v => phi (((1 - 2 * p) * posteriorBias L v) ^ 2)) / Real.log 2 :=
      objective_noiseless_formula p L
    _ ≤ phi (((1 - 2 * p) * b) ^ 2) / Real.log 2 := div_le_div_of_nonneg_right hmgl hlog.le
    _ = objective p (bsc noiseless) (bsc (hbInv (1 - Cv))) := hcand.symm

private theorem full_budget_bscOptimal {Cu Cv p : ℝ}
    (hCu0 : 0 ≤ Cu) (hCu1 : Cu ≤ 1) (hCv0 : 0 ≤ Cv) (hCv1 : Cv ≤ 1)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2) (hz : Cu = 1 ∨ Cv = 1) : bscOptimal Cu Cv p := by
  apply bscOptimal_of_upper_bound hCu0 hCu1 hCv0 hCv1
  intro n m K L hK hL
  rcases hz with hz | hz
  · subst Cu
    exact full_budget_upper hCv0 hCv1 hp0 hp1 K L hL
  · subst Cv
    rw [objective_symm p K L, objective_symm p (bsc (hbInv (1 - Cu))) (bsc (hbInv (1 - 1)))]
    exact full_budget_upper hCu0 hCu1 hp0 hp1 L K hK

theorem result : claim := by
  intro Cu hCu0 hCu1 Cv hCv0 hCv1
  refine ⟨hb_inv_spec _ ⟨by linarith, by linarith⟩,
    hb_inv_spec _ ⟨by linarith, by linarith⟩, ?_⟩
  by_cases hz : Cu = 0 ∨ Cv = 0
  · exact ⟨0, le_rfl, by norm_num, fun p _ _ _ => zero_budget_bscOptimal hCu0 hCu1 hCv0 hCv1 hz⟩
  by_cases ho : Cu = 1 ∨ Cv = 1
  · exact ⟨0, le_rfl, by norm_num,
      fun p hp0 hp1 _ => full_budget_bscOptimal hCu0 hCu1 hCv0 hCv1 hp0 hp1 ho⟩
  exact interior_bscOptimal
    (lt_of_le_of_ne hCu0 (Ne.symm (not_or.mp hz).1))
    (lt_of_le_of_ne hCu1 (not_or.mp ho).1)
    (lt_of_le_of_ne hCv0 (Ne.symm (not_or.mp hz).2))
    (lt_of_le_of_ne hCv1 (not_or.mp ho).2)

end D5.S3.Entropy.DoubleSidedBottleneckBSC
