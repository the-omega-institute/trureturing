/- GID: D5/S3/Quantum/QuantumChannels/FockAttenuator/BargmannKernel
   generality: I
   mirror-B: D5/B/S3/Quantum/QuantumChannels/FockAttenuator/BargmannKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual Hilbert-space evaluation sections of the completed two-mode Bargmann kernel. -/

import D5.S3.Quantum.QuantumChannels.FockAttenuator.Bargmann

/-! Actual Hilbert evaluation sections and both entire variables of the completed kernel. -/

noncomputable section
open scoped BigOperators InnerProductSpace ENNReal NNReal
open Filter Topology

namespace D5.S3.Quantum.QuantumChannels.FockAttenuator.Bargmann
open BeamSplitter

/-- Evaluating the retained Bargmann coordinate leaves a genuine discarded-mode Fock vector. -/
def retainedSection (V : TwoMode) (z : ℂ) : Fock :=
  ⟨fun j => transform (V j) z,
    ((lp.memℓp V).norm.const_mul (Real.exp (‖z‖ ^ 2 / 2))).mono
      (fun j => (norm_transform_le (V j) z).trans_eq (mul_comm _ _))⟩

theorem norm_retained_section_le (V : TwoMode) (z : ℂ) :
    ‖retainedSection V z‖ ≤ ‖V‖ * Real.exp (‖z‖ ^ 2 / 2) := by
  calc
    ‖retainedSection V z‖ ≤ ‖Real.exp (‖z‖ ^ 2 / 2) • lp.toNorm V‖ := by
      apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      intro j
      simpa only [lp.coeFn_smul, lp.toNorm, Pi.smul_apply, smul_eq_mul,
        norm_mul, Real.norm_eq_abs, Real.abs_exp, abs_norm, retainedSection] using
        (norm_transform_le (V j) z).trans_eq (mul_comm _ _)
    _ = ‖V‖ * Real.exp (‖z‖ ^ 2 / 2) := by
      rw [norm_smul, lp.norm_toNorm]
      simp only [Real.norm_eq_abs, Real.abs_exp, mul_comm]

/-- The retained variable is first; the discarded variable corresponds to the outer lp index. -/
def kernel (V : TwoMode) (z w : ℂ) : ℂ := transform (retainedSection V z) w

/-- Identification with the owner's two-mode exponential vectors fixes the physical convention. -/
theorem kernel_eq_inner (V : TwoMode) (z w : ℂ) :
    kernel V z w = inner ℂ (exponentialPair ((starRingEnd ℂ) z, (starRingEnd ℂ) w)) V := by
  have hs := has_sum (retainedSection V z) w
  apply hs.unique
  convert lp.hasSum_inner
    (exponentialPair ((starRingEnd ℂ) z, (starRingEnd ℂ) w)) V using 1
  ext j
  simp only [retainedSection, exponentialPair, tensor, inner_smul_left,
    exponentialVector, exponentialCoeff, map_div₀, map_pow, Complex.conj_conj,
    Complex.conj_ofReal, transform]
  ring

theorem norm_kernel_le (V : TwoMode) (z w : ℂ) :
    ‖kernel V z w‖ ≤ ‖V‖ * Real.exp ((‖z‖ ^ 2 + ‖w‖ ^ 2) / 2) := by
  calc
    ‖kernel V z w‖ ≤ ‖retainedSection V z‖ * Real.exp (‖w‖ ^ 2 / 2) :=
      norm_transform_le _ _
    _ ≤ (‖V‖ * Real.exp (‖z‖ ^ 2 / 2)) * Real.exp (‖w‖ ^ 2 / 2) :=
      mul_le_mul_of_nonneg_right (norm_retained_section_le V z) (Real.exp_nonneg _)
    _ = ‖V‖ * Real.exp ((‖z‖ ^ 2 + ‖w‖ ^ 2) / 2) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring

theorem retained_section_tensor (a b : Fock) (z : ℂ) :
    retainedSection (tensor a b) z = transform a z • b := by
  apply lp.ext
  funext j
  simp only [retainedSection, tensor, transform, inner_smul_right,
    lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  ring

theorem kernel_tensor (a b : Fock) (z w : ℂ) :
    kernel (tensor a b) z w = transform a z * transform b w := by
  rw [kernel, retained_section_tensor]
  exact inner_smul_right _ _ _

theorem kernel_injective : Function.Injective kernel := by
  intro V W h
  have hs (z : ℂ) : retainedSection V z = retainedSection W z :=
    injective (congrFun h z)
  apply lp.ext
  funext j
  apply injective
  funext z
  exact congrArg (fun v : Fock => v j) (hs z)

theorem discarded_entire (V : TwoMode) (z : ℂ) :
    Differentiable ℂ (kernel V z) := entire _

/-- Absolute convergence of the vector-valued exponential contraction. -/
theorem summable_contraction (V : TwoMode) (w : ℂ) :
    Summable (fun j => exponentialCoeff w j • V j) := by
  apply Summable.of_norm
  simpa only [norm_smul, exponentialVector, lp.toNorm, norm_norm] using
    lp.summable_mul (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞))
      (by rw [Real.holderConjugate_iff]; norm_num)
      (lp.toNorm (exponentialVector w)) (lp.toNorm V)

/-- Evaluating the discarded coordinate also reconstructs a vector in the retained Hilbert space. -/
def discardedSection (V : TwoMode) (w : ℂ) : Fock :=
  ∑' j, exponentialCoeff w j • V j

theorem norm_discarded_section_le (V : TwoMode) (w : ℂ) :
    ‖discardedSection V w‖ ≤ ‖V‖ * Real.exp (‖w‖ ^ 2 / 2) := by
  have habs : Summable (fun j => ‖exponentialCoeff w j • V j‖) := by
    simpa only [norm_smul, exponentialVector, lp.toNorm, norm_norm] using
      lp.summable_mul (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞))
        (by rw [Real.holderConjugate_iff]; norm_num)
        (lp.toNorm (exponentialVector w)) (lp.toNorm V)
  calc
    ‖discardedSection V w‖ ≤ ∑' j, ‖exponentialCoeff w j • V j‖ :=
      norm_tsum_le_tsum_norm habs
    _ = ∑' j, ‖exponentialVector w j‖ * ‖V j‖ := by
      simp only [norm_smul, exponentialVector]
    _ ≤ ‖exponentialVector w‖ * ‖V‖ :=
      by
        have h := lp.tsum_mul_le_mul_norm' (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞))
          (by rw [Real.holderConjugate_iff]; norm_num)
          (lp.toNorm (exponentialVector w)) (lp.toNorm V)
        rw [lp.norm_toNorm, lp.norm_toNorm] at h
        simpa only [lp.toNorm, norm_norm] using h
    _ = ‖V‖ * Real.exp (‖w‖ ^ 2 / 2) := by rw [exponential_norm, mul_comm]

theorem kernel_eq_transform_discarded_section (V : TwoMode) (z w : ℂ) :
    kernel V z w = transform (discardedSection V w) z := by
  have hs := (summable_contraction V w).hasSum.mapL
    (innerSL ℂ (exponentialVector ((starRingEnd ℂ) z)))
  change HasSum _ (transform (discardedSection V w) z) at hs
  apply (has_sum (retainedSection V z) w).unique
  convert hs using 1
  ext j
  simp only [innerSL_apply_apply, inner_smul_right, retainedSection, exponentialCoeff, transform]
  ring

theorem retained_entire (V : TwoMode) (w : ℂ) :
    Differentiable ℂ (fun z => kernel V z w) := by
  simpa only [kernel_eq_transform_discarded_section] using entire (discardedSection V w)

#print axioms kernel_eq_inner
#print axioms norm_kernel_le
#print axioms kernel_eq_transform_discarded_section

end D5.S3.Quantum.QuantumChannels.FockAttenuator.Bargmann
