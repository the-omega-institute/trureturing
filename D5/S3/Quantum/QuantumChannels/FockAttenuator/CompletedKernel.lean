/- GID: D5/S3/Quantum/QuantumChannels/FockAttenuator/CompletedKernel
   generality: I
   mirror-B: D5/B/S3/Quantum/QuantumChannels/FockAttenuator/CompletedKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Bargmann covariance of the existing completed beam splitter and the exact two-photon kernel. -/

import D5.S3.Quantum.QuantumChannels.FockAttenuator.BargmannKernel

/-! Covariance of the existing completed unitary fixes the exact physical kernel. -/

noncomputable section
open scoped BigOperators InnerProductSpace ENNReal NNReal
open Filter Topology

namespace D5.S3.Quantum.QuantumChannels.FockAttenuator.Bargmann
open BeamSplitter

/-- The action follows from the owner's actual dense Gram extension.
No replacement unitary or equality premise is introduced. -/
theorem beam_unitary_exponential (t r : ℝ) (h : t ^ 2 + r ^ 2 = 1) (z : ℂ × ℂ) :
    beamUnitary t r h (exponentialPair z) = exponentialPair (rotate t r z) := by
  classical
  have he : exponentialPair z =
      Finsupp.linearCombination ℂ exponentialPair (Finsupp.single z (1 : ℂ)) := by
    simp only [Finsupp.linearCombination_single, one_smul]
  unfold beamUnitary
  rw [he, LinearEquiv.extendOfIsometry_eq]
  simp only [LinearEquiv.refl_apply, Finsupp.linearCombination_single, one_smul,
    Function.comp_apply]

theorem rotate_inverse (t r : ℝ) (h : t ^ 2 + r ^ 2 = 1) (z : ℂ × ℂ) :
    rotate t (-r) (rotate t r z) = z := by
  have hc : (t : ℂ) ^ 2 + (r : ℂ) ^ 2 = 1 := by exact_mod_cast h
  apply Prod.ext
  · simp only [rotate, Complex.ofReal_neg]
    linear_combination hc * z.1
  · simp only [rotate, Complex.ofReal_neg]
    linear_combination hc * z.2

theorem beam_unitary_symm_exponential (t r : ℝ) (h : t ^ 2 + r ^ 2 = 1)
    (z : ℂ × ℂ) :
    (beamUnitary t r h).symm (exponentialPair z) = exponentialPair (rotate t (-r) z) := by
  apply (beamUnitary t r h).injective
  rw [LinearIsometryEquiv.apply_symm_apply, beam_unitary_exponential]
  congr 1
  simpa using (rotate_inverse t (-r) (by simpa using h) z).symm

/-- Completed two-mode covariance, for every Hilbert vector including
arbitrary infinite support. Totalness is already built into the owner's
unitary extension; the inner-product calculation has no cutoff limit. -/
theorem kernel_beam_unitary (t r : ℝ) (h : t ^ 2 + r ^ 2 = 1)
    (V : TwoMode) (z w : ℂ) :
    kernel (beamUnitary t r h V) z w =
      kernel V ((t : ℂ) * z + (r : ℂ) * w) (-(r : ℂ) * z + (t : ℂ) * w) := by
  rw [kernel_eq_inner, kernel_eq_inner]
  have hi := (beamUnitary t r h).inner_map_map
    ((beamUnitary t r h).symm (exponentialPair ((starRingEnd ℂ) z, (starRingEnd ℂ) w))) V
  rw [LinearIsometryEquiv.apply_symm_apply] at hi
  rw [hi]
  rw [beam_unitary_symm_exponential]
  congr 2
  apply Prod.ext <;>
    simp only [rotate, Complex.ofReal_neg, map_add, map_sub, map_mul,
      Complex.conj_ofReal, map_neg, sub_eq_add_neg, neg_mul]
  all_goals simp only [neg_neg]

theorem transform_single (n : ℕ) (z : ℂ) :
    transform (lp.single 2 n (1 : ℂ)) z =
      z ^ n / (Real.sqrt (n.factorial : ℝ) : ℂ) := by
  simp only [transform, lp.inner_single_right, exponentialVector, exponentialCoeff,
    RCLike.inner_apply, map_div₀, map_pow, Complex.conj_conj, Complex.conj_ofReal,
    one_mul]

/-- The exact completed kernel of the actual balanced two-photon input,
with retained variable first and discarded variable second. -/
theorem balanced_two_photon_kernel (a : Fock) (z w : ℂ)
    (hHalf : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1) :
    kernel (beamSplitter (1 / 2) hHalf (tensor a (lp.single 2 2 (1 : ℂ)))) z w =
      transform a ((z + w) / (Real.sqrt 2 : ℂ)) * (w - z) ^ 2 /
        (2 * (Real.sqrt 2 : ℂ)) := by
  have hreal : Real.sqrt (1 / 2 : ℝ) = 1 / Real.sqrt 2 := by
    rw [Real.sqrt_div (by norm_num), Real.sqrt_one]
  have ht : (Real.sqrt (1 / 2 : ℝ) : ℂ) = 1 / (Real.sqrt 2 : ℂ) := by
    exact_mod_cast hreal
  have hr : (Real.sqrt (1 - 1 / 2 : ℝ) : ℂ) = 1 / (Real.sqrt 2 : ℂ) := by
    norm_num only [show (1 - 1 / 2 : ℝ) = 1 / 2 by norm_num]
    exact ht
  have hs : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    norm_cast
    exact Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  rw [beamSplitter, kernel_beam_unitary, kernel_tensor, transform_single]
  rw [ht, hr]
  have hsum : (1 / (Real.sqrt 2 : ℂ)) * z + (1 / (Real.sqrt 2 : ℂ)) * w =
      (z + w) / (Real.sqrt 2 : ℂ) := by ring
  have hdiff : -(1 / (Real.sqrt 2 : ℂ)) * z + (1 / (Real.sqrt 2 : ℂ)) * w =
      (w - z) / (Real.sqrt 2 : ℂ) := by ring
  rw [hsum, hdiff, div_pow, hs]
  norm_num only [Nat.factorial, Nat.reduceMul, Nat.cast_ofNat]
  ring

#print axioms beam_unitary_exponential
#print axioms kernel_beam_unitary
#print axioms balanced_two_photon_kernel

end D5.S3.Quantum.QuantumChannels.FockAttenuator.Bargmann
