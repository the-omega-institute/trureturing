/- GID: D5/S3/Quantum/Analysis/RefinedBMV/DimFour
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/RefinedBMV/DimFour
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Refined BMV lower bounds for complex matrices of size four. -/

import D5.S3.Quantum.Analysis.RefinedBMV.DimFourScalar
import D5.S3.Quantum.Analysis.RefinedBMV.DimFourWalk

/-! # Refined BMV bounds with three second factors in dimension four -/

open Matrix NormedSpace
open scoped ComplexOrder BigOperators

namespace RefinedBMV.DimFour

open DimThree

noncomputable section

private abbrev Mat := Matrix (Fin 4) (Fin 4) ℂ

private theorem diagonal_bound {p : ℕ} (hp : p = 5 ∨ p = 6 ∨ p = 7)
    (a : Fin 4 → ℝ) (ha : ∀ i, 0 ≤ a i) (B : Mat) (hB : B.PosSemidef) :
    trace (((diagonal fun i ↦ (a i : ℂ)) ^ p * B) ^ 3) ≤
      DimThree.wordMean p ((diagonal fun i ↦ (a i : ℂ)) ^ 3) B := by
  have hn := walk_nonneg (defect p) a B hB
    (fun i j k ↦ defect_nonneg hp _ _ _ (ha i) (ha j) (ha k))
    (defect_diag hp) (defect_swap hp) (defect_cycle hp)
    (fun i j k ↦ individual_sq hp (ha i) (ha j) (ha k))
    (fun i j k ↦ pairing_all hp (criterion_nonneg_ordered p hp) _ _ _ (ha i) (ha j) (ha k))
  rw [← trace_gap hp] at hn
  have hlen : (0 : ℝ) < (gaps p).length := by exact_mod_cast (word_counts hp).2.1
  obtain ⟨hre, him⟩ := Complex.nonneg_iff.mp hn
  simp only [Complex.mul_re, Complex.mul_im, Complex.natCast_re, Complex.natCast_im,
    Complex.sub_re, Complex.sub_im, zero_mul, sub_zero, add_zero] at hre him
  exact Complex.le_def.mpr ⟨sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hlen).mp hre),
    (sub_eq_zero.mp (mul_eq_zero.mp him.symm |>.resolve_left hlen.ne')).symm⟩

theorem cubeRoot_bound {p : ℕ} (hp : p = 5 ∨ p = 6 ∨ p = 7)
    (X B : Mat) (hX : X.PosSemidef) (hB : B.PosSemidef) :
    trace ((X ^ p * B) ^ 3) ≤ DimThree.wordMean p (X ^ 3) B := by
  let U := hX.isHermitian.eigenvectorUnitary
  let f := Unitary.conjStarAlgAut ℂ _ (star U)
  have hB' : (f B).PosSemidef := by
    change (Unitary.conjStarAlgAut ℂ _ (star U) B).PosSemidef
    rw [Unitary.conjStarAlgAut_star_apply]
    exact hB.conjTranspose_mul_mul_same (U : Mat)
  have h := diagonal_bound hp _ hX.eigenvalues_nonneg (f B) hB'
  change trace (((diagonal (RCLike.ofReal ∘ hX.isHermitian.eigenvalues)) ^ p * f B) ^ 3) ≤
    DimThree.wordMean p ((diagonal (RCLike.ofReal ∘ hX.isHermitian.eigenvalues)) ^ 3) (f B) at h
  have hd : f X = diagonal (RCLike.ofReal ∘ hX.isHermitian.eigenvalues) :=
    hX.isHermitian.conjStarAlgAut_star_eigenvectorUnitary
  rw [← hd, ← map_pow f, ← map_mul f, ← map_pow f, ← map_pow f, trace_conjugation] at h
  change _ ≤ DimThree.wordMean p (f.toAlgEquiv (X ^ 3)) (f.toAlgEquiv B) at h
  simpa only [mean_map p f.toAlgEquiv (trace_conjugation (star U))] using h

open scoped MatrixOrder Matrix.Norms.L2Operator in
/-- The trace-power comparison for all PSD complex matrices of size four and (p=5,6,7). -/
theorem product_bound {p : ℕ} (hp : p = 5 ∨ p = 6 ∨ p = 7)
    (A B : Mat) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    trace (((A ^ ((p : ℝ) / 3)) * B) ^ 3) ≤ DimThree.wordMean p A B := by
  let X := A ^ (1 / 3 : ℝ)
  have hX : 0 ≤ X := CFC.rpow_nonneg
  have hpow (k : ℕ) : X ^ k = A ^ ((1 / 3 : ℝ) * k) := by
    rw [← CFC.rpow_natCast X k hX]
    exact CFC.rpow_rpow_of_exponent_nonneg A (1 / 3) k (by norm_num) (by positivity) hA.nonneg
  have h3 : X ^ (3 : ℕ) = A := by
    rw [hpow, show (1 / 3 : ℝ) * (↑(3 : ℕ) : ℝ) = 1 by norm_num, CFC.rpow_one A hA.nonneg]
  have hp' : X ^ p = A ^ ((p : ℝ) / 3) := by
    rw [hpow]
    congr 1
    ring
  simpa only [h3, hp'] using cubeRoot_bound hp X B
    (Matrix.nonneg_iff_posSemidef.mp hX) hB

/-- The refined BMV lower bound for all complex Hermitian size-four inputs and (p=5,6,7). -/
theorem exponential_bound {p : ℕ} (hp : p = 5 ∨ p = 6 ∨ p = 7)
    (H K : Mat) (hH : H.IsHermitian) (hK : K.IsHermitian) :
    trace (exp ((p : ℝ) • H + (3 : ℝ) • K)) ≤ DimThree.wordMean p (exp H) (exp K) := by
  let T : Mat := (1 / 3 : ℝ) • H
  let X := exp T
  have hT : T.IsHermitian := hermitian_real_smul hH _
  have hScale : (3 : ℝ) • ((p : ℝ) • T) = (p : ℝ) • H := by
    dsimp only [T]
    rw [smul_smul, smul_smul]
    congr 1
    ring
  have hpow (k : ℕ) : X ^ k = exp ((k : ℝ) • T) := by
    rw [Nat.cast_smul_eq_nsmul, Matrix.exp_nsmul]
  have h3 : X ^ (3 : ℕ) = exp H := by
    rw [hpow]
    norm_num [T, smul_smul]
  have hE := cubeRoot_bound hp X (exp K)
    (exp_posDef hT).posSemidef (exp_posDef hK).posSemidef
  rw [h3, hpow p] at hE
  have hh := hermitian_real_smul hT (p : ℝ)
  have ht := exponential_trace_le_cube ((p : ℝ) • T) K hh hK
  rw [hScale] at ht
  refine le_trans (Complex.le_def.mpr ⟨ht, ?_⟩) hE
  have he : IsSelfAdjoint (trace (exp ((p : ℝ) • H + (3 : ℝ) • K))) := by
    change star (trace _) = _
    rw [← trace_conjTranspose, ((hermitian_real_smul hH p).add (hermitian_real_smul hK 3)).exp.eq]
  rw [(Complex.im_eq_zero_iff_isSelfAdjoint _).mpr he,
    (Complex.im_eq_zero_iff_isSelfAdjoint _).mpr
      (trace_cube_isSelfAdjoint _ _ hh.exp hK.exp)]

#print axioms cubeRoot_bound
#print axioms product_bound
#print axioms exponential_bound

end

end RefinedBMV.DimFour
