/- GID: D5/S3/Quantum/Information/ProductMarginQubitOrder
   generality: G
   mirror-B: D5/B/S3/Quantum/Information/ProductMarginQubitOrder
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Closed-disk trace bounds for arbitrary complex common positive lower matrices. -/

import D5.S3.Quantum.Information.QubitNormalFormState
import D5.S3.Quantum.Hiai.ParallelSumVariational
import Mathlib.Tactic

noncomputable section
namespace D5.S3.Quantum.Information.ProductMarginQubitOrder
open _root_.Matrix
open scoped MatrixOrder ComplexOrder Kronecker
open D5.S3.Quantum.Information.QubitNormalFormState
open D5.S3.Quantum.Hiai.ParallelSumVariational


variable {d : Type*} [Fintype d] [DecidableEq d]

private lemma split_energy_mono {P Q K : Matrix d d ℂ}
    (hKP : K ≤ P) (hKQ : K ≤ Q) (W : Matrix d d ℂ × Matrix d d ℂ) :
    splitEnergy K K W ≤ splitEnergy P Q W := by
  have hu : W.1ᴴ * K * W.1 ≤ W.1ᴴ * P * W.1 := by
    apply Matrix.le_iff.mpr
    convert (Matrix.le_iff.mp hKP).conjTranspose_mul_mul_same W.1 using 1
    simp only [mul_sub, sub_mul]
  have hv : W.2ᴴ * K * W.2 ≤ W.2ᴴ * Q * W.2 := by
    apply Matrix.le_iff.mpr
    convert (Matrix.le_iff.mp hKQ).conjTranspose_mul_mul_same W.2 using 1
    simp only [mul_sub, sub_mul]
  exact add_le_add hu hv

private lemma split_energy_common_floor {K U V : Matrix d d ℂ}
    (hK : K.PosSemidef) (hUV : U + V = 1) :
    K ≤ (2 : ℝ) • (Uᴴ * K * U + Vᴴ * K * V) := by
  have he : (U + V)ᴴ * K * (U + V) = K := by rw [hUV]; simp
  apply Matrix.le_iff.mpr
  convert hK.conjTranspose_mul_mul_same (U - V) using 1
  calc
    (2 : ℝ) • (Uᴴ * K * U + Vᴴ * K * V) - K =
        (2 : ℝ) • (Uᴴ * K * U + Vᴴ * K * V) - (U + V)ᴴ * K * (U + V) := by rw [he]
    _ = (U - V)ᴴ * K * (U - V) := by
      simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_sub, add_mul, mul_add, sub_mul, mul_sub]
      module

/-- Any complex split of the identity gives an upper bound for a common PSD lower matrix.
The inputs themselves may be singular. -/
theorem common_lower_split_bound {P Q K : Matrix d d ℂ}
    (hK : K.PosSemidef) (hKP : K ≤ P) (hKQ : K ≤ Q)
    (W : Matrix d d ℂ × Matrix d d ℂ) (hW : W.1 + W.2 = 1) :
    K ≤ (2 : ℝ) • splitEnergy P Q W := by
  exact (split_energy_common_floor hK hW).trans
    (smul_le_smul_of_nonneg_left (split_energy_mono hKP hKQ W) (by norm_num))

private def pureSplit (x z : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(1 - (z : ℂ) / (1 - (x : ℂ) ^ 2)) / 2, -(x : ℂ) * z / (2 * (1 - (x : ℂ) ^ 2));
    (x : ℂ) * z / (2 * (1 - (x : ℂ) ^ 2)), (1 + (z : ℂ) / (1 - (x : ℂ) ^ 2)) / 2]

private lemma pure_annihilation {x z : ℝ} (hx : 0 ≤ x) (hx1 : x < 1)
    (hpure : x ^ 2 + z ^ 2 = 1) :
    qubitMatrix x z * pureSplit x z = 0 ∧
      qubitMatrix x (-z) * (1 - pureSplit x z) = 0 := by
  have hd : (1 : ℂ) - (x : ℂ) ^ 2 ≠ 0 := by
    have hr : (1 : ℝ) - x ^ 2 ≠ 0 := by nlinarith
    exact_mod_cast hr
  have hp : (x : ℂ) ^ 2 + (z : ℂ) ^ 2 = 1 := by exact_mod_cast hpure
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, qubitMatrix, pureSplit] <;>
    field_simp [hd] <;>
    first | linear_combination hp | linear_combination -hp |
      linear_combination (x : ℂ) * hp | linear_combination -(x : ℂ) * hp

/-- A distinct pure local pair has no nonzero common positive lower matrix after tensoring
with arbitrary other margins. This includes noncommuting complex lower matrices. -/
theorem common_lower_zero_of_pure_left {n : Type*} [Fintype n] [DecidableEq n]
    {x z : ℝ} (hx : 0 ≤ x) (hx1 : x < 1) (hpure : x ^ 2 + z ^ 2 = 1)
    (R S : Matrix n n ℂ) {K : Matrix (Fin 2 × n) (Fin 2 × n) ℂ}
    (hK : K.PosSemidef) (hKP : K ≤ qubitMatrix x z ⊗ₖ R)
    (hKQ : K ≤ qubitMatrix x (-z) ⊗ₖ S) : K = 0 := by
  let U := pureSplit x z ⊗ₖ (1 : Matrix n n ℂ)
  let V := (1 - pureSplit x z) ⊗ₖ (1 : Matrix n n ℂ)
  have hsum : U + V = 1 := by
    dsimp [U, V]
    rw [← Matrix.add_kronecker]
    simp
  have h := common_lower_split_bound hK hKP hKQ (U, V) hsum
  have hp := (pure_annihilation hx hx1 hpure).1
  have hq := (pure_annihilation hx hx1 hpure).2
  have henergy : splitEnergy (qubitMatrix x z ⊗ₖ R) (qubitMatrix x (-z) ⊗ₖ S) (U, V) = 0 := by
    dsimp [splitEnergy]
    have hpu : (qubitMatrix x z ⊗ₖ R) * U = 0 := by
      dsimp [U]
      rw [← Matrix.mul_kronecker_mul, hp]
      simp
    have hqv : (qubitMatrix x (-z) ⊗ₖ S) * V = 0 := by
      dsimp [V]
      rw [← Matrix.mul_kronecker_mul, hq]
      simp
    rw [Matrix.mul_assoc, hpu, Matrix.mul_assoc, hqv]
    simp
  rw [henergy, smul_zero] at h
  exact le_antisymm h hK.nonneg

private def flipMatrix (x : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, -(x : ℂ); -(x : ℂ), 1]

private def zMatrix : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

private def traceDenominator (x z y w : ℝ) : ℝ :=
  (1 - x ^ 2) * (1 - y ^ 2) - z ^ 2 * w ^ 2

private def mixtureInverse (x z y w : ℝ) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  (4 / (traceDenominator x z y w : ℂ)) •
    (flipMatrix x ⊗ₖ flipMatrix y - ((z * w : ℝ) : ℂ) • (zMatrix ⊗ₖ zMatrix))

private def traceSplit (x z y w : ℝ) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ ×
      Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  let N := (1 / 2 : ℂ) •
    (qubitMatrix x z ⊗ₖ qubitMatrix y w - qubitMatrix x (-z) ⊗ₖ qubitMatrix y (-w))
  ((1 / 2 : ℂ) • (1 - mixtureInverse x z y w * N),
    (1 / 2 : ℂ) • (1 + mixtureInverse x z y w * N))

-- Expanding the four-dimensional quadratic energy needs a larger finite algebra budget.
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private lemma trace_split_value {x z y w : ℝ} (hd : traceDenominator x z y w ≠ 0) :
    ((2 : ℝ) • splitEnergy (qubitMatrix x z ⊗ₖ qubitMatrix y w)
      (qubitMatrix x (-z) ⊗ₖ qubitMatrix y (-w)) (traceSplit x z y w)).trace =
      (((1 - x ^ 2 - z ^ 2) * (1 - y ^ 2 - w ^ 2) /
        traceDenominator x z y w : ℝ) : ℂ) := by
  have hd' : (traceDenominator x z y w : ℂ) ≠ 0 := by exact_mod_cast hd
  simp [splitEnergy, traceSplit, mixtureInverse, flipMatrix, zMatrix, qubitMatrix,
    Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.kronecker_apply, Matrix.smul_apply, Matrix.one_apply,
    Fintype.sum_prod_type, Fin.sum_univ_two, traceDenominator] at hd' ⊢
  push_cast
  field_simp [hd']
  <;> ring

/-- Every feasible complex lower matrix satisfies the full common-trace bound on the
closed local disks. Only the exceptional x=1 factors are excluded from the reliability
coordinates; pure factors with x<1 and arbitrary singular K remain included. -/
theorem common_lower_trace_bound {xC zC xD zD : ℝ}
    (hxC : 0 ≤ xC) (hxC1 : xC < 1) (hxD : 0 ≤ xD) (hxD1 : xD < 1)
    (hC : xC ^ 2 + zC ^ 2 ≤ 1) (hD : xD ^ 2 + zD ^ 2 ≤ 1)
    {K : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ}
    (hK : K.PosSemidef) (hKP : K ≤ qubitMatrix xC zC ⊗ₖ qubitMatrix xD zD)
    (hKQ : K ≤ qubitMatrix xC (-zC) ⊗ₖ qubitMatrix xD (-zD)) :
    K.trace.re ≤
      (1 - Real.sqrt ((zC ^ 2 / (1 - xC ^ 2)) * (zD ^ 2 / (1 - xD ^ 2)))) /
        (1 + Real.sqrt ((zC ^ 2 / (1 - xC ^ 2)) * (zD ^ 2 / (1 - xD ^ 2)))) := by
  have hfC : 0 < 1 - xC ^ 2 := by nlinarith
  have hfD : 0 < 1 - xD ^ 2 := by nlinarith
  let a := zC ^ 2 / (1 - xC ^ 2)
  let b := zD ^ 2 / (1 - xD ^ 2)
  let s := Real.sqrt (a * b)
  have ha : a ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨div_nonneg (sq_nonneg _) hfC.le, (div_le_one hfC).mpr (by linarith)⟩
  have hb : b ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨div_nonneg (sq_nonneg _) hfD.le, (div_le_one hfD).mpr (by linarith)⟩
  have hab : a * b ≤ 1 := mul_le_one₀ ha.2 hb.1 hb.2
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = a * b := Real.sq_sqrt (mul_nonneg ha.1 hb.1)
  have hs1 : s ≤ 1 := by nlinarith
  have hq : 0 ≤ (1 - s) / (1 + s) := div_nonneg (by linarith) (by positivity)
  change K.trace.re ≤ (1 - s) / (1 + s)
  by_cases hd : traceDenominator xC zC xD zD = 0
  · have hab1 : a * b = 1 := by
      dsimp [a, b]
      rw [div_mul_div_comm]
      apply (div_eq_one_iff_eq (mul_ne_zero hfC.ne' hfD.ne')).mpr
      dsimp [traceDenominator] at hd
      nlinarith only [hd]
    have ha1 : a = 1 := by
      apply le_antisymm ha.2
      nlinarith [mul_le_mul_of_nonneg_left hb.2 ha.1]
    have hpure : xC ^ 2 + zC ^ 2 = 1 := by
      have he := (div_eq_one_iff_eq hfC.ne').mp ha1
      linarith
    rw [common_lower_zero_of_pure_left hxC hxC1 hpure _ _ hK hKP hKQ]
    simpa using hq
  have hsplit : (traceSplit xC zC xD zD).1 + (traceSplit xC zC xD zD).2 = 1 := by
    dsimp [traceSplit]
    module
  have hbound := common_lower_split_bound hK hKP hKQ (traceSplit xC zC xD zD) hsplit
  have ht := (Complex.nonneg_iff.mp (Matrix.le_iff.mp hbound).trace_nonneg).1
  rw [Matrix.trace_sub, trace_split_value hd, Complex.sub_re, Complex.ofReal_re] at ht
  have hraw : K.trace.re ≤
      (1 - xC ^ 2 - zC ^ 2) * (1 - xD ^ 2 - zD ^ 2) /
        traceDenominator xC zC xD zD := by linarith
  have hablt : a * b < 1 := by
    apply lt_of_le_of_ne hab
    intro he
    apply hd
    have he' : zC ^ 2 * zD ^ 2 = (1 - xC ^ 2) * (1 - xD ^ 2) := by
      have hh := (div_eq_one_iff_eq (mul_ne_zero hfC.ne' hfD.ne')).mp
        (show zC ^ 2 * zD ^ 2 / ((1 - xC ^ 2) * (1 - xD ^ 2)) = 1 by
          simpa only [a, b, div_mul_div_comm] using he)
      exact hh
    dsimp [traceDenominator]
    linarith
  have hr : (1 - xC ^ 2 - zC ^ 2) * (1 - xD ^ 2 - zD ^ 2) /
      traceDenominator xC zC xD zD = (1 - a) * (1 - b) / (1 - a * b) := by
    dsimp [a, b, traceDenominator]
    field_simp
    <;> ring
  have ham : 2 * s ≤ a + b := by
    have hn : 0 ≤ (a + b) / 2 := by linarith [ha.1, hb.1]
    have hsq : s ^ 2 ≤ ((a + b) / 2) ^ 2 := by nlinarith [sq_nonneg (a - b)]
    have he := (sq_le_sq₀ hs0 hn).mp hsq
    linarith
  have hscalar : (1 - a) * (1 - b) / (1 - a * b) ≤ (1 - s) / (1 + s) := by
    apply (div_le_div_iff₀ (by linarith : 0 < 1 - a * b) (by positivity : 0 < 1 + s)).mpr
    nlinarith [mul_nonneg (show 0 ≤ a + b - 2 * s by linarith) (show 0 ≤ 1 + s by positivity)]
  exact (hraw.trans_eq hr).trans hscalar

#print axioms common_lower_zero_of_pure_left
#print axioms common_lower_trace_bound
end D5.S3.Quantum.Information.ProductMarginQubitOrder
