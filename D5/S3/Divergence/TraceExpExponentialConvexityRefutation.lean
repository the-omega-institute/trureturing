/- GID: D5/S3/Divergence/TraceExpExponentialConvexityRefutation
   generality: I
   mirror-B: D5/B/S3/Divergence/TraceExpExponentialConvexityRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Divergence/TraceExpExponentialConvexityRefutation.claim; result=D5/S3/Divergence/TraceExpExponentialConvexityRefutation.result; claim=D5/S3/Divergence/TraceExpExponentialConvexityRefutation.claim
   digest: Centre-plus-trine qubit states refute exponential convexity of the trace exponential. -/

/- escape_witness: the centre-plus-trine configuration has quadratic form −(3 / 2)(u−1)⁴.
   Direct frozen dependencies: none (pinned Mathlib only).
   admission_basis: open-problem-resolution (#16100; Refuted)
   Per-declaration proof_shape and live consumers:
     trExp: definition; consumers=claim, trace_exp_conjugate, kernel, quadratic, family
     IsDensity: definition; consumers=claim, density, family
     claim: definition; consumer=result
     rho: definition; consumers=density, spectral, kernel, quadratic, family
     sqrt_three_sq: bind-only; consumers=density, angles_unit, spectral
     density: bind-only; consumer=family
     rot: definition; consumers=rot_inv, spectral, kernel
     rot_inv: bind-only; consumer=kernel
     trace_exp_conjugate: bind-only; consumer=kernel
     angles: definition; consumers=angles_unit, spectral, kernel
     eigen: definition; consumers=spectral, kernel
     angles_unit: bind-only; consumer=kernel
     spectral: bind-only; consumer=kernel
     kernel: bind-only; consumer=quadratic
     coeff: definition; consumers=quadratic, family
     quadratic: bind-only; consumer=family
     family: bind-only; consumer=result
     result: bind-only; explicit external open-problem refutation. -/

import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

noncomputable section
open Matrix
open scoped ComplexOrder
namespace D5.S3.Divergence.TraceExpExponentialConvexityRefutation

/-- `Tr e^A`, with Mathlib's matrix exponential. -/
noncomputable def trExp {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  Matrix.trace (NormedSpace.exp A)
/-- Density matrices. -/
def IsDensity {n : ℕ} (ρ : Matrix (Fin n) (Fin n) ℂ) : Prop := ρ.PosSemidef ∧ ρ.trace = 1
/-- The §VI conjecture: `A ↦ Tr e^A` is exponentially convex on density matrices
(Definition 4: the kernel `(ρ, σ) ↦ Tr e^{(ρ+σ) / 2}` is positive definite). -/
def claim : Prop :=
  ∀ (n N : ℕ) (ρ : Fin N → Matrix (Fin n) (Fin n) ℂ) (c : Fin N → ℝ),
    (∀ i, IsDensity (ρ i)) →
    0 ≤ (∑ i, ∑ j, ((c i * c j : ℝ) : ℂ) * trExp ((1 / 2 : ℂ) • (ρ i + ρ j))).re

private def rho : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![!![1 / 2, 0; 0, 1 / 2], !![1, 0; 0, 0],
    !![1 / 4, (Real.sqrt 3 : ℂ) / 4; (Real.sqrt 3 : ℂ) / 4, 3 / 4],
    !![1 / 4, -(Real.sqrt 3 : ℂ) / 4; -(Real.sqrt 3 : ℂ) / 4, 3 / 4]]

private lemma sqrt_three_sq : (Real.sqrt 3 : ℂ) ^ 2 = 3 := by
  exact_mod_cast Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)

private lemma density : ∀ i, IsDensity (rho i) := by
  intro i
  have hs := sqrt_three_sq
  fin_cases i
  · constructor
    · have hp : (diagonal ![(1 / 2 : ℂ), 1 / 2]).PosSemidef := by
        simp only [posSemidef_diagonal_iff]
        intro j; fin_cases j <;> norm_num [Complex.le_def]
      convert hp using 1
      simp [rho, diagonal_fin_two]
    · norm_num [rho, Matrix.trace, Fin.sum_univ_two]
  · constructor
    · have hp : (diagonal ![(1 : ℂ), 0]).PosSemidef := by
        simp only [posSemidef_diagonal_iff]
        intro j; fin_cases j <;> norm_num
      convert hp using 1
      simp [rho, diagonal_fin_two]
    · norm_num [rho, Matrix.trace, Fin.sum_univ_two]
  · constructor
    · have hp := posSemidef_vecMulVec_self_star (![(1 / 2 : ℂ), (Real.sqrt 3 : ℂ) / 2])
      convert hp using 1
      ext j k; fin_cases j <;> fin_cases k <;>
        norm_num [rho, vecMulVec, map_div₀, map_ofNat] <;> ring_nf <;> norm_num [hs]
    · norm_num [rho, Matrix.trace, Fin.sum_univ_two]
  · constructor
    · have hp := posSemidef_vecMulVec_self_star (![(-1 / 2 : ℂ), (Real.sqrt 3 : ℂ) / 2])
      convert hp using 1
      ext j k; fin_cases j <;> fin_cases k <;>
        norm_num [rho, vecMulVec, map_div₀, map_ofNat] <;> ring_nf <;> norm_num [hs]
    · norm_num [rho, Matrix.trace, Fin.sum_univ_two]

private def rot (a b : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![a, -b; b, a]

private lemma rot_inv (a b : ℂ) (h : a ^ 2 + b ^ 2 = 1) :
    rot a b * rot a (-b) = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [rot, Matrix.mul_apply, Fin.sum_univ_two] <;>
    first | linear_combination h | ring

private lemma trace_exp_conjugate (U V : Matrix (Fin 2) (Fin 2) ℂ)
    (huv : U * V = 1) (hvu : V * U = 1) (x y : ℝ) :
    trExp (U * diagonal ![(x : ℂ), (y : ℂ)] * V) =
      (Real.exp x : ℂ) + (Real.exp y : ℂ) := by
  let W : (Matrix (Fin 2) (Fin 2) ℂ)ˣ := ⟨U, V, huv, hvu⟩
  change trace (NormedSpace.exp ((W : Matrix (Fin 2) (Fin 2) ℂ) *
    diagonal ![(x : ℂ), (y : ℂ)] * (↑W⁻¹ : Matrix (Fin 2) (Fin 2) ℂ))) = _
  rw [Matrix.exp_units_conj, Matrix.trace_units_conj, Matrix.exp_diagonal]
  simp [Matrix.trace, Fin.sum_univ_two, Pi.exp_def,
    ← Complex.exp_eq_exp_ℂ, ← Complex.ofReal_exp]

private def angles : Fin 4 → Fin 4 → ℂ × ℂ :=
  ![![(1, 0), (1, 0), (1 / 2, (Real.sqrt 3 : ℂ) / 2), (-1 / 2, (Real.sqrt 3 : ℂ) / 2)],
    ![(1, 0), (1, 0), ((Real.sqrt 3 : ℂ) / 2, 1 / 2), ((Real.sqrt 3 : ℂ) / 2, -1 / 2)],
    ![(1 / 2, (Real.sqrt 3 : ℂ) / 2), ((Real.sqrt 3 : ℂ) / 2, 1 / 2),
      (1 / 2, (Real.sqrt 3 : ℂ) / 2), (0, 1)],
    ![(-1 / 2, (Real.sqrt 3 : ℂ) / 2), ((Real.sqrt 3 : ℂ) / 2, -1 / 2),
      (0, 1), (-1 / 2, (Real.sqrt 3 : ℂ) / 2)]]

private def eigen (i j : Fin 4) : ℝ × ℝ :=
  if i = 0 ∧ j = 0 then (1, 1) else
  if i = j then (2, 0) else (3 / 2, 1 / 2)

private lemma angles_unit (i j : Fin 4) :
    (angles i j).1 ^ 2 + (angles i j).2 ^ 2 = 1 := by
  have hs := sqrt_three_sq
  fin_cases i <;> fin_cases j <;> norm_num [angles] <;> ring_nf <;> norm_num [hs]

private lemma spectral (i j : Fin 4) :
    rho i + rho j = rot (angles i j).1 (angles i j).2 *
      diagonal ![((eigen i j).1 : ℂ), ((eigen i j).2 : ℂ)] *
      rot (angles i j).1 (-(angles i j).2) := by
  have hs := sqrt_three_sq
  fin_cases i <;> fin_cases j <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    norm_num [rho, angles, eigen, rot, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.diagonal_fin_two, Matrix.add_apply] <;> ring_nf <;> norm_num [hs]

private lemma kernel (t : ℝ) (i j : Fin 4) :
    trExp (((t / 2 : ℝ) : ℂ) • (rho i + rho j)) =
      if i = 0 ∧ j = 0 then (2 * Real.exp (t / 4) ^ 2 : ℝ) else
      if i = j then (Real.exp (t / 4) ^ 4 + 1 : ℝ) else
      (Real.exp (t / 4) ^ 3 + Real.exp (t / 4) : ℝ) := by
  rw [spectral]
  rw [← Matrix.smul_mul, ← Matrix.mul_smul, ← Matrix.diagonal_smul]
  have hu := angles_unit i j
  have hv : (angles i j).1 ^ 2 + (-(angles i j).2) ^ 2 = 1 := by simpa using hu
  have he := trace_exp_conjugate _ _ (rot_inv _ _ hu) (by simpa using rot_inv _ _ hv)
    (t / 2 * (eigen i j).1) (t / 2 * (eigen i j).2)
  convert he using 1
  · congr 2
    ext a; fin_cases a <;> simp [Complex.ofReal_mul]
  · have h2 : Real.exp (t / 2) = Real.exp (t / 4) ^ 2 := by
      convert Real.exp_nat_mul (t / 4) 2 using 1 <;> congr 1 <;> ring
    have h3 : Real.exp (t / 2 * (3 / 2)) = Real.exp (t / 4) ^ 3 := by
      convert Real.exp_nat_mul (t / 4) 3 using 1 <;> congr 1 <;> ring
    have h4 : Real.exp (t / 2 * 2) = Real.exp (t / 4) ^ 4 := by
      convert Real.exp_nat_mul (t / 4) 4 using 1 <;> congr 1 <;> ring
    rw [← Complex.ofReal_add]
    apply congrArg Complex.ofReal
    by_cases h00 : i = 0 ∧ j = 0
    · simp only [eigen, if_pos h00, mul_one, h2]
      ring
    · by_cases hij : i = j
      · simp only [eigen, if_neg h00, if_pos hij, mul_zero, Real.exp_zero, h4]
      · simp only [eigen, if_neg h00, if_neg hij, h3]
        congr 2
        ring

private def coeff (u : ℝ) : Fin 4 → ℝ := ![-3 * (u + u⁻¹) / 2, 1, 1, 1]

private lemma quadratic (t : ℝ) :
    (∑ i, ∑ j, ((coeff (Real.exp (t / 4)) i * coeff (Real.exp (t / 4)) j : ℝ) : ℂ) *
      trExp (((t / 2 : ℝ) : ℂ) • (rho i + rho j))).re =
      -(3 / 2 : ℝ) * (Real.exp (t / 4) - 1) ^ 4 := by
  simp_rw [kernel]
  simp only [← Complex.ofReal_mul, ← Complex.ofReal_sum, Complex.ofReal_re]
  simp [coeff, Fin.sum_univ_succ]
  field_simp
  ring

/-- The same failure for every nonzero inverse temperature, covering the kernels
`Tr e^{-t(ρ+σ) / 2}` used in the paper's proof scheme. -/
theorem family (t : ℝ) (ht : t ≠ 0) :
    ∃ (ρ : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ) (c : Fin 4 → ℝ), (∀ i, IsDensity (ρ i)) ∧
      (∑ i, ∑ j, ((c i * c j : ℝ) : ℂ) * trExp (((t / 2 : ℝ) : ℂ) • (ρ i + ρ j))).re < 0 := by
  refine ⟨rho, coeff (Real.exp (t / 4)), density, ?_⟩
  rw [quadratic]
  have hu : Real.exp (t / 4) - 1 ≠ 0 := by
    intro h
    have he : Real.exp (t / 4) = 1 := sub_eq_zero.mp h
    have hz := (Real.exp_eq_one_iff (t / 4)).mp he
    apply ht
    linarith
  have hp : 0 < (Real.exp (t / 4) - 1) ^ 4 := by
    simpa only [← pow_mul] using pow_pos (sq_pos_of_ne_zero hu) 2
  nlinarith

theorem result : ¬ claim := by
  intro h
  obtain ⟨ρ, c, hd, hn⟩ := family 1 one_ne_zero
  have hp := h 2 4 ρ c hd
  have hn' : (∑ i, ∑ j, ((c i * c j : ℝ) : ℂ) *
      trExp ((1 / 2 : ℂ) • (ρ i + ρ j))).re < 0 := by
    convert hn using 1; norm_num
  exact (not_lt_of_ge hp) hn'

end D5.S3.Divergence.TraceExpExponentialConvexityRefutation
