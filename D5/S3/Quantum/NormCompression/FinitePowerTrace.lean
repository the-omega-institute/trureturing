/- GID: D5/S3/Quantum/NormCompression/FinitePowerTrace
   generality: G
   mirror-B: none(waiver:ordinary-finite-power-supplier)
   mirror-E: none(waiver:ordinary-finite-power-supplier)
   anchors: []
   utility: none
   digest: Actual Schatten trace-power supplier for nonnegative two-row tables. -/

import D5.S3.Quantum.NormCompression.SchattenContinuity
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
This module supplies the actual finite two-row operator trace power, its
continuity on the full cone, and nonnegative degree-one homogeneity.
The curvature and local-output gluing proofs consume this supplier separately.
-/

noncomputable section

namespace D5.S3.Quantum.NormCompression.FinitePowerConcavity

open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open D5.S3.Quantum.NormCompression.UpperBranchReduction

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {m : Type*} [Fintype m] [DecidableEq m]

local instance {n : Type*} [Fintype n] [DecidableEq n] : Pow (Matrix n n ℂ) ℝ := ⟨CFC.rpow⟩

/-! The actual finite-power column matrix.  The real nonnegative table is
    embedded into the complex matrix space used by the Schatten supplier. -/
def Aq (q : ℝ) (W : Matrix (Fin 2) m ℝ) : Matrix (Fin 2) m ℂ :=
  fun b j => (W b j ^ (1 / (2 * q)) : ℝ)

/-! `Fq` is the Schatten trace power of the actual matrix `Aq`. -/
def Fq (q : ℝ) (W : Matrix (Fin 2) m ℝ) : ℝ :=
  schattenPow (2 * q) (Aq q W)

theorem Fq_nonneg (q : ℝ) (W : Matrix (Fin 2) m ℝ) : 0 ≤ Fq q W := by
  exact schattenPow_nonneg (2 * q) (Aq q W)

/-- The row Gram formula has two eigenvalues regardless of the column type. -/
theorem Fq_eq_rowGram_power {q : ℝ} (hq : 0 < q)
    (W : Matrix (Fin 2) m ℝ) :
    Fq q W = ∑ b : Fin 2,
      ((Matrix.isHermitian_mul_conjTranspose_self (Aq q W)).eigenvalues b) ^ q := by
  unfold Fq
  rw [schattenPow_eq_rowGram (2 * q) (by positivity) (Aq q W)]
  congr 1
  ext b
  congr 1
  ring

/-- Identification with the actual operator trace power on the row Gram matrix. -/
theorem Fq_eq_trace_rpow {q : ℝ} (hq : 0 < q)
    (W : Matrix (Fin 2) m ℝ) :
    Fq q W = (CFC.rpow (Aq q W * (Aq q W)ᴴ) q).trace.re := by
  rw [Fq_eq_rowGram_power hq, CFC.rpow_eq_pow, CFC.rpow_eq_cfc_real
    (Matrix.posSemidef_self_mul_conjTranspose (Aq q W)).nonneg,
    D5.S3.Resource.LogDet.PathSpectralClassical.trace_cfc_eq_sum _
      (Matrix.isHermitian_mul_conjTranspose_self (Aq q W))]

private theorem Fq_eq_schattenPow_rowGram {q : ℝ} (hq : 0 < q)
    (W : Matrix (Fin 2) m ℝ) :
    Fq q W = schattenPow q (Aq q W * (Aq q W)ᴴ) := by
  rw [Fq, schattenPow_eq_eigenPow_rowGram (2 * q) (by positivity),
    schattenPow_eq_eigenPow q hq _
      (Matrix.posSemidef_self_mul_conjTranspose (Aq q W))]
  congr 1
  ring

/-- The entrywise root is continuous at every zero entry as well. -/
theorem continuous_Aq {q : ℝ} (hq : 0 < q) :
    Continuous (Aq q : Matrix (Fin 2) m ℝ → Matrix (Fin 2) m ℂ) := by
  apply continuous_pi
  intro b
  apply continuous_pi
  intro j
  exact Complex.continuous_ofReal.comp
    (((continuous_apply j).comp (continuous_apply b)).rpow_const
      (fun _ => Or.inr (by positivity)))

/-- Continuity of the actual trace power on the entire matrix space, hence the full cone. -/
theorem continuous_Fq {q : ℝ} (hq : 0 < q) :
    Continuous (Fq q : Matrix (Fin 2) m ℝ → ℝ) := by
  have hgram : Continuous (fun W : Matrix (Fin 2) m ℝ =>
      Aq q W * (Aq q W)ᴴ) :=
    (continuous_Aq hq).matrix_mul (continuous_Aq hq).matrix_conjTranspose
  have hcont :=
    (D5.S3.Quantum.NormCompression.SchattenContinuity.continuous_schattenPow
      (n := 2) hq).comp hgram
  convert hcont using 1
  funext W
  exact Fq_eq_schattenPow_rowGram hq W

theorem Aq_smul {q c : ℝ} (hc : 0 ≤ c)
    (W : Matrix (Fin 2) m ℝ) (hW : ∀ b j, 0 ≤ W b j) :
    Aq q (c • W) = ((c ^ (1 / (2 * q)) : ℝ) : ℂ) • Aq q W := by
  ext b j
  change (((c * W b j) ^ (1 / (2 * q)) : ℝ) : ℂ) =
    ((c ^ (1 / (2 * q)) : ℝ) : ℂ) * ((W b j ^ (1 / (2 * q)) : ℝ) : ℂ)
  rw [Real.mul_rpow hc (hW b j), Complex.ofReal_mul]

/-- Exact degree-one homogeneity for every nonnegative scalar, including zero. -/
theorem Fq_smul {q c : ℝ} (hq : 0 < q) (hc : 0 ≤ c)
    (W : Matrix (Fin 2) m ℝ) (hW : ∀ b j, 0 ≤ W b j) :
    Fq q (c • W) = c * Fq q W := by
  unfold Fq
  rw [Aq_smul hc W hW]
  have hscale : c ^ (1 / (2 * q)) = Real.sqrt (c ^ (1 / q)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hc]
    congr 1
    field_simp [hq.ne']
    <;> ring
  rw [hscale, schattenPow_sqrt_smul (2 * q) (by positivity)
    (c ^ (1 / q)) (Real.rpow_nonneg hc _) (Aq q W), ← Real.rpow_mul hc]
  rw [show 1 / q * (2 * q / 2) = (1 : ℝ) by field_simp [hq.ne'], Real.rpow_one]

/-- Every radial direction has zero actual second derivative, including axial supports. -/
theorem radial_second_derivative_zero {q : ℝ} (hq : 0 < q) (c : ℝ)
    (W : Matrix (Fin 2) m ℝ) (hW : ∀ b j, 0 ≤ W b j) :
    deriv (deriv (fun t : ℝ => Fq q ((1 + t * c) • W))) 0 = 0 := by
  have hc : Continuous (fun t : ℝ => 1 + t * c) := by fun_prop
  have hpos : ∀ᶠ t : ℝ in nhds 0, 0 < 1 + t * c := by
    exact (hc.tendsto 0).eventually (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1 + 0 * c))
  have heq : (fun t : ℝ => Fq q ((1 + t * c) • W)) =ᶠ[nhds 0]
      (fun t : ℝ => (1 + t * c) * Fq q W) := by
    filter_upwards [hpos] with t ht
    exact Fq_smul hq ht.le W hW
  have hd : deriv (fun t : ℝ => (1 + t * c) * Fq q W) = fun _ => c * Fq q W := by
    funext t
    simpa using (((hasDerivAt_const t (1 : ℝ)).add
      ((hasDerivAt_id t).mul_const c)).mul_const (Fq q W)).deriv
  have h := heq.deriv.deriv_eq
  rw [hd] at h
  simpa using h

#print axioms continuous_Fq
#print axioms Fq_smul

end D5.S3.Quantum.NormCompression.FinitePowerConcavity
