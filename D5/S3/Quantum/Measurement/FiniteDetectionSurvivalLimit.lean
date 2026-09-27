/- GID: D5/S3/Quantum/Measurement/FiniteDetectionSurvivalLimit
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/FiniteDetectionSurvivalLimit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Survival effects converge to the dark-space projection. -/

import D5.S3.Quantum.Measurement.FiniteDetectionDarkBlockContraction

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit

open Filter Matrix Metric
open scoped ComplexOrder Matrix.Norms.L2Operator MatrixOrder Topology
open D5.S3.Quantum.Measurement.FiniteDetectionDarkBlockContraction

/-- The vectors whose click amplitudes vanish after every number of no-click steps. -/
def darkSpace {d : ℕ} {ι : Type*}
    (Q : Matrix (Fin d) (Fin d) ℂ) (L : ι → Matrix (Fin d) (Fin d) ℂ) :
    Submodule ℂ (EuclideanSpace ℂ (Fin d)) :=
  ⨅ n : ℕ, ⨅ x : ι, LinearMap.ker (Matrix.toEuclideanLin (L x * Q ^ n))

/-- The matrix of the orthogonal projection onto the dark space. -/
def darkProjection {d : ℕ} {ι : Type*}
    (Q : Matrix (Fin d) (Fin d) ℂ) (L : ι → Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d) (Fin d) ℂ :=
  (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)).symm (darkSpace Q L).starProjection

/-- **Single-Kraus survival limit.** For a complete finite measurement with no-click operator
`Q`, the survival effects `(Qᴴ)ᴺ Qᴺ` converge to the orthogonal projection onto the vectors never
detected by any click operator. Consequently every matrix-weighted trace has the corresponding
projected limit. The zero-dimensional case is included. -/
theorem finite_detection_survival_limit {d : ℕ} {ι : Type*} [Fintype ι]
    (Q : Matrix (Fin d) (Fin d) ℂ) (L : ι → Matrix (Fin d) (Fin d) ℂ)
    (hcomp : Qᴴ * Q + ∑ x, (L x)ᴴ * L x = 1) :
    Tendsto (fun N => (Qᴴ) ^ N * Q ^ N) atTop (𝓝 (darkProjection Q L)) ∧
      ∀ ρ : Matrix (Fin d) (Fin d) ℂ,
        Tendsto (fun N => (ρ * ((Qᴴ) ^ N * Q ^ N)).trace) atTop
          (𝓝 (ρ * darkProjection Q L).trace) := by
  classical
  by_cases hd : d = 0
  · subst d
    constructor
    · convert tendsto_const_nhds using 1
      funext N
      exact Subsingleton.elim _ _
    · intro ρ
      convert tendsto_const_nhds using 1
      funext N
      congr 1
  letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hd)
  obtain ⟨g, c, hgpos, hgle, hc_nonneg, hc_le_one, hc_step, _hP_le, _hfactor,
    _hPc_nonneg, _hcontraction, hsurvival_norm, _hgap, _hblock⟩ :=
    dark_block_contraction Q L hcomp hd
  change ∀ N, ‖(Qᴴ) ^ N * Q ^ N - darkProjection Q L‖ ≤ c N at hsurvival_norm
  let a : ℝ := 1 - g
  have ha_nonneg : 0 ≤ a := sub_nonneg.mpr hgle
  have ha_lt : a < 1 := sub_lt_self 1 hgpos
  have hc_iter : ∀ n k, c (n + k * d) ≤ a ^ k := by
    intro n k
    induction k with
    | zero => simpa only [Nat.zero_mul, add_zero, pow_zero] using hc_le_one n
    | succ k ih =>
        calc
          c (n + k.succ * d) = c ((n + k * d) + d) := by
            rw [Nat.succ_mul, add_assoc]
          _ ≤ a * c (n + k * d) := by simpa only [a] using hc_step (n + k * d)
          _ ≤ a * a ^ k := mul_le_mul_of_nonneg_left ih ha_nonneg
          _ = a ^ k.succ := by rw [pow_succ']
  have hc_bound : ∀ N, c N ≤ a ^ (N / d) := by
    intro N
    have hdecomp : N = N % d + (N / d) * d := by
      rw [Nat.mul_comm, Nat.mod_add_div]
    calc
      c N = c (N % d + (N / d) * d) := congrArg c hdecomp
      _ ≤ a ^ (N / d) := hc_iter (N % d) (N / d)
  have hc_tendsto : Tendsto c atTop (𝓝 0) := by
    apply squeeze_zero hc_nonneg hc_bound
    exact (_root_.tendsto_pow_atTop_nhds_zero_of_lt_one ha_nonneg ha_lt).comp
      (Nat.tendsto_div_const_atTop hd)
  have hmatrix : Tendsto (fun N => (Qᴴ) ^ N * Q ^ N) atTop
      (𝓝 (darkProjection Q L)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    exact squeeze_zero (fun N => norm_nonneg _) hsurvival_norm hc_tendsto
  refine ⟨hmatrix, fun ρ => ?_⟩
  let tr : Matrix (Fin d) (Fin d) ℂ →L[ℂ] ℂ :=
    LinearMap.toContinuousLinearMap (Matrix.traceLinearMap (Fin d) ℂ ℂ)
  have hmul : Tendsto (fun N => ρ * ((Qᴴ) ^ N * Q ^ N)) atTop
      (𝓝 (ρ * darkProjection Q L)) := tendsto_const_nhds.mul hmatrix
  have htrace := (tr.continuous.tendsto (ρ * darkProjection Q L)).comp hmul
  refine htrace.congr' (Eventually.of_forall fun N => ?_)
  rfl

#print axioms finite_detection_survival_limit

end D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit
