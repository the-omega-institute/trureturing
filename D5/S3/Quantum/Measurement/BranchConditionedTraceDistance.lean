/- GID: D5/S3/Quantum/Measurement/BranchConditionedTraceDistance
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/BranchConditionedTraceDistance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Probability weighting controls trace distance after a finite Kraus branch. -/

import D5.S3.Quantum.Foundation.FiniteTraceDistance
import D5.S3.Weil.ZetaLinear.RankTrace

noncomputable section
namespace D5.S3.Quantum.Measurement.BranchConditionedTraceDistance

open BigOperators Matrix
open scoped ComplexOrder MatrixOrder
open D5.S3.Quantum.Foundation.FiniteTraceDistance

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- A finite Kraus branch cannot increase trace distance once the conditioned distance is weighted
by the larger branch probability. The same estimate controls conditioning above a fixed probability
floor. -/
theorem branch_conditioned_trace_distance
    {d : ℕ} {ι : Type*} [Fintype ι]
    (ρ σ : Matrix (Fin d) (Fin d) ℂ)
    (K : ι → Matrix (Fin d) (Fin d) ℂ)
    (hρ : ρ.PosSemidef) (hρtrace : ρ.trace = 1)
    (hσ : σ.PosSemidef) (hσtrace : σ.trace = 1)
    (hB : (∑ i, (K i)ᴴ * K i) ≤ (1 : Matrix (Fin d) (Fin d) ℂ)) :
    let B := ∑ i, (K i)ᴴ * K i
    let Φ := fun X : Matrix (Fin d) (Fin d) ℂ ↦ ∑ i, K i * X * (K i)ᴴ
    let p := (ρ * B).trace.re
    let q := (σ * B).trace.re
    let D := fun X Y : Matrix (Fin d) (Fin d) ℂ ↦ traceNorm (X - Y) / 2
    |p - q| ≤ D ρ σ ∧
      ((0 < p ∧ 0 < q) →
        max p q * D ((1 / p) • Φ ρ) ((1 / q) • Φ σ) ≤ D ρ σ) ∧
      ∀ pStar ε : ℝ, 0 < pStar → pStar ≤ p → D ρ σ ≤ ε → ε < pStar →
        0 < q ∧ D ((1 / p) • Φ ρ) ((1 / q) • Φ σ) ≤ ε / pStar := by
  classical
  let B : Matrix (Fin d) (Fin d) ℂ := ∑ i, (K i)ᴴ * K i
  let Φ : Matrix (Fin d) (Fin d) ℂ → Matrix (Fin d) (Fin d) ℂ :=
    fun X ↦ ∑ i, K i * X * (K i)ᴴ
  let p : ℝ := (ρ * B).trace.re
  let q : ℝ := (σ * B).trace.re
  let D : Matrix (Fin d) (Fin d) ℂ → Matrix (Fin d) (Fin d) ℂ → ℝ :=
    fun X Y ↦ traceNorm (X - Y) / 2
  let A : Matrix (Fin d) (Fin d) ℂ := ρ - σ
  let P : Matrix (Fin d) (Fin d) ℂ := posPart A
  let M : Matrix (Fin d) (Fin d) ℂ := negPart A
  let a : ℝ := (P * B).trace.re
  let b : ℝ := (M * B).trace.re
  change |p - q| ≤ D ρ σ ∧
    ((0 < p ∧ 0 < q) →
      max p q * D ((1 / p) • Φ ρ) ((1 / q) • Φ σ) ≤ D ρ σ) ∧
    ∀ pStar ε : ℝ, 0 < pStar → pStar ≤ p → D ρ σ ≤ ε → ε < pStar →
      0 < q ∧ D ((1 / p) • Φ ρ) ((1 / q) • Φ σ) ≤ ε / pStar
  have htraceNorm_smul_nonneg (r : ℝ) (hr : 0 ≤ r)
      (X : Matrix (Fin d) (Fin d) ℂ) :
      traceNorm (r • X) = r * traceNorm X := by
    obtain ⟨U, hU⟩ := (traceNorm_eq_max_re_tr_U X).1
    apply le_antisymm
    · obtain ⟨V, hV⟩ := (traceNorm_eq_max_re_tr_U (r • X)).1
      rw [← hV]
      have hVX := (traceNorm_eq_max_re_tr_U X).2 ⟨V, rfl⟩
      simpa only [Matrix.mul_smul, Matrix.trace_smul, Complex.real_smul,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero] using
        mul_le_mul_of_nonneg_left hVX hr
    · have hscaled := (traceNorm_eq_max_re_tr_U (r • X)).2
      have hcandidate := hscaled ⟨U, rfl⟩
      rw [← hU]
      simpa only [Matrix.mul_smul, Matrix.trace_smul, Complex.real_smul,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero] using
        hcandidate
  have htraceNorm_smul_real (r : ℝ) (X : Matrix (Fin d) (Fin d) ℂ) :
      traceNorm (r • X) = |r| * traceNorm X := by
    by_cases hr : 0 ≤ r
    · simpa only [abs_of_nonneg hr] using htraceNorm_smul_nonneg r hr X
    · have hneg : 0 ≤ -r := neg_nonneg.mpr (le_of_not_ge hr)
      calc
        traceNorm (r • X) = traceNorm ((-r) • (-X)) := by simp
        _ = (-r) * traceNorm (-X) := htraceNorm_smul_nonneg (-r) hneg (-X)
        _ = |r| * traceNorm X := by
          rw [traceNorm_neg, abs_of_neg (lt_of_not_ge hr)]
  have hBpos : B.PosSemidef := by
    dsimp only [B]
    exact posSemidef_sum Finset.univ fun i _ ↦ posSemidef_conjTranspose_mul_self (K i)
  have hBcomp : (1 - B).PosSemidef := hB
  have hΦpsd (X : Matrix (Fin d) (Fin d) ℂ) (hX : X.PosSemidef) :
      (Φ X).PosSemidef := by
    dsimp only [Φ]
    exact posSemidef_sum Finset.univ fun i _ ↦ hX.mul_mul_conjTranspose_same (K i)
  have hΦsub (X Y : Matrix (Fin d) (Fin d) ℂ) : Φ (X - Y) = Φ X - Φ Y := by
    simp only [Φ, Matrix.mul_sub, Matrix.sub_mul, Finset.sum_sub_distrib]
  have hΦtrace (X : Matrix (Fin d) (Fin d) ℂ) :
      (Φ X).trace = (X * B).trace := by
    dsimp only [Φ, B]
    rw [Matrix.trace_sum, Matrix.mul_sum, Matrix.trace_sum]
    apply Finset.sum_congr rfl
    intro i _
    calc
      (K i * X * (K i)ᴴ).trace = (K i * (X * (K i)ᴴ)).trace := by
        rw [Matrix.mul_assoc]
      _ = (X * ((K i)ᴴ * K i)).trace :=
        (Matrix.trace_mul_cycle' X (K i)ᴴ (K i)).symm
  have hflagMass (X : Matrix (Fin d) (Fin d) ℂ) :
      (Φ X).trace.re + (X * (1 - B)).trace.re = X.trace.re := by
    rw [hΦtrace, Matrix.mul_sub, Matrix.mul_one, Matrix.trace_sub, Complex.sub_re]
    ring
  have hfailureNonneg (X : Matrix (Fin d) (Fin d) ℂ) (hX : X.PosSemidef) :
      0 ≤ (X * (1 - B)).trace.re :=
    RHLinalg.trace_mul_nonneg_of_posSemidef hX hBcomp
  have hbranchNonneg (X : Matrix (Fin d) (Fin d) ℂ) (hX : X.PosSemidef) :
      0 ≤ (X * B).trace.re :=
    RHLinalg.trace_mul_nonneg_of_posSemidef hX hBpos
  have hbranchLeTrace (X : Matrix (Fin d) (Fin d) ℂ) (hX : X.PosSemidef) :
      (X * B).trace.re ≤ X.trace.re := by
    have hmass := hflagMass X
    rw [hΦtrace] at hmass
    linarith [hfailureNonneg X hX]
  have hΦtraceNorm (X : Matrix (Fin d) (Fin d) ℂ) (hX : X.PosSemidef) :
      traceNorm (Φ X) = (X * B).trace.re := by
    have hnorm := congrArg Complex.re (traceNorm_of_posSemidef (hΦpsd X hX))
    rw [hΦtrace] at hnorm
    simpa using hnorm
  have hAherm : A.IsHermitian := hρ.isHermitian.sub hσ.isHermitian
  have hAtrace : A.trace = 0 := by
    simp only [A, Matrix.trace_sub, hρtrace, hσtrace, sub_self]
  have hPpos : P.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.posPart_nonneg A)
  have hMpos : M.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.negPart_nonneg A)
  have hAdecomp : A = P - M := (CFC.posPart_sub_negPart A hAherm).symm
  have hPMtrace : P.trace.re = M.trace.re := by
    have htrace := congrArg (fun X : Matrix (Fin d) (Fin d) ℂ ↦ X.trace.re) hAdecomp
    rw [hAtrace, Matrix.trace_sub, Complex.sub_re] at htrace
    norm_num at htrace
    linarith
  have hJordan : traceNorm A = P.trace.re + M.trace.re :=
    trace_norm_jordan_mass A hAherm
  have hmass : traceNorm A = 2 * P.trace.re := by linarith
  have haNonneg : 0 ≤ a := hbranchNonneg P hPpos
  have hbNonneg : 0 ≤ b := hbranchNonneg M hMpos
  have haLe : a ≤ P.trace.re := hbranchLeTrace P hPpos
  have hbLe : b ≤ P.trace.re := by
    rw [hPMtrace]
    exact hbranchLeTrace M hMpos
  have hpq : p - q = (A * B).trace.re := by
    simp only [p, q, A, Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re]
  have hpqAB : p - q = a - b := by
    rw [hpq, hAdecomp, Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re]
  have habsLe : |a - b| ≤ P.trace.re := by
    by_cases hab : a ≤ b
    · rw [abs_of_nonpos (sub_nonpos.mpr hab)]
      linarith
    · rw [abs_of_nonneg (sub_nonneg.mpr (le_of_not_ge hab))]
      linarith
  have hprobability : |p - q| ≤ D ρ σ := by
    rw [hpqAB]
    dsimp only [D, A] at *
    linarith
  have hΦA : Φ A = Φ P - Φ M := by
    rw [hAdecomp, hΦsub]
  have hΦdifference : Φ ρ - Φ σ = Φ A := by
    rw [show A = ρ - σ from rfl]
    exact (hΦsub ρ σ).symm
  have hflagContraction : traceNorm (Φ A) + |p - q| ≤ traceNorm A := by
    have hnorm : traceNorm (Φ A) ≤ a + b := by
      rw [hΦA, sub_eq_add_neg]
      calc
        traceNorm (Φ P + -Φ M) ≤ traceNorm (Φ P) + traceNorm (-Φ M) :=
          traceNorm_add_le _ _
        _ = a + b := by rw [traceNorm_neg, hΦtraceNorm P hPpos, hΦtraceNorm M hMpos]
    rw [hpqAB]
    by_cases hab : a ≤ b
    · rw [abs_of_nonpos (sub_nonpos.mpr hab)]
      linarith
    · rw [abs_of_nonneg (sub_nonneg.mpr (le_of_not_ge hab))]
      linarith
  have hconditioned : (0 < p ∧ 0 < q) →
      max p q * D ((1 / p) • Φ ρ) ((1 / q) • Φ σ) ≤ D ρ σ := by
    rintro ⟨hp, hq⟩
    let ρΦ : Matrix (Fin d) (Fin d) ℂ := (1 / p) • Φ ρ
    let σΦ : Matrix (Fin d) (Fin d) ℂ := (1 / q) • Φ σ
    have hρΦnorm : traceNorm ρΦ = 1 := by
      dsimp only [ρΦ]
      rw [htraceNorm_smul_nonneg (1 / p) (by positivity), hΦtraceNorm ρ hρ]
      change (1 / p) * p = 1
      field_simp [hp.ne']
    have hσΦnorm : traceNorm σΦ = 1 := by
      dsimp only [σΦ]
      rw [htraceNorm_smul_nonneg (1 / q) (by positivity), hΦtraceNorm σ hσ]
      change (1 / q) * q = 1
      field_simp [hq.ne']
    have hpComplex : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
    have hqComplex : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
    have hpIdentity : p • (ρΦ - σΦ) = Φ ρ - Φ σ + (q - p) • σΦ := by
      ext i j
      simp only [ρΦ, σΦ, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
        Complex.real_smul]
      push_cast
      field_simp [hpComplex, hqComplex]
      ring
    have hqIdentity : q • (ρΦ - σΦ) = Φ ρ - Φ σ + (q - p) • ρΦ := by
      ext i j
      simp only [ρΦ, σΦ, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
        Complex.real_smul]
      push_cast
      field_simp [hpComplex, hqComplex]
      ring
    have hpBound : p * traceNorm (ρΦ - σΦ) ≤ traceNorm A := by
      rw [← htraceNorm_smul_nonneg p hp.le, hpIdentity]
      calc
        traceNorm (Φ ρ - Φ σ + (q - p) • σΦ) ≤
            traceNorm (Φ ρ - Φ σ) + traceNorm ((q - p) • σΦ) :=
          traceNorm_add_le _ _
        _ = traceNorm (Φ A) + |p - q| := by
          rw [hΦdifference, htraceNorm_smul_real, hσΦnorm, mul_one, abs_sub_comm]
        _ ≤ traceNorm A := hflagContraction
    have hqBound : q * traceNorm (ρΦ - σΦ) ≤ traceNorm A := by
      rw [← htraceNorm_smul_nonneg q hq.le, hqIdentity]
      calc
        traceNorm (Φ ρ - Φ σ + (q - p) • ρΦ) ≤
            traceNorm (Φ ρ - Φ σ) + traceNorm ((q - p) • ρΦ) :=
          traceNorm_add_le _ _
        _ = traceNorm (Φ A) + |p - q| := by
          rw [hΦdifference, htraceNorm_smul_real, hρΦnorm, mul_one, abs_sub_comm]
        _ ≤ traceNorm A := hflagContraction
    change max p q * (traceNorm (ρΦ - σΦ) / 2) ≤ traceNorm A / 2
    rcases le_total p q with hpqle | hqple
    · rw [max_eq_right hpqle]
      linarith
    · rw [max_eq_left hqple]
      linarith
  refine ⟨hprobability, hconditioned, ?_⟩
  intro pStar ε hpStar hpFloor hDε hεFloor
  have hpqLe : |p - q| ≤ ε := hprobability.trans (hDε.trans le_rfl)
  have hqPos : 0 < q := by
    have hsub : p - q ≤ ε := (le_abs_self (p - q)).trans hpqLe
    linarith
  have hpPos : 0 < p := lt_of_lt_of_le hpStar hpFloor
  have hweighted := hconditioned ⟨hpPos, hqPos⟩
  have hDnonneg : 0 ≤ D ((1 / p) • Φ ρ) ((1 / q) • Φ σ) := by
    exact div_nonneg (traceNorm_nonneg _) (by norm_num)
  have hpStarWeighted :
      pStar * D ((1 / p) • Φ ρ) ((1 / q) • Φ σ) ≤ ε := by
    have hpStarMax : pStar ≤ max p q := hpFloor.trans (le_max_left _ _)
    have := mul_le_mul_of_nonneg_right hpStarMax hDnonneg
    linarith
  refine ⟨hqPos, ?_⟩
  apply (le_div_iff₀ hpStar).2
  simpa [mul_comm] using hpStarWeighted

#print axioms branch_conditioned_trace_distance

end D5.S3.Quantum.Measurement.BranchConditionedTraceDistance
