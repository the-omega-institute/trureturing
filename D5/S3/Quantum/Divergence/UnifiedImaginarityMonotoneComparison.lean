/- GID: D5/S3/Quantum/Divergence/UnifiedImaginarityMonotoneComparison
   generality: I
   mirror-B: D5/B/S3/Quantum/Divergence/UnifiedImaginarityMonotoneComparison
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Unified imaginarity minimized over real states is bounded by conjugate divergence. -/

import D5.S3.Quantum.Information.SLDSpectralEnergy
import D5.S3.Quantum.Tomography.MUB.MUBCompletionRelativeGramEquivalence
import D5.S3.Resource.LogDet.PathSpectralClassical

/-! The real part of a density matrix compares the two unified imaginarity measures. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Quantum.Divergence.UnifiedImaginarityMonotoneComparison

open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder NNReal
open Matrix
open D5.S3.Quantum.Information.SLDSpectralEnergy (IsDensity)
open D5.S3.Quantum.Tomography.MUB.MUBCompletionRelativeGramEquivalence (entrywiseConj)


/-- The unified relative entropy for real parameters. -/
def unifiedDivergence {d : ℕ} (α β : ℝ) (ρ σ : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  (((ρ ^ α * σ ^ (1 - α)).trace.re) ^ β - 1) / ((α - 1) * β)

/-- Imaginarity measured by divergence from the conjugate state. -/
def imaginarityH {d : ℕ} (α β : ℝ) (ρ : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  unifiedDivergence α β ρ (entrywiseConj ρ)

/-- Imaginarity measured by the infimum of divergences from real states. -/
def imaginarityE {d : ℕ} (α β : ℝ) (ρ : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  sInf {x | ∃ σ, IsDensity σ ∧ entrywiseConj σ = σ ∧ x = unifiedDivergence α β ρ σ}

/-- The comparison includes every finite positive dimension and singular density matrices. -/
def claim : Prop :=
  ∀ (d : ℕ), 1 ≤ d → ∀ ρ : Matrix (Fin d) (Fin d) ℂ, IsDensity ρ →
    ∀ α ∈ Set.Ioo (0 : ℝ) 1, ∀ β ∈ Set.Ioc (0 : ℝ) 1,
      imaginarityE α β ρ ≤ imaginarityH α β ρ

variable {d : ℕ} {ρ σ : Matrix (Fin d) (Fin d) ℂ} {α β : ℝ}

private def realCompetitor (ρ : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d) (Fin d) ℂ := (1 / 2 : ℂ) • (ρ + entrywiseConj ρ)

private lemma conjugate_state (hρ : IsDensity ρ) : IsDensity (entrywiseConj ρ) := by
  have he : entrywiseConj ρ = ρ.transpose := by
    ext i j
    simpa only [entrywiseConj, Matrix.transpose_apply, Matrix.conjTranspose_apply] using
      congrArg (fun M : Matrix (Fin d) (Fin d) ℂ => M j i) hρ.1.isHermitian.eq
  rw [he]
  exact ⟨hρ.1.transpose, by simpa using hρ.2⟩

private lemma real_competitor (hρ : IsDensity ρ) :
    IsDensity (realCompetitor ρ) ∧ entrywiseConj (realCompetitor ρ) = realCompetitor ρ := by
  have hc := conjugate_state hρ
  constructor
  · refine ⟨(hρ.1.add hc.1).smul
      (Complex.nonneg_iff.mpr ⟨by norm_num, by norm_num⟩ : (0 : ℂ) ≤ 1 / 2), ?_⟩
    simp only [realCompetitor, Matrix.trace_smul, Matrix.trace_add, hρ.2, hc.2]
    norm_num
  · ext i j
    simp only [entrywiseConj, realCompetitor, Matrix.smul_apply, Matrix.add_apply,
      smul_eq_mul, star_mul, star_add, star_star]
    norm_num
    ring

private lemma overlap_nonneg (ρ σ : Matrix (Fin d) (Fin d) ℂ) (α : ℝ) :
    0 ≤ (ρ ^ α * σ ^ (1 - α)).trace.re := by
  exact RHLinalg.trace_mul_nonneg_of_posSemidef
    (CFC.rpow_nonneg (a := ρ) (y := α)).posSemidef
    (CFC.rpow_nonneg (a := σ) (y := 1 - α)).posSemidef

private lemma overlap_le_one (hρ : IsDensity ρ) (hσ : IsDensity σ)
    (hα : α ∈ Set.Ioo (0 : ℝ) 1) :
    (ρ ^ α * σ ^ (1 - α)).trace.re ≤ 1 := by
  let A := ρ ^ α
  let B := σ ^ (1 - α)
  have hA : A.PosSemidef := CFC.rpow_nonneg.posSemidef
  have hB : B.PosSemidef := CFC.rpow_nonneg.posSemidef
  have hsA : ∑ i, hA.isHermitian.eigenvalues i ^ (1 / α) = 1 := by
    rw [← D5.S3.Resource.LogDet.PathSpectralClassical.trace_cfc_eq_sum A hA.isHermitian
      (fun x : ℝ => x ^ (1 / α)),
      ← CFC.rpow_eq_cfc_real hA.nonneg]
    dsimp [A]
    rw [CFC.rpow_rpow_of_exponent_nonneg ρ α (1 / α) hα.1.le
      (one_div_pos.mpr hα.1).le
      hρ.1.nonneg, mul_one_div_cancel hα.1.ne', CFC.rpow_one ρ hρ.1.nonneg, hρ.2]
    simp
  have hsB : ∑ i, hB.isHermitian.eigenvalues i ^ (1 / (1 - α)) = 1 := by
    rw [← D5.S3.Resource.LogDet.PathSpectralClassical.trace_cfc_eq_sum B hB.isHermitian
      (fun x : ℝ => x ^ (1 / (1 - α))),
      ← CFC.rpow_eq_cfc_real hB.nonneg]
    dsimp [B]
    rw [CFC.rpow_rpow_of_exponent_nonneg σ (1 - α) (1 / (1 - α))
      (by linarith [hα.2]) (one_div_pos.mpr (sub_pos.mpr hα.2)).le hσ.1.nonneg,
      mul_one_div_cancel (by linarith [hα.2] : 1 - α ≠ 0),
      CFC.rpow_one σ hσ.1.nonneg, hσ.2]
    simp
  let W := star (hA.isHermitian.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) *
    (hB.isHermitian.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)
  have hW : W ∈ Matrix.unitaryGroup (Fin d) ℂ :=
    mul_mem (Unitary.star_mem hA.isHermitian.eigenvectorUnitary.2)
      hB.isHermitian.eigenvectorUnitary.2
  obtain ⟨hS, hrow, hcol⟩ := mem_doublyStochastic_iff_sum.mp
    (RHLinalg.normSqMatrix_mem_doublyStochastic_of_unitary hW)
  change (A * B).trace.re ≤ 1
  have hbilinear := RHLinalg.re_trace_mul_eq_eigenvalue_bilinear hA.isHermitian hB.isHermitian
  change (A * B).trace.re = _ at hbilinear
  rw [hbilinear]
  calc
    _ ≤ ∑ i, ∑ j, (α * hA.isHermitian.eigenvalues i ^ (1 / α) +
        (1 - α) * hB.isHermitian.eigenvalues j ^ (1 / (1 - α))) *
          RHLinalg.normSqMatrix W i j := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      have hy := Real.geom_mean_le_arith_mean2_weighted hα.1.le
        (by linarith [hα.2] : 0 ≤ 1 - α)
        (Real.rpow_nonneg (hA.eigenvalues_nonneg i) (1 / α))
        (Real.rpow_nonneg (hB.eigenvalues_nonneg j) (1 / (1 - α)))
        (by ring : α + (1 - α) = 1)
      rw [← Real.rpow_mul (hA.eigenvalues_nonneg i),
        ← Real.rpow_mul (hB.eigenvalues_nonneg j),
        one_div_mul_cancel hα.1.ne',
        one_div_mul_cancel (by linarith [hα.2] : 1 - α ≠ 0), Real.rpow_one,
        Real.rpow_one] at hy
      convert mul_le_mul_of_nonneg_right hy (hS i j) using 1 <;> dsimp [W] <;> ring
    _ = 1 := by
      simp only [add_mul, Finset.sum_add_distrib]
      rw [Finset.sum_comm (f := fun i j =>
        (1 - α) * hB.isHermitian.eigenvalues j ^ (1 / (1 - α)) *
          RHLinalg.normSqMatrix W i j)]
      simp only [← Finset.mul_sum, hrow, hcol, mul_one, hsA, hsB]
      ring

private lemma midpoint_overlap (hρ : IsDensity ρ) (hα : α ∈ Set.Ioo (0 : ℝ) 1) :
    (1 + (ρ ^ α * (entrywiseConj ρ) ^ (1 - α)).trace.re) / 2 ≤
      (ρ ^ α * (realCompetitor ρ) ^ (1 - α)).trace.re := by
  have hc := conjugate_state hρ
  have ht : (1 / 2 : ℝ) • ρ + (1 / 2 : ℝ) • entrywiseConj ρ = realCompetitor ρ := by
    ext i j
    simp [realCompetitor, Matrix.smul_apply, Matrix.add_apply, Complex.real_smul]
    ring
  have hop := (CFC.concaveOn_rpow (A := Matrix (Fin d) (Fin d) ℂ)
    (p := 1 - α) ⟨by linarith [hα.2], by linarith [hα.1]⟩).2
    hρ.1.nonneg hc.1.nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  rw [ht] at hop
  have hm := RHLinalg.trace_mul_nonneg_of_posSemidef
    (CFC.rpow_nonneg (a := ρ) (y := α)).posSemidef (Matrix.le_iff.mp hop)
  have hp : ρ ^ α * ρ ^ (1 - α) = ρ := by
    let a : ℝ≥0 := ⟨α, hα.1.le⟩
    let b : ℝ≥0 := ⟨1 - α, by linarith [hα.2]⟩
    have hab : a + b = 1 := by
      apply Subtype.ext
      change α + (1 - α) = 1
      ring
    have he := CFC.nnrpow_add (a := ρ) (x := a) (y := b)
      (show 0 < a from hα.1) (show 0 < b by exact sub_pos.mpr hα.2)
    rw [hab, CFC.nnrpow_one ρ hρ.1.nonneg,
      CFC.nnrpow_eq_rpow (show 0 < a from hα.1),
      CFC.nnrpow_eq_rpow (show 0 < b from sub_pos.mpr hα.2)] at he
    exact he.symm
  change 0 ≤ (ρ ^ α * ((realCompetitor ρ) ^ (1 - α) -
    ((1 / 2 : ℝ) • ρ ^ (1 - α) + (1 / 2 : ℝ) • (entrywiseConj ρ) ^ (1 - α)))).trace.re at hm
  simp only [mul_sub, Matrix.mul_add, Matrix.mul_smul, Matrix.trace_sub, Matrix.trace_add,
    Matrix.trace_smul, Complex.sub_re, Complex.add_re, Complex.smul_re, smul_eq_mul,
    hp, hρ.2, Complex.one_re] at hm
  linarith

private lemma scalar_midpoint {q r : ℝ} (hq : 0 ≤ q) (hr : (1 + q) / 2 ≤ r)
    (hβ : β ∈ Set.Ioc (0 : ℝ) 1) :
    (1 + q ^ β) / 2 ≤ r ^ β := by
  have hc := (Real.concaveOn_rpow hβ.1.le hβ.2).2
    (show (1 : ℝ) ∈ Set.Ici 0 by norm_num) hq
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  have hm : (1 + q ^ β) / 2 ≤ ((1 + q) / 2) ^ β := by
    simpa only [smul_eq_mul, one_mul, Real.one_rpow,
      show (1 / 2 : ℝ) * 1 + 1 / 2 * q = (1 + q) / 2 by ring,
      show (1 / 2 : ℝ) * 1 + 1 / 2 * q ^ β = (1 + q ^ β) / 2 by ring] using hc
  exact hm.trans (Real.rpow_le_rpow (by positivity) hr hβ.1.le)

private lemma divergence_nonneg (hρ : IsDensity ρ) (hσ : IsDensity σ)
    (hα : α ∈ Set.Ioo (0 : ℝ) 1) (hβ : β ∈ Set.Ioc (0 : ℝ) 1) :
    0 ≤ unifiedDivergence α β ρ σ := by
  have hq0 := overlap_nonneg ρ σ α
  have hq1 := overlap_le_one hρ hσ hα
  have hp : (ρ ^ α * σ ^ (1 - α)).trace.re ^ β ≤ 1 := by
    simpa using Real.rpow_le_rpow hq0 hq1 hβ.1.le
  exact div_nonneg_of_nonpos (by linarith) (by nlinarith [hα.2, hβ.1])

private lemma competitor_half (hρ : IsDensity ρ) (hα : α ∈ Set.Ioo (0 : ℝ) 1)
    (hβ : β ∈ Set.Ioc (0 : ℝ) 1) :
    unifiedDivergence α β ρ (realCompetitor ρ) ≤ imaginarityH α β ρ / 2 := by
  have hs := scalar_midpoint (overlap_nonneg ρ (entrywiseConj ρ) α) (midpoint_overlap hρ hα) hβ
  have hd : (α - 1) * β < 0 := mul_neg_of_neg_of_pos (by linarith [hα.2]) hβ.1
  unfold imaginarityH unifiedDivergence
  rw [div_right_comm ((ρ ^ α * (entrywiseConj ρ) ^ (1 - α)).trace.re ^ β - 1)
    ((α - 1) * β) 2]
  rw [div_le_div_right_of_neg hd]
  linarith

private lemma values_bddBelow (hρ : IsDensity ρ) (hα : α ∈ Set.Ioo (0 : ℝ) 1)
    (hβ : β ∈ Set.Ioc (0 : ℝ) 1) :
    BddBelow {x | ∃ σ, IsDensity σ ∧ entrywiseConj σ = σ ∧ x = unifiedDivergence α β ρ σ} := by
  refine ⟨0, ?_⟩
  rintro x ⟨σ, hσ, _, rfl⟩
  exact divergence_nonneg hρ hσ hα hβ

private lemma inf_le_competitor (hρ : IsDensity ρ) (hα : α ∈ Set.Ioo (0 : ℝ) 1)
    (hβ : β ∈ Set.Ioc (0 : ℝ) 1) :
    imaginarityE α β ρ ≤ unifiedDivergence α β ρ (realCompetitor ρ) := by
  apply csInf_le (values_bddBelow hρ hα hβ)
  exact ⟨realCompetitor ρ, (real_competitor hρ).1, (real_competitor hρ).2, rfl⟩

/-- The real part of a state supplies a competitor with at most half the conjugate divergence. -/
theorem result : claim := by
  intro d _ ρ hρ α hα β hβ
  have hH : 0 ≤ imaginarityH α β ρ :=
    divergence_nonneg hρ (conjugate_state hρ) hα hβ
  calc
    imaginarityE α β ρ ≤ unifiedDivergence α β ρ (realCompetitor ρ) :=
      inf_le_competitor hρ hα hβ
    _ ≤ imaginarityH α β ρ / 2 := competitor_half hρ hα hβ
    _ ≤ imaginarityH α β ρ := by linarith

end D5.S3.Quantum.Divergence.UnifiedImaginarityMonotoneComparison
