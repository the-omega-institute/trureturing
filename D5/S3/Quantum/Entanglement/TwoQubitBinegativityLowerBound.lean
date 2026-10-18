/- GID: D5/S3/Quantum/Entanglement/TwoQubitBinegativityLowerBound
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/TwoQubitBinegativityLowerBound
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The sharp lower bound on two-qubit binegativity at fixed negativity. -/

import D5.S3.Quantum.Entanglement.TwoQubitBinegativityUpperBoundRefutation

/-! The fixed-negativity boundary for the spectral binegativity of two-qubit states. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Entanglement.TwoQubitBinegativityLowerBound

open Matrix
open scoped MatrixOrder ComplexOrder
open D5.S3.Quantum.Entanglement.StructuredNegativityCoincidenceRefutation
  (partialTransposeB IsDensity)
open D5.S3.Quantum.Entanglement.TwoQubitBinegativityUpperBoundRefutation (binegativity)

/-- Girard–Gour's fixed-negativity lower bound, arXiv:1701.02724, Eq. (8). -/
def claim : Prop :=
  ∀ σ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ, IsDensity σ →
    let ν := 2 * ((partialTransposeB σ)⁻).trace.re
    let c := Real.sqrt (2 * ν * (ν + 1)) - ν
    ν / 2 * (1 + c / Real.sqrt ((1 - c) ^ 2 + c ^ 2)) ≤ binegativity σ

/-- The principal-minor constraint forces the sharp lower bound on the Schmidt product. -/
private theorem scalar_bound (ν x s : ℝ) (hν : 0 < ν) (hx : 0 ≤ x)
    (hx1 : x ≤ 1) (hs : 0 ≤ s)
    (hminor : ν * (2 * x + ν) ≤ (1 - x) ^ 2)
    (hschmidt : ν * (2 * x + ν) ≤ s ^ 2 * (x + ν) ^ 2) :
    let c := Real.sqrt (2 * ν * (ν + 1)) - ν
    c / Real.sqrt ((1 - c) ^ 2 + c ^ 2) ≤ s := by
  dsimp only
  let r := Real.sqrt (2 * ν * (ν + 1))
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hrsq : r ^ 2 = 2 * ν * (ν + 1) := Real.sq_sqrt (by positivity)
  have hν1 : ν ≤ 1 := by nlinarith [sq_nonneg x, mul_nonneg hν.le hx]
  have hνr : ν < r := by nlinarith
  have hr1 : r ≤ 1 + ν := by nlinarith
  have hxq : x ≤ 1 + ν - r := by
    have hsq : r ^ 2 ≤ (1 + ν - x) ^ 2 := by nlinarith
    have hright : 0 ≤ 1 + ν - x := by linarith
    nlinarith
  have hden : Real.sqrt ((1 - (r - ν)) ^ 2 + (r - ν) ^ 2) = 1 + 2 * ν - r := by
    apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by linarith)).mpr
    nlinarith only [hrsq]
  change (r - ν) / Real.sqrt ((1 - (r - ν)) ^ 2 + (r - ν) ^ 2) ≤ s
  rw [hden]
  have hD : 0 < 1 + 2 * ν - r := by linarith
  have hX : 0 < x + ν := by positivity
  have hfrac : x / (x + ν) ≤ (1 + ν - r) / (1 + 2 * ν - r) := by
    apply (div_le_div_iff₀ hX hD).mpr
    nlinarith
  have hfrac0 : 0 ≤ x / (x + ν) := div_nonneg hx hX.le
  have hfrac1 : 0 ≤ (1 + ν - r) / (1 + 2 * ν - r) :=
    div_nonneg (by linarith) hD.le
  have hfrac_sq := (sq_le_sq₀ hfrac0 hfrac1).mpr hfrac
  have hleft : 1 - (x / (x + ν)) ^ 2 ≤ s ^ 2 := by
    apply (le_of_mul_le_mul_right ?_ (sq_pos_of_pos hX))
    calc
      (1 - (x / (x + ν)) ^ 2) * (x + ν) ^ 2 = ν * (2 * x + ν) := by
        field_simp [ne_of_gt hX]
        <;> ring
      _ ≤ s ^ 2 * (x + ν) ^ 2 := hschmidt
  have hright : ((r - ν) / (1 + 2 * ν - r)) ^ 2 =
      1 - ((1 + ν - r) / (1 + 2 * ν - r)) ^ 2 := by
    rw [eq_sub_iff_add_eq, div_pow, div_pow, ← add_div]
    apply (div_eq_one_iff_eq (pow_ne_zero 2 (ne_of_gt hD))).mpr
    nlinarith only [hrsq]
  have hquot0 : 0 ≤ (r - ν) / (1 + 2 * ν - r) :=
    div_nonneg (by linarith) hD.le
  apply (sq_le_sq₀ hquot0 hs).mp
  rw [hright]
  linarith

private theorem nonnegative_trace_negPart
    (A : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) : 0 ≤ (A⁻).trace.re :=
  (RCLike.nonneg_iff.mp
    (Matrix.nonneg_iff_posSemidef.mp (CFC.negPart_nonneg A)).trace_nonneg).1

/-- A positive partial transpose gives the zero endpoint of the bound. -/
private theorem zero_case (σ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (hzero : 2 * ((partialTransposeB σ)⁻).trace.re = 0) :
    let ν := 2 * ((partialTransposeB σ)⁻).trace.re
    let c := Real.sqrt (2 * ν * (ν + 1)) - ν
    ν / 2 * (1 + c / Real.sqrt ((1 - c) ^ 2 + c ^ 2)) ≤ binegativity σ := by
  dsimp only
  rw [hzero]
  simp only [zero_mul, zero_div, mul_zero]
  unfold binegativity
  have hfirst := nonnegative_trace_negPart (partialTransposeB σ)
  have hsecond := nonnegative_trace_negPart (partialTransposeB ((partialTransposeB σ)⁻))
  linarith

private theorem positive_case
    (σ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (hσ : IsDensity σ)
    (hν : 0 < 2 * ((partialTransposeB σ)⁻).trace.re) :
    ∃ x s : ℝ, 0 ≤ x ∧ x ≤ 1 ∧ 0 ≤ s ∧
      (2 * ((partialTransposeB σ)⁻).trace.re) *
        (2 * x + 2 * ((partialTransposeB σ)⁻).trace.re) ≤ (1 - x) ^ 2 ∧
      (2 * ((partialTransposeB σ)⁻).trace.re) *
        (2 * x + 2 * ((partialTransposeB σ)⁻).trace.re) ≤
          s ^ 2 * (x + 2 * ((partialTransposeB σ)⁻).trace.re) ^ 2 ∧
      binegativity σ = ((partialTransposeB σ)⁻).trace.re * (1 + s) := by
  sorry

/-- The two-qubit binegativity is bounded below by the Girard–Gour curve. -/
theorem result : claim := by
  intro σ hσ
  by_cases hzero : 2 * ((partialTransposeB σ)⁻).trace.re = 0
  · exact zero_case σ hzero
  · have hν : 0 < 2 * ((partialTransposeB σ)⁻).trace.re :=
      lt_of_le_of_ne (mul_nonneg (by norm_num) (nonnegative_trace_negPart _))
        (Ne.symm hzero)
    obtain ⟨x, s, hx, hx1, hs, hminor, hschmidt, hbineg⟩ := positive_case σ hσ hν
    have hbound := scalar_bound _ x s hν hx hx1 hs hminor hschmidt
    dsimp only at hbound ⊢
    rw [hbineg]
    nlinarith

end D5.S3.Quantum.Entanglement.TwoQubitBinegativityLowerBound
