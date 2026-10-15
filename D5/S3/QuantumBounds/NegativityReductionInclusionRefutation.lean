/- GID: D5/S3/QuantumBounds/NegativityReductionInclusionRefutation
   generality: I
   mirror-B: D5/B/S3/QuantumBounds/NegativityReductionInclusionRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/QuantumBounds/NegativityReductionInclusionRefutation.claim; result=D5/S3/QuantumBounds/NegativityReductionInclusionRefutation.result; claim=D5/S3/QuantumBounds/NegativityReductionInclusionRefutation.claim
   digest: A pure two-qutrit state refutes the negativity-to-positive-reduction inclusion. -/

import D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation
import D5.S3.Quantum.Information.CoherentCopyCorrelationTax
import D5.S3.Quantum.PureState.PureStateHandshake

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false

noncomputable section

namespace D5.S3.QuantumBounds.NegativityReductionInclusionRefutation

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Kronecker

open D5.S3.Quantum.Foundation.FiniteTraceDistance (traceNorm)
open D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation (partialTranspose)
open D5.S3.Quantum.Information.PartialTraceMutualInformation (partialTraceRight)
open D5.S3.Quantum.Information.CoherentCopyCorrelationTax
  (copyMatrix copyMatrix_entry partialTraceRight_copyMatrix)
open D5.S3.Quantum.PureState.PureStateHandshake (rankOneDensity)

def negativity {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (ρ : Matrix (a × b) (a × b) ℂ) : ℝ := (traceNorm (partialTranspose ρ) - 1) / 2

def claim : Prop :=
  ∀ (a b : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (ρ : Matrix (a × b) (a × b) ℂ) (χ : ℕ),
    ρ.PosSemidef → ρ.trace = 1 → 1 ≤ χ → χ ≤ Fintype.card a → χ ≤ Fintype.card b →
    negativity ρ = ((χ : ℝ) - 1) / 2 →
    (partialTraceRight ρ ⊗ₖ (1 : Matrix b b ℂ) - ((χ : ℂ)⁻¹) • ρ).PosSemidef

private def coeff : Fin 3 → ℂ := ![4, 1, 1]

private def testCoeff : Fin 3 → ℂ := ![1, 4, 4]

private def v : Fin 3 × Fin 3 → ℂ :=
  fun p => if p.1 = p.2 then coeff p.1 else 0

private def rho : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
  (1 / 18 : ℂ) • rankOneDensity v

private def z : Fin 3 × Fin 3 → ℂ :=
  fun p => if p.1 = p.2 then testCoeff p.1 else 0

private def s : Fin 3 × Fin 3 → ℂ :=
  fun p => coeff p.1 * coeff p.2 / 18

private def S : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ := Matrix.diagonal s

private def M : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
  partialTraceRight rho ⊗ₖ (1 : Matrix (Fin 3) (Fin 3) ℂ) - (2 : ℂ)⁻¹ • rho

private theorem rho_posSemidef : rho.PosSemidef := by
  have hscalar : (0 : ℂ) ≤ (1 / 18 : ℂ) := by
    norm_num [RCLike.nonneg_iff (K := ℂ)]
  simpa only [rho.eq_1, rankOneDensity] using
    (Matrix.posSemidef_vecMulVec_self_star v).smul hscalar

private theorem rho_trace : rho.trace = 1 := by
  norm_num [rho.eq_1, rankOneDensity, Matrix.trace_smul, Matrix.trace_vecMulVec,
    dotProduct, v.eq_1, coeff.eq_1, Pi.star_apply, smul_eq_mul,
    Fintype.sum_prod_type, Fin.sum_univ_three, Matrix.cons_val_two, map_ofNat]

private theorem S_posSemidef : S.PosSemidef := by
  rw [S.eq_1]
  apply Matrix.PosSemidef.diagonal
  intro p
  rcases p with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;>
    norm_num [s.eq_1, coeff.eq_1, Matrix.cons_val_two, RCLike.nonneg_iff (K := ℂ)]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
-- Expanding the 81 entries requires a larger normalization budget.
private theorem gram_eq :
    (partialTranspose rho)ᴴ * partialTranspose rho = S * S := by
  funext p q
  change (∑ r : Fin 3 × Fin 3,
    star (rho (r.1, p.2) (p.1, r.2)) * rho (r.1, q.2) (q.1, r.2)) =
      ∑ r : Fin 3 × Fin 3, S p r * S r q
  rcases p with ⟨i, j⟩
  rcases q with ⟨k, l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [rho.eq_1, rankOneDensity, v.eq_1, coeff.eq_1,
      S.eq_1, s.eq_1,
      Matrix.vecMulVec_apply, Matrix.smul_apply, smul_eq_mul, Matrix.diagonal,
      Pi.star_apply, Fintype.sum_prod_type, Fin.sum_univ_three, Matrix.cons_val_two,
      map_ofNat, Fin.ext_iff, -Fin.val_eq_zero_iff]

private theorem sqrt_gram :
    CFC.sqrt ((partialTranspose rho)ᴴ * partialTranspose rho) = S := by
  rw [gram_eq]
  exact CFC.sqrt_mul_self S S_posSemidef.nonneg

private theorem traceNorm_partialTranspose : traceNorm (partialTranspose rho) = 2 := by
  unfold traceNorm
  rw [sqrt_gram]
  norm_num [S.eq_1, Matrix.trace_diagonal, s.eq_1, coeff.eq_1,
    Fintype.sum_prod_type, Fin.sum_univ_three, Matrix.cons_val_two]

private theorem negativity_rho : negativity rho = (1 / 2 : ℝ) := by
  rw [negativity.eq_1, traceNorm_partialTranspose]
  norm_num

private theorem rho_marginal : partialTraceRight rho =
    Matrix.diagonal (![8 / 9, 1 / 18, 1 / 18] : Fin 3 → ℂ) := by
  let T := (1 / 18 : ℂ) • rankOneDensity coeff
  have hcopy : copyMatrix T = rho := by
    ext ⟨i, j⟩ ⟨k, l⟩
    by_cases hij : i = j <;> by_cases hkl : k = l <;>
      simp [copyMatrix_entry, T, rho.eq_1, rankOneDensity, v.eq_1,
        Matrix.vecMulVec_apply, Matrix.smul_apply, smul_eq_mul, hij, hkl, Pi.star_apply]
  rw [← hcopy, partialTraceRight_copyMatrix]
  congr 1
  funext i
  change (1 / 18 : ℂ) * (coeff i * star (coeff i)) = _
  fin_cases i <;> norm_num [coeff.eq_1, Matrix.cons_val_two, map_ofNat]

-- The two finite sums produce nested complex arithmetic expressions.
set_option maxRecDepth 4096 in
private theorem M_quadratic : RCLike.re (star z ⬝ᵥ (M *ᵥ z)) = -(4 / 3 : ℝ) := by
  rw [M.eq_1, rho_marginal]
  norm_num [dotProduct, Matrix.mulVec, Matrix.kroneckerMap_apply, Matrix.one_apply,
    Matrix.diagonal, Matrix.smul_apply, Matrix.vecMulVec_apply, Matrix.sub_apply,
    Pi.star_apply, smul_eq_mul, Fintype.sum_prod_type, Fin.sum_univ_three,
    rho.eq_1, rankOneDensity, v.eq_1, coeff.eq_1, z.eq_1, testCoeff.eq_1,
    Matrix.cons_val_two, map_ofNat, Fin.ext_iff, -Fin.val_eq_zero_iff]

private theorem M_not_posSemidef : ¬ M.PosSemidef := by
  intro hM
  have hz := hM.re_dotProduct_nonneg z
  rw [M_quadratic] at hz
  norm_num at hz

theorem result : ¬ claim := by
  intro h
  rw [claim.eq_1] at h
  apply M_not_posSemidef
  rw [M.eq_1]
  exact h (Fin 3) (Fin 3) rho 2 rho_posSemidef rho_trace
    (by norm_num) (by norm_num) (by norm_num) (by rw [negativity_rho]; norm_num)

end D5.S3.QuantumBounds.NegativityReductionInclusionRefutation
