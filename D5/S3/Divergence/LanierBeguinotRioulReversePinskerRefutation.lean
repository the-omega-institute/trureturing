/- GID: D5/S3/Divergence/LanierBeguinotRioulReversePinskerRefutation
   generality: I
   mirror-B: D5/B/S3/Divergence/LanierBeguinotRioulReversePinskerRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Divergence/LanierBeguinotRioulReversePinskerRefutation.claim; result=D5/S3/Divergence/LanierBeguinotRioulReversePinskerRefutation.result; claim=D5/S3/Divergence/LanierBeguinotRioulReversePinskerRefutation.claim
   digest: A noncommuting qubit pair violates the maximal reverse Pinsker bound. -/

/- admission_basis: open-problem-resolution (#19943; Refuted)
   escape_witness: none; the settlement uses the external open-problem resolution basis.
   proof_shape: bind-only for every theorem; private helpers are consumed:
     sigma_pos -> theorem4_false; root_nonneg -> sqrt_sigma;
     sqrt_sigma -> relative_eq, divergence_eq; inv_root -> relative_eq;
     relative_eq -> inf_spectrum, sup_spectrum, divergence_eq;
     rho_psd, rho_trace, sigma_trace -> theorem4_false;
     delta_square, delta_abs_nonneg -> sqrt_delta;
     sqrt_delta -> abs_delta, trace_norm; abs_delta -> condition_49;
     trace_norm, inf_spectrum, sup_spectrum -> bound_eq;
     condition_49 -> theorem4_false; rel_sa -> cfc_rel;
     spectrum_rel -> inf_spectrum, sup_spectrum; cfc_rel -> divergence_eq;
     divergence_eq, bound_eq, f_convex -> theorem4_false;
     theorem4_false -> result; result is the external conjecture refutation.
   Direct frozen dependencies: PathSpectralClassical.relativeCongruence,
   SpectralPower.posDef_two and FiniteTraceDistance.traceNorm.
   Public formulas inline the source relative-matrix expression; proofs reuse
   PathSpectralClassical.relativeCongruence, without a duplicate definition.
   The public result is the designated refutation result (basis=refutes) and is
   exempt from four-slot escape registration (CLAUDE.md §3.9).
   The spectral maximal-divergence formula is Eq. (4) of arXiv:2501.14340v1.
   Its Definition 2 data-processing admissibility for the operator-convex
   generator (x-1)^2 is a literature premise, not a theorem proved here. -/

import D5.S3.Resource.LogDet.PathSpectralClassical
import D5.S3.Quantum.Matrix.SpectralPower
import D5.S3.Quantum.Foundation.FiniteTraceDistance

namespace D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation

open Matrix MatrixOrder ComplexOrder
open D5.S3.Quantum.Foundation.FiniteTraceDistance (traceNorm)
open D5.S3.Resource.LogDet.PathSpectralClassical (relativeCongruence)

/-- Eq. (4): `D_f^max(ρ‖σ) = Tr σ^{1/2} f(σ^{−1/2} ρ σ^{−1/2}) σ^{1/2}`. -/
noncomputable def maxDivergence {n : ℕ} (f : ℝ → ℝ) (ρ σ : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  RCLike.re (CFC.sqrt σ * cfc f ((CFC.sqrt σ)⁻¹ * ρ * (CFC.sqrt σ)⁻¹) * CFC.sqrt σ).trace

/-- The right-hand side of Eq. (50), with `m` and `M` the least and greatest points of the real spectrum of
`σ^{−1/2} ρ σ^{−1/2}`. -/
noncomputable def reversePinskerBound {n : ℕ} (f : ℝ → ℝ) (ρ σ : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  traceNorm (ρ - σ) / 2 *
    (f (sInf (spectrum ℝ ((CFC.sqrt σ)⁻¹ * ρ * (CFC.sqrt σ)⁻¹))) / (1 - sInf (spectrum ℝ ((CFC.sqrt σ)⁻¹ * ρ * (CFC.sqrt σ)⁻¹))) +
      f (sSup (spectrum ℝ ((CFC.sqrt σ)⁻¹ * ρ * (CFC.sqrt σ)⁻¹))) / (sSup (spectrum ℝ ((CFC.sqrt σ)⁻¹ * ρ * (CFC.sqrt σ)⁻¹)) - 1))

/-- The conjecture of Section III-C, for the maximal f-divergence: Eq. (50) holds without condition (49). -/
def claim : Prop :=
  ∀ (n : ℕ) (f : ℝ → ℝ), ConvexOn ℝ (Set.Ici 0) f → f 1 = 0 →
    ∀ ρ σ : Matrix (Fin n) (Fin n) ℂ, ρ.PosSemidef → ρ.trace = 1 → σ.PosDef → σ.trace = 1 →
      maxDivergence f ρ σ ≤ reversePinskerBound f ρ σ

/-- Theorem 4 as printed, for the maximal f-divergence: condition (49) implies Eq. (50). -/
private def claimTheorem4 : Prop :=
  ∀ (n : ℕ) (f : ℝ → ℝ), ConvexOn ℝ (Set.Ici 0) f → f 1 = 0 →
    ∀ ρ σ : Matrix (Fin n) (Fin n) ℂ, ρ.PosSemidef → ρ.trace = 1 → σ.PosDef → σ.trace = 1 →
      CFC.abs (ρ - σ) ≤ ρ + σ → maxDivergence f ρ σ ≤ reversePinskerBound f ρ σ

end D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation

namespace D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation
open Matrix MatrixOrder ComplexOrder
open D5.S3.Quantum.Foundation.FiniteTraceDistance (traceNorm)
open D5.S3.Resource.LogDet.PathSpectralClassical (relativeCongruence)
private noncomputable def sigma : Matrix (Fin 2) (Fin 2) ℂ := diagonal ![9/25, 16/25]
private noncomputable def rho : Matrix (Fin 2) (Fin 2) ℂ := !![9/25,12/125;12/125,16/25]
private noncomputable def root : Matrix (Fin 2) (Fin 2) ℂ := diagonal ![3/5,4/5]
private noncomputable def root_inv : Matrix (Fin 2) (Fin 2) ℂ := diagonal ![5/3,5/4]
private noncomputable def rel : Matrix (Fin 2) (Fin 2) ℂ := !![1,1/5;1/5,1]
private noncomputable def delta_abs : Matrix (Fin 2) (Fin 2) ℂ := (12/125 : ℝ) • 1
private noncomputable def f (x : ℝ) : ℝ := (x-1)^2

private theorem sigma_pos : sigma.PosDef := by
  apply Matrix.posDef_diagonal_iff.mpr
  intro i
  fin_cases i <;> norm_num [sigma, Complex.lt_def]

private theorem root_nonneg : 0 ≤ root := by
  apply Matrix.PosSemidef.nonneg
  apply Matrix.PosSemidef.diagonal
  intro i
  fin_cases i <;> norm_num [root, Complex.le_def]

private theorem sqrt_sigma : CFC.sqrt sigma = root := by
  apply CFC.sqrt_unique (hb := root_nonneg)
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [root,sigma,Matrix.mul_apply,Fin.sum_univ_two]

private theorem inv_root : root⁻¹ = root_inv := by
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [root,root_inv,Matrix.mul_apply,Fin.sum_univ_two]

private theorem relative_eq : relativeCongruence rho sigma = rel := by
  rw [relativeCongruence,sqrt_sigma,inv_root]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [root_inv,rho,rel,Matrix.mul_apply,Fin.sum_univ_two]

private theorem rho_psd : rho.PosSemidef := by
  have h := D5.S3.Quantum.Matrix.SpectralPower.posDef_two
    (9/25) (12/125) (16/25) (by norm_num) (by norm_num)
  simpa [rho] using h.posSemidef

private theorem rho_trace : rho.trace = 1 := by
  norm_num [rho,Matrix.trace,Fin.sum_univ_two]
private theorem sigma_trace : sigma.trace = 1 := by
  norm_num [sigma,Matrix.trace,Fin.sum_univ_two]

private theorem delta_square : (rho-sigma)ᴴ*(rho-sigma) = delta_abs*delta_abs := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [rho,sigma,delta_abs,Matrix.mul_apply,Fin.sum_univ_two,Matrix.conjTranspose_apply,Complex.real_smul,map_ofNat]

private theorem delta_abs_nonneg : 0 ≤ delta_abs := by
  exact smul_nonneg (by norm_num : (0:ℝ) ≤ 12/125) zero_le_one

private theorem sqrt_delta : CFC.sqrt ((rho-sigma)ᴴ*(rho-sigma)) = delta_abs := by
  exact CFC.sqrt_unique delta_square.symm delta_abs_nonneg

private theorem abs_delta : CFC.abs (rho-sigma) = delta_abs := by
  exact sqrt_delta

private theorem trace_norm : traceNorm (rho-sigma) = 24/125 := by
  unfold traceNorm
  rw [sqrt_delta]
  norm_num [delta_abs,Matrix.trace,Fin.sum_univ_two,Complex.real_smul]

private theorem condition_49 : CFC.abs (rho-sigma) ≤ rho+sigma := by
  rw [abs_delta, Matrix.le_iff]
  have h := D5.S3.Quantum.Matrix.SpectralPower.posDef_two
    (78/125) (12/125) (148/125) (by norm_num) (by norm_num)
  have heq : rho+sigma-delta_abs = !![(78/125:ℂ),12/125;12/125,148/125] := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [rho,sigma,delta_abs,Complex.real_smul]
  rw [heq]
  simpa using h.posSemidef

private theorem rel_sa : IsSelfAdjoint rel := by
  change relᴴ = rel
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [rel,Matrix.conjTranspose_apply]

private theorem spectrum_rel : spectrum ℝ rel = {4/5,6/5} := by
  ext x
  rw [spectrum.mem_iff,Matrix.isUnit_iff_isUnit_det,isUnit_iff_ne_zero,not_not]
  have hd : ((algebraMap ℝ (Matrix (Fin 2) (Fin 2) ℂ) x)-rel).det =
      (((x-1)^2-1/25:ℝ):ℂ) := by
    simp [Matrix.det_fin_two,rel,Algebra.algebraMap_eq_smul_one,Complex.real_smul]
    ring
  rw [hd,Complex.ofReal_eq_zero]
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff]
  constructor
  · intro hx
    have hprod : (x-4/5)*(x-6/5)=0 := by nlinarith [hx]
    rcases mul_eq_zero.mp hprod with h | h
    · left; linarith
    · right; linarith
  · rintro (rfl | rfl) <;> norm_num

private theorem inf_spectrum : sInf (spectrum ℝ (relativeCongruence rho sigma)) = 4/5 := by
  rw [relative_eq,spectrum_rel,csInf_pair]
  norm_num
private theorem sup_spectrum : sSup (spectrum ℝ (relativeCongruence rho sigma)) = 6/5 := by
  rw [relative_eq,spectrum_rel,csSup_pair]
  norm_num

private theorem cfc_rel : cfc f rel = (1/25:ℝ) • (1:Matrix (Fin 2) (Fin 2) ℂ) := by
  unfold f
  rw [cfc_pow (fun x:ℝ => x-1) 2 rel (ha := rel_sa),
    cfc_sub (fun x:ℝ => x) (fun _ : ℝ => 1) rel,
    cfc_id' ℝ rel rel_sa,cfc_const_one ℝ rel (ha := rel_sa),pow_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [rel,Matrix.mul_apply,Fin.sum_univ_two,Complex.real_smul]

private theorem divergence_eq : maxDivergence f rho sigma = 1/25 := by
  change RCLike.re (CFC.sqrt sigma * cfc f (relativeCongruence rho sigma) *
    CFC.sqrt sigma).trace = 1/25
  rw [sqrt_sigma,relative_eq,cfc_rel]
  norm_num [root,Matrix.trace,Matrix.mul_apply,Fin.sum_univ_two,Complex.real_smul]

private theorem bound_eq : reversePinskerBound f rho sigma = 24/625 := by
  change traceNorm (rho-sigma) / 2 *
    (f (sInf (spectrum ℝ (relativeCongruence rho sigma))) /
        (1 - sInf (spectrum ℝ (relativeCongruence rho sigma))) +
      f (sSup (spectrum ℝ (relativeCongruence rho sigma))) /
        (sSup (spectrum ℝ (relativeCongruence rho sigma)) - 1)) = 24/625
  rw [trace_norm,inf_spectrum,sup_spectrum]
  norm_num [f]

private theorem f_convex : ConvexOn ℝ (Set.Ici 0) f := by
  have h := ((even_two).convexOn_pow (𝕜 := ℝ)).translate_left (-1 : ℝ)
  have h' : ConvexOn ℝ Set.univ (fun x : ℝ => (x-1)^2) := by
    simpa only [Set.preimage_univ, Function.comp_def, sub_eq_add_neg] using h
  exact h'.subset (Set.subset_univ _) (convex_Ici 0)

private theorem theorem4_false : ¬ D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.claimTheorem4 := by
  intro h
  have hbound := h 2 f f_convex (by norm_num [f]) rho sigma rho_psd rho_trace sigma_pos sigma_trace condition_49
  rw [divergence_eq,bound_eq] at hbound
  norm_num at hbound

theorem result : ¬ D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.claim := by
  intro h
  apply theorem4_false
  intro n f hf hf1 rho sigma hpsd htr hpd htr2 _
  exact h n f hf hf1 rho sigma hpsd htr hpd htr2

end D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation
