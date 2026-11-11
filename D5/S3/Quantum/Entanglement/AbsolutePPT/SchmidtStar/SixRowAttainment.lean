/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAttainment
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAttainment
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: none
   digest: Actual central APPT densities in six rows and the strict n22 obstruction. -/

import D5.S3.Quantum.Entanglement.AbsolutePPT.ContractionAttainment
import D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitQuintitMaximumPurity
import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowScalarData
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-!
A projector of rank `centralIndex n` yields the central APPT density via the
contraction theorem. The normalized ray construction yields a separate APPT
density at dimension 22 whose purity exceeds the central value.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

open Matrix
open scoped BigOperators ComplexOrder

namespace D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowAttainment
open Bipartite (APPT partialTranspose)
open SixRowScalarData (theta centralIndex)
noncomputable section

/-- The first j* coordinates in the canonical product-to-Fin labelling. -/
def centralProjector (n : ℕ) : Matrix (Fin 6 × Fin n) (Fin 6 × Fin n) ℂ :=
  diagonal (fun p =>
    if (finProdFinEquiv p : Fin (6*n)).val < centralIndex n then 1 else 0)

/-- The actual trace of 5I+2P; j* is an integer, including in odd dimensions. -/
def normalization (n : ℕ) : ℝ := 30*(n : ℝ)+2*(centralIndex n : ℝ)

/-- The normalized actual six-row complex density. -/
def centralDensity (n : ℕ) : Matrix (Fin 6 × Fin n) (Fin 6 × Fin n) ℂ :=
  (((normalization n)⁻¹ : ℝ) : ℂ) •
    ((5 : ℂ) • 1+(2 : ℂ) • centralProjector n)

private theorem normalization_pos (n : ℕ) (hn : 23 ≤ n) :
    0 < normalization n := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  unfold normalization
  positivity

theorem projector_square (n : ℕ) :
    centralProjector n * centralProjector n = centralProjector n := by
  unfold centralProjector
  rw [diagonal_mul_diagonal]
  congr 1
  funext p
  split_ifs <;> norm_num

theorem projector_positive (n : ℕ) :
    (centralProjector n).PosSemidef ∧ (1-centralProjector n).PosSemidef := by
  have hH : (centralProjector n).IsHermitian := by
    unfold centralProjector
    apply Matrix.isHermitian_diagonal_iff.mpr
    intro p
    split_ifs <;> simp [IsSelfAdjoint]
  have hp : (centralProjector n)ᴴ * centralProjector n = centralProjector n := by
    rw [hH.eq, projector_square]
  have hc : (1-centralProjector n)ᴴ * (1-centralProjector n) =
      1-centralProjector n := by
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hH.eq]
    noncomm_ring [projector_square n]
  exact ⟨hp ▸ posSemidef_conjTranspose_mul_self _,
    hc ▸ posSemidef_conjTranspose_mul_self _⟩

private theorem prefix_sum (N j : ℕ) (hj : j ≤ N) :
    (∑ i : Fin N, if i.val < j then (1 : ℂ) else 0) = (j : ℂ) := by
  rw [Fin.sum_univ_eq_sum_range (f := fun i : ℕ => if i < j then (1 : ℂ) else 0)]
  have hf : (Finset.range N).filter (fun i => i < j) = Finset.range j := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [← Finset.sum_filter, hf]
  simp

theorem projector_trace (n : ℕ) :
    (centralProjector n).trace = (centralIndex n : ℂ) := by
  rw [centralProjector, trace_diagonal]
  rw [(finProdFinEquiv : (Fin 6 × Fin n) ≃ Fin (6*n)).sum_comp
    (fun i => if i.val < centralIndex n then (1 : ℂ) else 0)]
  apply prefix_sum
  dsimp only [centralIndex]
  omega

theorem projector_rank (n : ℕ) :
    (centralProjector n).rank = centralIndex n := by
  let P := centralProjector n
  have hlin : IsIdempotentElem P.mulVecLin := by
    rw [← Matrix.toLin'_apply']
    change Matrix.toLin' P ∘ₗ Matrix.toLin' P = Matrix.toLin' P
    rw [← Matrix.toLin'_mul]
    exact congrArg Matrix.toLin' (projector_square n)
  have ht := (LinearMap.IsIdempotentElem.isProj_range _ hlin).trace
  have htrace : LinearMap.trace ℂ ((Fin 6 × Fin n) → ℂ) P.mulVecLin = P.trace := by
    rw [← Matrix.toLin'_apply', LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ _),
      LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']
  rw [htrace] at ht
  change (centralProjector n).trace = ((centralProjector n).rank : ℂ) at ht
  rw [projector_trace] at ht
  exact_mod_cast ht.symm

private theorem identity_trace (n : ℕ) :
    (1 : Matrix (Fin 6 × Fin n) (Fin 6 × Fin n) ℂ).trace = 6*(n : ℂ) := by
  simp [Matrix.trace_one, Fintype.card_prod]

private theorem numerator_square (n : ℕ) :
    ((5 : ℂ) • 1+(2 : ℂ) • centralProjector n) *
      ((5 : ℂ) • 1+(2 : ℂ) • centralProjector n) =
      (25 : ℂ) • 1+(24 : ℂ) • centralProjector n := by
  simp only [mul_add, add_mul, one_mul, mul_one, Matrix.mul_smul,
    Matrix.smul_mul, smul_smul, projector_square]
  module

/-- PSD, actual trace one, and the literal all-global-unitary APPT predicate. -/
theorem central_density_physical (n : ℕ) (hn : 23 ≤ n) :
    (centralDensity n).PosSemidef ∧ (centralDensity n).trace = 1 ∧
      APPT (centralDensity n) := by
  have hP := projector_positive n
  have hd := normalization_pos n hn
  have hs : 0 ≤ (normalization n)⁻¹ := inv_nonneg.mpr hd.le
  have hnum : APPT ((5 : ℂ) • 1+(2 : ℂ) • centralProjector n) := by
    simpa only [Fintype.card_fin, Nat.cast_ofNat, show (6 : ℂ)-1=5 by norm_num]
      using ContractionAttainment.contraction_appt (centralProjector n) hP.1 hP.2
  refine ⟨?_, ?_, ?_⟩
  · exact ((Matrix.PosSemidef.one.smul (by norm_num : (0 : ℂ) ≤ 5)).add
      (hP.1.smul (by norm_num : (0 : ℂ) ≤ 2))).smul (Complex.zero_le_real.mpr hs)
  · simp only [centralDensity, Matrix.trace_smul, Matrix.trace_add,
      identity_trace, projector_trace, smul_eq_mul]
    have htr : (5 : ℂ)*(6*(n : ℂ))+2*(centralIndex n : ℂ) =
        (normalization n : ℂ) := by
      unfold normalization
      push_cast
      ring
    rw [htr]
    exact_mod_cast (inv_mul_cancel₀ hd.ne')
  · intro U
    have h := (hnum U).smul (Complex.zero_le_real.mpr hs)
    change (partialTranspose ((U : Matrix _ _ ℂ) * centralDensity n *
      (U : Matrix _ _ ℂ)ᴴ)).PosSemidef
    have pt_smul (c : ℂ) (M : Matrix (Fin 6 × Fin n) (Fin 6 × Fin n) ℂ) :
        partialTranspose (c • M) = c • partialTranspose M := rfl
    simpa only [centralDensity, Matrix.mul_smul, Matrix.smul_mul, pt_smul] using h

/-- Exact square trace before taking real parts or specializing parity. -/
theorem central_density_square_trace (n : ℕ) (hn : 23 ≤ n) :
    (centralDensity n * centralDensity n).trace =
      (((25*(6*(n : ℝ))+24*(centralIndex n : ℝ))/(normalization n)^2 : ℝ) : ℂ) := by
  have hdC : (normalization n : ℂ) ≠ 0 := by
    exact_mod_cast (normalization_pos n hn).ne'
  simp only [centralDensity, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    numerator_square, Matrix.trace_smul, Matrix.trace_add,
    identity_trace, projector_trace, smul_eq_mul]
  push_cast
  field_simp [hdC]
  <;> ring

/-- Even n has 2j*=5n; odd n has 2j*=5n+1. No real half-integer substitution. -/
theorem central_density_purity (n : ℕ) (hn : 23 ≤ n) :
    (centralDensity n * centralDensity n).trace.re = theta n := by
  rw [central_density_square_trace n hn, Complex.ofReal_re]
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  by_cases he : n%2=0
  · have hj : 2*centralIndex n=5*n := by dsimp only [centralIndex]; omega
    have hjR : 2*(centralIndex n : ℝ)=5*(n : ℝ) := by exact_mod_cast hj
    have hden : normalization n=35*(n : ℝ) := by
      unfold normalization
      linarith only [hjR]
    have hnum : 25*(6*(n : ℝ))+24*(centralIndex n : ℝ)=210*(n : ℝ) := by
      linarith only [hjR]
    rw [hden, hnum, theta, if_pos he]
    field_simp [hnR.ne']
    <;> ring
  · have hj : 2*centralIndex n=5*n+1 := by dsimp only [centralIndex]; omega
    have hjR : 2*(centralIndex n : ℝ)=5*(n : ℝ)+1 := by exact_mod_cast hj
    have hden : normalization n=35*(n : ℝ)+1 := by
      unfold normalization
      linarith only [hjR]
    have hnum : 25*(6*(n : ℝ))+24*(centralIndex n : ℝ)=6*(35*(n : ℝ)+2) := by
      linarith only [hjR]
    rw [hden, hnum, theta, if_neg he]

/-- Literal diagonal matrix in finProdFinEquiv labelling, with j* entries 7/d
and every remaining entry 5/d. This is the existing centralSpectrum formula. -/
theorem central_density_diagonal (n : ℕ) :
    centralDensity n = diagonal (fun p : Fin 6 × Fin n =>
      ((if (finProdFinEquiv p : Fin (6*n)).val < centralIndex n then
        7/(30*(n : ℝ)+2*(centralIndex n : ℝ))
      else 5/(30*(n : ℝ)+2*(centralIndex n : ℝ)) : ℝ) : ℂ)) := by
  ext p q
  by_cases hpq : p=q
  · subst q
    by_cases hp : p.2.val + n*p.1.val < centralIndex n <;>
      simp [centralDensity, centralProjector, normalization, Matrix.diagonal_apply,
        Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply, hp, div_eq_mul_inv] <;>
      push_cast <;> ring
  · simp [centralDensity, centralProjector, Matrix.diagonal_apply,
      Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply, hpq]

/-- The displayed literal diagonal is an ordered nonnegative unit-mass spectrum
whose square sum is theta. No eigenvalue spectral theorem is reproved. -/
theorem central_spectrum_data (n : ℕ) (hn : 23 ≤ n) :
    let l : Fin (6*n) → ℝ := fun k =>
      if k.val < centralIndex n then
        7/(30*(n : ℝ)+2*(centralIndex n : ℝ))
      else 5/(30*(n : ℝ)+2*(centralIndex n : ℝ))
    Antitone l ∧ (∀ i, 0 ≤ l i) ∧ (∑ i, l i=1) ∧ ∑ i, (l i)^2=theta n := by
  let l : Fin (6*n) → ℝ := fun k =>
    if k.val < centralIndex n then
      7/(30*(n : ℝ)+2*(centralIndex n : ℝ))
    else 5/(30*(n : ℝ)+2*(centralIndex n : ℝ))
  change Antitone l ∧ (∀ i, 0 ≤ l i) ∧ (∑ i, l i=1) ∧ ∑ i, (l i)^2=theta n
  have hd : 0 < 30*(n : ℝ)+2*(centralIndex n : ℝ) := normalization_pos n hn
  have heq : centralDensity n = diagonal (fun p =>
      (l (finProdFinEquiv p) : ℂ)) := central_density_diagonal n
  have ht := (central_density_physical n hn).2.1
  rw [heq, trace_diagonal,
    (finProdFinEquiv : (Fin 6 × Fin n) ≃ Fin (6*n)).sum_comp
      (fun i => (l i : ℂ))] at ht
  have hsum : ∑ i, l i=1 := by exact_mod_cast ht
  have hsq : (centralDensity n * centralDensity n).trace =
      ((∑ i, (l i)^2 : ℝ) : ℂ) := by
    rw [heq, diagonal_mul_diagonal, trace_diagonal,
      (finProdFinEquiv : (Fin 6 × Fin n) ≃ Fin (6*n)).sum_comp
        (fun i => (l i : ℂ)*(l i : ℂ))]
    simp [pow_two]
  refine ⟨?_, ?_, hsum, ?_⟩
  · intro i k hik
    have hikv : i.val ≤ k.val := hik
    by_cases hi : i.val < centralIndex n <;> by_cases hk : k.val < centralIndex n
    · simp [l, hi, hk]
    · simp only [l, hi, hk, if_true, if_false]
      exact div_le_div_of_nonneg_right (by norm_num) hd.le
    · omega
    · simp [l, hi, hk]
  · intro i
    dsimp only [l]
    split_ifs <;> positivity
  · have hp := central_density_purity n hn
    rw [hsq, Complex.ofReal_re] at hp
    exact hp

/-- Actual central attainment, consumed by the full threshold assembly. -/
theorem central_attainment (n : ℕ) (hn : 23 ≤ n) :
    (centralProjector n).rank = centralIndex n ∧
      (centralDensity n).PosSemidef ∧ (centralDensity n).trace=1 ∧
      APPT (centralDensity n) ∧
      (centralDensity n * centralDensity n).trace.re=theta n := by
  obtain ⟨hd, ht, ha⟩ := central_density_physical n hn
  exact ⟨projector_rank n, hd, ht, ha, central_density_purity n hn⟩

/-- A concrete unit coordinate vector on the actual 6 by 22 tensor product. -/
def ray22Vector : Fin 6 × Fin 22 → ℂ := Pi.single (0,0) 1

def ray22Density : Matrix (Fin 6 × Fin 22) (Fin 6 × Fin 22) ℂ :=
  QuadbitQuintitMaximumPurity.normalizedRay ray22Vector

theorem ray22_unit : star ray22Vector ⬝ᵥ ray22Vector = (1 : ℂ) := by
  classical
  simp [ray22Vector, dotProduct, Pi.single_apply]

/-- The actual ray beats the central value at 22. This is a lower obstruction
only; no maximum below 23 or least eventual threshold is asserted here. -/
theorem n22_obstruction :
    ray22Density.PosSemidef ∧ ray22Density.trace=1 ∧ APPT ray22Density ∧
      (ray22Density * ray22Density).trace.re=(35/4489 : ℝ) ∧
      theta 22=(3/385 : ℝ) ∧
      (ray22Density * ray22Density).trace.re-theta 22=(8/1728265 : ℝ) ∧
      theta 22 < (ray22Density * ray22Density).trace.re := by
  obtain ⟨hd, ht, ha, hp⟩ :=
    QuadbitQuintitMaximumPurity.normalized_ray ray22Vector ray22_unit
  change (ray22Density * ray22Density).trace.re = _ at hp
  norm_num at hp
  have htheta : theta 22=(3/385 : ℝ) := by norm_num [theta]
  have hdiff : (ray22Density * ray22Density).trace.re-theta 22=(8/1728265 : ℝ) := by
    rw [hp, htheta]
    norm_num
  refine ⟨hd, ht, ha, hp, htheta, hdiff, ?_⟩
  rw [hp, htheta]
  norm_num

end
end D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowAttainment
