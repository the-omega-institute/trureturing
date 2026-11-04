/- GID: D5/S3/Quantum/Recovery/PetzPhysicalWeightedCoordinates
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/PetzPhysicalWeightedCoordinates
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual physical Petz square-root errors have weighted modular Parseval coordinates. -/

/- Auxiliary source consumed by the actual Petz stability proof; no standalone admission. -/
import D5.S3.Quantum.Recovery.PetzSpectralCoordinates
import D5.S3.Quantum.Foundation.HilbertSchmidtTraceStability

/-! Weighted Parseval coordinates for the actual physical Petz square-root error. -/

noncomputable section
universe u v
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy
open D5.S3.Quantum.Divergence.CanonicalChannelDPI
open D5.S3.Quantum.Recovery.SpectralTransposeRecovery
open D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity
open D5.S3.Quantum.Foundation.HilbertSchmidtTraceStability
open D5.S3.Quantum.Entanglement.PrecessionSpinOneSeparableBound (entryNormSq)

namespace D5.S3.Quantum.Recovery.PetzPhysicalWeightedCoordinates

private theorem cfc_mulVec_basis {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (f : ℝ → ℝ) (i : n) :
    cfc f H *ᵥ (fun k => hH.eigenvectorBasis i k) =
      (f (hH.eigenvalues i) : ℂ) • (fun k => hH.eigenvectorBasis i k) := by
  rw [hH.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  simp only [← Matrix.mulVec_mulVec]
  rw [hH.star_eigenvectorUnitary_mulVec, Matrix.diagonal_mulVec_single]
  simp only [Function.comp_apply, RCLike.ofReal_eq_complex_ofReal, mul_one,
    Matrix.mulVec_single]
  ext k
  simp only [Pi.smul_apply, op_smul_eq_smul, smul_eq_mul, Matrix.col_apply,
    Matrix.IsHermitian.eigenvectorUnitary_apply]

private theorem basis_pair_cfc {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (f : ℝ → ℝ)
    (j : n) (y : n → ℂ) :
    star (fun k => hH.eigenvectorBasis j k) ⬝ᵥ (cfc f H *ᵥ y) =
      (f (hH.eigenvalues j) : ℂ) *
        (star (fun k => hH.eigenvectorBasis j k) ⬝ᵥ y) := by
  have hC : (cfc f H).IsHermitian := (IsSelfAdjoint.cfc (R := ℝ)).isHermitian
  have hpair : star (cfc f H *ᵥ (fun k => hH.eigenvectorBasis j k)) ⬝ᵥ y =
      star (fun k => hH.eigenvectorBasis j k) ⬝ᵥ (cfc f H *ᵥ y) := by
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, hC.eq]
  rw [← hpair, cfc_mulVec_basis]
  simp [star_smul, smul_dotProduct]

private theorem full_spectral_parseval {n : Type*} [Fintype n] [DecidableEq n]
    (E R S : Matrix n n ℂ) (hR : R.IsHermitian) (hS : S.IsHermitian) :
    ‖E‖ ^ 2 = ∑ j : n, ∑ i : n,
      ‖star (fun k => hS.eigenvectorBasis j k) ⬝ᵥ
        (E *ᵥ (fun k => hR.eigenvectorBasis i k))‖ ^ 2 := by
  let U := (hR.eigenvectorUnitary : Matrix n n ℂ)
  let W := (hS.eigenvectorUnitary : Matrix n n ℂ)
  let C := Wᴴ * E * U
  have hU : U * Uᴴ = 1 := by
    simpa only [U, Matrix.star_eq_conjTranspose] using
      Unitary.mul_star_self_of_mem hR.eigenvectorUnitary.2
  have hW : W * Wᴴ = 1 := by
    simpa only [W, Matrix.star_eq_conjTranspose] using
      Unitary.mul_star_self_of_mem hS.eigenvectorUnitary.2
  have hGram : Cᴴ * C = Uᴴ * (Eᴴ * E) * U := by
    dsimp only [C]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc
      _ = Uᴴ * Eᴴ * (W * Wᴴ) * E * U := by noncomm_ring
      _ = Uᴴ * (Eᴴ * E) * U := by rw [hW]; noncomm_ring
  have htrace : (Cᴴ * C).trace = (Eᴴ * E).trace := by
    rw [hGram, Matrix.trace_mul_comm (Uᴴ * (Eᴴ * E)) U,
      ← Matrix.mul_assoc, hU, Matrix.one_mul]
  have hnorm : ‖C‖ ^ 2 = ‖E‖ ^ 2 := by
    apply Complex.ofReal_injective
    rw [D5.S3.Quantum.GNSMatrix.frobenius_norm_sq_eq_trace,
      D5.S3.Quantum.GNSMatrix.frobenius_norm_sq_eq_trace, htrace]
  have hentry (j i : n) : C j i =
      star (fun k => hS.eigenvectorBasis j k) ⬝ᵥ
        (E *ᵥ (fun k => hR.eigenvectorBasis i k)) := by
    simp only [C, U, W, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.IsHermitian.eigenvectorUnitary_apply, Matrix.mulVec, dotProduct, Pi.star_apply,
      Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    ring
  calc
    ‖E‖ ^ 2 = ‖C‖ ^ 2 := hnorm.symm
    _ = entryNormSq C := (entryNormSq_eq_hs_sq C).symm
    _ = _ := by simp only [entryNormSq, hentry]

variable {a : Type u} {b : Type v} [Fintype a] [DecidableEq a] [Nonempty a]
  [Fintype b] [DecidableEq b] [Nonempty b]
  {Φ : QuantumChannel a b} {ρ σ : DensityState a}

abbrev physicalWeightedError (M : SupportedRelativeModularModel Φ ρ σ)
    (x : M.data.L × M.data.K → ℂ) : Matrix a a ℂ :=
  cfc Real.sqrt M.data.S * M.data.Ψ (M.data.spectralX x) * spectralSupport M.data.R -
    cfc Real.sqrt M.data.R

abbrev modularCoordinateError (M : SupportedRelativeModularModel Φ ρ σ)
    (x : M.data.L × M.data.K → ℂ) : M.data.J × M.data.I → ℂ :=
  cfc (fun t : ℝ => 1 / Real.sqrt t) M.data.A *ᵥ M.data.ξ - M.data.V *ᵥ x

omit [Nonempty a] [Nonempty b] in
private theorem physical_full_coordinate (M : SupportedRelativeModularModel Φ ρ σ)
    (x : M.data.L × M.data.K → ℂ) (j i : a) :
    star (fun k => M.data.hS.1.eigenvectorBasis j k) ⬝ᵥ
        (physicalWeightedError M x *ᵥ (fun k => M.data.hR.1.eigenvectorBasis i k)) =
      (Real.sqrt (M.data.hS.1.eigenvalues j) : ℂ) *
          (if M.data.hR.1.eigenvalues i = 0 then 0 else 1) *
          (star (fun k => M.data.hS.1.eigenvectorBasis j k) ⬝ᵥ
            (M.data.Ψ (M.data.spectralX x) *ᵥ
              (fun k => M.data.hR.1.eigenvectorBasis i k))) -
        (Real.sqrt (M.data.hR.1.eigenvalues i) : ℂ) *
          (star (fun k => M.data.hS.1.eigenvectorBasis j k) ⬝ᵥ
            (fun k => M.data.hR.1.eigenvectorBasis i k)) := by
  dsimp only [physicalWeightedError]
  rw [Matrix.sub_mulVec, dotProduct_sub, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec]
  change star _ ⬝ᵥ (cfc Real.sqrt M.data.S *ᵥ
    (M.data.Ψ (M.data.spectralX x) *ᵥ
      (cfc (fun t : ℝ => if t = 0 then 0 else 1) M.data.R *ᵥ _))) - _ = _
  rw [cfc_mulVec_basis, Matrix.mulVec_smul, Matrix.mulVec_smul, dotProduct_smul,
    basis_pair_cfc, cfc_mulVec_basis, dotProduct_smul]
  by_cases hi0 : M.data.hR.1.eigenvalues i = 0 <;> simp [hi0]

/-- The positive physical coordinates are the modular error multiplied by
the square root of the actual supported relative-modular eigenvalue. -/
theorem physical_positive_coordinate (M : SupportedRelativeModularModel Φ ρ σ)
    (x : M.data.L × M.data.K → ℂ) (j : M.data.J) (i : M.data.I) :
    star (M.data.v j) ⬝ᵥ (physicalWeightedError M x *ᵥ M.data.u i) =
      -(Real.sqrt (M.data.sj j / M.data.ri i) : ℂ) * modularCoordinateError M x (j, i) := by
  let D := M.data
  have hdiag : (cfc (fun t : ℝ => 1 / Real.sqrt t) D.A *ᵥ D.ξ) (j, i) =
      ((1 / Real.sqrt (D.sj j / D.ri i) : ℝ) : ℂ) * D.ξ (j, i) := by
    change (cfc (fun t : ℝ => 1 / Real.sqrt t)
      (diagonal (fun ji : D.J × D.I => ((D.sj ji.1 / D.ri ji.2 : ℝ) : ℂ))) *ᵥ _) _ = _
    rw [cfc_diagonal, Matrix.mulVec_diagonal]
  have hroot : Real.sqrt (D.sj j / D.ri i) * Real.sqrt (D.ri i) = Real.sqrt (D.sj j) := by
    rw [Real.sqrt_div j.2.le, div_mul_cancel₀ _ (Real.sqrt_pos.mpr i.2).ne']
  have hn : (Real.sqrt (D.sj j / D.ri i) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (div_pos j.2 i.2)).ne'
  have hrootC := congrArg Complex.ofReal hroot
  push_cast at hrootC
  rw [physical_full_coordinate]
  simp only [ite_eq_right (ne_of_gt i.2)]
  change _ = -(Real.sqrt (D.sj j / D.ri i) : ℂ) *
    ((cfc (fun t : ℝ => 1 / Real.sqrt t) D.A *ᵥ D.ξ) (j, i) - (D.V *ᵥ x) (j, i))
  rw [hdiag, M.coordinateAction]
  dsimp only [SupportedRelativeModularData.ξ]
  rw [Complex.ofReal_div, Complex.ofReal_one]
  field_simp [hn]
  linear_combination -hrootC *
    (star (D.v j) ⬝ᵥ (D.Ψ (D.spectralX x) *ᵥ D.u i))

/-- Exact Frobenius Parseval formula for the full physical matrix, including
its zero input columns and zero reference-spectrum rows. -/
theorem physical_weighted_parseval (M : SupportedRelativeModularModel Φ ρ σ)
    (x : M.data.L × M.data.K → ℂ) :
    ‖physicalWeightedError M x‖ ^ 2 = ∑ ji : M.data.J × M.data.I,
      (M.data.sj ji.1 / M.data.ri ji.2) * ‖modularCoordinateError M x ji‖ ^ 2 := by
  classical
  let D := M.data
  let c : a → a → ℂ := fun j i =>
    star (fun k => D.hS.1.eigenvectorBasis j k) ⬝ᵥ
      (physicalWeightedError M x *ᵥ (fun k => D.hR.1.eigenvectorBasis i k))
  have hcolzero (j i : a) (hi : ¬0 < D.hR.1.eigenvalues i) : c j i = 0 := by
    have hi0 := le_antisymm (le_of_not_gt hi) (D.hR.eigenvalues_nonneg i)
    simp [c, physical_full_coordinate, hi0]
  have hrowzero (j : a) (hj : ¬0 < D.hS.1.eigenvalues j) (i : D.I) : c j i.1 = 0 := by
    have hj0 := le_antisymm (le_of_not_gt hj) (D.hS.eigenvalues_nonneg j)
    simp only [c, physical_full_coordinate, hj0, Real.sqrt_zero, Complex.ofReal_zero,
      zero_mul, M.zeroCoordinatesR j hj0 i.1 i.2, mul_zero, sub_zero]
  have hcolumns (j : a) : (∑ i : a, ‖c j i‖ ^ 2) = ∑ i : D.I, ‖c j i.1‖ ^ 2 := by
    have hsplit := Fintype.sum_subtype_add_sum_subtype
      (fun i : a => 0 < D.hR.1.eigenvalues i) (fun i : a => ‖c j i‖ ^ 2)
    have hz : (∑ i : {i : a // ¬0 < D.hR.1.eigenvalues i}, ‖c j i.1‖ ^ 2) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      rw [hcolzero j i.1 i.2, norm_zero, zero_pow (by decide : 2 ≠ 0)]
    rw [hz, add_zero] at hsplit
    exact hsplit.symm
  have hrows : (∑ j : a, ∑ i : D.I, ‖c j i.1‖ ^ 2) =
      ∑ j : D.J, ∑ i : D.I, ‖c j.1 i.1‖ ^ 2 := by
    have hsplit := Fintype.sum_subtype_add_sum_subtype
      (fun j : a => 0 < D.hS.1.eigenvalues j)
      (fun j : a => ∑ i : D.I, ‖c j i.1‖ ^ 2)
    have hz : (∑ j : {j : a // ¬0 < D.hS.1.eigenvalues j},
        ∑ i : D.I, ‖c j.1 i.1‖ ^ 2) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      apply Finset.sum_eq_zero
      intro i _
      rw [hrowzero j.1 j.2 i, norm_zero, zero_pow (by decide : 2 ≠ 0)]
    rw [hz, add_zero] at hsplit
    exact hsplit.symm
  rw [full_spectral_parseval _ D.R D.S D.hR.1 D.hS.1]
  change (∑ j : a, ∑ i : a, ‖c j i‖ ^ 2) = _
  simp_rw [hcolumns]
  rw [hrows, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  change ‖star (D.v j) ⬝ᵥ (physicalWeightedError M x *ᵥ D.u i)‖ ^ 2 = _
  rw [physical_positive_coordinate, norm_mul, norm_neg, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt (div_nonneg j.2.le i.2.le)]

/-- A stated upper bound on the physical modular weights controls the
Frobenius error by the unweighted actual coordinate error. -/
theorem physical_hs_sq_le_coordinate_sq (M : SupportedRelativeModularModel Φ ρ σ)
    (x : M.data.L × M.data.K → ℂ) (L : ℝ)
    (hL : ∀ ji : M.data.J × M.data.I, M.data.sj ji.1 / M.data.ri ji.2 ≤ L) :
    ‖physicalWeightedError M x‖ ^ 2 ≤ L * ∑ ji, ‖modularCoordinateError M x ji‖ ^ 2 := by
  rw [physical_weighted_parseval, Finset.mul_sum]
  exact Finset.sum_le_sum (fun ji _ => mul_le_mul_of_nonneg_right (hL ji) (sq_nonneg _))

end D5.S3.Quantum.Recovery.PetzPhysicalWeightedCoordinates
