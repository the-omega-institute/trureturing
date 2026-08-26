/- GID: D5/S3/Quantum/Entanglement/LocalBReadoutResidualDimension
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/LocalBReadoutResidualDimension
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Local B readout leaves the A-local and correlation sectors invisible. -/

import D5.S3.Quantum.Entanglement.BipartiteSectorDecomposition

/- Library-search audit trail (2026-08-26):
   * Exact family hits `bipartiteTraceZero`, `localASector`, `localBSector`,
     `correlationSector`, and `bipartite_sector_decomposition` construct the
     source's real traceless Hermitian carrier and its canonical sectors.
   * The related frozen `LocalMarginalCorrelationBlindSpot` reads both local
     marginals and therefore leaves only the correlation sector; it is not an
     exact hit for a readout restricted to subsystem B.
   * Pinned Mathlib's exact `Submodule.finrank_sup_add_finrank_inf_eq` converts
     the imported orthogonality clauses into the two required join dimensions.
   * Searches found no exact theorem packaging all three B-local dimension
     clauses on this carrier. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace D5.S3.Quantum.Entanglement.LocalBReadoutResidualDimension

open D5.S3.Quantum.Entanglement.BipartiteSectorDecomposition

local instance matrixNormedAddCommGroup (d : Nat) :
    NormedAddCommGroup (Matrix (Fin d) (Fin d) ℂ) :=
  Matrix.toMatrixNormedAddCommGroup 1 Matrix.PosDef.one

local instance matrixComplexInnerProductSpace (d : Nat) :
    InnerProductSpace ℂ (Matrix (Fin d) (Fin d) ℂ) :=
  Matrix.toMatrixInnerProductSpace 1 Matrix.PosSemidef.one

local instance matrixRealInnerProductSpace (d : Nat) :
    InnerProductSpace ℝ (Matrix (Fin d) (Fin d) ℂ) :=
  InnerProductSpace.rclikeToReal ℂ (Matrix (Fin d) (Fin d) ℂ)

/-- For nonzero subsystem dimensions, the full traceless bipartite Hermitian
carrier has dimension `(m*n)^2-1`, the complete B-local readout sector has
dimension `n^2-1`, and its orthogonal invisible sector, constructed as the join
of the A-local and correlation sectors, has dimension `n^2*(m^2-1)`. -/
theorem local_b_readout_residual_dimension
    (m n : Nat) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    Module.finrank ℝ (bipartiteTraceZero m n) = (m * n) ^ 2 - 1 /\
      Module.finrank ℝ (localBSector m n) = n ^ 2 - 1 /\
      Module.finrank ℝ ↥(localASector m n ⊔ correlationSector m n) =
        n ^ 2 * (m ^ 2 - 1) := by
  letI : NeZero m := ⟨by omega⟩
  letI : NeZero n := ⟨by omega⟩
  rcases bipartite_sector_decomposition m n with
    ⟨hdecomp, hAB, hAC, hBC, hA, hB, hC⟩
  have hABdim :
      Module.finrank ℝ ↥(localASector m n ⊔ localBSector m n) =
        Module.finrank ℝ (localASector m n) +
          Module.finrank ℝ (localBSector m n) := by
    have hdim := Submodule.finrank_sup_add_finrank_inf_eq
      (localASector m n) (localBSector m n)
    rw [hAB.disjoint.eq_bot, finrank_bot, add_zero] at hdim
    exact hdim
  have hSumC : Submodule.IsOrtho (𝕜 := ℝ)
      (localASector m n ⊔ localBSector m n) (correlationSector m n) := by
    rw [Submodule.isOrtho_sup_left]
    exact ⟨hAC, hBC⟩
  have hTraceDim :
      Module.finrank ℝ (bipartiteTraceZero m n) = (m * n) ^ 2 - 1 := by
    have hdim := Submodule.finrank_sup_add_finrank_inf_eq
      (localASector m n ⊔ localBSector m n) (correlationSector m n)
    rw [hSumC.disjoint.eq_bot, finrank_bot, add_zero, hABdim, hA, hB, hC] at hdim
    rw [hdecomp] at hdim
    rw [hdim, sector_dimension_sum]
  have hResidualDim :
      Module.finrank ℝ ↥(localASector m n ⊔ correlationSector m n) =
        n ^ 2 * (m ^ 2 - 1) := by
    have hdim := Submodule.finrank_sup_add_finrank_inf_eq
      (localASector m n) (correlationSector m n)
    rw [hAC.disjoint.eq_bot, finrank_bot, add_zero, hA, hC] at hdim
    rw [hdim]
    have hnSquare : 1 ≤ n ^ 2 :=
      Nat.one_le_iff_ne_zero.mpr (pow_ne_zero 2 (NeZero.ne n))
    have hone : 1 + (n ^ 2 - 1) = n ^ 2 := by omega
    calc
      (m ^ 2 - 1) + (m ^ 2 - 1) * (n ^ 2 - 1) =
          (m ^ 2 - 1) * (1 + (n ^ 2 - 1)) := by
        rw [Nat.mul_add, Nat.mul_one]
      _ = (m ^ 2 - 1) * n ^ 2 := by rw [hone]
      _ = n ^ 2 * (m ^ 2 - 1) := by rw [Nat.mul_comm]
  exact ⟨hTraceDim, hB, hResidualDim⟩

#print axioms local_b_readout_residual_dimension

end D5.S3.Quantum.Entanglement.LocalBReadoutResidualDimension
