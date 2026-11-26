/- GID: D5/S3/Quantum/Semigroups/WuAlignedRealPowerOrbit
   generality: I
   mirror-B: D5/B/S3/Quantum/Semigroups/WuAlignedRealPowerOrbit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Per-mode CAR traces and real-power deficit interpolation in the physical odd frame. -/

import D5.S3.Quantum.Semigroups.WuAlignedCubicOrbit
import D5.S3.Quantum.Matrix.SpectralPower

/-! Real-power interpolation at fixed even determinant in the physical occupation frame. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Semigroups.WuAlignedRealPowerOrbit

open _root_.Matrix Kronecker
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open WuCubicOperatorBridge (Mat Occupation)
open WuAlignedCubicOrbit (Block AlignedData orbitMatrix pairedBlock diagonalFrame antidiagonalFrame)
open TwistedTwoModeOUComparison (modeJump)
open D5.S3.Quantum.Matrix.SpectralPower (mpow)
open private parityMatrix evenBlock crossBlock unitary_diagonal_products norm_weights
  even_diagonal_moments det_phase endpoint_frames diagonal_pairing_affine
  pairedBlock_hermitian pairedHom pairedHom_data pairedHom_trace
  realPairedBlock realPairedBlock_symm
  from D5.S3.Quantum.Semigroups.WuAlignedCubicOrbit
open private jump_zero jump_one from D5.S3.Quantum.Semigroups.WuRepeatedMiddleCubic

/-- The adjoint direction is selected by `reverse`. In older-mode-first occupation order, let
`L = |0⟩⟨1|` and `Z = diag(1, −1)`. The repository jumps `modeJump 0 = L ⊗ I` and
`modeJump 1 = −Z ⊗ L` are the literal `J₂` and `−J₁` of `WuPhysicalHighHigh`, respectively. -/
def directedJump (k : Fin 2) (reverse : Bool) : Mat :=
  if reverse then (modeJump k)ᴴ else modeJump k

set_option maxHeartbeats 2000000 in
-- Expanding the signed sandwiches over the four physical indices needs extra heartbeats.
private theorem trace_lowering_entries (A B E F : Block) (c d : Fin 2 → ℝ) :
    let T (k : Fin 2) := (parityMatrix E F d *
      ((modeJump k)ᴴ * parityMatrix A B c * modeJump k)).trace
    T 0 = (d 1 : ℂ) * A 0 0 + E 1 1 * (c 0 : ℂ) +
      F 1 1 * B 0 0 + star (F 1 1 * B 0 0) ∧
    T 1 = (d 0 : ℂ) * A 0 0 + E 1 1 * (c 1 : ℂ) -
      F 1 0 * B 0 1 - star (F 1 0 * B 0 1) := by
  dsimp only
  constructor <;>
    norm_num [jump_zero, jump_one, parityMatrix, Matrix.trace, Matrix.diag_apply,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.diagonal_apply, Matrix.one_apply,
      Matrix.kroneckerMap_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Complex.star_def,
      map_mul] <;> ring

private def lowerValue (k : Fin 2) (p z : ℝ) (M N : AlignedData) : ℝ :=
  if k = 0 then
    N.odd 1 * (p * M.even 0 + (1 - p) * M.even 1) +
      (p * N.even 1 + (1 - p) * N.even 0) * M.odd 0 +
      2 * z * p * N.cross 1 * M.cross 0
  else
    N.odd 0 * (p * M.even 0 + (1 - p) * M.even 1) +
      (p * N.even 1 + (1 - p) * N.even 0) * M.odd 1 +
      2 * z * (1 - p) * N.cross 0 * M.cross 1

private theorem trace_lowering_eval (U : Block) (hU : Uᴴ * U = 1) (M N : AlignedData)
    (k : Fin 2) :
    (orbitMatrix U N * ((modeJump k)ᴴ * orbitMatrix U M * modeJump k)).trace.re =
      lowerValue k (Complex.normSq (U 0 0)) U.det.re M N := by
  obtain ⟨hd, ha⟩ := unitary_diagonal_products U hU
  have crossDiag : crossBlock U N.cross 1 1 * crossBlock U M.cross 0 0 =
      (U 0 0 * U 1 1) * (N.cross 1 : ℂ) * (M.cross 0 : ℂ) := by
    simp only [crossBlock, Matrix.mul_diagonal]
    ring
  have crossAnti : crossBlock U N.cross 1 0 * crossBlock U M.cross 0 1 =
      -(-(U 0 1 * U 1 0)) * (N.cross 0 : ℂ) * (M.cross 1 : ℂ) := by
    simp only [crossBlock, Matrix.mul_diagonal]
    ring
  obtain ⟨h0, h1⟩ := trace_lowering_entries (evenBlock U M.even) (crossBlock U M.cross)
    (evenBlock U N.even) (crossBlock U N.cross) M.odd N.odd
  simp only [orbitMatrix]
  dsimp only at h0 h1
  have hk : k = 0 ∨ k = 1 := by fin_cases k <;> decide
  rcases hk with rfl | rfl
  · rw [h0, crossDiag, hd, (even_diagonal_moments U hU M.even).1,
      (even_diagonal_moments U hU N.even).2]
    simp [lowerValue, Complex.add_re, Complex.mul_re]
    ring
  · rw [h1, crossAnti, ha, (even_diagonal_moments U hU M.even).1,
      (even_diagonal_moments U hU N.even).2]
    norm_num [lowerValue, Complex.add_re, Complex.sub_re, Complex.neg_re, Complex.mul_re,
      Complex.star_def]
    ring

set_option maxHeartbeats 800000 in
-- Elaborating the cyclic trace rewrite in the two endpoint frames needs extra heartbeats.
/-- Every mode and both directions interpolate separately, with the same physical odd
frame and determinant at both endpoints. The two matrices may have independent real fiber data. -/
theorem mode_mixed_trace_affine (U : Block) (hU : Uᴴ * U = 1) (M N : AlignedData)
    (k : Fin 2) (reverse : Bool) :
    let J := directedJump k reverse
    let p := Complex.normSq (U 0 0)
    let V := diagonalFrame U.det
    let W := antidiagonalFrame U.det
    (orbitMatrix U N * (Jᴴ * orbitMatrix U M * J)).trace.re =
      p * (orbitMatrix V N * (Jᴴ * orbitMatrix V M * J)).trace.re +
      (1 - p) * (orbitMatrix W N * (Jᴴ * orbitMatrix W M * J)).trace.re := by
  obtain ⟨hV, hVdet, hVp, hW, hWdet, hWp⟩ := endpoint_frames U.det (det_phase U hU)
  have lower (m n : AlignedData) :
      (orbitMatrix U n * ((modeJump k)ᴴ * orbitMatrix U m * modeJump k)).trace.re =
        Complex.normSq (U 0 0) * (orbitMatrix (diagonalFrame U.det) n *
          ((modeJump k)ᴴ * orbitMatrix (diagonalFrame U.det) m * modeJump k)).trace.re +
        (1 - Complex.normSq (U 0 0)) * (orbitMatrix (antidiagonalFrame U.det) n *
          ((modeJump k)ᴴ * orbitMatrix (antidiagonalFrame U.det) m * modeJump k)).trace.re := by
    rw [trace_lowering_eval U hU, trace_lowering_eval _ hV, trace_lowering_eval _ hW,
      hVdet, hVp, hWdet, hWp]
    by_cases hk : k = 0 <;> simp only [lowerValue, hk, ite_true, ite_false] <;> ring
  have cycle (A B : Mat) :
      (B * (modeJump k * A * (modeJump k)ᴴ)).trace =
        (A * ((modeJump k)ᴴ * B * modeJump k)).trace := by
    simpa only [← Matrix.mul_assoc] using Matrix.trace_mul_comm (B * modeJump k) (A * (modeJump k)ᴴ)
  cases reverse
  · exact lower M N
  · dsimp only
    simp only [directedJump, Bool.true_eq, ite_true, Matrix.conjTranspose_conjTranspose, cycle]
    exact lower N M

private theorem paired_cfc (U : Block) (hU : Uᴴ * U = 1) (f : ℝ → ℝ) (C : Fin 2 → Block)
    (hC : ∀ i, (C i).IsHermitian) :
    cfc f (pairedHom U hU C) = pairedHom U hU (fun i => cfc f (C i)) := by
  let : ContinuousFunctionalCalculus ℝ (Fin 2 → Block) IsSelfAdjoint :=
    IsSelfAdjoint.instContinuousFunctionalCalculus
  have hC' : IsSelfAdjoint C := Pi.isSelfAdjoint.mpr hC
  have hc : ContinuousOn f (spectrum ℝ C) := by
    rw [Pi.spectrum_eq]
    exact (Set.finite_iUnion (fun i => (C i).finite_real_spectrum)).continuousOn _
  have hmap := (pairedHom U hU).map_cfc f C hc
    (pairedHom U hU).toLinearMap.continuous_of_finiteDimensional hC' (hC'.map _)
  rw [cfc_map_pi (S := ℂ) f C (by rwa [Pi.spectrum_eq] at hc) hC' hC] at hmap
  exact hmap.symm

private def complexify : Matrix (Fin 2) (Fin 2) ℝ →⋆ₐ[ℝ] Block where
  __ := Complex.ofRealAm.mapMatrix
  map_star' A := by
    ext i j
    simp [AlgHom.mapMatrix, Matrix.star_eq_conjTranspose]

private def cfcData (f : ℝ → ℝ) (d : AlignedData) : AlignedData where
  even i := cfc f (realPairedBlock d i) 0 0
  odd i := cfc f (realPairedBlock d i) 1 1
  cross i := cfc f (realPairedBlock d i) 0 1

private theorem pairedBlock_cfc (f : ℝ → ℝ) (d : AlignedData) :
    pairedBlock (cfcData f d) = fun i => cfc f (pairedBlock d i) := by
  funext i
  have hA : IsSelfAdjoint (realPairedBlock d i) := by
    simpa only [isSelfAdjoint_iff, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using (realPairedBlock_symm d i).eq
  have hcast : complexify (realPairedBlock d i) = pairedBlock d i := by
    ext j k
    fin_cases j <;> fin_cases k <;> rfl
  rw [← hcast, ← complexify.map_cfc f _ ((realPairedBlock d i).finite_real_spectrum.continuousOn _)
    complexify.toLinearMap.continuous_of_finiteDimensional hA (hA.map complexify)]
  have hs : IsSelfAdjoint (cfc f (realPairedBlock d i)) := cfc_predicate f _
  have h10 : cfc f (realPairedBlock d i) 1 0 = cfc f (realPairedBlock d i) 0 1 := by
    simpa only [Matrix.star_apply, star_trivial] using
      congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A 0 1) hs.star_eq
  ext j k
  change pairedBlock (cfcData f d) i j k = ((cfc f (realPairedBlock d i) j k : ℝ) : ℂ)
  fin_cases j <;> fin_cases k <;> simp [pairedBlock, cfcData, h10]

private theorem orbit_cfc (U : Block) (hU : Uᴴ * U = 1) (f : ℝ → ℝ) (d : AlignedData) :
    cfc f (orbitMatrix U d) = orbitMatrix U (cfcData f d) := by
  rw [← pairedHom_data U hU, paired_cfc U hU f _ (pairedBlock_hermitian d),
    ← pairedBlock_cfc, pairedHom_data]

private theorem spectral_terms (U : Block) (hU : Uᴴ * U = 1) (s : ℝ) (d : AlignedData) :
    let P := mpow (orbitMatrix U d) s
    let C i := mpow (pairedBlock d i) s
    P.trace = ∑ i, (C i).trace ∧
    (P * cfc Real.log P).trace = ∑ i, (C i * cfc Real.log (C i)).trace := by
  dsimp only [mpow]
  rw [← pairedHom_data U hU, paired_cfc U hU _ _ (pairedBlock_hermitian d)]
  let C (i : Fin 2) := cfc (fun t : ℝ => t ^ s) (pairedBlock d i)
  have hC (i : Fin 2) : (C i).IsHermitian := cfc_predicate _ _
  rw [paired_cfc U hU Real.log C hC, ← map_mul]
  exact ⟨pairedHom_trace _ _ _, pairedHom_trace _ _ _⟩

private theorem jump_projection (k : Fin 2) (reverse : Bool) :
    let J := directedJump k reverse
    Jᴴ * J = diagonal (fun (i : Occupation) => (Jᴴ * J) i i) := by
  dsimp only
  ext ⟨i,j⟩ ⟨a,b⟩
  cases reverse <;> fin_cases k <;> fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
    norm_num [directedJump, jump_zero, jump_one, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.diagonal_apply, Matrix.one_apply, Matrix.kroneckerMap_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two]

/-- Ordinary trace deficit with independent projection and mixed-trace weights for each direction.

For Wu v1's physical deficit (3.54) at `s > 1`, take positive definite `X`, the product Gibbs
density `D`, `G = D^(1/(2s))`, `M = GXG`, and `logDensity = diag(log D)`. In Wu's recursive
tensor order `(mode 2, mode 1)`, the normalized CAR lowering letters in (3.22) for modes 1
and 2 are `I ⊗ L` and `−L ⊗ Z`, respectively, up to unit phase. The dissipative jumps in
(3.24)–(3.27) match the repository's literal jumps up to unit phase, with `k = 0` for mode 2
and `k = 1` for mode 1. Match each Gibbs factor `diag(a, b)` from (3.21) to the corresponding
mode. Lowering and adjoint projection weights are `2a` and `2b`, with mixed weights
`2a(b/a)^(1/s)` and `2b(a/b)^(1/s)`, respectively.

In the repository CAR convention the positive Wick generator uses `Kₖ = modeJump k · (Z ⊗ Z)`.
The unitary `W = diag(1, i, i, 1)` from `WuAlignedCubicOrbit` fixes `D` and `G` and obeys
`W modeJump k W* = i Kₖ`. The phase cancels in the dissipator. Since
`W* orbitMatrix(U,d) W = orbitMatrix(iU,d)`, apply the literal interpolation at `iU` and
conjugate the endpoints back by `W`. The literal endpoints use `−det U`, with `p = |U₀₀|²` fixed. -/
def weightedDeficit (s α : ℝ) (projectionRate mixedRate : Fin 2 → Bool → ℝ)
    (logDensity : Occupation → ℝ) (M : Mat) : ℝ :=
  let Q := mpow M (s - 1)
  let P := mpow M s
  let h := P.trace.re
  (s * (s / (s - 1)) / 4) *
    (∑ k : Fin 2, ∑ reverse : Bool,
      let J := directedJump k reverse
      projectionRate k reverse * (P * (Jᴴ * J)).trace.re -
        mixedRate k reverse * (Q * (Jᴴ * M * J)).trace.re) -
    α * ((P * cfc Real.log P).trace.re - h * Real.log h -
      (P * diagonal (fun i => (logDensity i : ℂ))).trace.re)

/-- At fixed determinant the real-power deficit is the convex interpolation of the two physical
occupation endpoints. The formal identity allows any real `s`, independent real weights and a
fixed real occupation diagonal. For physical `s > 1` it includes singular PSD fibers by continuity. -/
theorem realPowerDeficit_affine (s α : ℝ) (projectionRate mixedRate : Fin 2 → Bool → ℝ)
    (logDensity : Occupation → ℝ) (U : Block) (hU : Uᴴ * U = 1) (d : AlignedData) :
    let p := Complex.normSq (U 0 0)
    let V := diagonalFrame U.det
    let W := antidiagonalFrame U.det
    let deficit := weightedDeficit s α projectionRate mixedRate logDensity
    0 ≤ p ∧ p ≤ 1 ∧
    deficit (orbitMatrix U d) =
      p * deficit (orbitMatrix V d) + (1 - p) * deficit (orbitMatrix W d) := by
  obtain ⟨hV, _, _, hW, _, _⟩ := endpoint_frames U.det (det_phase U hU)
  let p := Complex.normSq (U 0 0)
  let V := diagonalFrame U.det
  let W := antidiagonalFrame U.det
  let P := cfcData (fun t : ℝ => t ^ s) d
  let Q := cfcData (fun t : ℝ => t ^ (s - 1)) d
  have powerP (R : Block) (hR : Rᴴ * R = 1) : mpow (orbitMatrix R d) s = orbitMatrix R P :=
    orbit_cfc R hR _ d
  have powerQ (R : Block) (hR : Rᴴ * R = 1) : mpow (orbitMatrix R d) (s - 1) = orbitMatrix R Q :=
    orbit_cfc R hR _ d
  have hTerm (k : Fin 2) (reverse : Bool) :
      let J := directedJump k reverse
      let term (R : Block) := projectionRate k reverse * (orbitMatrix R P * (Jᴴ * J)).trace.re -
        mixedRate k reverse * (orbitMatrix R Q * (Jᴴ * orbitMatrix R d * J)).trace.re
      term U = p * term V + (1 - p) * term W := by
    dsimp only
    rw [mode_mixed_trace_affine U hU d Q k reverse]
    rw [jump_projection k reverse]
    rw [diagonal_pairing_affine U hU P]
    ring
  have sumAffine (k : Fin 2) := fun b => hTerm k b
  have spectralU := spectral_terms U hU s d
  have spectralV := spectral_terms V hV s d
  have spectralW := spectral_terms W hW s d
  refine ⟨Complex.normSq_nonneg _, ?_, ?_⟩
  · linarith only [(norm_weights U hU).1, Complex.normSq_nonneg (U 0 1)]
  dsimp only [weightedDeficit, V, W] at spectralV spectralW ⊢
  rw [spectralU.1, spectralU.2, spectralV.1, spectralV.2, spectralW.1, spectralW.2]
  simp only [powerP U hU, powerP (diagonalFrame U.det) hV, powerP (antidiagonalFrame U.det) hW,
    powerQ U hU, powerQ (diagonalFrame U.det) hV, powerQ (antidiagonalFrame U.det) hW,
    diagonal_pairing_affine U hU P]
  simp only [V, W, p] at sumAffine
  simp only [sumAffine, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

end D5.S3.Quantum.Semigroups.WuAlignedRealPowerOrbit
