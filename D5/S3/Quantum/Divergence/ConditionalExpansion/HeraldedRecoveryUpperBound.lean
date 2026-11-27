/- GID: D5/S3/Quantum/Divergence/ConditionalExpansion/HeraldedRecoveryUpperBound
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/ConditionalExpansion/HeraldedRecoveryUpperBound
   mirror-E: none(waiver:finite-matrix-proof)
   anchors: []
   utility: none
   digest: A heralded exact recovery bounds conditional trace expansion from above. -/

import D5.S3.Quantum.Divergence.ConditionalExpansion.BellKernelLimit
import D5.S3.Quantum.Divergence.ConditionalExpansion.DirectBellKrausRecovery

/-! The columns of the Bell-complement output kernel projection give an explicit
successful branch of exact recovery for a finite channel. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Quantum.Divergence.ConditionalExpansion

open _root_.Matrix
open scoped CStarAlgebra ComplexOrder MatrixOrder
open RHLinalg (rtrace rtrace_sub trace_mul_nonneg_of_posSemidef)
open BellCenteredConditionalTraceGap (bellProjector)
open D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction (act amp gap)
open D5.S3.Quantum.Divergence.CompleteHockeyStickRefutation (amp_psd)
open D5.S3.Quantum.Foundation.FiniteStateChannel (DensityState QuantumChannel)
open D5.S3.Quantum.Foundation.FiniteKrausChannel (krausRepresentation)
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf (MatrixMap)
open D5.S3.Quantum.Lieb.SupportPerspectiveTransport (spectral_sqrt_normalization)
open D5.S3.Quantum.Recovery.SpectralTransposeRecovery (spectralSupport)
open UnitaryReconstruction.LiuWildChoiObstruction (bell bell_norm outer pairMatrix)

open private canonicalCPOfPhyslib from D5.S3.Quantum.Foundation.FiniteKrausChannel
open private amp_eq_amplifyKraus from
  D5.S3.Quantum.Divergence.ConditionalExpansion.DirectBellKrausRecovery

variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- The canonical CP map whose Kraus operators are the reshaped columns of the
Bell-complement output kernel projection. -/
def bellKernelRecovery (N : QuantumChannel A B) :
    CompletelyPositiveMap (CStarMatrix B B ℂ) (CStarMatrix A A ℂ) :=
  let Q := 1 - spectralSupport (amp N (1 - bellProjector A))
  let R := bellRecoveryKraus Q.col
  canonicalCPOfPhyslib (MatrixMap.of_kraus R R) (MatrixMap.of_kraus_isCompletelyPositive R)

/-- Every finite channel of input dimension at least two has a Bell-kernel recovery
branch with success probability `p`. The branch is completely positive, is trace
nonincreasing on positive inputs, and recovers every input matrix up to the scalar
`p`. Orthogonal states on the reference `Option A` give actual conditional trace
ratios strictly below `d²p + ε` for every `ε > 0`. -/
theorem heralded_recovery_upper_bound (N : QuantumChannel A B) (hd : 2 ≤ Fintype.card A) :
    let P := bellProjector A
    let Q := 1 - spectralSupport (amp N (1 - P))
    let d : ℝ := Fintype.card A
    let p := rtrace (Q * amp N P) / d ^ 2
    let recovery := bellKernelRecovery N
    0 ≤ p ∧ p ≤ 1 ∧
      (∀ Y : Matrix B B ℂ, Y.PosSemidef →
        rtrace (CStarMatrix.ofMatrix.symm (recovery (CStarMatrix.ofMatrix Y))) ≤ rtrace Y) ∧
      (∀ X : Matrix A A ℂ,
        CStarMatrix.ofMatrix.symm (recovery (N.toCompletelyPositiveMap (CStarMatrix.ofMatrix X))) =
          (p : ℂ) • X) ∧
      ∀ ε : ℝ, 0 < ε → ∃ ρ σ : DensityState (Option A × A),
        pairMatrix ρ * pairMatrix σ = 0 ∧
        0 < gap 1 (pairMatrix ρ) (pairMatrix σ) ∧
        gap 1 (amp N (pairMatrix ρ)) (amp N (pairMatrix σ)) /
          gap 1 (pairMatrix ρ) (pairMatrix σ) < d ^ 2 * p + ε := by
  classical
  intro P Q d p recovery
  have : Nonempty A := Fintype.card_pos_iff.mp (by omega)
  let representation := krausRepresentation N.toCompletelyPositiveMap
  let K := representation.val
  have hK (X : Matrix A A ℂ) : act N X = MatrixMap.of_kraus K K X := by
    simpa only [act, K, MatrixMap.of_kraus, LinearMap.sum_apply, LinearMap.coe_mk, AddHom.coe_mk]
      using representation.property X
  have hP : IsStarProjection P := by
    refine isStarProjection_iff'.mpr ⟨?_, ?_⟩
    · change outer (bell A) * outer (bell A) = outer (bell A)
      rw [Matrix.vecMulVec_mul_vecMulVec, show star (bell A) ⬝ᵥ bell A = 1 from bell_norm,
        one_smul]
    · change (outer (bell A))ᴴ = outer (bell A)
      simp only [Matrix.conjTranspose_vecMulVec, star_star]
  have hB : (amp N (1 - P)).PosSemidef := amp_psd N hP.one_sub.nonneg.posSemidef
  obtain ⟨-, -, hSadj, hSidem, -, -, -, -⟩ := spectral_sqrt_normalization _ hB
  have hQ : IsStarProjection Q := (isStarProjection_iff'.mpr ⟨hSidem, hSadj⟩).one_sub
  have hGram : (∑ j, outer (Q.col j)) = Q := by
    calc
      _ = Q * Qᴴ := by
        ext x y
        simp only [Matrix.sum_apply, Matrix.vecMulVec_apply, Matrix.col_apply, Pi.star_apply,
          Matrix.mul_apply, Matrix.conjTranspose_apply]
      _ = Q := by rw [show Qᴴ = Q from hQ.isSelfAdjoint.star_eq, hQ.isIdempotentElem.eq]
  have hkernel : (∑ j, outer (Q.col j)) =
      1 - spectralSupport (amplifyKraus K (1 - outer (bell A))) := by
    rw [hGram, ← amp_eq_amplifyKraus N K hK]
    rfl
  obtain ⟨-, -, -, -, heffect, -, hp, hcomp⟩ := direct_bell_kernel_recovery K Q.col hkernel
  let R := bellRecoveryKraus Q.col
  let f := MatrixMap.of_kraus R R
  have hf (Y : Matrix B B ℂ) : f Y = ∑ j, R j * Y * (R j)ᴴ := by
    simp only [f, MatrixMap.of_kraus, LinearMap.sum_apply, LinearMap.coe_mk, AddHom.coe_mk]
  let pComplex := (Q * amp N P).trace / (Fintype.card A : ℂ) ^ 2
  have hX : amplifyKraus K (outer (bell A)) = amp N P :=
    (amp_eq_amplifyKraus N K hK P).symm
  have hpComplex_nonneg : 0 ≤ pComplex := by
    simpa only [hGram, hX] using hp
  have hpComplex : pComplex = (p : ℂ) := by
    have hre : pComplex.re = p := by
      dsimp only [pComplex, p, d, rtrace]
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_pow, Complex.div_ofReal_re]
      rfl
    exact (Complex.eq_re_of_ofReal_le hpComplex_nonneg).trans (congrArg Complex.ofReal hre)
  have hact (Y : Matrix B B ℂ) : rtrace (f Y) =
      rtrace ((∑ j, (R j)ᴴ * R j) * Y) := by
    rw [hf]
    unfold rtrace
    rw [Matrix.sum_mul, Matrix.trace_sum, Matrix.trace_sum]
    congr 1
    exact Finset.sum_congr rfl (fun j _ => by
      rw [Matrix.trace_mul_comm (R j * Y), ← Matrix.mul_assoc])
  have hTNI (Y : Matrix B B ℂ) (hY : Y.PosSemidef) : rtrace (f Y) ≤ rtrace Y := by
    have hn : 0 ≤ rtrace ((1 - ∑ j, (R j)ᴴ * R j) * Y) :=
      trace_mul_nonneg_of_posSemidef (Matrix.le_iff.mp heffect) hY
    rwa [Matrix.sub_mul, Matrix.one_mul, rtrace_sub, ← hact, sub_nonneg] at hn
  have hrec (X : Matrix A A ℂ) : f (act N X) = (p : ℂ) • X := by
    rw [hK, ← hpComplex]
    simpa only [hGram, hX] using hcomp X
  have hp0 : 0 ≤ p := RCLike.nonneg_iff.mp (hpComplex ▸ hpComplex_nonneg) |>.1
  have hp1 : p ≤ 1 := by
    have h_one : (1 : Matrix A A ℂ).PosSemidef := Matrix.PosSemidef.one
    have hY : (act N (1 : Matrix A A ℂ)).PosSemidef :=
      (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm
        (map_nonneg N.toCompletelyPositiveMap
          (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv h_one.nonneg))).posSemidef
    have htrace : (act N (1 : Matrix A A ℂ)).trace = (1 : Matrix A A ℂ).trace :=
      N.trace_preserving (CStarMatrix.ofMatrix 1)
    have hle := hTNI _ hY
    rw [hrec, rtrace, rtrace, Matrix.trace_smul, htrace, Matrix.trace_one] at hle
    have hd0 : 0 < d := by
      change (0 : ℝ) < Fintype.card A
      exact_mod_cast (Fintype.card_pos : 0 < Fintype.card A)
    have hpd : p * d ≤ 1 * d := by
      simpa [d, smul_eq_mul, ← Complex.ofReal_natCast, ← Complex.ofReal_mul] using hle
    exact le_of_mul_le_mul_right hpd hd0
  refine ⟨hp0, hp1, hTNI, hrec, ?_⟩
  intro ε hε
  obtain ⟨ρ, σ, horth, hgap, hratio⟩ := exists_bell_kernel_ratio_le N hd (ε / 2) (by positivity)
  have hscale : d ^ 2 * p = rtrace (Q * amp N P) := by
    have hd0 : d ^ 2 ≠ 0 := pow_ne_zero _ (by
      change (Fintype.card A : ℝ) ≠ 0
      exact_mod_cast Fintype.card_ne_zero)
    rw [mul_comm]
    exact div_mul_cancel₀ _ hd0
  rw [hscale]
  exact ⟨ρ, σ, horth, hgap, hratio.trans_lt (by linarith)⟩

#print axioms bellKernelRecovery
#print axioms heralded_recovery_upper_bound

end D5.S3.Quantum.Divergence.ConditionalExpansion
