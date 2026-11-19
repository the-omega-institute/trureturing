/- GID: D5/S3/Quantum/Fermionic/BravyiThreeModePhysicalEntropy
   generality: G
   mirror-B: D5/B/S3/Quantum/Fermionic/BravyiThreeModePhysicalEntropy
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: Physical output entropy of the three-mode Bravyi channel on its normal form. -/

import D5.S3.Quantum.Fermionic.BravyiThreeModeCARBlocks
import D5.S3.Quantum.Fermionic.FiniteSpectrumShiftedLogEntropy
import D5.S3.Quantum.Information.PartialTraceMutualInformation

/-!
# Physical output entropy in the three-mode normal form

For the isotropic channel of Bravyi, *Classical capacity of fermionic product
channels*, arXiv:quant-ph/0507282, §V.B, the comparator on the real normal form
has amplitudes `(√(1/2), 0, √(1/2))`. The characteristic polynomial records
the multiplicities of the chiral and both complementary blocks, including
zero eigenvalues at the endpoints.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Fermionic.BravyiThreeModePhysicalEntropy

open scoped BigOperators ComplexOrder Matrix MatrixOrder
open BravyiThreeModeCARBlocks BravyiThreeModeDeterminantOrder FiniteSpectrumShiftedLogEntropy
open D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition (DensityState)
open D5.S3.Quantum.Divergence.VonNeumannEntropyPinching (vonNeumannEntropy)
open D5.S3.Quantum.Information.PartialTraceMutualInformation
  (charpoly_conj_unitary entropy_eq_spectral)

noncomputable section

private theorem normalInput_posSemidef (c p q : ℝ) : (normalInput c p q).PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star fun i => (spinor c p q i : ℂ)

private theorem weight_nonneg {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (k : Fin 7) :
    0 ≤ weight lam k := by
  have h : 0 ≤ 1 - lam := sub_nonneg.mpr h1
  unfold weight
  positivity

private theorem channel_posSemidef {A : SpinMatrix} (hA : A.PosSemidef)
    {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1) : (channel lam A).PosSemidef := by
  apply Matrix.posSemidef_sum
  intro m _
  change (weight lam (degree m) • conjugateWord m A).PosSemidef
  exact (hA.mul_mul_conjTranspose_same (word m)).smul (weight_nonneg h0 h1 _)

private theorem degree_count (k : Fin 7) :
    (Finset.univ.filter (fun m : Fin 64 => degree m = k)).card = Nat.choose 6 k.val := by
  revert k
  decide

private theorem sum_weight (lam : ℝ) : (∑ m : Fin 64, weight lam (degree m)) = 1 := by
  have hgroup :
      (∑ k : Fin 7, ∑ m ∈ Finset.univ.filter (fun m : Fin 64 => degree m = k), weight lam k) =
        ∑ m : Fin 64, weight lam (degree m) := by
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    simp
  rw [← hgroup]
  simp only [Finset.sum_const, degree_count, nsmul_eq_mul]
  norm_num [Fin.sum_univ_succ, weight, Nat.choose]
  ring

private theorem trace_channel (lam : ℝ) (A : SpinMatrix) : (channel lam A).trace = A.trace := by
  unfold channel
  rw [Matrix.trace_sum]
  have hword (m : Fin 64) : (conjugateWord m A).trace = A.trace := by
    rw [conjugateWord, Matrix.trace_mul_cycle, (word_unitary m).2, one_mul]
  simp_rw [Matrix.trace_smul, hword, smul_eq_mul]
  rw [← Finset.sum_mul, ← Complex.ofReal_sum, sum_weight, Complex.ofReal_one, one_mul]

/-- The physical output density state of a normalized chiral normal-form spinor. -/
def normalOutput {lam c p q : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (hn : c ^ 2 + p ^ 2 + q ^ 2 = 1) : DensityState (Fin 8) := by
  refine ⟨CStarMatrix.ofMatrix (channel lam (normalInput c p q)), ?_, ?_⟩
  · exact map_nonneg CStarMatrix.ofMatrixStarAlgEquiv
      (channel_posSemidef (normalInput_posSemidef c p q) h0 h1).nonneg
  · change (channel lam (normalInput c p q)).trace = 1
    rw [trace_channel, trace_normalInput, hn, Complex.ofReal_one]

private theorem comparator_normalized :
    comparatorAmplitude ^ 2 + (0 : ℝ) ^ 2 + comparatorAmplitude ^ 2 = 1 := by
  have hs : comparatorAmplitude ^ 2 = 1 / 2 := Real.sq_sqrt (by norm_num)
  norm_num [hs]

/-- The physical comparator is the output of the same channel on the comparator spinor. -/
def comparatorOutput {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1) : DensityState (Fin 8) :=
  normalOutput h0 h1 comparator_normalized

private theorem roots_real_block {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian) :
    (A.charpoly.map Complex.ofRealHom).roots =
      Finset.univ.val.map (Complex.ofReal ∘ hA.eigenvalues) := by
  rw [hA.charpoly_eq]
  simp only [RCLike.ofReal_real_eq_id, id_eq, Polynomial.map_prod, Polynomial.map_sub,
    Polynomial.map_X, Polynomial.map_C]
  rw [Polynomial.roots_prod]
  · simp
  · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]

/-- The multiset of physical eigenvalues contains both copies of the complementary spectrum. -/
theorem normalOutput_spectrum {lam c p q : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (hn : c ^ 2 + p ^ 2 + q ^ 2 = 1) :
    let h := (channel_posSemidef (normalInput_posSemidef c p q) h0 h1).isHermitian
    let M := Finset.univ.val.map (chiral_isHermitian lam c p q).eigenvalues
    let N := Finset.univ.val.map (complement_isHermitian lam c q).eigenvalues
    Finset.univ.val.map h.eigenvalues = M + (N + N) := by
  dsimp only
  let A := channel lam (normalInput c p q)
  have hA : A.IsHermitian := (channel_posSemidef (normalInput_posSemidef c p q) h0 h1).isHermitian
  have hU : star signedBasis * signedBasis = 1 :=
    mul_eq_one_comm.mp signedBasis_isUnitary
  have hchar : A.charpoly =
      ((chiral lam c p q).charpoly.map Complex.ofRealHom) *
      ((complement lam c q).charpoly.map Complex.ofRealHom *
        (complement lam c q).charpoly.map Complex.ofRealHom) := by
    rw [← charpoly_conj_unitary (ρ := A) hU]
    change (signedBasis * channel lam (normalInput c p q) * signedBasisᴴ).charpoly = _
    rw [channel_normal_blocks lam c p q hn]
    change ((determinantBlocks (chiral lam c p q) (complement lam c q)).map
      Complex.ofRealHom).charpoly = _
    rw [Matrix.charpoly_map, determinantBlocks_charpoly, Polynomial.map_mul, Polynomial.map_mul]
  have hM := ((chiral lam c p q).charpoly_monic.map Complex.ofRealHom).ne_zero
  have hN := ((complement lam c q).charpoly_monic.map Complex.ofRealHom).ne_zero
  have hroots := congrArg Polynomial.roots hchar
  rw [Polynomial.roots_mul (mul_ne_zero hM (mul_ne_zero hN hN)),
    Polynomial.roots_mul (mul_ne_zero hN hN), roots_real_block (chiral_isHermitian lam c p q),
    roots_real_block (complement_isHermitian lam c q), hA.roots_charpoly_eq_eigenvalues] at hroots
  have hreal := congrArg (Multiset.map Complex.re) hroots
  simp only [Multiset.map_add, Multiset.map_map, Function.comp_def,
    RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_re] at hreal
  exact hreal

/-- Physical von Neumann entropy is the chiral block entropy plus twice the complementary
block entropy, with each sum taken over the entire spectrum of its real matrix. -/
theorem normalOutput_entropy_eq_blocks {lam c p q : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (hn : c ^ 2 + p ^ 2 + q ^ 2 = 1) :
    let a := (chiral_isHermitian lam c p q).eigenvalues
    let u := (complement_isHermitian lam c q).eigenvalues
    vonNeumannEntropy (normalOutput h0 h1 hn) =
      -((∑ i, a i * Real.log (a i)) + 2 * (∑ i, u i * Real.log (u i))) := by
  rw [entropy_eq_spectral]
  let hA := (channel_posSemidef (normalInput_posSemidef c p q) h0 h1).isHermitian
  change (∑ i, Real.negMulLog (hA.eigenvalues i)) = _
  simp only [Real.negMulLog, neg_mul, Finset.sum_neg_distrib, two_mul]
  simp only [Finset.sum_eq_multiset_sum]
  have hs := congrArg (fun xs : Multiset ℝ => (xs.map (fun x => x * Real.log x)).sum)
    (normalOutput_spectrum h0 h1 hn)
  simp only [Multiset.map_add, Multiset.map_map, Multiset.sum_add, Function.comp_def] at hs
  exact congrArg Neg.neg hs

/-- The physical Bravyi comparator minimizes output entropy on the normalized three-mode
normal form over the full closed interval of isotropic attenuations. -/
theorem comparator_entropy_le_normalOutput {lam c p q : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (hn : c ^ 2 + p ^ 2 + q ^ 2 = 1) :
    vonNeumannEntropy (comparatorOutput h0 h1) ≤ vonNeumannEntropy (normalOutput h0 h1 hn) := by
  rw [comparatorOutput, normalOutput_entropy_eq_blocks, normalOutput_entropy_eq_blocks]
  exact bravyi_three_mode_entropy_ge_comparator h0 h1 hn

end

end D5.S3.Quantum.Fermionic.BravyiThreeModePhysicalEntropy
