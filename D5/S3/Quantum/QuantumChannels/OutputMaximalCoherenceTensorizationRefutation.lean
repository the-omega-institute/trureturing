/- GID: D5/S3/Quantum/QuantumChannels/OutputMaximalCoherenceTensorizationRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/QuantumChannels/OutputMaximalCoherenceTensorizationRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/QuantumChannels/OutputMaximalCoherenceTensorizationRefutation.claim; result=D5/S3/Quantum/QuantumChannels/OutputMaximalCoherenceTensorizationRefutation.result; claim=D5/S3/Quantum/QuantumChannels/OutputMaximalCoherenceTensorizationRefutation.claim
   digest: A Pauli channel and Bell input refute tensorization of output maximal coherence. -/

import D5.S3.QuantumChannels.PauliThreeWeightBayesianInverseUniqueness
import D5.S3.Quantum.Matrix.CartesianVariance
import D5.S3.QuantumBounds.CHSHWitness

set_option linter.style.longLine false

noncomputable section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Kronecker
open D5.S3.Quantum.Foundation.FiniteStateChannel (DensityState)
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf (MatrixMap)
open D5.S3.Quantum.FiniteDimensional (qubitX qubitZ)
open D5.S3.QuantumChannels.PauliThreeWeightBayesianInverseUniqueness (sigma sigma_properties)
open D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence (pauliMatrix)
open D5.S3.QuantumBounds.CHSHWitness (bellDensity bellVector bell_density_is_state)

namespace D5.S3.Quantum.QuantumChannels.OutputMaximalCoherenceTensorizationRefutation

/-- Maximal coherence in the fixed basis; unsupported pairs contribute zero. -/
def maxCoherence {n : Type*} [Fintype n] (ρ : Matrix n n ℂ) : ℝ :=
  open scoped Classical in
  sSup (insert 0 (Set.range (fun p : n × n =>
    if p.1 ≠ p.2 ∧ 0 < (ρ p.1 p.1).re * (ρ p.2 p.2).re then
      ‖ρ p.1 p.2‖ / Real.sqrt ((ρ p.1 p.1).re * (ρ p.2 p.2).re) else 0)))

/-- The action of a finite Kraus family, using the canonical matrix-map API. -/
def krausApply {a b κ : Type*} [Fintype a] [DecidableEq a] [Fintype κ]
    (K : κ → Matrix b a ℂ) (ρ : Matrix a a ℂ) : Matrix b b ℂ :=
  MatrixMap.of_kraus K K ρ

/-- Trace preservation of a Kraus family. -/
def IsKrausChannel {a b κ : Type*} [Fintype a] [DecidableEq a]
    [Fintype b] [Fintype κ] (K : κ → Matrix b a ℂ) : Prop :=
  ∑ r, (K r)ᴴ * K r = 1

/-- Supremum of maximal coherence over all density inputs, including entangled inputs. -/
def outputMaxCoherence {a b κ : Type*} [Fintype a] [DecidableEq a]
    [Fintype b] [Fintype κ] (K : κ → Matrix b a ℂ) : ℝ :=
  sSup {x | ∃ ρ : DensityState a, x = maxCoherence (krausApply K ρ.1)}

/-- Kraus operators of the tensor product in the fixed product basis. -/
def krausTensor {a b c d κ ι : Type*}
    (K : κ → Matrix b a ℂ) (L : ι → Matrix d c ℂ) :
    κ × ι → Matrix (b × d) (a × c) ℂ :=
  fun r => K r.1 ⊗ₖ L r.2

/-- Lee–Baek–Park–Kim–Nha, Conjecture 1, arXiv:2104.12307v2, Eq. (29). -/
def claim : Prop :=
  ∀ (a b c d κ ι : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d] [Fintype κ] [Fintype ι]
    (K : κ → Matrix b a ℂ) (L : ι → Matrix d c ℂ),
    IsKrausChannel K → IsKrausChannel L →
    outputMaxCoherence (krausTensor K L) = max (outputMaxCoherence K) (outputMaxCoherence L)

private theorem coherence_le {n : Type*} [Fintype n] (ρ : Matrix n n ℂ) (c : ℝ)
    (hc : 0 ≤ c)
    (h : ∀ i j, i ≠ j → 0 < (ρ i i).re * (ρ j j).re →
      ‖ρ i j‖ / Real.sqrt ((ρ i i).re * (ρ j j).re) ≤ c) : maxCoherence ρ ≤ c := by
  classical
  rw [maxCoherence.eq_1]
  apply csSup_le (Set.insert_nonempty _ _)
  rintro x (rfl | ⟨⟨i,j⟩, rfl⟩)
  · exact hc
  · dsimp only
    split_ifs with hp
    · exact h i j hp.1 hp.2
    · exact hc

private theorem coherence_pair_le {n : Type*} [Fintype n] (ρ : Matrix n n ℂ)
    (i j : n) (hij : i ≠ j) (hp : 0 < (ρ i i).re * (ρ j j).re) :
    ‖ρ i j‖ / Real.sqrt ((ρ i i).re * (ρ j j).re) ≤ maxCoherence ρ := by
  classical
  rw [maxCoherence.eq_1]
  apply le_csSup ((Set.finite_range _).insert 0).bddAbove
  exact Set.mem_insert_of_mem _ ⟨(i,j), if_pos ⟨hij,hp⟩⟩

private theorem coherence_psd_le_one {n : Type*} [Fintype n]
    (ρ : Matrix n n ℂ) (hρ : ρ.PosSemidef) : maxCoherence ρ ≤ 1 := by
  classical
  apply coherence_le ρ 1 (by norm_num)
  intro i j _ hp
  apply (div_le_one (Real.sqrt_pos.mpr hp)).mpr
  apply (Real.le_sqrt (norm_nonneg _ ) hp.le).mpr
  simpa only [Complex.normSq_eq_norm_sq] using
    D5.S3.Quantum.Matrix.CartesianVariance.psd_entry_bound hρ i j

private theorem kraus_psd {a b κ : Type*} [Fintype a] [DecidableEq a]
    [Finite b] [Fintype κ] (K : κ → Matrix b a ℂ)
    (ρ : Matrix a a ℂ) (hρ : ρ.PosSemidef) : (krausApply K ρ).PosSemidef := by
  classical
  let := Fintype.ofFinite b
  rw [krausApply.eq_1, MatrixMap.of_kraus]
  simp only [LinearMap.sum_apply, LinearMap.coe_mk, AddHom.coe_mk]
  exact Matrix.posSemidef_sum _ (fun r _ => hρ.mul_mul_conjTranspose_same (K r))

private theorem output_bdd {a b κ : Type*} [Fintype a] [DecidableEq a]
    [Fintype b] [Fintype κ] (K : κ → Matrix b a ℂ) :
    BddAbove {x | ∃ ρ : DensityState a, x = maxCoherence (krausApply K ρ.1)} := by
  classical
  refine ⟨1, ?_⟩
  rintro x ⟨ρ, rfl⟩
  exact coherence_psd_le_one _ (kraus_psd K _ (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm ρ.2.1).posSemidef)

private def weights : Fin 4 → ℝ := ![31/40, 1/10, 1/10, 1/40]

private def witness : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ :=
  fun r => (Real.sqrt (weights r) : ℂ) • sigma r

private theorem weights_nonneg (r : Fin 4) : 0 ≤ weights r := by
  fin_cases r <;> norm_num [weights.eq_1]

private theorem sqrt_term {a b : Type*} [Fintype a] (p : ℝ) (hp : 0 ≤ p)
    (P : Matrix b a ℂ) (ρ : Matrix a a ℂ) :
    ((Real.sqrt p : ℂ) • P) * ρ * ((Real.sqrt p : ℂ) • P)ᴴ =
      (p : ℂ) • (P * ρ * Pᴴ) := by
  simp only [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← Complex.ofReal_mul,
    Real.mul_self_sqrt hp]

private theorem witness_apply (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    krausApply witness ρ =
      !![(4/5 : ℂ) * ρ 0 0 + (1/5 : ℂ) * ρ 1 1, (3/4 : ℂ) * ρ 0 1;
        (3/4 : ℂ) * ρ 1 0, (1/5 : ℂ) * ρ 0 0 + (4/5 : ℂ) * ρ 1 1] := by
  rw [krausApply.eq_1, MatrixMap.of_kraus]
  simp only [LinearMap.sum_apply, LinearMap.coe_mk, AddHom.coe_mk, witness.eq_1]
  simp_rw [sqrt_term _ (weights_nonneg _)]
  ext i j
  fin_cases i <;> fin_cases j <;>
    apply Complex.ext <;>
    norm_num [Fin.sum_univ_succ, weights.eq_1, sigma, pauliMatrix, qubitX, qubitZ,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.conjTranspose_apply,
      Matrix.smul_apply, smul_eq_mul] <;> ring


private theorem witness_normalized : IsKrausChannel witness := by
  rw [IsKrausChannel.eq_1]
  simp only [witness.eq_1, Matrix.conjTranspose_smul, Complex.star_def,
    Complex.conj_ofReal, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    ← Complex.ofReal_mul, Real.mul_self_sqrt (weights_nonneg _)]
  simp_rw [(sigma_properties _).1, (sigma_properties _).2]
  rw [← Finset.sum_smul, ← Complex.ofReal_sum]
  norm_num [weights.eq_1, Fin.sum_univ_succ]

private theorem ratio_bound (a b : ℝ) (z : ℂ)
    (hz : ‖z‖ ^ 2 ≤ a * b)
    (hp : 0 < (4 / 5 * a + 1 / 5 * b) * (1 / 5 * a + 4 / 5 * b)) :
    (3/4 : ℝ) * ‖z‖ / Real.sqrt ((4 / 5 * a + 1 / 5 * b) * (1 / 5 * a + 4 / 5 * b)) ≤ 3/4 := by
  have hd : a * b ≤ (4 / 5 * a + 1 / 5 * b) * (1 / 5 * a + 4 / 5 * b) := by
    nlinarith [sq_nonneg (a - b)]
  have hn : ‖z‖ ≤ Real.sqrt ((4 / 5 * a + 1 / 5 * b) * (1 / 5 * a + 4 / 5 * b)) :=
    (Real.le_sqrt (norm_nonneg _) hp.le).mpr (hz.trans hd)
  apply (div_le_iff₀ (Real.sqrt_pos.mpr hp)).mpr
  nlinarith

private theorem witness_coherence_le (ρ : Matrix (Fin 2) (Fin 2) ℂ)
    (hρ : ρ.PosSemidef) : maxCoherence (krausApply witness ρ) ≤ 3/4 := by
  rw [witness_apply]
  apply coherence_le _ (3/4) (by norm_num)
  intro i j hij hp
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · norm_num [Complex.mul_re] at hp ⊢
    exact ratio_bound _ _ _ (by simpa only [Complex.normSq_eq_norm_sq] using
      D5.S3.Quantum.Matrix.CartesianVariance.psd_entry_bound hρ 0 1) hp
  · norm_num [Complex.mul_re] at hp ⊢
    simpa only [add_comm] using ratio_bound (ρ 1 1).re (ρ 0 0).re (ρ 1 0)
      (by simpa only [Complex.normSq_eq_norm_sq] using
        D5.S3.Quantum.Matrix.CartesianVariance.psd_entry_bound hρ 1 0)
      (by simpa only [add_comm] using hp)
  · exact (hij rfl).elim

private theorem witness_output_upper : outputMaxCoherence witness ≤ 3/4 := by
  let ρ : DensityState (Fin 2) :=
    ⟨CStarMatrix.ofMatrix ((1/2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)),
      map_nonneg CStarMatrix.ofMatrixStarAlgEquiv
        ((Matrix.PosSemidef.one.smul (by norm_num : (0 : ℝ) ≤ 1/2)).nonneg),
      by
        change Matrix.trace ((1/2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) = 1
        norm_num [Matrix.trace, Matrix.diag, Fin.sum_univ_two]⟩
  rw [outputMaxCoherence.eq_1]
  refine csSup_le ⟨maxCoherence (krausApply witness ρ.1), ρ, rfl⟩ ?_
  rintro x ⟨σ, rfl⟩
  exact witness_coherence_le _
    (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm σ.2.1).posSemidef

private theorem tensor_apply_product {a b c d κ ι : Type*}
    [Fintype a] [DecidableEq a] [Fintype c] [DecidableEq c]
    [Fintype κ] [Fintype ι]
    (K : κ → Matrix b a ℂ) (L : ι → Matrix d c ℂ)
    (ρ : Matrix a a ℂ) (σ : Matrix c c ℂ) :
    krausApply (krausTensor K L) (ρ ⊗ₖ σ) = krausApply K ρ ⊗ₖ krausApply L σ := by
  classical
  repeat rw [krausApply.eq_1]
  simp only [MatrixMap.of_kraus, LinearMap.sum_apply,
    LinearMap.coe_mk, AddHom.coe_mk, krausTensor.eq_1,
    Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, Fintype.sum_prod_type]
  ext ⟨i,k⟩ ⟨j,l⟩
  simp only [Matrix.sum_apply, Matrix.kronecker_apply, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm

private theorem bell_expansion : bellDensity = (1/2 : ℂ) •
    ((Matrix.single 0 0 1 ⊗ₖ Matrix.single 0 0 1) +
     (Matrix.single 0 1 1 ⊗ₖ Matrix.single 0 1 1) +
     (Matrix.single 1 0 1 ⊗ₖ Matrix.single 1 0 1) +
     (Matrix.single 1 1 1 ⊗ₖ Matrix.single 1 1 1)) := by
  ext ⟨i,k⟩ ⟨j,l⟩
  fin_cases i <;> fin_cases k <;> fin_cases j <;> fin_cases l <;>
    norm_num [bellDensity, bellVector, D5.S3.Quantum.QubitWitnesses.bellCoefficients,
      Matrix.vecMulVec, Matrix.single, Matrix.kronecker_apply, smul_eq_mul,
      D5.S3.QuantumBounds.CHSHWitness.complex_sqrt_two_inv_mul_self]

private theorem bell_output (i j : Fin 2 × Fin 2) :
    krausApply (krausTensor witness witness) bellDensity i j =
      if i = j then (if i.1 = i.2 then 17/50 else 4/25)
      else (if i.1 = i.2 ∧ j.1 = j.2 then 9/32 else 0) := by
  rw [bell_expansion]
  change MatrixMap.of_kraus _ _ _ i j = _
  simp only [map_smul, map_add]
  change ((1/2 : ℂ) •
    (krausApply (krausTensor witness witness) (Matrix.single 0 0 1 ⊗ₖ Matrix.single 0 0 1) +
     krausApply (krausTensor witness witness) (Matrix.single 0 1 1 ⊗ₖ Matrix.single 0 1 1) +
     krausApply (krausTensor witness witness) (Matrix.single 1 0 1 ⊗ₖ Matrix.single 1 0 1) +
     krausApply (krausTensor witness witness) (Matrix.single 1 1 1 ⊗ₖ Matrix.single 1 1 1))) i j = _
  repeat rw [tensor_apply_product]
  repeat rw [witness_apply]
  rcases i with ⟨i,k⟩
  rcases j with ⟨j,l⟩
  fin_cases i <;> fin_cases k <;> fin_cases j <;> fin_cases l <;>
    norm_num [Matrix.single, Matrix.kronecker_apply, smul_eq_mul]

private theorem bell_output_lower :
    (225/272 : ℝ) ≤ outputMaxCoherence (krausTensor witness witness) := by
  let ρ : DensityState (Fin 2 × Fin 2) :=
    ⟨CStarMatrix.ofMatrix bellDensity,
      map_nonneg CStarMatrix.ofMatrixStarAlgEquiv bell_density_is_state.1.nonneg,
      bell_density_is_state.2⟩
  have hpair := coherence_pair_le
    (krausApply (krausTensor witness witness) bellDensity) (0,0) (1,1)
    (by decide) (by rw [bell_output, bell_output]; norm_num)
  have hvalue : (225/272 : ℝ) ≤
      maxCoherence (krausApply (krausTensor witness witness) bellDensity) := by
    convert hpair using 1
    rw [bell_output, bell_output, bell_output]
    norm_num
  exact hvalue.trans (le_csSup (output_bdd _) ⟨ρ, rfl⟩)

/-- Entangled Bell inputs violate the conjectured tensorization equality. -/
theorem result : ¬ claim := by
  intro h
  rw [claim.eq_1] at h
  have heq := h (Fin 2) (Fin 2) (Fin 2) (Fin 2) (Fin 4) (Fin 4)
    witness witness witness_normalized witness_normalized
  have hu := witness_output_upper
  have hl := bell_output_lower
  rw [heq, max_self] at hl
  exact (by norm_num : ¬ ((225/272 : ℝ) ≤ 3/4)) (hl.trans hu)

end D5.S3.Quantum.QuantumChannels.OutputMaximalCoherenceTensorizationRefutation
