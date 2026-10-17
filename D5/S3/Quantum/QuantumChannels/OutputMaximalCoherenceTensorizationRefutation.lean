/- GID: D5/S3/Quantum/QuantumChannels/OutputMaximalCoherenceTensorizationRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/QuantumChannels/OutputMaximalCoherenceTensorizationRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/QuantumChannels/OutputMaximalCoherenceTensorizationRefutation.claim; result=D5/S3/Quantum/QuantumChannels/OutputMaximalCoherenceTensorizationRefutation.result; claim=D5/S3/Quantum/QuantumChannels/OutputMaximalCoherenceTensorizationRefutation.claim
   digest: A Pauli channel and Bell input refute tensorization of output maximal coherence. -/

import D5.S3.Quantum.Foundation.FiniteKrausChannel
import D5.S3.Quantum.Matrix.CartesianVariance
import D5.S3.QuantumBounds.CHSHWitness

set_option linter.style.longLine false

noncomputable section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Kronecker
open D5.S3.Quantum.Foundation.FiniteStateChannel (DensityState)
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf (MatrixMap)
open D5.S3.Quantum.FiniteDimensional (qubitX qubitZ)
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
  letI := Fintype.ofFinite b
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

private def paulis : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![1, qubitX, Complex.I • (qubitX * qubitZ), qubitZ]

private def witness : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ :=
  fun r => (Real.sqrt (weights r) : ℂ) • paulis r

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
    norm_num [Fin.sum_univ_succ, weights.eq_1, paulis.eq_1, qubitX, qubitZ,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.conjTranspose_apply,
      Matrix.smul_apply, smul_eq_mul] <;> ring

end D5.S3.Quantum.QuantumChannels.OutputMaximalCoherenceTensorizationRefutation
