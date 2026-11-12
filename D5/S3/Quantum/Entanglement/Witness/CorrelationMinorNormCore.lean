/- GID: D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormCore
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/Witness/CorrelationMinorNormCore
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Shared actual correlation-minor definitions and single-row norm geometry. -/

import D5.S3.Quantum.QuantumChannels.IptPptSquaredEquivalence
import D5.S3.Quantum.Information.PartialTraceMutualInformation
import D5.S3.Quantum.Schatten.Partition
import D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity
import D5.S3.Quantum.Information.Pauli.PauliMatrix

/-! Source factoring of the original actual correlation, increasing compound and
norm definitions. Existing declaration names and objects are preserved. The
single-row proofs are moved unchanged; no parallel state or norm stack is added.
The fixed rational counterexample imports this core, while general consumers do
not import that counterexample. -/

set_option autoImplicit false
set_option linter.style.longLine false
noncomputable section
open Matrix
open scoped BigOperators ComplexOrder Kronecker MatrixOrder Matrix.Norms.L2Operator
open D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence (pauliMatrix)
namespace D5.S3.Quantum.Entanglement.Witness.CorrelationMinorNormFNFRefutation

/-- A complete Hilbert–Schmidt orthonormal family of Hermitian matrices. -/
def IsHermBasis {n m : ℕ} (a : Fin m → Matrix (Fin n) (Fin n) ℂ) : Prop :=
  (∀ i, (a i).IsHermitian) ∧ m = n ^ 2 ∧
    ∀ i j, (a i * a j).trace = if i = j then 1 else 0

/-- Real correlation coefficients in local Hermitian bases. -/
def corr {da db ma mb : ℕ}
    (ρ : Matrix (Fin da × Fin db) (Fin da × Fin db) ℂ)
    (a : Fin ma → Matrix (Fin da) (Fin da) ℂ)
    (b : Fin mb → Matrix (Fin db) (Fin db) ℂ) : Matrix (Fin ma) (Fin mb) ℝ :=
  fun i j => (ρ * (a i ⊗ₖ b j)).trace.re

/-- The compound matrix, with each minor in increasing row and column order. -/
def compound {m n : ℕ} (h : ℕ) (c : Matrix (Fin m) (Fin n) ℝ) :
    Matrix {r : Finset (Fin m) // r.card = h} {s : Finset (Fin n) // s.card = h} ℝ :=
  fun r s => (c.submatrix (r.val.orderEmbOfFin r.property)
    (s.val.orderEmbOfFin s.property)).det

/-- The Schatten infinity norm of the compound matrix. -/
def cmnInf {m n : ℕ} (h : ℕ) (c : Matrix (Fin m) (Fin n) ℝ) : ℝ := by
  classical
  exact ‖compound h c‖

/-- The finite-p norm uses the existing actual rectangular complex Schatten functional.
The increasing real compound is complexified entrywise; infinity remains `cmnInf`. -/
def cmnP {m n : ℕ} (p : ℝ) (h : ℕ) (c : Matrix (Fin m) (Fin n) ℝ) : ℝ := by
  classical
  exact D5.S3.Quantum.Schatten.Partition.rectangularNorm
    ((compound h c).map Complex.ofReal) p

/-- The right hand side of Theorem 3, with real exponent `(h-1)/2`. -/
def bound (da db h : ℕ) : ℝ :=
  1 / Real.sqrt ((max da db : ℝ) * (min da db : ℝ)) *
    (((max da db : ℝ) - 1) / ((max da db : ℝ) * ((h : ℝ) - 1)) *
      (((min da db : ℝ) - 1) / ((min da db : ℝ) * ((h : ℝ) - 1)))) ^
      (((h : ℝ) - 1) / 2)

def alice : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ :=
  fun i => ((Real.sqrt 2 : ℂ)⁻¹) •
    (![pauliMatrix .I, pauliMatrix .Z, pauliMatrix .X, pauliMatrix .Y] i)

/-- The original normalized IZX Y family, verified directly from the shared Pauli carrier. -/
lemma alice_basis : IsHermBasis alice := by
  refine ⟨?_, by decide, ?_⟩
  · intro i
    change (alice i)ᴴ = alice i
    ext j k
    fin_cases i <;> fin_cases j <;> fin_cases k <;>
      simp [alice, pauliMatrix, D5.S3.Quantum.FiniteDimensional.qubitX,
        D5.S3.Quantum.FiniteDimensional.qubitZ, Matrix.conjTranspose_apply,
        Matrix.mul_apply, Fin.sum_univ_two]
  · intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [alice, pauliMatrix, D5.S3.Quantum.FiniteDimensional.qubitX,
        D5.S3.Quantum.FiniteDimensional.qubitZ, Matrix.trace,
        Matrix.mul_apply, Fin.sum_univ_two,
        ← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] <;>
      ring_nf <;>
      norm_num [inv_pow, ← Complex.ofReal_pow,
        Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

private lemma single_row_gram {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (r : m) (v : n → ℝ) :
    (Matrix.vecMulVec (Pi.single r (1 : ℝ)) v) *
      (Matrix.vecMulVec (Pi.single r (1 : ℝ)) v)ᴴ =
      Matrix.diagonal (Pi.single r (∑ j, v j ^ 2) : m → ℝ) := by
  ext i k
  by_cases hi : i = r <;> by_cases hk : k = r <;>
    simp_all [Matrix.mul_apply, Matrix.vecMulVec, Matrix.conjTranspose_apply,
      Pi.single_apply, Matrix.diagonal_apply, pow_two]
  all_goals aesop

lemma single_row_opnorm {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (r : m) (v : n → ℝ) :
    ‖Matrix.vecMulVec (Pi.single r (1 : ℝ)) v‖ = Real.sqrt (∑ j, v j ^ 2) := by
  have h := Matrix.l2_opNorm_conjTranspose_mul_self
    (Matrix.vecMulVec (Pi.single r (1 : ℝ)) v)ᴴ
  rw [Matrix.conjTranspose_conjTranspose, single_row_gram,
    Matrix.l2_opNorm_diagonal, Pi.norm_single, Matrix.l2_opNorm_conjTranspose,
    Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _))] at h
  apply (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _)), pow_two]
  exact h.symm

private lemma single_row_complex_gram {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (r : m) (v : n → ℝ) :
    ((Matrix.vecMulVec (Pi.single r (1 : ℝ)) v).map Complex.ofReal) *
      ((Matrix.vecMulVec (Pi.single r (1 : ℝ)) v).map Complex.ofReal)ᴴ =
      Matrix.diagonal (fun i => (((Pi.single r (∑ j, v j ^ 2) : m → ℝ) i) : ℂ)) := by
  ext i k
  by_cases hi : i = r <;> by_cases hk : k = r <;>
    simp_all [Matrix.mul_apply, Matrix.vecMulVec, Matrix.conjTranspose_apply,
      Pi.single_apply, Matrix.diagonal_apply, pow_two, ← map_sum]
  all_goals aesop

lemma single_row_schatten {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (r : m) (v : n → ℝ) (p : ℝ) (hp : 0 < p) :
    D5.S3.Quantum.Schatten.Partition.rectangularNorm
      ((Matrix.vecMulVec (Pi.single r (1 : ℝ)) v).map Complex.ofReal) p =
        Real.sqrt (∑ j, v j ^ 2) := by
  classical
  let E : ℝ := ∑ j, v j ^ 2
  have hE : 0 ≤ E := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hdiag : (Matrix.diagonal (fun i => (((Pi.single r E : m → ℝ) i) : ℂ))).PosSemidef :=
    Matrix.PosSemidef.diagonal (by
      intro i
      change (0 : ℂ) ≤ (((Pi.single r E : m → ℝ) i) : ℂ)
      apply Complex.zero_le_real.mpr
      by_cases hi : i = r <;> simp [Pi.single_apply, hi, hE])
  apply (Real.rpow_left_inj
    (schattenNorm_nonneg _ _) (Real.sqrt_nonneg _) hp.ne').mp
  change D5.S3.Quantum.Schatten.Partition.rectangularNorm
    ((Matrix.vecMulVec (Pi.single r (1 : ℝ)) v).map Complex.ofReal) p ^ p = _
  rw [D5.S3.Quantum.Schatten.Partition.rectangularNorm_rpow _ hp,
    single_row_complex_gram]
  unfold D5.S3.Quantum.Hiai.InverseMeanVariational.tracePower
  rw [CFC.rpow_eq_cfc_real hdiag.nonneg,
    D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity.cfc_diagonal,
    Matrix.trace_diagonal]
  try simp only [← Complex.ofReal_sum, Complex.ofReal_re]
  have hz : (0 : ℝ) ^ (p / 2) = 0 := Real.zero_rpow (by linarith)
  have he : (∑ i : m, (Pi.single r E : m → ℝ) i ^ (p / 2)) = E ^ (p / 2) := by
    simp [Pi.single_apply, hz]
  rw [he, Real.sqrt_eq_rpow, ← Real.rpow_mul hE]
  congr 1
  ring

end D5.S3.Quantum.Entanglement.Witness.CorrelationMinorNormFNFRefutation
