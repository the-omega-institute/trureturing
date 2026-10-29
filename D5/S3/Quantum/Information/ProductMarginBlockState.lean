/- GID: D5/S3/Quantum/Information/ProductMarginBlockState
   generality: G
   mirror-B: D5/B/S3/Quantum/Information/ProductMarginBlockState
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual two-bit block density state and its exact product-margin partial traces. -/

import D5.S3.Quantum.Information.QubitNormalFormState
import Mathlib.Tactic

noncomputable section
namespace D5.S3.Quantum.Information.ProductMarginBlockState
open _root_.Matrix
open scoped MatrixOrder ComplexOrder Kronecker BigOperators
open D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
open D5.S3.Quantum.Information.PartialTraceMutualInformation
variable {n : Type*} [Fintype n] [DecidableEq n]

private def pointer (a : Fin 2) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal fun b => if b = a then 1 else 0

private lemma pointer_pos (a : Fin 2) : (pointer a).PosSemidef := by
  apply Matrix.PosSemidef.diagonal
  intro b
  dsimp
  split_ifs <;> simp

private lemma pointer_trace (a : Fin 2) : (pointer a).trace = 1 := by
  fin_cases a <;> norm_num [pointer, Matrix.trace, Fin.sum_univ_two]

/-- The subnormalized quantum block is never divided by its trace. -/
def gamma (P Q K : Matrix n n ℂ) (a b : Fin 2) : Matrix n n ℂ :=
  if a = b then
    if a = 0 then (1 / 2 : ℝ) • (P - K) else (1 / 2 : ℝ) • (Q - K)
  else (1 / 2 : ℝ) • K

/-- The register order is A × (B × n), matching the canonical four-party carrier. -/
def blockMatrix (P Q K : Matrix n n ℂ) :
    Matrix (Fin 2 × (Fin 2 × n)) (Fin 2 × (Fin 2 × n)) ℂ :=
  ∑ a : Fin 2, ∑ b : Fin 2, pointer a ⊗ₖ (pointer b ⊗ₖ gamma P Q K a b)

private lemma gamma_pos {P Q K : Matrix n n ℂ}
    (hK : K.PosSemidef) (hKP : K ≤ P) (hKQ : K ≤ Q) (a b : Fin 2) :
    (gamma P Q K a b).PosSemidef := by
  have hp := (Matrix.le_iff.mp hKP).smul (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hq := (Matrix.le_iff.mp hKQ).smul (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hk := hK.smul (by norm_num : (0 : ℝ) ≤ 1 / 2)
  fin_cases a <;> fin_cases b <;>
    first | simpa [gamma] using hp | simpa [gamma] using hq | simpa [gamma] using hk

private lemma block_pos {P Q K : Matrix n n ℂ}
    (hK : K.PosSemidef) (hKP : K ≤ P) (hKQ : K ≤ Q) :
    (blockMatrix P Q K).PosSemidef := by
  apply Matrix.posSemidef_sum
  intro a _
  apply Matrix.posSemidef_sum
  intro b _
  exact (pointer_pos a).kronecker ((pointer_pos b).kronecker (gamma_pos hK hKP hKQ a b))

private lemma block_trace {P Q K : Matrix n n ℂ} (htP : P.trace = 1) (htQ : Q.trace = 1) :
    (blockMatrix P Q K).trace = 1 := by
  simp only [blockMatrix, Matrix.trace_sum, Matrix.trace_kronecker, pointer_trace, one_mul]
  simp [Fin.sum_univ_two, gamma, Matrix.trace_smul, Matrix.trace_sub, htP, htQ]
  <;> ring

/-- An actual density state for every complex PSD common lower matrix, including zero blocks. -/
def blockState (P Q : DensityState n) (K : Matrix n n ℂ)
    (hK : K.PosSemidef) (hKP : K ≤ CStarMatrix.ofMatrix.symm P.1)
    (hKQ : K ≤ CStarMatrix.ofMatrix.symm Q.1) : DensityState (Fin 2 × (Fin 2 × n)) :=
  ⟨CStarMatrix.ofMatrix (blockMatrix (CStarMatrix.ofMatrix.symm P.1) (CStarMatrix.ofMatrix.symm Q.1) K),
    map_nonneg CStarMatrix.ofMatrixStarAlgEquiv (block_pos hK hKP hKQ).nonneg,
    block_trace P.2.2 Q.2.2⟩

/-- Reading either bit leaves the same two unnormalized quantum row sums, P/2 and Q/2.
Tracing both bits gives the exact quantum mixture (P+Q)/2. Tracing the quantum index gives the diagonal AB state with the actual block traces. -/
theorem block_partial_traces (P Q K : Matrix n n ℂ) :
    partialTraceLeft (blockMatrix P Q K) =
      (1 / 2 : ℝ) • (pointer 0 ⊗ₖ P + pointer 1 ⊗ₖ Q) ∧
    (fun a c => ∑ b : Fin 2, blockMatrix P Q K (a.1, (b, a.2)) (c.1, (b, c.2))) =
      (1 / 2 : ℝ) • (pointer 0 ⊗ₖ P + pointer 1 ⊗ₖ Q) ∧
    partialTraceLeft (partialTraceLeft (blockMatrix P Q K)) = (1 / 2 : ℝ) • (P + Q) ∧
    (fun a c : Fin 2 × Fin 2 => ∑ i : n,
      blockMatrix P Q K (a.1, (a.2, i)) (c.1, (c.2, i))) =
      Matrix.diagonal (fun a => (gamma P Q K a.1 a.2).trace) := by
  have hleft : partialTraceLeft (blockMatrix P Q K) =
      (1 / 2 : ℝ) • (pointer 0 ⊗ₖ P + pointer 1 ⊗ₖ Q) := by
    ext ⟨b,i⟩ ⟨c,j⟩
    fin_cases b <;> fin_cases c <;>
      simp [partialTraceLeft, blockMatrix, pointer, gamma, Fin.sum_univ_two,
        Matrix.kronecker_apply, Matrix.diagonal_apply, Matrix.smul_apply] <;> ring
  refine ⟨hleft, ?_, ?_, ?_⟩
  · ext ⟨a,i⟩ ⟨c,j⟩
    fin_cases a <;> fin_cases c <;>
      simp [blockMatrix, pointer, gamma, Fin.sum_univ_two,
        Matrix.kronecker_apply, Matrix.diagonal_apply, Matrix.smul_apply] <;> ring
  · rw [hleft]
    ext i j
    simp [partialTraceLeft, pointer, Fin.sum_univ_two, Matrix.kronecker_apply,
      Matrix.diagonal_apply, Matrix.smul_apply]
    <;> ring

  · ext ⟨a,b⟩ ⟨c,d⟩
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
      simp [blockMatrix, pointer, gamma, Fin.sum_univ_two, Matrix.kronecker_apply,
        Matrix.diagonal_apply, Matrix.smul_apply, Matrix.trace]

/-- The complete four-parameter physical family, with the prescribed two product margins.
Feasibility is imposed on the actual complex CD matrix. Nonnegative coordinate restrictions
can be imposed by the endpoint; state construction works on the whole signed closed disks. -/
def normalFormState (xC zC xD zD : ℝ)
    (hC : xC ^ 2 + zC ^ 2 ≤ 1) (hD : xD ^ 2 + zD ^ 2 ≤ 1)
    (K : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (hK : K.PosSemidef)
    (hKP : K ≤ QubitNormalFormState.qubitMatrix xC zC ⊗ₖ QubitNormalFormState.qubitMatrix xD zD)
    (hKQ : K ≤ QubitNormalFormState.qubitMatrix xC (-zC) ⊗ₖ QubitNormalFormState.qubitMatrix xD (-zD)) :
    DensityState (Fin 2 × (Fin 2 × (Fin 2 × Fin 2))) :=
  blockState
    (productState (QubitNormalFormState.qubitState xC zC hC) (QubitNormalFormState.qubitState xD zD hD))
    (productState (QubitNormalFormState.qubitState xC (-zC) (by nlinarith [hC]))
      (QubitNormalFormState.qubitState xD (-zD) (by nlinarith [hD]))) K hK hKP hKQ

#print axioms block_partial_traces
#print axioms normalFormState
end D5.S3.Quantum.Information.ProductMarginBlockState
