/- GID: D5/S3/QuantumChannels/QutritStochasticNonunitalRefutation
   generality: I
   mirror-B: D5/B/S3/QuantumChannels/QutritStochasticNonunitalRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/QuantumChannels/QutritStochasticNonunitalRefutation.claim; result=D5/S3/QuantumChannels/QutritStochasticNonunitalRefutation.result; claim=D5/S3/QuantumChannels/QutritStochasticNonunitalRefutation.claim
   digest: A stochastic qutrit channel is not unital. -/

/-
proof_shape: result: bind-only; escape_witness: none.
admission_basis: open-problem-resolution (#16492; Refuted)
Private theorems (all bind-only; escape_witness: none):
  weight_nonneg; consumers: kraus_term, phi_cptp.
  kraus_term; consumer: phi_eq_kraus.
  phi_eq_kraus; consumer: phi_cptp.
  phi_cptp; consumer: result.
  phi_choi_eigen; consumer: result.
  phi_one_entry; consumer: phi_not_unital.
  phi_not_unital; consumer: result.
Definitions: IsStochastic, claim, Phi, base, weight, K (proof_shape: not-applicable).
The public result is the designated refutation result (`basis=refutes`) and is exempt
from four-slot escape registration (CLAUDE.md §3.9).
The preregistered colOne and choiState expressions are inlined in IsStochastic;
the Choi entry formula is expanded, and proofs use the existing omega and choi
owners, with correspondence by unfolding.
FiniteKrausRepresentation is closed but unfrozen; its Choi construction is reached
through the frozen normalized-choi owner, and no representation theorem is used.
Direct frozen dependencies:
  D5/S3/Quantum/Foundation/FiniteKrausChannel.PhyslibLeaf.MatrixMap
    statement_id: sha256:df01dcc9d6d91985f3214eaee7e1c5eacebab3335dff64bb7b620043c650cad7
  D5/S3/Quantum/Foundation/FiniteKrausChannel.PhyslibLeaf.MatrixMap.IsCompletelyPositive
    statement_id: sha256:39e2682fd93035c705a08181bb7fdfb77067eba43afcc98c200c30543b913ed4
  D5/S3/Quantum/Foundation/FiniteKrausChannel.PhyslibLeaf.MatrixMap.of_kraus_isCompletelyPositive
    statement_id: sha256:522daaecff9970808def6ecdd938d4b89107d2820c79bafbf378ab083767f57f
  D5/S3/Quantum/Foundation/FiniteKrausChannel.PhyslibLeaf.MatrixMap.of_kraus._proof_1
    statement_id: sha256:5dc7bcde8ce2ae710c058683e5324d31e0ca70317f167566967eee1cf3b23bbb
  D5/S3/Quantum/Foundation/FiniteKrausChannel.PhyslibLeaf.MatrixMap.of_kraus._proof_2
    statement_id: sha256:9b70ce4858eb731b17facafe93b167007eb9ca6533c641dc770fc553d31ddaa1
  D5/S3/Quantum/Foundation/FiniteKrausChannel.PhyslibLeaf.MatrixMap.of_kraus
    statement_id: sha256:024ca3125b8f182e070b880d7c41840a31fa9cb0aaa89e5d81dbe4ebb3c5f287
  D5/S3/Quantum/QuantumChannels/ProductUnitaryChoiSpectrum.omega
    statement_id: sha256:0c834517c8e4db0abae6b88aa664babab6969b2c66667817cb32dc18ba6cdbf6
  D5/S3/QuantumChannels/CoPRelativeQuantumnessRefutation.IsCPTP
    statement_id: sha256:1440f7e681ed2017e7c90aedfe54aa0ad218d57311655f9d554863853dd8f53c
  D5/S3/QuantumChannels/PassiveMemoryNonclassicalRefutation.choi
    statement_id: sha256:1bbd0d1feb1ddefb8c13a5c075bab8ef5d8945262674ee8cec4f234008f01565
-/

import D5.S3.QuantumChannels.CoPRelativeQuantumnessRefutation
import D5.S3.Quantum.QuantumChannels.ProductUnitaryChoiSpectrum
import D5.S3.QuantumChannels.PassiveMemoryNonclassicalRefutation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
open scoped BigOperators Matrix
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
open D5.S3.QuantumChannels.CoPRelativeQuantumnessRefutation (IsCPTP)

noncomputable section
namespace D5.S3.QuantumChannels.QutritStochasticNonunitalRefutation

def IsStochastic {d : ℕ} (Phi : MatrixMap (Fin d) (Fin d) ℂ) : Prop :=
  IsCPTP Phi ∧ ∃ lam : ℝ, 0 < lam ∧ lam ≤ 1 ∧
    (((d : ℂ)⁻¹) •
      (fun p q : Fin d × Fin d => Phi (Matrix.single p.2 q.2 1) p.1 q.1)) *ᵥ
      (fun p : Fin d × Fin d => if p.1 = p.2 then 1 else 0) =
        (lam : ℂ) • (fun p : Fin d × Fin d => if p.1 = p.2 then 1 else 0)

def claim : Prop := ∀ Phi : MatrixMap (Fin 3) (Fin 3) ℂ,
  IsStochastic Phi → Phi 1 = 1

private def Phi : MatrixMap (Fin 3) (Fin 3) ℂ where
  toFun X := !![
    X 0 0 + (3/8 : ℂ) * (X 1 1 + X 2 2), (1/4 : ℂ) * X 0 1, (1/4 : ℂ) * X 0 2;
    (1/4 : ℂ) * X 1 0, (5/8 : ℂ) * X 1 1, (5/8 : ℂ) * X 1 2;
    (1/4 : ℂ) * X 2 0, (5/8 : ℂ) * X 2 1, (5/8 : ℂ) * X 2 2]
  map_add' X Y := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> ring
  map_smul' c X := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> ring

private def base : Fin 4 → Matrix (Fin 3) (Fin 3) ℂ := ![
  1,
  Matrix.diagonal ![(1 : ℂ), -(1/2 : ℂ), -(1/2 : ℂ)],
  Matrix.single 0 1 1,
  Matrix.single 0 2 1]

private def weight : Fin 4 → ℝ := ![1/2, 1/2, 3/8, 3/8]

private def K (r : Fin 4) : Matrix (Fin 3) (Fin 3) ℂ := Real.sqrt (weight r) • base r


private theorem weight_nonneg (r : Fin 4) : 0 ≤ weight r := by
  fin_cases r <;> norm_num [weight]

private theorem kraus_term (r : Fin 4) (X : Matrix (Fin 3) (Fin 3) ℂ) :
    K r * X * (K r).conjTranspose =
      weight r • (base r * X * (base r).conjTranspose) := by
  simp only [K, Matrix.conjTranspose_smul, star_trivial,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Real.mul_self_sqrt (weight_nonneg r)]

set_option maxHeartbeats 2000000 in
-- Nine entries each contain four three-dimensional matrix products.
private theorem phi_eq_kraus : Phi = MatrixMap.of_kraus K K := by
  ext X i j
  change _ = (∑ r : Fin 4, K r * X * (K r).conjTranspose) i j
  simp_rw [kraus_term]
  fin_cases i <;> fin_cases j <;>
    norm_num [Phi, base, Matrix.diagonal, weight, Fin.sum_univ_four, Matrix.mul_apply,
      Fin.sum_univ_three, Matrix.vecMul, dotProduct, Matrix.conjTranspose_apply,
      Matrix.single, Matrix.one_apply, map_ofNat,
      Matrix.cons_val_two, Matrix.cons_val_three, Fin.reduceFinMk] <;>
    simp +decide [map_ofNat] <;> norm_num <;> ring!

set_option maxHeartbeats 2000000 in
-- The completeness identity expands the four finite Kraus summands.
private theorem phi_cptp : IsCPTP Phi := by
  have gram_term (r : Fin 4) : (K r).conjTranspose * K r =
      weight r • ((base r).conjTranspose * base r) := by
    simp only [K, Matrix.conjTranspose_smul, star_trivial,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      Real.mul_self_sqrt (weight_nonneg r)]
  have gram : (∑ r : Fin 4, (K r).conjTranspose * K r) = 1 := by
    simp_rw [gram_term]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp +decide [base, Matrix.diagonal, weight, Fin.sum_univ_four, Matrix.mul_apply,
        Matrix.conjTranspose_apply,
        Matrix.single, map_ofNat, Matrix.cons_val_two,
        Matrix.cons_val_three, Fin.reduceFinMk] <;> norm_num
  constructor
  · rw [phi_eq_kraus]
    exact MatrixMap.of_kraus_isCompletelyPositive K
  · intro X
    rw [phi_eq_kraus]
    simp only [MatrixMap.of_kraus, LinearMap.sum_apply, LinearMap.coe_mk,
      AddHom.coe_mk, Matrix.trace_sum]
    conv =>
      enter [1,2,r]
      rw [Matrix.trace_mul_cycle (K r) X (K r).conjTranspose]
    rw [← Matrix.trace_sum, ← Finset.sum_mul, gram, one_mul]

private theorem phi_choi_eigen :
    D5.S3.QuantumChannels.PassiveMemoryNonclassicalRefutation.choi 3 Phi *ᵥ
      D5.S3.Quantum.QuantumChannels.ProductUnitaryChoiSpectrum.omega 3 =
        (1/2 : ℂ) • D5.S3.Quantum.QuantumChannels.ProductUnitaryChoiSpectrum.omega 3 := by
  ext p
  rcases p with ⟨i,j⟩
  fin_cases i <;> fin_cases j <;>
    simp +decide [D5.S3.QuantumChannels.PassiveMemoryNonclassicalRefutation.choi,
      D5.S3.Quantum.QuantumChannels.ProductUnitaryChoiSpectrum.omega, Matrix.mulVec, dotProduct,
      Fintype.sum_prod_type, Fin.sum_univ_three, MatrixMap.choi_matrix,
      Phi, Matrix.single, Matrix.cons_val_two, Fin.reduceFinMk]
    <;> norm_num

private theorem phi_one_entry : (Phi 1) 0 0 = (7/4 : ℂ) := by
  norm_num [Phi, Matrix.one_apply]

private theorem phi_not_unital : Phi 1 ≠ 1 := by
  intro h
  have h00 := congrArg (fun X : Matrix (Fin 3) (Fin 3) ℂ => X 0 0) h
  rw [phi_one_entry] at h00
  norm_num [Matrix.one_apply] at h00

/-- The qutrit case of the source's unitality question is false. -/
theorem result : ¬ claim := by
  intro h
  apply phi_not_unital
  apply h Phi
  refine ⟨phi_cptp, (1/2 : ℝ), by norm_num, by norm_num, ?_⟩
  change D5.S3.QuantumChannels.PassiveMemoryNonclassicalRefutation.choi 3 Phi *ᵥ
    D5.S3.Quantum.QuantumChannels.ProductUnitaryChoiSpectrum.omega 3 =
      (((1/2 : ℝ) : ℂ)) • D5.S3.Quantum.QuantumChannels.ProductUnitaryChoiSpectrum.omega 3
  norm_num only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  exact phi_choi_eigen

end D5.S3.QuantumChannels.QutritStochasticNonunitalRefutation
