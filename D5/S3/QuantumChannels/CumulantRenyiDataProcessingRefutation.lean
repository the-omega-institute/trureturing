/- GID: D5/S3/QuantumChannels/CumulantRenyiDataProcessingRefutation
   generality: I
   mirror-B: D5/B/S3/QuantumChannels/CumulantRenyiDataProcessingRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/QuantumChannels/CumulantRenyiDataProcessingRefutation.claim; result=D5/S3/QuantumChannels/CumulantRenyiDataProcessingRefutation.result; claim=D5/S3/QuantumChannels/CumulantRenyiDataProcessingRefutation.claim
   digest: QDPI fails for the cumulant-based Renyi functional at every alpha > 1, by a dephased qubit pair. -/

/-
proof_shape: result: bind-only. Each private theorem is bind-only and is used on the proof
  path of result; no private theorem is unused.
escape_witness: none
admission_basis: open-problem-resolution (#13439; Refuted)
Direct frozen dependencies:
  D5/S3/QuantumChannels/CoPRelativeQuantumnessRefutation.IsDensity
    statement_id: sha256:4ba4e6b5fd69f7af3d48c8ecc93d1d3efe0fbd32799aa8b021b502f76ad76988
  D5/S3/QuantumChannels/CoPRelativeQuantumnessRefutation.IsCPTP
    statement_id: sha256:1440f7e681ed2017e7c90aedfe54aa0ad218d57311655f9d554863853dd8f53c
  D5/S3/QuantumChannels/CoPRelativeQuantumnessRefutation.pauli
    statement_id: sha256:c4f0d4e23308ae5d68c882cc28b36b011300866d6af6d76596159135b0da94a5
  D5/S3/Quantum/FiniteDimensional.qubitZ
    statement_id: sha256:381a2bec567456715f58fe6c0c413d59d37882b8499fc81a486c49e7c081d78c
  D5/S3/Quantum/FiniteDimensional.qubit_weyl_star
    statement_id: sha256:be07b0533dfdb8741136a43d8272fd7a664770fb9b4a851805c5db573532362d
  D5/S3/QuantumChannels/Pinching.pinching_apply
    statement_id: sha256:95dacc8bed01114b64a32196697cac3bc98aeae86868d263050138966e4d4308
  D5/S3/QuantumChannels/ProjectionDiagnostics/StaticDynamicScalarSeparation.pinchingEnd
    statement_id: sha256:d57ad3ae5e7865c4be9ea3ac1e896aa2508d79b1026756e5eb16045cdd9b8f8b
  D5/S3/Quantum/Dynamics/EntropyProductionCoherenceDeletionIdentity.cfc_log_diagonal
    statement_id: sha256:3a60f49e4c654be846afb7f639e5ad2ed4d5eb5fbd277586af42d3a0b6fd1809
  D5/S3/Quantum/Foundation/FiniteKrausChannel.PhyslibLeaf.MatrixMap
    statement_id: sha256:df01dcc9d6d91985f3214eaee7e1c5eacebab3335dff64bb7b620043c650cad7
  D5/S3/Quantum/Foundation/FiniteKrausChannel.PhyslibLeaf.MatrixMap.of_kraus
    statement_id: sha256:024ca3125b8f182e070b880d7c41840a31fa9cb0aaa89e5d81dbe4ebb3c5f287
  D5/S3/Quantum/Foundation/FiniteKrausChannel.PhyslibLeaf.MatrixMap.of_kraus_isCompletelyPositive
    statement_id: sha256:522daaecff9970808def6ecdd938d4b89107d2820c79bafbf378ab083767f57f
  Mathlib constants are pinned upstream dependencies, not frozen repository nodes.
-/

import D5.S3.QuantumChannels.CoPRelativeQuantumnessRefutation
import D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity
import D5.S3.QuantumChannels.ProjectionDiagnostics.StaticDynamicScalarSeparation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf

noncomputable section
namespace D5.S3.QuantumChannels.CumulantRenyiDataProcessingRefutation

private abbrev Mat (d : ℕ) := Matrix (Fin d) (Fin d) ℂ
open D5.S3.QuantumChannels.CoPRelativeQuantumnessRefutation (IsDensity IsCPTP pauli)
open D5.S3.Quantum.FiniteDimensional (qubitZ qubit_weyl_star)
open D5.S3.QuantumChannels.Pinching (pinching_apply)
open D5.S3.QuantumChannels.ProjectionDiagnostics.StaticDynamicScalarSeparation (pinchingEnd)

/-- The cumulant-based quantum relative Rényi functional of arXiv:2606.31205, Definition 3,
for faithful inputs. -/
def cuRenyi {d : ℕ} (α : ℝ) (A B : Mat d) : ℝ :=
  1 / (α - 1) * Real.log (Matrix.trace
    (A * NormedSpace.exp ((α - 1) • (CFC.log A - CFC.log B)))).re

/-- The quantum data-processing inequality at α, for faithful inputs with faithful outputs. -/
def QDPI (α : ℝ) : Prop :=
  ∀ (d : ℕ) (ρ σ : Mat d) (N : MatrixMap (Fin d) (Fin d) ℂ),
    IsDensity ρ → IsDensity σ → ρ.PosDef → σ.PosDef → IsCPTP N →
    (N ρ).PosDef → (N σ).PosDef → cuRenyi α (N ρ) (N σ) ≤ cuRenyi α ρ σ

def claim : Prop := ∃ α : ℝ, 1 < α ∧ QDPI α

private theorem involution_spectrum {n : Type} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) (hH : IsSelfAdjoint H) (hHH : H * H = 1)
    {x : ℝ} (hx : x ∈ spectrum ℝ H) : x = 1 ∨ x = -1 := by
  have hc : cfc (fun x : ℝ => x * x) H = cfc (fun _ : ℝ => 1) H := by
    rw [cfc_mul (fun x : ℝ => x) (fun x : ℝ => x) H, cfc_id' ℝ H hH,
      cfc_const 1 H hH, Algebra.algebraMap_eq_smul_one]
    simpa using hHH
  have hsq := eqOn_of_cfc_eq_cfc hc (ha := hH) (by fun_prop) (by fun_prop) hx
  dsimp at hsq
  rcases eq_or_eq_neg_of_sq_eq_sq x 1 (by nlinarith) with h | h
  · exact Or.inl h
  · exact Or.inr h

theorem two_point_cfc {n : Type} [Fintype n] [DecidableEq n]
    (f : ℝ → ℝ) (a b : ℝ) (H : Matrix n n ℂ)
    (hH : IsSelfAdjoint H) (hHH : H * H = 1) :
    cfc f (a • (1 : Matrix n n ℂ) + b • H) =
      ((f (a+b) + f (a-b))/2) • (1 : Matrix n n ℂ) +
      ((f (a+b) - f (a-b))/2) • H := by
  have haff : cfc (fun x : ℝ => a + b*x) H = a • (1 : Matrix n n ℂ) + b • H := by
    rw [cfc_const_add a (fun x : ℝ => b*x) H (by fun_prop) hH,
      cfc_const_mul_id b H hH, Algebra.algebraMap_eq_smul_one]
  rw [← haff, ← cfc_comp f (fun x : ℝ => a+b*x) H hH
    ((H.finite_real_spectrum.image _).continuousOn _) (by fun_prop)]
  calc
    cfc (fun x : ℝ => f (a+b*x)) H =
      cfc (fun x : ℝ => (f (a+b)+f (a-b))/2 + ((f (a+b)-f (a-b))/2)*x) H := by
      apply cfc_congr
      intro x hx
      rcases involution_spectrum H hH hHH hx with rfl | rfl <;> dsimp <;>
        simp only [mul_one, mul_neg_one, ← sub_eq_add_neg] <;> ring
    _ = _ := by
      rw [cfc_const_add _ (fun x : ℝ => ((f (a+b)-f (a-b))/2)*x) H (by fun_prop) hH,
        cfc_const_mul_id _ H hH, Algebra.algebraMap_eq_smul_one]

private theorem affine_posDef {n : Type} [Fintype n] [DecidableEq n]
    (a b : ℝ) (H : Matrix n n ℂ) (hH : IsSelfAdjoint H) (hHH : H * H = 1)
    (hp : 0 < a + b) (hm : 0 < a - b) :
    (a • (1 : Matrix n n ℂ) + b • H).PosDef := by
  have haff : cfc (fun x : ℝ => a+b*x) H = a • (1 : Matrix n n ℂ) + b • H := by
    rw [cfc_const_add a (fun x : ℝ => b*x) H (by fun_prop) hH,
      cfc_const_mul_id b H hH, Algebra.algebraMap_eq_smul_one]
  rw [← haff]
  apply Matrix.isStrictlyPositive_iff_posDef.mp
  apply (cfc_isStrictlyPositive_iff _ _ (by fun_prop) hH).mpr
  intro x hx
  rcases involution_spectrum H hH hHH hx with rfl | rfl
  · simpa using hp
  · simpa [sub_eq_add_neg] using hm

private def N : Mat 2 := pauli (1/2) (Real.sqrt 3/2)
private def B : Mat 2 := pauli (-1/2) (Real.sqrt 3/2)
private def r (x : ℝ) : ℝ := (x-1)/(x+1)
private def state (x : ℝ) (H : Mat 2) : Mat 2 := (1/2 : ℝ) • 1 + (r x/2) • H
theorem dephase_apply (A : Mat 2) :
    pinchingEnd A = Matrix.diagonal ![A 0 0, A 1 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pinchingEnd, pinching_apply, Matrix.diagonal]

theorem pinching_kraus :
    (pinchingEnd : MatrixMap (Fin 2) (Fin 2) ℂ) =
      MatrixMap.of_kraus (fun k : Fin 2 => Matrix.single k k (1 : ℂ))
        (fun k : Fin 2 => Matrix.single k k (1 : ℂ)) := by
  apply LinearMap.ext
  intro A
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pinchingEnd, pinching_apply, MatrixMap.of_kraus, Fin.sum_univ_two]

private theorem dephase_cptp : IsCPTP (pinchingEnd : MatrixMap (Fin 2) (Fin 2) ℂ) := by
  refine ⟨?_, ?_⟩
  · rw [pinching_kraus]
    exact MatrixMap.of_kraus_isCompletelyPositive _
  · intro A
    rw [dephase_apply]
    simp [Matrix.trace, Fin.sum_univ_two]

private theorem pauli_sa (z v : ℝ) : IsSelfAdjoint (pauli z v) := by
  change Matrix.conjTranspose (pauli z v) = pauli z v
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauli, Matrix.conjTranspose_apply]

private theorem pauli_sq (z v : ℝ) (h : z ^ 2 + v ^ 2 = 1) :
    pauli z v * pauli z v = 1 := by
  have hc : (z : ℂ)^2+(v : ℂ)^2=1 := by exact_mod_cast h
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauli, Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination hc
  · ring
  · ring
  · linear_combination hc

private theorem involutions : N*N=1 ∧ qubitZ*qubitZ=1 ∧ B*B=1 ∧ N-qubitZ=B := by
  refine ⟨pauli_sq _ _ ?_, by simpa [pow_two] using qubit_weyl_star.2.2.2.2, pauli_sq _ _ ?_, ?_⟩
  · nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)]
  · nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [N,qubitZ,B,pauli] <;> norm_num

private theorem state_trace (x : ℝ) (z v : ℝ) :
    Matrix.trace (state x (pauli z v)) = 1 := by
  simp [state, pauli, Matrix.trace, Fin.sum_univ_two]
  ring

private def pPlus (x : ℝ) : ℝ := (3*x+1)/(4*(x+1))
private def pMinus (x : ℝ) : ℝ := (x+3)/(4*(x+1))
private def qPlus (x : ℝ) : ℝ := x/(x+1)
private def qMinus (x : ℝ) : ℝ := 1/(x+1)

private theorem output_states (x : ℝ) (hx : 1 < x) :
    pinchingEnd (state x N) = Matrix.diagonal ![(pPlus x : ℂ), (pMinus x : ℂ)] ∧
    pinchingEnd (state x qubitZ) = Matrix.diagonal ![(qPlus x : ℂ), (qMinus x : ℂ)] := by
  have hd : x+1 ≠ 0 := by linarith
  constructor <;> rw [dephase_apply] <;> congr 1 <;> ext i <;> fin_cases i <;>
    simp [state, N, qubitZ, pauli, r, pPlus, pMinus, qPlus, qMinus,
      Complex.real_smul] <;>
    field_simp <;> ring

private theorem state_posDef (x : ℝ) (hx : 1 < x) (K : Mat 2)
    (hK : IsSelfAdjoint K) (hKK : K * K = 1) : (state x K).PosDef := by
  have hd : x+1 ≠ 0 := by linarith
  change ((1/2 : ℝ) • (1 : Mat 2) + ((x-1)/(x+1)/2) • K).PosDef
  apply affine_posDef (1/2) ((x-1)/(x+1)/2) K hK hKK
  · have ep : (1/2:ℝ)+(x-1)/(x+1)/2 = x/(x+1) := by field_simp [hd]; ring
    rw [ep]
    exact div_pos (by linarith) (by linarith)
  · have em : (1/2:ℝ)-(x-1)/(x+1)/2 = 1/(x+1) := by field_simp [hd]; ring
    rw [em]
    exact div_pos zero_lt_one (by linarith)

private theorem log_state (x : ℝ) (hx : 1 < x) (K : Mat 2)
    (hK : IsSelfAdjoint K) (hKK : K * K = 1) :
    CFC.log (state x K) =
      (Real.log x/2 - Real.log (x+1)) • (1 : Mat 2) +
      (Real.log x/2) • K := by
  have hx0 : x ≠ 0 := ne_of_gt (lt_trans zero_lt_one hx)
  have hd : x+1 ≠ 0 := by linarith
  have ep : (1/2:ℝ)+(x-1)/(x+1)/2 = x/(x+1) := by field_simp [hd]; ring
  have em : (1/2:ℝ)-(x-1)/(x+1)/2 = 1/(x+1) := by field_simp [hd]; ring
  have lp : Real.log ((1/2:ℝ)+(x-1)/(x+1)/2) = Real.log x - Real.log (x+1) := by
    rw [ep, Real.log_div hx0 hd]
  have lm : Real.log ((1/2:ℝ)-(x-1)/(x+1)/2) = -Real.log (x+1) := by
    rw [em, Real.log_div (by norm_num) hd, Real.log_one, zero_sub]
  change cfc Real.log (state x K) = _
  rw [state, r, two_point_cfc Real.log (1/2) ((x-1)/(x+1)/2) K hK hKK, lp, lm]
  congr 1 <;> congr 1 <;> ring

private theorem exp_affine (a b : ℝ) (M : Mat 2) (hM : IsSelfAdjoint M)
    (hMM : M * M = 1) :
    NormedSpace.exp (a • (1 : Mat 2)+b • M) =
      ((Real.exp (a+b)+Real.exp (a-b))/2) • (1:Mat 2) +
      ((Real.exp (a+b)-Real.exp (a-b))/2) • M := by
  have hsa : IsSelfAdjoint (a • (1 : Mat 2)+b • M) :=
    ((isSelfAdjoint_iff.mpr (by simp) : IsSelfAdjoint a).smul (IsSelfAdjoint.one (Mat 2))).add
      ((isSelfAdjoint_iff.mpr (by simp) : IsSelfAdjoint b).smul hM)
  rw [← CFC.real_exp_eq_normedSpace_exp hsa]
  exact two_point_cfc Real.exp a b M hM hMM

private theorem scalar_gap_general (t x : ℝ) (ht : 0 < t) (hx : 1 < x)
    (hbalance : t * Real.log x = 2 * (t + 1) * Real.log 4) :
    let r := (x - 1) / (x + 1)
    let u := t * Real.log x / 2
    let pPlus := (3 * x + 1) / (4 * (x + 1))
    let pMinus := (x + 3) / (4 * (x + 1))
    let qPlus := x / (x + 1)
    let qMinus := 1 / (x + 1)
    let F := (Real.exp u + Real.exp (-u)) / 2 +
      r / 2 * ((Real.exp u - Real.exp (-u)) / 2)
    let G := pPlus * Real.exp (t * (Real.log pPlus - Real.log qPlus)) +
      pMinus * Real.exp (t * (Real.log pMinus - Real.log qMinus))
    0 < F ∧ F < G := by
  dsimp only
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  have hx1 : 0 < x + 1 := by linarith
  have hd : 0 < 4 * (x + 1) := by positivity
  have hr0 : 0 < (x - 1) / (x + 1) := by positivity
  have hr1 : (x - 1) / (x + 1) < 1 := by
    apply (div_lt_one hx1).2
    linarith
  have hu : 0 < t * Real.log x / 2 := by
    exact div_pos (mul_pos ht (Real.log_pos hx)) (by norm_num)
  have he : Real.exp (-(t * Real.log x / 2)) < Real.exp (t * Real.log x / 2) := by
    apply Real.exp_lt_exp.2
    linarith
  have hF0 : 0 < (Real.exp (t * Real.log x / 2) +
      Real.exp (-(t * Real.log x / 2))) / 2 +
      (x - 1) / (x + 1) / 2 *
        ((Real.exp (t * Real.log x / 2) - Real.exp (-(t * Real.log x / 2))) / 2) := by
    have hA := Real.exp_pos (t * Real.log x / 2)
    have hB := Real.exp_pos (-(t * Real.log x / 2))
    have hC : 0 < (x - 1) / (x + 1) / 2 *
      ((Real.exp (t * Real.log x / 2) - Real.exp (-(t * Real.log x / 2))) / 2) := by
      exact mul_pos (div_pos hr0 (by norm_num))
        (div_pos (sub_pos.2 he) (by norm_num))
    linarith
  have hF : (Real.exp (t * Real.log x / 2) +
      Real.exp (-(t * Real.log x / 2))) / 2 +
      (x - 1) / (x + 1) / 2 *
        ((Real.exp (t * Real.log x / 2) - Real.exp (-(t * Real.log x / 2))) / 2) <
      Real.exp (t * Real.log x / 2) := by
    have hC := mul_lt_mul_of_pos_right (show (x - 1) / (x + 1) / 2 < 1 by linarith)
      (show 0 < (Real.exp (t * Real.log x / 2) -
        Real.exp (-(t * Real.log x / 2))) / 2 by linarith)
    linarith
  have hpPlus : 0 < (3 * x + 1) / (4 * (x + 1)) := by positivity
  have hpMinus : 0 < (x + 3) / (4 * (x + 1)) := by positivity
  have hqMinus : 0 < 1 / (x + 1) := by positivity
  have hpQuarter : (1 : ℝ) / 4 < (x + 3) / (4 * (x + 1)) := by
    apply (lt_div_iff₀ hd).2
    nlinarith
  have hratio : ((x + 3) / (4 * (x + 1))) / (1 / (x + 1)) = (x + 3) / 4 := by
    field_simp
  have hlogs : Real.log ((x + 3) / (4 * (x + 1))) - Real.log (1 / (x + 1)) >
      Real.log x - Real.log 4 := by
    rw [← Real.log_div (ne_of_gt hpMinus) (ne_of_gt hqMinus), hratio,
      ← Real.log_div (ne_of_gt hx0) (by norm_num : (4 : ℝ) ≠ 0)]
    exact Real.log_lt_log (by positivity) (by linarith)
  have hexps : Real.exp (t * (Real.log x - Real.log 4)) <
      Real.exp (t * (Real.log ((x + 3) / (4 * (x + 1))) - Real.log (1 / (x + 1)))) :=
    Real.exp_lt_exp.2 (mul_lt_mul_of_pos_left hlogs ht)
  have hthreshold : (1 : ℝ) / 4 * Real.exp (t * (Real.log x - Real.log 4)) =
      Real.exp (t * Real.log x / 2) := by
    have hquarter : (1 : ℝ) / 4 = Real.exp (-Real.log 4) := by
      rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 4)]
      norm_num
    rw [hquarter, ← Real.exp_add]
    congr 1
    nlinarith [hbalance]
  have hG : Real.exp (t * Real.log x / 2) <
      (3 * x + 1) / (4 * (x + 1)) *
        Real.exp (t * (Real.log ((3 * x + 1) / (4 * (x + 1))) - Real.log (x / (x + 1)))) +
      (x + 3) / (4 * (x + 1)) *
        Real.exp (t * (Real.log ((x + 3) / (4 * (x + 1))) - Real.log (1 / (x + 1)))) := by
    have hprod : (1 : ℝ) / 4 * Real.exp (t * (Real.log x - Real.log 4)) <
        (x + 3) / (4 * (x + 1)) *
          Real.exp (t * (Real.log ((x + 3) / (4 * (x + 1))) - Real.log (1 / (x + 1)))) := by
      exact (mul_lt_mul_of_pos_right hpQuarter (Real.exp_pos _)).trans
        (mul_lt_mul_of_pos_left hexps hpMinus)
    rw [hthreshold] at hprod
    have hfirst : 0 < (3 * x + 1) / (4 * (x + 1)) *
      Real.exp (t * (Real.log ((3 * x + 1) / (4 * (x + 1))) - Real.log (x / (x + 1)))) := by
      exact mul_pos hpPlus (Real.exp_pos _)
    linarith
  exact ⟨hF0, hF.trans hG⟩

private theorem scalar_family_gap (t : ℝ) (ht : 0 < t) :
    let x := (16 : ℝ) ^ (1 + 1 / t)
    let r := (x - 1) / (x + 1)
    let u := t * Real.log x / 2
    let pPlus := (3 * x + 1) / (4 * (x + 1))
    let pMinus := (x + 3) / (4 * (x + 1))
    let qPlus := x / (x + 1)
    let qMinus := 1 / (x + 1)
    let F := (Real.exp u + Real.exp (-u)) / 2 +
      r / 2 * ((Real.exp u - Real.exp (-u)) / 2)
    let G := pPlus * Real.exp (t * (Real.log pPlus - Real.log qPlus)) +
      pMinus * Real.exp (t * (Real.log pMinus - Real.log qMinus))
    0 < F ∧ F < G := by
  apply scalar_gap_general t ((16 : ℝ) ^ (1 + 1 / t)) ht
  · exact Real.one_lt_rpow (by norm_num) (by positivity)
  · rw [Real.log_rpow (by norm_num : (0 : ℝ) < 16)]
    have hlog : Real.log (16 : ℝ) = 2 * Real.log 4 := by
      rw [show (16 : ℝ) = 4 ^ (2 : ℕ) by norm_num, Real.log_pow]
      norm_num
    rw [hlog]
    field_simp

private theorem log_diagonal (p q : ℝ) :
    CFC.log (Matrix.diagonal ![(p : ℂ), (q : ℂ)] : Mat 2) =
      Matrix.diagonal ![(Real.log p : ℂ), (Real.log q : ℂ)] := by
  have e₁ : (Matrix.diagonal ![(p : ℂ), (q : ℂ)] : Mat 2) =
      Matrix.diagonal fun i => ((![p, q] i : ℝ) : ℂ) := by
    congr 1; ext i; fin_cases i <;> rfl
  have e₂ : (Matrix.diagonal ![(Real.log p : ℂ), (Real.log q : ℂ)] : Mat 2) =
      Matrix.diagonal fun i => (Real.log (![p, q] i) : ℂ) := by
    congr 1; ext i; fin_cases i <;> rfl
  rw [e₁, e₂]
  exact D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity.cfc_log_diagonal _

private theorem exp_log_diagonal (t p₀ p₁ q₀ q₁ : ℝ) :
    NormedSpace.exp (t •
      (CFC.log (Matrix.diagonal ![(p₀:ℂ), (p₁:ℂ)] : Mat 2) -
      CFC.log (Matrix.diagonal ![(q₀:ℂ), (q₁:ℂ)] : Mat 2))) =
      Matrix.diagonal ![(Real.exp (t*(Real.log p₀-Real.log q₀)) : ℂ),
        (Real.exp (t*(Real.log p₁-Real.log q₁)) : ℂ)] := by
  rw [log_diagonal, log_diagonal]
  have hdiag : t •
      ((Matrix.diagonal ![(Real.log p₀:ℂ), (Real.log p₁:ℂ)] : Mat 2) -
      Matrix.diagonal ![(Real.log q₀:ℂ), (Real.log q₁:ℂ)]) =
      Matrix.diagonal ![((t*(Real.log p₀-Real.log q₀)):ℂ),
        ((t*(Real.log p₁-Real.log q₁)):ℂ)] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]
  rw [hdiag, Matrix.exp_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.diagonal, Pi.coe_exp, ← Complex.exp_eq_exp_ℂ]

private theorem trace_input (t x : ℝ) (hx : 1 < x) :
    (Matrix.trace (state x N *
      NormedSpace.exp (t • (CFC.log (state x N) - CFC.log (state x qubitZ))))).re =
    (Real.exp (t * Real.log x / 2) + Real.exp (-(t * Real.log x / 2))) / 2 +
      r x / 2 * ((Real.exp (t * Real.log x / 2) -
        Real.exp (-(t * Real.log x / 2))) / 2) := by
  have he : t • (CFC.log (state x N) - CFC.log (state x qubitZ)) =
      (0 : ℝ) • (1 : Mat 2) + (t * Real.log x / 2) • B := by
    rw [log_state x hx N (pauli_sa _ _) involutions.1,
      log_state x hx qubitZ qubit_weyl_star.2.2.1 involutions.2.1]
    rw [← involutions.2.2.2]
    module
  rw [he, exp_affine _ _ B (pauli_sa _ _) involutions.2.2.1]
  simp only [zero_add, zero_sub]
  simp [-Complex.ofReal_exp, state, N, B, pauli, Matrix.trace, Matrix.mul_apply,
    Fin.sum_univ_two, Complex.real_smul]
  ring_nf
  simp [Real.sq_sqrt]
  ring

private theorem output_posDef (x : ℝ) (hx : 1 < x) :
    (pinchingEnd (state x N)).PosDef ∧ (pinchingEnd (state x qubitZ)).PosDef := by
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  rw [(output_states x hx).1, (output_states x hx).2]
  constructor <;> apply Matrix.PosDef.diagonal <;> intro i <;> fin_cases i <;>
    dsimp only <;>
    apply Complex.zero_lt_real.mpr <;>
    dsimp [pPlus, pMinus, qPlus, qMinus] <;> positivity

private theorem trace_output (t x : ℝ) (hx : 1 < x) :
    (Matrix.trace (pinchingEnd (state x N) * NormedSpace.exp
      (t • (CFC.log (pinchingEnd (state x N)) - CFC.log (pinchingEnd (state x qubitZ)))))).re =
    pPlus x * Real.exp (t * (Real.log (pPlus x) - Real.log (qPlus x))) +
      pMinus x * Real.exp (t * (Real.log (pMinus x) - Real.log (qMinus x))) := by
  rw [(output_states x hx).1, (output_states x hx).2, exp_log_diagonal]
  simp [-Complex.ofReal_exp, Matrix.trace, Fin.sum_univ_two]

/-- No order greater than one satisfies quantum data processing for this functional. -/
theorem result : ¬ claim := by
  rintro ⟨α, hα, hQDPI⟩
  let t : ℝ := α - 1
  have ht : 0 < t := sub_pos.mpr hα
  let x : ℝ := (16 : ℝ) ^ (1 + 1 / t)
  have hx : 1 < x := Real.one_lt_rpow (by norm_num) (by positivity)
  have hρ := state_posDef x hx N (pauli_sa _ _) involutions.1
  have hσ := state_posDef x hx qubitZ qubit_weyl_star.2.2.1 involutions.2.1
  have hbound := hQDPI 2 (state x N) (state x qubitZ) pinchingEnd
    ⟨hρ.posSemidef, state_trace x _ _⟩
    ⟨hσ.posSemidef, by simp [state, qubitZ, Matrix.trace, Fin.sum_univ_two]; ring⟩
    hρ hσ dephase_cptp (output_posDef x hx).1 (output_posDef x hx).2
  have hgap := scalar_family_gap t ht
  change 0 < _ ∧ _ < _ at hgap
  have hlog := Real.log_lt_log hgap.1 hgap.2
  have hstrict := mul_lt_mul_of_pos_left hlog (one_div_pos.mpr ht)
  unfold cuRenyi at hbound
  rw [trace_input t x hx, trace_output t x hx] at hbound
  exact (not_lt_of_ge hbound) hstrict

#print axioms result

end D5.S3.QuantumChannels.CumulantRenyiDataProcessingRefutation
