/- GID: D5/S3/QuantumChannels/UnitalBlockOverlapRefutation
   generality: I
   mirror-B: D5/B/S3/QuantumChannels/UnitalBlockOverlapRefutation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/QuantumChannels/UnitalBlockOverlapRefutation.claim; result=D5/S3/QuantumChannels/UnitalBlockOverlapRefutation.result; claim=D5/S3/QuantumChannels/UnitalBlockOverlapRefutation.claim
   digest: Two qutrit Kraus channels have unital-block overlap -4/3. -/

/-
proof_shape: result: bind-only; all private theorem helpers are bind-only with consumers
  recorded at their declarations. The finite matrix calculations, square-root identities,
  complete positivity and contradiction use frozen owners and pinned Mathlib normalization.
escape_witness: none
admission_basis: open-problem-resolution (#16416; Refuted)
Direct frozen dependencies:
  D5/S3/Quantum/Foundation/FiniteKrausChannel.PhyslibLeaf.MatrixMap
    statement_id: sha256:df01dcc9d6d91985f3214eaee7e1c5eacebab3335dff64bb7b620043c650cad7
  D5/S3/Quantum/Foundation/FiniteKrausChannel.PhyslibLeaf.MatrixMap.IsCompletelyPositive
    statement_id: sha256:39e2682fd93035c705a08181bb7fdfb77067eba43afcc98c200c30543b913ed4
  D5/S3/Quantum/Foundation/FiniteKrausChannel.PhyslibLeaf.MatrixMap.of_kraus_isCompletelyPositive
    statement_id: sha256:522daaecff9970808def6ecdd938d4b89107d2820c79bafbf378ab083767f57f
  D5/S3/Quantum/Foundation/FiniteKrausChannel.PhyslibLeaf.MatrixMap.of_kraus
    statement_id: sha256:024ca3125b8f182e070b880d7c41840a31fa9cb0aaa89e5d81dbe4ebb3c5f287
  D5/S3/Quantum/Foundation/FiniteKrausChannel.finite_kraus_quantum_channel
    statement_id: sha256:0ede64813b26e6161a0898eec4e0ff5c4fffc9727c0094b5bcfbc6a77c6ef9a0
  D5/S3/QuantumChannels/CoPRelativeQuantumnessRefutation.IsCPTP
    statement_id: sha256:1440f7e681ed2017e7c90aedfe54aa0ad218d57311655f9d554863853dd8f53c
  D5/S3/Quantum/Foundation/FiniteKrausChannel.PhyslibLeaf.MatrixMap.of_kraus._proof_1
    statement_id: sha256:5dc7bcde8ce2ae710c058683e5324d31e0ca70317f167566967eee1cf3b23bbb
  D5/S3/Quantum/Foundation/FiniteKrausChannel.PhyslibLeaf.MatrixMap.of_kraus._proof_2
    statement_id: sha256:9b70ce4858eb731b17facafe93b167007eb9ca6533c641dc770fc553d31ddaa1
  D5/S3/Observer/Existence/EmpiricalReflexiveSeparation.complex_sqrt_two_sq
    statement_id: sha256:aa2d46ddad1e237909d93d17969740efc5ff85ce1ccb3dcbe8b20475fe1e7c71
  D5/S3/Quantum/Algebra/CStarSmaleHigherOrder.sqrt3_sq
    statement_id: sha256:c18076146017460c0664cc760f33eb5d976501bf57026a84e8a3a3a34cc9d38d
  D5/S3/Quantum/Foundation/FiniteStateChannel.QuantumChannel
    statement_id: sha256:b7b2554d55122b11b177ecdf92367d243e4d35ec1e3897c844deba5df1285d05
  D5/S3/Quantum/Foundation/FiniteStateChannel.QuantumChannel.toCompletelyPositiveMap
    statement_id: sha256:7e2eefba0a4c0a6af6a4d36e7168066ad5899f2ba2622c43f082056bec8fb7dc
  D5/S3/Quantum/Foundation/FiniteStateChannel.QuantumChannel.trace_preserving
    statement_id: sha256:f7348a8905d2b54384d2e26b2c769f3d8eae0d734f588b9c2c8b8cc3892faf15
Trace preservation uses the public finite_kraus_quantum_channel; the private
of_kraus_isTracePreserving owner has 114 transitive D5 importers at
05b8ab543cfb52c4a7c6485f1b0a4db11fa858aa, so its module is unchanged.
The channel predicate is the frozen IsCPTP, with the exact completely-positive and
trace-preserving condition of the source; no IsChannel or type alias is introduced.
The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).
The four-slot escape audits of the two published square-root owner declarations
are unfinished: https://github.com/the-omega-institute/trureturing/issues/16616.
Girling, Cîrstoiu and Jennings, Appendix C.5, arXiv:2104.04352v3, conjecture the
lower bound -1. The two dimension-three channels below have overlap -4/3.
-/

import D5.S3.QuantumChannels.CoPRelativeQuantumnessRefutation
import D5.S3.Observer.Existence.EmpiricalReflexiveSeparation
import D5.S3.Quantum.Algebra.CStarSmaleHigherOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped BigOperators ComplexConjugate Matrix
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
open D5.S3.QuantumChannels.CoPRelativeQuantumnessRefutation (IsCPTP)
namespace D5.S3.QuantumChannels.UnitalBlockOverlapRefutation

def IsLiouvilleBasis {d : ℕ}
    (X : Fin (d ^ 2) → Matrix (Fin d) (Fin d) ℂ) (h0 : 0 < d ^ 2) : Prop :=
  (∀ μ ν, ((X μ)ᴴ * X ν).trace = if μ = ν then 1 else 0) ∧
    X ⟨0, h0⟩ = ((Real.sqrt d)⁻¹ : ℂ) • 1

def unitalBlock {d : ℕ} (Φ : MatrixMap (Fin d) (Fin d) ℂ)
    (X : Fin (d ^ 2) → Matrix (Fin d) (Fin d) ℂ) (i j : Fin (d ^ 2)) : ℂ :=
  ((X i)ᴴ * Φ (X j)).trace

def overlap {d : ℕ} (Φ Ψ : MatrixMap (Fin d) (Fin d) ℂ)
    (X : Fin (d ^ 2) → Matrix (Fin d) (Fin d) ℂ) : ℂ :=
  ∑ i : Fin (d ^ 2), ∑ j : Fin (d ^ 2),
    if i.val ≠ 0 ∧ j.val ≠ 0 then star (unitalBlock Φ X i j) * unitalBlock Ψ X i j else 0

def claim : Prop :=
  ∀ (d : ℕ) (h0 : 0 < d ^ 2)
    (Φ Ψ : MatrixMap (Fin d) (Fin d) ℂ)
    (X : Fin (d ^ 2) → Matrix (Fin d) (Fin d) ℂ),
    IsCPTP Φ → IsCPTP Ψ → IsLiouvilleBasis X h0 →
      -1 ≤ (overlap Φ Ψ X).re

private def phi : MatrixMap (Fin 3) (Fin 3) ℂ :=
  MatrixMap.of_kraus
    ![Matrix.single 0 0 1, Matrix.single 0 1 1, Matrix.single 1 2 1]
    ![Matrix.single 0 0 1, Matrix.single 0 1 1, Matrix.single 1 2 1]

private def psi : MatrixMap (Fin 3) (Fin 3) ℂ :=
  MatrixMap.of_kraus
    ![Matrix.single 1 0 1, Matrix.single 1 1 1, Matrix.single 0 2 1]
    ![Matrix.single 1 0 1, Matrix.single 1 1 1, Matrix.single 0 2 1]

-- proof_shape: bind-only; consumer: phi_basis
private theorem phi_apply (A : Matrix (Fin 3) (Fin 3) ℂ) :
    phi A = !![A 0 0 + A 1 1, 0, 0; 0, A 2 2, 0; 0, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [phi, MatrixMap.of_kraus, Matrix.mul_apply,
      Matrix.single, Matrix.conjTranspose_apply, Fin.sum_univ_three]

-- proof_shape: bind-only; consumer: psi_basis
private theorem psi_apply (A : Matrix (Fin 3) (Fin 3) ℂ) :
    psi A = !![A 2 2, 0, 0; 0, A 0 0 + A 1 1, 0; 0, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [psi, MatrixMap.of_kraus, Matrix.mul_apply,
      Matrix.single, Matrix.conjTranspose_apply, Fin.sum_univ_three]

-- proof_shape: bind-only; consumers: phi_channel, psi_channel
private theorem kraus_trace_preserving {d : ℕ} {κ : Type*} [Fintype κ]
    (K : κ → Matrix (Fin d) (Fin d) ℂ)
    (hK : (∑ r, (K r)ᴴ * K r) = 1) :
    ∀ A, (MatrixMap.of_kraus K K A).trace = A.trace := by
  obtain ⟨channel, action⟩ :=
    D5.S3.Quantum.Foundation.FiniteKrausChannel.finite_kraus_quantum_channel K hK
  intro A
  have ht := channel.trace_preserving (CStarMatrix.ofMatrix A)
  change (CStarMatrix.ofMatrix.symm
    (channel.toCompletelyPositiveMap (CStarMatrix.ofMatrix A))).trace = A.trace at ht
  rw [action A] at ht
  simpa only [MatrixMap.of_kraus, LinearMap.sum_apply, LinearMap.coe_mk,
    AddHom.coe_mk] using ht

-- proof_shape: bind-only; consumer: result
private theorem phi_channel : IsCPTP phi := by
  refine ⟨MatrixMap.of_kraus_isCompletelyPositive _, ?_⟩
  unfold phi
  apply kraus_trace_preserving
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Fin.sum_univ_three, Matrix.mul_apply, Matrix.single,
      Matrix.conjTranspose_apply]

-- proof_shape: bind-only; consumer: result
private theorem psi_channel : IsCPTP psi := by
  refine ⟨MatrixMap.of_kraus_isCompletelyPositive _, ?_⟩
  unfold psi
  apply kraus_trace_preserving
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Fin.sum_univ_three, Matrix.mul_apply, Matrix.single,
      Matrix.conjTranspose_apply]

private def basis : Fin 9 → Matrix (Fin 3) (Fin 3) ℂ := ![
  !![(((Real.sqrt 3)⁻¹ : ℝ) : ℂ),0,0; 0,(((Real.sqrt 3)⁻¹ : ℝ) : ℂ),0; 0,0,(((Real.sqrt 3)⁻¹ : ℝ) : ℂ)],
  !![(((Real.sqrt 2)⁻¹ : ℝ) : ℂ),0,0; 0,-(((Real.sqrt 2)⁻¹ : ℝ) : ℂ),0; 0,0,0],
  !![(((Real.sqrt 6)⁻¹ : ℝ) : ℂ),0,0; 0,(((Real.sqrt 6)⁻¹ : ℝ) : ℂ),0; 0,0,-2*(((Real.sqrt 6)⁻¹ : ℝ) : ℂ)],
  !![0,(((Real.sqrt 2)⁻¹ : ℝ) : ℂ),0; (((Real.sqrt 2)⁻¹ : ℝ) : ℂ),0,0; 0,0,0],
  !![0,-Complex.I*(((Real.sqrt 2)⁻¹ : ℝ) : ℂ),0; Complex.I*(((Real.sqrt 2)⁻¹ : ℝ) : ℂ),0,0; 0,0,0],
  !![0,0,(((Real.sqrt 2)⁻¹ : ℝ) : ℂ); 0,0,0; (((Real.sqrt 2)⁻¹ : ℝ) : ℂ),0,0],
  !![0,0,-Complex.I*(((Real.sqrt 2)⁻¹ : ℝ) : ℂ); 0,0,0; Complex.I*(((Real.sqrt 2)⁻¹ : ℝ) : ℂ),0,0],
  !![0,0,0; 0,0,(((Real.sqrt 2)⁻¹ : ℝ) : ℂ); 0,(((Real.sqrt 2)⁻¹ : ℝ) : ℂ),0],
  !![0,0,0; 0,0,-Complex.I*(((Real.sqrt 2)⁻¹ : ℝ) : ℂ); 0,Complex.I*(((Real.sqrt 2)⁻¹ : ℝ) : ℂ),0]]

-- proof_shape: bind-only; consumers: basis_orthonormal, overlap_eq
private theorem c6_sq : ((Real.sqrt 6 : ℝ) : ℂ) ^ 2 = (6 : ℂ) := by
  exact_mod_cast Real.sq_sqrt (show (0 : ℝ) ≤ 6 by norm_num)

-- proof_shape: bind-only; consumers: basis_liouville
private theorem basis_orthonormal (μ ν : Fin 9) :
    ((basis μ)ᴴ * basis ν).trace = if μ = ν then 1 else 0 := by
  fin_cases μ <;> fin_cases ν <;>
    norm_num [basis, Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_three, Matrix.cons_val_two,
      star_mul, map_ofNat] <;>
    ring_nf <;> norm_num [D5.S3.Observer.Existence.EmpiricalReflexiveSeparation.complex_sqrt_two_sq, D5.S3.Quantum.Algebra.CStarSmaleHigherOrder.sqrt3_sq, c6_sq]

-- proof_shape: bind-only; consumers: basis_liouville
private theorem basis_identity : basis 0 = ((Real.sqrt 3)⁻¹ : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [basis]

-- proof_shape: bind-only; consumers: result
private theorem basis_liouville : IsLiouvilleBasis (d := 3) basis (by norm_num) := by
  exact ⟨basis_orthonormal, basis_identity⟩

-- proof_shape: bind-only; consumers: block_phi
private theorem phi_basis (j : Fin 9) (hj : j ≠ 0) :
    phi (basis j) = if j = 2 then !![2*(((Real.sqrt 6)⁻¹ : ℝ) : ℂ),0,0; 0,-2*(((Real.sqrt 6)⁻¹ : ℝ) : ℂ),0; 0,0,0] else 0 := by
  fin_cases j <;> try contradiction
  all_goals
    ext a b
    fin_cases a <;> fin_cases b <;> simp [phi_apply, basis, two_mul]

-- proof_shape: bind-only; consumers: block_psi
private theorem psi_basis (j : Fin 9) (hj : j ≠ 0) :
    psi (basis j) = if j = 2 then !![-2*(((Real.sqrt 6)⁻¹ : ℝ) : ℂ),0,0; 0,2*(((Real.sqrt 6)⁻¹ : ℝ) : ℂ),0; 0,0,0] else 0 := by
  fin_cases j <;> try contradiction
  all_goals
    ext a b
    fin_cases a <;> fin_cases b <;> simp [psi_apply, basis, two_mul]

-- proof_shape: bind-only; consumers: overlap_eq
private theorem block_phi (i j : Fin 9) (hj : j ≠ 0) :
    unitalBlock phi basis i j = if i = 1 ∧ j = 2 then 4*(((Real.sqrt 2)⁻¹ : ℝ) : ℂ)*(((Real.sqrt 6)⁻¹ : ℝ) : ℂ) else 0 := by
  unfold unitalBlock
  rw [phi_basis j hj]
  by_cases h : j = 2
  · subst j
    fin_cases i <;>
      norm_num [basis, Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Fin.sum_univ_three, Matrix.cons_val_two, map_ofNat] <;> ring
  · simp [h]

-- proof_shape: bind-only; consumers: overlap_eq
private theorem block_psi (i j : Fin 9) (hj : j ≠ 0) :
    unitalBlock psi basis i j = if i = 1 ∧ j = 2 then -(4*(((Real.sqrt 2)⁻¹ : ℝ) : ℂ)*(((Real.sqrt 6)⁻¹ : ℝ) : ℂ)) else 0 := by
  unfold unitalBlock
  rw [psi_basis j hj]
  by_cases h : j = 2
  · subst j
    fin_cases i <;>
      norm_num [basis, Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Fin.sum_univ_three, Matrix.cons_val_two, map_ofNat] <;> ring
  · simp [h]

-- proof_shape: bind-only; consumers: result
private theorem overlap_eq : overlap phi psi basis = (-4 / 3 : ℂ) := by
  unfold overlap
  change (∑ i : Fin 9, ∑ j : Fin 9,
    if i.val ≠ 0 ∧ j.val ≠ 0 then
      star (unitalBlock phi basis i j) * unitalBlock psi basis i j else 0) = _
  have hterm (i j : Fin 9) :
      (if i.val ≠ 0 ∧ j.val ≠ 0 then
        star (unitalBlock phi basis i j) * unitalBlock psi basis i j else 0) =
        if i = 1 ∧ j = 2 then -(4*(((Real.sqrt 2)⁻¹ : ℝ) : ℂ)*(((Real.sqrt 6)⁻¹ : ℝ) : ℂ))^2 else 0 := by
    by_cases hj : j = 0
    · subst j
      simp
    · rw [block_phi i j hj, block_psi i j hj]
      by_cases hi : i = 1 ∧ j = 2
      · obtain ⟨rfl,rfl⟩ := hi
        simp
        ring
      · simp [hi]
  simp_rw [hterm]
  simp only [ite_and]
  ring_nf
  norm_num [D5.S3.Observer.Existence.EmpiricalReflexiveSeparation.complex_sqrt_two_sq, c6_sq]

-- proof_shape: bind-only; consumer: external conjecture settlement
theorem result : ¬ claim := by
  intro h
  have hbound := h 3 (by norm_num) phi psi basis phi_channel psi_channel basis_liouville
  rw [overlap_eq] at hbound
  norm_num at hbound

end D5.S3.QuantumChannels.UnitalBlockOverlapRefutation
