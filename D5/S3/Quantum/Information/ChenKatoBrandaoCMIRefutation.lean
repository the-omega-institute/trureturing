/- GID: D5/S3/Quantum/Information/ChenKatoBrandaoCMIRefutation
   generality: G
   mirror-B: D5/B/S3/Quantum/Information/ChenKatoBrandaoCMIRefutation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Information/ChenKatoBrandaoCMIRefutation.claim; result=D5/S3/Quantum/Information/ChenKatoBrandaoCMIRefutation.result; claim=D5/S3/Quantum/Information/ChenKatoBrandaoCMIRefutation.claim
   digest: Scalar correctable observables do not force strict CMI contraction. -/

/-
result
  proof_shape: bind-only
  escape_witness: none (the settling result uses open-problem-resolution).
  admission_basis: open-problem-resolution (#13891; Refuted).
Direct frozen dependencies:
  D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceLeft
    declaration statement_id: sha256:68653a556c9228bbd8018884585aa56fe5fce5cd40b4a12a493f4aa319c78f5d
  D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceRight
    declaration statement_id: sha256:8fd00cbe799f3e8a3163a296b2ad235e0a251e3e79b744b52197ba12d0343f77
  D5/S3/Quantum/Information/PartialTraceMutualInformation.spectral_sum_eq_of_charpoly_prod
    declaration statement_id: sha256:dafc3dfdcf5048650b86f2007835dd68d7d16eee997da46a835084ecf12d3119
  D5/S3/Quantum/Foundation/FiniteKrausChannel.PhyslibLeaf.MatrixMap.of_kraus
    declaration statement_id: sha256:024ca3125b8f182e070b880d7c41840a31fa9cb0aaa89e5d81dbe4ebb3c5f287
  D5/S3/Quantum/Divergence/QuantumRelativeEntropyDefectComposition.DensityState
    declaration statement_id: sha256:b8e1957ba4f81600248989dc21f0a107bcdd5ce2e68546c38b9164c4a09ac337
Information-escape registration is paused under CLAUDE.md section 3.9.
Private helper classifications:
  family_correctable: content; whole-space commutant reduction and cyclic induction;
    consumer: result. Its content does not change result's conservative bind-only label.
  entropy_diagonal: bind-only; consumer: cmi_diagonal.
  family_diag_product: bind-only; consumers: family_normal, family_correctable.
  family_edge_product: bind-only; consumer: family_correctable.
  family_normal: bind-only; consumer: result.
  partialTraceRight_diagonal: bind-only; consumer: cmi_diagonal.
  partialTraceLeft_diagonal: bind-only; consumer: cmi_diagonal.
  assoc_diagonal: bind-only; consumer: cmi_diagonal.
  cmi_diagonal: bind-only; consumers: witness_cmi, output_cmi.
  witness_cmi: bind-only; consumer: result.
  output_cmi: bind-only; consumer: result.
  witness_density: bind-only; consumer: witnessState.
  witness_action: bind-only; consumer: result.
-/

import D5.S3.Quantum.Information.PartialTraceMutualInformation
import D5.S3.Quantum.Foundation.FiniteKrausChannel

open Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Information.ChenKatoBrandaoCMIRefutation
noncomputable section

variable {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

def correctable {ι : Type*} (K : ι → Matrix b a ℂ) : Subalgebra ℂ (Matrix a a ℂ) :=
  Algebra.adjoin ℂ {O | ∀ i j, Commute O ((K i)ᴴ * K j)}

def entropy (M : Matrix a a ℂ) : ℝ :=
  if h : M.IsHermitian then spectralEntropy h else 0

def cmi {A B C : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
    (M : Matrix ((A × B) × C) ((A × B) × C) ℂ) : ℝ :=
  entropy (partialTraceRight M) +
  entropy (partialTraceLeft (M.submatrix (fun x : A × (B × C) => ((x.1,x.2.1),x.2.2))
    (fun x : A × (B × C) => ((x.1,x.2.1),x.2.2)))) -
  entropy (partialTraceRight (partialTraceLeft (M.submatrix
    (fun x : A × (B × C) => ((x.1,x.2.1),x.2.2))
    (fun x : A × (B × C) => ((x.1,x.2.1),x.2.2))))) - entropy M


def claim : Prop :=
  ∀ (n n' : ℕ),
  ∀ (ι : Type) [Fintype ι] (K : ι → Matrix (Fin n') (Fin n) ℂ),
  (∑ i, (K i)ᴴ * K i) = 1 → correctable K = ⊥ →
  ∃ η : ℝ, η < 1 ∧ ∀ (dA dB : ℕ),
  ∀ ρ : DensityState ((Fin dA × Fin dB) × Fin n),
    cmi ((of_kraus (fun i => (1 : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ) ⊗ₖ K i)
      (fun i => (1 : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ) ⊗ₖ K i)) (CStarMatrix.ofMatrix.symm ρ.1)) ≤
      η * cmi (CStarMatrix.ofMatrix.symm ρ.1)

private theorem entropy_diagonal (d : a → ℝ) :
    entropy (diagonal (fun i => (d i : ℂ))) = ∑ i, Real.negMulLog (d i) := by
  have hh : (diagonal (fun i => (d i : ℂ))).IsHermitian := by
    apply Matrix.isHermitian_diagonal_iff.mpr
    intro i
    simp [isSelfAdjoint_iff]
  rw [entropy, dif_pos hh, spectralEntropy]
  apply spectral_sum_eq_of_charpoly_prod hh d Real.negMulLog
  simpa using Matrix.charpoly_diagonal (fun i => (d i : ℂ))

-- j+1 is computed in the finite cyclic group.

private def familyK (n : ℕ) [NeZero n] (p : ℝ) (k : Fin n × Bool) : Matrix (Fin n) (Fin n) ℂ :=
  single (if k.2 then k.1 + 1 else k.1) k.1
    (if k.2 then (Real.sqrt p : ℂ) else (Real.sqrt (1-p) : ℂ))

private theorem family_diag_product (n : ℕ) [NeZero n] (p : ℝ) (hp : p ≤ 1) (j : Fin n) :
    (familyK n p (j,false))ᴴ * familyK n p (j,false) = single j j ((1-p : ℝ) : ℂ) := by
  simp only [familyK, Bool.false_eq_true, ↓reduceIte, conjTranspose_single,
    Complex.star_def, Complex.conj_ofReal, single_mul_single_same]
  congr 1
  exact_mod_cast Real.mul_self_sqrt (sub_nonneg.mpr hp)

private theorem family_edge_product (n : ℕ) [NeZero n] (p : ℝ) (j : Fin n) :
    (familyK n p (j+1,false))ᴴ * familyK n p (j,true) =
      single (j+1) j ((Real.sqrt (1-p) * Real.sqrt p : ℝ) : ℂ) := by
  simp [familyK, conjTranspose_single, single_mul_single_same]

private theorem family_normal (n : ℕ) [NeZero n] (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (∑ k : Fin n × Bool, (familyK n p k)ᴴ * familyK n p k) = 1 := by
  have htrue (j : Fin n) : (familyK n p (j,true))ᴴ * familyK n p (j,true) =
      single j j (p : ℂ) := by
    simp only [familyK, ↓reduceIte, conjTranspose_single,
      Complex.star_def, Complex.conj_ofReal, single_mul_single_same]
    congr 1
    exact_mod_cast Real.mul_self_sqrt hp0
  ext i j
  simp only [Fintype.sum_prod_type, Matrix.sum_apply, Fintype.sum_bool,
    family_diag_product n p hp1, htrue]
  by_cases hij : i = j
  · subst j
    simp [single, Finset.sum_add_distrib]
  · have hx (x : Fin n) : ¬ (x = i ∧ x = j) := by
      rintro ⟨rfl,h⟩
      exact hij h
    simp [single, Matrix.one_apply, hij, hx]

private theorem family_correctable (n : ℕ) [NeZero n] (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    correctable (familyK n p) = ⊥ := by
  apply le_antisymm _ bot_le
  apply Algebra.adjoin_le
  intro O hO
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hcoef : ((1-p : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (sub_pos.mpr hp1))
  have hecoef : ((Real.sqrt (1-p) * Real.sqrt p : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (mul_pos (Real.sqrt_pos.2 (sub_pos.mpr hp1)) (Real.sqrt_pos.2 hp0)))
  have hoff (i j : Fin n) (hij : i ≠ j) : O i j = 0 := by
    have h := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M i j)
      (hO (j,false) (j,false)).eq
    rw [family_diag_product n p hp1.le j] at h
    have hh : O i j * ((1-p : ℝ) : ℂ) = 0 := by
      simpa [Matrix.mul_apply, Matrix.single, hij, eq_comm] using h
    exact (mul_eq_zero.mp hh).resolve_right hcoef
  have hedge (j : Fin n) : O (j+1) (j+1) = O j j := by
    have h := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M (j+1) j)
      (hO (j+1,false) (j,true)).eq
    rw [family_edge_product] at h
    have hh : O (j+1) (j+1) * ((Real.sqrt (1-p) * Real.sqrt p : ℝ) : ℂ) =
        ((Real.sqrt (1-p) * Real.sqrt p : ℝ) : ℂ) * O j j := by
      simpa [Matrix.mul_apply, Matrix.single, eq_comm] using h
    rw [mul_comm _ (O j j)] at hh
    exact mul_right_cancel₀ hecoef hh
  have hdiag (k : ℕ) : ∀ hk : k < n, O ⟨k,hk⟩ ⟨k,hk⟩ = O 0 0 := by
    induction k with
    | zero => intro hk; rfl
    | succ k ih =>
      intro hk
      have hk' : k < n := by omega
      have hs : (⟨k,hk'⟩ : Fin n) + 1 = ⟨k+1,hk⟩ := by
        apply Fin.ext
        simp [Fin.val_add, Nat.mod_eq_of_lt hk]
      rw [← hs, hedge, ih hk']
  change O ∈ (⊥ : Subalgebra ℂ (Matrix (Fin n) (Fin n) ℂ))
  rw [Algebra.mem_bot]
  refine ⟨O 0 0, ?_⟩
  ext i j
  by_cases hij : i = j
  · subst j
    simpa [Algebra.algebraMap_eq_smul_one] using (hdiag i.val i.isLt).symm
  · simp [Algebra.algebraMap_eq_smul_one, Matrix.one_apply, hij, hoff i j hij]

section DiagonalMarginals
variable {A B C : Type*} [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]

private theorem partialTraceRight_diagonal (r : A × B → ℝ) :
    partialTraceRight (diagonal (fun x => (r x : ℂ))) =
      diagonal (fun a => ((∑ b, r (a,b) : ℝ) : ℂ)) := by
  ext i j
  by_cases h : i = j
  · subst j; simp [partialTraceRight, Matrix.diagonal]
  · simp [partialTraceRight, Matrix.diagonal, h]

private theorem partialTraceLeft_diagonal (r : A × B → ℝ) :
    partialTraceLeft (diagonal (fun x => (r x : ℂ))) =
      diagonal (fun b => ((∑ a, r (a,b) : ℝ) : ℂ)) := by
  ext i j
  by_cases h : i = j
  · subst j; simp [partialTraceLeft, Matrix.diagonal]
  · simp [partialTraceLeft, Matrix.diagonal, h]

private theorem assoc_diagonal (r : (A × B) × C → ℝ) :
    (diagonal (fun x => (r x : ℂ))).submatrix
      (fun x : A × (B × C) => ((x.1,x.2.1),x.2.2))
      (fun x : A × (B × C) => ((x.1,x.2.1),x.2.2)) =
    diagonal (fun x : A × (B × C) => (r ((x.1,x.2.1),x.2.2) : ℂ)) := by
  ext i j
  simp [Matrix.diagonal, Matrix.submatrix_apply, Prod.ext_iff, and_assoc]

private theorem cmi_diagonal (r : (A × B) × C → ℝ) :
    cmi (diagonal (fun x => (r x : ℂ))) =
      (∑ ab : A × B, Real.negMulLog (∑ c, r (ab,c))) +
      (∑ bc : B × C, Real.negMulLog (∑ a, r ((a,bc.1),bc.2))) -
      (∑ b : B, Real.negMulLog (∑ c, ∑ a, r ((a,b),c))) -
      ∑ x, Real.negMulLog (r x) := by
  unfold cmi
  rw [partialTraceRight_diagonal, assoc_diagonal, partialTraceLeft_diagonal,
    partialTraceRight_diagonal]
  simp only [entropy_diagonal]

end DiagonalMarginals

private def witnessWeights (x : (Fin 2 × Fin 1) × Fin 4) : ℝ :=
  if (x.1.1 = 0 ∧ x.2 = 0) ∨ (x.1.1 = 1 ∧ x.2 = 2) then 1/2 else 0

private def witnessMatrix : Matrix ((Fin 2 × Fin 1) × Fin 4) ((Fin 2 × Fin 1) × Fin 4) ℂ :=
  diagonal (fun x => (witnessWeights x : ℂ))

private def outputWeights (x : (Fin 2 × Fin 1) × Fin 4) : ℝ :=
  if (x.1.1 = 0 ∧ (x.2 = 0 ∨ x.2 = 1)) ∨
     (x.1.1 = 1 ∧ (x.2 = 2 ∨ x.2 = 3)) then 1/4 else 0

private def outputMatrix : Matrix ((Fin 2 × Fin 1) × Fin 4) ((Fin 2 × Fin 1) × Fin 4) ℂ :=
  diagonal (fun x => (outputWeights x : ℂ))

private theorem witness_cmi : cmi witnessMatrix = Real.log 2 := by
  rw [witnessMatrix, cmi_diagonal]
  simp [witnessWeights, Fintype.sum_prod_type, Fin.sum_univ_succ,
    ]
  norm_num [Real.negMulLog, Real.log_div, Real.log_inv, Real.log_pow]
  ring

private theorem output_cmi : cmi outputMatrix = Real.log 2 := by
  rw [outputMatrix, cmi_diagonal]
  simp [outputWeights, Fintype.sum_prod_type, Fin.sum_univ_succ,
    ]
  norm_num [Real.negMulLog, Real.log_div, Real.log_inv, Real.log_pow]
  ring

set_option maxHeartbeats 4000000

private theorem witness_density : witnessMatrix.PosSemidef ∧ witnessMatrix.trace = 1 := by
  constructor
  · apply Matrix.posSemidef_diagonal_iff.mpr
    intro x
    change (0 : ℂ) ≤ (witnessWeights x : ℂ)
    have hx : 0 ≤ witnessWeights x := by
      unfold witnessWeights
      split <;> norm_num
    exact_mod_cast hx
  · simp [witnessMatrix, Matrix.trace_diagonal, witnessWeights,
      Fintype.sum_prod_type, Fin.sum_univ_succ]
    norm_num

private def witnessState : DensityState ((Fin 2 × Fin 1) × Fin 4) :=
  ⟨CStarMatrix.ofMatrix witnessMatrix,
    map_nonneg CStarMatrix.ofMatrixStarAlgEquiv witness_density.1.nonneg,
    witness_density.2⟩

private theorem witness_action : (of_kraus (fun i => (1 : Matrix (Fin 2 × Fin 1) (Fin 2 × Fin 1) ℂ) ⊗ₖ familyK 4 (1/2) i)
    (fun i => (1 : Matrix (Fin 2 × Fin 1) (Fin 2 × Fin 1) ℂ) ⊗ₖ familyK 4 (1/2) i)) witnessMatrix = outputMatrix := by
  change (∑ i : Fin 4 × Bool,
    ((1 : Matrix (Fin 2 × Fin 1) (Fin 2 × Fin 1) ℂ) ⊗ₖ familyK 4 (1/2) i) *
      witnessMatrix *
    ((1 : Matrix (Fin 2 × Fin 1) (Fin 2 × Fin 1) ℂ) ⊗ₖ familyK 4 (1/2) i)ᴴ) = outputMatrix
  have hsq2 : (Real.sqrt 2 : ℂ)^2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  ext ⟨⟨a,b⟩,c⟩ ⟨⟨a',b'⟩,c'⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    fin_cases a' <;> fin_cases b' <;> fin_cases c' <;>
    simp [familyK, witnessMatrix, outputMatrix, witnessWeights, outputWeights,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply,
      Matrix.one_apply, Matrix.diagonal, Matrix.single,
      Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_succ] <;>
    ring_nf <;> norm_num [hsq2]

theorem result : ¬ claim := by
  intro h
  obtain ⟨η,hη,hbound⟩ := h 4 4 (Fin 4 × Bool) (familyK 4 (1/2))
    (family_normal 4 (1/2) (by norm_num) (by norm_num))
    (family_correctable 4 (1/2) (by norm_num) (by norm_num))
  have hb := hbound 2 1 witnessState
  change cmi ((of_kraus (fun i => (1 : Matrix (Fin 2 × Fin 1) (Fin 2 × Fin 1) ℂ) ⊗ₖ familyK 4 (1/2) i)
    (fun i => (1 : Matrix (Fin 2 × Fin 1) (Fin 2 × Fin 1) ℂ) ⊗ₖ familyK 4 (1/2) i)) witnessMatrix) ≤ η * cmi witnessMatrix at hb
  rw [witness_action, witness_cmi, output_cmi] at hb
  have hp : 0 < Real.log 2 := Real.log_pos (by norm_num)
  nlinarith

#print axioms result

end
end D5.S3.Quantum.Information.ChenKatoBrandaoCMIRefutation
