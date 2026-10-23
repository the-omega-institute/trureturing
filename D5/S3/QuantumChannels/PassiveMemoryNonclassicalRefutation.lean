/- GID: D5/S3/QuantumChannels/PassiveMemoryNonclassicalRefutation
   generality: I
   mirror-B: D5/B/S3/QuantumChannels/PassiveMemoryNonclassicalRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/QuantumChannels/PassiveMemoryNonclassicalRefutation.claim; result=D5/S3/QuantumChannels/PassiveMemoryNonclassicalRefutation.result; claim=D5/S3/QuantumChannels/PassiveMemoryNonclassicalRefutation.claim
   digest: A passive qubit memory for a qutrit system refutes classical Gram simulation. -/

import D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction
import D5.S3.Quantum.Foundation.FiniteKrausRepresentation
import D5.S3.Quantum.Information.PartialTraceMutualInformation
import D5.S3.Quantum.Entanglement.StructuredNegativityCoincidenceRefutation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
noncomputable section

open Matrix
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Entanglement.StructuredNegativityCoincidenceRefutation
open D5.S3.Quantum.FiniteDimensional

namespace D5.S3.QuantumChannels.PassiveMemoryNonclassicalRefutation

abbrev Mat (ι : Type*) := Matrix ι ι ℂ

def KrausChannel (ι : Type*) [Fintype ι] [DecidableEq ι] : Type _ :=
  Σ n : ℕ, {K : Fin n → Mat ι // (∑ a, (K a).conjTranspose * K a) = 1}

def act {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : KrausChannel ι) : MatrixMap ι ι ℂ :=
  MatrixMap.of_kraus E.2.1 E.2.1

def stateMatrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : DensityState ι) : Mat ι :=
  CStarMatrix.ofMatrix.symm ρ.1

def appendMemory {d r : ℕ} (τ : DensityState (Fin r)) :
    MatrixMap (Fin d) (Fin d × Fin r) ℂ :=
  { toFun := fun A => Matrix.kronecker A (stateMatrix τ)
    map_add' := fun A B => Matrix.add_kronecker A B (stateMatrix τ)
    map_smul' := by
      intro c A
      ext ⟨i, a⟩ ⟨j, b⟩
      simp [Matrix.kronecker_apply, Matrix.smul_apply, smul_eq_mul]
      ring }

def discardMemory {d r : ℕ} : MatrixMap (Fin d × Fin r) (Fin d) ℂ :=
  { toFun := partialTraceRight
    map_add' := partialTraceRight_add
    map_smul' :=
      D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction.partialTraceRight_smul }

def implemented {d r : ℕ} (τ : DensityState (Fin r))
    (Nen Nde : KrausChannel (Fin d × Fin r))
    (E : KrausChannel (Fin d)) : MatrixMap (Fin d) (Fin d) ℂ :=
  (discardMemory (d := d) (r := r)).comp
    ((act Nde).comp
      ((MatrixMap.kron (act E) (LinearMap.id : MatrixMap (Fin r) (Fin r) ℂ)).comp
        ((act Nen).comp (appendMemory (d := d) τ))))

def choi (d : ℕ) (F : MatrixMap (Fin d) (Fin d) ℂ) :
    Mat (Fin d × Fin d) :=
  (d : ℂ)⁻¹ • MatrixMap.choi_matrix F

def Gram {ι : Type*} (C : Mat ι) : Prop :=
  C.PosSemidef ∧ ∀ i, C i i = 1

def DephasingGram {d : ℕ} (C : Mat (Fin d × Fin d)) : Prop :=
  Gram C ∧ ∀ i k j l : Fin d, C (i,j) (i,l) = C (k,j) (k,l)

def Passive {d r : ℕ} (τ : DensityState (Fin r))
    (Nen : KrausChannel (Fin d × Fin r)) : Prop :=
  ∀ ρ σ : DensityState (Fin d),
    partialTraceLeft (act Nen (Matrix.kronecker (stateMatrix ρ) (stateMatrix τ))) =
    partialTraceLeft (act Nen (Matrix.kronecker (stateMatrix σ) (stateMatrix τ)))

def ClassicalGram {d : ℕ} (C : Mat (Fin d × Fin d)) : Prop :=
  ∃ (n : ℕ) (q : Fin n → ℝ) (P Q : Fin n → Mat (Fin d)),
    (∀ a, 0 ≤ q a) ∧ (∑ a, q a) = 1 ∧
    (∀ a, Gram (P a) ∧ Gram (Q a)) ∧
    C = ∑ a, q a • Matrix.kronecker (P a) (Q a)

def Implements {d r : ℕ} (τ : DensityState (Fin r))
    (Nen Nde : KrausChannel (Fin d × Fin r))
    (C : Mat (Fin d × Fin d)) : Prop :=
  DephasingGram C ∧ ∀ E : KrausChannel (Fin d),
    choi d (implemented τ Nen Nde E) = Matrix.hadamard C (choi d (act E))

def claim : Prop :=
  ∀ (d r : ℕ), 0 < d → 0 < r →
    ∀ (τ : DensityState (Fin r))
      (Nen Nde : KrausChannel (Fin d × Fin r))
      (C : Mat (Fin d × Fin d)),
      Implements τ Nen Nde C → Passive τ Nen → ClassicalGram C

private noncomputable def tau0 : DensityState (Fin 2) := by
  refine ⟨CStarMatrix.ofMatrix ((1 / 2 : ℝ) • (1 : Mat (Fin 2))), ?_, ?_⟩
  · apply map_nonneg CStarMatrix.ofMatrixStarAlgEquiv
    apply Matrix.nonneg_iff_posSemidef.mpr
    exact (Matrix.PosSemidef.one (n := Fin 2) (R := ℂ)).smul (a := (1 / 2 : ℝ))
      (by norm_num)
  · change Matrix.trace ((1 / 2 : ℝ) • (1 : Mat (Fin 2))) = 1
    rw [Matrix.trace_smul]
    norm_num

private def controls : Fin 3 → Mat (Fin 2) := fun i =>
  if i = 0 then 1 else if i = 1 then qubitX else qubitZ

private def controlled : Mat (Fin 3 × Fin 2) :=
  (Matrix.blockDiagonal controls).submatrix Prod.swap Prod.swap

private theorem controls_apply (i : Fin 3) (a b : Fin 2) :
    controls i a b = if i = 0 then (if a = b then 1 else 0)
      else if i = 1 then qubitX a b else qubitZ a b := by
  fin_cases i <;> fin_cases a <;> fin_cases b <;> rfl

private theorem controlled_apply (p q : Fin 3 × Fin 2) :
    controlled p q =
      if p.1 = q.1 then
        if p.1 = 0 then (if p.2 = q.2 then 1 else 0)
        else if p.1 = 1 then qubitX p.2 q.2 else qubitZ p.2 q.2
      else 0 := by
  simp only [controlled.eq_1, Matrix.submatrix_apply, Matrix.blockDiagonal_apply,
    Prod.swap]
  rw [controls_apply]

private theorem controlled_unitary :
    controlled.conjTranspose * controlled = 1 := by
  ext ⟨i, a⟩ ⟨j, b⟩
  fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
    simp [controlled_apply, controls_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_three, qubitX, qubitZ]

private def witnessChannel : KrausChannel (Fin 3 × Fin 2) :=
  ⟨1, ⟨fun _ => controlled, by simpa [Fin.sum_univ_one] using controlled_unitary⟩⟩

private def gramFactor : Matrix (Fin 4) (Fin 3 × Fin 3) ℂ := fun a p =>
  if a = 0 then (if p.1 = p.2 then 1 else 0)
  else if a = 1 then
    (if (p = (0, 1) ∨ p = (1, 0)) then 1 else 0)
  else if a = 2 then
    (if (p = (0, 2) ∨ p = (2, 0)) then 1 else 0)
  else if p = (1, 2) then 1 else if p = (2, 1) then -1 else 0

private def witnessC : Mat (Fin 3 × Fin 3) := gramFactor.conjTranspose * gramFactor

private theorem witnessC_gram : Gram witnessC := by
  constructor
  · exact Matrix.posSemidef_conjTranspose_mul_self gramFactor
  · intro p
    rcases p with ⟨p1, p2⟩
    fin_cases p1 <;> fin_cases p2 <;>
      dsimp only [witnessC] <;>
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_four] <;>
      dsimp only [gramFactor] <;>
      simp [Matrix.mul_apply, Fin.sum_univ_four]

private theorem witnessC_formula (p q : Fin 3 × Fin 3) :
    witnessC p q = (1 / 2 : ℂ) * Matrix.trace
      (controls p.1 * controls p.2 * (controls q.2).conjTranspose *
        (controls q.1).conjTranspose) := by
  rcases p with ⟨p1, p2⟩
  rcases q with ⟨q1, q2⟩
  fin_cases p1 <;> fin_cases p2 <;> fin_cases q1 <;> fin_cases q2 <;>
    dsimp only [witnessC] <;>
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.trace,
      Fin.sum_univ_four, Fin.sum_univ_two] <;>
    dsimp only [gramFactor, controls] <;>
    norm_num +decide [Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.trace, Fin.sum_univ_four,
      Fin.sum_univ_two, dotProduct, Matrix.mulVec, Matrix.vecMul,
      Matrix.mulVec_eq_sum, Matrix.vecMul_eq_sum, Matrix.cons_val_zero,
      Matrix.cons_val_succ, Matrix.head_cons, Matrix.tail_cons,
      Matrix.cons_val_one, Matrix.cons_val_two, Fin.reduceFinMk, Fin.reduceEq,
      qubitX, qubitZ]

private theorem witnessC_dephasing : DephasingGram witnessC := by
  constructor
  · exact witnessC_gram
  · intro i k j l
    fin_cases i <;> fin_cases k <;> fin_cases j <;> fin_cases l <;>
      dsimp only [witnessC] <;>
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_four] <;>
      dsimp only [gramFactor] <;>
      simp [Matrix.mul_apply, Fin.sum_univ_four]

private theorem witness_memory_marginal (ρ : DensityState (Fin 3)) :
    partialTraceLeft (act witnessChannel
      (Matrix.kronecker (stateMatrix ρ) (stateMatrix tau0))) = stateMatrix tau0 := by
  have htr : Matrix.trace (stateMatrix ρ) = 1 := DensityState.trace_eq_one ρ
  have htr' : ∑ i : Fin 3, stateMatrix ρ i i = 1 := by
    simpa [Matrix.trace] using htr
  have htr'' : ∑ i : Fin 3, (ρ.1 : Mat (Fin 3)) i i = 1 := by
    dsimp only [stateMatrix] at htr'
    simpa using htr'
  change partialTraceLeft
    (MatrixMap.of_kraus (fun _ : Fin 1 => controlled) (fun _ : Fin 1 => controlled)
      (Matrix.kronecker (stateMatrix ρ) (stateMatrix tau0))) = stateMatrix tau0
  ext b d
  have hcard1 : (Finset.univ : Finset (Fin 1)).card = 1 := Finset.card_fin 1
  fin_cases b <;> fin_cases d <;>
    simp only [MatrixMap.of_kraus, LinearMap.sum_apply, LinearMap.coe_mk,
      AddHom.coe_mk, Matrix.mul_apply, Matrix.conjTranspose_apply, partialTraceLeft,
      Fintype.sum_prod_type, Fin.sum_univ_one, Fin.sum_univ_two, Fin.sum_univ_three,
      Matrix.kronecker_apply] at htr ⊢ <;>
    dsimp only [stateMatrix, tau0] at htr ⊢ <;>
    simp [controlled_apply, controls_apply, MatrixMap.of_kraus,
      LinearMap.sum_apply, LinearMap.coe_mk, AddHom.coe_mk,
      Matrix.mul_apply, Matrix.conjTranspose_apply, partialTraceLeft,
      Fintype.sum_prod_type, Fin.sum_univ_one, Fin.sum_univ_two, Fin.sum_univ_three,
      qubitX, qubitZ, Matrix.kronecker_apply] at htr ⊢
  all_goals norm_num [Finset.card_univ, Fintype.card_fin, Finset.card_fin]
  · have htr''' : (ρ.1 : Mat (Fin 3)) 0 0 + (ρ.1 : Mat (Fin 3)) 1 1 +
        (ρ.1 : Mat (Fin 3)) 2 2 = 1 := by
      simpa only [Fin.sum_univ_three] using htr''
    linear_combination (1 / 2 : ℂ) * htr'''
  · have htr''' : (ρ.1 : Mat (Fin 3)) 0 0 + (ρ.1 : Mat (Fin 3)) 1 1 +
        (ρ.1 : Mat (Fin 3)) 2 2 = 1 := by
      simpa only [Fin.sum_univ_three] using htr''
    linear_combination (1 / 2 : ℂ) * htr'''

private theorem witness_passive : Passive tau0 witnessChannel := by
  intro ρ σ
  rw [witness_memory_marginal ρ, witness_memory_marginal σ]

set_option maxHeartbeats 2000000 in
-- The finite controlled-channel expansion needs more reduction heartbeats.
private theorem controlled_tensor (A : Mat (Fin 3)) (B : Mat (Fin 2))
    (i k : Fin 3) (a b : Fin 2) :
    act witnessChannel (Matrix.kronecker A B) (i,a) (k,b) =
      A i k * (controls i * B * (controls k).conjTranspose) a b := by
  change MatrixMap.of_kraus (fun _ : Fin 1 => controlled)
    (fun _ : Fin 1 => controlled) (Matrix.kronecker A B) (i,a) (k,b) = _
  fin_cases i <;> fin_cases k <;> fin_cases a <;> fin_cases b <;>
    simp [controlled_apply, controls_apply, MatrixMap.of_kraus, Matrix.kronecker_apply,
      Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type, Fin.sum_univ_one, Fin.sum_univ_two,
      Fin.sum_univ_three]
  all_goals norm_num [Finset.card_fin]
  all_goals ring

private theorem encoded_unit (j l : Fin 3) :
    act witnessChannel
      (Matrix.kronecker (Matrix.single j l 1) (stateMatrix tau0)) =
    Matrix.kronecker (Matrix.single j l 1)
      (controls j * stateMatrix tau0 * (controls l).conjTranspose) := by
  change act witnessChannel (Matrix.kronecker (Matrix.single j l 1)
      (stateMatrix tau0)) = _
  ext ⟨i,a⟩ ⟨k,b⟩
  rw [controlled_tensor]
  by_cases hi : i = j <;> by_cases hk : k = l
  all_goals simp_all [Matrix.kronecker_apply, Matrix.single, eq_comm]

private theorem append_unit (j l : Fin 3) :
    appendMemory (d := 3) tau0 (Matrix.single j l 1) =
      Matrix.kronecker (Matrix.single j l 1) (stateMatrix tau0) := by
  rfl

set_option maxHeartbeats 2000000 in
-- The tensor-map basis expansion needs more reduction heartbeats.
private theorem tensor_unit (E : MatrixMap (Fin 3) (Fin 3) ℂ)
    (B : Mat (Fin 2)) (j l : Fin 3) :
    MatrixMap.kron E (LinearMap.id : MatrixMap (Fin 2) (Fin 2) ℂ)
      (Matrix.kronecker (Matrix.single j l 1) B) =
      Matrix.kronecker (E (Matrix.single j l 1)) B := by
  ext ⟨i,a⟩ ⟨k,b⟩
  rw [MatrixMap.kron_def]
  fin_cases i <;> fin_cases k <;> fin_cases a <;> fin_cases b <;>
    fin_cases j <;> fin_cases l <;>
    simp [Matrix.kronecker_apply, Matrix.single, Fin.sum_univ_three,
      Fin.sum_univ_two]

private theorem witness_choi_identity (E : KrausChannel (Fin 3)) :
    choi 3 (implemented tau0 witnessChannel witnessChannel E) =
      Matrix.hadamard witnessC (choi 3 (act E)) := by
  ext ⟨i,j⟩ ⟨k,l⟩
  dsimp only [choi, MatrixMap.choi_matrix, Matrix.smul_apply, smul_eq_mul, implemented]
  simp only [LinearMap.comp_apply, LinearMap.coe_mk, AddHom.coe_mk]
  rw [append_unit, encoded_unit, tensor_unit]
  simp only [Matrix.hadamard_apply]
  change (3 : ℂ)⁻¹ * (∑ a : Fin 2, act witnessChannel
    (Matrix.kronecker (act E (Matrix.single j l 1))
      (controls j * stateMatrix tau0 * (controls l).conjTranspose)) (i,a) (k,a)) = _
  simp only [controlled_tensor, ← Finset.mul_sum]
  rw [witnessC_formula]
  change (3 : ℂ)⁻¹ * (act E (Matrix.single j l 1) i k *
    Matrix.trace (controls i * (controls j * stateMatrix tau0 *
      (controls l).conjTranspose) * (controls k).conjTranspose)) =
    ((1 / 2 : ℂ) * Matrix.trace (controls i * controls j *
      (controls l).conjTranspose * (controls k).conjTranspose)) *
    ((3 : ℂ)⁻¹ * act E (Matrix.single j l 1) i k)
  have ht : stateMatrix tau0 = (1 / 2 : ℂ) • (1 : Mat (Fin 2)) := by
    ext a b
    dsimp only [stateMatrix, tau0]
    simp [Matrix.smul_apply, smul_eq_mul]
  rw [ht]
  simp only [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.trace_smul,
    smul_eq_mul, Matrix.mul_assoc]
  ring

private theorem witness_implements : Implements tau0 witnessChannel witnessChannel witnessC :=
  ⟨witnessC_dephasing, witness_choi_identity⟩

private theorem classical_ppt {d : ℕ} {C : Mat (Fin d × Fin d)}
    (h : ClassicalGram C) : (partialTransposeB C).PosSemidef := by
  rcases h with ⟨n, q, P, Q, hq, _, hG, hC⟩
  have heq : partialTransposeB C =
      ∑ a : Fin n, q a • Matrix.kronecker (P a) (Q a).transpose := by
    rw [hC]
    ext ⟨i,j⟩ ⟨k,l⟩
    simp only [partialTransposeB, Matrix.sum_apply, Matrix.smul_apply,
      Matrix.kronecker_apply, Matrix.transpose_apply]
    rfl
  rw [heq]
  apply Matrix.posSemidef_sum
  intro a ha
  exact ((hG a).1.1.kronecker (hG a).2.1.transpose).smul (hq a)

private theorem witness_not_ppt : ¬ (partialTransposeB witnessC).PosSemidef := by
  intro h
  have hp := h.submatrix (fun i : Fin 3 => (i,i))
  have hn := hp.dotProduct_mulVec_nonneg (![-1,1,1] : Fin 3 → ℂ)
  have hb : (partialTransposeB witnessC).submatrix (fun i : Fin 3 => (i,i))
      (fun i : Fin 3 => (i,i)) = !![(1 : ℂ),1,1; 1,1,-1; 1,-1,1] := by
    ext i j
    change witnessC (i,j) (j,i) = _
    rw [witnessC_formula]
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Fin.sum_univ_two] <;>
      dsimp only [controls] <;>
      simp [Matrix.trace,
        Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two,
        Matrix.vecMul, Matrix.vecMul_eq_sum, Matrix.cons_val_zero,
        Matrix.cons_val_succ, Matrix.head_cons, Matrix.tail_cons,
        qubitX, qubitZ]
    all_goals norm_num
  have hv : star (![-1,1,1] : Fin 3 → ℂ) ⬝ᵥ
      ((partialTransposeB witnessC).submatrix (fun i : Fin 3 => (i,i))
        (fun i : Fin 3 => (i,i)) *ᵥ (![-1,1,1] : Fin 3 → ℂ)) = -3 := by
    rw [hb]
    norm_num [dotProduct, Matrix.mulVec, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_succ, Matrix.head_cons, Matrix.tail_cons,
      Matrix.vecHead, Matrix.vecTail]
  rw [hv] at hn
  rw [Complex.nonneg_iff] at hn
  norm_num at hn

theorem result : ¬ claim := by
  intro h
  have hc := h 3 2 (by norm_num) (by norm_num) tau0 witnessChannel witnessChannel
    witnessC witness_implements witness_passive
  exact witness_not_ppt (classical_ppt hc)

end D5.S3.QuantumChannels.PassiveMemoryNonclassicalRefutation
