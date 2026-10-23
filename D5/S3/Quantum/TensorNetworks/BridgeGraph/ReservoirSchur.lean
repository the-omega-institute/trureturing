/- GID: D5/S3/Quantum/TensorNetworks/BridgeGraph/ReservoirSchur
   generality: G
   mirror-B: D5/B/S3/Quantum/TensorNetworks/BridgeGraph/ReservoirSchur
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: ReservoirSchur for width-three bridge flow. -/

/-
proof_shape: kernelEmbedding_injective: bind-only; consumer: LongReservoir.long_reservoir_injective
escape_witness: kernelEmbedding_injective: none
proof_shape: kernel_coordinates: content
escape_witness: kernel_coordinates: ShiftPencilBlocks.rectangular_chain_zero
proof_shape: kernelMatrix_mulVec: bind-only; consumer: LongReservoir.single_update_injective
escape_witness: kernelMatrix_mulVec: none
proof_shape: cokernelMatrix_mul_widthTwo: bind-only; consumer: LongReservoir.single_update_injective
escape_witness: cokernelMatrix_mul_widthTwo: none
proof_shape: kernel_sample_identity: bind-only; consumer: LongReservoir.single_update_injective
escape_witness: kernel_sample_identity: none
proof_shape: cokernel_sample_identity: bind-only; consumer: LongReservoir.single_update_injective
escape_witness: cokernel_sample_identity: none
proof_shape: inclusion_prod: bind-only; consumer: LongReservoir.rectId_tensor_injective
escape_witness: inclusion_prod: none
proof_shape: singleCross_kronecker: bind-only; consumer: LongReservoir.single_reversal_injective_witness
escape_witness: singleCross_kronecker: none
proof_shape: widthTwo_mulVec_block: bind-only; consumer: LongReservoir.long_sourceSL_kernel_of_updated_zero
escape_witness: widthTwo_mulVec_block: none
proof_shape: cokernel_mulVec_formula: bind-only; consumer: LongReservoir.cokernel_long_LL
escape_witness: cokernel_mulVec_formula: none
proof_shape: slLine_kernelEmbedding: bind-only; consumer: LongReservoir.cokernel_long_kernel
escape_witness: slLine_kernelEmbedding: none
proof_shape: sourceSL_kernelEmbedding: bind-only; consumer: LongReservoir.cokernel_long_kernel
escape_witness: sourceSL_kernelEmbedding: none
proof_shape: short_short_witness: content
escape_witness: short_short_witness: ReservoirSchur.short_reservoir_injective
admission_basis: escape-witness (short_short_witness)
Module content mechanism: short_reservoir_injective: exact higher-order short-reservoir Schur reduction.
Direct frozen dependencies: none on the implementation baseline.
Utility: none; symbolic constructions and proofs for arbitrary dimensions,
not bounded enumeration, a checker, numeric reduction, or a certified instance.
Information-escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/14762
-/

import D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks

set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur
open Matrix Module

open D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound
open D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles
open D5.S3.Quantum.TensorNetworks.BridgeGraph.CyclicResolvent
open D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks
open Matrix Module
section

open Matrix Module

def kernelEmbedding (p alpha beta gamma delta : ℕ) :
    (Fin alpha × Fin delta → ℚ) →ₗ[ℚ]
      ((Σ t : Fin alpha ⊕ Fin beta, Fin (blockLength p alpha beta t + 1)) × (Σ t : Fin gamma ⊕ Fin delta, Fin (blockLength p gamma delta t)) → ℚ) where
  toFun w u := match u.1, u.2 with
    | ⟨Sum.inl i, s⟩, ⟨Sum.inr h, j⟩ => w (i, h) * antiDiagonal p (s, j)
    | _, _ => 0
  map_add' w z := by
    funext ⟨⟨i, s⟩, ⟨h, j⟩⟩
    cases i <;> cases h <;> simp [add_mul]
  map_smul' c w := by
    funext ⟨⟨i, s⟩, ⟨h, j⟩⟩
    cases i <;> cases h <;> simp [mul_assoc]

private lemma kernelEmbedding_at (p alpha beta gamma delta : ℕ)
    (w : Fin alpha × Fin delta → ℚ) (i : Fin alpha) (h : Fin delta) :
    kernelEmbedding p alpha beta gamma delta w
      (⟨Sum.inl i, ⟨0, by dsimp [blockLength]; omega⟩⟩,
       ⟨Sum.inr h, ⟨p, by dsimp [blockLength]; omega⟩⟩) = w (i, h) := by
  simp [kernelEmbedding, antiDiagonal]

theorem kernelEmbedding_injective (p alpha beta gamma delta : ℕ) :
    Function.Injective (kernelEmbedding p alpha beta gamma delta) := by
  intro w z hw
  funext ⟨i, h⟩
  have hv := congrFun hw
    (⟨Sum.inl i, ⟨0, by dsimp [blockLength]; omega⟩⟩,
     ⟨Sum.inr h, ⟨p, by dsimp [blockLength]; omega⟩⟩)
  simpa only [kernelEmbedding_at] using hv

private theorem widthTwo_kernelEmbedding (p alpha beta gamma delta : ℕ)
    (w : Fin alpha × Fin delta → ℚ) :
    (widthTwoMatrix p p alpha beta gamma delta).mulVec
      (kernelEmbedding p alpha beta gamma delta w) = 0 := by
  rw [widthTwo_block_decomposition, Matrix.submatrix_mulVec_equiv]
  funext ⟨⟨i, s⟩, ⟨h, j⟩⟩
  change (blockDiagonal' (fun t : (Fin alpha ⊕ Fin beta) × (Fin gamma ⊕ Fin delta) =>
    pencil (blockLength p alpha beta t.1) (blockLength p gamma delta t.2))).mulVec
      ((kernelEmbedding p alpha beta gamma delta w) ∘
        (tensorBlockEquiv (fun t => Fin (blockLength p alpha beta t + 1))
          (fun t => Fin (blockLength p gamma delta t))).symm)
      ⟨(i, h), (s, j)⟩ = 0
  rw [block_mulVec]
  cases i <;> cases h
  · change (pencil p p).mulVec (0 : Fin (p + 1) × Fin p → ℚ) (s, j) = 0
    simp
  · rename_i i h
    change (pencil p (p + 1)).mulVec ((w (i, h)) • antiDiagonal p) (s, j) = 0
    rw [Matrix.mulVec_smul, antiDiagonal_kernel]
    simp
  · change (pencil (p + 1) p).mulVec (0 : Fin (p + 2) × Fin p → ℚ) (s, j) = 0
    simp
  · change (pencil (p + 1) (p + 1)).mulVec (0 : Fin (p + 2) × Fin (p + 1) → ℚ) (s, j) = 0
    simp

private theorem kernelEmbedding_range (p alpha beta gamma delta : ℕ) :
    LinearMap.range (kernelEmbedding p alpha beta gamma delta) =
      LinearMap.ker (widthTwoMatrix p p alpha beta gamma delta).mulVecLin := by
  apply Submodule.eq_of_le_of_finrank_eq
  · rintro v ⟨w, rfl⟩
    exact widthTwo_kernelEmbedding p alpha beta gamma delta w
  · rw [LinearMap.finrank_range_of_inj (kernelEmbedding_injective _ _ _ _ _),
      Module.finrank_pi, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin,
      same_depth_kernel_dimension]

theorem kernel_coordinates (p alpha beta gamma delta : ℕ)
    (u : (Σ t : Fin alpha ⊕ Fin beta, Fin (blockLength p alpha beta t + 1)) × (Σ t : Fin gamma ⊕ Fin delta, Fin (blockLength p gamma delta t)) → ℚ)
    (hu : (widthTwoMatrix p p alpha beta gamma delta).mulVec u = 0) :
    ∃ w, kernelEmbedding p alpha beta gamma delta w = u := by
  change u ∈ LinearMap.range (kernelEmbedding p alpha beta gamma delta)
  rw [kernelEmbedding_range]
  exact hu

private theorem widthTwo_transpose_swap (p q alpha beta gamma delta : ℕ) :
    (widthTwoMatrix p q alpha beta gamma delta).transpose =
      (widthTwoMatrix q p gamma delta alpha beta).submatrix
        (Equiv.prodComm _ _) (Equiv.prodComm _ _) := by
  ext i j
  change arrow0 p alpha beta j.1 i.1 * arrow0 q gamma delta i.2 j.2 +
      arrow1 p alpha beta j.1 i.1 * arrow1 q gamma delta i.2 j.2 =
    arrow0 q gamma delta i.2 j.2 * arrow0 p alpha beta j.1 i.1 +
      arrow1 q gamma delta i.2 j.2 * arrow1 p alpha beta j.1 i.1
  simp only [mul_comm]

def cokernelEmbedding (p alpha beta gamma delta : ℕ) :
    (Fin beta × Fin gamma → ℚ) →ₗ[ℚ]
      ((Σ t : Fin alpha ⊕ Fin beta, Fin (blockLength p alpha beta t)) × (Σ t : Fin gamma ⊕ Fin delta, Fin (blockLength p gamma delta t + 1)) → ℚ) where
  toFun w u := match u.1, u.2 with
    | ⟨Sum.inr k, s⟩, ⟨Sum.inl j, t⟩ => w (k, j) * (antiDiagonal p ((s, t).2, (s, t).1))
    | _, _ => 0
  map_add' w z := by
    funext ⟨⟨i, s⟩, ⟨h, j⟩⟩
    cases i <;> cases h <;> simp [add_mul]
  map_smul' c w := by
    funext ⟨⟨i, s⟩, ⟨h, j⟩⟩
    cases i <;> cases h <;> simp [mul_assoc]

private lemma cokernelEmbedding_swap (p alpha beta gamma delta : ℕ)
    (w : Fin beta × Fin gamma → ℚ) :
    cokernelEmbedding p alpha beta gamma delta w =
      (kernelEmbedding p gamma delta alpha beta (fun k => w (k.2, k.1))) ∘
        (Equiv.prodComm _ _) := by
  funext ⟨⟨i, s⟩, ⟨h, j⟩⟩
  cases i <;> cases h <;> rfl

private theorem widthTwo_cokernelEmbedding (p alpha beta gamma delta : ℕ)
    (w : Fin beta × Fin gamma → ℚ) :
    (widthTwoMatrix p p alpha beta gamma delta).transpose.mulVec
      (cokernelEmbedding p alpha beta gamma delta w) = 0 := by
  rw [cokernelEmbedding_swap, widthTwo_transpose_swap, Matrix.submatrix_mulVec_equiv]
  change ((widthTwoMatrix p p gamma delta alpha beta).mulVec
    (kernelEmbedding p gamma delta alpha beta (fun k => w (k.2, k.1)))) ∘
      (Equiv.prodComm _ _) = 0
  rw [widthTwo_kernelEmbedding]
  rfl

end
section

open Matrix Module

lemma kernelMatrix_mulVec (p alpha beta gamma delta : ℕ) (w : Fin alpha × Fin delta → ℚ) :
    ((LinearMap.toMatrix' (kernelEmbedding p alpha beta gamma delta))).mulVec w =
      kernelEmbedding p alpha beta gamma delta w := LinearMap.toMatrix'_mulVec _ _

lemma cokernelMatrix_mul_widthTwo (p alpha beta gamma delta : ℕ) :
    (LinearMap.toMatrix' (cokernelEmbedding p alpha beta gamma delta)).transpose * widthTwoMatrix p p alpha beta gamma delta = 0 := by
  have h : (widthTwoMatrix p p alpha beta gamma delta).transpose *
      (LinearMap.toMatrix' (cokernelEmbedding p alpha beta gamma delta)) = 0 := by
    ext i j
    change (widthTwoMatrix p p alpha beta gamma delta).transpose.mulVec
      (cokernelEmbedding p alpha beta gamma delta (Pi.single j 1)) i = 0
    rw [widthTwo_cokernelEmbedding]
    rfl
  have ht := congrArg Matrix.transpose h
  simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero] using ht

private lemma mul_inclusion {m n s : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix m n ℚ) (e : s → n) : A * inclusion e = A.submatrix id e := by
  classical
  ext i j
  change (∑ k, A i k * (if k = e j then (1 : ℚ) else 0)) = A i (e j)
  simp

private lemma observation_mul {m n s : Type*} [Fintype m] [DecidableEq m]
    (e : s → m) (A : Matrix m n ℚ) : (inclusion e).transpose * A = A.submatrix e id := by
  classical
  ext i j
  change (∑ k, (if k = e i then (1 : ℚ) else 0) * A k j) = A (e i) j
  simp

def kernelSample (p alpha beta gamma delta : ℕ) (t : Fin alpha × Fin delta) :
    (Σ t : Fin alpha ⊕ Fin beta, Fin (blockLength p alpha beta t + 1)) × (Σ t : Fin gamma ⊕ Fin delta, Fin (blockLength p gamma delta t)) :=
  (⟨Sum.inl t.1, ⟨0, by dsimp [blockLength]; omega⟩⟩,
    ⟨Sum.inr t.2, ⟨p, by dsimp [blockLength]; omega⟩⟩)

def cokernelSample (p alpha beta gamma delta : ℕ) (t : Fin beta × Fin gamma) :
    (Σ t : Fin alpha ⊕ Fin beta, Fin (blockLength p alpha beta t)) × (Σ t : Fin gamma ⊕ Fin delta, Fin (blockLength p gamma delta t + 1)) :=
  (⟨Sum.inr t.1, ⟨p, by dsimp [blockLength]; omega⟩⟩,
    ⟨Sum.inl t.2, ⟨0, by dsimp [blockLength]; omega⟩⟩)

lemma kernel_sample_identity (p alpha beta gamma delta : ℕ) :
    (inclusion (kernelSample p alpha beta gamma delta)).transpose *
      (LinearMap.toMatrix' (kernelEmbedding p alpha beta gamma delta)) = 1 := by
  rw [observation_mul]
  ext i j
  change kernelEmbedding p alpha beta gamma delta (Pi.single j 1)
      (kernelSample p alpha beta gamma delta i) = _
  simp [kernelSample, kernelEmbedding, antiDiagonal, Matrix.one_apply, Pi.single_apply, eq_comm]

lemma cokernel_sample_identity (p alpha beta gamma delta : ℕ) :
    (LinearMap.toMatrix' (cokernelEmbedding p alpha beta gamma delta)).transpose *
      inclusion (cokernelSample p alpha beta gamma delta) = 1 := by
  rw [mul_inclusion]
  ext i j
  change cokernelEmbedding p alpha beta gamma delta (Pi.single i 1)
      (cokernelSample p alpha beta gamma delta j) = _
  simp [cokernelSample, cokernelEmbedding,  antiDiagonal,
    Matrix.one_apply, Pi.single_apply, eq_comm]

noncomputable def singleCross (p alpha beta gamma delta : ℕ)
    (BM : Matrix (Fin beta) (Fin alpha) ℚ) (DM : Matrix (Fin gamma) (Fin delta) ℚ) :=
  inclusion (cokernelSample p alpha beta gamma delta) * kronecker BM DM *
    (inclusion (kernelSample p alpha beta gamma delta)).transpose

lemma inclusion_prod {m n r s : Type*} [DecidableEq m] [DecidableEq r]
    (e : n → m) (f : s → r) :
    inclusion (fun k : n × s => (e k.1, f k.2)) = kronecker (inclusion e) (inclusion f) := by
  ext i j
  change (if i = (e j.1, f j.2) then (1 : ℚ) else 0) =
    (if i.1 = e j.1 then 1 else 0) * (if i.2 = f j.2 then 1 else 0)
  simp only [Prod.ext_iff]
  split_ifs <;> simp_all

private lemma observation_prod {m n r s : Type*} [DecidableEq m] [DecidableEq r]
    (e : n → m) (f : s → r) :
    (inclusion (fun k : n × s => (e k.1, f k.2))).transpose =
      kronecker ((inclusion e).transpose) ((inclusion f).transpose) := by
  have h := congrArg Matrix.transpose (inclusion_prod e f)
  exact h

def shortZeroCol (p alpha beta : ℕ) (i : Fin alpha) : (Σ t : Fin alpha ⊕ Fin beta, Fin (blockLength p alpha beta t + 1)) :=
  ⟨Sum.inl i, ⟨0, by dsimp [blockLength]; omega⟩⟩

def longLastRow (p alpha beta : ℕ) (k : Fin beta) : (Σ t : Fin alpha ⊕ Fin beta, Fin (blockLength p alpha beta t)) :=
  ⟨Sum.inr k, ⟨p, by dsimp [blockLength]; omega⟩⟩


noncomputable def singleThirdLeft (p alpha beta : ℕ) (BM : Matrix (Fin beta) (Fin alpha) ℚ) :
    Matrix ((Σ t : Fin alpha ⊕ Fin beta, Fin (blockLength p alpha beta t))) ((Σ t : Fin alpha ⊕ Fin beta, Fin (blockLength p alpha beta t + 1))) ℚ :=
  inclusion (longLastRow p alpha beta) * BM * (inclusion (shortZeroCol p alpha beta)).transpose

noncomputable def singleThirdRight (p gamma delta : ℕ) (DM : Matrix (Fin gamma) (Fin delta) ℚ) :
    Matrix ((Σ t : Fin gamma ⊕ Fin delta, Fin (blockLength p gamma delta t + 1))) ((Σ t : Fin gamma ⊕ Fin delta, Fin (blockLength p gamma delta t))) ℚ :=
  inclusion (shortZeroCol p gamma delta) * DM * (inclusion (longLastRow p gamma delta)).transpose

theorem singleCross_kronecker (p alpha beta gamma delta : ℕ)
    (BM : Matrix (Fin beta) (Fin alpha) ℚ) (DM : Matrix (Fin gamma) (Fin delta) ℚ) :
    singleCross p alpha beta gamma delta BM DM =
      kronecker (singleThirdLeft p alpha beta BM) (singleThirdRight p gamma delta DM) := by
  have hk : kernelSample p alpha beta gamma delta =
      fun k : Fin alpha × Fin delta => (shortZeroCol p alpha beta k.1, longLastRow p gamma delta k.2) := rfl
  have hc : cokernelSample p alpha beta gamma delta =
      fun k : Fin beta × Fin gamma => (longLastRow p alpha beta k.1, shortZeroCol p gamma delta k.2) := rfl
  dsimp only [singleCross, singleThirdLeft, singleThirdRight]
  rw [hk, hc, inclusion_prod, observation_prod]
  exact (congrArg (fun Z => Z * kronecker ((inclusion (shortZeroCol p alpha beta)).transpose)
      ((inclusion (longLastRow p gamma delta)).transpose))
    (Matrix.mul_kronecker_mul (inclusion (longLastRow p alpha beta)) BM
      (inclusion (shortZeroCol p gamma delta)) DM).symm).trans
    (Matrix.mul_kronecker_mul (inclusion (longLastRow p alpha beta) * BM)
      ((inclusion (shortZeroCol p alpha beta)).transpose)
      (inclusion (shortZeroCol p gamma delta) * DM)
      ((inclusion (longLastRow p gamma delta)).transpose)).symm

end
section

open Matrix Module

private def reservoirThirdLeft (p alpha beta : ℕ)
    (X : Matrix (Fin alpha) (Fin alpha) ℚ) (BM : Matrix (Fin beta) (Fin alpha) ℚ) :
    Matrix ((Σ t : Fin alpha ⊕ Fin beta, Fin (blockLength p alpha beta t))) ((Σ t : Fin alpha ⊕ Fin beta, Fin (blockLength p alpha beta t + 1))) ℚ := fun r s =>
  match r, s with
  | ⟨Sum.inl i, u⟩, ⟨Sum.inl j, v⟩ => if u.val = 0 ∧ v.val = 0 then X i j else 0
  | ⟨Sum.inr k, u⟩, ⟨Sum.inl i, v⟩ => if u.val + v.val = p then BM k i else 0
  | _, _ => 0

private def reservoirThirdRight (p gamma delta : ℕ)
    (Y : Matrix (Fin gamma) (Fin gamma) ℚ) (DM : Matrix (Fin gamma) (Fin delta) ℚ) :
    Matrix ((Σ t : Fin gamma ⊕ Fin delta, Fin (blockLength p gamma delta t + 1))) ((Σ t : Fin gamma ⊕ Fin delta, Fin (blockLength p gamma delta t))) ℚ := fun r s =>
  match r, s with
  | ⟨Sum.inl j, u⟩, ⟨Sum.inl k, v⟩ => if u.val = 0 ∧ v.val = 0 then Y j k else 0
  | ⟨Sum.inl j, u⟩, ⟨Sum.inr h, v⟩ => if u.val + v.val = p then DM j h else 0
  | _, _ => 0

private def reservoirCross (p alpha beta gamma delta : ℕ)
    (X : Matrix (Fin alpha) (Fin alpha) ℚ) (Y : Matrix (Fin gamma) (Fin gamma) ℚ)
    (BM : Matrix (Fin beta) (Fin alpha) ℚ) (DM : Matrix (Fin gamma) (Fin delta) ℚ) :=
  kronecker (reservoirThirdLeft p alpha beta X BM) (reservoirThirdRight p gamma delta Y DM)

def localSource (p q alpha beta gamma delta : ℕ)
    (u : (Σ t : Fin alpha ⊕ Fin beta, Fin (blockLength p alpha beta t + 1)) × (Σ t : Fin gamma ⊕ Fin delta, Fin (blockLength q gamma delta t)) → ℚ)
    (i : (Fin alpha ⊕ Fin beta)) (j : (Fin gamma ⊕ Fin delta)) :
    Fin (blockLength p alpha beta i + 1) × Fin (blockLength q gamma delta j) → ℚ :=
  fun k => u (⟨i, k.1⟩, ⟨j, k.2⟩)

lemma widthTwo_mulVec_block (p q alpha beta gamma delta : ℕ)
    (u : (Σ t : Fin alpha ⊕ Fin beta, Fin (blockLength p alpha beta t + 1)) × (Σ t : Fin gamma ⊕ Fin delta, Fin (blockLength q gamma delta t)) → ℚ)
    (i : (Fin alpha ⊕ Fin beta)) (j : (Fin gamma ⊕ Fin delta))
    (s : Fin (blockLength p alpha beta i)) (t : Fin (blockLength q gamma delta j + 1)) :
    (widthTwoMatrix p q alpha beta gamma delta).mulVec u (⟨i, s⟩, ⟨j, t⟩) =
      (pencil (blockLength p alpha beta i) (blockLength q gamma delta j)).mulVec
        (localSource p q alpha beta gamma delta u i j) (s, t) := by
  rw [widthTwo_block_decomposition, Matrix.submatrix_mulVec_equiv]
  change (blockDiagonal' (fun k : (Fin alpha ⊕ Fin beta) × (Fin gamma ⊕ Fin delta) =>
      pencil (blockLength p alpha beta k.1) (blockLength q gamma delta k.2))).mulVec
    (u ∘ (tensorBlockEquiv (fun t => Fin (blockLength p alpha beta t + 1))
      (fun t => Fin (blockLength q gamma delta t))).symm) ⟨(i, j), (s, t)⟩ = _
  rw [block_mulVec]
  rfl

private def sourceSS (p alpha beta gamma delta : ℕ)
    (u : (Σ t : Fin alpha ⊕ Fin beta, Fin (blockLength p alpha beta t + 1)) × (Σ t : Fin gamma ⊕ Fin delta, Fin (blockLength p gamma delta t)) → ℚ) :
    (Σ t : Fin alpha ⊕ Fin beta, Fin (blockLength p alpha beta t + 1)) × (Σ t : Fin gamma ⊕ Fin delta, Fin (blockLength p gamma delta t)) → ℚ := fun k =>
  match k.1.1, k.2.1 with
  | Sum.inl _, Sum.inl _ => u k
  | _, _ => 0

def sourceSL (p alpha beta gamma delta : ℕ)
    (u : (Σ t : Fin alpha ⊕ Fin beta, Fin (blockLength p alpha beta t + 1)) × (Σ t : Fin gamma ⊕ Fin delta, Fin (blockLength p gamma delta t)) → ℚ) :
    (Σ t : Fin alpha ⊕ Fin beta, Fin (blockLength p alpha beta t + 1)) × (Σ t : Fin gamma ⊕ Fin delta, Fin (blockLength p gamma delta t)) → ℚ := fun k =>
  match k.1.1, k.2.1 with
  | Sum.inl _, Sum.inr _ => u k
  | _, _ => 0

private lemma reservoirThirdLeft_long_column (p alpha beta : ℕ)
    (X : Matrix (Fin alpha) (Fin alpha) ℚ) (BM : Matrix (Fin beta) (Fin alpha) ℚ)
    (r : (Σ t : Fin alpha ⊕ Fin beta, Fin (blockLength p alpha beta t))) (j : Fin beta) (s : Fin (p + 2)) :
    reservoirThirdLeft p alpha beta X BM r ⟨Sum.inr j, s⟩ = 0 := by
  rcases r with ⟨i, u⟩
  cases i <;> rfl

private lemma reservoirThirdRight_long_row (p gamma delta : ℕ)
    (Y : Matrix (Fin gamma) (Fin gamma) ℚ) (DM : Matrix (Fin gamma) (Fin delta) ℚ)
    (j : Fin delta) (s : Fin (p + 2)) (c : (Σ t : Fin gamma ⊕ Fin delta, Fin (blockLength p gamma delta t))) :
    reservoirThirdRight p gamma delta Y DM ⟨Sum.inr j, s⟩ c = 0 := by
  rcases c with ⟨i, u⟩
  cases i <;> rfl

private lemma reservoirCross_long_output (p alpha beta gamma delta : ℕ)
    (X : Matrix (Fin alpha) (Fin alpha) ℚ) (Y : Matrix (Fin gamma) (Fin gamma) ℚ)
    (BM : Matrix (Fin beta) (Fin alpha) ℚ) (DM : Matrix (Fin gamma) (Fin delta) ℚ)
    (u : (Σ t : Fin alpha ⊕ Fin beta, Fin (blockLength p alpha beta t + 1)) × (Σ t : Fin gamma ⊕ Fin delta, Fin (blockLength p gamma delta t)) → ℚ)
    (r : (Σ t : Fin alpha ⊕ Fin beta, Fin (blockLength p alpha beta t))) (h : Fin delta) (t : Fin (p + 2)) :
    (reservoirCross p alpha beta gamma delta X Y BM DM).mulVec u (r, ⟨Sum.inr h, t⟩) = 0 := by
  apply Finset.sum_eq_zero
  intro k _
  change reservoirThirdLeft p alpha beta X BM r k.1 *
    reservoirThirdRight p gamma delta Y DM ⟨Sum.inr h, t⟩ k.2 * u k = 0
  rw [reservoirThirdRight_long_row, mul_zero, zero_mul]

private lemma reservoirCross_source_decomposition (p alpha beta gamma delta : ℕ)
    (X : Matrix (Fin alpha) (Fin alpha) ℚ) (Y : Matrix (Fin gamma) (Fin gamma) ℚ)
    (BM : Matrix (Fin beta) (Fin alpha) ℚ) (DM : Matrix (Fin gamma) (Fin delta) ℚ)
    (u : (Σ t : Fin alpha ⊕ Fin beta, Fin (blockLength p alpha beta t + 1)) × (Σ t : Fin gamma ⊕ Fin delta, Fin (blockLength p gamma delta t)) → ℚ) :
    (reservoirCross p alpha beta gamma delta X Y BM DM).mulVec u =
      (reservoirCross p alpha beta gamma delta X Y BM DM).mulVec (sourceSS p alpha beta gamma delta u) +
      (reservoirCross p alpha beta gamma delta X Y BM DM).mulVec (sourceSL p alpha beta gamma delta u) := by
  rw [← Matrix.mulVec_add]
  funext r
  apply Finset.sum_congr rfl
  rintro ⟨⟨i, s⟩, ⟨j, t⟩⟩ _
  cases i <;> cases j
  · simp [sourceSS, sourceSL]
  · simp [sourceSS, sourceSL]
  · change reservoirThirdLeft p alpha beta X BM r.1 ⟨Sum.inr _, s⟩ *
      reservoirThirdRight p gamma delta Y DM r.2 ⟨Sum.inl _, t⟩ * _ = _
    rw [reservoirThirdLeft_long_column, zero_mul, zero_mul]
    simp [sourceSS, sourceSL]
  · change reservoirThirdLeft p alpha beta X BM r.1 ⟨Sum.inr _, s⟩ *
      reservoirThirdRight p gamma delta Y DM r.2 ⟨Sum.inr _, t⟩ * _ = _
    rw [reservoirThirdLeft_long_column, zero_mul, zero_mul]
    simp [sourceSS, sourceSL]

private theorem sourceSL_kernel_of_updated_zero (p alpha beta gamma delta : ℕ)
    (X : Matrix (Fin alpha) (Fin alpha) ℚ) (Y : Matrix (Fin gamma) (Fin gamma) ℚ)
    (BM : Matrix (Fin beta) (Fin alpha) ℚ) (DM : Matrix (Fin gamma) (Fin delta) ℚ)
    (u : (Σ t : Fin alpha ⊕ Fin beta, Fin (blockLength p alpha beta t + 1)) × (Σ t : Fin gamma ⊕ Fin delta, Fin (blockLength p gamma delta t)) → ℚ)
    (hu : (widthTwoMatrix p p alpha beta gamma delta +
      reservoirCross p alpha beta gamma delta X Y BM DM).mulVec u = 0) :
    (widthTwoMatrix p p alpha beta gamma delta).mulVec (sourceSL p alpha beta gamma delta u) = 0 := by
  funext ⟨⟨i, s⟩, ⟨j, t⟩⟩
  rw [widthTwo_mulVec_block]
  cases i <;> cases j
  · change (pencil p p).mulVec (0 : Fin (p + 1) × Fin p → ℚ) (s, t) = 0
    simp
  · rename_i i j
    have hh := congrFun hu (⟨Sum.inl i, s⟩, ⟨Sum.inr j, t⟩)
    rw [Matrix.add_mulVec] at hh
    simp only [Pi.add_apply, reservoirCross_long_output, add_zero, Pi.zero_apply,
      widthTwo_mulVec_block] at hh
    exact hh
  · change (pencil (p + 1) p).mulVec (0 : Fin (p + 2) × Fin p → ℚ) (s, t) = 0
    simp
  · change (pencil (p + 1) (p + 1)).mulVec (0 : Fin (p + 2) × Fin (p + 1) → ℚ) (s, t) = 0
    simp

private theorem sourceSS_kernel_of_rows_zero (p alpha beta gamma delta : ℕ)
    (u : (Σ t : Fin alpha ⊕ Fin beta, Fin (blockLength p alpha beta t + 1)) × (Σ t : Fin gamma ⊕ Fin delta, Fin (blockLength p gamma delta t)) → ℚ)
    (hu : ∀ i : Fin alpha, ∀ j : Fin gamma, ∀ s : Fin p, ∀ t : Fin (p + 1),
      (widthTwoMatrix p p alpha beta gamma delta).mulVec u (⟨Sum.inl i, s⟩, ⟨Sum.inl j, t⟩) = 0) :
    (widthTwoMatrix p p alpha beta gamma delta).mulVec (sourceSS p alpha beta gamma delta u) = 0 := by
  funext ⟨⟨i, s⟩, ⟨j, t⟩⟩
  rw [widthTwo_mulVec_block]
  cases i <;> cases j
  · rename_i i j
    have hh := hu i j s t
    rw [widthTwo_mulVec_block] at hh
    exact hh
  · change (pencil p (p + 1)).mulVec (0 : Fin (p + 1) × Fin (p + 1) → ℚ) (s, t) = 0
    simp
  · change (pencil (p + 1) p).mulVec (0 : Fin (p + 2) × Fin p → ℚ) (s, t) = 0
    simp
  · change (pencil (p + 1) (p + 1)).mulVec (0 : Fin (p + 2) × Fin (p + 1) → ℚ) (s, t) = 0
    simp

private theorem sourceSS_zero_of_kernel (p alpha beta gamma delta : ℕ)
    (u : (Σ t : Fin alpha ⊕ Fin beta, Fin (blockLength p alpha beta t + 1)) × (Σ t : Fin gamma ⊕ Fin delta, Fin (blockLength p gamma delta t)) → ℚ)
    (hu : (widthTwoMatrix p p alpha beta gamma delta).mulVec (sourceSS p alpha beta gamma delta u) = 0) :
    sourceSS p alpha beta gamma delta u = 0 := by
  obtain ⟨w, hw⟩ := kernel_coordinates p alpha beta gamma delta _ hu
  have hw0 : w = 0 := by
    funext ⟨i, h⟩
    have hh := congrFun hw (⟨Sum.inl i, ⟨0, by dsimp [blockLength]; omega⟩⟩,
      ⟨Sum.inr h, ⟨p, by dsimp [blockLength]; omega⟩⟩)
    simpa [kernelEmbedding, antiDiagonal, sourceSS] using hh
  rw [← hw, hw0, map_zero]

private def ssSource (p alpha beta gamma delta : ℕ) (hp : 0 < p) (k : Fin alpha × Fin gamma) :
    (Σ t : Fin alpha ⊕ Fin beta, Fin (blockLength p alpha beta t + 1)) × (Σ t : Fin gamma ⊕ Fin delta, Fin (blockLength p gamma delta t)) :=
  (⟨Sum.inl k.1, ⟨0, by dsimp [blockLength]; omega⟩⟩,
    ⟨Sum.inl k.2, ⟨0, by dsimp [blockLength]; omega⟩⟩)

private def ssTarget (p alpha beta gamma delta : ℕ) (hp : 0 < p) (k : Fin alpha × Fin gamma) :
    (Σ t : Fin alpha ⊕ Fin beta, Fin (blockLength p alpha beta t)) × (Σ t : Fin gamma ⊕ Fin delta, Fin (blockLength p gamma delta t + 1)) :=
  (⟨Sum.inl k.1, ⟨0, by dsimp [blockLength]; omega⟩⟩,
    ⟨Sum.inl k.2, ⟨0, by dsimp [blockLength]; omega⟩⟩)

private theorem old_reservoir_sample (p alpha beta gamma delta : ℕ) (hp : 0 < p)
    (u : (Σ t : Fin alpha ⊕ Fin beta, Fin (blockLength p alpha beta t + 1)) × (Σ t : Fin gamma ⊕ Fin delta, Fin (blockLength p gamma delta t)) → ℚ) (k : Fin alpha × Fin gamma) :
    (widthTwoMatrix p p alpha beta gamma delta).mulVec u
      (ssTarget p alpha beta gamma delta hp k) = u (ssSource p alpha beta gamma delta hp k) := by
  rw [ssTarget, widthTwo_mulVec_block, pencil_mulVec]
  simp [rectExtend, hp, blockLength, localSource, ssSource]

end
section

open Matrix Module

private def ssLine (p alpha beta gamma delta : ℕ) (hp : 0 < p)
    (u : (Σ t : Fin alpha ⊕ Fin beta, Fin (blockLength p alpha beta t + 1)) × (Σ t : Fin gamma ⊕ Fin delta, Fin (blockLength p gamma delta t)) → ℚ) (r : Fin (p + 1)) :
    Fin alpha × Fin gamma → ℚ := fun k =>
  u (⟨Sum.inl k.1, ⟨p - r.val, by dsimp [blockLength]; omega⟩⟩,
    ⟨Sum.inl k.2, ⟨0, by dsimp [blockLength]; omega⟩⟩)

def slLine (p alpha beta gamma delta : ℕ)
    (u : (Σ t : Fin alpha ⊕ Fin beta, Fin (blockLength p alpha beta t + 1)) × (Σ t : Fin gamma ⊕ Fin delta, Fin (blockLength p gamma delta t)) → ℚ) (r t : Fin (p + 1)) :
    Fin alpha × Fin delta → ℚ := fun k =>
  u (⟨Sum.inl k.1, ⟨p - r.val, by dsimp [blockLength]; omega⟩⟩,
    ⟨Sum.inr k.2, ⟨p - t.val, by dsimp [blockLength]; omega⟩⟩)

private lemma reservoirCross_SS_long_row (p alpha beta gamma delta : ℕ) (hp : 0 < p)
    (X : Matrix (Fin alpha) (Fin alpha) ℚ) (Y : Matrix (Fin gamma) (Fin gamma) ℚ)
    (BM : Matrix (Fin beta) (Fin alpha) ℚ) (DM : Matrix (Fin gamma) (Fin delta) ℚ)
    (u : (Σ t : Fin alpha ⊕ Fin beta, Fin (blockLength p alpha beta t + 1)) × (Σ t : Fin gamma ⊕ Fin delta, Fin (blockLength p gamma delta t)) → ℚ)
    (k : Fin beta) (j : Fin gamma) (r t : Fin (p + 1)) :
    (reservoirCross p alpha beta gamma delta X Y BM DM).mulVec
      (sourceSS p alpha beta gamma delta u) (⟨Sum.inr k, r⟩, ⟨Sum.inl j, t⟩) =
      if t.val = 0 then (kronecker BM Y).mulVec (ssLine p alpha beta gamma delta hp u r) (k, j) else 0 := by
  classical
  have hr (s : Fin (p + 1)) : r.val + s.val = p ↔ s.val = p - r.val := by
    have h := r.isLt
    omega
  simp only [reservoirCross, Matrix.mulVec, dotProduct, Matrix.kronecker, Matrix.kroneckerMap,
    Matrix.of_apply, Fintype.sum_prod_type, Fintype.sum_sigma, Fintype.sum_sum_type,
    reservoirThirdLeft, reservoirThirdRight, sourceSS, blockLength, Sum.elim_inl, Sum.elim_inr,
    mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
  simp_rw [hr]
  by_cases ht : t.val = 0
  · simp only [ht, true_and, if_pos]
    calc
      _ = ∑ i : Fin alpha, ∑ h : Fin gamma, ∑ s : Fin (p + 1), ∑ v : Fin p,
        (if s.val = p - r.val then BM k i else 0) * (if v.val = 0 then Y j h else 0) *
          u (⟨Sum.inl i, s⟩, ⟨Sum.inl h, v⟩) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro h _
        have hpr : p - r.val < p + 1 := by omega
        exact (double_fin_pick (p+1) p (p-r.val) 0 (BM k i) (Y j h)
          (fun z => u (⟨Sum.inl i, z.1⟩, ⟨Sum.inl h, z.2⟩))).trans
          (by simp [rectExtend, hp, hpr, ssLine])
  · simp [ht]

private lemma reservoirCross_SL_long_row (p alpha beta gamma delta : ℕ)
    (X : Matrix (Fin alpha) (Fin alpha) ℚ) (Y : Matrix (Fin gamma) (Fin gamma) ℚ)
    (BM : Matrix (Fin beta) (Fin alpha) ℚ) (DM : Matrix (Fin gamma) (Fin delta) ℚ)
    (u : (Σ t : Fin alpha ⊕ Fin beta, Fin (blockLength p alpha beta t + 1)) × (Σ t : Fin gamma ⊕ Fin delta, Fin (blockLength p gamma delta t)) → ℚ)
    (k : Fin beta) (j : Fin gamma) (r t : Fin (p + 1)) :
    (reservoirCross p alpha beta gamma delta X Y BM DM).mulVec
      (sourceSL p alpha beta gamma delta u) (⟨Sum.inr k, r⟩, ⟨Sum.inl j, t⟩) =
      (kronecker BM DM).mulVec (slLine p alpha beta gamma delta u r t) (k, j) := by
  classical
  have hr (s : Fin (p + 1)) : r.val + s.val = p ↔ s.val = p - r.val := by
    have h := r.isLt
    omega
  have ht (s : Fin (p + 1)) : t.val + s.val = p ↔ s.val = p - t.val := by
    have h := t.isLt
    omega
  simp only [reservoirCross, Matrix.mulVec, dotProduct, Matrix.kronecker, Matrix.kroneckerMap,
    Matrix.of_apply, Fintype.sum_prod_type, Fintype.sum_sigma, Fintype.sum_sum_type,
    reservoirThirdLeft, reservoirThirdRight, sourceSL, blockLength, Sum.elim_inl, Sum.elim_inr,
    mul_zero, zero_mul, Finset.sum_const_zero, zero_add, add_zero]
  simp_rw [hr, ht]
  calc
    _ = ∑ i : Fin alpha, ∑ h : Fin delta, ∑ s : Fin (p + 1), ∑ v : Fin (p + 1),
      (if s.val = p - r.val then BM k i else 0) * (if v.val = p - t.val then DM j h else 0) *
        u (⟨Sum.inl i, s⟩, ⟨Sum.inr h, v⟩) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro h _
      have hpr : p - r.val < p + 1 := by omega
      have hpt : p - t.val < p + 1 := by omega
      exact (double_fin_pick (p+1) (p+1) (p-r.val) (p-t.val) (BM k i) (DM j h)
        (fun z => u (⟨Sum.inl i, z.1⟩, ⟨Sum.inr h, z.2⟩))).trans
        (by simp [rectExtend, hpr, hpt, slLine])

private lemma reservoirCross_SS_short_row (p alpha beta gamma delta : ℕ) (hp : 0 < p)
    (X : Matrix (Fin alpha) (Fin alpha) ℚ) (Y : Matrix (Fin gamma) (Fin gamma) ℚ)
    (BM : Matrix (Fin beta) (Fin alpha) ℚ) (DM : Matrix (Fin gamma) (Fin delta) ℚ)
    (u : (Σ t : Fin alpha ⊕ Fin beta, Fin (blockLength p alpha beta t + 1)) × (Σ t : Fin gamma ⊕ Fin delta, Fin (blockLength p gamma delta t)) → ℚ)
    (i : Fin alpha) (j : Fin gamma) (r : Fin p) (t : Fin (p + 1)) :
    (reservoirCross p alpha beta gamma delta X Y BM DM).mulVec
      (sourceSS p alpha beta gamma delta u) (⟨Sum.inl i, r⟩, ⟨Sum.inl j, t⟩) =
      if r.val = 0 ∧ t.val = 0 then
        (kronecker X Y).mulVec (fun k => u (ssSource p alpha beta gamma delta hp k)) (i, j) else 0 := by
  classical
  simp only [reservoirCross, Matrix.mulVec, dotProduct, Matrix.kronecker, Matrix.kroneckerMap,
    Matrix.of_apply, Fintype.sum_prod_type, Fintype.sum_sigma, Fintype.sum_sum_type,
    reservoirThirdLeft, reservoirThirdRight, sourceSS, blockLength, Sum.elim_inl, Sum.elim_inr,
    mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
  by_cases hr : r.val = 0 <;> by_cases ht : t.val = 0
  · simp only [hr, ht, true_and, if_pos]
    calc
      _ = ∑ k : Fin alpha, ∑ h : Fin gamma, ∑ s : Fin (p + 1), ∑ v : Fin p,
        (if s.val = 0 then X i k else 0) * (if v.val = 0 then Y j h else 0) *
          u (⟨Sum.inl k, s⟩, ⟨Sum.inl h, v⟩) := by
        apply Finset.sum_congr rfl
        intro k _
        rw [Finset.sum_comm]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro k _
        apply Finset.sum_congr rfl
        intro h _
        exact (double_fin_pick (p+1) p 0 0 (X i k) (Y j h)
          (fun z => u (⟨Sum.inl k, z.1⟩, ⟨Sum.inl h, z.2⟩))).trans
          (by simp [rectExtend, hp, ssSource])
  · simp [hr, ht]
  · simp [hr, ht]
  · simp [hr, ht]

private lemma reservoirCross_SL_short_row (p alpha beta gamma delta : ℕ)
    (X : Matrix (Fin alpha) (Fin alpha) ℚ) (Y : Matrix (Fin gamma) (Fin gamma) ℚ)
    (BM : Matrix (Fin beta) (Fin alpha) ℚ) (DM : Matrix (Fin gamma) (Fin delta) ℚ)
    (u : (Σ t : Fin alpha ⊕ Fin beta, Fin (blockLength p alpha beta t + 1)) × (Σ t : Fin gamma ⊕ Fin delta, Fin (blockLength p gamma delta t)) → ℚ)
    (i : Fin alpha) (j : Fin gamma) (r : Fin p) (t : Fin (p + 1)) :
    (reservoirCross p alpha beta gamma delta X Y BM DM).mulVec
      (sourceSL p alpha beta gamma delta u) (⟨Sum.inl i, r⟩, ⟨Sum.inl j, t⟩) =
      if r.val = 0 then
        (kronecker X DM).mulVec (fun k => u
          (⟨Sum.inl k.1, ⟨0, by dsimp [blockLength]; omega⟩⟩,
            ⟨Sum.inr k.2, ⟨p - t.val, by dsimp [blockLength]; omega⟩⟩)) (i, j) else 0 := by
  classical
  have ht (s : Fin (p + 1)) : t.val + s.val = p ↔ s.val = p - t.val := by
    have h := t.isLt
    omega
  simp only [reservoirCross, Matrix.mulVec, dotProduct, Matrix.kronecker, Matrix.kroneckerMap,
    Matrix.of_apply, Fintype.sum_prod_type, Fintype.sum_sigma, Fintype.sum_sum_type,
    reservoirThirdLeft, reservoirThirdRight, sourceSL, blockLength, Sum.elim_inl, Sum.elim_inr,
    mul_zero, zero_mul, Finset.sum_const_zero, zero_add, add_zero]
  simp_rw [ht]
  by_cases hr : r.val = 0
  · simp only [hr, true_and, if_pos]
    calc
      _ = ∑ k : Fin alpha, ∑ h : Fin delta, ∑ s : Fin (p + 1), ∑ v : Fin (p + 1),
        (if s.val = 0 then X i k else 0) * (if v.val = p - t.val then DM j h else 0) *
          u (⟨Sum.inl k, s⟩, ⟨Sum.inr h, v⟩) := by
        apply Finset.sum_congr rfl
        intro k _
        rw [Finset.sum_comm]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro k _
        apply Finset.sum_congr rfl
        intro h _
        have hpt : p - t.val < p + 1 := by omega
        exact (double_fin_pick (p+1) (p+1) 0 (p-t.val) (X i k) (DM j h)
          (fun z => u (⟨Sum.inl k, z.1⟩, ⟨Sum.inr h, z.2⟩))).trans
          (by simp [rectExtend, hpt])
  · simp [hr]

end
section

open Matrix Module

private lemma fin_pick (n r : ℕ) (a : ℚ) (u : Fin n → ℚ) (hr : r < n) :
    (∑ i : Fin n, (if i.val = r then a else 0) * u i) = a * u ⟨r, hr⟩ := by
  classical
  have he (i : Fin n) : i.val = r ↔ i = ⟨r, hr⟩ := by simp only [Fin.ext_iff]
  simp_rw [he]
  simp [ite_mul]

lemma cokernel_mulVec_formula (p alpha beta gamma delta : ℕ)
    (z : (Σ t : Fin alpha ⊕ Fin beta, Fin (blockLength p alpha beta t)) × (Σ t : Fin gamma ⊕ Fin delta, Fin (blockLength p gamma delta t + 1)) → ℚ) (k : Fin beta) (j : Fin gamma) :
    ((LinearMap.toMatrix' (cokernelEmbedding p alpha beta gamma delta)).transpose).mulVec z (k,j) =
      ∑ t : Fin (p+1), (-1 : ℚ)^t.val *
        z (⟨Sum.inr k, ⟨p-t.val, by dsimp [blockLength]; omega⟩⟩, ⟨Sum.inl j,t⟩) := by
  classical
  change (∑ v : (Σ t : Fin alpha ⊕ Fin beta, Fin (blockLength p alpha beta t)) × (Σ t : Fin gamma ⊕ Fin delta, Fin (blockLength p gamma delta t + 1)),
    (match v.1, v.2 with
    | ⟨Sum.inr k',s⟩, ⟨Sum.inl j',t⟩ =>
      (Pi.single (k,j) (1 : ℚ) : Fin beta × Fin gamma → ℚ) (k',j') * (antiDiagonal p ((s,t).2, (s,t).1))
    | _,_ => 0) * z v) = _
  simp only [Fintype.sum_prod_type, Fintype.sum_sigma, Fintype.sum_sum_type,
    cokernelEmbedding, Sum.elim_inl, Sum.elim_inr, zero_mul,
    Finset.sum_const_zero, zero_add, add_zero]
  let zr : Fin beta → Fin (p+1) → Fin gamma → Fin (p+1) → ℚ :=
    fun k s j t => z (⟨Sum.inr k,s⟩,⟨Sum.inl j,t⟩)
  change (∑ k' : Fin beta, ∑ s : Fin (p+1), ∑ j' : Fin gamma, ∑ t : Fin (p+1),
    ((Pi.single (k,j) (1 : ℚ) : Fin beta × Fin gamma → ℚ) (k',j') * (antiDiagonal p ((s,t).2, (s,t).1))) *
      zr k' s j' t) = ∑ t : Fin (p+1), (-1 : ℚ)^t.val * zr k ⟨p-t.val,by omega⟩ j t
  simp only [Pi.single_apply, Prod.mk.injEq, ite_mul, one_mul, zero_mul]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero]
  simp only [ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [ antiDiagonal]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  have he (s : Fin (p+1)) : t.val + s.val = p ↔ s.val = p-t.val := by
    have h := t.isLt
    omega
  simp_rw [he]
  exact fin_pick (p+1) (p-t.val) ((-1 : ℚ)^t.val)
    (fun s => zr k s j t) (by omega)

lemma slLine_kernelEmbedding (p alpha beta gamma delta : ℕ)
    (w : Fin alpha × Fin delta → ℚ) (r t : Fin (p+1)) :
    slLine p alpha beta gamma delta (kernelEmbedding p alpha beta gamma delta w) r t =
      if r.val + t.val = p then (-1 : ℚ)^(p-r.val) • w else 0 := by
  funext k
  have he : (p-r.val)+(p-t.val) = p ↔ r.val+t.val=p := by
    have hr := r.isLt
    have ht := t.isLt
    omega
  change w k * (if (p-r.val)+(p-t.val)=p then (-1 : ℚ)^(p-r.val) else 0) = _
  simp only [he]
  split_ifs <;> simp [mul_comm]

private lemma ssLine_at_last (p alpha beta gamma delta : ℕ) (hp : 0 < p)
    (u : (Σ t : Fin alpha ⊕ Fin beta, Fin (blockLength p alpha beta t + 1)) × (Σ t : Fin gamma ⊕ Fin delta, Fin (blockLength p gamma delta t)) → ℚ) :
    ssLine p alpha beta gamma delta hp u ⟨p,by omega⟩ =
      fun k => u (ssSource p alpha beta gamma delta hp k) := by
  funext k
  change u (⟨Sum.inl k.1,⟨p-p,by dsimp [blockLength]; omega⟩⟩,
    ⟨Sum.inl k.2,⟨0,by dsimp [blockLength]; omega⟩⟩) = _
  simp [ssSource]

private lemma cokernel_reservoir_SS (p alpha beta gamma delta : ℕ) (hp : 0 < p)
    (X : Matrix (Fin alpha) (Fin alpha) ℚ) (Y : Matrix (Fin gamma) (Fin gamma) ℚ)
    (BM : Matrix (Fin beta) (Fin alpha) ℚ) (DM : Matrix (Fin gamma) (Fin delta) ℚ)
    (u : (Σ t : Fin alpha ⊕ Fin beta, Fin (blockLength p alpha beta t + 1)) × (Σ t : Fin gamma ⊕ Fin delta, Fin (blockLength p gamma delta t)) → ℚ) :
    ((LinearMap.toMatrix' (cokernelEmbedding p alpha beta gamma delta)).transpose).mulVec
      ((reservoirCross p alpha beta gamma delta X Y BM DM).mulVec
        (sourceSS p alpha beta gamma delta u)) =
      (kronecker BM Y).mulVec (fun k => u (ssSource p alpha beta gamma delta hp k)) := by
  classical
  funext ⟨k,j⟩
  rw [cokernel_mulVec_formula]
  simp_rw [reservoirCross_SS_long_row p alpha beta gamma delta hp X Y BM DM u]
  have he (t : Fin (p+1)) : t.val = 0 ↔ t = 0 := by simp
  simp_rw [he]
  simp [mul_ite, ssLine_at_last p alpha beta gamma delta hp u]

private lemma cokernel_reservoir_kernel (p alpha beta gamma delta : ℕ)
    (X : Matrix (Fin alpha) (Fin alpha) ℚ) (Y : Matrix (Fin gamma) (Fin gamma) ℚ)
    (BM : Matrix (Fin beta) (Fin alpha) ℚ) (DM : Matrix (Fin gamma) (Fin delta) ℚ)
    (w : Fin alpha × Fin delta → ℚ) :
    ((LinearMap.toMatrix' (cokernelEmbedding p alpha beta gamma delta)).transpose).mulVec
      ((reservoirCross p alpha beta gamma delta X Y BM DM).mulVec
        (kernelEmbedding p alpha beta gamma delta w)) =
      (((p : ℚ)+1) • kronecker BM DM).mulVec w := by
  classical
  have hk : sourceSL p alpha beta gamma delta (kernelEmbedding p alpha beta gamma delta w) =
      kernelEmbedding p alpha beta gamma delta w := by
    funext ⟨⟨i,s⟩,⟨j,t⟩⟩
    cases i <;> cases j <;> rfl
  funext ⟨k,j⟩
  rw [← hk, cokernel_mulVec_formula]
  simp_rw [reservoirCross_SL_long_row p alpha beta gamma delta X Y BM DM,
    slLine_kernelEmbedding]
  have he (t : Fin (p+1)) : (p-t.val)+t.val=p := by have h := t.isLt; omega
  simp only [he, if_true, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
  have hh (t : Fin (p+1)) : (-1 : ℚ)^t.val *
      ((-1 : ℚ)^(p-(p-t.val)) * (kronecker BM DM).mulVec w (k,j)) =
      (kronecker BM DM).mulVec w (k,j) := by
    have ht : p-(p-t.val)=t.val := by have h := t.isLt; omega
    rw [ht, ← mul_assoc, neg_one_pow_square, one_mul]
  simp_rw [hh]
  simp [Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul, Nat.cast_add, Nat.cast_one]

end
section

open Matrix Module

lemma sourceSL_kernelEmbedding (p alpha beta gamma delta : ℕ)
    (w : Fin alpha × Fin delta → ℚ) :
    sourceSL p alpha beta gamma delta (kernelEmbedding p alpha beta gamma delta w) =
      kernelEmbedding p alpha beta gamma delta w := by
  funext ⟨⟨i,s⟩,⟨j,t⟩⟩
  cases i <;> cases j <;> rfl

private lemma reservoirCross_kernel_short_row (p alpha beta gamma delta : ℕ)
    (X : Matrix (Fin alpha) (Fin alpha) ℚ) (Y : Matrix (Fin gamma) (Fin gamma) ℚ)
    (BM : Matrix (Fin beta) (Fin alpha) ℚ) (DM : Matrix (Fin gamma) (Fin delta) ℚ)
    (w : Fin alpha × Fin delta → ℚ)
    (i : Fin alpha) (j : Fin gamma) (r : Fin p) (t : Fin (p+1)) :
    (reservoirCross p alpha beta gamma delta X Y BM DM).mulVec
      (kernelEmbedding p alpha beta gamma delta w) (⟨Sum.inl i,r⟩,⟨Sum.inl j,t⟩) =
      if r.val=0 ∧ t.val=0 then (kronecker X DM).mulVec w (i,j) else 0 := by
  rw [← sourceSL_kernelEmbedding p alpha beta gamma delta w,
    reservoirCross_SL_short_row]
  have hline : (fun k : Fin alpha × Fin delta =>
      (kernelEmbedding p alpha beta gamma delta w)
        (⟨Sum.inl k.1,⟨0,by dsimp [blockLength]; omega⟩⟩,
         ⟨Sum.inr k.2,⟨p-t.val,by dsimp [blockLength]; omega⟩⟩)) =
        if t.val=0 then w else 0 := by
    funext k
    change w k * (if 0+(p-t.val)=p then (-1 : ℚ)^0 else 0) = _
    have ht : 0+(p-t.val)=p ↔ t.val=0 := by have h := t.isLt; omega
    simp only [ht, pow_zero]
    split_ifs <;> simp
  rw [hline]
  by_cases hr : r.val=0 <;> by_cases ht : t.val=0 <;> simp [hr,ht]

private lemma reservoirCross_sample_SS (p alpha beta gamma delta : ℕ) (hp : 0 < p)
    (X : Matrix (Fin alpha) (Fin alpha) ℚ) (Y : Matrix (Fin gamma) (Fin gamma) ℚ)
    (BM : Matrix (Fin beta) (Fin alpha) ℚ) (DM : Matrix (Fin gamma) (Fin delta) ℚ)
    (u : (Σ t : Fin alpha ⊕ Fin beta, Fin (blockLength p alpha beta t + 1)) × (Σ t : Fin gamma ⊕ Fin delta, Fin (blockLength p gamma delta t)) → ℚ) :
    (fun k => (reservoirCross p alpha beta gamma delta X Y BM DM).mulVec
      (sourceSS p alpha beta gamma delta u) (ssTarget p alpha beta gamma delta hp k)) =
      (kronecker X Y).mulVec (fun k => u (ssSource p alpha beta gamma delta hp k)) := by
  funext ⟨i,j⟩
  rw [ssTarget, reservoirCross_SS_short_row p alpha beta gamma delta hp]
  simp

private lemma reservoirCross_sample_kernel (p alpha beta gamma delta : ℕ) (hp : 0 < p)
    (X : Matrix (Fin alpha) (Fin alpha) ℚ) (Y : Matrix (Fin gamma) (Fin gamma) ℚ)
    (BM : Matrix (Fin beta) (Fin alpha) ℚ) (DM : Matrix (Fin gamma) (Fin delta) ℚ)
    (w : Fin alpha × Fin delta → ℚ) :
    (fun k => (reservoirCross p alpha beta gamma delta X Y BM DM).mulVec
      (kernelEmbedding p alpha beta gamma delta w) (ssTarget p alpha beta gamma delta hp k)) =
      (kronecker X DM).mulVec w := by
  funext ⟨i,j⟩
  rw [ssTarget, reservoirCross_kernel_short_row]
  simp

end
section

open Matrix Module

private theorem short_reservoir_injective (p alpha beta gamma delta : ℕ) (hp : 0 < p)
    (X : Matrix (Fin alpha) (Fin alpha) ℚ) (Y : Matrix (Fin gamma) (Fin gamma) ℚ)
    (BM : Matrix (Fin beta) (Fin alpha) ℚ) (DM : Matrix (Fin gamma) (Fin delta) ℚ)
    (hR : IsUnit (1+kronecker X Y))
    (hS : Function.Injective ((((p : ℚ)+1) • kronecker BM DM -
      kronecker BM Y * (1+kronecker X Y)⁻¹ * kronecker X DM).mulVec)) :
    Function.Injective (widthTwoMatrix p p alpha beta gamma delta +
      reservoirCross p alpha beta gamma delta X Y BM DM).mulVecLin := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro u hu
  change (widthTwoMatrix p p alpha beta gamma delta +
    reservoirCross p alpha beta gamma delta X Y BM DM).mulVec u = 0 at hu
  let W := widthTwoMatrix p p alpha beta gamma delta
  let C := reservoirCross p alpha beta gamma delta X Y BM DM
  let E := (LinearMap.toMatrix' (cokernelEmbedding p alpha beta gamma delta)).transpose
  let v : Fin alpha × Fin gamma → ℚ := fun k => u (ssSource p alpha beta gamma delta hp k)
  obtain ⟨w,hw⟩ := kernel_coordinates p alpha beta gamma delta _
    (sourceSL_kernel_of_updated_zero p alpha beta gamma delta X Y BM DM u hu)
  have hc : C.mulVec u = C.mulVec (sourceSS p alpha beta gamma delta u) +
      C.mulVec (kernelEmbedding p alpha beta gamma delta w) := by
    rw [reservoirCross_source_decomposition, ← hw]
  have hr : (1+kronecker X Y).mulVec v + (kronecker X DM).mulVec w = 0 := by
    have hh := congrArg (fun z => fun k => z (ssTarget p alpha beta gamma delta hp k)) hu
    rw [Matrix.add_mulVec, hc] at hh
    change (fun k => W.mulVec u (ssTarget p alpha beta gamma delta hp k) +
      (C.mulVec (sourceSS p alpha beta gamma delta u) (ssTarget p alpha beta gamma delta hp k) +
       C.mulVec (kernelEmbedding p alpha beta gamma delta w) (ssTarget p alpha beta gamma delta hp k))) = 0 at hh
    simp only [W, old_reservoir_sample] at hh
    have hss := reservoirCross_sample_SS p alpha beta gamma delta hp X Y BM DM u
    have hsl := reservoirCross_sample_kernel p alpha beta gamma delta hp X Y BM DM w
    change _ = (kronecker X Y).mulVec v at hss
    change _ = (kronecker X DM).mulVec w at hsl
    have heq : (fun k => v k +
      (C.mulVec (sourceSS p alpha beta gamma delta u) (ssTarget p alpha beta gamma delta hp k) +
       C.mulVec (kernelEmbedding p alpha beta gamma delta w) (ssTarget p alpha beta gamma delta hp k))) =
      v + ((kronecker X Y).mulVec v + (kronecker X DM).mulVec w) := by
      rw [← hss, ← hsl]
      rfl
    rw [heq] at hh
    simpa only [Matrix.add_mulVec, Matrix.one_mulVec, add_assoc] using hh
  have he : (kronecker BM Y).mulVec v + (((p : ℚ)+1) • kronecker BM DM).mulVec w = 0 := by
    have hh := congrArg E.mulVec hu
    rw [Matrix.add_mulVec, Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_zero] at hh
    change (E*W).mulVec u + E.mulVec (C.mulVec u) = 0 at hh
    rw [cokernelMatrix_mul_widthTwo, Matrix.zero_mulVec, zero_add, hc, Matrix.mulVec_add] at hh
    change ((LinearMap.toMatrix' (cokernelEmbedding p alpha beta gamma delta)).transpose).mulVec _ +
      ((LinearMap.toMatrix' (cokernelEmbedding p alpha beta gamma delta)).transpose).mulVec _ = 0 at hh
    rw [cokernel_reservoir_SS p alpha beta gamma delta hp, cokernel_reservoir_kernel] at hh
    exact hh
  obtain ⟨hv0,hw0⟩ := schur_two_equations (1+kronecker X Y) (kronecker X DM)
    (kronecker BM Y) (((p : ℚ)+1) • kronecker BM DM) hR hS v w hr he
  have hss : sourceSS p alpha beta gamma delta u = 0 := by
    apply sourceSS_zero_of_kernel
    apply sourceSS_kernel_of_rows_zero
    intro i j r t
    have hh := congrFun hu (⟨Sum.inl i,r⟩,⟨Sum.inl j,t⟩)
    rw [Matrix.add_mulVec, hc, hw0, map_zero, Matrix.mulVec_zero, add_zero] at hh
    have hcr := reservoirCross_SS_short_row p alpha beta gamma delta hp X Y BM DM u i j r t
    change C.mulVec (sourceSS p alpha beta gamma delta u) (⟨Sum.inl i,r⟩,⟨Sum.inl j,t⟩) = if r.val=0 ∧ t.val=0 then (kronecker X Y).mulVec v (i,j) else 0 at hcr
    rw [hv0, Matrix.mulVec_zero] at hcr
    simp only [Pi.zero_apply, ite_self] at hcr
    simp only [Pi.add_apply, hcr, add_zero, Pi.zero_apply] at hh
    exact hh
  have hc0 : C.mulVec u = 0 := by rw [hc,hss,hw0,map_zero,Matrix.mulVec_zero,zero_add]
  have huW : W.mulVec u = 0 := by
    rw [Matrix.add_mulVec, hc0, add_zero] at hu
    exact hu
  obtain ⟨z,hz⟩ := kernel_coordinates p alpha beta gamma delta u huW
  have hsl0 : sourceSL p alpha beta gamma delta u = 0 := by rw [← hw,hw0,map_zero]
  have hz0 : z = 0 := by
    apply kernelEmbedding_injective p alpha beta gamma delta
    rw [map_zero, ← sourceSL_kernelEmbedding, hz, hsl0]
  rw [← hz,hz0,map_zero]

private theorem short_short_injective_witness (p alpha beta gamma delta : ℕ) (hp : 0 < p)
    (hB : 0 < beta) (hBA : beta ≤ alpha) (hD : 0 < delta) (hDG : delta ≤ gamma)
    (hdim : alpha*delta ≤ beta*gamma) :
    RationalWitness (leftDim p alpha beta) (rightDim p alpha beta)
      (leftDim p gamma delta) (rightDim p gamma delta) := by
  let X := -backward alpha
  let Y := forwardHalf gamma
  let BM := rowSelector alpha beta
  let DM := (rowSelector gamma delta).transpose
  let F := widthTwoMatrix p p alpha beta gamma delta + reservoirCross p alpha beta gamma delta X Y BM DM
  have hR : IsUnit (1+kronecker X Y) :=
    (cyclic_resolvent_lemma alpha beta gamma delta hB hBA hD hDG (p : ℚ) (by exact_mod_cast hp)).1
  have hS : Function.Injective ((((p : ℚ)+1) • kronecker BM DM -
      kronecker BM Y * (1+kronecker X Y)⁻¹ * kronecker X DM).mulVec) := by
    apply matrix_injective_of_rank
    have hh := short_short_cyclic_schur_rank alpha beta gamma delta p hB hBA hD hDG hp
    simpa only [X,Y,BM,DM,reservoir,Fintype.card_prod, Fintype.card_fin, min_eq_left hdim] using hh
  have hi : Function.Injective F.mulVecLin := short_reservoir_injective p alpha beta gamma delta hp X Y BM DM hR hS
  have hr : F.rank = rightDim p alpha beta * leftDim p gamma delta := by
    rw [Matrix.rank,LinearMap.finrank_range_of_inj hi,Module.finrank_pi,
      Fintype.card_prod,cols_card,rows_card]
  have hu := F.rank_le_card_height
  simp only [Fintype.card_prod,rows_card,cols_card] at hu
  rw [hr] at hu
  apply witness_of_typed_slices (rows_card _ _ _) (cols_card _ _ _)
    (rows_card _ _ _) (cols_card _ _ _)
    (threeSlices (arrow0 p alpha beta) (arrow1 p alpha beta) (reservoirThirdLeft p alpha beta X BM))
    (threeSlices (arrow0 p gamma delta).transpose (arrow1 p gamma delta).transpose
      (reservoirThirdRight p gamma delta Y DM))
  rw [typed_three_slice_flow]
  change F.rank = _
  rw [hr,min_eq_right hu]

theorem short_short_witness (p alpha beta gamma delta : ℕ) (hp : 0 < p)
    (hB : 0 < beta) (hBA : beta ≤ alpha) (hD : 0 < delta) (hDG : delta ≤ gamma) :
    RationalWitness (leftDim p alpha beta) (rightDim p alpha beta)
      (leftDim p gamma delta) (rightDim p gamma delta) := by
  rcases le_total (alpha*delta) (beta*gamma) with h | h
  · exact short_short_injective_witness p alpha beta gamma delta hp hB hBA hD hDG h
  · exact witness_swap (short_short_injective_witness p gamma delta alpha beta hp hD hDG hB hBA
      (by simpa only [mul_comm] using h))

end

end D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur
