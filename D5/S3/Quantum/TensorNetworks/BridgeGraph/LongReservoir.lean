/- GID: D5/S3/Quantum/TensorNetworks/BridgeGraph/LongReservoir
   generality: G
   mirror-B: D5/B/S3/Quantum/TensorNetworks/BridgeGraph/LongReservoir
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: LongReservoir for width-three bridge flow. -/

/-
proof_shape: base_witness: content
escape_witness: base_witness: LongReservoir.long_reservoir_injective
admission_basis: escape-witness (base_witness)
Module content mechanism: long_reservoir_injective: exact higher-order long-reservoir Schur reduction.
Direct frozen dependencies: none on the implementation baseline.
Utility: none; symbolic constructions and proofs for arbitrary dimensions,
not bounded enumeration, a checker, numeric reduction, or a certified instance.
Information-escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/14762
-/

import D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur

set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Quantum.TensorNetworks.BridgeGraph.LongReservoir
open Matrix Module

open D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound
open D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles
open D5.S3.Quantum.TensorNetworks.BridgeGraph.CyclicResolvent
open D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks
open D5.S3.Quantum.TensorNetworks.BridgeGraph.ReservoirSchur
open Matrix Module
section

open Matrix Module

private theorem single_update_injective (p alpha beta gamma delta : ℕ)
    (BM : Matrix (Fin beta) (Fin alpha) ℚ) (DM : Matrix (Fin gamma) (Fin delta) ℚ)
    (hS : Function.Injective (kronecker BM DM).mulVec) :
    Function.Injective (widthTwoMatrix p p alpha beta gamma delta +
      singleCross p alpha beta gamma delta BM DM).mulVecLin := by
  apply (LinearMap.ker_eq_bot).mp
  apply LinearMap.ker_eq_bot'.mpr
  intro u hu
  change (widthTwoMatrix p p alpha beta gamma delta +
    singleCross p alpha beta gamma delta BM DM).mulVec u = 0 at hu
  let E := (LinearMap.toMatrix' (cokernelEmbedding p alpha beta gamma delta)).transpose
  let V := (inclusion (kernelSample p alpha beta gamma delta)).transpose
  let J := inclusion (cokernelSample p alpha beta gamma delta)
  let S := kronecker BM DM
  have he : E * (widthTwoMatrix p p alpha beta gamma delta +
      singleCross p alpha beta gamma delta BM DM) = S * V := by
    dsimp [E, S, V, singleCross]
    rw [Matrix.mul_add, cokernelMatrix_mul_widthTwo, zero_add]
    simp only [← Matrix.mul_assoc, cokernel_sample_identity, Matrix.one_mul]
  have hs : S.mulVec (V.mulVec u) = 0 := by
    rw [Matrix.mulVec_mulVec, ← he, ← Matrix.mulVec_mulVec, hu]
    simp
  have hv : V.mulVec u = 0 := hS (by simpa [S] using hs)
  have hc : (singleCross p alpha beta gamma delta BM DM).mulVec u = 0 := by
    change (J * S * V).mulVec u = 0
    rw [← Matrix.mulVec_mulVec, hv]
    simp
  have ha : (widthTwoMatrix p p alpha beta gamma delta).mulVec u = 0 := by
    rw [Matrix.add_mulVec, hc, add_zero] at hu
    exact hu
  obtain ⟨w, hw⟩ := kernel_coordinates p alpha beta gamma delta u ha
  have hw0 : w = 0 := by
    rw [← hw, ← kernelMatrix_mulVec, Matrix.mulVec_mulVec] at hv
    change ((inclusion (kernelSample p alpha beta gamma delta)).transpose *
      (LinearMap.toMatrix' (kernelEmbedding p alpha beta gamma delta))).mulVec w = 0 at hv
    rw [kernel_sample_identity, Matrix.one_mulVec] at hv
    exact hv
  rw [← hw, hw0, map_zero]

private lemma rectId_inclusion {a b : ℕ} (hab : a ≤ b) :
    rectId b a = inclusion (Fin.castLE hab) := by
  ext i j
  simp [rectId, inclusion, Matrix.one_apply, Fin.ext_iff]

private lemma rectId_tensor_injective {alpha beta gamma delta : ℕ}
    (hAB : alpha ≤ beta) (hDG : delta ≤ gamma) :
    Function.Injective (kronecker (rectId beta alpha) (rectId gamma delta)).mulVec := by
  rw [rectId_inclusion hAB, rectId_inclusion hDG, ← inclusion_prod]
  apply inclusion_injective
  intro i j h
  apply Prod.ext
  · apply Fin.ext
    have hh := congrArg (fun k => k.1.val) h
    exact hh
  · apply Fin.ext
    have hh := congrArg (fun k => k.2.val) h
    exact hh

private theorem single_reversal_injective_witness (p alpha beta gamma delta : ℕ)
    (hAB : alpha ≤ beta) (hDG : delta ≤ gamma) :
    RationalWitness (leftDim p alpha beta) (rightDim p alpha beta)
      (leftDim p gamma delta) (rightDim p gamma delta) := by
  let BM := rectId beta alpha
  let DM := rectId gamma delta
  let F := widthTwoMatrix p p alpha beta gamma delta +
    singleCross p alpha beta gamma delta BM DM
  have hi : Function.Injective F.mulVecLin :=
    single_update_injective p alpha beta gamma delta BM DM (rectId_tensor_injective hAB hDG)
  have hr : F.rank = rightDim p alpha beta * leftDim p gamma delta := by
    rw [Matrix.rank, LinearMap.finrank_range_of_inj hi, Module.finrank_pi,
      Fintype.card_prod, cols_card, rows_card]
  have hu := F.rank_le_card_height
  simp only [Fintype.card_prod, rows_card, cols_card] at hu
  rw [hr] at hu
  apply witness_of_typed_slices (rows_card _ _ _) (cols_card _ _ _)
    (rows_card _ _ _) (cols_card _ _ _)
    (threeSlices (arrow0 p alpha beta) (arrow1 p alpha beta) (singleThirdLeft p alpha beta BM))
    (threeSlices (arrow0 p gamma delta).transpose (arrow1 p gamma delta).transpose
      (singleThirdRight p gamma delta DM))
  rw [typed_three_slice_flow, ← singleCross_kronecker]
  change F.rank = _
  rw [hr, min_eq_right hu]

private theorem single_reversal_witness (p alpha beta gamma delta : ℕ)
    (horient : (alpha ≤ beta ∧ delta ≤ gamma) ∨ (beta ≤ alpha ∧ gamma ≤ delta)) :
    RationalWitness (leftDim p alpha beta) (rightDim p alpha beta)
      (leftDim p gamma delta) (rightDim p gamma delta) := by
  rcases horient with h | h
  · exact single_reversal_injective_witness p alpha beta gamma delta h.1 h.2
  · exact witness_swap (single_reversal_injective_witness p gamma delta alpha beta h.2 h.1)

end
section

open Matrix Module

private def longThirdLeft (p alpha beta : ℕ)
    (X : Matrix (Fin beta) (Fin beta) ℚ) (BM : Matrix (Fin beta) (Fin alpha) ℚ) :
    Matrix ((Σ t : Fin alpha ⊕ Fin beta, Fin (blockLength p alpha beta t))) ((Σ t : Fin alpha ⊕ Fin beta, Fin (blockLength p alpha beta t + 1))) ℚ := fun r s =>
  match r,s with
  | ⟨Sum.inr k,u⟩,⟨Sum.inr h,v⟩ => if u.val=p ∧ v.val=p+1 then X k h else 0
  | ⟨Sum.inr k,u⟩,⟨Sum.inl i,v⟩ => if u.val+v.val=p then BM k i else 0
  | _,_ => 0

private def longThirdRight (p gamma delta : ℕ)
    (Y : Matrix (Fin delta) (Fin delta) ℚ) (DM : Matrix (Fin gamma) (Fin delta) ℚ) :
    Matrix ((Σ t : Fin gamma ⊕ Fin delta, Fin (blockLength p gamma delta t + 1))) ((Σ t : Fin gamma ⊕ Fin delta, Fin (blockLength p gamma delta t))) ℚ := fun r s =>
  match r,s with
  | ⟨Sum.inr j,u⟩,⟨Sum.inr h,v⟩ => if u.val=p+1 ∧ v.val=p then Y j h else 0
  | ⟨Sum.inl j,u⟩,⟨Sum.inr h,v⟩ => if u.val+v.val=p then DM j h else 0
  | _,_ => 0

private def longCross (p alpha beta gamma delta : ℕ)
    (X : Matrix (Fin beta) (Fin beta) ℚ) (Y : Matrix (Fin delta) (Fin delta) ℚ)
    (BM : Matrix (Fin beta) (Fin alpha) ℚ) (DM : Matrix (Fin gamma) (Fin delta) ℚ) :=
  kronecker (longThirdLeft p alpha beta X BM) (longThirdRight p gamma delta Y DM)

private def sourceLL (p alpha beta gamma delta : ℕ)
    (u : (Σ t : Fin alpha ⊕ Fin beta, Fin (blockLength p alpha beta t + 1)) × (Σ t : Fin gamma ⊕ Fin delta, Fin (blockLength p gamma delta t)) → ℚ) :
    (Σ t : Fin alpha ⊕ Fin beta, Fin (blockLength p alpha beta t + 1)) × (Σ t : Fin gamma ⊕ Fin delta, Fin (blockLength p gamma delta t)) → ℚ := fun k =>
  match k.1.1,k.2.1 with
  | Sum.inr _,Sum.inr _ => u k
  | _,_ => 0

private lemma longThirdLeft_short_row (p alpha beta : ℕ)
    (X : Matrix (Fin beta) (Fin beta) ℚ) (BM : Matrix (Fin beta) (Fin alpha) ℚ)
    (i : Fin alpha) (r : Fin p) (s : (Σ t : Fin alpha ⊕ Fin beta, Fin (blockLength p alpha beta t + 1))) :
    longThirdLeft p alpha beta X BM ⟨Sum.inl i,r⟩ s = 0 := by
  rcases s with ⟨j,t⟩
  cases j <;> rfl

private lemma longThirdRight_short_column (p gamma delta : ℕ)
    (Y : Matrix (Fin delta) (Fin delta) ℚ) (DM : Matrix (Fin gamma) (Fin delta) ℚ)
    (r : (Σ t : Fin gamma ⊕ Fin delta, Fin (blockLength p gamma delta t + 1))) (j : Fin gamma) (s : Fin p) :
    longThirdRight p gamma delta Y DM r ⟨Sum.inl j,s⟩ = 0 := by
  rcases r with ⟨i,t⟩
  cases i <;> rfl

private lemma longCross_short_output (p alpha beta gamma delta : ℕ)
    (X : Matrix (Fin beta) (Fin beta) ℚ) (Y : Matrix (Fin delta) (Fin delta) ℚ)
    (BM : Matrix (Fin beta) (Fin alpha) ℚ) (DM : Matrix (Fin gamma) (Fin delta) ℚ)
    (u : (Σ t : Fin alpha ⊕ Fin beta, Fin (blockLength p alpha beta t + 1)) × (Σ t : Fin gamma ⊕ Fin delta, Fin (blockLength p gamma delta t)) → ℚ)
    (i : Fin alpha) (r : Fin p) (s : (Σ t : Fin gamma ⊕ Fin delta, Fin (blockLength p gamma delta t + 1))) :
    (longCross p alpha beta gamma delta X Y BM DM).mulVec u (⟨Sum.inl i,r⟩,s) = 0 := by
  apply Finset.sum_eq_zero
  intro k _
  change longThirdLeft p alpha beta X BM ⟨Sum.inl i,r⟩ k.1 *
    longThirdRight p gamma delta Y DM s k.2 * u k = 0
  rw [longThirdLeft_short_row,zero_mul,zero_mul]

private lemma longCross_source_decomposition (p alpha beta gamma delta : ℕ)
    (X : Matrix (Fin beta) (Fin beta) ℚ) (Y : Matrix (Fin delta) (Fin delta) ℚ)
    (BM : Matrix (Fin beta) (Fin alpha) ℚ) (DM : Matrix (Fin gamma) (Fin delta) ℚ)
    (u : (Σ t : Fin alpha ⊕ Fin beta, Fin (blockLength p alpha beta t + 1)) × (Σ t : Fin gamma ⊕ Fin delta, Fin (blockLength p gamma delta t)) → ℚ) :
    (longCross p alpha beta gamma delta X Y BM DM).mulVec u =
      (longCross p alpha beta gamma delta X Y BM DM).mulVec (sourceLL p alpha beta gamma delta u) +
      (longCross p alpha beta gamma delta X Y BM DM).mulVec (sourceSL p alpha beta gamma delta u) := by
  rw [← Matrix.mulVec_add]
  funext r
  apply Finset.sum_congr rfl
  rintro ⟨⟨i,s⟩,⟨j,t⟩⟩ _
  cases i <;> cases j
  · change longThirdLeft p alpha beta X BM r.1 ⟨Sum.inl _,s⟩ *
      longThirdRight p gamma delta Y DM r.2 ⟨Sum.inl _,t⟩ * _ = _
    rw [longThirdRight_short_column,mul_zero,zero_mul]
    simp [sourceLL,sourceSL]
  · simp [sourceLL,sourceSL]
  · change longThirdLeft p alpha beta X BM r.1 ⟨Sum.inr _,s⟩ *
      longThirdRight p gamma delta Y DM r.2 ⟨Sum.inl _,t⟩ * _ = _
    rw [longThirdRight_short_column,mul_zero,zero_mul]
    simp [sourceLL,sourceSL]
  · simp [sourceLL,sourceSL]

private theorem long_sourceSL_kernel_of_updated_zero (p alpha beta gamma delta : ℕ)
    (X : Matrix (Fin beta) (Fin beta) ℚ) (Y : Matrix (Fin delta) (Fin delta) ℚ)
    (BM : Matrix (Fin beta) (Fin alpha) ℚ) (DM : Matrix (Fin gamma) (Fin delta) ℚ)
    (u : (Σ t : Fin alpha ⊕ Fin beta, Fin (blockLength p alpha beta t + 1)) × (Σ t : Fin gamma ⊕ Fin delta, Fin (blockLength p gamma delta t)) → ℚ)
    (hu : (widthTwoMatrix p p alpha beta gamma delta +
      longCross p alpha beta gamma delta X Y BM DM).mulVec u = 0) :
    (widthTwoMatrix p p alpha beta gamma delta).mulVec (sourceSL p alpha beta gamma delta u) = 0 := by
  funext ⟨⟨i,s⟩,⟨j,t⟩⟩
  rw [widthTwo_mulVec_block]
  cases i <;> cases j
  · change (pencil p p).mulVec (0 : Fin (p+1) × Fin p → ℚ) (s,t)=0
    simp
  · rename_i i j
    have hh := congrFun hu (⟨Sum.inl i,s⟩,⟨Sum.inr j,t⟩)
    rw [Matrix.add_mulVec] at hh
    simp only [Pi.add_apply,longCross_short_output,add_zero,Pi.zero_apply,widthTwo_mulVec_block] at hh
    exact hh
  · change (pencil (p+1) p).mulVec (0 : Fin (p+2) × Fin p → ℚ) (s,t)=0
    simp
  · change (pencil (p+1) (p+1)).mulVec (0 : Fin (p+2) × Fin (p+1) → ℚ) (s,t)=0
    simp

private theorem sourceLL_kernel_of_rows_zero (p alpha beta gamma delta : ℕ)
    (u : (Σ t : Fin alpha ⊕ Fin beta, Fin (blockLength p alpha beta t + 1)) × (Σ t : Fin gamma ⊕ Fin delta, Fin (blockLength p gamma delta t)) → ℚ)
    (hu : ∀ i : Fin beta, ∀ j : Fin delta, ∀ s : Fin (p+1), ∀ t : Fin (p+2),
      (widthTwoMatrix p p alpha beta gamma delta).mulVec u (⟨Sum.inr i,s⟩,⟨Sum.inr j,t⟩)=0) :
    (widthTwoMatrix p p alpha beta gamma delta).mulVec (sourceLL p alpha beta gamma delta u)=0 := by
  funext ⟨⟨i,s⟩,⟨j,t⟩⟩
  rw [widthTwo_mulVec_block]
  cases i <;> cases j
  · change (pencil p p).mulVec (0 : Fin (p+1) × Fin p → ℚ) (s,t)=0
    simp
  · change (pencil p (p+1)).mulVec (0 : Fin (p+1) × Fin (p+1) → ℚ) (s,t)=0
    simp
  · change (pencil (p+1) p).mulVec (0 : Fin (p+2) × Fin p → ℚ) (s,t)=0
    simp
  · rename_i i j
    have hh := hu i j s t
    rw [widthTwo_mulVec_block] at hh
    exact hh

private theorem sourceLL_zero_of_kernel (p alpha beta gamma delta : ℕ)
    (u : (Σ t : Fin alpha ⊕ Fin beta, Fin (blockLength p alpha beta t + 1)) × (Σ t : Fin gamma ⊕ Fin delta, Fin (blockLength p gamma delta t)) → ℚ)
    (hu : (widthTwoMatrix p p alpha beta gamma delta).mulVec (sourceLL p alpha beta gamma delta u)=0) :
    sourceLL p alpha beta gamma delta u=0 := by
  obtain ⟨w,hw⟩ := kernel_coordinates p alpha beta gamma delta _ hu
  have hw0 : w=0 := by
    funext ⟨i,h⟩
    have hh := congrFun hw (kernelSample p alpha beta gamma delta (i,h))
    simpa [kernelSample,kernelEmbedding,antiDiagonal,sourceLL] using hh
  rw [← hw,hw0,map_zero]

private def llSource (p alpha beta gamma delta : ℕ) (k : Fin beta × Fin delta) :
    (Σ t : Fin alpha ⊕ Fin beta, Fin (blockLength p alpha beta t + 1)) × (Σ t : Fin gamma ⊕ Fin delta, Fin (blockLength p gamma delta t)) :=
  (⟨Sum.inr k.1,⟨p+1,by dsimp [blockLength]; omega⟩⟩,
   ⟨Sum.inr k.2,⟨p,by dsimp [blockLength]; omega⟩⟩)

private def llTarget (p alpha beta gamma delta : ℕ) (k : Fin beta × Fin delta) :
    (Σ t : Fin alpha ⊕ Fin beta, Fin (blockLength p alpha beta t)) × (Σ t : Fin gamma ⊕ Fin delta, Fin (blockLength p gamma delta t + 1)) :=
  (⟨Sum.inr k.1,⟨p,by dsimp [blockLength]; omega⟩⟩,
   ⟨Sum.inr k.2,⟨p+1,by dsimp [blockLength]; omega⟩⟩)

private theorem old_long_reservoir_sample (p alpha beta gamma delta : ℕ)
    (u : (Σ t : Fin alpha ⊕ Fin beta, Fin (blockLength p alpha beta t + 1)) × (Σ t : Fin gamma ⊕ Fin delta, Fin (blockLength p gamma delta t)) → ℚ) (k : Fin beta × Fin delta) :
    (widthTwoMatrix p p alpha beta gamma delta).mulVec u (llTarget p alpha beta gamma delta k)=
      u (llSource p alpha beta gamma delta k) := by
  rw [llTarget,widthTwo_mulVec_block,pencil_mulVec]
  simp [rectExtend,blockLength,localSource,llSource]

end
section

open Matrix Module

private def llLine (p alpha beta gamma delta : ℕ)
    (u : (Σ t : Fin alpha ⊕ Fin beta, Fin (blockLength p alpha beta t + 1)) × (Σ t : Fin gamma ⊕ Fin delta, Fin (blockLength p gamma delta t)) → ℚ) (t : Fin (p+1)) :
    Fin beta × Fin delta → ℚ := fun k =>
  u (⟨Sum.inr k.1,⟨p+1,by dsimp [blockLength]; omega⟩⟩,
     ⟨Sum.inr k.2,⟨p-t.val,by dsimp [blockLength]; omega⟩⟩)

private def slCorner (p alpha beta gamma delta : ℕ)
    (u : (Σ t : Fin alpha ⊕ Fin beta, Fin (blockLength p alpha beta t + 1)) × (Σ t : Fin gamma ⊕ Fin delta, Fin (blockLength p gamma delta t)) → ℚ) (r : Fin (p+1)) :
    Fin alpha × Fin delta → ℚ := fun k =>
  u (⟨Sum.inl k.1,⟨p-r.val,by dsimp [blockLength]; omega⟩⟩,
     ⟨Sum.inr k.2,⟨p,by dsimp [blockLength]; omega⟩⟩)

private lemma longCross_SL_short_row (p alpha beta gamma delta : ℕ)
    (X : Matrix (Fin beta) (Fin beta) ℚ) (Y : Matrix (Fin delta) (Fin delta) ℚ)
    (BM : Matrix (Fin beta) (Fin alpha) ℚ) (DM : Matrix (Fin gamma) (Fin delta) ℚ)
    (u : (Σ t : Fin alpha ⊕ Fin beta, Fin (blockLength p alpha beta t + 1)) × (Σ t : Fin gamma ⊕ Fin delta, Fin (blockLength p gamma delta t)) → ℚ)
    (k : Fin beta) (j : Fin gamma) (r t : Fin (p + 1)) :
    (longCross p alpha beta gamma delta X Y BM DM).mulVec
      (sourceSL p alpha beta gamma delta u) (⟨Sum.inr k, r⟩, ⟨Sum.inl j, t⟩) =
      (kronecker BM DM).mulVec (slLine p alpha beta gamma delta u r t) (k, j) := by
  classical
  have hr (s : Fin (p + 1)) : r.val + s.val = p ↔ s.val = p - r.val := by
    have h := r.isLt
    omega
  have ht (s : Fin (p + 1)) : t.val + s.val = p ↔ s.val = p - t.val := by
    have h := t.isLt
    omega
  simp only [longCross, Matrix.mulVec, dotProduct, Matrix.kronecker, Matrix.kroneckerMap,
    Matrix.of_apply, Fintype.sum_prod_type, Fintype.sum_sigma, Fintype.sum_sum_type,
    longThirdLeft, longThirdRight, sourceSL, blockLength, Sum.elim_inl, Sum.elim_inr,
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

private lemma longCross_LL_short_row (p alpha beta gamma delta : ℕ)
    (X : Matrix (Fin beta) (Fin beta) ℚ) (Y : Matrix (Fin delta) (Fin delta) ℚ)
    (BM : Matrix (Fin beta) (Fin alpha) ℚ) (DM : Matrix (Fin gamma) (Fin delta) ℚ)
    (u : (Σ t : Fin alpha ⊕ Fin beta, Fin (blockLength p alpha beta t + 1)) × (Σ t : Fin gamma ⊕ Fin delta, Fin (blockLength p gamma delta t)) → ℚ)
    (k : Fin beta) (j : Fin gamma) (r t : Fin (p+1)) :
    (longCross p alpha beta gamma delta X Y BM DM).mulVec
      (sourceLL p alpha beta gamma delta u) (⟨Sum.inr k,r⟩,⟨Sum.inl j,t⟩) =
      if r.val=p then (kronecker X DM).mulVec (llLine p alpha beta gamma delta u t) (k,j) else 0 := by
  classical
  have ht (s : Fin (p+1)) : t.val+s.val=p ↔ s.val=p-t.val := by have h := t.isLt; omega
  simp only [longCross,Matrix.mulVec,dotProduct,Matrix.kronecker,Matrix.kroneckerMap,
    Matrix.of_apply,Fintype.sum_prod_type,Fintype.sum_sigma,Fintype.sum_sum_type,
    longThirdLeft,longThirdRight,sourceLL,blockLength,Sum.elim_inl,Sum.elim_inr,
    mul_zero,zero_mul,Finset.sum_const_zero,zero_add,add_zero]
  simp_rw [ht]
  by_cases hr : r.val=p
  · simp only [hr,true_and,if_pos]
    calc
      _ = ∑ i : Fin beta, ∑ h : Fin delta, ∑ s : Fin (p+2), ∑ v : Fin (p+1),
        (if s.val=p+1 then X k i else 0) * (if v.val=p-t.val then DM j h else 0) *
          u (⟨Sum.inr i,s⟩,⟨Sum.inr h,v⟩) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro h _
        have hpt : p-t.val<p+1 := by omega
        exact (double_fin_pick (p+2) (p+1) (p+1) (p-t.val) (X k i) (DM j h)
          (fun z => u (⟨Sum.inr i,z.1⟩,⟨Sum.inr h,z.2⟩))).trans
          (by simp [rectExtend,hpt,llLine])
  · simp [hr]

private lemma longCross_SL_long_row (p alpha beta gamma delta : ℕ)
    (X : Matrix (Fin beta) (Fin beta) ℚ) (Y : Matrix (Fin delta) (Fin delta) ℚ)
    (BM : Matrix (Fin beta) (Fin alpha) ℚ) (DM : Matrix (Fin gamma) (Fin delta) ℚ)
    (u : (Σ t : Fin alpha ⊕ Fin beta, Fin (blockLength p alpha beta t + 1)) × (Σ t : Fin gamma ⊕ Fin delta, Fin (blockLength p gamma delta t)) → ℚ)
    (k : Fin beta) (j : Fin delta) (r : Fin (p+1)) (t : Fin (p+2)) :
    (longCross p alpha beta gamma delta X Y BM DM).mulVec
      (sourceSL p alpha beta gamma delta u) (⟨Sum.inr k,r⟩,⟨Sum.inr j,t⟩) =
      if t.val=p+1 then (kronecker BM Y).mulVec (slCorner p alpha beta gamma delta u r) (k,j) else 0 := by
  classical
  have hr (s : Fin (p+1)) : r.val+s.val=p ↔ s.val=p-r.val := by have h := r.isLt; omega
  simp only [longCross,Matrix.mulVec,dotProduct,Matrix.kronecker,Matrix.kroneckerMap,
    Matrix.of_apply,Fintype.sum_prod_type,Fintype.sum_sigma,Fintype.sum_sum_type,
    longThirdLeft,longThirdRight,sourceSL,blockLength,Sum.elim_inl,Sum.elim_inr,
    mul_zero,zero_mul,Finset.sum_const_zero,zero_add,add_zero]
  simp_rw [hr]
  by_cases ht : t.val=p+1
  · simp only [ht,true_and,if_pos]
    calc
      _ = ∑ i : Fin alpha, ∑ h : Fin delta, ∑ s : Fin (p+1), ∑ v : Fin (p+1),
        (if s.val=p-r.val then BM k i else 0) * (if v.val=p then Y j h else 0) *
          u (⟨Sum.inl i,s⟩,⟨Sum.inr h,v⟩) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro h _
        have hpr : p-r.val<p+1 := by omega
        exact (double_fin_pick (p+1) (p+1) (p-r.val) p (BM k i) (Y j h)
          (fun z => u (⟨Sum.inl i,z.1⟩,⟨Sum.inr h,z.2⟩))).trans
          (by simp [rectExtend,hpr,slCorner])
  · simp [ht]

private lemma longCross_LL_long_row (p alpha beta gamma delta : ℕ)
    (X : Matrix (Fin beta) (Fin beta) ℚ) (Y : Matrix (Fin delta) (Fin delta) ℚ)
    (BM : Matrix (Fin beta) (Fin alpha) ℚ) (DM : Matrix (Fin gamma) (Fin delta) ℚ)
    (u : (Σ t : Fin alpha ⊕ Fin beta, Fin (blockLength p alpha beta t + 1)) × (Σ t : Fin gamma ⊕ Fin delta, Fin (blockLength p gamma delta t)) → ℚ)
    (k : Fin beta) (j : Fin delta) (r : Fin (p+1)) (t : Fin (p+2)) :
    (longCross p alpha beta gamma delta X Y BM DM).mulVec
      (sourceLL p alpha beta gamma delta u) (⟨Sum.inr k,r⟩,⟨Sum.inr j,t⟩) =
      if r.val=p ∧ t.val=p+1 then
        (kronecker X Y).mulVec (fun k => u (llSource p alpha beta gamma delta k)) (k,j) else 0 := by
  classical
  simp only [longCross,Matrix.mulVec,dotProduct,Matrix.kronecker,Matrix.kroneckerMap,
    Matrix.of_apply,Fintype.sum_prod_type,Fintype.sum_sigma,Fintype.sum_sum_type,
    longThirdLeft,longThirdRight,sourceLL,blockLength,Sum.elim_inl,Sum.elim_inr,
    mul_zero,zero_mul,Finset.sum_const_zero,zero_add,add_zero]
  by_cases hr : r.val=p <;> by_cases ht : t.val=p+1
  · simp only [hr,ht,true_and,if_pos]
    calc
      _ = ∑ i : Fin beta, ∑ h : Fin delta, ∑ s : Fin (p+2), ∑ v : Fin (p+1),
        (if s.val=p+1 then X k i else 0) * (if v.val=p then Y j h else 0) *
          u (⟨Sum.inr i,s⟩,⟨Sum.inr h,v⟩) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro h _
        exact (double_fin_pick (p+2) (p+1) (p+1) p (X k i) (Y j h)
          (fun z => u (⟨Sum.inr i,z.1⟩,⟨Sum.inr h,z.2⟩))).trans
          (by simp [rectExtend,llSource])
  · simp [hr,ht]
  · simp [hr,ht]
  · simp [hr,ht]

end
section

open Matrix Module

private lemma llLine_at_zero (p alpha beta gamma delta : ℕ)
    (u : (Σ t : Fin alpha ⊕ Fin beta, Fin (blockLength p alpha beta t + 1)) × (Σ t : Fin gamma ⊕ Fin delta, Fin (blockLength p gamma delta t)) → ℚ) :
    llLine p alpha beta gamma delta u 0 = fun k => u (llSource p alpha beta gamma delta k) := by
  funext k
  change u (⟨Sum.inr k.1,⟨p+1,by dsimp [blockLength]; omega⟩⟩,
    ⟨Sum.inr k.2,⟨p-0,by dsimp [blockLength]; omega⟩⟩) = _
  simp [llSource]

private lemma cokernel_long_LL (p alpha beta gamma delta : ℕ)
    (X : Matrix (Fin beta) (Fin beta) ℚ) (Y : Matrix (Fin delta) (Fin delta) ℚ)
    (BM : Matrix (Fin beta) (Fin alpha) ℚ) (DM : Matrix (Fin gamma) (Fin delta) ℚ)
    (u : (Σ t : Fin alpha ⊕ Fin beta, Fin (blockLength p alpha beta t + 1)) × (Σ t : Fin gamma ⊕ Fin delta, Fin (blockLength p gamma delta t)) → ℚ) :
    ((LinearMap.toMatrix' (cokernelEmbedding p alpha beta gamma delta)).transpose).mulVec
      ((longCross p alpha beta gamma delta X Y BM DM).mulVec
        (sourceLL p alpha beta gamma delta u)) =
      (kronecker X DM).mulVec (fun k => u (llSource p alpha beta gamma delta k)) := by
  classical
  funext ⟨k,j⟩
  rw [cokernel_mulVec_formula]
  simp_rw [longCross_LL_short_row p alpha beta gamma delta X Y BM DM u]
  have he (t : Fin (p+1)) : p-t.val=p ↔ t=0 := by
    have ht := t.isLt
    simp only [Fin.ext_iff,Fin.val_zero]
    omega
  simp_rw [he]
  simp [mul_ite,llLine_at_zero p alpha beta gamma delta u]

private lemma cokernel_long_kernel (p alpha beta gamma delta : ℕ)
    (X : Matrix (Fin beta) (Fin beta) ℚ) (Y : Matrix (Fin delta) (Fin delta) ℚ)
    (BM : Matrix (Fin beta) (Fin alpha) ℚ) (DM : Matrix (Fin gamma) (Fin delta) ℚ)
    (w : Fin alpha × Fin delta → ℚ) :
    ((LinearMap.toMatrix' (cokernelEmbedding p alpha beta gamma delta)).transpose).mulVec
      ((longCross p alpha beta gamma delta X Y BM DM).mulVec
        (kernelEmbedding p alpha beta gamma delta w)) =
      (((p : ℚ)+1) • kronecker BM DM).mulVec w := by
  classical
  rw [← sourceSL_kernelEmbedding p alpha beta gamma delta w]
  funext ⟨k,j⟩
  rw [cokernel_mulVec_formula]
  simp_rw [longCross_SL_short_row p alpha beta gamma delta X Y BM DM,
    slLine_kernelEmbedding]
  have he (t : Fin (p+1)) : (p-t.val)+t.val=p := by have h := t.isLt; omega
  simp only [he,if_true,Matrix.mulVec_smul,Pi.smul_apply,smul_eq_mul]
  have hh (t : Fin (p+1)) : (-1 : ℚ)^t.val *
      ((-1 : ℚ)^(p-(p-t.val)) * (kronecker BM DM).mulVec w (k,j)) =
      (kronecker BM DM).mulVec w (k,j) := by
    have ht : p-(p-t.val)=t.val := by have h := t.isLt; omega
    rw [ht,← mul_assoc,neg_one_pow_square,one_mul]
  simp_rw [hh]
  simp [Matrix.smul_mulVec,Pi.smul_apply,smul_eq_mul,Nat.cast_add,Nat.cast_one]

private lemma longCross_kernel_long_row (p alpha beta gamma delta : ℕ)
    (X : Matrix (Fin beta) (Fin beta) ℚ) (Y : Matrix (Fin delta) (Fin delta) ℚ)
    (BM : Matrix (Fin beta) (Fin alpha) ℚ) (DM : Matrix (Fin gamma) (Fin delta) ℚ)
    (w : Fin alpha × Fin delta → ℚ)
    (i : Fin beta) (j : Fin delta) (r : Fin (p+1)) (t : Fin (p+2)) :
    (longCross p alpha beta gamma delta X Y BM DM).mulVec
      (kernelEmbedding p alpha beta gamma delta w) (⟨Sum.inr i,r⟩,⟨Sum.inr j,t⟩) =
      if r.val=p ∧ t.val=p+1 then (kronecker BM Y).mulVec w (i,j) else 0 := by
  rw [← sourceSL_kernelEmbedding p alpha beta gamma delta w,longCross_SL_long_row]
  have hline : slCorner p alpha beta gamma delta (kernelEmbedding p alpha beta gamma delta w) r =
      if r.val=p then w else 0 := by
    funext k
    change w k * (if (p-r.val)+p=p then (-1 : ℚ)^(p-r.val) else 0) = _
    have he : (p-r.val)+p=p ↔ r.val=p := by have h := r.isLt; omega
    simp only [he]
    by_cases hr : r.val=p
    · simp [hr]
    · simp [hr]
  rw [hline]
  by_cases hr : r.val=p <;> by_cases ht : t.val=p+1 <;> simp [hr,ht]

private lemma longCross_sample_LL (p alpha beta gamma delta : ℕ)
    (X : Matrix (Fin beta) (Fin beta) ℚ) (Y : Matrix (Fin delta) (Fin delta) ℚ)
    (BM : Matrix (Fin beta) (Fin alpha) ℚ) (DM : Matrix (Fin gamma) (Fin delta) ℚ)
    (u : (Σ t : Fin alpha ⊕ Fin beta, Fin (blockLength p alpha beta t + 1)) × (Σ t : Fin gamma ⊕ Fin delta, Fin (blockLength p gamma delta t)) → ℚ) :
    (fun k => (longCross p alpha beta gamma delta X Y BM DM).mulVec
      (sourceLL p alpha beta gamma delta u) (llTarget p alpha beta gamma delta k)) =
      (kronecker X Y).mulVec (fun k => u (llSource p alpha beta gamma delta k)) := by
  funext ⟨i,j⟩
  rw [llTarget,longCross_LL_long_row]
  simp

private lemma longCross_sample_kernel (p alpha beta gamma delta : ℕ)
    (X : Matrix (Fin beta) (Fin beta) ℚ) (Y : Matrix (Fin delta) (Fin delta) ℚ)
    (BM : Matrix (Fin beta) (Fin alpha) ℚ) (DM : Matrix (Fin gamma) (Fin delta) ℚ)
    (w : Fin alpha × Fin delta → ℚ) :
    (fun k => (longCross p alpha beta gamma delta X Y BM DM).mulVec
      (kernelEmbedding p alpha beta gamma delta w) (llTarget p alpha beta gamma delta k)) =
      (kronecker BM Y).mulVec w := by
  funext ⟨i,j⟩
  rw [llTarget,longCross_kernel_long_row]
  simp

end
section

open Matrix Module

private theorem long_reservoir_injective (p alpha beta gamma delta : ℕ) (hp : 0 < p)
    (X : Matrix (Fin beta) (Fin beta) ℚ) (Y : Matrix (Fin delta) (Fin delta) ℚ)
    (BM : Matrix (Fin beta) (Fin alpha) ℚ) (DM : Matrix (Fin gamma) (Fin delta) ℚ)
    (hR : IsUnit (1+kronecker X Y))
    (hS : Function.Injective ((((p : ℚ)+1) • kronecker BM DM -
      kronecker X DM * (1+kronecker X Y)⁻¹ * kronecker BM Y).mulVec)) :
    Function.Injective (widthTwoMatrix p p alpha beta gamma delta +
      longCross p alpha beta gamma delta X Y BM DM).mulVecLin := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro u hu
  change (widthTwoMatrix p p alpha beta gamma delta +
    longCross p alpha beta gamma delta X Y BM DM).mulVec u = 0 at hu
  let W := widthTwoMatrix p p alpha beta gamma delta
  let C := longCross p alpha beta gamma delta X Y BM DM
  let E := (LinearMap.toMatrix' (cokernelEmbedding p alpha beta gamma delta)).transpose
  let v : Fin beta × Fin delta → ℚ := fun k => u (llSource p alpha beta gamma delta k)
  obtain ⟨w,hw⟩ := kernel_coordinates p alpha beta gamma delta _
    (long_sourceSL_kernel_of_updated_zero p alpha beta gamma delta X Y BM DM u hu)
  have hc : C.mulVec u = C.mulVec (sourceLL p alpha beta gamma delta u) +
      C.mulVec (kernelEmbedding p alpha beta gamma delta w) := by
    rw [longCross_source_decomposition, ← hw]
  have hr : (1+kronecker X Y).mulVec v + (kronecker BM Y).mulVec w = 0 := by
    have hh := congrArg (fun z => fun k => z (llTarget p alpha beta gamma delta k)) hu
    rw [Matrix.add_mulVec, hc] at hh
    change (fun k => W.mulVec u (llTarget p alpha beta gamma delta k) +
      (C.mulVec (sourceLL p alpha beta gamma delta u) (llTarget p alpha beta gamma delta k) +
       C.mulVec (kernelEmbedding p alpha beta gamma delta w) (llTarget p alpha beta gamma delta k))) = 0 at hh
    simp only [W, old_long_reservoir_sample] at hh
    have hss := longCross_sample_LL p alpha beta gamma delta X Y BM DM u
    have hsl := longCross_sample_kernel p alpha beta gamma delta X Y BM DM w
    change _ = (kronecker X Y).mulVec v at hss
    change _ = (kronecker BM Y).mulVec w at hsl
    have heq : (fun k => v k +
      (C.mulVec (sourceLL p alpha beta gamma delta u) (llTarget p alpha beta gamma delta k) +
       C.mulVec (kernelEmbedding p alpha beta gamma delta w) (llTarget p alpha beta gamma delta k))) =
      v + ((kronecker X Y).mulVec v + (kronecker BM Y).mulVec w) := by
      rw [← hss, ← hsl]
      rfl
    rw [heq] at hh
    simpa only [Matrix.add_mulVec, Matrix.one_mulVec, add_assoc] using hh
  have he : (kronecker X DM).mulVec v + (((p : ℚ)+1) • kronecker BM DM).mulVec w = 0 := by
    have hh := congrArg E.mulVec hu
    rw [Matrix.add_mulVec, Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_zero] at hh
    change (E*W).mulVec u + E.mulVec (C.mulVec u) = 0 at hh
    rw [cokernelMatrix_mul_widthTwo, Matrix.zero_mulVec, zero_add, hc, Matrix.mulVec_add] at hh
    change ((LinearMap.toMatrix' (cokernelEmbedding p alpha beta gamma delta)).transpose).mulVec _ +
      ((LinearMap.toMatrix' (cokernelEmbedding p alpha beta gamma delta)).transpose).mulVec _ = 0 at hh
    rw [cokernel_long_LL p alpha beta gamma delta, cokernel_long_kernel] at hh
    exact hh
  obtain ⟨hv0,hw0⟩ := schur_two_equations (1+kronecker X Y) (kronecker BM Y)
    (kronecker X DM) (((p : ℚ)+1) • kronecker BM DM) hR hS v w hr he
  have hss : sourceLL p alpha beta gamma delta u = 0 := by
    apply sourceLL_zero_of_kernel
    apply sourceLL_kernel_of_rows_zero
    intro i j r t
    have hh := congrFun hu (⟨Sum.inr i,r⟩,⟨Sum.inr j,t⟩)
    rw [Matrix.add_mulVec, hc, hw0, map_zero, Matrix.mulVec_zero, add_zero] at hh
    have hcr := longCross_LL_long_row p alpha beta gamma delta X Y BM DM u i j r t
    change C.mulVec (sourceLL p alpha beta gamma delta u) (⟨Sum.inr i,r⟩,⟨Sum.inr j,t⟩) = if r.val=p ∧ t.val=p+1 then (kronecker X Y).mulVec v (i,j) else 0 at hcr
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

private theorem long_long_injective_witness (p alpha beta gamma delta : ℕ) (hp : 0 < p)
    (hA : 0 < alpha) (hAB : alpha ≤ beta) (hG : 0 < gamma) (hGD : gamma ≤ delta)
    (hdim : alpha*delta ≤ beta*gamma) :
    RationalWitness (leftDim p alpha beta) (rightDim p alpha beta)
      (leftDim p gamma delta) (rightDim p gamma delta) := by
  let X := (-backward beta).transpose
  let Y := (forwardHalf delta).transpose
  let BM := (rowSelector beta alpha).transpose
  let DM := (rowSelector delta gamma)
  let F := widthTwoMatrix p p alpha beta gamma delta + longCross p alpha beta gamma delta X Y BM DM
  have hR : IsUnit (1+kronecker X Y) := by
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    have hh := (cyclic_resolvent_lemma beta alpha delta gamma hA hAB hG hGD
      (p : ℚ) (by exact_mod_cast hp)).1
    have ht : 1+kronecker X Y = (reservoir beta delta).transpose := by
      simp only [X, Y, reservoir, Matrix.transpose_add, Matrix.transpose_one]
      rfl
    rw [ht,Matrix.det_transpose]
    exact (Matrix.isUnit_iff_isUnit_det _).mp hh
  have hS : Function.Injective ((((p : ℚ)+1) • kronecker BM DM -
      kronecker X DM * (1+kronecker X Y)⁻¹ * kronecker BM Y).mulVec) := by
    apply matrix_injective_of_rank
    have hh := long_long_cyclic_schur_rank alpha beta gamma delta p hA hAB hG hGD hp
    simpa only [X,Y,BM,DM,Fintype.card_prod,Fintype.card_fin,min_eq_left hdim] using hh
  have hi : Function.Injective F.mulVecLin := long_reservoir_injective p alpha beta gamma delta hp X Y BM DM hR hS
  have hr : F.rank = rightDim p alpha beta * leftDim p gamma delta := by
    rw [Matrix.rank,LinearMap.finrank_range_of_inj hi,Module.finrank_pi,
      Fintype.card_prod,cols_card,rows_card]
  have hu := F.rank_le_card_height
  simp only [Fintype.card_prod,rows_card,cols_card] at hu
  rw [hr] at hu
  apply witness_of_typed_slices (rows_card _ _ _) (cols_card _ _ _)
    (rows_card _ _ _) (cols_card _ _ _)
    (threeSlices (arrow0 p alpha beta) (arrow1 p alpha beta) (longThirdLeft p alpha beta X BM))
    (threeSlices (arrow0 p gamma delta).transpose (arrow1 p gamma delta).transpose
      (longThirdRight p gamma delta Y DM))
  rw [typed_three_slice_flow]
  change F.rank = _
  rw [hr,min_eq_right hu]

private theorem long_long_witness (p alpha beta gamma delta : ℕ) (hp : 0 < p)
    (hA : 0 < alpha) (hAB : alpha ≤ beta) (hG : 0 < gamma) (hGD : gamma ≤ delta) :
    RationalWitness (leftDim p alpha beta) (rightDim p alpha beta)
      (leftDim p gamma delta) (rightDim p gamma delta) := by
  rcases le_total (alpha*delta) (beta*gamma) with h | h
  · exact long_long_injective_witness p alpha beta gamma delta hp hA hAB hG hGD h
  · exact witness_swap (long_long_injective_witness p gamma delta alpha beta hp hG hGD hA hAB
      (by simpa only [mul_comm] using h))

end
section

private theorem parameterized_base_witness : ParameterizedBaseWitness := by
  intro p q alpha beta gamma delta hp hq hb hd
  change RationalWitness (leftDim p alpha beta) (rightDim p alpha beta)
    (leftDim q gamma delta) (rightDim q gamma delta)
  by_cases hpq : p=q
  · subst q
    by_cases hz : alpha*delta=0 ∨ beta*gamma=0
    · exact zero_defect_witness p alpha beta gamma delta hz
    · have ha : 0 < alpha := by
        have h : alpha*delta ≠ 0 := fun h => hz (Or.inl h)
        exact Nat.pos_of_ne_zero (fun h0 => h (by simp [h0]))
      have hg : 0 < gamma := by
        have h : beta*gamma ≠ 0 := fun h => hz (Or.inr h)
        exact Nat.pos_of_ne_zero (fun h0 => h (by simp [h0]))
      rcases le_total alpha beta with hab | hba
      · rcases le_total gamma delta with hgd | hdg
        · exact long_long_witness p alpha beta gamma delta hp ha hab hg hgd
        · exact single_reversal_witness p alpha beta gamma delta (Or.inl ⟨hab,hdg⟩)
      · rcases le_total gamma delta with hgd | hdg
        · exact single_reversal_witness p alpha beta gamma delta (Or.inr ⟨hba,hgd⟩)
        · exact short_short_witness p alpha beta gamma delta hp hb hba hd hdg
  · exact different_depth_witness p q alpha beta gamma delta hpq

theorem base_witness : BaseWitness := base_of_parameterized parameterized_base_witness

end

end D5.S3.Quantum.TensorNetworks.BridgeGraph.LongReservoir
