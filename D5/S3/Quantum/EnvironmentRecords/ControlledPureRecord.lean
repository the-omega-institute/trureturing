/- GID: D5/S3/Quantum/EnvironmentRecords/ControlledPureRecord
   generality: G
   mirror-B: D5/B/S3/Quantum/EnvironmentRecords/ControlledPureRecord
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [lake/module/D5.S3.Quantum.EnvironmentRecords, lake/module/D5.S3.Quantum.Foundation.FiniteDiamondDistance]
   utility: none
   digest: Controlled pure-record readout and its exact diamond distance from address dephasing. -/

import D5.S3.Quantum.EnvironmentRecords
import D5.S3.Quantum.Foundation.FiniteDiamondDistance
import D5.S3.Quantum.Foundation.FiniteKrausChannel
import D5.S3.Quantum.Foundation.TraceNormTensorProduct
import D5.S3.Quantum.Information.PartialTraceMutualInformation
import D5.S3.Quantum.Entanglement.PermutationCriteria.BellBlocks
import D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability
import D5.S3.Quantum.Measurement.Auric.RootTrace

/-!
# Controlled pure records and complete address dephasing

The two record vectors are stored as visible-by-hidden amplitude matrices.
A common visible density matrix fixes the diagonal address blocks. The
cross reduction controls the operational distance from complete dephasing.
-/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Quantum.EnvironmentRecords.ControlledPureRecord

open _root_.Matrix
open scoped BigOperators CStarAlgebra ComplexOrder Kronecker MatrixOrder
open scoped _root_.Matrix
open D5.S3.Quantum.Foundation.FiniteDiamondDistance
open D5.S3.Quantum.Foundation.FiniteKrausChannel (finite_kraus_quantum_channel)
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteTraceDistance
  (isometry traceNorm_add_le traceNorm_neg traceNorm_nonneg traceNorm_of_posSemidef)
open D5.S3.Quantum.Information.PartialTraceMutualInformation (partialTraceLeft partialTraceRight)
open D5.S3.Quantum.Entanglement.PermutationCriteria.NormInvariance
  (traceNorm_submatrix_equiv traceNorm_two_isometries traceNorm_conjTranspose)
open D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability (traceNorm_smul_nonneg)
open D5.S3.Quantum.Classicalization.XuImaiGuhneSimultaneousUnboundedness.Toolkit
  (traceNorm_kronecker)
open D5.S3.Quantum.Measurement.Auric.RootTrace (sqrt_direct_sum)

abbrev Address := Fin 2
abbrev Records (O E : Type*) := Address → Matrix O E ℂ

section Preparation

variable {O E : Type*} [Fintype O] [Fintype E]

/-- Insert the amplitudes into the output rows carrying the corresponding address. -/
private def embed {B : Type*} (v : Address → B → ℂ) : Matrix (Address × B) Address ℂ :=
  fun (i, b) j => if i = j then v i b else 0

private theorem embed_action {B : Type*} (v : Address → B → ℂ) (X : Matrix Address Address ℂ)
    (i j : Address) (p q : B) :
    (embed v * X * (embed v)ᴴ) (i, p) (j, q) = v i p * star (v j q) * X i j := by
  have hleft (k : Address) : (embed v * X) (i, p) k = v i p * X i k := by
    simp [Matrix.mul_apply, embed, ite_mul]
  rw [Matrix.mul_apply]
  simp only [hleft, Matrix.conjTranspose_apply]
  simp [embed, apply_ite star, mul_ite, mul_right_comm]

private theorem embed_gram {B : Type*} [Fintype B] (v : Address → B → ℂ) :
    (embed v)ᴴ * embed v = Matrix.diagonal (fun i => ∑ p, star (v i p) * v i p) := by
  ext i j
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single i]
  · by_cases hij : i = j
    · subst j
      simp [embed, Matrix.conjTranspose_apply]
    · simp [embed, Matrix.conjTranspose_apply, Matrix.diagonal_apply, hij]
  · intro k _ hki
    simp [embed, Matrix.conjTranspose_apply, hki]
  · simp

/-- The pure-record preparation sends each address basis vector to itself
tensored with its record vector. The output order is address, visible, hidden. -/
def controlledIsometry (W : Records O E) : Matrix ((Address × O) × E) Address ℂ :=
  (embed (fun i (p, e) => W i p e)).submatrix
    (Equiv.prodAssoc Address O E) id

/-- The normalization needed for an ordinary channel is unit mass in each record. -/
def Normalized (W : Records O E) : Prop :=
  ∀ i, (W i * (W i)ᴴ).trace = 1

theorem controlledIsometry_isometry (W : Records O E) (hW : Normalized W) :
    isometry (controlledIsometry W) := by
  let v : Address → O × E → ℂ := fun i (p, e) => W i p e
  have hg : (controlledIsometry W)ᴴ * controlledIsometry W = (embed v)ᴴ * embed v := by
    ext i j
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, controlledIsometry,
      Matrix.submatrix_apply, id_eq] using
      (Equiv.prodAssoc Address O E).sum_comp
        (fun b => star (embed v b i) * embed v b j)
  rw [isometry, hg, embed_gram]
  ext i j
  have hi : (∑ p : O × E, star (v i p) * v i p) = 1 := by
    rw [Fintype.sum_prod_type]
    simpa [v, Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply, mul_comm] using hW i
  rw [Matrix.diagonal_apply, Matrix.one_apply, hi]

set_option maxHeartbeats 1000000 in
/-- The joint density-matrix action before the hidden register is traced out. -/
theorem controlledIsometry_joint_apply (W : Records O E) (X : Matrix Address Address ℂ)
    (i j : Address) (p q : O) (e f : E) :
    (controlledIsometry W * X * (controlledIsometry W)ᴴ) ((i, p), e) ((j, q), f) =
      W i p e * star (W j q f) * X i j := by
  let v : Address → O × E → ℂ := fun a (x, u) => W a x u
  calc
    (controlledIsometry W * X * (controlledIsometry W)ᴴ) ((i, p), e) ((j, q), f) =
        (embed v * X * (embed v)ᴴ) (i, (p, e)) (j, (q, f)) := by
      simp only [controlledIsometry, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Matrix.submatrix_apply, Equiv.prodAssoc_apply, id_eq, v]
    _ = _ := embed_action v X i j (p, e) (q, f)

private def kraus (W : Records O E) (e : E) : Matrix (Address × O) Address ℂ :=
  embed (fun i p => W i p e)

private theorem kraus_complete (W : Records O E) (hW : Normalized W) :
    (∑ e, (kraus W e)ᴴ * kraus W e) = 1 := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.sum_apply, kraus, embed_gram, Matrix.diagonal_apply_eq,
      Matrix.one_apply_eq]
    rw [Finset.sum_comm]
    simpa [Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply, mul_comm] using hW i
  · simp only [Matrix.sum_apply, kraus, embed_gram, Matrix.diagonal_apply,
      ite_eq_right hij, Finset.sum_const_zero, Matrix.one_apply_ne hij]

/-- The matrix map obtained by tracing out the hidden record factor. -/
def readoutMap (W : Records O E) : MatrixMap Address (Address × O) ℂ :=
  MatrixMap.of_kraus (kraus W) (kraus W)

private theorem readoutMap_sum (W : Records O E) (X : Matrix Address Address ℂ) :
    readoutMap W X = ∑ e, kraus W e * X * (kraus W e)ᴴ := by
  simp only [readoutMap, MatrixMap.of_kraus, LinearMap.sum_apply, LinearMap.coe_mk,
    AddHom.coe_mk]

theorem readoutMap_apply (W : Records O E) (X : Matrix Address Address ℂ)
    (i j : Address) (p q : O) :
    readoutMap W X (i, p) (j, q) = (W i * (W j)ᴴ) p q * X i j := by
  rw [readoutMap_sum]
  simp only [Matrix.sum_apply, kraus, embed_action]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]

theorem readoutMap_eq_partialTrace (W : Records O E) (X : Matrix Address Address ℂ) :
    readoutMap W X =
      partialTraceRight (controlledIsometry W * X * (controlledIsometry W)ᴴ) := by
  ext ⟨i, p⟩ ⟨j, q⟩
  rw [readoutMap_apply]
  simp only [partialTraceRight, controlledIsometry_joint_apply]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]

/-- Tracing the visible register too leaves the scalar Gram overlap on each address entry. -/
theorem trace_visible_apply (W : Records O E) (X : Matrix Address Address ℂ) (i j : Address) :
    partialTraceRight (readoutMap W X) i j = (W i * (W j)ᴴ).trace * X i j := by
  simp only [partialTraceRight, readoutMap_apply, Matrix.trace, Matrix.diag, Finset.sum_mul]

/-- The original two-component environment rule is the case with a trivial visible factor. -/
theorem recovers_recordChannel (record : EnvironmentRecord) (X : Matrix Address Address ℂ) :
    partialTraceRight (readoutMap (O := Unit) (fun i _ e => record i e) X) =
      recordChannel record X := by
  ext i j
  let V : Records Unit Address := fun a => Matrix.of fun _ e => record a e
  change partialTraceRight (readoutMap V X) i j = recordOverlap record i j * X i j
  rw [trace_visible_apply V X i j]
  simp only [V, Matrix.trace, Matrix.diag, Fintype.sum_unique, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.of_apply, recordOverlap]

/-- Store an extra copy of the address in the traced register. -/
def withHiddenAddress (W : Records O E) : Records O (E × Address) :=
  fun i p (e, k) => if k = i then W i p e else 0

private theorem hiddenAddress_gram (W : Records O E) (i j : Address) :
    withHiddenAddress W i * (withHiddenAddress W j)ᴴ =
      if i = j then W i * (W i)ᴴ else 0 := by
  ext p q
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  by_cases h : i = j
  · subst j
    simp only [if_pos rfl, Matrix.mul_apply, Matrix.conjTranspose_apply]
    apply Finset.sum_congr rfl
    intro e _
    rw [Finset.sum_eq_single i]
    · simp [withHiddenAddress]
    · intro k _ hk
      simp [withHiddenAddress, hk]
    · simp
  · simp only [if_neg h, Matrix.zero_apply]
    apply Finset.sum_eq_zero
    intro e _
    apply Finset.sum_eq_zero
    intro k _
    by_cases hk : k = i
    · subst k
      simp [withHiddenAddress, Matrix.conjTranspose_apply, h]
    · simp [withHiddenAddress, hk]

theorem withHiddenAddress_normalized (W : Records O E) (hW : Normalized W) :
    Normalized (withHiddenAddress W) := by
  intro i
  rw [hiddenAddress_gram, if_pos rfl]
  exact hW i

/-- The ordinary CPTP channel with the actual Kraus action. -/
def readoutChannel [DecidableEq O] (W : Records O E) (hW : Normalized W) :
    QuantumChannel Address (Address × O) :=
  Classical.choose (finite_kraus_quantum_channel (kraus W) (kraus_complete W hW))

theorem readoutChannel_apply [DecidableEq O] (W : Records O E) (hW : Normalized W)
    (X : Matrix Address Address ℂ) :
    CStarMatrix.ofMatrix.symm
      ((readoutChannel W hW).toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) =
      readoutMap W X := by
  calc
    _ = ∑ e, kraus W e * X * (kraus W e)ᴴ :=
      (Classical.choose_spec
        (finite_kraus_quantum_channel (kraus W) (kraus_complete W hW))) X
    _ = _ := (readoutMap_sum W X).symm

theorem dephased_apply (W : Records O E) (R : Matrix O O ℂ)
    (hR : ∀ i, W i * (W i)ᴴ = R) (X : Matrix Address Address ℂ)
    (i j : Address) (p q : O) :
    readoutMap (withHiddenAddress W) X (i, p) (j, q) =
      if i = j then R p q * X i i else 0 := by
  rw [readoutMap_apply, hiddenAddress_gram]
  by_cases h : i = j
  · subst j
    simp [hR]
  · simp [h]

/-- Discarding the address yields the same visible output for the two maps. -/
theorem visible_agreement (W : Records O E) (R : Matrix O O ℂ)
    (hR : ∀ i, W i * (W i)ᴴ = R) (X : Matrix Address Address ℂ) :
    partialTraceLeft (readoutMap W X) = X.trace • R ∧
      partialTraceLeft (readoutMap (withHiddenAddress W) X) = X.trace • R := by
  have hs (p q : O) : (∑ i : Address, R p q * X i i) = (∑ i : Address, X i i) * R p q := by
    rw [← Finset.mul_sum, mul_comm]
  constructor
  · ext p q
    simp only [partialTraceLeft, readoutMap_apply, hR, Matrix.trace, Matrix.diag,
      Matrix.smul_apply, smul_eq_mul]
    exact hs p q
  · ext p q
    simp only [partialTraceLeft, dephased_apply W R hR, if_pos rfl, Matrix.trace,
      Matrix.diag, Matrix.smul_apply, smul_eq_mul]
    exact hs p q

/-- The cross reduction is the operator multiplying the 01 address block. -/
def cross (W : Records O E) : Matrix O O ℂ := W 0 * (W 1)ᴴ

private theorem cross_adjoint (W : Records O E) :
    (cross W)ᴴ = W 1 * (W 0)ᴴ := by
  simp [cross, Matrix.conjTranspose_mul]

private theorem difference_apply (W : Records O E) (X : Matrix Address Address ℂ)
    (i j : Address) (p q : O) :
    (readoutMap W X - readoutMap (withHiddenAddress W) X) (i, p) (j, q) =
      if i = j then 0 else (W i * (W j)ᴴ) p q * X i j := by
  simp only [Matrix.sub_apply, readoutMap_apply, hiddenAddress_gram]
  by_cases h : i = j
  · subst j
    simp
  · simp [h]

end Preparation

section TraceNorm

variable {b : Type*} [Fintype b] [DecidableEq b]

private theorem traceNorm_offDiagonal (B C : Matrix b b ℂ) :
    Foundation.FiniteTraceDistance.traceNorm (fromBlocks 0 B C 0) =
      Foundation.FiniteTraceDistance.traceNorm B + Foundation.FiniteTraceDistance.traceNorm C := by
  have hB : 0 ≤ Bᴴ * B := (Matrix.posSemidef_conjTranspose_mul_self B).nonneg
  have hC : 0 ≤ Cᴴ * C := (Matrix.posSemidef_conjTranspose_mul_self C).nonneg
  have hgram : (fromBlocks 0 B C 0)ᴴ * fromBlocks 0 B C 0 =
      fromBlocks (Cᴴ * C) 0 0 (Bᴴ * B) := by
    simp [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
  unfold Foundation.FiniteTraceDistance.traceNorm
  rw [hgram, sqrt_direct_sum _ _ hC hB]
  change (fromBlocks (CFC.sqrt (Cᴴ * C)) 0 0 (CFC.sqrt (Bᴴ * B))).trace.re =
    (CFC.sqrt (Bᴴ * B)).trace.re + (CFC.sqrt (Cᴴ * C)).trace.re
  simp only [Matrix.trace, Matrix.diag, Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁,
    Matrix.fromBlocks_apply₂₂, Complex.add_re, add_comm]

private theorem offDiagonal_le (A B C D : Matrix b b ℂ) :
    Foundation.FiniteTraceDistance.traceNorm B + Foundation.FiniteTraceDistance.traceNorm C ≤
      Foundation.FiniteTraceDistance.traceNorm (fromBlocks A B C D) := by
  let X := fromBlocks A B C D
  let Z : Matrix (b ⊕ b) (b ⊕ b) ℂ := fromBlocks 1 0 0 (-1)
  let Y : Matrix (b ⊕ b) (b ⊕ b) ℂ := fromBlocks 0 B C 0
  have hZstar : Zᴴ = Z := by
    simp [Z, Matrix.fromBlocks_conjTranspose]
  have hZ : Zᴴ * Z = 1 := by
    rw [hZstar]
    simp [Z, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]
  have h₂ : X + -(Z * X * Zᴴ) = ((2 : ℝ) : ℂ) • Y := by
    rw [hZstar, show ((2 : ℝ) : ℂ) = 2 by norm_num]
    simp [Z, X, Y, Matrix.fromBlocks_multiply, Matrix.fromBlocks_neg,
      Matrix.fromBlocks_add, Matrix.fromBlocks_smul, two_smul]
  have h := traceNorm_add_le X (-(Z * X * Zᴴ))
  rw [h₂, traceNorm_neg, traceNorm_two_isometries X Z Z hZ hZ] at h
  change Foundation.FiniteTraceDistance.traceNorm (((2 : ℝ) : ℂ) • fromBlocks 0 B C 0) ≤
    Foundation.FiniteTraceDistance.traceNorm X + Foundation.FiniteTraceDistance.traceNorm X at h
  rw [traceNorm_smul_nonneg _ 2 (by norm_num), traceNorm_offDiagonal B C] at h
  change Foundation.FiniteTraceDistance.traceNorm B + Foundation.FiniteTraceDistance.traceNorm C ≤
    Foundation.FiniteTraceDistance.traceNorm X
  linarith

end TraceNorm

section Distance

variable {O E r : Type} [Fintype O] [DecidableEq O] [Fintype E]
  [Fintype r] [DecidableEq r]

private def addressOrder (b : Type*) : b ⊕ b ≃ Address × b where
  toFun := Sum.elim (fun s => (0, s)) (fun s => (1, s))
  invFun := fun (i, s) => if i = 0 then Sum.inl s else Sum.inr s
  left_inv := by intro s; cases s <;> simp
  right_inv := by rintro ⟨i, s⟩; fin_cases i <;> rfl

private def inputOrder (r : Type*) : r ⊕ r ≃ r × Address :=
  (addressOrder r).trans (Equiv.prodComm Address r)

private def outputOrder (r O : Type*) : (r × O) ⊕ (r × O) ≃ r × (Address × O) :=
  (addressOrder (r × O)).trans
    ((Equiv.prodAssoc Address r O).symm.trans
      ((Equiv.prodCongr (Equiv.prodComm Address r) (Equiv.refl O)).trans
        (Equiv.prodAssoc r Address O)))

private theorem input_blocks (X : Matrix (r × Address) (r × Address) ℂ) :
    X.submatrix (inputOrder r) (inputOrder r) = fromBlocks
      (Matrix.of fun s t => X (s, 0) (t, 0)) (Matrix.of fun s t => X (s, 0) (t, 1))
      (Matrix.of fun s t => X (s, 1) (t, 0)) (Matrix.of fun s t => X (s, 1) (t, 1)) := by
  ext s t
  cases s <;> cases t <;> rfl

private theorem reference_apply (W : Records O E) (hW : Normalized W)
    (X : Matrix (r × Address) (r × Address) ℂ) (s t : r) (i j : Address) (p q : O) :
    CStarMatrix.ofMatrix.symm
      (referenceAction (readoutChannel W hW) (CStarMatrix.ofMatrix X)) (s, (i, p)) (t, (j, q)) =
        readoutMap W (Matrix.of fun u v => X (s, u) (t, v)) (i, p) (j, q) := by
  let B : Matrix Address Address ℂ := Matrix.of fun u v => X (s, u) (t, v)
  change CStarMatrix.ofMatrix.symm
    ((readoutChannel W hW).toCompletelyPositiveMap (CStarMatrix.ofMatrix B)) (i, p) (j, q) = _
  exact congrArg (fun M : Matrix (Address × O) (Address × O) ℂ => M (i, p) (j, q))
    (readoutChannel_apply W hW B)

/-- The amplified difference of the ordinary channels, with the reference first. -/
def referenceDifference (W : Records O E) (hW : Normalized W)
    (X : Matrix (r × Address) (r × Address) ℂ) :
    Matrix (r × (Address × O)) (r × (Address × O)) ℂ :=
  CStarMatrix.ofMatrix.symm
      (referenceAction (readoutChannel W hW) (CStarMatrix.ofMatrix X)) -
    CStarMatrix.ofMatrix.symm
      (referenceAction (readoutChannel (withHiddenAddress W) (withHiddenAddress_normalized W hW))
        (CStarMatrix.ofMatrix X))

private theorem referenceDifference_apply (W : Records O E) (hW : Normalized W)
    (X : Matrix (r × Address) (r × Address) ℂ) (s t : r) (i j : Address) (p q : O) :
    referenceDifference W hW X (s, (i, p)) (t, (j, q)) =
      if i = j then 0 else (W i * (W j)ᴴ) p q * X (s, i) (t, j) := by
  simp only [referenceDifference, Matrix.sub_apply, reference_apply]
  simpa only [Matrix.sub_apply, Matrix.of_apply] using
    difference_apply W (Matrix.of fun u v => X (s, u) (t, v)) i j p q

private theorem referenceDifference_blocks (W : Records O E) (hW : Normalized W)
    (X : Matrix (r × Address) (r × Address) ℂ) :
    (referenceDifference W hW X).submatrix (outputOrder r O) (outputOrder r O) =
      fromBlocks 0
        ((Matrix.of fun s t => X (s, 0) (t, 1)) ⊗ₖ cross W)
        ((Matrix.of fun s t => X (s, 1) (t, 0)) ⊗ₖ (cross W)ᴴ) 0 := by
  ext u v
  rcases u with ⟨s, p⟩ | ⟨s, p⟩ <;> rcases v with ⟨t, q⟩ | ⟨t, q⟩
  · change referenceDifference W hW X (s, (0, p)) (t, (0, q)) = 0
    simp [referenceDifference_apply]
  · change referenceDifference W hW X (s, (0, p)) (t, (1, q)) =
      X (s, 0) (t, 1) * cross W p q
    simp [referenceDifference_apply, cross, mul_comm]
  · change referenceDifference W hW X (s, (1, p)) (t, (0, q)) =
      X (s, 1) (t, 0) * (cross W)ᴴ p q
    rw [referenceDifference_apply, ite_eq_right (by decide : (1 : Address) ≠ 0),
      cross_adjoint W]
    exact mul_comm _ _
  · change referenceDifference W hW X (s, (1, p)) (t, (1, q)) = 0
    simp [referenceDifference_apply]

/-- On every complex input matrix, the amplified difference has norm equal to
the trace norm of the cross reduction times the sum of the two input coherence norms. -/
theorem referenceDifference_norm (W : Records O E) (hW : Normalized W)
    (X : Matrix (r × Address) (r × Address) ℂ) :
    Foundation.FiniteTraceDistance.traceNorm (referenceDifference W hW X) =
      Foundation.FiniteTraceDistance.traceNorm (cross W) *
        (Foundation.FiniteTraceDistance.traceNorm (Matrix.of fun s t => X (s, 0) (t, 1)) +
          Foundation.FiniteTraceDistance.traceNorm (Matrix.of fun s t => X (s, 1) (t, 0))) := by
  rw [← traceNorm_submatrix_equiv _ (outputOrder r O) (outputOrder r O),
    referenceDifference_blocks, traceNorm_offDiagonal, traceNorm_kronecker,
    traceNorm_kronecker, traceNorm_conjTranspose]
  ring

/-- The induced trace-norm upper bound holds at every finite reference dimension. -/
theorem referenceDifference_le (W : Records O E) (hW : Normalized W)
    (X : Matrix (r × Address) (r × Address) ℂ) :
    Foundation.FiniteTraceDistance.traceNorm (referenceDifference W hW X) ≤
      Foundation.FiniteTraceDistance.traceNorm (cross W) *
        Foundation.FiniteTraceDistance.traceNorm X := by
  rw [referenceDifference_norm]
  apply mul_le_mul_of_nonneg_left _ (traceNorm_nonneg _)
  rw [← traceNorm_submatrix_equiv X (inputOrder r) (inputOrder r), input_blocks]
  exact offDiagonal_le _ _ _ _

private def plusAmplitude : Address → ℂ := fun _ => (Real.sqrt (1 / 2 : ℝ) : ℂ)

private theorem plusAmplitude_mul_star (i j : Address) :
    plusAmplitude i * star (plusAmplitude j) = (1 / 2 : ℂ) := by
  rw [show star (plusAmplitude j) = plusAmplitude i by
    simp [plusAmplitude, Complex.star_def]]
  change (Real.sqrt (1 / 2 : ℝ) : ℂ) * (Real.sqrt (1 / 2 : ℝ) : ℂ) = _
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 2)] <;> norm_num

/-- The balanced address superposition. -/
def plusState : DensityState Address :=
  pureState plusAmplitude (by
    change (∑ i : Address, star (plusAmplitude i) * plusAmplitude i) = 1
    calc
      _ = ∑ _ : Address, (1 / 2 : ℂ) := by
        apply Finset.sum_congr rfl
        intro i _
        calc
          _ = plusAmplitude i * star (plusAmplitude i) := mul_comm _ _
          _ = _ := plusAmplitude_mul_star i i
      _ = _ := by norm_num [Fin.sum_univ_two])

private theorem plusState_apply (i j : Address) :
    CStarMatrix.ofMatrix.symm plusState.1 i j = (1 / 2 : ℂ) := by
  change plusAmplitude i * star (plusAmplitude j) = _
  exact plusAmplitude_mul_star i j

/-- Pair the balanced address state with any finite reference state. -/
def productInput (σ : DensityState r) : DensityState (r × Address) :=
  let S := CStarMatrix.ofMatrix.symm σ.1
  let P := CStarMatrix.ofMatrix.symm plusState.1
  ⟨CStarMatrix.ofMatrix (S ⊗ₖ P),
    map_nonneg CStarMatrix.ofMatrixStarAlgEquiv
      ((Matrix.nonneg_iff_posSemidef.mp
        (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm σ.nonnegative)).kronecker
        (Matrix.nonneg_iff_posSemidef.mp
          (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm plusState.nonnegative))).nonneg,
    by
      change (S ⊗ₖ P).trace = 1
      rw [Matrix.trace_kronecker]
      change (Matrix.trace σ.1) * (Matrix.trace plusState.1) = 1
      simp⟩

private theorem density_traceNorm {a : Type*} [Fintype a] [DecidableEq a] (ρ : DensityState a) :
    Foundation.FiniteTraceDistance.traceNorm (CStarMatrix.ofMatrix.symm ρ.1) = 1 := by
  have hp : (CStarMatrix.ofMatrix.symm ρ.1).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp
      (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm ρ.nonnegative)
  have h := congrArg Complex.re (traceNorm_of_posSemidef hp)
  change Foundation.FiniteTraceDistance.traceNorm (CStarMatrix.ofMatrix.symm ρ.1) =
    (CStarMatrix.ofMatrix.symm ρ.1).trace.re at h
  have ht : (CStarMatrix.ofMatrix.symm ρ.1).trace = 1 := ρ.trace_eq_one
  simpa only [ht, Complex.one_re] using h

/-- A product input attains the bound for every reference density state. -/
theorem referenceDifference_product (W : Records O E) (hW : Normalized W) (σ : DensityState r) :
    Foundation.FiniteTraceDistance.traceNorm
      (referenceDifference W hW (CStarMatrix.ofMatrix.symm (productInput σ).1)) =
      Foundation.FiniteTraceDistance.traceNorm (cross W) := by
  have hblock (i j : Address) :
      (Matrix.of fun s t => CStarMatrix.ofMatrix.symm (productInput σ).1 (s, i) (t, j)) =
        ((1 / 2 : ℝ) : ℂ) • CStarMatrix.ofMatrix.symm σ.1 := by
    ext s t
    change CStarMatrix.ofMatrix.symm σ.1 s t * CStarMatrix.ofMatrix.symm plusState.1 i j =
      ((1 / 2 : ℝ) : ℂ) * CStarMatrix.ofMatrix.symm σ.1 s t
    rw [plusState_apply, mul_comm] <;> norm_num
  rw [referenceDifference_norm, hblock 0 1, hblock 1 0,
    traceNorm_smul_nonneg _ (1 / 2) (by norm_num), density_traceNorm]
  ring

/-- The balanced address state already attains the distance without a reference. -/
theorem readoutDifference_plus (W : Records O E) :
    Foundation.FiniteTraceDistance.traceNorm (readoutMap W (CStarMatrix.ofMatrix.symm plusState.1) -
        readoutMap (withHiddenAddress W) (CStarMatrix.ofMatrix.symm plusState.1)) =
      Foundation.FiniteTraceDistance.traceNorm (cross W) := by
  let X := CStarMatrix.ofMatrix.symm plusState.1
  let D := readoutMap W X - readoutMap (withHiddenAddress W) X
  let c : ℝ := 1 / 2
  have hcCast : (c : ℂ) = (1 / 2 : ℂ) := by norm_num [c]
  have hD : D.submatrix (addressOrder O) (addressOrder O) =
      fromBlocks 0 ((c : ℂ) • cross W) ((c : ℂ) • (cross W)ᴴ) 0 := by
    ext u v
    rcases u with p | p <;> rcases v with q | q
    · change (readoutMap W X - readoutMap (withHiddenAddress W) X) (0, p) (0, q) = 0
      rw [difference_apply W X 0 0 p q, ite_eq_left rfl]
    · change D (0, p) (1, q) = (c : ℂ) * cross W p q
      simp only [D, difference_apply, if_neg (by decide : (0 : Address) ≠ 1)]
      simp [X, hcCast, plusState_apply, cross, mul_comm]
    · change D (1, p) (0, q) = (c : ℂ) * (cross W)ᴴ p q
      simp only [D, difference_apply, ite_eq_right (by decide : (1 : Address) ≠ 0),
        X, hcCast, plusState_apply, cross_adjoint, mul_comm]
    · change (readoutMap W X - readoutMap (withHiddenAddress W) X) (1, p) (1, q) = 0
      rw [difference_apply W X 1 1 p q, ite_eq_left rfl]
  change Foundation.FiniteTraceDistance.traceNorm D = _
  have hc : 0 ≤ c := by norm_num [c]
  rw [← traceNorm_submatrix_equiv D (addressOrder O) (addressOrder O), hD, traceNorm_offDiagonal,
    traceNorm_smul_nonneg (cross W) c hc, traceNorm_smul_nonneg (cross W)ᴴ c hc,
    traceNorm_conjTranspose]
  dsimp [c]
  ring

/-- A single reconstructed output on the balanced input incurs at least half
the two candidate outputs' separation in the worst case. -/
theorem reconstruction_lower (W : Records O E) (Y : Matrix (Address × O) (Address × O) ℂ) :
    let X := CStarMatrix.ofMatrix.symm plusState.1
    Foundation.FiniteTraceDistance.traceNorm (cross W) / 2 ≤
      max (Foundation.FiniteTraceDistance.traceNorm (readoutMap W X - Y))
        (Foundation.FiniteTraceDistance.traceNorm (readoutMap (withHiddenAddress W) X - Y)) := by
  dsimp only
  let X := CStarMatrix.ofMatrix.symm plusState.1
  let N := readoutMap W X
  let D := readoutMap (withHiddenAddress W) X
  have h := traceNorm_add_le (N - Y) (Y - D)
  rw [show N - Y + (Y - D) = N - D by abel,
    show Y - D = -(D - Y) by abel, traceNorm_neg] at h
  have he : Foundation.FiniteTraceDistance.traceNorm (N - D) =
      Foundation.FiniteTraceDistance.traceNorm (cross W) := readoutDifference_plus W
  rw [he] at h
  change Foundation.FiniteTraceDistance.traceNorm (cross W) / 2 ≤
    max (Foundation.FiniteTraceDistance.traceNorm (N - Y))
      (Foundation.FiniteTraceDistance.traceNorm (D - Y))
  linarith [le_max_left (Foundation.FiniteTraceDistance.traceNorm (N - Y))
      (Foundation.FiniteTraceDistance.traceNorm (D - Y)),
    le_max_right (Foundation.FiniteTraceDistance.traceNorm (N - Y))
      (Foundation.FiniteTraceDistance.traceNorm (D - Y))]

/-- Exact unhalved distance in the ordinary finite diamond distance API. -/
theorem diamondDistance_readout_dephased (W : Records O E) (hW : Normalized W) :
    diamondDistance (readoutChannel W hW)
      (readoutChannel (withHiddenAddress W) (withHiddenAddress_normalized W hW)) =
      Foundation.FiniteTraceDistance.traceNorm (cross W) := by
  let N := readoutChannel W hW
  let D := readoutChannel (withHiddenAddress W) (withHiddenAddress_normalized W hW)
  let values := {0} ∪ {x : ℝ | ∃ n : ℕ, ∃ ρ : DensityState (Fin n × Address),
    x = referenceError N D ρ}
  have herror (n : ℕ) (ρ : DensityState (Fin n × Address)) :
      referenceError N D ρ =
        Foundation.FiniteTraceDistance.traceNorm
          (referenceDifference W hW (CStarMatrix.ofMatrix.symm ρ.1)) := by
    change Foundation.FiniteTraceDistance.traceNorm
      (CStarMatrix.ofMatrix.symm (referenceAction N ρ.1) -
        CStarMatrix.ofMatrix.symm (referenceAction D ρ.1)) = _
    simp only [referenceDifference, Equiv.apply_symm_apply, N, D]
  have hupper : ∀ x ∈ values, x ≤ Foundation.FiniteTraceDistance.traceNorm (cross W) := by
    intro x hx
    rcases hx with hx | ⟨n, ρ, rfl⟩
    · rw [Set.mem_singleton_iff.mp hx]
      exact traceNorm_nonneg _
    · rw [herror n ρ]
      simpa only [density_traceNorm, mul_one] using
        referenceDifference_le W hW (CStarMatrix.ofMatrix.symm ρ.1)
  let σ : DensityState (Fin 1) := pureState (fun _ => 1) (by
    change (∑ _ : Fin 1, star (1 : ℂ) * 1) = 1
    simp only [Fin.sum_univ_one, star_one, one_mul])
  have hmem : Foundation.FiniteTraceDistance.traceNorm (cross W) ∈ values :=
    Or.inr ⟨1, productInput σ,
      ((herror 1 (productInput σ)).trans (referenceDifference_product W hW σ)).symm⟩
  change sSup values = _
  exact le_antisymm (csSup_le ⟨_, hmem⟩ hupper)
    (le_csSup ⟨_, hupper⟩ hmem)

end Distance

end D5.S3.Quantum.EnvironmentRecords.ControlledPureRecord
