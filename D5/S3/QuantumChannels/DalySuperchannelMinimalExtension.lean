/- GID: D5/S3/QuantumChannels/DalySuperchannelMinimalExtension
   generality: I
   mirror-B: D5/B/S3/QuantumChannels/DalySuperchannelMinimalExtension
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/QuantumChannels/DalySuperchannelMinimalExtension.claim; result=D5/S3/QuantumChannels/DalySuperchannelMinimalExtension.result; claim=D5/S3/QuantumChannels/DalySuperchannelMinimalExtension.claim
   digest: A two-qubit QSC has full-rank extensions and a non-extreme minimizing extension. -/

/-
proof_shape: result: content
escape_witness: Rank.coherent_block_full_rank
admission_basis: open-problem-resolution (#19620; Refuted)
Direct frozen dependencies:
D5/S3/Quantum/Foundation/FiniteKrausChannel.IsCompletelyPositive [sha256:31bd68fc3c839750d1a8ac1474555b08fcd9579b1627c81db36a58f3172e1252]
D5/S3/Quantum/Foundation/FiniteKrausChannel.MatrixMap [sha256:df01dcc9d6d91985f3214eaee7e1c5eacebab3335dff64bb7b620043c650cad7]
D5/S3/Quantum/Foundation/FiniteKrausChannel.add_kron [sha256:7c8b4efef5a5a7662187d5af3f0c14db61d89ecc96590ea5ba5d0d8e22e54d35]
D5/S3/Quantum/Foundation/FiniteKrausChannel.kron [sha256:6bbbe42180d7cde8ee171b8a1aeeb16449194862345f2042d95ec7c0b2055471]
D5/S3/Quantum/Foundation/FiniteKrausChannel.kron_def [sha256:0a066df1b1de64e4fda175d1ac776d744674a6465abc8a7f13b12f185ce29405]
D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceLeft [sha256:68653a556c9228bbd8018884585aa56fe5fce5cd40b4a12a493f4aa319c78f5d]
D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceRight [sha256:8fd00cbe799f3e8a3163a296b2ad235e0a251e3e79b744b52197ba12d0343f77]
D5/S3/Quantum/QuantumChannels/PositiveFilterTransposeRefutation.IsPositive [sha256:7a4695f661932a0a47c32fdeeb85ddd0bb0229f782a9050b66d85174520afa2a]
D5/S3/Quantum/Recovery/LiJiangPolarPairOptimalityRefutation.inputFirstChoi [sha256:7620ae518a39944b6825fd260cd713177187b28856493804968f5ddc77f33bd0]
D5/S3/Quantum/Reduction/IsometricCompression.compress [sha256:ece129ea3121d41eb72b96831bf50f675e9fccf3bae2b5d39dc556c28adb9beb]

The Choi map and its equivalence use the matrix-unit action and double-sum
inverse. The proofs use inputFirstChoi for that action. The consumed adapter
cp_iff_choi applies MatrixMap.choi_PSD_iff_CP_map from FiniteKrausRepresentation
and transports positive semidefiniteness through Equiv.prodComm; cp_amplify
applies MatrixMap.IsCompletelyPositive.of_Fintype from the same owner.
The public result is the designated refutation result (`basis=refutes`) and is
exempt from four-slot escape registration (CLAUDE.md §3.9).

Declaration classifications (bind-only witnesses are none; consumers are direct):
proof_shape: cp_iff_choi: bind-only; consumer: cp_induced_preserving, entangled_cp, preserving_cp_induced, coherence_channel, ftilde_cp_of_diagonal, all_extensions_e
proof_shape: choi_kron: bind-only; consumer: shuffled_naturality, entangled_shuffled
proof_shape: kronLift_tmul: bind-only; consumer: shuffled_naturality, entangled_shuffled
proof_shape: choi_induced_apply: bind-only; consumer: shuffled_naturality, cp_induced_preserving, super_quantum, extension_fixed_unit
proof_shape: matrixMap_expand: bind-only; consumer: kron_apply_kronecker
proof_shape: kron_apply_kronecker: bind-only; consumer: shuffled_naturality
proof_shape: shuffled_naturality: bind-only; consumer: cp_induced_preserving, preserving_cp_induced
proof_shape: cp_amplify: bind-only; consumer: cp_induced_preserving
proof_shape: cp_induced_preserving: bind-only; consumer: super_quantum
proof_shape: choi_ofChoi: bind-only; consumer: entangled_shuffled, extension_fixed_unit
proof_shape: entangled_shuffled: bind-only; consumer: entangled_cp, preserving_cp_induced
proof_shape: entangled_cp: bind-only; consumer: preserving_cp_induced
proof_shape: preserving_cp_induced: bind-only; consumer: all_extensions_e
proof_shape: induced_super: bind-only; consumer: super_quantum, extension_fixed_unit
proof_shape: ftilde_midpoint: bind-only; consumer: super_midpoint
proof_shape: ftilde_distinct: bind-only; consumer: super_distinct
proof_shape: super_midpoint: bind-only; consumer: super_not_extreme
proof_shape: super_distinct: bind-only; consumer: super_not_extreme
proof_shape: super_not_extreme: bind-only; consumer: result
proof_shape: tp_iff_choi: bind-only; consumer: coherence_channel, super_quantum, charge_zero_on_span
proof_shape: coherence_psd: bind-only; consumer: coherence_channel
proof_shape: coherence_tp: bind-only; consumer: coherence_channel
proof_shape: coherence_channel: bind-only; consumer: offdiagonal_in_span
proof_shape: offdiagonal_in_span: bind-only; consumer: extension_fixed_unit
proof_shape: quantum_maps_span: bind-only; consumer: quantum_restriction, gamma, gamma_qsc
proof_shape: quantum_restriction: bind-only; consumer: gamma_qsc
proof_shape: bell_psd: bind-only; consumer: coherentK_posDef, ftilde_cp_of_diagonal
proof_shape: coherentK_posDef: bind-only; consumer: ftilde_cp_of_diagonal, all_extensions_e
proof_shape: choi_ftilde_decomposition: bind-only; consumer: ftilde_cp_of_diagonal
proof_shape: ftilde_cp_of_diagonal: bind-only; consumer: ftilde_cp
proof_shape: diagonalJ_nonneg: bind-only; consumer: ftilde_cp
proof_shape: ftilde_cp: bind-only; consumer: super_quantum
proof_shape: trace_of_tp_readout: bind-only; consumer: ftilde_tp_readout, charge_zero_on_span
proof_shape: ftilde_tp_readout: bind-only; consumer: super_quantum
proof_shape: super_quantum: bind-only; consumer: gamma, gamma_qsc, super_extension
proof_shape: charge_zero_on_span: bind-only; consumer: super_agrees_on_span
proof_shape: super_agrees_on_span: bind-only; consumer: super_extension
proof_shape: gamma_qsc: bind-only; consumer: result
proof_shape: super_extension: bind-only; consumer: result
proof_shape: Rank.compression_apply: bind-only; consumer: Rank.trace_compression, Rank.coherent_block_full_rank
proof_shape: Rank.compression_psd: bind-only; consumer: Rank.coherent_block_full_rank
proof_shape: Rank.trace_compression: bind-only; consumer: Rank.coherent_block_full_rank
proof_shape: Rank.coherent_block_full_rank: content; escape_witness: Rank.coherent_block_full_rank; consumer: all_extensions_e
proof_shape: extension_fixed_unit: bind-only; consumer: extension_fixed_coherence
proof_shape: extension_fixed_coherence: bind-only; consumer: all_extensions_e
proof_shape: all_extensions_e: content; escape_witness: Rank.coherent_block_full_rank; consumer: result
-/

import D5.S3.Quantum.Recovery.LiJiangPolarPairOptimalityRefutation
import D5.S3.Quantum.QuantumChannels.PositiveFilterTransposeRefutation
import D5.S3.Quantum.Foundation.FiniteKrausChannel
import D5.S3.Quantum.Foundation.FiniteKrausRepresentation
import D5.S3.Quantum.Information.PartialTraceMutualInformation
import D5.S3.Quantum.Reduction.IsometricCompression

set_option backward.isDefEq.respectTransparency false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

open D5.S3.Quantum.Information.PartialTraceMutualInformation (partialTraceLeft)

namespace D5.S3.QuantumChannels.DalySuperchannelMinimalExtension

open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
open D5.S3.Quantum.Recovery.LiJiangPolarPairOptimalityRefutation (inputFirstChoi)
open D5.S3.Quantum.Information.PartialTraceMutualInformation (partialTraceLeft)
open scoped TensorProduct

/-- Definition 3.1: `SCPTP(d, r) = span {φ | φ : M_d → M_r is a CPTP map} ⊂ L(M_d, M_r)`. -/
noncomputable def SCPTP (d r : ℕ) : Submodule ℂ (MatrixMap (Fin d) (Fin r) ℂ) :=
  Submodule.span ℂ {φ | φ.IsCompletelyPositive ∧ ∀ X, (φ X).trace = X.trace}

/-- The tensor product of linear maps `φ ⊗ ψ` as a map on the tensor product of the spaces
(Remark 3.3), bilinear in `(φ, ψ)`. -/
noncomputable def kronBilin {A B C D : Type*} [Fintype A] [DecidableEq A] [Fintype B]
    [Fintype C] [DecidableEq C] [Fintype D] :
    MatrixMap A B ℂ →ₗ[ℂ] MatrixMap C D ℂ →ₗ[ℂ] MatrixMap (A × C) (B × D) ℂ :=
  LinearMap.mk₂ ℂ MatrixMap.kron
    (fun φ₁ φ₂ ψ => MatrixMap.add_kron φ₁ φ₂ ψ)
    (fun c φ ψ => by
      ext M ⟨b₁, d₁⟩ ⟨b₂, d₂⟩
      simp only [MatrixMap.kron_def, LinearMap.smul_apply, Matrix.smul_apply, smul_eq_mul,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)
    (fun φ ψ₁ ψ₂ => by
      ext M ⟨b₁, d₁⟩ ⟨b₂, d₂⟩
      simp only [MatrixMap.kron_def, LinearMap.add_apply, Matrix.add_apply, mul_add, add_mul,
        Finset.sum_add_distrib])
    (fun c φ ψ => by
      ext M ⟨b₁, d₁⟩ ⟨b₂, d₂⟩
      simp only [MatrixMap.kron_def, LinearMap.smul_apply, Matrix.smul_apply, smul_eq_mul,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)

/-- The inclusion of `L(M_a, M_b) ⊗ L(M_c, M_d)` in `L(M_a ⊗ M_c, M_b ⊗ M_d)` (Remark 3.3). -/
noncomputable def kronLift {A B C D : Type*} [Fintype A] [DecidableEq A] [Fintype B]
    [Fintype C] [DecidableEq C] [Fintype D] :
    MatrixMap A B ℂ ⊗[ℂ] MatrixMap C D ℂ →ₗ[ℂ] MatrixMap (A × C) (B × D) ℂ :=
  TensorProduct.lift kronBilin

/-- Definition 3.4: a QSC `Γ : SCPTP(d₁, r₁) → SCPTP(d₂, r₂)`. -/
def IsQSC {d₁ r₁ d₂ r₂ : ℕ} (Γ : SCPTP d₁ r₁ →ₗ[ℂ] SCPTP d₂ r₂) : Prop :=
  (∀ φ : SCPTP d₁ r₁,
      ((φ : MatrixMap (Fin d₁) (Fin r₁) ℂ).IsCompletelyPositive ∧
        ∀ X, ((φ : MatrixMap (Fin d₁) (Fin r₁) ℂ) X).trace = X.trace) →
      ((Γ φ : MatrixMap (Fin d₂) (Fin r₂) ℂ).IsCompletelyPositive ∧
        ∀ X, ((Γ φ : MatrixMap (Fin d₂) (Fin r₂) ℂ) X).trace = X.trace)) ∧
  ∀ d₃ r₃ : ℕ, ∀ t : SCPTP d₁ r₁ ⊗[ℂ] SCPTP d₃ r₃,
    (kronLift (TensorProduct.map (SCPTP d₁ r₁).subtype (SCPTP d₃ r₃).subtype t)).IsCompletelyPositive →
    (kronLift (TensorProduct.map (SCPTP d₂ r₂).subtype (SCPTP d₃ r₃).subtype
      (TensorProduct.map Γ LinearMap.id t))).IsCompletelyPositive

/-- Remark 3.7: a quantum superchannel `S : L(M_{d₁}, M_{r₁}) → L(M_{d₂}, M_{r₂})`. -/
def IsQuantumSuperchannel {d₁ r₁ d₂ r₂ : ℕ}
    (S : MatrixMap (Fin d₁) (Fin r₁) ℂ →ₗ[ℂ] MatrixMap (Fin d₂) (Fin r₂) ℂ) : Prop :=
  (∀ φ : MatrixMap (Fin d₁) (Fin r₁) ℂ, φ.IsCompletelyPositive → (S φ).IsCompletelyPositive) ∧
  (∀ d r : ℕ, ∀ t : MatrixMap (Fin d₁) (Fin r₁) ℂ ⊗[ℂ] MatrixMap (Fin d) (Fin r) ℂ,
    (kronLift t).IsCompletelyPositive →
      (kronLift (TensorProduct.map S LinearMap.id t)).IsCompletelyPositive) ∧
  ∀ φ : MatrixMap (Fin d₁) (Fin r₁) ℂ, (∀ X, (φ X).trace = X.trace) →
    ∀ X, (S φ X).trace = X.trace

/-- The superchannel extensions of a QSC `Γ` (Theorem 3.8, Remark 4.1). -/
def extensions {d₁ r₁ d₂ r₂ : ℕ} (Γ : SCPTP d₁ r₁ →ₗ[ℂ] SCPTP d₂ r₂) :
    Set (MatrixMap (Fin d₁) (Fin r₁) ℂ →ₗ[ℂ] MatrixMap (Fin d₂) (Fin r₂) ℂ) :=
  {S | IsQuantumSuperchannel S ∧
    ∀ φ : SCPTP d₁ r₁, S (φ : MatrixMap (Fin d₁) (Fin r₁) ℂ) = (Γ φ : MatrixMap (Fin d₂) (Fin r₂) ℂ)}

/-- Section 2: the Choi matrix `C_L := (L(E_{i,j}))`, a block matrix in `M_d(M_r)`. -/
def choi {A B : Type*} [DecidableEq A] (L : MatrixMap A B ℂ) : Matrix (A × B) (A × B) ℂ :=
  fun p q => L (Matrix.single p.1 q.1 1) p.2 q.2

/-- Section 2: the vector space isomorphism `L ↦ (L(E_{i,j}))` from `L(M_d, M_r)` onto `M_d(M_r)`. -/
noncomputable def choiEquiv (A B : Type*) [Fintype A] [DecidableEq A] :
    MatrixMap A B ℂ ≃ₗ[ℂ] Matrix (A × B) (A × B) ℂ where
  toFun := choi
  map_add' L M := by ext p q; simp [choi]
  map_smul' c L := by ext p q; simp [choi]
  invFun X :=
    { toFun := fun Y => Matrix.of fun k l => ∑ i, ∑ j, Y i j * X (i, k) (j, l)
      map_add' := fun Y Y' => by
        ext k l
        simp only [Matrix.of_apply, Matrix.add_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := fun c Y => by
        ext k l
        simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum,
          mul_assoc] }
  left_inv L := by
    ext Y k l
    show ∑ i, ∑ j, Y i j * L (Matrix.single i j 1) k l = L Y k l
    conv_rhs => rw [Matrix.matrix_eq_sum_single Y]
    simp only [map_sum, Matrix.sum_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have h : Matrix.single i j (Y i j) = Y i j • Matrix.single i j (1 : ℂ) := by
      rw [Matrix.smul_single, smul_eq_mul, mul_one]
    rw [h, map_smul, Matrix.smul_apply, smul_eq_mul]
  right_inv X := by
    ext ⟨i, k⟩ ⟨j, l⟩
    show ∑ i', ∑ j', Matrix.single i j (1 : ℂ) i' j' * X (i', k) (j', l) = X (i, k) (j, l)
    rw [Finset.sum_eq_single i, Finset.sum_eq_single j]
    · simp
    · intro j' _ hj'; simp [Ne.symm hj']
    · intro h; exact absurd (Finset.mem_univ j) h
    · intro i' _ hi'
      exact Finset.sum_eq_zero fun j' _ => by simp [Ne.symm hi']
    · intro h; exact absurd (Finset.mem_univ i) h

/-- Section 3: the induced map `S̃ = R₂ ∘ S ∘ R₁⁻¹ : M_{d₁}(M_{r₁}) → M_{d₂}(M_{r₂})`. -/
noncomputable def induced {d₁ r₁ d₂ r₂ : ℕ}
    (S : MatrixMap (Fin d₁) (Fin r₁) ℂ →ₗ[ℂ] MatrixMap (Fin d₂) (Fin r₂) ℂ) :
    MatrixMap (Fin d₁ × Fin r₁) (Fin d₂ × Fin r₂) ℂ :=
  (choiEquiv (Fin d₂) (Fin r₂)).toLinearMap ∘ₗ S ∘ₗ (choiEquiv (Fin d₁) (Fin r₁)).symm.toLinearMap

open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
open D5.S3.Quantum.Recovery.LiJiangPolarPairOptimalityRefutation (inputFirstChoi)
open Matrix
open scoped TensorProduct Kronecker BigOperators ComplexOrder MatrixOrder

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2000000 in
private theorem cp_iff_choi {A B : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (L : MatrixMap A B ℂ) :
    L.IsCompletelyPositive ↔ (inputFirstChoi L).PosSemidef := by
  rw [MatrixMap.choi_PSD_iff_CP_map L]
  exact (Matrix.posSemidef_submatrix_equiv (Equiv.prodComm A B)).symm

set_option maxHeartbeats 2000000 in
private theorem choi_kron {A B C D : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]
    (φ : MatrixMap A B ℂ) (ψ : MatrixMap C D ℂ) :
    (inputFirstChoi (MatrixMap.kron φ ψ)).submatrix
      (Equiv.prodProdProdComm A B C D) (Equiv.prodProdProdComm A B C D) =
      Matrix.kronecker (inputFirstChoi φ) (inputFirstChoi ψ) := by
  ext ⟨⟨a, b⟩, c, d⟩ ⟨⟨a', b'⟩, c', d'⟩
  change MatrixMap.kron φ ψ (Matrix.single (a,c) (a',c') 1) (b,d) (b',d') =
    φ (Matrix.single a a' 1) b b' * ψ (Matrix.single c c' 1) d d'
  simp [MatrixMap.kron_def, Matrix.single, ite_and]

set_option maxHeartbeats 2000000 in
private theorem kronLift_tmul {A B C D : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [Fintype C] [DecidableEq C] [Fintype D]
    (φ : MatrixMap A B ℂ) (ψ : MatrixMap C D ℂ) :
    kronLift (φ ⊗ₜ[ℂ] ψ) = MatrixMap.kron φ ψ := by
  rfl

set_option maxHeartbeats 2000000 in
private theorem choi_induced_apply {d₁ r₁ d₂ r₂ : ℕ}
    (S : MatrixMap (Fin d₁) (Fin r₁) ℂ →ₗ[ℂ] MatrixMap (Fin d₂) (Fin r₂) ℂ)
    (φ : MatrixMap (Fin d₁) (Fin r₁) ℂ) :
    inputFirstChoi (S φ) = induced S (inputFirstChoi φ) := by
  change (choiEquiv _ _) (S φ) =
    (choiEquiv _ _) (S ((choiEquiv _ _).symm ((choiEquiv _ _) φ)))
  rw [LinearEquiv.symm_apply_apply]

private theorem matrixMap_expand {I O : Type*} [Fintype I] [DecidableEq I]
    (L : MatrixMap I O ℂ) (M : Matrix I I ℂ) (b b' : O) :
    L M b b' = ∑ i, ∑ j, M i j * L (Matrix.single i j 1) b b' := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single M]
  simp only [map_sum, Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hh : Matrix.single i j (M i j) = M i j • Matrix.single i j (1 : ℂ) := by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [hh, map_smul, Matrix.smul_apply, smul_eq_mul]

set_option maxHeartbeats 2000000 in
private theorem kron_apply_kronecker {A B C D : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [Fintype C] [DecidableEq C] [Fintype D]
    (φ : MatrixMap A B ℂ) (ψ : MatrixMap C D ℂ)
    (X : Matrix A A ℂ) (Y : Matrix C C ℂ) :
    MatrixMap.kron φ ψ (Matrix.kronecker X Y) = Matrix.kronecker (φ X) (ψ Y) := by
  ext ⟨b,d⟩ ⟨b',d'⟩
  rw [MatrixMap.kron_def]
  change (∑ a, ∑ a', ∑ c, ∑ c',
    φ (Matrix.single a a' 1) b b' * ψ (Matrix.single c c' 1) d d' *
      (X a a' * Y c c')) = φ X b b' * ψ Y d d'
  rw [matrixMap_expand φ X b b', matrixMap_expand ψ Y d d']
  simp only [Finset.sum_mul]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro a' _
  apply Finset.sum_congr rfl; intro c _
  apply Finset.sum_congr rfl; intro c' _
  ring

private noncomputable def shuffledChoiLinear {A B C D : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D] :
    MatrixMap A B ℂ ⊗[ℂ] MatrixMap C D ℂ →ₗ[ℂ]
      Matrix ((A × B) × (C × D)) ((A × B) × (C × D)) ℂ :=
  (Matrix.reindexLinearEquiv ℂ ℂ (Equiv.prodProdProdComm A B C D).symm
    (Equiv.prodProdProdComm A B C D).symm).toLinearMap.comp
      ((choiEquiv (A × C) (B × D)).toLinearMap.comp kronLift)

set_option maxHeartbeats 2000000 in
private theorem shuffled_naturality {d₁ r₁ d₂ r₂ d r : ℕ}
    (S : MatrixMap (Fin d₁) (Fin r₁) ℂ →ₗ[ℂ] MatrixMap (Fin d₂) (Fin r₂) ℂ)
    (t : MatrixMap (Fin d₁) (Fin r₁) ℂ ⊗[ℂ] MatrixMap (Fin d) (Fin r) ℂ) :
    shuffledChoiLinear (TensorProduct.map S LinearMap.id t) =
      MatrixMap.kron (induced S) LinearMap.id (shuffledChoiLinear t) := by
  induction t using TensorProduct.induction_on with
  | zero =>
    change shuffledChoiLinear (TensorProduct.map S LinearMap.id 0) =
      MatrixMap.kron (induced S) LinearMap.id (shuffledChoiLinear 0)
    simp only [map_zero]
  | tmul φ ψ =>
    change (inputFirstChoi (kronLift (TensorProduct.map S LinearMap.id (φ ⊗ₜ[ℂ] ψ)))).submatrix
      (Equiv.prodProdProdComm _ _ _ _) (Equiv.prodProdProdComm _ _ _ _) = _
    simp only [TensorProduct.map_tmul, LinearMap.id_apply, kronLift_tmul, choi_kron]
    change Matrix.kronecker (inputFirstChoi (S φ)) (inputFirstChoi ψ) =
      MatrixMap.kron (induced S) LinearMap.id
        ((inputFirstChoi (kronLift (φ ⊗ₜ[ℂ] ψ))).submatrix
          (Equiv.prodProdProdComm _ _ _ _) (Equiv.prodProdProdComm _ _ _ _))
    simp only [kronLift_tmul, choi_kron, kron_apply_kronecker, LinearMap.id_apply,
      choi_induced_apply]
  | add t u ht hu =>
    change shuffledChoiLinear (TensorProduct.map S LinearMap.id (t + u)) =
      MatrixMap.kron (induced S) LinearMap.id (shuffledChoiLinear (t + u))
    simp only [map_add]
    exact congrArg₂ (· + ·) ht hu

set_option maxHeartbeats 2000000 in
private theorem cp_amplify {A B T : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] [Fintype T] [DecidableEq T]
    {F : MatrixMap A B ℂ} (hF : F.IsCompletelyPositive)
    {X : Matrix (A × T) (A × T) ℂ} (hX : X.PosSemidef) :
    (MatrixMap.kron F (LinearMap.id : MatrixMap T T ℂ) X).PosSemidef := by
  exact MatrixMap.IsCompletelyPositive.of_Fintype hF T hX

set_option maxHeartbeats 2000000 in
private theorem cp_induced_preserving {d₁ r₁ d₂ r₂ : ℕ}
    (S : MatrixMap (Fin d₁) (Fin r₁) ℂ →ₗ[ℂ] MatrixMap (Fin d₂) (Fin r₂) ℂ)
    (hS : (induced S).IsCompletelyPositive) :
    (∀ φ : MatrixMap (Fin d₁) (Fin r₁) ℂ,
      φ.IsCompletelyPositive → (S φ).IsCompletelyPositive) ∧
    (∀ d r : ℕ, ∀ t : MatrixMap (Fin d₁) (Fin r₁) ℂ ⊗[ℂ] MatrixMap (Fin d) (Fin r) ℂ,
      (kronLift (A := Fin d₁) (B := Fin r₁) (C := Fin d) (D := Fin r) t).IsCompletelyPositive →
      (kronLift (A := Fin d₂) (B := Fin r₂) (C := Fin d) (D := Fin r)
        (TensorProduct.map S (LinearMap.id : MatrixMap (Fin d) (Fin r) ℂ →ₗ[ℂ]
          MatrixMap (Fin d) (Fin r) ℂ) t)).IsCompletelyPositive) := by
  constructor
  · intro φ hφ
    refine (cp_iff_choi (S φ)).mpr ?_
    rw [choi_induced_apply S φ]
    exact MatrixMap.IsCompletelyPositive.IsPositive hS ((cp_iff_choi φ).mp hφ)
  · intro d r t ht
    have hin : (shuffledChoiLinear t).PosSemidef :=
      ((cp_iff_choi (kronLift (A := Fin d₁) (B := Fin r₁)
        (C := Fin d) (D := Fin r) t)).mp ht).submatrix
          (Equiv.prodProdProdComm (Fin d₁) (Fin r₁) (Fin d) (Fin r))
    have hout : (shuffledChoiLinear (TensorProduct.map S LinearMap.id t)).PosSemidef := by
      rw [shuffled_naturality S t]
      exact cp_amplify hS hin
    refine (cp_iff_choi (kronLift (A := Fin d₂) (B := Fin r₂)
      (C := Fin d) (D := Fin r) (TensorProduct.map S LinearMap.id t))).mpr ?_
    exact (Matrix.posSemidef_submatrix_equiv
      (Equiv.prodProdProdComm (Fin d₂) (Fin r₂) (Fin d) (Fin r))).mp hout

set_option maxHeartbeats 2000000 in
private theorem choi_ofChoi {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (X : Matrix (A × B) (A × B) ℂ) : inputFirstChoi ((choiEquiv A B).symm X) = X := by
  exact (choiEquiv A B).apply_symm_apply X

private noncomputable def entangledTensor (d r : ℕ) :
    MatrixMap (Fin d) (Fin r) ℂ ⊗[ℂ] MatrixMap (Fin d) (Fin r) ℂ :=
  ∑ i : Fin d × Fin r, ∑ j : Fin d × Fin r,
    ((choiEquiv _ _).symm (Matrix.single i j 1)) ⊗ₜ[ℂ]
      ((choiEquiv _ _).symm (Matrix.single i j 1))

set_option maxHeartbeats 2000000 in
private theorem entangled_shuffled (d r : ℕ) :
    shuffledChoiLinear (entangledTensor d r) =
      Matrix.vecMulVec (fun p : (Fin d × Fin r) × (Fin d × Fin r) =>
        if p.1 = p.2 then (1 : ℂ) else 0)
        (star (fun p : (Fin d × Fin r) × (Fin d × Fin r) =>
          if p.1 = p.2 then (1 : ℂ) else 0)) := by
  change shuffledChoiLinear (entangledTensor d r) = _
  simp only [entangledTensor, map_sum]
  change (∑ i : Fin d × Fin r, ∑ j : Fin d × Fin r,
    (inputFirstChoi (kronLift (((choiEquiv _ _).symm (Matrix.single i j 1)) ⊗ₜ[ℂ]
      ((choiEquiv _ _).symm (Matrix.single i j 1))))).submatrix
        (Equiv.prodProdProdComm _ _ _ _) (Equiv.prodProdProdComm _ _ _ _)) = _
  simp only [kronLift_tmul, choi_kron, choi_ofChoi]
  ext ⟨i,k⟩ ⟨j,l⟩
  by_cases hik : i = k <;> by_cases hjl : j = l <;>
    simp [Matrix.sum_apply, Matrix.kronecker_apply, Matrix.single,
      Matrix.vecMulVec, ite_and, eq_comm, hik, hjl]

set_option maxHeartbeats 2000000 in
private theorem entangled_cp (d r : ℕ) : (kronLift (entangledTensor d r)).IsCompletelyPositive := by
  apply (cp_iff_choi _).mpr
  apply (Matrix.posSemidef_submatrix_equiv
    (Equiv.prodProdProdComm (Fin d) (Fin r) (Fin d) (Fin r))).mp
  change (shuffledChoiLinear (entangledTensor d r)).PosSemidef
  rw [entangled_shuffled]
  exact Matrix.posSemidef_vecMulVec_self_star _

set_option maxHeartbeats 2000000 in
private theorem preserving_cp_induced {d₁ r₁ d₂ r₂ : ℕ}
    (S : MatrixMap (Fin d₁) (Fin r₁) ℂ →ₗ[ℂ] MatrixMap (Fin d₂) (Fin r₂) ℂ)
    (hS : ∀ d r : ℕ, ∀ t : MatrixMap (Fin d₁) (Fin r₁) ℂ ⊗[ℂ] MatrixMap (Fin d) (Fin r) ℂ,
      (kronLift t).IsCompletelyPositive →
      (kronLift (TensorProduct.map S LinearMap.id t)).IsCompletelyPositive) :
    (induced S).IsCompletelyPositive := by
  have h := hS d₁ r₁ (entangledTensor d₁ r₁) (entangled_cp d₁ r₁)
  have h' : (shuffledChoiLinear (TensorProduct.map S LinearMap.id (entangledTensor d₁ r₁))).PosSemidef :=
    ((cp_iff_choi _).mp h).submatrix _
  rw [shuffled_naturality, entangled_shuffled] at h'
  apply (cp_iff_choi _).mpr
  convert h'.submatrix (Equiv.prodComm _ _) using 1
  ext ⟨a,b⟩ ⟨a',b'⟩
  change induced S (Matrix.single a a' 1) b b' = _
  simp only [Matrix.submatrix_apply, Equiv.prodComm_apply]
  rw [MatrixMap.kron_def]
  simp [Matrix.single, Matrix.vecMulVec, ite_and, eq_comm]

private noncomputable def z : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal ![1,-1]

private noncomputable def ftilde (s : ℂ) : MatrixMap (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ where
  toFun X := (1/2 : ℂ) • X + (1/8 : ℂ) • Matrix.kronecker 1 (partialTraceLeft X) +
    (X.trace/16) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) +
    (s * ((Matrix.kronecker z 1 * X).trace) / 32) • Matrix.kronecker z 1
  map_add' X Y := by
    ext ⟨a,b⟩ ⟨c,d⟩
    simp only [partialTraceLeft, Matrix.smul_apply, smul_eq_mul, Matrix.add_apply, Matrix.kronecker, Matrix.kronecker_apply,
      Matrix.mul_add, Matrix.trace_add, Finset.sum_add_distrib, mul_add, add_div]
    ring
  map_smul' c X := by
    ext ⟨a,b⟩ ⟨d,e⟩
    simp only [partialTraceLeft, Matrix.mul_smul, Matrix.trace_smul, Matrix.smul_apply, smul_eq_mul,
      Matrix.add_apply, Matrix.kronecker, Matrix.kronecker_apply, RingHom.id_apply,
      ← Finset.mul_sum]
    ring

private theorem induced_super (s : ℂ) : induced (((choiEquiv (Fin 2) (Fin 2)).symm.conj (ftilde s))) = ftilde s := by
  exact LinearEquiv.conj_conj_symm (choiEquiv (Fin 2) (Fin 2)) (ftilde s)

private theorem ftilde_midpoint : ftilde 0 = (1/2 : ℂ) • ftilde 1 + (1/2 : ℂ) • ftilde (-1) := by
  ext X p q
  simp [ftilde, partialTraceLeft, Matrix.smul_apply, smul_eq_mul, Matrix.add_apply]
  ring

private theorem ftilde_distinct : ftilde 1 ≠ ftilde (-1) := by
  intro h
  have h' := congrFun (congrFun (congrArg (fun F => F (Matrix.kronecker z 1)) h) (0,0)) (0,0)
  norm_num [ftilde, partialTraceLeft, z, Matrix.kronecker_apply, Matrix.mul_apply, Matrix.trace,
    Matrix.diagonal, Matrix.one_apply, Fin.sum_univ_two,
    Fintype.sum_prod_type] at h'

private theorem super_midpoint : ((choiEquiv (Fin 2) (Fin 2)).symm.conj (ftilde 0)) = (1/2 : ℝ) • ((choiEquiv (Fin 2) (Fin 2)).symm.conj (ftilde 1)) + (1/2 : ℝ) • ((choiEquiv (Fin 2) (Fin 2)).symm.conj (ftilde (-1))) := by
  ext φ X p q
  change (choiEquiv _ _).symm (ftilde 0 ((choiEquiv _ _) φ)) X p q = _
  rw [ftilde_midpoint]
  simp only [LinearMap.add_apply, LinearMap.smul_apply, map_add, map_smul,
    Matrix.add_apply, Matrix.smul_apply]
  simp [Complex.real_smul, LinearEquiv.conj_apply]

private theorem super_distinct : ((choiEquiv (Fin 2) (Fin 2)).symm.conj (ftilde 1)) ≠ ((choiEquiv (Fin 2) (Fin 2)).symm.conj (ftilde (-1))) := by
  exact (choiEquiv (Fin 2) (Fin 2)).symm.conj.injective.ne ftilde_distinct

private theorem super_not_extreme {Γ : SCPTP 2 2 →ₗ[ℂ] SCPTP 2 2}
    (hplus : ((choiEquiv (Fin 2) (Fin 2)).symm.conj (ftilde 1)) ∈ extensions Γ) (hminus : ((choiEquiv (Fin 2) (Fin 2)).symm.conj (ftilde (-1))) ∈ extensions Γ) :
    ((choiEquiv (Fin 2) (Fin 2)).symm.conj (ftilde 0)) ∉ (extensions Γ).extremePoints ℝ := by
  intro h
  have hmid : ((choiEquiv (Fin 2) (Fin 2)).symm.conj (ftilde 0)) ∈ openSegment ℝ (((choiEquiv (Fin 2) (Fin 2)).symm.conj (ftilde 1))) (((choiEquiv (Fin 2) (Fin 2)).symm.conj (ftilde (-1)))) := by
    rw [super_midpoint]
    simpa only [midpoint_eq_smul_add, invOf_eq_inv, inv_eq_one_div, smul_add] using
      (midpoint_mem_openSegment (𝕜 := ℝ) (((choiEquiv (Fin 2) (Fin 2)).symm.conj (ftilde 1))) (((choiEquiv (Fin 2) (Fin 2)).symm.conj (ftilde (-1)))))
  have h₁ := h.2 hplus hminus hmid
  have h₂ := h.2 hminus hplus (by rwa [openSegment_symm])
  exact super_distinct (h₁.trans h₂.symm)

private theorem tp_iff_choi {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (φ : MatrixMap A B ℂ) :
    (∀ X, (φ X).trace = X.trace) ↔
      ∀ i j, ∑ b, inputFirstChoi φ (i,b) (j,b) = (1 : Matrix A A ℂ) i j := by
  constructor
  · intro h i j
    have hh := h (Matrix.single i j 1)
    change (∑ b, φ (Matrix.single i j 1) b b) = _
    simpa [Matrix.trace, Matrix.single, Matrix.one_apply, ite_and, eq_comm] using hh
  · intro h X
    have expand : X = ∑ i, ∑ j, X i j • Matrix.single i j 1 := by
      simpa only [Matrix.smul_single, smul_eq_mul, mul_one] using Matrix.matrix_eq_sum_single X
    conv_lhs => rw [expand]
    simp only [map_sum, map_smul, Matrix.trace_sum, Matrix.trace_smul]
    have ht : ∀ i j, (φ (Matrix.single i j 1)).trace = (1 : Matrix A A ℂ) i j := h
    simp_rw [ht]
    simp [Matrix.one_apply, smul_eq_mul, Matrix.trace]

private noncomputable def coherence (a a' : Fin 2) (c : ℂ) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  (1/2 : ℂ) • ((1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) +
    c • Matrix.single (a,0) (a',1) 1 + star c • Matrix.single (a',1) (a,0) 1)

private theorem coherence_psd (a a' : Fin 2) (c : ℂ) (hc : c * star c = 1) :
    (coherence a a' c).PosSemidef := by
  let i : Fin 2 × Fin 2 := (a,0)
  let j : Fin 2 × Fin 2 := (a',1)
  let v : Fin 2 × Fin 2 → ℂ := fun p => if p = i then c else if p = j then 1 else 0
  let d : Fin 2 × Fin 2 → ℂ := fun p => if p = i ∨ p = j then 0 else 1
  have heq : coherence a a' c = (1/2 : ℂ) •
      (Matrix.vecMulVec v (star v) + Matrix.diagonal d) := by
    unfold coherence
    congr 1
    ext ⟨p₁,p₂⟩ ⟨q₁,q₂⟩
    fin_cases a <;> fin_cases a' <;> fin_cases p₁ <;> fin_cases p₂ <;>
      fin_cases q₁ <;> fin_cases q₂ <;>
      norm_num [i, j, v, d, Matrix.vecMulVec, Matrix.single,
        Matrix.diagonal, Matrix.one_apply, Matrix.smul_apply, smul_eq_mul]
    all_goals first | exact hc | exact hc.symm |
      (simpa only [mul_comm] using hc) | (simpa only [mul_comm] using hc.symm)

  rw [heq]
  apply Matrix.PosSemidef.smul _ (by norm_num [Complex.nonneg_iff])
  apply (Matrix.posSemidef_vecMulVec_self_star v).add
  apply Matrix.PosSemidef.diagonal
  intro p
  simp only [d]
  split_ifs <;> norm_num [Complex.nonneg_iff]

private theorem coherence_tp (a a' : Fin 2) (c : ℂ) :
    ∀ m n, ∑ b : Fin 2, coherence a a' c (m,b) (n,b) =
      (1 : Matrix (Fin 2) (Fin 2) ℂ) m n := by
  intro m n
  fin_cases m <;> fin_cases n <;> fin_cases a <;> fin_cases a' <;>
    simp [coherence, Matrix.single, Matrix.one_apply, Fin.sum_univ_two,
      Matrix.smul_apply, smul_eq_mul]
  all_goals ring

private theorem coherence_channel (a a' : Fin 2) (c : ℂ) (hc : c * star c = 1) :
    let φ := (choiEquiv (Fin 2) (Fin 2)).symm (coherence a a' c)
    φ.IsCompletelyPositive ∧ ∀ X, (φ X).trace = X.trace := by
  dsimp only
  constructor
  · apply (cp_iff_choi _).mpr
    change ((choiEquiv _ _) ((choiEquiv _ _).symm _)).PosSemidef
    rw [LinearEquiv.apply_symm_apply]
    exact coherence_psd a a' c hc
  · apply (tp_iff_choi _).mpr
    change ∀ m n, ∑ b : Fin 2,
      ((choiEquiv _ _) ((choiEquiv _ _).symm (coherence a a' c))) (m,b) (n,b) = _
    simp only [LinearEquiv.apply_symm_apply]
    exact coherence_tp a a' c

private theorem offdiagonal_in_span (a a' : Fin 2) :
    (choiEquiv (Fin 2) (Fin 2)).symm (Matrix.single (a,0) (a',1) 1) ∈ SCPTP 2 2 := by
  let C (c : ℂ) := (choiEquiv (Fin 2) (Fin 2)).symm (coherence a a' c)
  have hC (c : ℂ) (hc : c * star c = 1) : C c ∈ SCPTP 2 2 :=
    Submodule.subset_span (coherence_channel a a' c hc)
  have h₁ := hC 1 (by simp)
  have h₂ := hC (-1) (by simp)
  have h₃ := hC Complex.I (by simp [Complex.star_def])
  have h₄ := hC (-Complex.I) (by simp [Complex.star_def])
  have hlin : (choiEquiv (Fin 2) (Fin 2)).symm
      (Matrix.single (a,0) (a',1) 1) =
      (1/2 : ℂ) • ((C 1 - C (-1)) + (-Complex.I) • (C Complex.I - C (-Complex.I))) := by
    apply (choiEquiv _ _).injective
    simp only [map_smul, map_add, map_sub, C, LinearEquiv.apply_symm_apply]
    ext p q
    simp only [coherence, Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply,
      smul_eq_mul, star_one, star_neg, Complex.star_def, map_one, map_neg, Complex.conj_I]
    ring_nf
    all_goals simp only [Complex.I_sq]
    all_goals ring

  rw [hlin]
  exact Submodule.smul_mem _ _ (Submodule.add_mem _ (Submodule.sub_mem _ h₁ h₂)
    (Submodule.smul_mem _ _ (Submodule.sub_mem _ h₃ h₄)))

private theorem quantum_maps_span {d₁ r₁ d₂ r₂ : ℕ}
    {S : MatrixMap (Fin d₁) (Fin r₁) ℂ →ₗ[ℂ] MatrixMap (Fin d₂) (Fin r₂) ℂ}
    (hS : IsQuantumSuperchannel S) : ∀ φ ∈ SCPTP d₁ r₁, S φ ∈ SCPTP d₂ r₂ := by
  have hle : SCPTP d₁ r₁ ≤ (SCPTP d₂ r₂).comap S := by
    apply Submodule.span_le.mpr
    intro φ hφ
    exact Submodule.subset_span ⟨hS.1 φ hφ.1, hS.2.2 φ hφ.2⟩
  intro φ hφ
  exact hle hφ

private theorem quantum_restriction {d₁ r₁ d₂ r₂ : ℕ}
    {S : MatrixMap (Fin d₁) (Fin r₁) ℂ →ₗ[ℂ] MatrixMap (Fin d₂) (Fin r₂) ℂ}
    (hS : IsQuantumSuperchannel S) :
    IsQSC (d₁ := d₁) (r₁ := r₁) (d₂ := d₂) (r₂ := r₂) (S.restrict (quantum_maps_span hS)) ∧
      S ∈ extensions (d₁ := d₁) (r₁ := r₁) (d₂ := d₂) (r₂ := r₂) (S.restrict (quantum_maps_span hS)) := by
  constructor
  · constructor
    · intro φ hφ
      exact ⟨hS.1 φ hφ.1, hS.2.2 φ hφ.2⟩
    · intro d₃ r₃ t ht
      have heq :
          TensorProduct.map (SCPTP d₂ r₂).subtype (SCPTP d₃ r₃).subtype
            (TensorProduct.map (S.restrict (quantum_maps_span hS)) LinearMap.id t) =
          TensorProduct.map S LinearMap.id
            (TensorProduct.map (SCPTP d₁ r₁).subtype (SCPTP d₃ r₃).subtype t) := by
        clear ht
        induction t using TensorProduct.induction_on with
        | zero => simp
        | tmul φ ψ => rfl
        | add t u ht hu => simp only [map_add, ht, hu]
      rw [heq]
      exact hS.2.1 d₃ r₃ _ ht
  · exact ⟨hS, fun _ => rfl⟩

private noncomputable def omega : Fin 2 × Fin 2 → ℂ := fun p => if p.1 = p.2 then 1 else 0
private noncomputable def bell : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.vecMulVec omega (star omega)
private noncomputable def coherentK : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  (1/2 : ℂ) • bell + (1/8 : ℂ) • 1
private noncomputable def shuffleJ (F : MatrixMap (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :=
  (inputFirstChoi F).submatrix (Equiv.prodProdProdComm (Fin 2) (Fin 2) (Fin 2) (Fin 2))
    (Equiv.prodProdProdComm (Fin 2) (Fin 2) (Fin 2) (Fin 2))
private noncomputable def diagonalJ (s : ℂ) :
    ((Fin 2 × Fin 2) × (Fin 2 × Fin 2)) → ℂ :=
  fun p => 1/16 + s * z p.1.1 p.1.1 * z p.1.2 p.1.2 / 32

private theorem bell_psd : bell.PosSemidef := by
  exact Matrix.posSemidef_vecMulVec_self_star omega

private theorem coherentK_posDef : coherentK.PosDef := by
  have h₁ : ((1/2 : ℂ) • bell).PosSemidef := bell_psd.smul (by norm_num [Complex.nonneg_iff])
  have h₂ : ((1/8 : ℂ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)).PosDef :=
    Matrix.PosDef.one.smul (by norm_num [Complex.pos_iff])
  exact Matrix.PosDef.posSemidef_add h₁ h₂

private theorem choi_ftilde_decomposition (s : ℂ) :
    shuffleJ (ftilde s) =
      Matrix.kronecker coherentK bell + Matrix.diagonal (diagonalJ s) := by
  ext ⟨⟨a,d⟩,b,c⟩ ⟨⟨a',d'⟩,b',c'⟩
  change ftilde s (Matrix.single (a,b) (a',b') 1) (d,c) (d',c') = _
  simp only [ftilde, partialTraceLeft, LinearMap.coe_mk, AddHom.coe_mk, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul, coherentK, bell, omega,
    Matrix.kronecker_apply, Matrix.vecMulVec, Pi.star_apply]
  simp only [Matrix.trace_mul_single]
  simp [partialTraceLeft, Matrix.single, Matrix.one_apply, Matrix.diagonal,
    diagonalJ, z, Matrix.trace, Fintype.sum_prod_type, ite_and,
    eq_comm, Finset.filter_eq, Finset.filter_eq']
  all_goals split_ifs <;> simp_all <;> ring

private theorem ftilde_cp_of_diagonal (s : ℂ) (hs : ∀ p, 0 ≤ diagonalJ s p) :
    (ftilde s).IsCompletelyPositive := by
  apply (cp_iff_choi _).mpr
  apply (Matrix.posSemidef_submatrix_equiv
    (Equiv.prodProdProdComm (Fin 2) (Fin 2) (Fin 2) (Fin 2))).mp
  change (shuffleJ (ftilde s)).PosSemidef
  rw [choi_ftilde_decomposition]
  exact (coherentK_posDef.posSemidef.kronecker bell_psd).add (Matrix.PosSemidef.diagonal hs)

private theorem diagonalJ_nonneg (s : ℝ) (hs₀ : -1 ≤ s) (hs₁ : s ≤ 1) :
    ∀ p, 0 ≤ diagonalJ (s : ℂ) p := by
  intro ⟨⟨a,d⟩,b,c⟩
  fin_cases a <;> fin_cases d <;>
    simp [diagonalJ, z, Matrix.diagonal, Complex.nonneg_iff]
  all_goals linarith

private theorem ftilde_cp (s : ℝ) (hs₀ : -1 ≤ s) (hs₁ : s ≤ 1) :
    (ftilde (s : ℂ)).IsCompletelyPositive := by
  exact ftilde_cp_of_diagonal _ (diagonalJ_nonneg s hs₀ hs₁)

private theorem trace_of_tp_readout (X : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (hX : ∀ a a', ∑ b : Fin 2, X (a,b) (a',b) = (1 : Matrix (Fin 2) (Fin 2) ℂ) a a') :
    X.trace = 2 ∧ (Matrix.kronecker z 1 * X).trace = 0 := by
  have h₀ := hX 0 0
  have h₁ := hX 1 1
  simp only [Fin.sum_univ_two, Matrix.one_apply_eq] at h₀ h₁
  constructor
  · simp only [Matrix.trace, Matrix.diag_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
    linear_combination h₀ + h₁
  · simp [Matrix.trace, Matrix.mul_apply, Matrix.kronecker_apply, z,
      Matrix.diagonal, Matrix.one_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
    linear_combination h₀ - h₁

private theorem ftilde_tp_readout (s : ℂ) (X : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (hX : ∀ a a', ∑ b : Fin 2, X (a,b) (a',b) = (1 : Matrix (Fin 2) (Fin 2) ℂ) a a') :
    ∀ d d', ∑ c : Fin 2, ftilde s X (d,c) (d',c) =
      (1 : Matrix (Fin 2) (Fin 2) ℂ) d d' := by
  obtain ⟨htr,hz⟩ := trace_of_tp_readout X hX
  have htr' : X (0,0) (0,0) + X (0,1) (0,1) +
      (X (1,0) (1,0) + X (1,1) (1,1)) = 2 := by
    simpa only [Matrix.trace, Matrix.diag_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two] using htr
  intro d d'
  have hd := hX d d'
  simp only [Fin.sum_univ_two] at hd
  simp only [ftilde, partialTraceLeft, LinearMap.coe_mk, AddHom.coe_mk, hz, htr]
  fin_cases d <;> fin_cases d' <;>
    simp [partialTraceLeft, Fin.sum_univ_two, Matrix.one_apply,
      Matrix.kronecker_apply, Matrix.smul_apply, smul_eq_mul] at hd ⊢
  all_goals first | (linear_combination (1/2 : ℂ) * hd + (1/8 : ℂ) * htr') |
    (linear_combination (1/2 : ℂ) * hd)

private theorem super_quantum (s : ℝ) (hs₀ : -1 ≤ s) (hs₁ : s ≤ 1) :
    IsQuantumSuperchannel (((choiEquiv (Fin 2) (Fin 2)).symm.conj (ftilde (s : ℂ)))) := by
  have hcp : (induced (((choiEquiv (Fin 2) (Fin 2)).symm.conj (ftilde (s : ℂ))))).IsCompletelyPositive := by
    rw [induced_super]
    exact ftilde_cp s hs₀ hs₁
  obtain ⟨h₁,h₂⟩ := cp_induced_preserving _ hcp
  refine ⟨h₁,h₂,?_⟩
  intro φ hφ
  apply (tp_iff_choi _).mpr
  rw [choi_induced_apply, induced_super]
  exact ftilde_tp_readout _ _ ((tp_iff_choi _).mp hφ)

private noncomputable def charge : MatrixMap (Fin 2) (Fin 2) ℂ →ₗ[ℂ] ℂ :=
  (Matrix.traceLinearMap (Fin 2 × Fin 2) ℂ ℂ).comp
    ((LinearMap.mulLeft ℂ (Matrix.kronecker z 1)).comp
      (choiEquiv (Fin 2) (Fin 2)).toLinearMap)

private theorem charge_zero_on_span (φ : MatrixMap (Fin 2) (Fin 2) ℂ) (hφ : φ ∈ SCPTP 2 2) :
    charge φ = 0 := by
  have hle : SCPTP 2 2 ≤ charge.ker := by
    apply Submodule.span_le.mpr
    intro ψ hψ
    exact (trace_of_tp_readout (inputFirstChoi ψ) ((tp_iff_choi _).mp hψ.2)).2
  exact hle hφ

private theorem super_agrees_on_span (s : ℂ) (φ : SCPTP 2 2) :
    ((choiEquiv (Fin 2) (Fin 2)).symm.conj (ftilde s)) φ = ((choiEquiv (Fin 2) (Fin 2)).symm.conj (ftilde 0)) φ := by
  apply (choiEquiv (Fin 2) (Fin 2)).injective
  change (choiEquiv (Fin 2) (Fin 2)) ((choiEquiv (Fin 2) (Fin 2)).symm
      (ftilde s (inputFirstChoi (φ : MatrixMap (Fin 2) (Fin 2) ℂ)))) =
    (choiEquiv (Fin 2) (Fin 2)) ((choiEquiv (Fin 2) (Fin 2)).symm
      (ftilde 0 (inputFirstChoi (φ : MatrixMap (Fin 2) (Fin 2) ℂ))))
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  have hz := charge_zero_on_span φ φ.property
  change (Matrix.kronecker z 1 * inputFirstChoi (φ : MatrixMap (Fin 2) (Fin 2) ℂ)).trace = 0 at hz
  simp only [ftilde, partialTraceLeft, LinearMap.coe_mk, AddHom.coe_mk, hz, mul_zero,
    zero_div, zero_smul, add_zero]

private noncomputable def gamma : SCPTP 2 2 →ₗ[ℂ] SCPTP 2 2 :=
  (((choiEquiv (Fin 2) (Fin 2)).symm.conj (ftilde 0))).restrict (quantum_maps_span (super_quantum 0 (by norm_num) (by norm_num)))

private theorem gamma_qsc : IsQSC (d₁ := 2) (r₁ := 2) (d₂ := 2) (r₂ := 2) gamma := by
  exact (quantum_restriction (super_quantum 0 (by norm_num) (by norm_num))).1

private theorem super_extension (s : ℝ) (hs₀ : -1 ≤ s) (hs₁ : s ≤ 1) :
    ((choiEquiv (Fin 2) (Fin 2)).symm.conj (ftilde (s : ℂ))) ∈ extensions (d₁ := 2) (r₁ := 2) (d₂ := 2) (r₂ := 2) gamma := by
  exact ⟨super_quantum s hs₀ hs₁, super_agrees_on_span (s : ℂ)⟩


end D5.S3.QuantumChannels.DalySuperchannelMinimalExtension

set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000
namespace D5.S3.QuantumChannels.DalySuperchannelMinimalExtension.Rank
open Matrix
open scoped BigOperators ComplexOrder

private theorem compression_apply {N T : Type*} [Fintype N] [DecidableEq N] [Fintype T] [DecidableEq T]
    (J : Matrix (N × T) (N × T) ℂ) (v : N → ℂ) (t u : T) :
    (let B := (Matrix.kronecker (Matrix.replicateRow Unit (star v)) (1 : Matrix T T ℂ)).submatrix
        (fun t => ((), t)) id;
      D5.S3.Quantum.Reduction.IsometricCompression.compress B.conjTranspose J) t u = ∑ i, ∑ j, star (v i) * J (i,t) (j,u) * v j := by
  simp [D5.S3.Quantum.Reduction.IsometricCompression.compress, Matrix.mul_apply, Matrix.kronecker_apply, Matrix.replicateRow,
    Matrix.one_apply, Matrix.conjTranspose_apply, Matrix.submatrix_apply,
    Fintype.sum_prod_type, Finset.mul_sum, Finset.sum_mul, ite_mul, mul_ite,
    apply_ite] <;> rw [Finset.sum_comm]

private theorem compression_psd {N T : Type*} [Fintype N] [DecidableEq N] [Fintype T] [DecidableEq T]
    {J : Matrix (N × T) (N × T) ℂ} (hJ : J.PosSemidef) (v : N → ℂ) :
    (let B := (Matrix.kronecker (Matrix.replicateRow Unit (star v)) (1 : Matrix T T ℂ)).submatrix
        (fun t => ((), t)) id;
      D5.S3.Quantum.Reduction.IsometricCompression.compress B.conjTranspose J).PosSemidef := by
  exact hJ.conjTranspose_mul_mul_same _

private theorem trace_compression {N T : Type*} [Fintype N] [DecidableEq N] [Fintype T] [DecidableEq T]
    (J : Matrix (N × T) (N × T) ℂ) (R : Matrix N N ℂ)
    (hR : ∀ i j, R i j = ∑ t, J (i,t) (j,t)) (v : N → ℂ) :
    (let B := (Matrix.kronecker (Matrix.replicateRow Unit (star v)) (1 : Matrix T T ℂ)).submatrix
        (fun t => ((), t)) id;
      D5.S3.Quantum.Reduction.IsometricCompression.compress B.conjTranspose J).trace = star v ⬝ᵥ (R *ᵥ v) := by
  simp only [Matrix.trace, Matrix.diag_apply, compression_apply, dotProduct, Matrix.mulVec,
    hR, Finset.mul_sum, Finset.sum_mul, Pi.star_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro t _
  ring

private theorem coherent_block_full_rank {N T : Type*} [Fintype N] [DecidableEq N]
    [Fintype T] [DecidableEq T]
    {J : Matrix (N × T) (N × T) ℂ} (hJ : J.PosSemidef)
    {K : Matrix N N ℂ} (hK : K.PosDef) (t₀ t₁ : T)
    (hblock : ∀ i j, J (i,t₀) (j,t₁) = K i j)
    (R : Matrix N N ℂ) (hR : ∀ i j, R i j = ∑ t, J (i,t) (j,t)) :
    R.rank = Fintype.card N := by
  have hker : ∀ v : N → ℂ, R *ᵥ v = 0 → v = 0 := by
    intro v hv
    by_contra hn
    let B := (Matrix.kronecker (Matrix.replicateRow Unit (star v)) (1 : Matrix T T ℂ)).submatrix
      (fun t => ((), t)) id
    have hq := compression_psd hJ v
    have htrace : (D5.S3.Quantum.Reduction.IsometricCompression.compress B.conjTranspose J).trace = 0 := by
      rw [trace_compression J R hR, hv, dotProduct_zero]
    have hz := hq.trace_eq_zero_iff.mp htrace
    have he : D5.S3.Quantum.Reduction.IsometricCompression.compress B.conjTranspose J t₀ t₁ = star v ⬝ᵥ (K *ᵥ v) := by
      rw [show D5.S3.Quantum.Reduction.IsometricCompression.compress B.conjTranspose J t₀ t₁ =
          ∑ i, ∑ j, star (v i) * J (i,t₀) (j,t₁) * v j from compression_apply J v t₀ t₁]
      simp only [hblock, dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hp := hK.dotProduct_mulVec_pos hn
    rw [← he, hz] at hp
    simpa using hp
  have hinj : Function.Injective R.mulVecLin :=
    (injective_iff_map_eq_zero R.mulVecLin).mpr hker
  rw [Matrix.rank, LinearMap.finrank_range_of_inj hinj]
  simp

end D5.S3.QuantumChannels.DalySuperchannelMinimalExtension.Rank

set_option backward.isDefEq.respectTransparency false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
namespace D5.S3.QuantumChannels.DalySuperchannelMinimalExtension
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
open D5.S3.Quantum.Recovery.LiJiangPolarPairOptimalityRefutation (inputFirstChoi)
open Matrix
open scoped TensorProduct Kronecker BigOperators ComplexOrder MatrixOrder
private theorem extension_fixed_unit {G : MatrixMap (Fin 2) (Fin 2) ℂ →ₗ[ℂ]
    MatrixMap (Fin 2) (Fin 2) ℂ} (hG : G ∈ extensions (d₁ := 2) (r₁ := 2) (d₂ := 2) (r₂ := 2) gamma) (a a' : Fin 2) :
    induced G (Matrix.single (a,0) (a',1) 1) =
      ftilde 0 (Matrix.single (a,0) (a',1) 1) := by
  let φ : SCPTP 2 2 := ⟨(choiEquiv _ _).symm (Matrix.single (a,0) (a',1) 1),
    offdiagonal_in_span a a'⟩
  have hh : G (φ : MatrixMap (Fin 2) (Fin 2) ℂ) = ((choiEquiv (Fin 2) (Fin 2)).symm.conj (ftilde 0)) φ := hG.2 φ
  have he := congrArg inputFirstChoi hh
  rw [choi_induced_apply, choi_induced_apply, induced_super] at he
  simpa only [φ, choi_ofChoi] using he

private theorem extension_fixed_coherence {G : MatrixMap (Fin 2) (Fin 2) ℂ →ₗ[ℂ]
    MatrixMap (Fin 2) (Fin 2) ℂ} (hG : G ∈ extensions (d₁ := 2) (r₁ := 2) (d₂ := 2) (r₂ := 2) gamma) :
    ∀ i j, shuffleJ (induced G) (i,(0,0)) (j,(1,1)) = coherentK i j := by
  intro ⟨a,d⟩ ⟨a',d'⟩
  change induced G (Matrix.single (a,0) (a',1) 1) (d,0) (d',1) = _
  rw [extension_fixed_unit hG]
  fin_cases a <;> fin_cases d <;> fin_cases a' <;> fin_cases d' <;>
    norm_num [ftilde, partialTraceLeft, Matrix.single, Matrix.one_apply, Matrix.mul_apply,
      Matrix.kronecker_apply, Matrix.trace, Fintype.sum_prod_type,
      Fin.sum_univ_two, coherentK, bell, omega, Matrix.vecMulVec, Matrix.diagonal,
      Finset.filter_eq, Finset.filter_eq', eq_comm]


end D5.S3.QuantumChannels.DalySuperchannelMinimalExtension

namespace D5.S3.QuantumChannels.DalySuperchannelMinimalExtension
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
open D5.S3.Quantum.Recovery.LiJiangPolarPairOptimalityRefutation (inputFirstChoi)
open Matrix
open scoped TensorProduct Kronecker BigOperators ComplexOrder MatrixOrder

open D5.S3.Quantum.Information.PartialTraceMutualInformation
/-- Section 4: the dimension `e = rank (Tr_{r₁} Tr_{r₂} C_{S̃})`. -/
noncomputable def e {d₁ r₁ d₂ r₂ : ℕ}
    (S : MatrixMap (Fin d₁) (Fin r₁) ℂ →ₗ[ℂ] MatrixMap (Fin d₂) (Fin r₂) ℂ) : ℕ :=
  (partialTraceRight
    ((inputFirstChoi (induced S)).reindex (Equiv.prodProdProdComm (Fin d₁) (Fin r₁) (Fin d₂) (Fin r₂))
      (Equiv.prodProdProdComm (Fin d₁) (Fin r₁) (Fin d₂) (Fin r₂)))).rank

private theorem all_extensions_e (G : MatrixMap (Fin 2) (Fin 2) ℂ →ₗ[ℂ]
    MatrixMap (Fin 2) (Fin 2) ℂ) (hG : G ∈ extensions (d₁ := 2) (r₁ := 2) (d₂ := 2) (r₂ := 2) gamma) : e G = 4 := by
  have hcp := preserving_cp_induced G hG.1.2.1
  have hJ : (shuffleJ (induced G)).PosSemidef := ((cp_iff_choi _).mp hcp).submatrix _
  let R : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
    fun i j => ∑ t : Fin 2 × Fin 2, shuffleJ (induced G) (i,t) (j,t)
  have hr := Rank.coherent_block_full_rank hJ coherentK_posDef (0,0) (1,1)
    (extension_fixed_coherence hG) R (fun _ _ => rfl)
  change R.rank = 4
  simpa only [Fintype.card_prod, Fintype.card_fin] using hr

/-- Remark 4.1: the extensions which give minimal dimensions `e` are extreme points. -/
def claim : Prop :=
  ∀ d₁ r₁ d₂ r₂ : ℕ, 1 ≤ d₁ → 1 ≤ r₁ → 1 ≤ d₂ → 1 ≤ r₂ →
    ∀ Γ : SCPTP d₁ r₁ →ₗ[ℂ] SCPTP d₂ r₂, IsQSC Γ →
      ∀ S ∈ extensions Γ, (∀ G ∈ extensions Γ, e S ≤ e G) →
        S ∈ (extensions Γ).extremePoints ℝ


theorem result : ¬ claim := by
  intro h
  have h₀ : ((choiEquiv (Fin 2) (Fin 2)).symm.conj (ftilde 0)) ∈ extensions (d₁ := 2) (r₁ := 2) (d₂ := 2) (r₂ := 2) gamma := by
    simpa using (super_extension (0 : ℝ) (by norm_num) (by norm_num))
  have hplus : ((choiEquiv (Fin 2) (Fin 2)).symm.conj (ftilde 1)) ∈ extensions (d₁ := 2) (r₁ := 2) (d₂ := 2) (r₂ := 2) gamma := by
    simpa using (super_extension (1 : ℝ) (by norm_num) (by norm_num))
  have hminus : ((choiEquiv (Fin 2) (Fin 2)).symm.conj (ftilde (-1))) ∈ extensions (d₁ := 2) (r₁ := 2) (d₂ := 2) (r₂ := 2) gamma := by
    simpa using (super_extension ((-1) : ℝ) (by norm_num) (by norm_num))
  have hmin : ∀ G ∈ extensions (d₁ := 2) (r₁ := 2) (d₂ := 2) (r₂ := 2) gamma, e (((choiEquiv (Fin 2) (Fin 2)).symm.conj (ftilde 0))) ≤ e G := by
    intro G hG
    rw [all_extensions_e _ h₀, all_extensions_e _ hG]
  exact super_not_extreme hplus hminus
    (h 2 2 2 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      gamma gamma_qsc (((choiEquiv (Fin 2) (Fin 2)).symm.conj (ftilde 0))) h₀ hmin)

end D5.S3.QuantumChannels.DalySuperchannelMinimalExtension
