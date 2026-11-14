/- GID: D5/S3/QuantumChannels/WallmanFlammiaTwoContractivity
   generality: I
   mirror-B: D5/B/S3/QuantumChannels/WallmanFlammiaTwoContractivity
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Every nonunitary CPTP channel is two-contractive for finite exact unitary two-designs. -/

/-
admission_basis: open-problem-resolution (#22351; Proved).
escape_witness: none.
The definitions retain the source's matrix-unit formulas and algebraic multiplicities.
The trace-zero space is the trace map's kernel; finTwoArrowEquiv supplies tensor coordinates.
The standard matrix basis and LinearMap.toMatrix give the channel transfer matrix.
The scalar projector uses PeritoTsirelson.maxEntangled; private equalities connect its trace-vector and Q representations.
proof_shape: DesignEntries.scalarProjector_eq: bind-only; consumers: DesignEntries.scalarProjector_eq_Q,DesignEntries.scalarProjector_entry,DesignEntries.tracelessProjector_kills_trace,TransferGeometry.transfer_scalar_left,TransferGeometry.transfer_scalar_image,TraceInterface.projection_matrix,ConjugationInterface.scalar_rep_right.
proof_shape: DesignEntries.scalarProjector_eq_Q: bind-only; consumers: DesignEntries.scalarProjector_projection,ConjugationInterface.scalar_rep_left.
All theorem proofs below are bind-only compositions of spectral, norm and channel owners.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/23694.
proof_shape: IsUnitaryTwoDesign: bind-only; consumers: claim,DesignEntries.design_haar_entry,DesignEntries.average_rep_entry,DesignEntries.averaged_endomorphism_entry,DesignEntries.averaged_traceless_endomorphism,DesignEntries.projected_gram_averages,DesignTensorBound.projected_tensor_bound,CanonicalSector.canonical_tensor_strict,FinalAssembly.canonical_result | conjugatedEntry: bind-only; consumers: twirledTensorPower,TransferGeometry.twirledTensorPower_two_reindex,FinalAssembly.inverse_entry,FinalAssembly.target_charpoly | twirledTensorPower: bind-only; consumers: IsNContractive,TransferGeometry.twirledTensorPower_two_reindex,FinalAssembly.target_charpoly,FinalAssembly.canonical_result | IsNContractive: bind-only; consumers: claim,FinalAssembly.canonical_result | claim: bind-only; consumers: result.
proof_shape: PurityEquality.probability_purity_one: bind-only; consumers: PurityEquality.density_purity_one_outer | PurityEquality.density_purity_one_outer: bind-only; consumers: ChannelPurity.maximal_choi_purity_unitary | ChoiRankOne.rank_one_choi_unitary: bind-only; consumers: ChannelPurity.maximal_choi_purity_unitary | ChannelPurity.canonical_action_trace: bind-only; consumers: ChannelPurity.canonical_choi_trace,ChannelPurity.maximal_choi_purity_unitary,ChannelPurity.strict_unitarity_value,TransferGeometry.canonical_projected_mass | ChannelPurity.canonical_action_choi_psd: bind-only; consumers: ChannelPurity.maximal_choi_purity_unitary,ChannelPurity.strict_unitarity_value,TransferGeometry.canonical_projected_mass.
proof_shape: ChannelPurity.canonical_choi_trace: bind-only; consumers: ChannelPurity.maximal_choi_purity_unitary,ChannelPurity.strict_unitarity_value | ChannelPurity.maximal_choi_purity_unitary: bind-only; consumers: ChannelPurity.strict_unitarity_value | ChannelPurity.unitarityValue: bind-only; consumers: ChannelPurity.strict_unitarity_value,TransferGeometry.canonical_unitarity_mass,TransferGeometry.canonical_unitarity_nonneg,CanonicalSector.canonical_coefficient,CanonicalSector.canonical_tensor_strict | ChannelPurity.strict_unitarity_value: bind-only; consumers: CanonicalSector.canonical_one_copy_strict,CanonicalSector.canonical_tensor_strict | TransferGeometry.std_repr: bind-only; consumers: TransferGeometry.transfer_entry,TransferGeometry.transfer_action,TraceInterface.projection_matrix.
proof_shape: TransferGeometry.transfer_entry: bind-only; consumers: TransferGeometry.transfer_choi_purity,TransferGeometry.transfer_scalar_row,ConjugationInterface.transfer_conjugation,FinalAssembly.inverse_entry | TransferGeometry.transfer_action: bind-only; consumers: TransferGeometry.transfer_scalar_image | TransferGeometry.transfer_choi_purity: bind-only; consumers: TransferGeometry.canonical_projected_mass | TransferGeometry.conjugationRep_action: bind-only; consumers: ConjugationInterface.scalar_rep_right | TransferGeometry.twirledTensorPower_two_reindex: bind-only; consumers: FinalAssembly.target_charpoly.
proof_shape: DesignEntries.design_haar_entry: bind-only; consumers: DesignEntries.average_rep_entry | DesignEntries.average_rep_entry: bind-only; consumers: DesignEntries.averaged_endomorphism_entry | DesignEntries.diagonal_pair_sum: bind-only; consumers: DesignEntries.averaged_endomorphism_entry | DesignEntries.fourth_moment_reshaped: bind-only; consumers: DesignEntries.averaged_endomorphism_entry.
proof_shape: DesignEntries.averaged_endomorphism_entry: bind-only; consumers: DesignEntries.averaged_traceless_endomorphism | DesignEntries.tracelessProjector: bind-only; consumers: DesignEntries.tracelessProjector_projection,DesignEntries.averaged_traceless_endomorphism,DesignEntries.tracelessProjector_trace,DesignEntries.tracelessProjector_kills_trace,DesignEntries.projected_gram_averages,TransferGeometry.transfer_traceless_compression,TransferGeometry.canonical_projected_mass,TransferGeometry.canonical_unitarity_mass,TransferGeometry.canonical_unitarity_nonneg,DesignTensorBound.projected_tensor_bound,CanonicalSector.canonical_coefficient,CanonicalSector.canonical_one_copy_strict,CanonicalSector.canonical_tensor_strict,TraceInterface.projection_matrix,TraceInterface.inclusion_projection_matrix,TraceInterface.smallMatrix_lift,ConjugationInterface.projector_rep_commute,ConjugationInterface.inverseConjugatedMap_compression,FinalAssembly.canonical_result | DesignEntries.traceVector_dot: bind-only; consumers: DesignEntries.tracelessProjector_kills_trace,TransferGeometry.transfer_scalar_mass | DesignEntries.scalarProjector_projection: bind-only; consumers: DesignEntries.tracelessProjector_projection,TransferGeometry.transfer_traceless_compression,TransferGeometry.canonical_projected_mass.
proof_shape: DesignEntries.tracelessProjector_projection: bind-only; consumers: DesignEntries.projected_gram_averages,DesignTensorBound.projected_tensor_bound,CanonicalSector.canonical_one_copy_strict | DesignEntries.scalarProjector_entry: bind-only; consumers: DesignEntries.averaged_traceless_endomorphism | DesignEntries.averaged_traceless_endomorphism: bind-only; consumers: DesignEntries.projected_gram_averages,FinalAssembly.canonical_result | ProjectionMass.projection_mass_split: bind-only; consumers: TransferGeometry.canonical_projected_mass | ProjectionMass.trace_product_cauchy_generic: bind-only; consumers: ProjectionMass.strict_projected_one_copy_bound.
proof_shape: ProjectionMass.strict_projected_one_copy_bound: bind-only; consumers: CanonicalSector.canonical_one_copy_strict | DesignEntries.scalarProjector_trace: bind-only; consumers: DesignEntries.tracelessProjector_trace | DesignEntries.tracelessProjector_trace: bind-only; consumers: CanonicalSector.canonical_one_copy_strict | DesignEntries.tracelessProjector_kills_trace: bind-only; consumers: DesignEntries.projected_gram_averages,FinalAssembly.canonical_result | DesignEntries.diagonal_pair_sum_zero_of_kills_trace: bind-only; consumers: DesignEntries.projected_gram_averages,FinalAssembly.canonical_result.
proof_shape: DesignEntries.projected_gram_averages: bind-only; consumers: DesignTensorBound.projected_tensor_bound | TransferGeometry.transfer_scalar_row: bind-only; consumers: TransferGeometry.transfer_scalar_left | TransferGeometry.transfer_scalar_left: bind-only; consumers: TransferGeometry.transfer_traceless_compression | TransferGeometry.transfer_traceless_compression: bind-only; consumers: TransferGeometry.canonical_projected_mass | TransferGeometry.transfer_scalar_image: bind-only; consumers: TransferGeometry.transfer_scalar_mass.
proof_shape: TransferGeometry.transfer_scalar_mass: bind-only; consumers: TransferGeometry.canonical_projected_mass | TransferGeometry.canonical_projected_mass: bind-only; consumers: TransferGeometry.canonical_unitarity_mass,CanonicalSector.canonical_coefficient | TransferGeometry.canonical_unitarity_mass: bind-only; consumers: TransferGeometry.canonical_unitarity_nonneg,CanonicalSector.canonical_one_copy_strict | TransferGeometry.canonical_unitarity_nonneg: bind-only; consumers: CanonicalSector.canonical_tensor_strict | TensorGram.tensorRow: bind-only; consumers: TensorGram.row_col,TensorGram.row_gram,TensorGram.projection_tensor_norm_bound.
proof_shape: TensorGram.tensorCol: bind-only; consumers: TensorGram.row_col,TensorGram.col_gram,TensorGram.projection_tensor_norm_bound | TensorGram.row_col: bind-only; consumers: TensorGram.projection_tensor_norm_bound | TensorGram.row_gram: bind-only; consumers: TensorGram.projection_tensor_norm_bound | TensorGram.col_gram: bind-only; consumers: TensorGram.projection_tensor_norm_bound | SpectralClosure.unit_circle_roots_of_factor: bind-only; consumers: SpectralClosure.unit_circle_roots_of_block_bound.
proof_shape: SpectralClosure.unit_circle_roots_of_block_bound: bind-only; consumers: FinalAssembly.canonical_result | TensorGram.projection_tensor_norm_bound: bind-only; consumers: DesignTensorBound.projected_tensor_bound | AveragedGram.conjugateFamily: bind-only; consumers: AveragedGram.family_left_gram,AveragedGram.family_right_gram,DesignTensorBound.projected_tensor_bound | AveragedGram.family_left_gram: bind-only; consumers: DesignTensorBound.projected_tensor_bound | AveragedGram.family_right_gram: bind-only; consumers: DesignTensorBound.projected_tensor_bound.
proof_shape: DesignTensorBound.projected_tensor_bound: bind-only; consumers: CanonicalSector.canonical_tensor_strict | CanonicalSector.canonical_coefficient: bind-only; consumers: CanonicalSector.canonical_tensor_strict | CanonicalSector.canonical_one_copy_strict: bind-only; consumers: FinalAssembly.canonical_result | CanonicalSector.canonical_tensor_strict: bind-only; consumers: FinalAssembly.canonical_result | TensorBlocks.tensorSplit: bind-only; consumers: TensorBlocks.averaged_lower_tensor_charpoly.
proof_shape: TensorBlocks.lowerLift: bind-only; consumers: TensorBlocks.averaged_lower_tensor_charpoly,TraceCoordinates.adapted_matrix_lower,TraceCoordinates.adapted_tensor_charpoly | TensorBlocks.charpoly_lower: bind-only; consumers: TensorBlocks.averaged_lower_tensor_charpoly | TensorBlocks.scalar_charpoly: bind-only; consumers: TensorBlocks.averaged_lower_tensor_charpoly | TensorBlocks.averaged_lower_tensor_charpoly: bind-only; consumers: TraceCoordinates.adapted_tensor_charpoly | CompressionSpectral.compression_charpoly_identity: bind-only; consumers: CompressionSpectral.compression_root_bound.
proof_shape: CompressionSpectral.compression_root_bound: bind-only; consumers: FinalAssembly.canonical_result | TraceCoordinates.assemble: bind-only; consumers: TraceCoordinates.adaptedBasis,TraceCoordinates.adaptedBasis_first_coefficient,TraceInterface.project,TraceInterface.project_inclusion,TraceInterface.smallMatrix_adapted | TraceCoordinates.adaptedBasis: bind-only; consumers: TraceCoordinates.adaptedBasis_first_coefficient,TraceCoordinates.trace_preserving_first_row,TraceCoordinates.adapted_matrix_lower,TraceCoordinates.adapted_tensor_charpoly,TraceInterface.smallMatrix_adapted,FinalAssembly.canonical_result | TraceCoordinates.adaptedBasis_first_coefficient: bind-only; consumers: TraceCoordinates.trace_preserving_first_row | TraceCoordinates.trace_preserving_first_row: bind-only; consumers: TraceCoordinates.adapted_matrix_lower.
proof_shape: TensorCoordinates.tensor_mean_matrix: bind-only; consumers: TensorCoordinates.tensor_average_charpoly_basis | TensorCoordinates.tensor_average_charpoly_basis: bind-only; consumers: FinalAssembly.canonical_result | TraceCoordinates.adapted_matrix_lower: bind-only; consumers: TraceCoordinates.adapted_tensor_charpoly | TraceCoordinates.adapted_tensor_charpoly: bind-only; consumers: FinalAssembly.canonical_result | TraceInterface.project: bind-only; consumers: TraceInterface.project_inclusion,TraceInterface.projection_matrix,TraceInterface.projection_inclusion_matrix,TraceInterface.inclusion_projection_matrix,TraceInterface.smallMatrix,TraceInterface.smallMatrix_compression,TraceInterface.smallMatrix_adapted,TraceInterface.smallMatrix_lift,FinalAssembly.canonical_result.
proof_shape: TraceInterface.project_inclusion: bind-only; consumers: TraceInterface.projection_inclusion_matrix | TraceInterface.projection_matrix: bind-only; consumers: TraceInterface.inclusion_projection_matrix | TraceInterface.projection_inclusion_matrix: bind-only; consumers: FinalAssembly.canonical_result | TraceInterface.inclusion_projection_matrix: bind-only; consumers: TraceInterface.smallMatrix_lift,FinalAssembly.canonical_result | TraceInterface.smallMatrix: bind-only; consumers: TraceInterface.smallMatrix_compression,TraceInterface.smallMatrix_adapted,TraceInterface.smallMatrix_lift,FinalAssembly.canonical_result.
proof_shape: TraceInterface.smallMatrix_compression: bind-only; consumers: TraceInterface.smallMatrix_lift | TraceInterface.smallMatrix_adapted: bind-only; consumers: FinalAssembly.canonical_result | TraceInterface.smallMatrix_lift: bind-only; consumers: FinalAssembly.canonical_result | ConjugationInterface.conjugationMap_trace: bind-only; consumers: ConjugationInterface.inverseConjugatedMap_trace | ConjugationInterface.conjugationMap_one: bind-only; consumers: ConjugationInterface.scalar_rep_right.
proof_shape: ConjugationInterface.transfer_conjugation: bind-only; consumers: ConjugationInterface.inverseConjugatedMap_transfer | ConjugationInterface.conjugationRep_star: bind-only; consumers: ConjugationInterface.scalar_rep_left,ConjugationInterface.inverseConjugatedMap_transfer,ConjugationInterface.inverseConjugatedMap_compression | ConjugationInterface.scalar_rep_right: bind-only; consumers: ConjugationInterface.scalar_rep_left,ConjugationInterface.projector_rep_commute | ConjugationInterface.scalar_rep_left: bind-only; consumers: ConjugationInterface.projector_rep_commute | ConjugationInterface.projector_rep_commute: bind-only; consumers: ConjugationInterface.inverseConjugatedMap_compression.
proof_shape: ConjugationInterface.inverseConjugatedMap: bind-only; consumers: ConjugationInterface.inverseConjugatedMap_trace,ConjugationInterface.inverseConjugatedMap_transfer,ConjugationInterface.inverseConjugatedMap_compression,FinalAssembly.inverse_entry,FinalAssembly.target_charpoly,FinalAssembly.canonical_result | ConjugationInterface.inverseConjugatedMap_trace: bind-only; consumers: FinalAssembly.canonical_result | ConjugationInterface.inverseConjugatedMap_transfer: bind-only; consumers: ConjugationInterface.inverseConjugatedMap_compression | ConjugationInterface.inverseConjugatedMap_compression: bind-only; consumers: FinalAssembly.canonical_result | FinalAssembly.tensor_lift_average: bind-only; consumers: FinalAssembly.canonical_result.
proof_shape: FinalAssembly.inverse_entry: bind-only; consumers: FinalAssembly.target_charpoly | FinalAssembly.target_charpoly: bind-only; consumers: FinalAssembly.canonical_result | FinalAssembly.canonical_result: bind-only; consumers: result | result: bind-only; consumers: none (settling result).
-/

import D5.S3.Quantum.Recovery.LiJiangPolarPairOptimalityRefutation
import D5.S3.Quantum.Matrix.CartesianVariance
import D5.S3.Quantum.Entanglement.AbsoluteSeparability.GurvitsBarnumBall
import D5.S3.Quantum.Foundation.FiniteStateChannel
import D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl
import D5.S3.Quantum.Recovery.ActualChannelAlgebra
import D5.S3.Quantum.Foundation.FiniteKrausRepresentation
import D5.S3.Quantum.Foundation.FiniteKrausChannel
import D5.S3.Quantum.GNSMatrix
import D5.S3.Weil.ZetaLinear.PosIndex
import D5.S3.Quantum.RandomCircuits.CHaarConcatenationNonmonotone
import D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability
import D5.S3.QuantumBounds.PeritoTsirelson
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
open Matrix
open scoped BigOperators
open D5.S3.Quantum.Foundation.FiniteStateChannel (QuantumChannel)
open D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl (literalMoment haarAverage)
namespace D5.S3.QuantumChannels.WallmanFlammiaTwoContractivity
def IsUnitaryTwoDesign {d : ℕ}
    (G : Subgroup (Matrix.unitaryGroup (Fin d) ℂ)) [Fintype G] : Prop :=
  (Fintype.card G : ℂ)⁻¹ • (∑ g : G, literalMoment (g.val.val)) = haarAverage (Fin d)
def conjugatedEntry {d : ℕ}
    (Λ : QuantumChannel (Fin d) (Fin d)) (U : Matrix.unitaryGroup (Fin d) ℂ)
    (r c : Fin d × Fin d) : ℂ :=
  (U.val * CStarMatrix.ofMatrix.symm (Λ.toCompletelyPositiveMap (CStarMatrix.ofMatrix (U.val.conjTranspose * Matrix.single c.1 c.2 1 * U.val))) * U.val.conjTranspose) r.1 r.2
def twirledTensorPower {d : ℕ}
    (Λ : QuantumChannel (Fin d) (Fin d))
    (G : Subgroup (Matrix.unitaryGroup (Fin d) ℂ)) [Fintype G] (n : ℕ) :
    Matrix (Fin n → Fin d × Fin d) (Fin n → Fin d × Fin d) ℂ :=
  fun r c => (Fintype.card G : ℂ)⁻¹ * ∑ g : G, ∏ k : Fin n, conjugatedEntry Λ g.val (r k) (c k)
def IsNContractive {d : ℕ}
    (Λ : QuantumChannel (Fin d) (Fin d))
    (G : Subgroup (Matrix.unitaryGroup (Fin d) ℂ)) [Fintype G] (n : ℕ) : Prop := by
  classical
  exact (((twirledTensorPower Λ G n).charpoly.roots).filter (fun z : ℂ => ‖z‖ = 1)).card ≤ 1
def claim : Prop := ∀ (d : ℕ), 2 ≤ d → ∀ (Λ : QuantumChannel (Fin d) (Fin d)) (G : Subgroup (Matrix.unitaryGroup (Fin d) ℂ)) [Fintype G], IsUnitaryTwoDesign G → (¬ ∃ U : Matrix.unitaryGroup (Fin d) ℂ, ∀ X : Matrix (Fin d) (Fin d) ℂ, CStarMatrix.ofMatrix.symm (Λ.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) = U.val * X * U.val.conjTranspose) → IsNContractive Λ G 2
end D5.S3.QuantumChannels.WallmanFlammiaTwoContractivity
open scoped BigOperators ComplexOrder
namespace D5.S3.QuantumChannels.WallmanFlammiaTwoContractivity.PurityEquality
private theorem probability_purity_one {ι : Type*} [Fintype ι] [DecidableEq ι] (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i) (hsum : ∑ i, x i = 1) (hsq : ∑ i, x i ^ 2 = 1) : ∃ k, ∀ j, x j = if j = k then 1 else 0 := by
  classical
  have hle (i : ι) : x i ≤ 1 := by
    rw [← hsum]; exact Finset.single_le_sum (fun j _ => hx j) (Finset.mem_univ i)
  have hterms (i : ι) : x i * (1 - x i) = 0 := by
    apply (Finset.sum_eq_zero_iff_of_nonneg (fun j (_ : j ∈ (Finset.univ : Finset ι)) =>
        mul_nonneg (hx j) (sub_nonneg.mpr (hle j)))).mp _ i (Finset.mem_univ i)
    calc
      (∑ j, x j * (1 - x j)) = (∑ j, x j) - ∑ j, x j ^ 2 := by
        simp_rw [mul_sub, mul_one, ← pow_two]; exact Finset.sum_sub_distrib _ _
      _ = 0 := by rw [hsum, hsq]; norm_num
  obtain ⟨k, hk⟩ : ∃ k, x k ≠ 0 := by
    by_contra h
    push_neg at h
    have hzero : ∑ i, x i = 0 := Finset.sum_eq_zero (fun i _ => h i)
    linarith
  have hk1 : x k = 1 := by
    have ht := (mul_eq_zero.mp (hterms k)).resolve_left hk
    linarith
  have herase : ∑ i ∈ (Finset.univ : Finset ι).erase k, x i = 0 := by
    have ht := Finset.sum_erase_add (Finset.univ : Finset ι) x (Finset.mem_univ k)
    rw [hsum, hk1] at ht; linarith
  refine ⟨k, fun j => ?_⟩
  by_cases hj : j = k
  · simp [hj, hk1]
  · simp only [hj, ↓reduceIte]
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hx i)).mp herase j (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩)
private theorem density_purity_one_outer {ι : Type*} [Fintype ι] [DecidableEq ι] (J : Matrix ι ι ℂ) (hJ : J.PosSemidef) (htrace : J.trace = 1) (hpurity : (J * J).trace = 1) : ∃ v : ι → ℂ, J = Matrix.vecMulVec v (star v) := by
  classical
  have hsum : ∑ i, hJ.1.eigenvalues i = 1 := by
    have ht := hJ.1.trace_eq_sum_eigenvalues
    rw [htrace] at ht
    have hr := congrArg Complex.re ht
    simpa using hr.symm
  have hsqcomplex : (J * J).trace = ∑ i, ((hJ.1.eigenvalues i : ℂ) ^ 2) := by
    conv_lhs => rw [hJ.1.spectral_theorem]
    rw [← map_mul]; simp only [Unitary.conjStarAlgAut_apply]; rw [Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, Matrix.one_mul]; simp [Matrix.diagonal_mul_diagonal, pow_two]
  have hsq : ∑ i, hJ.1.eigenvalues i ^ 2 = 1 := by
    rw [hpurity] at hsqcomplex
    have hr := congrArg Complex.re hsqcomplex
    simpa [pow_two, Complex.mul_re] using hr.symm
  obtain ⟨k, hk⟩ := probability_purity_one _ hJ.eigenvalues_nonneg hsum hsq
  let U := hJ.1.eigenvectorUnitary
  refine ⟨fun i => U.val i k, ?_⟩; rw [hJ.1.spectral_theorem]; simp only [Unitary.conjStarAlgAut_apply]; ext i j
  simp only [Matrix.mul_apply, Matrix.diagonal, Matrix.conjTranspose_apply, Matrix.vecMulVec_apply, Pi.star_apply, U]; simp [hk, apply_ite, mul_ite, ite_mul]
end D5.S3.QuantumChannels.WallmanFlammiaTwoContractivity.PurityEquality
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
namespace D5.S3.QuantumChannels.WallmanFlammiaTwoContractivity.ChoiRankOne
private theorem rank_one_choi_unitary {n : Type*} [Fintype n] [DecidableEq n] (F : MatrixMap n n ℂ) (hTP : ∀ X, (F X).trace = X.trace) (v : n × n → ℂ) (hJ : F.choi_matrix = Matrix.vecMulVec v (star v)) : ∃ U : Matrix.unitaryGroup n ℂ, ∀ X, F X = U.val * X * U.val.conjTranspose := by
  let K : Matrix n n ℂ := fun i j => v (i,j)
  have hF : F = MatrixMap.of_kraus (fun _ : Unit => K) (fun _ : Unit => K) := by
    apply MatrixMap.choi_matrix_inj; rw [hJ, MatrixMap.choi_of_kraus]; simp [K]; rfl
  have haction (X : Matrix n n ℂ) : F X = K * X * Kᴴ := by
    rw [hF]; simp [MatrixMap.of_kraus]
  have hK : Kᴴ * K = 1 := by
    have h := Original8340Global.kraus_normalization_from_actual_trace (fun _ : Unit => K) (fun X => by simpa [← haction X] using hTP X)
    simpa using h
  refine ⟨⟨K, Matrix.mem_unitaryGroup_iff'.mpr ?_⟩, haction⟩
  simpa only [Matrix.star_eq_conjTranspose] using hK
end D5.S3.QuantumChannels.WallmanFlammiaTwoContractivity.ChoiRankOne
namespace D5.S3.QuantumChannels.WallmanFlammiaTwoContractivity.ChannelPurity
open scoped BigOperators ComplexOrder
open D5.S3.Quantum.Foundation.FiniteKrausChannel
open D5.S3.Quantum.Recovery.LiJiangPolarPairOptimalityRefutation (matrixAction)
private theorem canonical_action_trace {d : ℕ} (Λ : QuantumChannel (Fin d) (Fin d)) (X : Matrix (Fin d) (Fin d) ℂ) : (matrixAction Λ.toCompletelyPositiveMap X).trace = X.trace := by
  exact Λ.trace_preserving (CStarMatrix.ofMatrix X)
private theorem canonical_action_choi_psd {d : ℕ} (Λ : QuantumChannel (Fin d) (Fin d)) : (matrixAction Λ.toCompletelyPositiveMap).choi_matrix.PosSemidef := by
  let K := krausRepresentation Λ.toCompletelyPositiveMap
  have hK : matrixAction Λ.toCompletelyPositiveMap = PhyslibLeaf.MatrixMap.of_kraus K.val K.val := by
    apply LinearMap.ext; intro X
    calc
      _ = CStarMatrix.ofMatrix.symm (Λ.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) := rfl
      _ = ∑ r, K.val r * X * (K.val r)ᴴ := K.property X
      _ = _ := by
        simp only [PhyslibLeaf.MatrixMap.of_kraus, LinearMap.sum_apply, LinearMap.coe_mk, AddHom.coe_mk]
  rw [hK]; exact (PhyslibLeaf.MatrixMap.choi_PSD_iff_CP_map _).mp (PhyslibLeaf.MatrixMap.of_kraus_isCompletelyPositive K.val)
private theorem canonical_choi_trace {d : ℕ} (Λ : QuantumChannel (Fin d) (Fin d)) : (matrixAction Λ.toCompletelyPositiveMap).choi_matrix.trace = (d : ℂ) := by
  simp only [Matrix.trace, Matrix.diag_apply, Fintype.sum_prod_type, PhyslibLeaf.MatrixMap.choi_matrix]; rw [Finset.sum_comm]
  change (∑ i : Fin d, (matrixAction Λ.toCompletelyPositiveMap (Matrix.single i i 1)).trace) = (d : ℂ); simp_rw [canonical_action_trace]; simp
private theorem maximal_choi_purity_unitary {d : ℕ} (hd : 0 < d) (Λ : QuantumChannel (Fin d) (Fin d)) (hpurity : (((matrixAction Λ.toCompletelyPositiveMap).choi_matrix) * ((matrixAction Λ.toCompletelyPositiveMap).choi_matrix)).trace = (d : ℂ)^2) : ∃ U : Matrix.unitaryGroup (Fin d) ℂ, ∀ X : Matrix (Fin d) (Fin d) ℂ, CStarMatrix.ofMatrix.symm (Λ.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) = U.val * X * U.val.conjTranspose := by
  let F := matrixAction Λ.toCompletelyPositiveMap
  let J := (d : ℂ)⁻¹ • F.choi_matrix
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hd)
  have hJ : J.PosSemidef := by
    exact (canonical_action_choi_psd Λ).smul (inv_nonneg.mpr (Nat.cast_nonneg d))
  have htrace : J.trace = 1 := by
    dsimp only [J]; rw [Matrix.trace_smul]; change (d : ℂ)⁻¹ * (matrixAction Λ.toCompletelyPositiveMap).choi_matrix.trace = 1; rw [canonical_choi_trace]; simp [hd0]
  have hp : (J * J).trace = 1 := by
    simp only [J, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.trace_smul, smul_eq_mul]; change ((d : ℂ)⁻¹ * (d : ℂ)⁻¹) * (F.choi_matrix * F.choi_matrix).trace = 1
    rw [hpurity]; field_simp
  obtain ⟨v, hv⟩ := PurityEquality.density_purity_one_outer J hJ htrace hp
  let w : Fin d × Fin d → ℂ := (Real.sqrt (d : ℝ) : ℂ) • v
  have hsqrt : (Real.sqrt (d : ℝ) : ℂ) ^ 2 = (d : ℂ) := by
    exact_mod_cast Real.sq_sqrt (show 0 ≤ (d : ℝ) by positivity)
  have houter : F.choi_matrix = Matrix.vecMulVec w (star w) := by
    calc
      F.choi_matrix = (d : ℂ) • J := by simp [J, smul_smul, hd0]
      _ = (d : ℂ) • Matrix.vecMulVec v (star v) := by rw [hv]
      _ = _ := by
        ext i j; simp only [w, Matrix.smul_apply, smul_eq_mul, Matrix.vecMulVec_apply, Pi.smul_apply, Pi.star_apply, star_mul, Complex.star_def, map_natCast, Complex.conj_ofReal]
        rw [← hsqrt]; ring
  obtain ⟨U, hU⟩ := ChoiRankOne.rank_one_choi_unitary F (canonical_action_trace Λ) w houter; exact ⟨U, hU⟩
open scoped BigOperators ComplexOrder
open D5.S3.Quantum.Recovery.LiJiangPolarPairOptimalityRefutation (matrixAction)
private def unitarityValue {d : ℕ} (Λ : QuantumChannel (Fin d) (Fin d)) : ℝ :=
  let F := matrixAction Λ.toCompletelyPositiveMap
  ((F.choi_matrix * F.choi_matrix).trace.re - ((F 1)ᴴ * F 1).trace.re / (d : ℝ)) / ((d : ℝ)^2 - 1)
private theorem strict_unitarity_value {d : ℕ} (hd : 2 ≤ d) (Λ : QuantumChannel (Fin d) (Fin d)) (hnot : ¬ ∃ U : Matrix.unitaryGroup (Fin d) ℂ, ∀ X : Matrix (Fin d) (Fin d) ℂ, CStarMatrix.ofMatrix.symm (Λ.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) = U.val * X * U.val.conjTranspose) : unitarityValue Λ < 1 := by
  let F := matrixAction Λ.toCompletelyPositiveMap
  let J := F.choi_matrix
  have hJ : J.PosSemidef := canonical_action_choi_psd Λ
  have ht : J.trace = (d : ℂ) := canonical_choi_trace Λ
  have hupper := D5.S3.Quantum.Entanglement.AbsoluteSeparability.GurvitsBarnumBall.psd_trace_sq J hJ
  rw [ht] at hupper; simp only [Complex.natCast_re] at hupper
  have houttrace : (F 1).trace = (d : ℂ) := by
    rw [canonical_action_trace, Matrix.trace_one, Fintype.card_fin]
  have hcs := D5.S3.Quantum.Matrix.CartesianVariance.trace_product_cauchy (1 : Matrix (Fin d) (Fin d) ℂ) (F 1)
  simp only [Matrix.one_mul, houttrace, RHLinalg.frobSq, Matrix.conjTranspose_one, Matrix.trace_one, Fintype.card_fin, Complex.natCast_re, RCLike.re_eq_complex_re, RCLike.natCast_re, Complex.normSq_natCast] at hcs
  have hdR : 0 < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  have hm : 0 < (d : ℝ)^2 - 1 := by
    have : 2 ≤ (d : ℝ) := by exact_mod_cast hd
    nlinarith
  have hlow : 1 ≤ ((F 1)ᴴ * F 1).trace.re / (d : ℝ) := by
    apply (le_div_iff₀ hdR).mpr; nlinarith
  by_contra hlt
  have hle : 1 ≤ unitarityValue Λ := le_of_not_gt hlt
  have hnum : (d : ℝ)^2 - 1 ≤ (J * J).trace.re - ((F 1)ᴴ * F 1).trace.re / (d : ℝ) := by
    simpa only [one_mul] using (le_div_iff₀ hm).mp hle
  have hreal : (J * J).trace.re = (d : ℝ)^2 := by linarith
  have hpure : (J * J).trace = (d : ℂ)^2 := by
    have hp := (Matrix.posSemidef_conjTranspose_mul_self J).trace_nonneg
    rw [hJ.isHermitian.eq] at hp
    rw [Complex.eq_re_of_ofReal_le hp, hreal]; norm_cast
  exact hnot (maximal_choi_purity_unitary (by omega) Λ hpure)
end D5.S3.QuantumChannels.WallmanFlammiaTwoContractivity.ChannelPurity
namespace D5.S3.QuantumChannels.WallmanFlammiaTwoContractivity.TransferGeometry
open scoped BigOperators Matrix.Norms.Frobenius
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
private theorem std_repr {d : ℕ} (X : Matrix (Fin d) (Fin d) ℂ) (r : Fin d × Fin d) : (Matrix.stdBasis ℂ (Fin d) (Fin d)).repr X r = X r.1 r.2 := by
  exact Module.Basis.repr_apply_eq (Matrix.stdBasis ℂ (Fin d) (Fin d))
    (fun X r => X r.1 r.2) (fun x => congrFun rfl) (fun c => congrFun rfl) (congrFun rfl) X r
private theorem transfer_entry {d : ℕ}
    (F : MatrixMap (Fin d) (Fin d) ℂ) (r c : Fin d × Fin d) :
    LinearMap.toMatrix (Matrix.stdBasis ℂ (Fin d) (Fin d)) (Matrix.stdBasis ℂ (Fin d) (Fin d)) F r c = F (Matrix.single c.1 c.2 1) r.1 r.2 := by
  rw [LinearMap.toMatrix_apply, std_repr, Matrix.stdBasis_eq_single]
private theorem transfer_action {d : ℕ} (F : MatrixMap (Fin d) (Fin d) ℂ) (X : Matrix (Fin d) (Fin d) ℂ) (r : Fin d × Fin d) : (LinearMap.toMatrix (Matrix.stdBasis ℂ (Fin d) (Fin d)) (Matrix.stdBasis ℂ (Fin d) (Fin d)) F *ᵥ (fun c : Fin d × Fin d => X c.1 c.2)) r = F X r.1 r.2 := by
  have h := LinearMap.toMatrix_mulVec_repr (Matrix.stdBasis ℂ (Fin d) (Fin d)) (Matrix.stdBasis ℂ (Fin d) (Fin d)) F X
  simpa only [Matrix.mulVec, dotProduct, std_repr] using congrFun h r
private theorem transfer_choi_purity {d : ℕ}
    (F : MatrixMap (Fin d) (Fin d) ℂ) (hJ : F.choi_matrix.IsHermitian) :
    (F.choi_matrix * F.choi_matrix).trace.re = ((LinearMap.toMatrix (Matrix.stdBasis ℂ (Fin d) (Fin d)) (Matrix.stdBasis ℂ (Fin d) (Fin d)) F)ᴴ * LinearMap.toMatrix (Matrix.stdBasis ℂ (Fin d) (Fin d)) (Matrix.stdBasis ℂ (Fin d) (Fin d)) F).trace.re := by
  classical
  have hleft : (F.choi_matrix * F.choi_matrix).trace.re = ∑ i, ∑ j, ‖F.choi_matrix i j‖ ^ 2 := by
    have h := D5.S3.Quantum.GNSMatrix.frobenius_norm_sq_eq_trace F.choi_matrix
    rw [hJ.eq] at h; rw [← h]; change ‖WithLp.toLp 2 (fun i => WithLp.toLp 2 (F.choi_matrix i))‖ ^ 2 = _; simp [PiLp.norm_sq_eq_of_L2]
  have hright : ((LinearMap.toMatrix (Matrix.stdBasis ℂ (Fin d) (Fin d)) (Matrix.stdBasis ℂ (Fin d) (Fin d)) F)ᴴ * LinearMap.toMatrix (Matrix.stdBasis ℂ (Fin d) (Fin d)) (Matrix.stdBasis ℂ (Fin d) (Fin d)) F).trace.re = ∑ i : Fin d, ∑ j : Fin d, ∑ a : Fin d, ∑ b : Fin d, ‖F (Matrix.single i j 1) a b‖ ^ 2 := by
    rw [← D5.S3.Quantum.GNSMatrix.frobenius_norm_sq_eq_trace]
    change ‖WithLp.toLp 2 (fun i => WithLp.toLp 2 (LinearMap.toMatrix (Matrix.stdBasis ℂ (Fin d) (Fin d)) (Matrix.stdBasis ℂ (Fin d) (Fin d)) F i))‖ ^ 2 = _
    simp only [PiLp.norm_sq_eq_of_L2]; rw [Finset.sum_comm]; simp only [Fintype.sum_prod_type, transfer_entry]
  rw [hright, hleft]; simp only [Fintype.sum_prod_type, MatrixMap.choi_matrix]; rw [Finset.sum_comm]
  calc
    _ = ∑ i : Fin d, ∑ a : Fin d, ∑ j : Fin d, ∑ b : Fin d, ‖F (Matrix.single i j 1) a b‖ ^ 2 := by
      apply Finset.sum_congr rfl; intro i hi; apply Finset.sum_congr rfl; intro a ha; rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl; intro i hi; rw [Finset.sum_comm]
open scoped BigOperators Kronecker
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
open D5.S3.Quantum.Recovery.LiJiangPolarPairOptimalityRefutation (matrixAction)
private theorem conjugationRep_action {d : ℕ}
    (U : Matrix.unitaryGroup (Fin d) ℂ)
    (X : Matrix (Fin d) (Fin d) ℂ) (r : Fin d × Fin d) :
    ((U.val ⊗ₖ U.val.map star) *ᵥ (fun c => X c.1 c.2)) r = (U.val * X * U.valᴴ) r.1 r.2 := by
  have h := Matrix.kronecker_mulVec_vec (U.val.map star) Xᵀ U.val
  have ht : U.val.map star * Xᵀ * U.valᵀ = (U.val * X * U.valᴴ)ᵀ := by
    simp only [Matrix.transpose_mul]
    change U.val.map star * Xᵀ * U.valᵀ = U.val.map star * (Xᵀ * U.valᵀ)
    exact Matrix.mul_assoc _ _ _
  rw [ht] at h
  change (U.val ⊗ₖ U.val.map star) *ᵥ (fun c : Fin d × Fin d => X c.1 c.2) = (U.val * X * U.valᴴ)ᵀ.vec at h
  exact congrFun h r
private theorem twirledTensorPower_two_reindex {d : ℕ}
    (Λ : QuantumChannel (Fin d) (Fin d))
    (G : Subgroup (Matrix.unitaryGroup (Fin d) ℂ)) [Fintype G] :
    Matrix.reindex (finTwoArrowEquiv (Fin d × Fin d)) (finTwoArrowEquiv (Fin d × Fin d)) (twirledTensorPower Λ G 2) = (Fintype.card G : ℂ)⁻¹ • (∑ g : G, (fun r c => conjugatedEntry Λ g.val r c) ⊗ₖ (fun r c => conjugatedEntry Λ g.val r c)) := by
  classical
  ext r c
  simp [Matrix.reindex, Matrix.submatrix, finTwoArrowEquiv, twirledTensorPower, Matrix.smul_apply, Matrix.sum_apply, Matrix.kroneckerMap, Matrix.of_apply, Fin.prod_univ_two]
end D5.S3.QuantumChannels.WallmanFlammiaTwoContractivity.TransferGeometry
open D5.S3.Quantum.RandomCircuits.CHaarConcatenationNonmonotone (haarAverageEntry)
open scoped Kronecker
namespace D5.S3.QuantumChannels.WallmanFlammiaTwoContractivity.DesignEntries
private theorem design_haar_entry {d : ℕ} (G : Subgroup (Matrix.unitaryGroup (Fin d) ℂ)) [Fintype G] (hG : IsUnitaryTwoDesign G) (r c : ((Fin d × Fin d) × (Fin d × Fin d))) : (Fintype.card G : ℂ)⁻¹ * (∑ g : G, literalMoment g.val.val r c) = haarAverage (Fin d) r c := by
  simpa only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul] using congrFun (congrFun hG r) c
private theorem average_rep_entry {d : ℕ} (G : Subgroup (Matrix.unitaryGroup (Fin d) ℂ)) [Fintype G] (hG : IsUnitaryTwoDesign G) (H : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (r c : Fin d × Fin d) : ((Fintype.card G : ℂ)⁻¹ • (∑ g : G, ((g.val.val ⊗ₖ g.val.val.map star))ᴴ * H * (g.val.val ⊗ₖ g.val.val.map star))) r c = ∑ q : Fin d × Fin d, ∑ p : Fin d × Fin d, H p q * haarAverage (Fin d) ((p.1,q.2),(p.2,q.1)) ((r.1,c.2),(r.2,c.1)) := by
  classical
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.sum_apply, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro q hq
  rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro p hp
  calc
    _ = H p q * ((Fintype.card G : ℂ)⁻¹ * ∑ g : G, literalMoment g.val.val ((p.1,q.2),(p.2,q.1)) ((r.1,c.2),(r.2,c.1))) := by
      simp only [Finset.mul_sum, Matrix.conjTranspose_apply, literalMoment, Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.map_apply, star_mul, star_star]
      apply Finset.sum_congr rfl; intro g hg; ring
    _ = _ := by rw [design_haar_entry G hG]
private theorem diagonal_pair_sum {d : ℕ} (H : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) : (∑ q : Fin d × Fin d, ∑ p : Fin d × Fin d, H p q * (if p.1 = p.2 ∧ q.1 = q.2 then 1 else 0)) = ∑ i : Fin d, ∑ j : Fin d, H (i,i) (j,j) := by
  classical
  simp only [Fintype.sum_prod_type]; simp [ite_and]; rw [Finset.sum_comm]
private theorem fourth_moment_reshaped {d : ℕ} (hd : 2 ≤ d) (p q r c : Fin d × Fin d) : haarAverage (Fin d) ((p.1,q.2),(p.2,q.1)) ((r.1,c.2),(r.2,c.1)) = (((if r.1 = r.2 ∧ c.1 = c.2 then 1 else 0 : ℂ) - (if r = c then 1 else 0 : ℂ) / (d : ℂ)) / ((d : ℂ)^2-1)) * (if p.1 = p.2 ∧ q.1 = q.2 then 1 else 0) + (((if r = c then 1 else 0 : ℂ) - (if r.1 = r.2 ∧ c.1 = c.2 then 1 else 0 : ℂ) / (d : ℂ)) / ((d : ℂ)^2-1)) * (if p = q then 1 else 0) := by
  have h := haarAverageEntry ((p.1,q.2),(p.2,q.1)) ((r.1,c.2),(r.2,c.1)) (by simpa using hd)
  simpa [Prod.ext_iff, and_comm, and_left_comm, eq_comm] using h
private theorem averaged_endomorphism_entry {d : ℕ} (hd : 2 ≤ d) (G : Subgroup (Matrix.unitaryGroup (Fin d) ℂ)) [Fintype G] (hG : IsUnitaryTwoDesign G) (H : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (r c : Fin d × Fin d) : ((Fintype.card G : ℂ)⁻¹ • (∑ g : G, ((g.val.val ⊗ₖ g.val.val.map star))ᴴ * H * (g.val.val ⊗ₖ g.val.val.map star))) r c = (((if r.1 = r.2 ∧ c.1 = c.2 then 1 else 0 : ℂ) - (if r = c then 1 else 0 : ℂ) / (d : ℂ)) / ((d : ℂ)^2-1)) * (∑ i : Fin d, ∑ j : Fin d, H (i,i) (j,j)) + (((if r = c then 1 else 0 : ℂ) - (if r.1 = r.2 ∧ c.1 = c.2 then 1 else 0 : ℂ) / (d : ℂ)) / ((d : ℂ)^2-1)) * H.trace := by
  classical
  rw [average_rep_entry G hG]; simp_rw [fourth_moment_reshaped hd]; simp only [mul_add, Finset.sum_add_distrib]; congr 1
  · rw [← diagonal_pair_sum H]
    simp only [Finset.mul_sum]; apply Finset.sum_congr rfl; intro q hq; apply Finset.sum_congr rfl; intro p hp; ring
  · simp [Matrix.trace, Matrix.diag_apply, Finset.mul_sum, mul_ite, mul_comm]
open scoped BigOperators Kronecker Matrix.Norms.L2Operator
private theorem scalarProjector_eq (d : ℕ) : D5.S3.QuantumBounds.PeritoTsirelson.maxEntangled (Fin d) =
    (d : ℂ)⁻¹ • Matrix.vecMulVec (Matrix.vec (1 : Matrix (Fin d) (Fin d) ℂ)) (Matrix.vec (1 : Matrix (Fin d) (Fin d) ℂ)) := by
  have hs : ((Real.sqrt (d : ℝ) : ℂ))⁻¹ * ((Real.sqrt (d : ℝ) : ℂ))⁻¹ = (d : ℂ)⁻¹ := by
    rw [← pow_two, inv_pow, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg d)]; simp only [Complex.ofReal_natCast]
  symm; ext r c
  simp only [D5.S3.QuantumBounds.PeritoTsirelson.maxEntangled, D5.S3.QuantumBounds.PeritoTsirelson.maxEntangledVector,
    Matrix.smul_apply, smul_eq_mul, Matrix.vecMulVec_apply, Matrix.vec, Matrix.one_apply, Pi.star_apply, Fintype.card_fin]
  by_cases hr : r.1 = r.2 <;> by_cases hc : c.1 = c.2 <;>
    simp [hr, hc, eq_comm, Complex.conj_ofReal, hs]
private theorem scalarProjector_eq_Q (d : ℕ) : D5.S3.QuantumBounds.PeritoTsirelson.maxEntangled (Fin d) = D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability.Q d := by
  rw [scalarProjector_eq, D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability.Q,
    Matrix.star_vec, Matrix.map_one star (by simp) (by simp)]
private def tracelessProjector (d : ℕ) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ := 1 - D5.S3.QuantumBounds.PeritoTsirelson.maxEntangled (Fin d)
private theorem traceVector_dot (d : ℕ) : (Matrix.vec (1 : Matrix (Fin d) (Fin d) ℂ)) ⬝ᵥ (Matrix.vec (1 : Matrix (Fin d) (Fin d) ℂ)) = (d : ℂ) := by
  simpa [Matrix.star_vec, Matrix.map_one, Matrix.trace_one] using Matrix.star_vec_dotProduct_vec (1 : Matrix (Fin d) (Fin d) ℂ) 1
private theorem scalarProjector_projection {d : ℕ} (hd : 0 < d) : IsStarProjection (D5.S3.QuantumBounds.PeritoTsirelson.maxEntangled (Fin d)) := by
  rw [isStarProjection_iff', Matrix.star_eq_conjTranspose]
  constructor
  · simpa only [scalarProjector_eq_Q] using D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability.Q_square hd
  · simpa only [scalarProjector_eq_Q] using D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability.Q_hermitian d
private theorem tracelessProjector_projection {d : ℕ} (hd : 0 < d) : IsStarProjection (tracelessProjector d) := (scalarProjector_projection hd).one_sub
private theorem scalarProjector_entry (d : ℕ) (r c : Fin d × Fin d) : D5.S3.QuantumBounds.PeritoTsirelson.maxEntangled (Fin d) r c = (if r.1 = r.2 ∧ c.1 = c.2 then 1 else 0 : ℂ) / (d : ℂ) := by
  classical
  simp only [scalarProjector_eq, Matrix.smul_apply, smul_eq_mul, Matrix.vecMulVec_apply, Matrix.vec, Matrix.one_apply, eq_comm]
  split_ifs <;> simp_all [div_eq_mul_inv]
private theorem averaged_traceless_endomorphism {d : ℕ} (hd : 2 ≤ d) (G : Subgroup (Matrix.unitaryGroup (Fin d) ℂ)) [Fintype G] (hG : IsUnitaryTwoDesign G) (H : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (hzero : (∑ i : Fin d, ∑ j : Fin d, H (i,i) (j,j)) = 0) : (Fintype.card G : ℂ)⁻¹ • (∑ g : G, ((g.val.val ⊗ₖ g.val.val.map star))ᴴ * H * (g.val.val ⊗ₖ g.val.val.map star)) = (H.trace / ((d : ℂ)^2 - 1)) • tracelessProjector d := by
  classical
  ext r c; rw [averaged_endomorphism_entry hd G hG, hzero]
  simp only [mul_zero, zero_add, Matrix.smul_apply, smul_eq_mul, tracelessProjector, Matrix.sub_apply, Matrix.one_apply, scalarProjector_entry]; ring
end D5.S3.QuantumChannels.WallmanFlammiaTwoContractivity.DesignEntries
namespace D5.S3.QuantumChannels.WallmanFlammiaTwoContractivity.ProjectionMass
private theorem projection_mass_split {n : Type*} [Fintype n] [DecidableEq n] (S L : Matrix n n ℂ) (hS : IsStarProjection S) : ((L * (1 - S))ᴴ * (L * (1 - S))).trace = (Lᴴ * L).trace - ((L * S)ᴴ * (L * S)).trace := by
  have hmass (P : Matrix n n ℂ) (hp : P * P = P) (hPH : Pᴴ = P) : ((L * P)ᴴ * (L * P)).trace = ((Lᴴ * L) * P).trace := by
    calc
      _ = (P * (Lᴴ * L) * P).trace := by
        simp only [Matrix.conjTranspose_mul, hPH, Matrix.mul_assoc]
      _ = _ := by
        rw [Matrix.trace_mul_cycle P (Lᴴ * L) P, ← Matrix.mul_assoc, hp]
        simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm P (Lᴴ * L)
  rw [hmass (1 - S) hS.one_sub.isIdempotentElem.eq hS.one_sub.isSelfAdjoint.star_eq, hmass S hS.isIdempotentElem.eq hS.isSelfAdjoint.star_eq]
  rw [Matrix.mul_sub, Matrix.mul_one, Matrix.trace_sub]
private theorem trace_product_cauchy_generic {n : Type*} [Fintype n] [DecidableEq n] (Q B : Matrix n n ℂ) : Complex.normSq (Q * B).trace ≤ (Qᴴ * Q).trace.re * (Bᴴ * B).trace.re := by
  let e := Fintype.equivFin n
  let R := Matrix.reindexRingEquiv ℂ e
  have hm (A C : Matrix n n ℂ) : R (A * C) = R A * R C := R.map_mul A C
  have ht (A : Matrix n n ℂ) : (R A).trace = A.trace := e.symm.sum_comp (fun i => A i i)
  have hs (A : Matrix n n ℂ) : (R A)ᴴ = R Aᴴ := Matrix.conjTranspose_reindex e e A
  have hc := D5.S3.Quantum.Matrix.CartesianVariance.trace_product_cauchy (R Q) (R B)
  simpa only [RHLinalg.frobSq, hs, ← hm, ht, RCLike.re_eq_complex_re] using hc
private theorem strict_projected_one_copy_bound {n : Type*} [Fintype n] [DecidableEq n] (P B : Matrix n n ℂ) (hP : IsStarProjection P) (hPB : P * B = B) (m u : ℝ) (hm : 0 < m) (hu : u < 1) (htrace : P.trace.re = m) (hmass : (Bᴴ * B).trace.re = m * u) : ‖B.trace / (m : ℂ)‖ < 1 := by
  have hPH : Pᴴ = P := hP.isSelfAdjoint.star_eq
  have hPP : P * P = P := hP.isIdempotentElem.eq
  have hc := trace_product_cauchy_generic P B
  rw [hPB, hPH, hPP, htrace, hmass, Complex.normSq_eq_norm_sq] at hc
  have hsmall : ‖B.trace‖ < m := by
    nlinarith [norm_nonneg B.trace, mul_pos hm hm]
  simpa only [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hm] using (div_lt_one hm).mpr hsmall
end D5.S3.QuantumChannels.WallmanFlammiaTwoContractivity.ProjectionMass
namespace D5.S3.QuantumChannels.WallmanFlammiaTwoContractivity.DesignEntries
private theorem scalarProjector_trace {d : ℕ} (hd : 0 < d) : (D5.S3.QuantumBounds.PeritoTsirelson.maxEntangled (Fin d)).trace = 1 := by
  letI : NeZero d := ⟨Nat.ne_zero_of_lt hd⟩
  exact (D5.S3.QuantumBounds.PeritoTsirelson.max_entangled_density (Fin d)).2
private theorem tracelessProjector_trace {d : ℕ} (hd : 0 < d) : (tracelessProjector d).trace = (d : ℂ)^2 - 1 := by
  rw [tracelessProjector, Matrix.trace_sub, Matrix.trace_one, scalarProjector_trace hd]; simp [Fintype.card_prod, pow_two]
private theorem tracelessProjector_kills_trace {d : ℕ} (hd : 0 < d) : tracelessProjector d *ᵥ (Matrix.vec (1 : Matrix (Fin d) (Fin d) ℂ)) = 0 := by
  classical
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_zero_of_lt hd
  rw [tracelessProjector, Matrix.sub_mulVec, Matrix.one_mulVec, scalarProjector_eq, Matrix.smul_mulVec, Matrix.vecMulVec_mulVec, traceVector_dot]; ext i
  simp [Pi.smul_apply, smul_eq_mul, hd0] <;> field_simp [hd0] <;> ring
private theorem diagonal_pair_sum_zero_of_kills_trace {d : ℕ} (H : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (hkill : H *ᵥ (Matrix.vec (1 : Matrix (Fin d) (Fin d) ℂ)) = 0) : (∑ i : Fin d, ∑ j : Fin d, H (i,i) (j,j)) = 0 := by
  classical
  have h (i : Fin d) : ∑ j : Fin d, H (i,i) (j,j) = 0 := by
    have hi := congrFun hkill (i,i)
    simpa [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.vec, Matrix.one_apply, eq_comm] using hi
  simp_rw [h]; simp
private theorem projected_gram_averages {d : ℕ} (hd : 2 ≤ d) (G : Subgroup (Matrix.unitaryGroup (Fin d) ℂ)) [Fintype G] (hG : IsUnitaryTwoDesign G) (L : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    let B := tracelessProjector d * L * tracelessProjector d
    ((Fintype.card G : ℂ)⁻¹ • (∑ g : G, ((g.val.val ⊗ₖ g.val.val.map star))ᴴ * (Bᴴ * B) * (g.val.val ⊗ₖ g.val.val.map star)) = ((Bᴴ * B).trace / ((d : ℂ)^2 - 1)) • tracelessProjector d) ∧
    ((Fintype.card G : ℂ)⁻¹ • (∑ g : G, ((g.val.val ⊗ₖ g.val.val.map star))ᴴ * (B * Bᴴ) * (g.val.val ⊗ₖ g.val.val.map star)) = ((Bᴴ * B).trace / ((d : ℂ)^2 - 1)) • tracelessProjector d) := by
  classical
  intro B
  have hk := tracelessProjector_kills_trace (show 0 < d by omega)
  have hPH : (tracelessProjector d)ᴴ = tracelessProjector d := (tracelessProjector_projection (show 0 < d by omega)).isSelfAdjoint.star_eq
  have hB : B *ᵥ (Matrix.vec (1 : Matrix (Fin d) (Fin d) ℂ)) = 0 := by
    dsimp only [B]; rw [← Matrix.mulVec_mulVec, hk, Matrix.mulVec_zero]
  have hBH : Bᴴ *ᵥ (Matrix.vec (1 : Matrix (Fin d) (Fin d) ℂ)) = 0 := by
    dsimp only [B]; rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hPH]; rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hk, Matrix.mulVec_zero, Matrix.mulVec_zero]
  constructor
  · apply averaged_traceless_endomorphism hd G hG
    apply diagonal_pair_sum_zero_of_kills_trace; rw [← Matrix.mulVec_mulVec, hB, Matrix.mulVec_zero]
  · rw [Matrix.trace_mul_comm Bᴴ B]
    apply averaged_traceless_endomorphism hd G hG; apply diagonal_pair_sum_zero_of_kills_trace; rw [← Matrix.mulVec_mulVec, hBH, Matrix.mulVec_zero]
end D5.S3.QuantumChannels.WallmanFlammiaTwoContractivity.DesignEntries
namespace D5.S3.QuantumChannels.WallmanFlammiaTwoContractivity.TransferGeometry
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
open D5.S3.QuantumChannels.WallmanFlammiaTwoContractivity.DesignEntries
private theorem transfer_scalar_row {d : ℕ}
    (F : MatrixMap (Fin d) (Fin d) ℂ)
    (hTP : ∀ X, (F X).trace = X.trace) :
    (Matrix.vec (1 : Matrix (Fin d) (Fin d) ℂ)) ᵥ* LinearMap.toMatrix (Matrix.stdBasis ℂ (Fin d) (Fin d)) (Matrix.stdBasis ℂ (Fin d) (Fin d)) F = (Matrix.vec (1 : Matrix (Fin d) (Fin d) ℂ)) := by
  classical
  ext c
  have hs : (Matrix.single c.1 c.2 (1 : ℂ)).trace = (Matrix.vec (1 : Matrix (Fin d) (Fin d) ℂ)) c := by
    by_cases h : c.1 = c.2
    · rw [h, Matrix.trace_single_eq_same]
      simp [Matrix.vec, Matrix.one_apply, eq_comm, h]
    · rw [Matrix.trace_single_eq_of_ne c.1 c.2 1 h]
      simp [Matrix.vec, Matrix.one_apply, eq_comm, h]
  have ht := (hTP (Matrix.single c.1 c.2 1)).trans hs
  simpa [Matrix.vecMul, dotProduct, Fintype.sum_prod_type, Matrix.vec, Matrix.one_apply, eq_comm, transfer_entry, Matrix.trace, Matrix.diag_apply] using ht
private theorem transfer_scalar_left {d : ℕ}
    (F : MatrixMap (Fin d) (Fin d) ℂ)
    (hTP : ∀ X, (F X).trace = X.trace) :
    D5.S3.QuantumBounds.PeritoTsirelson.maxEntangled (Fin d) * LinearMap.toMatrix (Matrix.stdBasis ℂ (Fin d) (Fin d)) (Matrix.stdBasis ℂ (Fin d) (Fin d)) F = D5.S3.QuantumBounds.PeritoTsirelson.maxEntangled (Fin d) := by
  rw [scalarProjector_eq, Matrix.smul_mul, Matrix.vecMulVec_mul, transfer_scalar_row F hTP]
private theorem transfer_traceless_compression {d : ℕ} (hd : 0 < d) (F : MatrixMap (Fin d) (Fin d) ℂ) (hTP : ∀ X, (F X).trace = X.trace) : tracelessProjector d * LinearMap.toMatrix (Matrix.stdBasis ℂ (Fin d) (Fin d)) (Matrix.stdBasis ℂ (Fin d) (Fin d)) F * tracelessProjector d = LinearMap.toMatrix (Matrix.stdBasis ℂ (Fin d) (Fin d)) (Matrix.stdBasis ℂ (Fin d) (Fin d)) F * tracelessProjector d := by
  have hS := (scalarProjector_projection hd).isIdempotentElem.eq
  have hSL := transfer_scalar_left F hTP
  dsimp only [tracelessProjector]; rw [Matrix.sub_mul, Matrix.one_mul, Matrix.sub_mul, hSL, Matrix.mul_sub (D5.S3.QuantumBounds.PeritoTsirelson.maxEntangled (Fin d)), Matrix.mul_one, hS, sub_self, sub_zero]
private theorem transfer_scalar_image {d : ℕ}
    (F : MatrixMap (Fin d) (Fin d) ℂ) :
    LinearMap.toMatrix (Matrix.stdBasis ℂ (Fin d) (Fin d)) (Matrix.stdBasis ℂ (Fin d) (Fin d)) F * D5.S3.QuantumBounds.PeritoTsirelson.maxEntangled (Fin d) = (d : ℂ)⁻¹ • Matrix.vecMulVec (fun r : Fin d × Fin d => F 1 r.1 r.2) ((Matrix.vec (1 : Matrix (Fin d) (Fin d) ℂ))) := by
  rw [scalarProjector_eq, Matrix.mul_smul, Matrix.mul_vecMulVec]; congr 1; congr 1; funext r
  have ht : (Matrix.vec (1 : Matrix (Fin d) (Fin d) ℂ)) = (fun c : Fin d × Fin d =>
      (1 : Matrix (Fin d) (Fin d) ℂ) c.1 c.2) := by
    change (1 : Matrix (Fin d) (Fin d) ℂ).vec = (1 : Matrix (Fin d) (Fin d) ℂ)ᵀ.vec
    rw [Matrix.transpose_one]
  rw [ht]; exact transfer_action F 1 r
open scoped BigOperators ComplexOrder
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
open D5.S3.Quantum.Recovery.LiJiangPolarPairOptimalityRefutation (matrixAction)
open D5.S3.QuantumChannels.WallmanFlammiaTwoContractivity.DesignEntries
private theorem transfer_scalar_mass {d : ℕ} (hd : 0 < d) (F : MatrixMap (Fin d) (Fin d) ℂ) : ((LinearMap.toMatrix (Matrix.stdBasis ℂ (Fin d) (Fin d)) (Matrix.stdBasis ℂ (Fin d) (Fin d)) F * D5.S3.QuantumBounds.PeritoTsirelson.maxEntangled (Fin d))ᴴ * (LinearMap.toMatrix (Matrix.stdBasis ℂ (Fin d) (Fin d)) (Matrix.stdBasis ℂ (Fin d) (Fin d)) F * D5.S3.QuantumBounds.PeritoTsirelson.maxEntangled (Fin d))).trace = ((F 1)ᴴ * F 1).trace / (d : ℂ) := by
  classical
  let v : Fin d × Fin d → ℂ := fun r => F 1 r.1 r.2
  have hstar : star ((Matrix.vec (1 : Matrix (Fin d) (Fin d) ℂ))) = (Matrix.vec (1 : Matrix (Fin d) (Fin d) ℂ)) := by
    rw [Matrix.star_vec, Matrix.map_one star (by simp) (by simp)]
  have hv : star v ⬝ᵥ v = ((F 1)ᴴ * F 1).trace := by
    calc
      _ = star (Matrix.vec (F 1)) ⬝ᵥ Matrix.vec (F 1) := by simp only [v, dotProduct, Fintype.sum_prod_type, Pi.star_apply, Matrix.vec]; rw [Finset.sum_comm]
      _ = _ := Matrix.star_vec_dotProduct_vec (F 1) (F 1)
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_zero_of_lt hd
  rw [transfer_scalar_image, Matrix.conjTranspose_inv_natCast_smul, Matrix.conjTranspose_vecMulVec, hstar, Matrix.smul_mul, Matrix.mul_smul, Matrix.vecMulVec_mul_vecMulVec, Matrix.vecMulVec_smul, Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_vecMulVec, traceVector_dot, hv]
  simp only [star_inv, star_natCast, smul_eq_mul]; field_simp [hd0] <;> simp [star_natCast, Complex.star_def, hd0] <;> ring
private theorem canonical_projected_mass {d : ℕ} (hd : 0 < d) (Λ : QuantumChannel (Fin d) (Fin d)) :
    let F := matrixAction Λ.toCompletelyPositiveMap
    let B := tracelessProjector d * LinearMap.toMatrix (Matrix.stdBasis ℂ (Fin d) (Fin d)) (Matrix.stdBasis ℂ (Fin d) (Fin d)) F * tracelessProjector d
    (Bᴴ * B).trace.re = (F.choi_matrix * F.choi_matrix).trace.re - ((F 1)ᴴ * F 1).trace.re / (d : ℝ) := by
  intro F B
  rw [show B = LinearMap.toMatrix (Matrix.stdBasis ℂ (Fin d) (Fin d)) (Matrix.stdBasis ℂ (Fin d) (Fin d)) F * tracelessProjector d from transfer_traceless_compression hd F (ChannelPurity.canonical_action_trace Λ)]
  have hsplit := ProjectionMass.projection_mass_split (D5.S3.QuantumBounds.PeritoTsirelson.maxEntangled (Fin d)) (LinearMap.toMatrix (Matrix.stdBasis ℂ (Fin d) (Fin d)) (Matrix.stdBasis ℂ (Fin d) (Fin d)) F) (scalarProjector_projection hd)
  change ((LinearMap.toMatrix (Matrix.stdBasis ℂ (Fin d) (Fin d)) (Matrix.stdBasis ℂ (Fin d) (Fin d)) F * tracelessProjector d)ᴴ * (LinearMap.toMatrix (Matrix.stdBasis ℂ (Fin d) (Fin d)) (Matrix.stdBasis ℂ (Fin d) (Fin d)) F * tracelessProjector d)).trace = _ at hsplit
  rw [transfer_scalar_mass hd F] at hsplit
  have hreal := congrArg Complex.re hsplit
  rw [Complex.sub_re] at hreal; rw [← transfer_choi_purity F (ChannelPurity.canonical_action_choi_psd Λ).isHermitian] at hreal
  simpa only [Complex.sub_re, ← Complex.ofReal_natCast, Complex.div_ofReal_re] using hreal
private theorem canonical_unitarity_mass {d : ℕ} (hd : 2 ≤ d) (Λ : QuantumChannel (Fin d) (Fin d)) :
    let F := matrixAction Λ.toCompletelyPositiveMap
    let B := tracelessProjector d * LinearMap.toMatrix (Matrix.stdBasis ℂ (Fin d) (Fin d)) (Matrix.stdBasis ℂ (Fin d) (Fin d)) F * tracelessProjector d
    (Bᴴ * B).trace.re = ((d : ℝ)^2 - 1) * ChannelPurity.unitarityValue Λ := by
  intro F B; rw [canonical_projected_mass (by omega) Λ]; dsimp only [ChannelPurity.unitarityValue]
  have hm : (d : ℝ)^2 - 1 ≠ 0 := by
    have h : 2 ≤ (d : ℝ) := by exact_mod_cast hd
    nlinarith
  field_simp <;> ring
private theorem canonical_unitarity_nonneg {d : ℕ} (hd : 2 ≤ d) (Λ : QuantumChannel (Fin d) (Fin d)) : 0 ≤ ChannelPurity.unitarityValue Λ := by
  let B := tracelessProjector d * LinearMap.toMatrix (Matrix.stdBasis ℂ (Fin d) (Fin d)) (Matrix.stdBasis ℂ (Fin d) (Fin d)) (matrixAction Λ.toCompletelyPositiveMap) *
    tracelessProjector d
  have hp : 0 ≤ (Bᴴ * B).trace.re := (Complex.nonneg_iff.mp (Matrix.posSemidef_conjTranspose_mul_self B).trace_nonneg).1
  rw [canonical_unitarity_mass hd Λ] at hp
  have hm : 0 < (d : ℝ)^2 - 1 := by
    have h : 2 ≤ (d : ℝ) := by exact_mod_cast hd
    nlinarith
  exact nonneg_of_mul_nonneg_right hp hm
end D5.S3.QuantumChannels.WallmanFlammiaTwoContractivity.TransferGeometry
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Kronecker Matrix.Norms.L2Operator
namespace D5.S3.QuantumChannels.WallmanFlammiaTwoContractivity.TensorGram
variable {n g : Type*} [Fintype n] [DecidableEq n] [Fintype g]
private def tensorRow (A : g → Matrix n n ℂ) : Matrix (n × n) (g × (n × n)) ℂ := fun r c => (A c.1 ⊗ₖ (1 : Matrix n n ℂ)) r c.2
private def tensorCol (A : g → Matrix n n ℂ) : Matrix (g × (n × n)) (n × n) ℂ := fun r c => ((1 : Matrix n n ℂ) ⊗ₖ A r.1) r.2 c
private theorem row_col (A : g → Matrix n n ℂ) : tensorRow A * tensorCol A = ∑ a, A a ⊗ₖ A a := by
  ext r c; simp only [Matrix.mul_apply, Fintype.sum_prod_type, tensorRow, tensorCol, Matrix.sum_apply]; apply Finset.sum_congr rfl; intro a ha
  have h := congrFun (congrFun (Matrix.mul_kronecker_mul (A a) (1 : Matrix n n ℂ) (1 : Matrix n n ℂ) (A a)).symm r) c
  simpa only [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.mul_one, Matrix.one_mul] using h
private theorem row_gram (A : g → Matrix n n ℂ) : tensorRow A * (tensorRow A)ᴴ = (∑ a, A a * (A a)ᴴ) ⊗ₖ (1 : Matrix n n ℂ) := by
  ext r c; simp only [Matrix.mul_apply, Fintype.sum_prod_type, tensorRow, Matrix.conjTranspose_apply]
  have h (a : g) : (∑ k, ∑ l, (A a ⊗ₖ (1 : Matrix n n ℂ)) r (k,l) * star ((A a ⊗ₖ (1 : Matrix n n ℂ)) c (k,l))) = ((A a * (A a)ᴴ) ⊗ₖ (1 : Matrix n n ℂ)) r c := by
    have hmat : (A a ⊗ₖ (1 : Matrix n n ℂ)) * (A a ⊗ₖ (1 : Matrix n n ℂ))ᴴ = (A a * (A a)ᴴ) ⊗ₖ (1 : Matrix n n ℂ) := by
      rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul, Matrix.one_mul]
    simpa only [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.conjTranspose_apply] using congrFun (congrFun hmat r) c
  simp_rw [h]
  rcases r with ⟨i,j⟩
  rcases c with ⟨k,l⟩
  simp [Matrix.kroneckerMap_apply, Matrix.sum_apply, Finset.sum_mul]
private theorem col_gram (A : g → Matrix n n ℂ) : (tensorCol A)ᴴ * tensorCol A = (1 : Matrix n n ℂ) ⊗ₖ (∑ a, (A a)ᴴ * A a) := by
  ext r c; simp only [Matrix.mul_apply, Fintype.sum_prod_type, tensorCol, Matrix.conjTranspose_apply]
  have h (a : g) : (∑ k, ∑ l, star (((1 : Matrix n n ℂ) ⊗ₖ A a) (k,l) r) * ((1 : Matrix n n ℂ) ⊗ₖ A a) (k,l) c) = ((1 : Matrix n n ℂ) ⊗ₖ ((A a)ᴴ * A a)) r c := by
    have hmat : ((1 : Matrix n n ℂ) ⊗ₖ A a)ᴴ * ((1 : Matrix n n ℂ) ⊗ₖ A a) = (1 : Matrix n n ℂ) ⊗ₖ ((A a)ᴴ * A a) := by
      rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul, Matrix.one_mul]
    simpa only [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.conjTranspose_apply] using congrFun (congrFun hmat r) c
  simp_rw [h]
  rcases r with ⟨i,j⟩
  rcases c with ⟨k,l⟩
  simp [Matrix.kroneckerMap_apply, Matrix.sum_apply, Finset.mul_sum]
end D5.S3.QuantumChannels.WallmanFlammiaTwoContractivity.TensorGram
open Polynomial Matrix
namespace D5.S3.QuantumChannels.WallmanFlammiaTwoContractivity.SpectralClosure
private theorem unit_circle_roots_of_factor (p q : ℂ[X]) (hq : q ≠ 0) (hp : p = (X - C 1) * q) (hinside : ∀ z ∈ q.roots, ‖z‖ < 1) : (p.roots.filter (fun z : ℂ => ‖z‖ = 1)).card = 1 := by
  classical
  have hempty : q.roots.filter (fun z : ℂ => ‖z‖ = 1) = 0 := by
    apply Multiset.filter_eq_nil.mpr; intro z hz; exact ne_of_lt (hinside z hz)
  rw [hp, Polynomial.roots_mul (mul_ne_zero (X_sub_C_ne_zero 1) hq), Polynomial.roots_X_sub_C, Multiset.filter_add, hempty]; simp [Multiset.filter_singleton]
private theorem unit_circle_roots_of_block_bound (m : ℕ) (f : ℂ) (u : ℝ) (p q : ℂ[X]) (hq : q ≠ 0) (hp : p = (X - C 1) * ((X - C f) ^ (2 * m) * q)) (hf : ‖f‖ < 1) (hu : u < 1) (hbound : ∀ z ∈ q.roots, ‖z‖ ≤ u) : (p.roots.filter (fun z : ℂ => ‖z‖ = 1)).card = 1 := by
  classical
  apply unit_circle_roots_of_factor p ((X - C f) ^ (2 * m) * q) (mul_ne_zero (pow_ne_zero _ (X_sub_C_ne_zero f)) hq) hp; intro z hz
  rw [Polynomial.roots_mul (mul_ne_zero (pow_ne_zero _ (X_sub_C_ne_zero f)) hq), Polynomial.roots_pow] at hz
  rcases Multiset.mem_add.mp hz with hz | hz
  · have hzf : z = f := by
      have hmem := Multiset.mem_of_mem_nsmul hz
      simpa using hmem
    simpa [hzf] using hf
  · exact lt_of_le_of_lt (hbound z hz) hu
end D5.S3.QuantumChannels.WallmanFlammiaTwoContractivity.SpectralClosure
namespace D5.S3.QuantumChannels.WallmanFlammiaTwoContractivity.TensorGram
open scoped BigOperators Kronecker Matrix.Norms.L2Operator
private theorem projection_tensor_norm_bound {n g : Type*} [Fintype n] [DecidableEq n] [Fintype g] (P : Matrix n n ℂ) (hP : IsStarProjection P) (A : g → Matrix n n ℂ) (u : ℝ) (hu : 0 ≤ u) (hleft : ∑ a, A a * (A a)ᴴ = (u : ℂ) • P) (hright : ∑ a, (A a)ᴴ * A a = (u : ℂ) • P) : ‖∑ a, A a ⊗ₖ A a‖ ≤ u := by
  classical
  have hPP : P * P = P := hP.isIdempotentElem.eq
  have hPH : Pᴴ = P := hP.isSelfAdjoint.star_eq
  have hPL : IsStarProjection (P ⊗ₖ (1 : Matrix n n ℂ)) := by
    rw [isStarProjection_iff', Matrix.star_eq_conjTranspose]
    constructor
    · rw [← Matrix.mul_kronecker_mul, hPP, Matrix.one_mul]
    · rw [Matrix.conjTranspose_kronecker, hPH, Matrix.conjTranspose_one]
  have hPR : IsStarProjection ((1 : Matrix n n ℂ) ⊗ₖ P) := by
    rw [isStarProjection_iff', Matrix.star_eq_conjTranspose]
    constructor
    · rw [← Matrix.mul_kronecker_mul, hPP, Matrix.one_mul]
    · rw [Matrix.conjTranspose_kronecker, hPH, Matrix.conjTranspose_one]
  have hr : ‖tensorRow A‖ * ‖tensorRow A‖ ≤ u := by
    calc
      _ = ‖tensorRow A * (tensorRow A)ᴴ‖ := by
        simpa only [Matrix.conjTranspose_conjTranspose, Matrix.l2_opNorm_conjTranspose] using (Matrix.l2_opNorm_conjTranspose_mul_self (tensorRow A)ᴴ).symm
      _ = u * ‖P ⊗ₖ (1 : Matrix n n ℂ)‖ := by
        rw [row_gram, hleft, Matrix.smul_kronecker, norm_smul]; simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu]
      _ ≤ u := by nlinarith [IsStarProjection.norm_le _ hPL]
  have hc : ‖tensorCol A‖ * ‖tensorCol A‖ ≤ u := by
    calc
      _ = ‖(tensorCol A)ᴴ * tensorCol A‖ := (Matrix.l2_opNorm_conjTranspose_mul_self (tensorCol A)).symm
      _ = u * ‖(1 : Matrix n n ℂ) ⊗ₖ P‖ := by
        rw [col_gram, hright, Matrix.kronecker_smul, norm_smul]; simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu]
      _ ≤ u := by nlinarith [IsStarProjection.norm_le _ hPR]
  rw [← row_col]; apply le_trans (Matrix.l2_opNorm_mul _ _); nlinarith [sq_nonneg (‖tensorRow A‖ - ‖tensorCol A‖)]
end D5.S3.QuantumChannels.WallmanFlammiaTwoContractivity.TensorGram
namespace D5.S3.QuantumChannels.WallmanFlammiaTwoContractivity.AveragedGram
open scoped BigOperators Kronecker Matrix.Norms.L2Operator
variable {n g : Type*} [Fintype n] [DecidableEq n] [Nonempty n] [Fintype g]
private def conjugateFamily (U : g → Matrix.unitaryGroup n ℂ) (A : Matrix n n ℂ) (c : ℂ) (a : g) : Matrix n n ℂ := c • ((U a).valᴴ * A * (U a).val)
private theorem family_left_gram (U : g → Matrix.unitaryGroup n ℂ) (A : Matrix n n ℂ) (c : ℂ) (a : g) : conjugateFamily U A c a * (conjugateFamily U A c a)ᴴ = (c * star c) • ((U a).valᴴ * (A * Aᴴ) * (U a).val) := by
  have hU : (U a).val * (U a).valᴴ = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using (U a).property.2
  have hmat : ((U a).valᴴ * A * (U a).val) * ((U a).valᴴ * Aᴴ * (U a).val) = (U a).valᴴ * (A * Aᴴ) * (U a).val := by
    calc
      _ = (U a).valᴴ * A * ((U a).val * (U a).valᴴ) * Aᴴ * (U a).val := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [hU]; simp only [Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]
  simpa only [conjugateFamily, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_comm, Matrix.mul_assoc] using congrArg (fun M => (c * star c) • M) hmat
private theorem family_right_gram (U : g → Matrix.unitaryGroup n ℂ) (A : Matrix n n ℂ) (c : ℂ) (a : g) : (conjugateFamily U A c a)ᴴ * conjugateFamily U A c a = (star c * c) • ((U a).valᴴ * (Aᴴ * A) * (U a).val) := by
  have hU : (U a).val * (U a).valᴴ = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using (U a).property.2
  have hmat : ((U a).valᴴ * Aᴴ * (U a).val) * ((U a).valᴴ * A * (U a).val) = (U a).valᴴ * (Aᴴ * A) * (U a).val := by
    calc
      _ = (U a).valᴴ * Aᴴ * ((U a).val * (U a).valᴴ) * A * (U a).val := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [hU]; simp only [Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]
  simpa only [conjugateFamily, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_comm, Matrix.mul_assoc] using congrArg (fun M => (star c * c) • M) hmat
end D5.S3.QuantumChannels.WallmanFlammiaTwoContractivity.AveragedGram
namespace D5.S3.QuantumChannels.WallmanFlammiaTwoContractivity.DesignTensorBound
open scoped BigOperators Kronecker Matrix.Norms.L2Operator
open D5.S3.QuantumChannels.WallmanFlammiaTwoContractivity.DesignEntries
open D5.S3.QuantumChannels.WallmanFlammiaTwoContractivity.AveragedGram
private theorem projected_tensor_bound {d : ℕ} (hd : 2 ≤ d) (G : Subgroup (Matrix.unitaryGroup (Fin d) ℂ)) [Fintype G] (hG : IsUnitaryTwoDesign G) (L : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (u : ℝ) (hu : 0 ≤ u) (hcoeff :
      let B := tracelessProjector d * L * tracelessProjector d
      (Bᴴ * B).trace / ((d : ℂ)^2 - 1) = (u : ℂ)) :
    let B := tracelessProjector d * L * tracelessProjector d
    ‖(Fintype.card G : ℂ)⁻¹ • ∑ g : G, (((g.val.val ⊗ₖ g.val.val.map star))ᴴ * B * (g.val.val ⊗ₖ g.val.val.map star)) ⊗ₖ (((g.val.val ⊗ₖ g.val.val.map star))ᴴ * B * (g.val.val ⊗ₖ g.val.val.map star))‖ ≤ u := by
  classical
  letI : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  intro B
  let R : G → Matrix.unitaryGroup (Fin d × Fin d) ℂ := fun g =>
    ⟨(g.val.val ⊗ₖ g.val.val.map star), Matrix.kronecker_mem_unitary g.val.property (Matrix.map_star_mem_unitaryGroup_iff.mpr g.val.property)⟩
  let c : ℂ := (Real.sqrt ((Fintype.card G : ℝ)⁻¹) : ℂ)
  have hsc : star c = c := by simp [c]
  have hcc : c * c = (Fintype.card G : ℂ)⁻¹ := by
    rw [← pow_two]; dsimp only [c]; rw [← Complex.ofReal_pow, Real.sq_sqrt (inv_nonneg.mpr (Nat.cast_nonneg (Fintype.card G)))]
    simp only [Complex.ofReal_inv, Complex.ofReal_natCast]
  have hgrams := projected_gram_averages hd G hG L
  have hleft : ∑ g : G, conjugateFamily R B c g * (conjugateFamily R B c g)ᴴ = (u : ℂ) • tracelessProjector d := by
    simp_rw [family_left_gram, hsc, hcc]; rw [← Finset.smul_sum]; change (Fintype.card G : ℂ)⁻¹ • (∑ g : G, ((g.val.val ⊗ₖ g.val.val.map star))ᴴ * (B * Bᴴ) * (g.val.val ⊗ₖ g.val.val.map star)) = _
    rw [hgrams.2, hcoeff]
  have hright : ∑ g : G, (conjugateFamily R B c g)ᴴ * conjugateFamily R B c g = (u : ℂ) • tracelessProjector d := by
    simp_rw [family_right_gram, hsc, hcc]; rw [← Finset.smul_sum]; change (Fintype.card G : ℂ)⁻¹ • (∑ g : G, ((g.val.val ⊗ₖ g.val.val.map star))ᴴ * (Bᴴ * B) * (g.val.val ⊗ₖ g.val.val.map star)) = _
    rw [hgrams.1, hcoeff]
  have hbound := TensorGram.projection_tensor_norm_bound (tracelessProjector d) (tracelessProjector_projection (by omega)) (conjugateFamily R B c) u hu hleft hright
  have htensor : (∑ g : G, conjugateFamily R B c g ⊗ₖ conjugateFamily R B c g) = (Fintype.card G : ℂ)⁻¹ • ∑ g : G, (((g.val.val ⊗ₖ g.val.val.map star))ᴴ * B * (g.val.val ⊗ₖ g.val.val.map star)) ⊗ₖ (((g.val.val ⊗ₖ g.val.val.map star))ᴴ * B * (g.val.val ⊗ₖ g.val.val.map star)) := by
    simp only [conjugateFamily, Matrix.smul_kronecker, Matrix.kronecker_smul, smul_smul, hcc, Finset.smul_sum]; rfl
  simpa only [htensor] using hbound
end D5.S3.QuantumChannels.WallmanFlammiaTwoContractivity.DesignTensorBound
namespace D5.S3.QuantumChannels.WallmanFlammiaTwoContractivity.CanonicalSector
open scoped BigOperators Kronecker Matrix.Norms.L2Operator ComplexOrder
open D5.S3.Quantum.Recovery.LiJiangPolarPairOptimalityRefutation (matrixAction)
open D5.S3.QuantumChannels.WallmanFlammiaTwoContractivity.DesignEntries
open D5.S3.QuantumChannels.WallmanFlammiaTwoContractivity.TransferGeometry
private theorem canonical_coefficient {d : ℕ} (hd : 2 ≤ d) (Λ : QuantumChannel (Fin d) (Fin d)) :
    let B := tracelessProjector d * LinearMap.toMatrix (Matrix.stdBasis ℂ (Fin d) (Fin d)) (Matrix.stdBasis ℂ (Fin d) (Fin d)) (matrixAction Λ.toCompletelyPositiveMap) *
      tracelessProjector d
    (Bᴴ * B).trace / ((d : ℂ)^2 - 1) = (ChannelPurity.unitarityValue Λ : ℂ) := by
  intro B
  have hp := (Matrix.posSemidef_conjTranspose_mul_self B).trace_nonneg
  have hreal : (Bᴴ * B).trace = ((Bᴴ * B).trace.re : ℂ) := Complex.eq_re_of_ofReal_le hp
  rw [hreal]
  have hden : (d : ℂ)^2 - 1 = (((d : ℝ)^2 - 1 : ℝ) : ℂ) := by push_cast; rfl
  rw [hden, ← Complex.ofReal_div]; congr 1; dsimp only [ChannelPurity.unitarityValue]; rw [canonical_projected_mass (by omega) Λ]
private theorem canonical_one_copy_strict {d : ℕ} (hd : 2 ≤ d) (Λ : QuantumChannel (Fin d) (Fin d)) (hnot : ¬ ∃ U : Matrix.unitaryGroup (Fin d) ℂ, ∀ X : Matrix (Fin d) (Fin d) ℂ, CStarMatrix.ofMatrix.symm (Λ.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) = U.val * X * U.val.conjTranspose) :
    let B := tracelessProjector d * LinearMap.toMatrix (Matrix.stdBasis ℂ (Fin d) (Fin d)) (Matrix.stdBasis ℂ (Fin d) (Fin d)) (matrixAction Λ.toCompletelyPositiveMap) *
      tracelessProjector d
    ‖B.trace / (((d : ℝ)^2 - 1 : ℝ) : ℂ)‖ < 1 := by
  intro B
  have hP := tracelessProjector_projection (show 0 < d by omega)
  apply ProjectionMass.strict_projected_one_copy_bound (tracelessProjector d) B hP
  · dsimp only [B]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hP.isIdempotentElem.eq]
  · have h : 2 ≤ (d : ℝ) := by exact_mod_cast hd
    nlinarith
  · exact ChannelPurity.strict_unitarity_value hd Λ hnot
  · rw [tracelessProjector_trace (by omega)]
    simp [pow_two, Complex.mul_re]
  · exact canonical_unitarity_mass hd Λ
private theorem canonical_tensor_strict {d : ℕ} (hd : 2 ≤ d) (Λ : QuantumChannel (Fin d) (Fin d)) (G : Subgroup (Matrix.unitaryGroup (Fin d) ℂ)) [Fintype G] (hG : IsUnitaryTwoDesign G) (hnot : ¬ ∃ U : Matrix.unitaryGroup (Fin d) ℂ, ∀ X : Matrix (Fin d) (Fin d) ℂ, CStarMatrix.ofMatrix.symm (Λ.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) = U.val * X * U.val.conjTranspose) :
    let B := tracelessProjector d * LinearMap.toMatrix (Matrix.stdBasis ℂ (Fin d) (Fin d)) (Matrix.stdBasis ℂ (Fin d) (Fin d)) (matrixAction Λ.toCompletelyPositiveMap) *
      tracelessProjector d
    ‖(Fintype.card G : ℂ)⁻¹ • ∑ g : G, (((g.val.val ⊗ₖ g.val.val.map star))ᴴ * B * (g.val.val ⊗ₖ g.val.val.map star)) ⊗ₖ (((g.val.val ⊗ₖ g.val.val.map star))ᴴ * B * (g.val.val ⊗ₖ g.val.val.map star))‖ < 1 := by
  intro B
  exact lt_of_le_of_lt (DesignTensorBound.projected_tensor_bound hd G hG (LinearMap.toMatrix (Matrix.stdBasis ℂ (Fin d) (Fin d)) (Matrix.stdBasis ℂ (Fin d) (Fin d)) (matrixAction Λ.toCompletelyPositiveMap)) (ChannelPurity.unitarityValue Λ) (canonical_unitarity_nonneg hd Λ) (canonical_coefficient hd Λ)) (ChannelPurity.strict_unitarity_value hd Λ hnot)
end D5.S3.QuantumChannels.WallmanFlammiaTwoContractivity.CanonicalSector
open Matrix Polynomial
open scoped BigOperators Kronecker
namespace D5.S3.QuantumChannels.WallmanFlammiaTwoContractivity.TensorBlocks
private def tensorSplit (n : Type*) : ((Unit ⊕ n) × (Unit ⊕ n)) ≃ ((Unit × Unit) ⊕ ((Unit × n) ⊕ ((n × Unit) ⊕ (n × n)))) := ((Equiv.sumProdDistrib Unit n (Unit ⊕ n)).trans (Equiv.sumCongr (Equiv.prodSumDistrib Unit Unit n) (Equiv.prodSumDistrib n Unit n))).trans (Equiv.sumAssoc (Unit × Unit) (Unit × n) ((n × Unit) ⊕ (n × n)))
private def lowerLift {n : Type*} [DecidableEq n] (a : n → ℂ) (A : Matrix n n ℂ) : Matrix (Unit ⊕ n) (Unit ⊕ n) ℂ := Matrix.fromBlocks 1 0 (fun r _ => a r) A
private theorem charpoly_lower (α β : Type*) [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (M : Matrix (α ⊕ β) (α ⊕ β) ℂ) (hzero : M.toBlocks₁₂ = 0) : M.charpoly = M.toBlocks₁₁.charpoly * M.toBlocks₂₂.charpoly := by
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks M, hzero]
  exact Matrix.charpoly_fromBlocks_zero₁₂ (M₁₁ := M.toBlocks₁₁) (M₂₁ := M.toBlocks₂₁) (M₂₂ := M.toBlocks₂₂)
private theorem scalar_charpoly {κ : Type*} [Fintype κ] [DecidableEq κ] (f : ℂ) : (f • (1 : Matrix κ κ ℂ)).charpoly = (X - C f) ^ Fintype.card κ := by
  rw [show f • (1 : Matrix κ κ ℂ) = Matrix.diagonal (fun _ => f) by
    ext i j; simp [Matrix.one_apply, Matrix.diagonal_apply, mul_ite]]
  simp [Matrix.charpoly_diagonal]
private theorem averaged_lower_tensor_charpoly {n g : Type*} [Fintype n] [DecidableEq n] [Fintype g] (a : g → n → ℂ) (A : g → Matrix n n ℂ) (t f : ℂ) (ht : t * (Fintype.card g : ℂ) = 1) (hmean : t • (∑ x : g, A x) = f • (1 : Matrix n n ℂ)) : (t • (∑ x : g, lowerLift (a x) (A x) ⊗ₖ lowerLift (a x) (A x))).charpoly = (X - C 1) * ((X - C f) ^ (2 * Fintype.card n) * (t • (∑ x : g, A x ⊗ₖ A x)).charpoly) := by
  classical
  let Q := t • (∑ x : g, lowerLift (a x) (A x) ⊗ₖ lowerLift (a x) (A x))
  let R := Matrix.reindex (tensorSplit n) (tensorSplit n) Q
  let S := R.toBlocks₂₂
  let T := S.toBlocks₂₂
  have h00 : R.toBlocks₁₁ = (1 : Matrix (Unit × Unit) (Unit × Unit) ℂ) := by
    ext ⟨u,v⟩ ⟨w,z⟩
    cases u; cases v; cases w; cases z
    simpa [R, Q, Matrix.reindex, Matrix.submatrix, tensorSplit, Matrix.toBlocks₁₁, Matrix.smul_apply, Matrix.sum_apply, Matrix.kronecker, Matrix.kroneckerMap_apply, lowerLift, Matrix.fromBlocks, smul_eq_mul] using ht
  have h01 : R.toBlocks₁₂ = 0 := by
    ext ⟨u,v⟩ c
    rcases c with c | c
    · rcases c with ⟨w,z⟩
      simp [R, Q, Matrix.reindex, Matrix.submatrix, tensorSplit, Matrix.toBlocks₁₂, Matrix.kronecker, Matrix.kroneckerMap_apply, lowerLift, Matrix.fromBlocks, Matrix.sum_apply]
    · rcases c with c | c <;> rcases c with ⟨w,z⟩ <;>
      simp [R, Q, Matrix.reindex, Matrix.submatrix, tensorSplit, Matrix.toBlocks₁₂, Matrix.kronecker, Matrix.kroneckerMap_apply, lowerLift, Matrix.fromBlocks, Matrix.sum_apply]
  have h11 : S.toBlocks₁₁ = f • (1 : Matrix (Unit × n) (Unit × n) ℂ) := by
    ext ⟨u,r⟩ ⟨v,c⟩
    cases u; cases v
    simpa [S, R, Q, Matrix.reindex, Matrix.submatrix, tensorSplit, Matrix.toBlocks₁₁, Matrix.toBlocks₂₂, Matrix.kronecker, Matrix.kroneckerMap_apply, lowerLift, Matrix.fromBlocks, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, Matrix.one_apply] using congrFun (congrFun hmean r) c
  have h12 : S.toBlocks₁₂ = 0 := by
    ext ⟨u,r⟩ c
    rcases c with c | c <;> rcases c with ⟨v,s⟩ <;>
      simp [S, R, Q, Matrix.reindex, Matrix.submatrix, tensorSplit, Matrix.toBlocks₁₂, Matrix.toBlocks₂₂, Matrix.kronecker, Matrix.kroneckerMap_apply, lowerLift, Matrix.fromBlocks, Matrix.sum_apply]
  have h22 : T.toBlocks₁₁ = f • (1 : Matrix (n × Unit) (n × Unit) ℂ) := by
    ext ⟨r,u⟩ ⟨c,v⟩
    cases u; cases v
    simpa [T, S, R, Q, Matrix.reindex, Matrix.submatrix, tensorSplit, Matrix.toBlocks₁₁, Matrix.toBlocks₂₂, Matrix.kronecker, Matrix.kroneckerMap_apply, lowerLift, Matrix.fromBlocks, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, Matrix.one_apply] using congrFun (congrFun hmean r) c
  have h23 : T.toBlocks₁₂ = 0 := by
    ext ⟨r,u⟩ ⟨v,s⟩
    simp [T, S, R, Q, Matrix.reindex, Matrix.submatrix, tensorSplit, Matrix.toBlocks₁₂, Matrix.toBlocks₂₂, Matrix.kronecker, Matrix.kroneckerMap_apply, lowerLift, Matrix.fromBlocks, Matrix.sum_apply]
  have h33 : T.toBlocks₂₂ = t • (∑ x : g, A x ⊗ₖ A x) := by
    ext ⟨r,s⟩ ⟨v,w⟩
    simp [T, S, R, Q, Matrix.reindex, Matrix.submatrix, tensorSplit, Matrix.toBlocks₂₂, Matrix.kronecker, Matrix.kroneckerMap_apply, lowerLift, Matrix.fromBlocks, Matrix.sum_apply]
  have hchar : Q.charpoly = R.charpoly := (Matrix.charpoly_reindex _ Q).symm
  rw [hchar, charpoly_lower _ _ R h01]; change R.toBlocks₁₁.charpoly * S.charpoly = _; rw [charpoly_lower _ _ S h12]
  change R.toBlocks₁₁.charpoly * (S.toBlocks₁₁.charpoly * T.charpoly) = _; rw [charpoly_lower _ _ T h23, h00, h11, h22, h33]
  rw [scalar_charpoly (κ := Unit × n) f, scalar_charpoly (κ := n × Unit) f, Matrix.charpoly_one]
  simp only [Fintype.card_prod, Fintype.card_unit, mul_one, one_mul, pow_one, C_1, mul_assoc]; rw [two_mul, pow_add]; ring
end D5.S3.QuantumChannels.WallmanFlammiaTwoContractivity.TensorBlocks
namespace D5.S3.QuantumChannels.WallmanFlammiaTwoContractivity.CompressionSpectral
open Matrix Polynomial
private theorem compression_charpoly_identity {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m] (V : Matrix n m ℂ) (W : Matrix m n ℂ) (hWV : W * V = 1) (A : Matrix m m ℂ) : X ^ Fintype.card m * (V * A * W).charpoly = X ^ Fintype.card n * A.charpoly := by
  have h := Matrix.charpoly_mul_comm' V (A * W)
  have ha : (A * W) * V = A := by
    rw [Matrix.mul_assoc, hWV, Matrix.mul_one]
  simpa only [ha, Matrix.mul_assoc] using h
private theorem compression_root_bound {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m] (V : Matrix n m ℂ) (W : Matrix m n ℂ) (hWV : W * V = 1) (A : Matrix m m ℂ) (u : ℝ) (hu : 0 ≤ u) (hbound : ∀ z ∈ (V * A * W).charpoly.roots, ‖z‖ ≤ u) (z : ℂ) (hz : z ∈ A.charpoly.roots) : ‖z‖ ≤ u := by
  by_cases hz0 : z = 0
  · simpa only [hz0, norm_zero] using hu
  · apply hbound z
    rw [Polynomial.mem_roots (Matrix.charpoly_monic _).ne_zero]
    have he := congrArg (Polynomial.eval z) (compression_charpoly_identity V W hWV A)
    have hzA : A.charpoly.eval z = 0 := (Polynomial.mem_roots (Matrix.charpoly_monic A).ne_zero).mp hz
    simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, hzA, mul_zero] at he; exact (mul_eq_zero.mp he).resolve_left (pow_ne_zero _ hz0)
end D5.S3.QuantumChannels.WallmanFlammiaTwoContractivity.CompressionSpectral
namespace D5.S3.QuantumChannels.WallmanFlammiaTwoContractivity.TraceCoordinates
private def assemble (d : ℕ) (hd : 0 < d) : (ℂ × ((Matrix.traceLinearMap (Fin d) ℂ ℂ).ker)) ≃ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ := by
  classical
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_zero_of_lt hd
  have hzero (X : Matrix (Fin d) (Fin d) ℂ) : X - (X.trace / (d : ℂ)) • 1 ∈ ((Matrix.traceLinearMap (Fin d) ℂ ℂ).ker) := by
    change (X - (X.trace / (d : ℂ)) • 1).trace = 0; simp [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, hd0]
  refine {
    toFun := fun p => (p.1 / (d : ℂ)) • 1 + p.2.val
    invFun := fun X => (X.trace, ⟨X - (X.trace / (d : ℂ)) • 1, hzero X⟩)
    map_add' := ?_
    map_smul' := ?_
    left_inv := ?_
    right_inv := ?_
  }
  · intro p q
    simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, add_div, add_smul]
    abel
  · intro z p
    change (z * p.1 / (d : ℂ)) • 1 + z • p.2.val = z • ((p.1 / (d : ℂ)) • 1 + p.2.val); rw [smul_add, smul_smul]; congr 1; ring
  · intro p
    have hp : p.2.val.trace = 0 := p.2.property
    have ht : ((p.1 / (d : ℂ)) • (1 : Matrix (Fin d) (Fin d) ℂ) + p.2.val).trace = p.1 := by
      simp [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one, hp, hd0]
    apply Prod.ext
    · exact ht
    · apply Subtype.ext
      change ((p.1 / (d : ℂ)) • 1 + p.2.val) - (((p.1 / (d : ℂ)) • 1 + p.2.val).trace / (d : ℂ)) • 1 = p.2.val; rw [ht]
      abel
  · intro X
    change (X.trace / (d : ℂ)) • 1 + (X - (X.trace / (d : ℂ)) • 1) = X
    abel
private def adaptedBasis {d : ℕ} (hd : 0 < d) {κ : Type*} (b : Module.Basis κ ℂ (((Matrix.traceLinearMap (Fin d) ℂ ℂ).ker))) : Module.Basis (Unit ⊕ κ) ℂ (Matrix (Fin d) (Fin d) ℂ) := ((Module.Basis.singleton Unit ℂ).prod b).map (assemble d hd)
private theorem adaptedBasis_first_coefficient {d : ℕ} (hd : 0 < d) {κ : Type*}
    (b : Module.Basis κ ℂ (((Matrix.traceLinearMap (Fin d) ℂ ℂ).ker)))
    (X : Matrix (Fin d) (Fin d) ℂ) (i : Unit) :
    (adaptedBasis hd b).repr X (.inl i) = X.trace := by
  simp [adaptedBasis, Module.Basis.map_repr, assemble]
private theorem trace_preserving_first_row {d : ℕ} (hd : 0 < d) {κ : Type*} [Fintype κ] [DecidableEq κ] (b : Module.Basis κ ℂ (((Matrix.traceLinearMap (Fin d) ℂ ℂ).ker))) (F : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ) (hTP : ∀ X, (F X).trace = X.trace) (i : Unit) (j : Unit ⊕ κ) : LinearMap.toMatrix (adaptedBasis hd b) (adaptedBasis hd b) F (.inl i) j = if j = .inl i then 1 else 0 := by
  classical
  rw [LinearMap.toMatrix_apply, adaptedBasis_first_coefficient, hTP]
  have hc := (adaptedBasis hd b).repr_self j
  have h := congrArg (fun v => v (.inl i)) hc
  rw [adaptedBasis_first_coefficient] at h
  simpa only [Finsupp.single_apply, eq_comm] using h
end D5.S3.QuantumChannels.WallmanFlammiaTwoContractivity.TraceCoordinates
namespace D5.S3.QuantumChannels.WallmanFlammiaTwoContractivity.TensorCoordinates
open scoped BigOperators Kronecker
private theorem tensor_mean_matrix {M ι g : Type*} [AddCommGroup M] [Module ℂ M] [Fintype ι] [DecidableEq ι] [Fintype g] (b : Module.Basis ι ℂ M) (F : g → M →ₗ[ℂ] M) (t : ℂ) : LinearMap.toMatrix (b.tensorProduct b) (b.tensorProduct b) (t • ∑ a : g, TensorProduct.map (F a) (F a)) = t • ∑ a : g, LinearMap.toMatrix b b (F a) ⊗ₖ LinearMap.toMatrix b b (F a) := by
  simp only [map_smul, map_sum, TensorProduct.toMatrix_map]
private theorem tensor_average_charpoly_basis {M ι κ g : Type*} [AddCommGroup M] [Module ℂ M] [Module.Finite ℂ M] [Module.Free ℂ M] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype g] (b : Module.Basis ι ℂ M) (c : Module.Basis κ ℂ M) (F : g → M →ₗ[ℂ] M) (t : ℂ) : (t • ∑ a : g, LinearMap.toMatrix b b (F a) ⊗ₖ LinearMap.toMatrix b b (F a)).charpoly = (t • ∑ a : g, LinearMap.toMatrix c c (F a) ⊗ₖ LinearMap.toMatrix c c (F a)).charpoly := by
  letI : Module.Finite ℂ (TensorProduct ℂ M M) := Module.Finite.of_basis (b.tensorProduct b)
  let T := t • ∑ a : g, TensorProduct.map (F a) (F a)
  calc
    _ = (LinearMap.toMatrix (b.tensorProduct b) (b.tensorProduct b) T).charpoly := congrArg Matrix.charpoly (tensor_mean_matrix b F t).symm
    _ = T.charpoly := LinearMap.charpoly_toMatrix T (b.tensorProduct b)
    _ = (LinearMap.toMatrix (c.tensorProduct c) (c.tensorProduct c) T).charpoly := (LinearMap.charpoly_toMatrix T (c.tensorProduct c)).symm
    _ = _ := congrArg Matrix.charpoly (tensor_mean_matrix c F t)
end D5.S3.QuantumChannels.WallmanFlammiaTwoContractivity.TensorCoordinates
namespace D5.S3.QuantumChannels.WallmanFlammiaTwoContractivity.TraceCoordinates
open Matrix Polynomial
open scoped BigOperators Kronecker
private theorem adapted_matrix_lower {d : ℕ} (hd : 0 < d) {κ : Type*} [Fintype κ] [DecidableEq κ] (b : Module.Basis κ ℂ (((Matrix.traceLinearMap (Fin d) ℂ ℂ).ker))) (F : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ) (hTP : ∀ X, (F X).trace = X.trace) :
    let M := LinearMap.toMatrix (adaptedBasis hd b) (adaptedBasis hd b) F
    M = TensorBlocks.lowerLift (fun i => M (.inr i) (.inl ())) (fun i j => M (.inr i) (.inr j)) := by
  intro M; ext i j
  rcases i with i | i
  · rcases j with j | j
    · cases i; cases j
      simpa [TensorBlocks.lowerLift, Matrix.fromBlocks] using trace_preserving_first_row hd b F hTP () (.inl ())
    · cases i
      simpa [TensorBlocks.lowerLift, Matrix.fromBlocks] using trace_preserving_first_row hd b F hTP () (.inr j)
  · rcases j with j | j
    · cases j
      rfl
    · rfl
private theorem adapted_tensor_charpoly {d : ℕ} (hd : 0 < d) {κ g : Type*}
    [Fintype κ] [DecidableEq κ] [Fintype g]
    (b : Module.Basis κ ℂ (((Matrix.traceLinearMap (Fin d) ℂ ℂ).ker)))
    (F : g → Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (hTP : ∀ x X, (F x X).trace = X.trace)
    (t f : ℂ) (ht : t * (Fintype.card g : ℂ) = 1)
    (hmean : t • ∑ x : g, (fun i j : κ => LinearMap.toMatrix (adaptedBasis hd b) (adaptedBasis hd b) (F x) (.inr i) (.inr j)) = f • (1 : Matrix κ κ ℂ)) :
    (t • ∑ x : g, LinearMap.toMatrix (adaptedBasis hd b) (adaptedBasis hd b) (F x) ⊗ₖ LinearMap.toMatrix (adaptedBasis hd b) (adaptedBasis hd b) (F x)).charpoly = (X - C 1) * ((X - C f) ^ (2 * Fintype.card κ) * (t • ∑ x : g, (fun i j : κ => LinearMap.toMatrix (adaptedBasis hd b) (adaptedBasis hd b) (F x) (.inr i) (.inr j)) ⊗ₖ (fun i j : κ => LinearMap.toMatrix (adaptedBasis hd b) (adaptedBasis hd b) (F x) (.inr i) (.inr j))).charpoly) := by
  let M := fun x => LinearMap.toMatrix (adaptedBasis hd b) (adaptedBasis hd b) (F x)
  let a := fun x i => M x (.inr i) (.inl ())
  let A := fun x i j => M x (.inr i) (.inr j)
  have hM (x : g) : M x = TensorBlocks.lowerLift (a x) (A x) := adapted_matrix_lower hd b (F x) (hTP x)
  change (t • ∑ x : g, M x ⊗ₖ M x).charpoly = (X - C 1) * ((X - C f) ^ (2 * Fintype.card κ) * (t • ∑ x : g, A x ⊗ₖ A x).charpoly); simp_rw [hM]
  exact TensorBlocks.averaged_lower_tensor_charpoly a A t f ht hmean
end D5.S3.QuantumChannels.WallmanFlammiaTwoContractivity.TraceCoordinates
open D5.S3.Quantum.Foundation.FiniteStateChannel (QuantumChannel)
namespace D5.S3.QuantumChannels.WallmanFlammiaTwoContractivity.TraceInterface
open scoped BigOperators Kronecker
open D5.S3.QuantumChannels.WallmanFlammiaTwoContractivity.TraceCoordinates
open D5.S3.QuantumChannels.WallmanFlammiaTwoContractivity.DesignEntries
open D5.S3.QuantumChannels.WallmanFlammiaTwoContractivity.TransferGeometry
private def project {d : ℕ} (hd : 0 < d) : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] ((Matrix.traceLinearMap (Fin d) ℂ ℂ).ker) := (LinearMap.snd ℂ ℂ (((Matrix.traceLinearMap (Fin d) ℂ ℂ).ker))).comp (assemble d hd).symm.toLinearMap
private theorem project_inclusion {d : ℕ} (hd : 0 < d) : (project hd).comp (((Matrix.traceLinearMap (Fin d) ℂ ℂ).ker)).subtype = LinearMap.id := by
  apply LinearMap.ext; intro X; apply Subtype.ext
  have hx : X.val.trace = 0 := X.property
  simp [project, assemble, hx]
private theorem projection_matrix {d : ℕ} (hd : 0 < d) : LinearMap.toMatrix (Matrix.stdBasis ℂ (Fin d) (Fin d)) (Matrix.stdBasis ℂ (Fin d) (Fin d)) ((((Matrix.traceLinearMap (Fin d) ℂ ℂ).ker)).subtype.comp (project hd)) = tracelessProjector d := by
  classical
  ext r c; rw [LinearMap.toMatrix_apply, std_repr, Matrix.stdBasis_eq_single]; simp only [LinearMap.comp_apply, Submodule.subtype_apply, project, LinearMap.snd_apply]
  change ((Matrix.single c.1 c.2 (1 : ℂ) - ((Matrix.single c.1 c.2 (1 : ℂ)).trace / (d : ℂ)) • (1 : Matrix (Fin d) (Fin d) ℂ)) : Matrix (Fin d) (Fin d) ℂ) r.1 r.2 = _
  have ht : (Matrix.single c.1 c.2 (1 : ℂ)).trace = (Matrix.vec (1 : Matrix (Fin d) (Fin d) ℂ)) c := by
    by_cases h : c.1 = c.2
    · simp [h, Matrix.vec, Matrix.one_apply, eq_comm]
    · simp [Matrix.trace_single_eq_of_ne c.1 c.2 1 h, Matrix.vec, Matrix.one_apply, eq_comm, h]
  rw [ht]
  by_cases hc : c.1 = c.2 <;> by_cases hr : r.1 = r.2 <;>
    simp [tracelessProjector, scalarProjector_eq, Matrix.vec, Matrix.one_apply, eq_comm, hc, hr, Matrix.sub_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, Matrix.one_apply, Matrix.single_apply, div_eq_mul_inv, Prod.ext_iff, eq_comm]
private theorem projection_inclusion_matrix {d : ℕ} (hd : 0 < d) {κ : Type*} [Fintype κ] [DecidableEq κ] (b : Module.Basis κ ℂ (((Matrix.traceLinearMap (Fin d) ℂ ℂ).ker))) : (LinearMap.toMatrix (Matrix.stdBasis ℂ (Fin d) (Fin d)) b (project hd)) * (LinearMap.toMatrix b (Matrix.stdBasis ℂ (Fin d) (Fin d)) ((Matrix.traceLinearMap (Fin d) ℂ ℂ).ker).subtype) = 1 := by
  rw [← LinearMap.toMatrix_comp, project_inclusion, LinearMap.toMatrix_id]
private theorem inclusion_projection_matrix {d : ℕ} (hd : 0 < d) {κ : Type*} [Fintype κ] [DecidableEq κ] (b : Module.Basis κ ℂ (((Matrix.traceLinearMap (Fin d) ℂ ℂ).ker))) : (LinearMap.toMatrix b (Matrix.stdBasis ℂ (Fin d) (Fin d)) ((Matrix.traceLinearMap (Fin d) ℂ ℂ).ker).subtype) * (LinearMap.toMatrix (Matrix.stdBasis ℂ (Fin d) (Fin d)) b (project hd)) = tracelessProjector d := by
  rw [← LinearMap.toMatrix_comp, projection_matrix]
private def smallMatrix {d : ℕ} (hd : 0 < d) {κ : Type*} [Fintype κ] [DecidableEq κ] (b : Module.Basis κ ℂ (((Matrix.traceLinearMap (Fin d) ℂ ℂ).ker))) (F : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ) : Matrix κ κ ℂ := LinearMap.toMatrix b b ((project hd).comp (F.comp (((Matrix.traceLinearMap (Fin d) ℂ ℂ).ker)).subtype))
private theorem smallMatrix_compression {d : ℕ} (hd : 0 < d) {κ : Type*} [Fintype κ] [DecidableEq κ] (b : Module.Basis κ ℂ (((Matrix.traceLinearMap (Fin d) ℂ ℂ).ker))) (F : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ) : smallMatrix hd b F = (LinearMap.toMatrix (Matrix.stdBasis ℂ (Fin d) (Fin d)) b (project hd)) * LinearMap.toMatrix (Matrix.stdBasis ℂ (Fin d) (Fin d)) (Matrix.stdBasis ℂ (Fin d) (Fin d)) F * (LinearMap.toMatrix b (Matrix.stdBasis ℂ (Fin d) (Fin d)) ((Matrix.traceLinearMap (Fin d) ℂ ℂ).ker).subtype) := by
  rw [smallMatrix, LinearMap.toMatrix_comp b (Matrix.stdBasis ℂ (Fin d) (Fin d)) b, LinearMap.toMatrix_comp b (Matrix.stdBasis ℂ (Fin d) (Fin d)) (Matrix.stdBasis ℂ (Fin d) (Fin d))]
  simp only [Matrix.mul_assoc]
private theorem smallMatrix_adapted {d : ℕ} (hd : 0 < d) {κ : Type*} [Fintype κ] [DecidableEq κ] (b : Module.Basis κ ℂ (((Matrix.traceLinearMap (Fin d) ℂ ℂ).ker))) (F : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ) : smallMatrix hd b F = fun i j =>
      LinearMap.toMatrix (adaptedBasis hd b) (adaptedBasis hd b) F (.inr i) (.inr j) := by
  ext i j
  simp [smallMatrix, LinearMap.toMatrix_apply, adaptedBasis, project, Module.Basis.map_apply, Module.Basis.map_repr, Module.Basis.prod_repr_inr, Module.Basis.prod_apply, assemble]
private theorem smallMatrix_lift {d : ℕ} (hd : 0 < d) {κ : Type*} [Fintype κ] [DecidableEq κ] (b : Module.Basis κ ℂ (((Matrix.traceLinearMap (Fin d) ℂ ℂ).ker))) (F : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ) : (LinearMap.toMatrix b (Matrix.stdBasis ℂ (Fin d) (Fin d)) ((Matrix.traceLinearMap (Fin d) ℂ ℂ).ker).subtype) * smallMatrix hd b F * (LinearMap.toMatrix (Matrix.stdBasis ℂ (Fin d) (Fin d)) b (project hd)) = tracelessProjector d * LinearMap.toMatrix (Matrix.stdBasis ℂ (Fin d) (Fin d)) (Matrix.stdBasis ℂ (Fin d) (Fin d)) F * tracelessProjector d := by
  rw [smallMatrix_compression]; simp only [← Matrix.mul_assoc, inclusion_projection_matrix]; simp only [Matrix.mul_assoc, inclusion_projection_matrix]
end D5.S3.QuantumChannels.WallmanFlammiaTwoContractivity.TraceInterface
namespace D5.S3.QuantumChannels.WallmanFlammiaTwoContractivity.ConjugationInterface
open scoped BigOperators Kronecker
open D5.S3.QuantumChannels.WallmanFlammiaTwoContractivity.DesignEntries
open D5.S3.QuantumChannels.WallmanFlammiaTwoContractivity.TransferGeometry
open D5.S3.Quantum.Recovery.LiJiangPolarPairOptimalityRefutation (matrixAction)
private theorem conjugationMap_trace {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℂ) (X : Matrix (Fin d) (Fin d) ℂ) : ((Unitary.conjStarAlgAut ℂ (Matrix (Fin d) (Fin d) ℂ) U).toAlgEquiv.toLinearMap X).trace = X.trace := by
  have hU : U.valᴴ * U.val = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using U.property.1
  change (U.val * X * U.valᴴ).trace = X.trace; rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hU, Matrix.one_mul]
private theorem conjugationMap_one {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℂ) : (Unitary.conjStarAlgAut ℂ (Matrix (Fin d) (Fin d) ℂ) U).toAlgEquiv.toLinearMap 1 = 1 := by
  exact (Unitary.conjStarAlgAut ℂ (Matrix (Fin d) (Fin d) ℂ) U).map_one
private theorem transfer_conjugation {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℂ) : LinearMap.toMatrix (Matrix.stdBasis ℂ (Fin d) (Fin d)) (Matrix.stdBasis ℂ (Fin d) (Fin d)) ((Unitary.conjStarAlgAut ℂ (Matrix (Fin d) (Fin d) ℂ) U).toAlgEquiv.toLinearMap) = (U.val ⊗ₖ U.val.map star) := by
  classical
  ext r c; rw [transfer_entry]; change (U.val * Matrix.single c.1 c.2 (1 : ℂ) * U.valᴴ) r.1 r.2 = _
  simp [Matrix.single_eq_single_vecMulVec_single, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMulVec_apply, Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply, Matrix.map_apply]
private theorem conjugationRep_star {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℂ) : ((star U).val ⊗ₖ (star U).val.map star) = ((U.val ⊗ₖ U.val.map star))ᴴ := by
  change U.valᴴ ⊗ₖ U.valᴴ.map star = (U.val ⊗ₖ U.val.map star)ᴴ
  rw [Matrix.conjTranspose_kronecker]
  congr 1
private theorem scalar_rep_right {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℂ) : (U.val ⊗ₖ U.val.map star) * D5.S3.QuantumBounds.PeritoTsirelson.maxEntangled (Fin d) = D5.S3.QuantumBounds.PeritoTsirelson.maxEntangled (Fin d) := by
  have hv : (U.val ⊗ₖ U.val.map star) *ᵥ (Matrix.vec (1 : Matrix (Fin d) (Fin d) ℂ)) = (Matrix.vec (1 : Matrix (Fin d) (Fin d) ℂ)) := by
    ext r
    have h := conjugationRep_action U 1 r
    have hU : U.val * (1 : Matrix (Fin d) (Fin d) ℂ) * U.valᴴ = 1 := conjugationMap_one U
    rw [hU] at h
    simpa only [Matrix.mulVec, dotProduct, Matrix.vec, Matrix.one_apply, eq_comm] using h
  rw [scalarProjector_eq, Matrix.mul_smul, Matrix.mul_vecMulVec, hv]
private theorem scalar_rep_left {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℂ) : D5.S3.QuantumBounds.PeritoTsirelson.maxEntangled (Fin d) * (U.val ⊗ₖ U.val.map star) = D5.S3.QuantumBounds.PeritoTsirelson.maxEntangled (Fin d) := by
  have h := scalar_rep_right (star U)
  have hSH : (D5.S3.QuantumBounds.PeritoTsirelson.maxEntangled (Fin d))ᴴ = D5.S3.QuantumBounds.PeritoTsirelson.maxEntangled (Fin d) := by
    simpa only [scalarProjector_eq_Q] using D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability.Q_hermitian d
  rw [conjugationRep_star] at h
  have hh := congrArg Matrix.conjTranspose h
  simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hSH] using hh
private theorem projector_rep_commute {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℂ) : tracelessProjector d * (U.val ⊗ₖ U.val.map star) = (U.val ⊗ₖ U.val.map star) * tracelessProjector d := by
  simp only [tracelessProjector, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, scalar_rep_left, scalar_rep_right]
private def inverseConjugatedMap {d : ℕ}
    (Λ : QuantumChannel (Fin d) (Fin d)) (U : Matrix.unitaryGroup (Fin d) ℂ) :
    Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ :=
  ((Unitary.conjStarAlgAut ℂ (Matrix (Fin d) (Fin d) ℂ) (star U)).toAlgEquiv.toLinearMap).comp ((matrixAction Λ.toCompletelyPositiveMap).comp ((Unitary.conjStarAlgAut ℂ (Matrix (Fin d) (Fin d) ℂ) U).toAlgEquiv.toLinearMap))
private theorem inverseConjugatedMap_trace {d : ℕ}
    (Λ : QuantumChannel (Fin d) (Fin d)) (U : Matrix.unitaryGroup (Fin d) ℂ)
    (X : Matrix (Fin d) (Fin d) ℂ) :
    (inverseConjugatedMap Λ U X).trace = X.trace := by
  dsimp only [inverseConjugatedMap, LinearMap.comp_apply]; rw [conjugationMap_trace]
  change (CStarMatrix.ofMatrix.symm (Λ.toCompletelyPositiveMap (CStarMatrix.ofMatrix ((Unitary.conjStarAlgAut ℂ (Matrix (Fin d) (Fin d) ℂ) U).toAlgEquiv.toLinearMap X)))).trace = _
  exact (Λ.trace_preserving (CStarMatrix.ofMatrix ((Unitary.conjStarAlgAut ℂ (Matrix (Fin d) (Fin d) ℂ) U).toAlgEquiv.toLinearMap X))).trans (conjugationMap_trace U X)
private theorem inverseConjugatedMap_transfer {d : ℕ}
    (Λ : QuantumChannel (Fin d) (Fin d)) (U : Matrix.unitaryGroup (Fin d) ℂ) :
    LinearMap.toMatrix (Matrix.stdBasis ℂ (Fin d) (Fin d)) (Matrix.stdBasis ℂ (Fin d) (Fin d)) (inverseConjugatedMap Λ U) = ((U.val ⊗ₖ U.val.map star))ᴴ * LinearMap.toMatrix (Matrix.stdBasis ℂ (Fin d) (Fin d)) (Matrix.stdBasis ℂ (Fin d) (Fin d)) (matrixAction Λ.toCompletelyPositiveMap) * (U.val ⊗ₖ U.val.map star) := by
  dsimp only [inverseConjugatedMap]
  rw [LinearMap.toMatrix_comp (Matrix.stdBasis ℂ (Fin d) (Fin d)) (Matrix.stdBasis ℂ (Fin d) (Fin d)) (Matrix.stdBasis ℂ (Fin d) (Fin d)), LinearMap.toMatrix_comp (Matrix.stdBasis ℂ (Fin d) (Fin d)) (Matrix.stdBasis ℂ (Fin d) (Fin d)) (Matrix.stdBasis ℂ (Fin d) (Fin d))]
  simp only [transfer_conjugation, conjugationRep_star, Matrix.mul_assoc]
private theorem inverseConjugatedMap_compression {d : ℕ}
    (Λ : QuantumChannel (Fin d) (Fin d)) (U : Matrix.unitaryGroup (Fin d) ℂ) :
    tracelessProjector d * LinearMap.toMatrix (Matrix.stdBasis ℂ (Fin d) (Fin d)) (Matrix.stdBasis ℂ (Fin d) (Fin d)) (inverseConjugatedMap Λ U) * tracelessProjector d = ((U.val ⊗ₖ U.val.map star))ᴴ * (tracelessProjector d * LinearMap.toMatrix (Matrix.stdBasis ℂ (Fin d) (Fin d)) (Matrix.stdBasis ℂ (Fin d) (Fin d)) (matrixAction Λ.toCompletelyPositiveMap) * tracelessProjector d) * (U.val ⊗ₖ U.val.map star) := by
  have hH : tracelessProjector d * ((U.val ⊗ₖ U.val.map star))ᴴ = ((U.val ⊗ₖ U.val.map star))ᴴ * tracelessProjector d := by
    rw [← conjugationRep_star]; exact projector_rep_commute (star U)
  rw [inverseConjugatedMap_transfer]
  calc
    _ = (tracelessProjector d * ((U.val ⊗ₖ U.val.map star))ᴴ) * LinearMap.toMatrix (Matrix.stdBasis ℂ (Fin d) (Fin d)) (Matrix.stdBasis ℂ (Fin d) (Fin d)) (matrixAction Λ.toCompletelyPositiveMap) * ((U.val ⊗ₖ U.val.map star) * tracelessProjector d) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hH, ← projector_rep_commute]; simp only [Matrix.mul_assoc]
end D5.S3.QuantumChannels.WallmanFlammiaTwoContractivity.ConjugationInterface
set_option backward.isDefEq.respectTransparency false
open D5.S3.Quantum.Foundation.FiniteStateChannel (QuantumChannel)
namespace D5.S3.QuantumChannels.WallmanFlammiaTwoContractivity.FinalAssembly
open D5.S3.QuantumChannels.WallmanFlammiaTwoContractivity.TensorCoordinates
open D5.S3.QuantumChannels.WallmanFlammiaTwoContractivity.CanonicalSector
open D5.S3.QuantumChannels.WallmanFlammiaTwoContractivity.CompressionSpectral
open D5.S3.QuantumChannels.WallmanFlammiaTwoContractivity.SpectralClosure
open Matrix Polynomial
open scoped BigOperators Kronecker Matrix.Norms.L2Operator
open D5.S3.QuantumChannels.WallmanFlammiaTwoContractivity.TraceCoordinates
open D5.S3.QuantumChannels.WallmanFlammiaTwoContractivity.TraceInterface
open D5.S3.QuantumChannels.WallmanFlammiaTwoContractivity.ConjugationInterface
open D5.S3.QuantumChannels.WallmanFlammiaTwoContractivity.DesignEntries
open D5.S3.QuantumChannels.WallmanFlammiaTwoContractivity.TransferGeometry
open D5.S3.Quantum.Recovery.LiJiangPolarPairOptimalityRefutation (matrixAction)
private theorem tensor_lift_average {n m g : Type*} [Fintype n] [Fintype m] [Fintype g] (V : Matrix n m ℂ) (W : Matrix m n ℂ) (A : g → Matrix m m ℂ) (t : ℂ) : (V ⊗ₖ V) * (t • ∑ x : g, A x ⊗ₖ A x) * (W ⊗ₖ W) = t • ∑ x : g, (V * A x * W) ⊗ₖ (V * A x * W) := by
  rw [Matrix.mul_smul, Matrix.smul_mul]; congr 1; rw [Matrix.mul_sum, Matrix.sum_mul]; apply Finset.sum_congr rfl; intro x hx
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
private theorem inverse_entry {d : ℕ}
    (Λ : QuantumChannel (Fin d) (Fin d))
    (U : Matrix.unitaryGroup (Fin d) ℂ) (r c : Fin d × Fin d) :
    LinearMap.toMatrix (Matrix.stdBasis ℂ (Fin d) (Fin d)) (Matrix.stdBasis ℂ (Fin d) (Fin d)) (inverseConjugatedMap Λ U) r c = conjugatedEntry Λ (star U) r c := by
  simp [transfer_entry, inverseConjugatedMap, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, conjugatedEntry, matrixAction, Matrix.star_eq_conjTranspose, Unitary.coe_star] <;> rfl
private theorem target_charpoly {d : ℕ}
    (Λ : QuantumChannel (Fin d) (Fin d))
    (G : Subgroup (Matrix.unitaryGroup (Fin d) ℂ)) [Fintype G] :
    (twirledTensorPower Λ G 2).charpoly = ((Fintype.card G : ℂ)⁻¹ • ∑ x : G, LinearMap.toMatrix (Matrix.stdBasis ℂ (Fin d) (Fin d)) (Matrix.stdBasis ℂ (Fin d) (Fin d)) (inverseConjugatedMap Λ x.val) ⊗ₖ LinearMap.toMatrix (Matrix.stdBasis ℂ (Fin d) (Fin d)) (Matrix.stdBasis ℂ (Fin d) (Fin d)) (inverseConjugatedMap Λ x.val)).charpoly := by
  classical
  rw [← Matrix.charpoly_reindex (finTwoArrowEquiv (Fin d × Fin d)), twirledTensorPower_two_reindex]; congr 1; congr 1
  have h (x : G) : (fun r c => conjugatedEntry Λ (x⁻¹).val r c) = LinearMap.toMatrix (Matrix.stdBasis ℂ (Fin d) (Fin d)) (Matrix.stdBasis ℂ (Fin d) (Fin d)) (inverseConjugatedMap Λ x.val) := by
    ext r c; rw [inverse_entry]; congr 1
  have hh := Equiv.sum_comp (Equiv.inv G) (fun x : G => (fun r c => conjugatedEntry Λ x.val r c) ⊗ₖ (fun r c => conjugatedEntry Λ x.val r c))
  simpa only [Equiv.inv_apply, h] using hh.symm
private theorem canonical_result {d : ℕ} (hd : 2 ≤ d) (Λ : QuantumChannel (Fin d) (Fin d)) (G : Subgroup (Matrix.unitaryGroup (Fin d) ℂ)) [Fintype G] (hG : IsUnitaryTwoDesign G) (hnot : ¬ ∃ U : Matrix.unitaryGroup (Fin d) ℂ, ∀ X : Matrix (Fin d) (Fin d) ℂ, CStarMatrix.ofMatrix.symm (Λ.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) = U.val * X * U.val.conjTranspose) : IsNContractive Λ G 2 := by
  classical
  let hd0 : 0 < d := by omega
  letI : Nonempty (Fin d) := ⟨⟨0, hd0⟩⟩
  let κ := Fin (Module.finrank ℂ (((Matrix.traceLinearMap (Fin d) ℂ ℂ).ker)))
  let b : Module.Basis κ ℂ (((Matrix.traceLinearMap (Fin d) ℂ ℂ).ker)) := Module.finBasis ℂ (((Matrix.traceLinearMap (Fin d) ℂ ℂ).ker))
  let V := (LinearMap.toMatrix b (Matrix.stdBasis ℂ (Fin d) (Fin d)) ((Matrix.traceLinearMap (Fin d) ℂ ℂ).ker).subtype)
  let W := (LinearMap.toMatrix (Matrix.stdBasis ℂ (Fin d) (Fin d)) b (project hd0))
  let P := tracelessProjector d
  let L := LinearMap.toMatrix (Matrix.stdBasis ℂ (Fin d) (Fin d)) (Matrix.stdBasis ℂ (Fin d) (Fin d)) (matrixAction Λ.toCompletelyPositiveMap)
  let B := P * L * P
  let F := fun x : G => inverseConjugatedMap Λ x.val
  let A := fun x : G => smallMatrix hd0 b (F x)
  let D := fun x : G => ((x.val.val ⊗ₖ x.val.val.map star))ᴴ * B * (x.val.val ⊗ₖ x.val.val.map star)
  let t : ℂ := (Fintype.card G : ℂ)⁻¹
  let f : ℂ := B.trace / ((d : ℂ)^2 - 1)
  have hWV : W * V = 1 := projection_inclusion_matrix hd0 b
  have hVW : V * W = P := inclusion_projection_matrix hd0 b
  have hPV : P * V = V := by rw [← hVW, Matrix.mul_assoc, hWV, Matrix.mul_one]
  have hWP : W * P = W := by rw [← hVW, ← Matrix.mul_assoc, hWV, Matrix.one_mul]
  have hlift (x : G) : V * A x * W = D x := by
    exact (smallMatrix_lift hd0 b (F x)).trans (inverseConjugatedMap_compression Λ x.val)
  have hsmall (x : G) : A x = W * D x * V := by
    rw [← hlift]; simp only [← Matrix.mul_assoc, hWV, Matrix.one_mul]; rw [Matrix.mul_assoc, hWV, Matrix.mul_one]
  have hzero : (∑ i : Fin d, ∑ j : Fin d, B (i,i) (j,j)) = 0 := by
    apply diagonal_pair_sum_zero_of_kills_trace; dsimp only [B]; rw [← Matrix.mulVec_mulVec, tracelessProjector_kills_trace hd0, Matrix.mulVec_zero]
  have hmeanD : t • ∑ x : G, D x = f • P := averaged_traceless_endomorphism hd G hG B hzero
  have hmean : t • ∑ x : G, A x = f • (1 : Matrix κ κ ℂ) := by
    calc
      _ = W * (t • ∑ x : G, D x) * V := by
        simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sum, Matrix.sum_mul, hsmall]
      _ = W * (f • P) * V := by rw [hmeanD]
      _ = _ := by simp only [Matrix.mul_smul, Matrix.smul_mul, hWP, hWV]
  have hmeanAdapt : t • ∑ x : G, ((fun i j : κ => LinearMap.toMatrix (adaptedBasis hd0 b) (adaptedBasis hd0 b) (F x) (.inr i) (.inr j)) : Matrix κ κ ℂ) = f • (1 : Matrix κ κ ℂ) := by
    simpa only [A, smallMatrix_adapted] using hmean
  have ht : t * (Fintype.card G : ℂ) = 1 := by
    have hc : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    exact inv_mul_cancel₀ hc
  have hfactor : (twirledTensorPower Λ G 2).charpoly = (X - C 1) * ((X - C f) ^ (2 * Fintype.card κ) * (t • ∑ x : G, A x ⊗ₖ A x).charpoly) := by
    rw [target_charpoly]; rw [tensor_average_charpoly_basis (Matrix.stdBasis ℂ (Fin d) (Fin d)) (adaptedBasis hd0 b) F t]
    simpa only [A, smallMatrix_adapted] using adapted_tensor_charpoly hd0 b F (fun x => inverseConjugatedMap_trace Λ x.val) t f ht hmeanAdapt
  have hf : ‖f‖ < 1 := by
    have hf0 := canonical_one_copy_strict hd Λ hnot
    convert hf0 using 1 <;> simp only [f, B, P, L, Complex.ofReal_sub, Complex.ofReal_pow, Complex.ofReal_natCast, Complex.ofReal_one]
  let u : ℝ := ‖t • ∑ x : G, D x ⊗ₖ D x‖
  have hu : u < 1 := canonical_tensor_strict hd Λ G hG hnot
  have hTensorLift : (V ⊗ₖ V) * (t • ∑ x : G, A x ⊗ₖ A x) * (W ⊗ₖ W) = t • ∑ x : G, D x ⊗ₖ D x := by
    rw [tensor_lift_average]; simp_rw [hlift]
  have hTensorWV : (W ⊗ₖ W) * (V ⊗ₖ V) = 1 := by
    rw [← Matrix.mul_kronecker_mul, hWV, Matrix.one_kronecker_one]
  have hbound (z : ℂ) (hz : z ∈ (t • ∑ x : G, A x ⊗ₖ A x).charpoly.roots) : ‖z‖ ≤ u := by
    apply compression_root_bound (V ⊗ₖ V) (W ⊗ₖ W) hTensorWV (t • ∑ x : G, A x ⊗ₖ A x) u (norm_nonneg _) _ z hz; intro w hw; rw [hTensorLift] at hw
    exact spectrum.norm_le_norm_of_mem (Matrix.mem_spectrum_of_isRoot_charpoly ((Polynomial.mem_roots (Matrix.charpoly_monic _).ne_zero).mp hw))
  have hc := unit_circle_roots_of_block_bound (Fintype.card κ) f u (twirledTensorPower Λ G 2).charpoly (t • ∑ x : G, A x ⊗ₖ A x).charpoly (Matrix.charpoly_monic _).ne_zero hfactor hf hu hbound
  exact hc.le
end D5.S3.QuantumChannels.WallmanFlammiaTwoContractivity.FinalAssembly
namespace D5.S3.QuantumChannels.WallmanFlammiaTwoContractivity
theorem result : claim := by
  intro d hd Λ G _ hG hnot; exact FinalAssembly.canonical_result hd Λ G hG hnot
end D5.S3.QuantumChannels.WallmanFlammiaTwoContractivity
