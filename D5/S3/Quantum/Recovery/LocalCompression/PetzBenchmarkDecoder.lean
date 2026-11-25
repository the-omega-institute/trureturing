/- GID: D5/S3/Quantum/Recovery/LocalCompression/PetzBenchmarkDecoder
   generality: I
   mirror-B: D5/B/S3/Quantum/Recovery/LocalCompression/PetzBenchmarkDecoder
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fixed-reference completed Petz channels compose through singular intermediate states. -/

/-
proof_shape: content
admission_basis: escape-witness
escape_witness: The intermediate spectral support cancels between the two
reverse Kraus matrices, and the outer decoder sends the inner reset state
back to the original reference.
-/

import D5.S3.Quantum.Recovery.CanonicalPetzEquality
import D5.S3.Quantum.Divergence.UmegakiKernelContraction
import D5.S3.Quantum.Recovery.ReferencePetzChannel
import D5.S3.Quantum.Recovery.LocalCompression.PetzFixedMarginalNoise

/-! # Transitivity and compression with the ordinary Petz decoder -/

noncomputable section

open scoped BigOperators ComplexOrder MatrixOrder Kronecker
open Matrix
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteKrausChannel (finite_kraus_quantum_channel)
open D5.S3.Quantum.Recovery.ReferencePetzChannel (completed_reference_petz_channel)
open D5.S3.Quantum.Recovery.SpectralTransposeRecovery

namespace D5.S3.Quantum.Recovery.LocalCompression.PetzBenchmarkDecoder

set_option autoImplicit false
set_option relaxedAutoImplicit false

variable {A B C I J : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype C] [DecidableEq C] [Fintype I] [Fintype J]

/-- Matrix action of a finite quantum channel. -/
abbrev matrixAction (N : QuantumChannel A B) (X : Matrix A A ℂ) : Matrix B B ℂ :=
  CStarMatrix.ofMatrix.symm (N.toCompletelyPositiveMap (CStarMatrix.ofMatrix X))

/-- The finite channel with the prescribed Kraus matrices. -/
def krausChannel (K : I → Matrix B A ℂ) (hK : (∑ i, (K i)ᴴ * K i) = 1) :
    QuantumChannel A B :=
  Classical.choose (finite_kraus_quantum_channel K hK)

private theorem krausChannel_apply (K : I → Matrix B A ℂ)
    (hK : (∑ i, (K i)ᴴ * K i) = 1) (X : Matrix A A ℂ) :
    matrixAction (krausChannel K hK) X = ∑ i, K i * X * (K i)ᴴ :=
  Classical.choose_spec (finite_kraus_quantum_channel K hK) X

abbrev raw (σ : DensityState A) : Matrix A A ℂ := CStarMatrix.ofMatrix.symm σ.1

/-- The ordinary Petz channel with the input reference as its reset state. -/
def completedPetz (K : I → Matrix B A ℂ) (hK : (∑ i, (K i)ᴴ * K i) = 1)
    (σ : DensityState A) : QuantumChannel B A :=
  Classical.choose (completed_reference_petz_channel K hK σ)

/-- Multiplication of the two Kraus families in forward order. -/
def compositeKraus (K : I → Matrix B A ℂ) (L : J → Matrix C B ℂ) :
    I × J → Matrix C A ℂ := fun ij => L ij.2 * K ij.1

omit [Fintype A] [DecidableEq C] in
private theorem composite_complete (K : I → Matrix B A ℂ) (L : J → Matrix C B ℂ)
    (hK : (∑ i, (K i)ᴴ * K i) = 1) (hL : (∑ j, (L j)ᴴ * L j) = 1) :
    (∑ ij, (compositeKraus K L ij)ᴴ * compositeKraus K L ij) = 1 := by
  classical
  rw [Fintype.sum_prod_type, ← hK]
  refine Finset.sum_congr rfl fun i _ => ?_
  calc
    _ = (K i)ᴴ * (∑ j, (L j)ᴴ * L j) * K i := by
      simp only [compositeKraus, Matrix.conjTranspose_mul, Matrix.mul_sum, Matrix.sum_mul,
        Matrix.mul_assoc]
    _ = _ := by rw [hL, Matrix.mul_one]

/-- The forward composite represented by the multiplied Kraus matrices. -/
def compositeChannel (K : I → Matrix B A ℂ) (L : J → Matrix C B ℂ)
    (hK : (∑ i, (K i)ᴴ * K i) = 1) (hL : (∑ j, (L j)ᴴ * L j) = 1) :
    QuantumChannel A C :=
  krausChannel (compositeKraus K L) (composite_complete K L hK hL)

/-- The completed ordinary Petz decoder for the forward composite. -/
def compositePetz (K : I → Matrix B A ℂ) (L : J → Matrix C B ℂ)
    (hK : (∑ i, (K i)ᴴ * K i) = 1) (hL : (∑ j, (L j)ᴴ * L j) = 1)
    (σ : DensityState A) : QuantumChannel C A :=
  completedPetz (compositeKraus K L) (composite_complete K L hK hL) σ

private theorem composite_apply (K : I → Matrix B A ℂ) (L : J → Matrix C B ℂ)
    (hK : (∑ i, (K i)ᴴ * K i) = 1) (hL : (∑ j, (L j)ᴴ * L j) = 1)
    (X : Matrix A A ℂ) :
    matrixAction (compositeChannel K L hK hL) X =
      matrixAction (krausChannel L hL) (matrixAction (krausChannel K hK) X) := by
  classical
  simp only [compositeChannel, krausChannel_apply, Fintype.sum_prod_type,
    compositeKraus, Matrix.conjTranspose_mul, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_assoc]
  exact Finset.sum_comm

private theorem completedPetz_apply (K : I → Matrix B A ℂ)
    (hK : (∑ i, (K i)ᴴ * K i) = 1) (σ : DensityState A) (X : Matrix B B ℂ) :
    let τ := raw ((krausChannel K hK).mapState σ)
    let S := cfc Real.sqrt (raw σ)
    let W := spectralInverseSqrt τ
    matrixAction (completedPetz K hK σ) X =
      (∑ i, S * (K i)ᴴ * W * X * W * K i * S) +
        Matrix.trace ((1 - spectralSupport τ) * X) • raw σ := by
  have h := (Classical.choose_spec (completed_reference_petz_channel K hK σ)).1 X
  dsimp only
  change matrixAction (completedPetz K hK σ) X =
    (∑ i, cfc Real.sqrt (raw σ) * (K i)ᴴ *
      spectralInverseSqrt (matrixAction (krausChannel K hK) (raw σ)) * X *
      spectralInverseSqrt (matrixAction (krausChannel K hK) (raw σ)) * K i *
      cfc Real.sqrt (raw σ)) +
      Matrix.trace ((1 - spectralSupport (matrixAction (krausChannel K hK) (raw σ))) * X) •
        raw σ
  rw [krausChannel_apply]
  exact h

private theorem completedPetz_reference (K : I → Matrix B A ℂ)
    (hK : (∑ i, (K i)ᴴ * K i) = 1) (σ : DensityState A) :
    matrixAction (completedPetz K hK σ) (raw ((krausChannel K hK).mapState σ)) = raw σ := by
  change matrixAction (completedPetz K hK σ) (matrixAction (krausChannel K hK) (raw σ)) = _
  rw [krausChannel_apply]
  exact (Classical.choose_spec (completed_reference_petz_channel K hK σ)).2

private theorem sqrt_adjoint (M : Matrix A A ℂ) :
    (cfc Real.sqrt M)ᴴ = cfc Real.sqrt M :=
  (cfc_predicate _ _ : IsSelfAdjoint (cfc Real.sqrt M)).star_eq

private theorem sqrt_sq {M : Matrix A A ℂ} (hM : M.PosSemidef) :
    cfc Real.sqrt M * cfc Real.sqrt M = M := by
  have hcont := M.finite_real_spectrum.continuousOn Real.sqrt
  calc
    _ = cfc (fun x : ℝ => √x * √x) M :=
      (cfc_mul Real.sqrt Real.sqrt M hcont hcont).symm
    _ = cfc (fun x : ℝ => x) M := by
      apply cfc_congr
      intro x hx
      rw [hM.isHermitian.spectrum_real_eq_range_eigenvalues] at hx
      obtain ⟨i, rfl⟩ := hx
      exact Real.mul_self_sqrt (hM.eigenvalues_nonneg i)
    _ = M := cfc_id' ℝ M hM.isHermitian.isSelfAdjoint

private theorem inverseSqrt_mul_sqrt {M : Matrix A A ℂ} (hM : M.PosSemidef) :
    spectralInverseSqrt M * cfc Real.sqrt M = spectralSupport M := by
  unfold spectralInverseSqrt spectralSupport
  rw [← cfc_mul _ _ M (M.finite_real_spectrum.continuousOn _)
    (M.finite_real_spectrum.continuousOn _)]
  apply cfc_congr
  intro x hx
  rw [hM.isHermitian.spectrum_real_eq_range_eigenvalues] at hx
  obtain ⟨i, rfl⟩ := hx
  by_cases h : hM.isHermitian.eigenvalues i = 0
  · simp [h]
  · have hr := Real.sqrt_pos.2 (lt_of_le_of_ne (hM.eigenvalues_nonneg i) (Ne.symm h))
    simp [h, ne_of_gt hr]

private theorem support_mul_sqrt (M : Matrix A A ℂ) :
    spectralSupport M * cfc Real.sqrt M = cfc Real.sqrt M := by
  unfold spectralSupport
  rw [← cfc_mul _ _ M (M.finite_real_spectrum.continuousOn _)
    (M.finite_real_spectrum.continuousOn _)]
  apply cfc_congr
  intro x _
  by_cases h : x = 0 <;> simp [h]

private theorem support_on_weighted_kraus (K : I → Matrix B A ℂ)
    (hK : (∑ i, (K i)ᴴ * K i) = 1) (σ : DensityState A) (i : I) :
    let S := cfc Real.sqrt (raw σ)
    let τ := raw ((krausChannel K hK).mapState σ)
    spectralSupport τ * (K i * S) = K i * S := by
  dsimp only
  have hS := sqrt_sq (D5.S3.Quantum.Information.PartialTraceMutualInformation.density_posSemidef σ)
  have ht : raw ((krausChannel K hK).mapState σ) =
      ∑ j, (K j * cfc Real.sqrt (raw σ)) * (K j * cfc Real.sqrt (raw σ))ᴴ := by
    change matrixAction (krausChannel K hK) (raw σ) = _
    rw [krausChannel_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Matrix.conjTranspose_mul, sqrt_adjoint, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (cfc Real.sqrt (raw σ)), hS]
  rw [ht]
  exact spectral_support_on_kraus (fun j => K j * cfc Real.sqrt (raw σ)) i

private theorem action_add (N : QuantumChannel A B) (X Y : Matrix A A ℂ) :
    matrixAction N (X + Y) = matrixAction N X + matrixAction N Y :=
  map_add N.toCompletelyPositiveMap _ _

private theorem action_smul (N : QuantumChannel A B) (z : ℂ) (X : Matrix A A ℂ) :
    matrixAction N (z • X) = z • matrixAction N X :=
  map_smul N.toCompletelyPositiveMap _ _

/-- For arbitrary input matrices, the composed ordinary Petz decoder agrees
with the ordinary decoder of the forward composite, with fixed reference reset. -/
theorem completed_petz_transitivity (K : I → Matrix B A ℂ) (L : J → Matrix C B ℂ)
    (hK : (∑ i, (K i)ᴴ * K i) = 1) (hL : (∑ j, (L j)ᴴ * L j) = 1)
    (σ : DensityState A) (X : Matrix C C ℂ) :
    let sequential := matrixAction (completedPetz K hK σ)
      (matrixAction (completedPetz L hL ((krausChannel K hK).mapState σ)) X)
    matrixAction (compositePetz K L hK hL σ) X = sequential := by
  classical
  dsimp only
  let τ := (krausChannel K hK).mapState σ
  let υ := (krausChannel L hL).mapState τ
  let S := cfc Real.sqrt (raw σ)
  let T := cfc Real.sqrt (raw τ)
  let P := spectralSupport (raw τ)
  let W := spectralInverseSqrt (raw τ)
  let V := spectralInverseSqrt (raw υ)
  let Y := ∑ j, T * (L j)ᴴ * V * X * V * L j * T
  let z := Matrix.trace ((1 - spectralSupport (raw υ)) * X)
  have hout : raw ((compositeChannel K L hK hL).mapState σ) = raw υ :=
    composite_apply K L hK hL (raw σ)
  have hT : W * T = P := inverseSqrt_mul_sqrt
    (D5.S3.Quantum.Information.PartialTraceMutualInformation.density_posSemidef τ)
  have hW : Wᴴ = W :=
    (cfc_predicate _ _ : IsSelfAdjoint (spectralInverseSqrt (raw τ))).star_eq
  have hP : Pᴴ = P :=
    (cfc_predicate _ _ : IsSelfAdjoint (spectralSupport (raw τ))).star_eq
  have hT' : T * W = P := by
    simpa only [Matrix.conjTranspose_mul, hW, T, sqrt_adjoint, hP] using
      congrArg Matrix.conjTranspose hT
  have hright (i : I) : P * (K i * S) = K i * S :=
    support_on_weighted_kraus K hK σ i
  have hleft (i : I) : S * (K i)ᴴ * P = S * (K i)ᴴ := by
    simpa only [Matrix.conjTranspose_mul, hP, S, sqrt_adjoint] using
      congrArg Matrix.conjTranspose (hright i)
  have hY : P * Y = Y := by
    simp only [Y, Matrix.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [← Matrix.mul_assoc, show P * T = T from support_mul_sqrt (raw τ)]
  have htrace : Matrix.trace ((1 - P) * Y) = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, hY, sub_self, Matrix.trace_zero]
  have hinner : matrixAction (completedPetz L hL τ) X = Y + z • raw τ :=
    completedPetz_apply L hL τ X
  rw [hinner, action_add, action_smul, completedPetz_reference K hK σ]
  have houter := completedPetz_apply K hK σ Y
  change matrixAction (completedPetz K hK σ) Y =
    (∑ i, S * (K i)ᴴ * W * Y * W * K i * S) + Matrix.trace ((1 - P) * Y) • raw σ at houter
  rw [houter, htrace, zero_smul, add_zero]
  unfold compositePetz
  rw [completedPetz_apply]
  change (∑ ij, S * (compositeKraus K L ij)ᴴ *
    spectralInverseSqrt (raw ((compositeChannel K L hK hL).mapState σ)) * X *
    spectralInverseSqrt (raw ((compositeChannel K L hK hL).mapState σ)) *
    compositeKraus K L ij * S) +
    Matrix.trace ((1 - spectralSupport (raw ((compositeChannel K L hK hL).mapState σ))) * X) •
      raw σ = _
  rw [hout]
  congr 1
  rw [Fintype.sum_prod_type]
  simp only [Y, Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [compositeKraus, Matrix.conjTranspose_mul]
  change S * ((K i)ᴴ * (L j)ᴴ) * V * X * V * (L j * K i) * S =
    S * (K i)ᴴ * W * (T * (L j)ᴴ * V * X * V * L j * T) * W * K i * S
  calc
    _ = S * (K i)ᴴ * ((L j)ᴴ * V * X * V * L j) * (K i * S) := by
      simp only [Matrix.mul_assoc]
    _ = (S * (K i)ᴴ * P) * ((L j)ᴴ * V * X * V * L j) * (P * (K i * S)) := by
      rw [hleft, hright]
    _ = _ := by
      nth_rw 1 [← hT]
      rw [← hT']
      simp only [Matrix.mul_assoc]


section Compression

open D5.S3.Quantum.Information.PartialTraceMutualInformation
  (partialTraceRight trace_partialTraceRight marginalRight)
open D5.S3.Quantum.Divergence.UmegakiReferenceTransport (partialTraceRight_mul_embed)
open D5.S3.Quantum.Divergence.CanonicalChannelDPI
  (actual_kraus_representation krausAdjoint extended_quantum_relative_entropy_channel_dpi)
open D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy
open D5.S3.Quantum.Recovery.LocalCompression.PetzFixedMarginalNoise (loss)
open D5.S3.Quantum.Foundation.FiniteTraceDistance
  (traceNorm traceNorm_add_le traceNorm_neg traceNorm_of_posSemidef trace_norm_jordan_mass)

universe u

variable {R E F : Type u} [Fintype R] [DecidableEq R] [Nonempty R]
  [Fintype E] [DecidableEq E] [Nonempty E] [Fintype F] [DecidableEq F] [Nonempty F]

/-- Discard the environment and retain the first subsystem. -/
def retainedErasure : QuantumChannel (R × E) R :=
  Classical.choose D5.S3.Quantum.Divergence.FannesRootFidelityHolevo.exists_eraseChannel

omit [Nonempty R] [Nonempty E] in
private theorem retainedErasure_apply (X : Matrix (R × E) (R × E) ℂ) :
    matrixAction retainedErasure X = partialTraceRight X := by
  have he : matrixAction retainedErasure X =
      ∑ e : E, X.submatrix (fun r => (r, e)) (fun r => (r, e)) :=
    Classical.choose_spec D5.S3.Quantum.Divergence.FannesRootFidelityHolevo.exists_eraseChannel X
  rw [he]
  ext r s
  simp [Matrix.sum_apply, partialTraceRight]

omit [Nonempty R] [Nonempty E] in
private theorem krausErasure_apply (X : Matrix (R × E) (R × E) ℂ) :
    let L := actual_kraus_representation (retainedErasure (R := R) (E := E))
    matrixAction (krausChannel L.kraus L.hkraus) X = partialTraceRight X := by
  dsimp only
  rw [krausChannel_apply, ← (actual_kraus_representation retainedErasure).haction X]
  exact retainedErasure_apply X

/-- The ordinary decoder of the actual retained partial trace, with reference reset. -/
def retainedPetz (σ : DensityState (R × E)) : QuantumChannel R (R × E) :=
  let L := actual_kraus_representation (retainedErasure (R := R) (E := E))
  completedPetz L.kraus L.hkraus σ

/-- The ordinary Petz benchmark obtained by decoding the actual retained marginal. -/
def benchmark (ρ σ : DensityState (R × E)) : DensityState (R × E) :=
  (retainedPetz σ).mapState (marginalRight ρ)

private theorem kraus_trace_pair (K : I → Matrix B A ℂ)
    (hK : (∑ i, (K i)ᴴ * K i) = 1) (X : Matrix A A ℂ) (Y : Matrix B B ℂ) :
    (X * krausAdjoint K Y).trace = (matrixAction (krausChannel K hK) X * Y).trace := by
  rw [krausChannel_apply, krausAdjoint, Matrix.mul_sum, Matrix.sum_mul,
    Matrix.trace_sum, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simpa only [Matrix.mul_assoc] using Matrix.trace_mul_cycle (X * (K i)ᴴ) Y (K i)

omit [Nonempty R] [Nonempty E] in
private theorem decoder_of_partialTrace (K : I → Matrix R (R × E) ℂ)
    (hK : (∑ i, (K i)ᴴ * K i) = 1)
    (hErase : ∀ X, matrixAction (krausChannel K hK) X = partialTraceRight X)
    (σ : DensityState (R × E)) (X : Matrix R R ℂ) :
    let W := spectralInverseSqrt (partialTraceRight (raw σ))
    let S := cfc Real.sqrt (raw σ)
    matrixAction (completedPetz K hK σ) X =
      S * ((W * X * W) ⊗ₖ (1 : Matrix E E ℂ)) * S +
        Matrix.trace ((1 - spectralSupport (partialTraceRight (raw σ))) * X) • raw σ := by
  dsimp only
  have hadjoint (Y : Matrix R R ℂ) : krausAdjoint K Y = Y ⊗ₖ (1 : Matrix E E ℂ) := by
    apply Matrix.ext_iff_trace_mul_left.mpr
    intro Z
    rw [kraus_trace_pair K hK, hErase, ← partialTraceRight_mul_embed, trace_partialTraceRight]
  have hσ : raw ((krausChannel K hK).mapState σ) = partialTraceRight (raw σ) :=
    hErase (raw σ)
  rw [completedPetz_apply, hσ]
  rw [← hadjoint]
  simp only [krausAdjoint, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_assoc]

/-- Compress the environment while preserving the retained partial trace.
The original benchmark is reconstructed exactly by decoding the compressed
benchmark, with the same fixed reference reset as in transitivity. -/
theorem compression_recovers_benchmark (K : I → Matrix (R × F) (R × E) ℂ)
    (hK : (∑ i, (K i)ᴴ * K i) = 1)
    (hRetained : ∀ X, partialTraceRight (matrixAction (krausChannel K hK) X) =
      partialTraceRight X)
    (ρ σ : DensityState (R × E)) :
    let N := krausChannel K hK
    (completedPetz K hK σ).mapState (benchmark (N.mapState ρ) (N.mapState σ)) =
      benchmark ρ σ := by
  dsimp only
  let L := actual_kraus_representation (retainedErasure (R := R) (E := F))
  let L₀ := actual_kraus_representation (retainedErasure (R := R) (E := E))
  have hcomp (X : Matrix (R × E) (R × E) ℂ) :
      matrixAction (compositeChannel K L.kraus hK L.hkraus) X = partialTraceRight X := by
    rw [composite_apply, krausErasure_apply, hRetained]
  have hmarg : marginalRight ((krausChannel K hK).mapState ρ) = marginalRight ρ := by
    apply Subtype.ext
    apply CStarMatrix.ofMatrix.symm.injective
    exact hRetained (raw ρ)
  apply Subtype.ext
  apply CStarMatrix.ofMatrix.symm.injective
  change matrixAction (completedPetz K hK σ)
    (matrixAction (completedPetz L.kraus L.hkraus ((krausChannel K hK).mapState σ))
      (raw (marginalRight ((krausChannel K hK).mapState ρ)))) =
    matrixAction (completedPetz L₀.kraus L₀.hkraus σ) (raw (marginalRight ρ))
  rw [hmarg, ← completed_petz_transitivity]
  change matrixAction (completedPetz (compositeKraus K L.kraus)
    (composite_complete K L.kraus hK L.hkraus) σ) (raw (marginalRight ρ)) = _
  rw [decoder_of_partialTrace _ _ hcomp, decoder_of_partialTrace _ _ krausErasure_apply]

private theorem action_sub (N : QuantumChannel A B) (X Y : Matrix A A ℂ) :
    matrixAction N (X - Y) = matrixAction N X - matrixAction N Y :=
  map_sub N.toCompletelyPositiveMap _ _

private theorem traceNorm_contract (N : QuantumChannel A B) (X : Matrix A A ℂ)
    (hX : X.IsHermitian) : traceNorm (matrixAction N X) ≤ traceNorm X := by
  let P := posPart X
  let Q := negPart X
  have hmass (Y : Matrix A A ℂ) (hY : 0 ≤ Y) :
      traceNorm (matrixAction N Y) = (Matrix.trace Y).re := by
    have hout : (matrixAction N Y).PosSemidef :=
      (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm
        (map_nonneg N.toCompletelyPositiveMap
          (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv hY))).posSemidef
    exact (congrArg Complex.re (traceNorm_of_posSemidef hout)).trans
      (congrArg Complex.re (N.trace_preserving (CStarMatrix.ofMatrix Y)))
  calc
    traceNorm (matrixAction N X) =
        traceNorm (matrixAction N P - matrixAction N Q) := by
      rw [← action_sub, CFC.posPart_sub_negPart X hX]
    _ ≤ traceNorm (matrixAction N P) + traceNorm (matrixAction N Q) := by
      rw [sub_eq_add_neg, ← traceNorm_neg (matrixAction N Q)]
      exact traceNorm_add_le _ _
    _ = traceNorm X := by
      rw [hmass P (CFC.posPart_nonneg X), hmass Q (CFC.negPart_nonneg X),
        trace_norm_jordan_mass X hX]

/-- The unhalved ordinary Petz score using the actual supported entropy loss. -/
def compressionScore (ρ σ : DensityState (R × E)) : ℝ :=
  traceNorm (raw ρ - raw (benchmark ρ σ)) ^ 2 / loss ρ σ

/-- A single retained-marginal preserving compression retains a strict score
whenever the trace norm of the source decoder residual fits the score margin. -/
theorem strict_score_of_decoder_residual (K : I → Matrix (R × F) (R × E) ℂ)
    (hK : (∑ i, (K i)ᴴ * K i) = 1)
    (hRetained : ∀ X, partialTraceRight (matrixAction (krausChannel K hK) X) =
      partialTraceRight X)
    (ρ σ : DensityState (R × E)) (hSupp : SupportContained ρ σ)
    (threshold : ℝ) (hthreshold : 0 ≤ threshold) (ε : ℝ) :
    let N := krausChannel K hK
    let ρ' := N.mapState ρ
    let σ' := N.mapState σ
    let decoded := (completedPetz K hK σ).mapState ρ'
    traceNorm (raw ρ - raw decoded) ≤ ε →
    ε + Real.sqrt (threshold * loss ρ σ) < traceNorm (raw ρ - raw (benchmark ρ σ)) →
    0 < loss ρ' σ' ∧ threshold < compressionScore ρ' σ' := by
  classical
  dsimp only
  let N := krausChannel K hK
  let ρ' := N.mapState ρ
  let σ' := N.mapState σ
  let decoder := completedPetz K hK σ
  have hmarg (ω : DensityState (R × E)) : marginalRight (N.mapState ω) = marginalRight ω := by
    apply Subtype.ext
    apply CStarMatrix.ofMatrix.symm.injective
    exact hRetained (raw ω)
  have hdpi := extended_quantum_relative_entropy_channel_dpi N ρ σ
  have hs' := (extendedQuantumRelativeEntropy_ne_top_iff ρ' σ').mp
    (ne_top_of_le_ne_top ((extendedQuantumRelativeEntropy_ne_top_iff ρ σ).mpr hSupp) hdpi)
  rw [extendedQuantumRelativeEntropy_eq_coe_of_support hSupp,
    extendedQuantumRelativeEntropy_eq_coe_of_support hs'] at hdpi
  have hLossLE : loss ρ' σ' ≤ loss ρ σ := by
    unfold loss
    rw [hmarg ρ, hmarg σ]
    exact sub_le_sub_right (WithTop.coe_le_coe.mp hdpi) _
  intro hresidual hmargin
  have hBenchmark := compression_recovers_benchmark K hK hRetained ρ σ
  have hcontract := traceNorm_contract decoder (raw ρ' - raw (benchmark ρ' σ'))
    ((D5.S3.Quantum.Information.PartialTraceMutualInformation.density_posSemidef ρ').isHermitian.sub
      (D5.S3.Quantum.Information.PartialTraceMutualInformation.density_posSemidef
        (benchmark ρ' σ')).isHermitian)
  rw [action_sub] at hcontract
  change traceNorm (raw (decoder.mapState ρ') - raw (decoder.mapState (benchmark ρ' σ'))) ≤
    traceNorm (raw ρ' - raw (benchmark ρ' σ')) at hcontract
  rw [hBenchmark] at hcontract
  have htri := traceNorm_add_le (raw ρ - raw (decoder.mapState ρ'))
    (raw (decoder.mapState ρ') - raw (benchmark ρ σ))
  rw [sub_add_sub_cancel] at htri
  have hmain : Real.sqrt (threshold * loss ρ σ) <
      traceNorm (raw ρ' - raw (benchmark ρ' σ')) := by linarith
  have hrespos : 0 < traceNorm (raw ρ' - raw (benchmark ρ' σ')) :=
    (Real.sqrt_nonneg _).trans_lt hmain
  let erase : QuantumChannel (R × F) R := retainedErasure
  have herase (ω : DensityState (R × F)) : erase.mapState ω = marginalRight ω := by
    apply Subtype.ext
    apply CStarMatrix.ofMatrix.symm.injective
    exact retainedErasure_apply (raw ω)
  have hdpiErase := extended_quantum_relative_entropy_channel_dpi erase ρ' σ'
  have hsErase := (extendedQuantumRelativeEntropy_ne_top_iff _ _).mp
    (ne_top_of_le_ne_top ((extendedQuantumRelativeEntropy_ne_top_iff ρ' σ').mpr hs') hdpiErase)
  rw [extendedQuantumRelativeEntropy_eq_coe_of_support hs',
    extendedQuantumRelativeEntropy_eq_coe_of_support hsErase, herase ρ', herase σ'] at hdpiErase
  have hloss : 0 ≤ loss ρ' σ' := sub_nonneg.mpr (WithTop.coe_le_coe.mp hdpiErase)
  have hloss' : 0 < loss ρ' σ' := by
    by_contra! h
    have heq : loss ρ' σ' = 0 := le_antisymm h hloss
    obtain ⟨D, hD, _, hEq⟩ :=
      D5.S3.Quantum.Recovery.CanonicalPetzEquality.supported_entropy_equality_iff_fixed_petz_recovery
        erase σ'
    have hrecovered : D.mapState (erase.mapState ρ') = ρ' := by
      apply (hEq ρ' hs').mp
      rw [herase ρ', herase σ']
      exact sub_eq_zero.mp heq
    have hD' : matrixAction (retainedPetz σ') (raw (erase.mapState ρ')) =
        matrixAction D (raw (erase.mapState ρ')) := by
      have hDAction := hD (raw (erase.mapState ρ'))
      change matrixAction D (raw (erase.mapState ρ')) = _ at hDAction
      unfold retainedPetz
      rw [completedPetz_apply, hDAction]
      let L := actual_kraus_representation erase
      have hσ' : raw ((krausChannel L.kraus L.hkraus).mapState σ') =
          raw (erase.mapState σ') := by
        change matrixAction (krausChannel L.kraus L.hkraus) (raw σ') =
          matrixAction erase (raw σ')
        rw [krausChannel_apply]
        exact (L.haction _).symm
      dsimp only [erase, L] at hσ'
      rw [hσ']
    have hDone : raw (benchmark ρ' σ') = raw ρ' := by
      calc
        _ = matrixAction (retainedPetz σ') (raw (erase.mapState ρ')) := by
          rw [herase]
          rfl
        _ = raw ρ' := hD'.trans (congrArg raw hrecovered)
    rw [hDone, sub_self] at hrespos
    have hzero : traceNorm (0 : Matrix (R × F) (R × F) ℂ) = 0 := by
      simp [D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm]
    rw [hzero] at hrespos
    exact (lt_irrefl 0) hrespos
  refine ⟨hloss', (lt_div_iff₀ hloss').mpr ?_⟩
  have hbudget := mul_le_mul_of_nonneg_left hLossLE hthreshold
  have hnonneg : 0 ≤ threshold * loss ρ σ :=
    (mul_nonneg hthreshold hloss).trans hbudget
  nlinarith [Real.sq_sqrt hnonneg, Real.sqrt_nonneg (threshold * loss ρ σ)]

end Compression

#print axioms completed_petz_transitivity
#print axioms compression_recovers_benchmark
#print axioms strict_score_of_decoder_residual

end D5.S3.Quantum.Recovery.LocalCompression.PetzBenchmarkDecoder
