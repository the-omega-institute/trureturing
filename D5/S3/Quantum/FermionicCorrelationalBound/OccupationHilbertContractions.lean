/- GID: D5/S3/Quantum/FermionicCorrelationalBound/OccupationHilbertContractions
   generality: G
   mirror-B: D5/B/S3/Quantum/FermionicCorrelationalBound/OccupationHilbertContractions
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Occupation contractions and completed tensor Hilbert bases. -/
/-
Admission witness: D5.S3.Quantum.FermionicCorrelationalBound.OccupationHilbertContractions.sum_pair_energies.
orthonormal_countable: proof_shape: bind-only; escape_witness: none; consumer: CompletedTensorSlaterGeometry.exists_pair_preserving_tensor, PhysicalContractionRdmBridge.adaptedChart_nonempty, PhysicalContractionRdmBridge.canonicalPair_countable.
adapted_hilbert_basis: proof_shape: bind-only; escape_witness: none; consumer: CompletedTensorSlaterGeometry.exists_pair_preserving_tensor, PhysicalContractionRdmBridge.adaptedChart_nonempty.
tensorBasisVector_orthonormal: proof_shape: bind-only; escape_witness: none; consumer: OccupationHilbertContractions.tensorHilbertBasis, OccupationHilbertContractions.tensorHilbertBasis_apply.
tensorBasisVector_dense: proof_shape: content; escape_witness: OccupationHilbertContractions.tensorBasisVector_dense; consumer: OccupationHilbertContractions.tensorHilbertBasis, OccupationHilbertContractions.tensorHilbertBasis_apply.
tensorHilbertBasis_apply: proof_shape: bind-only; escape_witness: none; consumer: CanonicalRdmAndPadding.tensorCoordinateEmbedding_basis, CompletedTensorSlaterGeometry.tensorHead_adjoint, CompletedTensorSlaterGeometry.tensorHead_basis_coordinates, CompletedTensorSlaterGeometry.tensorHilbertBasis_repr_tmul, PhysicalContractionRdmBridge.sourceGamma_eq_gram, PhysicalContractionRdmBridge.sourceGram_tmul.
partialPull_sum: proof_shape: bind-only; escape_witness: none; consumer: OccupationHilbertContractions.partialPull, OccupationHilbertContractions.partialPull_norm.
partialPull_norm: proof_shape: bind-only; escape_witness: none; consumer: OccupationHilbertContractions.partialPullCLM.
countable_pair_sign: proof_shape: bind-only; escape_witness: none; consumer: CanonicalRdmAndPadding.pairContract_adjacent_swap, CompletedCorrelationalBound.finite_pair_coordinate.
pairInsert_injective: proof_shape: bind-only; escape_witness: none; consumer: OccupationHilbertContractions.pairContract.
pairPhase_norm: proof_shape: bind-only; escape_witness: none; consumer: OccupationHilbertContractions.pairContract.
pairContract_apply: proof_shape: bind-only; escape_witness: none; consumer: CanonicalRdmAndPadding.countableB_apply, CanonicalRdmAndPadding.pairContract_adjacent_swap, CompletedCorrelationalBound.finite_pair_sum_transport, OccupationHilbertContractions.ordered_pair_energy, PhysicalContractionRdmBridge.padded_pair_zero, PhysicalContractionRdmBridge.single_pair_composition.
mem_doublePairLabels: proof_shape: bind-only; escape_witness: none; consumer: OccupationHilbertContractions.countable_doublePair_count, OccupationHilbertContractions.sum_pair_energies.
countable_doublePair_count: proof_shape: bind-only; escape_witness: none; consumer: OccupationHilbertContractions.countable_doublePair_sector.
countable_doublePair_sector: proof_shape: bind-only; escape_witness: none; consumer: OccupationHilbertContractions.sum_pair_energies.
removeOrderedPair_card: proof_shape: bind-only; escape_witness: none; consumer: OccupationHilbertContractions.occupiedOrderedPairEquiv.
removeOrderedPair_insert: proof_shape: bind-only; escape_witness: none; consumer: OccupationHilbertContractions.occupiedOrderedPairEquiv.
countable_norm_sq: proof_shape: bind-only; escape_witness: none; consumer: CanonicalRdmAndPadding.countable_identity_2_4, CanonicalRdmAndPadding.countable_ordered_pair_trace, CanonicalRdmAndPadding.finite_ordered_pair_energies, OccupationHilbertContractions.ordered_pair_energy, OccupationHilbertContractions.sum_pair_energies.
countable_norm_sq_summable: proof_shape: bind-only; escape_witness: none; consumer: CanonicalRdmAndPadding.countable_ordered_pair_trace, CanonicalRdmAndPadding.finite_ordered_pair_energies, OccupationHilbertContractions.sum_pair_energies.
ordered_pair_energy: proof_shape: content; escape_witness: OccupationHilbertContractions.ordered_pair_energy; consumer: CanonicalRdmAndPadding.countable_ordered_pair_trace, CanonicalRdmAndPadding.finite_ordered_pair_energies, OccupationHilbertContractions.canonical_pair_energy.
canonical_pair_energy: proof_shape: content; escape_witness: OccupationHilbertContractions.ordered_pair_energy; consumer: OccupationHilbertContractions.sum_pair_energies.
sum_pair_energies: proof_shape: content; escape_witness: OccupationHilbertContractions.sum_pair_energies; consumer: CanonicalRdmAndPadding.contractionFamily.
coordinateSingleton_orthonormal: proof_shape: bind-only; escape_witness: none; consumer: CanonicalRdmAndPadding.tensorCoordinateEmbedding_basis, OccupationHilbertContractions.coordinateRename, OccupationHilbertContractions.coordinateRename_apply.
coordinateRename_apply: proof_shape: bind-only; escape_witness: none; consumer: OccupationHilbertContractions.coordinateRename_image, OccupationHilbertContractions.coordinateRename_outside.
coordinateRename_image: proof_shape: bind-only; escape_witness: none; consumer: CompletedCorrelationalBound.finiteEmbed_apply, CompletedTensorSlaterGeometry.coordinateEquiv, CompletedTensorSlaterGeometry.sourceTensorCoordinates_permutation, CompletedTensorSlaterGeometry.tensorPermutation_repr, CompletedTensorSlaterGeometry.tupleBasis_repr, PhysicalContractionRdmBridge.coordinateRename_star, PhysicalContractionRdmBridge.particleHead_coordinates, PhysicalContractionRdmBridge.particleHead_repr, PhysicalContractionRdmBridge.sourceSynthesis_transport.
coordinateRename_outside: proof_shape: bind-only; escape_witness: none; consumer: CompletedCorrelationalBound.finiteEmbed_outside, CompletedTensorSlaterGeometry.sourceTensorCoordinates_permutation, PhysicalContractionRdmBridge.coordinateRename_star, PhysicalContractionRdmBridge.particleCoordinates_outside, PhysicalContractionRdmBridge.particleHead_coordinates, PhysicalContractionRdmBridge.sourceSynthesis_transport.
weighted_schur: proof_shape: bind-only; escape_witness: none; consumer: CompletedCorrelationalBound.actual_sector_bound.
scalar_row_bound: proof_shape: bind-only; escape_witness: none; consumer: OccupationHilbertContractions.occupation_row_bound.
denominator_sum_bound: proof_shape: bind-only; escape_witness: none; consumer: OccupationHilbertContractions.occupation_row_bound.
occupation_row_bound: proof_shape: bind-only; escape_witness: none; consumer: OccupationHilbertContractions.pairKernel_row_bound.
comparisonWeight_pos: proof_shape: bind-only; escape_witness: none; consumer: OccupationHilbertContractions.comparisonVector_pos, OccupationHilbertContractions.comparison_move.
comparisonVector_pos: proof_shape: bind-only; escape_witness: none; consumer: CompletedCorrelationalBound.actual_row_le_pair_row, CompletedCorrelationalBound.actual_sector_bound, CompletedCorrelationalBound.actual_weighted_row_bound, OccupationHilbertContractions.comparison_move, OccupationHilbertContractions.pairKernel_weighted_row.
comparison_hop: proof_shape: bind-only; escape_witness: none; consumer: OccupationHilbertContractions.weighted_hop_bound.
comparison_move: proof_shape: bind-only; escape_witness: none; consumer: OccupationHilbertContractions.weighted_hop_bound.
erase_insert_condition: proof_shape: bind-only; escape_witness: none; consumer: OccupationHilbertContractions.pairIncidence_creation.
pairIncidence_creation: proof_shape: bind-only; escape_witness: none; consumer: OccupationHilbertContractions.pairIncidence_row.
pairIncidence_row: proof_shape: bind-only; escape_witness: none; consumer: OccupationHilbertContractions.pairKernel_row.
pairKernel_row: proof_shape: bind-only; escape_witness: none; consumer: CompletedCorrelationalBound.actual_row_le_pair_row, OccupationHilbertContractions.pairKernel_weighted_row.
weighted_hop_bound: proof_shape: bind-only; escape_witness: none; consumer: OccupationHilbertContractions.pairKernel_weighted_row.
pairKernel_weighted_row: proof_shape: bind-only; escape_witness: none; consumer: OccupationHilbertContractions.pairKernel_row_bound.
pairKernel_row_bound: proof_shape: bind-only; escape_witness: none; consumer: CompletedCorrelationalBound.actual_weighted_row_bound.
admission_basis: escape-witness
Direct frozen dependencies:
  D5/S3/Observer/HilbertGeometry/HilbertPathFundamentalTheorem.CountableBasisPort.countable_of_orthonormal, statement_id: sha256:a5521de8505973b16b4e7a49dfb8251827384f04271b790a46a1b18868a33143.
  D5/S3/Quantum/FockSpace/ForbiddenNeighbourDeterminant.occupationCount, statement_id: sha256:97804cfc85a668f345a5b3e2421ba02e5e6203f36590508faccac8726341bc0a.
  D5/S3/Weil/ProjectiveRayleigh/ScaledComplexQuadraticRowBound.norm_complex_quadratic_le_scaled_rows, statement_id: sha256:0546d1b31c5831f1ec46dc0ae54d7592aac449e3f961a4ea5c4b83a26803cd2a.
Information-escape registration is paused.
-/
import D5.S3.Quantum.FockSpace.ForbiddenNeighbourDeterminant
import D5.S3.Observer.HilbertGeometry.HilbertPathFundamentalTheorem
import D5.S3.Weil.ProjectiveRayleigh.ScaledComplexQuadraticRowBound
noncomputable section
open scoped Classical BigOperators TensorProduct ComplexConjugate Matrix
namespace D5.S3.Quantum.FermionicCorrelationalBound.OccupationHilbertContractions
open D5.S3.Quantum.FockSpace.ForbiddenNeighbourDeterminant
section
open scoped BigOperators Matrix ComplexConjugate
def lift {d N : ℕ} (ψ : (EuclideanSpace ℂ ({s : Fin d → Bool // occupationCount s = N}))) : (EuclideanSpace ℂ (Fin d → Bool)) :=
  WithLp.toLp 2 (fun s => if h : occupationCount s = N then ψ ⟨s,h⟩ else 0)
end
section
open scoped Classical
open TopologicalSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
/-- Orthonormal coordinates in a separable Hilbert space form a countable family. -/
theorem orthonormal_countable {ι : Type*} [SeparableSpace E] {v : ι → E}
    (hv : Orthonormal ℂ v) : Countable ι := by
  have hs : (Set.range v).Countable := by
    exact D5.S3.Observer.HilbertGeometry.HilbertPathFundamentalTheorem.CountableBasisPort.countable_of_orthonormal hv.toSubtypeRange
  letI : Countable (Set.range v) := hs.to_subtype
  exact Function.Injective.countable (f := Set.rangeFactorization v) (by
    intro i j h
    exact hv.linearIndependent.injective (congrArg Subtype.val h))
/-- An adapted Hilbert basis preserves every given canonical pair vector. -/
theorem adapted_hilbert_basis [CompleteSpace E] {ι : Type*} {v : ι → E}
    (hv : Orthonormal ℂ v) :
    ∃ (w : Set E) (b : HilbertBasis w ℂ E),Set.range v ⊆ w ∧ ⇑b=Subtype.val := by
  exact hv.toSubtypeRange.exists_hilbertBasis_extension
end
section
open scoped TensorProduct BigOperators Classical
open UniformSpace
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
def tensorBasisVector {ι κ : Type*} (b : HilbertBasis ι ℂ E) (c : HilbertBasis κ ℂ F)
    (p : ι × κ) : (UniformSpace.Completion (E ⊗[ℂ] F)) := (b p.1 ⊗ₜ[ℂ] c p.2 : E ⊗[ℂ] F)
private theorem tensorBasisVector_orthonormal {ι κ : Type*}
    (b : HilbertBasis ι ℂ E) (c : HilbertBasis κ ℂ F) :
    Orthonormal ℂ (tensorBasisVector b c) := by
  rw [orthonormal_iff_ite]
  intro p q
  simpa only [tensorBasisVector,Completion.inner_coe] using
    (orthonormal_iff_ite.mp (b.orthonormal.tmul c.orthonormal)) p q
private theorem tensorBasisVector_dense {ι κ : Type*}
    (b : HilbertBasis ι ℂ E) (c : HilbertBasis κ ℂ F) :
    (Submodule.span ℂ (Set.range (tensorBasisVector b c)))ᗮ = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro z hz
  have hbase : ∀ i j, inner ℂ z (tensorBasisVector b c (i,j)) = 0 := by
    intro i j
    exact (Submodule.mem_orthogonal' _ _).mp hz _ (Submodule.subset_span ⟨(i,j),rfl⟩)
  have hx : ∀ (x : E) (j : κ), inner ℂ z
      ((x ⊗ₜ[ℂ] c j : E ⊗[ℂ] F) : (UniformSpace.Completion (E ⊗[ℂ] F))) = 0 := by
    intro x j
    let T : E →L[ℂ] ℂ := (innerSL ℂ z).comp
      ((Completion.toComplL : E ⊗[ℂ] F →L[ℂ] (UniformSpace.Completion (E ⊗[ℂ] F))).comp
        ((TensorProduct.mkL ℂ E F).flip (c j)))
    have hs := T.hasSum (b.hasSum_repr x)
    have ht : (fun i => T (b.repr x i • b i)) = fun _ => (0:ℂ) := by
      funext i
      rw [map_smul]
      have hi : T (b i) = 0 := hbase i j
      rw [hi,smul_zero]
    rw [ht] at hs
    exact hs.unique hasSum_zero
  have hxy : ∀ (x : E) (y : F), inner ℂ z
      ((x ⊗ₜ[ℂ] y : E ⊗[ℂ] F) : (UniformSpace.Completion (E ⊗[ℂ] F))) = 0 := by
    intro x y
    let T : F →L[ℂ] ℂ := (innerSL ℂ z).comp
      ((Completion.toComplL : E ⊗[ℂ] F →L[ℂ] (UniformSpace.Completion (E ⊗[ℂ] F))).comp
        (TensorProduct.mkL ℂ E F x))
    have hs := T.hasSum (c.hasSum_repr y)
    have ht : (fun j => T (c.repr y j • c j)) = fun _ => (0:ℂ) := by
      funext j
      rw [map_smul]
      have hj : T (c j) = 0 := hx x j
      rw [hj,smul_zero]
    rw [ht] at hs
    exact hs.unique hasSum_zero
  have halg : ∀ t : E ⊗[ℂ] F, inner ℂ z (t : (UniformSpace.Completion (E ⊗[ℂ] F))) = 0 := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => change inner ℂ z ((0 : E ⊗[ℂ] F) : (UniformSpace.Completion (E ⊗[ℂ] F))) = 0
              rw [Completion.coe_zero,inner_zero_right]
    | tmul x y => exact hxy x y
    | add t u ht hu => simpa only [Completion.coe_add,inner_add_right,ht,hu,add_zero]
  have hall : ∀ t : (UniformSpace.Completion (E ⊗[ℂ] F)), inner ℂ z t = 0 := by
    intro t
    exact Completion.induction_on t (isClosed_eq (by fun_prop) continuous_const) halg
  have hz0 : z = 0 := inner_self_eq_zero.mp (hall z)
  exact hz0 ▸ Submodule.zero_mem _
/-- The countable product of Hilbert bases is a basis of the completed Hilbert tensor. -/
def tensorHilbertBasis {ι κ : Type*} (b : HilbertBasis ι ℂ E) (c : HilbertBasis κ ℂ F) :
    HilbertBasis (ι × κ) ℂ ((UniformSpace.Completion (E ⊗[ℂ] F))) :=
  HilbertBasis.mkOfOrthogonalEqBot (tensorBasisVector_orthonormal b c) (tensorBasisVector_dense b c)
theorem tensorHilbertBasis_apply {ι κ : Type*} (b : HilbertBasis ι ℂ E) (c : HilbertBasis κ ℂ F)
    (p : ι × κ) : tensorHilbertBasis b c p = tensorBasisVector b c p := by
  rw [tensorHilbertBasis,HilbertBasis.coe_mkOfOrthogonalEqBot]
end
section
open scoped BigOperators
/-- Coordinate annihilation of a single normalized ordered-wedge basis mode. -/
def annihilationCoordinate {N : ℕ} (ψ : (lp (fun _ : {s : Finset ℕ // s.card = N} => ℂ) 2)) (i : ℕ)
    (R : Finset ℕ) : ℂ :=
  if h : i ∉ R ∧ (insert i R).card = N then
    (-1 : ℂ)^((R.filter fun k => k < i).card) * ψ ⟨insert i R,h.2⟩
  else 0
/-- Ordered pair contraction; an adjacent canonical pair has positive sign. -/
def pairCoordinate {N : ℕ} (ψ : (lp (fun _ : {s : Finset ℕ // s.card = N} => ℂ) 2)) (i j : ℕ)
    (R : Finset ℕ) : ℂ :=
  if h : i ≠ j ∧ i ∉ R ∧ j ∉ R ∧ (insert i (insert j R)).card = N then
    (-1 : ℂ)^((R.filter fun k => k < j).card +
      ((insert j R).filter fun k => k < i).card) *
      ψ ⟨insert i (insert j R),h.2.2.2⟩
  else 0
/-- A canonical coefficient sequence is real, nonnegative and square-summable with unit mass. -/
structure CanonicalSequence where
  coeff : ℕ → ℝ
  nonneg : ∀ i, 0 ≤ coeff i
  summable_sq : Summable fun i => coeff i^2
  mass : (∑' i, coeff i^2) = 1
/-- Canonical RDM expectation as the contraction quadratic form. -/
def canonicalRayleigh {N : ℕ} (c : CanonicalSequence) (ψ : (lp (fun _ : {s : Finset ℕ // s.card = N} => ℂ) 2)) : ℝ :=
  2 * ∑' R : ({s : Finset ℕ // s.card = (N-2)}),
    ‖∑' i, (c.coeff i : ℂ) * pairCoordinate ψ (2*i) (2*i+1) R.val‖^2
/-- CHR-3 in countable canonical occupation coordinates, with arbitrary spectator occupancy. -/
def coordinateClaim : Prop := ∀ (m : ℕ), 1 ≤ m →
  ∀ (c : CanonicalSequence) (α : ℝ),
  (∀ i, c.coeff i^2 ≤ α) → 2*(m : ℝ)*α ≤ 1 →
  ∀ ψ : (lp (fun _ : {s : Finset ℕ // s.card = (2*m)} => ℂ) 2), ‖ψ‖ = 1 →
    canonicalRayleigh c ψ ≤ (2*(m : ℝ)) *
      (1-((m : ℝ)-1)*(∑' i, c.coeff i^4) + (5/8 : ℝ)*(2*(m : ℝ)*α)^2)
end
section
open scoped BigOperators Classical
variable {A B : Type*}
def partialPullRaw (P : B → Prop) (f : {b // P b} → A)
    (phase : B → ℂ) (ψ : lp (fun _ : A => ℂ) 2) (b : B) : ℂ :=
  if h : P b then phase b * ψ (f ⟨b,h⟩) else 0
private theorem partialPull_sum (P : B → Prop) (f : {b // P b} → A)
    (hf : Function.Injective f) (phase : B → ℂ) (hphase : ∀ b, ‖phase b‖ ≤ 1)
    (ψ : lp (fun _ : A => ℂ) 2) (s : Finset B) :
    ∑ b ∈ s, ‖partialPullRaw P f phase ψ b‖^2 ≤ ‖ψ‖^2 := by
  let g (b : B) := ‖partialPullRaw P f phase ψ b‖^2
  have hs : (∑ b ∈ s,g b) = ∑ q ∈ s.subtype P,g q.val := by
    rw [Finset.sum_subtype_eq_sum_filter,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro b _
    by_cases hb : P b
    · simp [hb]
    · simp [g,partialPullRaw,hb]
  rw [hs]
  calc
    _ ≤ ∑ q ∈ s.subtype P, ‖ψ (f q)‖^2 := by
      apply Finset.sum_le_sum
      intro q _
      have hn : ‖partialPullRaw P f phase ψ q.val‖ ≤ ‖ψ (f q)‖ := by
        simp only [partialPullRaw,dif_pos q.property,norm_mul]
        exact mul_le_of_le_one_left (norm_nonneg (ψ (f q))) (hphase q.val)
      exact pow_le_pow_left₀ (norm_nonneg _) hn 2
    _ = ∑ a ∈ (s.subtype P).image f, ‖ψ a‖^2 := by
      rw [Finset.sum_image]
      exact fun _ _ _ _ h => hf h
    _ ≤ ‖ψ‖^2 := by
      simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
        lp.sum_rpow_le_norm_rpow (p := 2) (by norm_num) ψ ((s.subtype P).image f)
def partialPull (P : B → Prop) (f : {b // P b} → A)
    (hf : Function.Injective f) (phase : B → ℂ) (hphase : ∀ b, ‖phase b‖ ≤ 1)
    (ψ : lp (fun _ : A => ℂ) 2) : lp (fun _ : B => ℂ) 2 :=
  ⟨partialPullRaw P f phase ψ,memℓp_gen' (C := ‖ψ‖^2) (by
    intro s
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using partialPull_sum P f hf phase hphase ψ s)⟩
private theorem partialPull_norm (P : B → Prop) (f : {b // P b} → A)
    (hf : Function.Injective f) (phase : B → ℂ) (hphase : ∀ b, ‖phase b‖ ≤ 1)
    (ψ : lp (fun _ : A => ℂ) 2) : ‖partialPull P f hf phase hphase ψ‖ ≤ ‖ψ‖ := by
  apply lp.norm_le_of_forall_sum_le (by norm_num) (norm_nonneg ψ)
  intro s
  simpa only [partialPull,ENNReal.toReal_ofNat,Real.rpow_two] using
    partialPull_sum P f hf phase hphase ψ s
def partialPullLinear (P : B → Prop) (f : {b // P b} → A)
    (hf : Function.Injective f) (phase : B → ℂ) (hphase : ∀ b, ‖phase b‖ ≤ 1) :
    lp (fun _ : A => ℂ) 2 →ₗ[ℂ] lp (fun _ : B => ℂ) 2 where
  toFun := partialPull P f hf phase hphase
  map_add' ψ χ := by
    ext b
    change partialPullRaw P f phase (ψ+χ) b = partialPullRaw P f phase ψ b + partialPullRaw P f phase χ b
    by_cases hb : P b <;> simp [partialPullRaw,hb,mul_add,lp.coeFn_add,PreLp.add_apply]
  map_smul' a ψ := by
    ext b
    by_cases hb : P b <;> simp [partialPull,partialPullRaw,hb,mul_left_comm,Pi.smul_apply]
def partialPullCLM (P : B → Prop) (f : {b // P b} → A)
    (hf : Function.Injective f) (phase : B → ℂ) (hphase : ∀ b, ‖phase b‖ ≤ 1) :
    lp (fun _ : A => ℂ) 2 →L[ℂ] lp (fun _ : B => ℂ) 2 :=
  (partialPullLinear P f hf phase hphase).mkContinuous 1 (by
    intro ψ
    simpa [partialPullLinear] using partialPull_norm P f hf phase hphase ψ)
end
section
open scoped BigOperators
/-- A complete canonical adjacent pair has a positive annihilation sign. -/
theorem countable_pair_sign {N : ℕ} (ψ : (lp (fun _ : {s : Finset ℕ // s.card = N} => ℂ) 2)) (i : ℕ) (R : Finset ℕ)
    (hi : 2*i ∉ R) (hj : 2*i+1 ∉ R)
    (hN : (insert (2*i) (insert (2*i+1) R)).card = N) :
    pairCoordinate ψ (2*i) (2*i+1) R = ψ ⟨insert (2*i) (insert (2*i+1) R),hN⟩ := by
  classical
  have hne : 2*i ≠ 2*i+1 := by omega
  have hfilter : R.filter (fun k => k < 2*i+1) = R.filter (fun k => k < 2*i) := by
    ext k
    simp only [Finset.mem_filter]
    constructor
    · intro ⟨hk,hlt⟩
      have hki : k ≠ 2*i := by intro h; subst k; exact hi hk
      exact ⟨hk,by omega⟩
    · intro ⟨hk,hlt⟩
      exact ⟨hk,by omega⟩
  have hinsert : (insert (2*i+1) R).filter (fun k => k < 2*i) =
      R.filter (fun k => k < 2*i) := by
    rw [Finset.filter_insert]
    simp
  have hcond : 2*i ≠ 2*i+1 ∧ 2*i ∉ R ∧ 2*i+1 ∉ R ∧
      (insert (2*i) (insert (2*i+1) R)).card = N := ⟨hne,hi,hj,hN⟩
  simp only [pairCoordinate, dif_pos hcond, hinsert, hfilter]
  rw [← two_mul, pow_mul]
  norm_num
end
section
open scoped BigOperators Classical
def pairValid (N i j : ℕ) (R : ({s : Finset ℕ // s.card = (N-2)})) : Prop :=
  i ≠ j ∧ i ∉ R.val ∧ j ∉ R.val ∧ (insert i (insert j R.val)).card = N
def pairInsert (N i j : ℕ) (R : {R : ({s : Finset ℕ // s.card = (N-2)}) // pairValid N i j R}) :
    ({s : Finset ℕ // s.card = N}) := ⟨insert i (insert j R.val.val),R.property.2.2.2⟩
private theorem pairInsert_injective (N i j : ℕ) : Function.Injective (pairInsert N i j) := by
  intro R T h
  have he := congrArg (fun S : ({s : Finset ℕ // s.card = N}) => (S.val.erase i).erase j) h
  have hir : i ∉ insert j R.val.val := by
    simp only [Finset.mem_insert,not_or]
    exact ⟨R.property.1,R.property.2.1⟩
  have hit : i ∉ insert j T.val.val := by
    simp only [Finset.mem_insert,not_or]
    exact ⟨T.property.1,T.property.2.1⟩
  simp only [pairInsert,Finset.erase_insert hir,Finset.erase_insert hit,
    Finset.erase_insert R.property.2.2.1,Finset.erase_insert T.property.2.2.1] at he
  exact Subtype.ext (Subtype.ext he)
def pairPhase (i j : ℕ) (R : ({s : Finset ℕ // s.card = (N-2)})) : ℂ :=
  (-1:ℂ)^((R.val.filter fun k => k < j).card + ((insert j R.val).filter fun k => k < i).card)
private theorem pairPhase_norm (N i j : ℕ) (R : ({s : Finset ℕ // s.card = (N-2)})) : ‖pairPhase (N := N) i j R‖ ≤ 1 := by
  simp [pairPhase,norm_pow]
/-- Every ordered contraction is an actual bounded linear operator, without an abstract CAR axiom. -/
def pairContract (N i j : ℕ) : (lp (fun _ : {s : Finset ℕ // s.card = N} => ℂ) 2) →L[ℂ] (lp (fun _ : {s : Finset ℕ // s.card = (N-2)} => ℂ) 2) :=
  partialPullCLM (pairValid N i j) (pairInsert N i j) (pairInsert_injective N i j)
    (pairPhase (N := N) i j) (pairPhase_norm N i j)
theorem pairContract_apply (N i j : ℕ) (ψ : (lp (fun _ : {s : Finset ℕ // s.card = N} => ℂ) 2)) (R : ({s : Finset ℕ // s.card = (N-2)})) :
    pairContract N i j ψ R = pairCoordinate ψ i j R.val := by
  change partialPullRaw (pairValid N i j) (pairInsert N i j)
    (pairPhase (N := N) i j) ψ R = pairCoordinate ψ i j R.val
  unfold partialPullRaw pairValid pairCoordinate
  by_cases h : i ≠ j ∧ i ∉ R.val ∧ j ∉ R.val ∧ (insert i (insert j R.val)).card=N
  · rw [dif_pos h,dif_pos h]
    rfl
  · rw [dif_neg h,dif_neg h]
end
section
open scoped BigOperators Classical
private def doublePairLabels (S : Finset ℕ) : Finset ℕ :=
  (S.image fun k => k/2).filter fun i => 2*i ∈ S ∧ 2*i+1 ∈ S
private theorem mem_doublePairLabels (S : Finset ℕ) (i : ℕ) :
    i ∈ doublePairLabels S ↔ 2*i ∈ S ∧ 2*i+1 ∈ S := by
  simp only [doublePairLabels,Finset.mem_filter]
  constructor
  · exact And.right
  · intro h
    refine ⟨Finset.mem_image.mpr ⟨2*i,h.1,?_⟩,h⟩
    omega
/-- At most N/2 disjoint canonical pairs can be occupied in an N-set. -/
private theorem countable_doublePair_count (S : Finset ℕ) : 2*(doublePairLabels S).card ≤ S.card := by
  let U := (doublePairLabels S).image (fun i => 2*i)
  let V := (doublePairLabels S).image (fun i => 2*i+1)
  have hu : U ⊆ S := by
    rintro k hk
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hk
    exact ((mem_doublePairLabels S i).mp hi).1
  have hv : V ⊆ S := by
    rintro k hk
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hk
    exact ((mem_doublePairLabels S i).mp hi).2
  have hd : Disjoint U V := by
    apply Finset.disjoint_left.mpr
    intro k hku hkv
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hku
    obtain ⟨j,_,hj⟩ := Finset.mem_image.mp hkv
    omega
  have huinj : Function.Injective (fun i : ℕ => 2*i) := by intro i j h; change 2*i=2*j at h; omega
  have hvinj : Function.Injective (fun i : ℕ => 2*i+1) := by intro i j h; change 2*i+1=2*j+1 at h; omega
  have hcu : U.card=(doublePairLabels S).card := Finset.card_image_of_injective _ huinj
  have hcv : V.card=(doublePairLabels S).card := Finset.card_image_of_injective _ hvinj
  have h := Finset.card_le_card (Finset.union_subset hu hv)
  rw [Finset.card_union_of_disjoint hd,hcu,hcv] at h
  omega
private theorem countable_doublePair_sector (m : ℕ) (S : ({s : Finset ℕ // s.card = (2*m)})) :
    (doublePairLabels S.val).card ≤ m := by
  have h := countable_doublePair_count S.val
  rw [S.property] at h
  omega
private def removeOrderedPair (S : Finset ℕ) (i j : ℕ) := (S.erase i).erase j
private theorem removeOrderedPair_card (S : Finset ℕ) (i j : ℕ) (hij : i≠j)
    (hi : i∈S) (hj : j∈S) : (removeOrderedPair S i j).card=S.card-2 := by
  have hj' : j ∈ S.erase i := Finset.mem_erase.mpr ⟨hij.symm,hj⟩
  rw [removeOrderedPair,Finset.card_erase_of_mem hj',Finset.card_erase_of_mem hi]
  omega
private theorem removeOrderedPair_insert (S : Finset ℕ) (i j : ℕ) (hi : i∈S) (hj : j∈S) :
    insert i (insert j (removeOrderedPair S i j))=S := by
  ext k
  simp only [removeOrderedPair,Finset.mem_insert,Finset.mem_erase]
  constructor
  · rintro (h|h|⟨_,_,hk⟩)
    · simpa [h] using hi
    · simpa [h] using hj
    · exact hk
  · intro hk
    by_cases hki : k=i
    · exact Or.inl hki
    · by_cases hkj : k=j
      · exact Or.inr (Or.inl hkj)
      · exact Or.inr (Or.inr ⟨hkj,hki,hk⟩)
def occupiedOrderedPairEquiv (N i j : ℕ) (hij : i≠j) :
    {R : ({s : Finset ℕ // s.card = (N-2)}) // pairValid N i j R} ≃
      {S : ({s : Finset ℕ // s.card = N}) // i∈S.val ∧ j∈S.val} where
  toFun R := ⟨pairInsert N i j R,by simp [pairInsert]⟩
  invFun S := ⟨⟨removeOrderedPair S.val.val i j,
    (removeOrderedPair_card S.val.val i j hij S.property.1 S.property.2).trans
      (congrArg (fun n : ℕ => n-2) S.val.property)⟩,by
    refine ⟨hij,?_,?_,?_⟩
    · simp [removeOrderedPair]
    · simp [removeOrderedPair]
    · rw [removeOrderedPair_insert _ _ _ S.property.1 S.property.2]
      exact S.val.property⟩
  left_inv R := by
    apply Subtype.ext
    apply Subtype.ext
    change removeOrderedPair (insert i (insert j R.val.val)) i j=R.val.val
    unfold removeOrderedPair
    rw [Finset.erase_insert (by simp [R.property.1,R.property.2.1]),
      Finset.erase_insert R.property.2.2.1]
  right_inv S := by
    apply Subtype.ext
    apply Subtype.ext
    exact removeOrderedPair_insert S.val.val i j S.property.1 S.property.2
end
section
open scoped BigOperators Classical ENNReal
set_option backward.isDefEq.respectTransparency false
theorem countable_norm_sq {A : Type*} (ψ : lp (fun _ : A => ℂ) 2) :
    ‖ψ‖^2 = ∑' a, ‖ψ a‖^2 := by
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
    lp.norm_rpow_eq_tsum (p := 2) (by norm_num) ψ
theorem countable_norm_sq_summable {A : Type*} (ψ : lp (fun _ : A => ℂ) 2) :
    Summable fun a => ‖ψ a‖^2 := by
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
    (lp.memℓp ψ).summable (by norm_num : 0 < (2:ℝ≥0∞).toReal)
/-- Arbitrary ordered-mode contraction energy counts its occupied configurations. -/
theorem ordered_pair_energy (N i j : ℕ) (ψ : (lp (fun _ : {s : Finset ℕ // s.card = N} => ℂ) 2)) :
    ‖pairContract N i j ψ‖^2 =
      ∑' S : ({s : Finset ℕ // s.card = N}),if i≠j ∧ i∈S.val ∧ j∈S.val then ‖ψ S‖^2 else 0 := by
  by_cases hij : i=j
  · subst j
    have hz : pairContract N i i ψ=0 := by
      ext R
      rw [pairContract_apply]
      simp [pairCoordinate]
    simp [hz]
  · have hsupp : Function.support (fun R : ({s : Finset ℕ // s.card = (N-2)}) =>
        ‖pairContract N i j ψ R‖^2) ⊆ {R | pairValid N i j R} := by
      intro R hR
      by_contra hp
      apply hR
      have hp' : ¬(i≠j ∧ i∉R.val ∧ j∉R.val ∧ (insert i (insert j R.val)).card=N) := hp
      have hz : pairCoordinate ψ i j R.val=0 := by
        unfold pairCoordinate
        rw [dif_neg hp']
      simp only [pairContract_apply,hz,norm_zero,zero_pow (by decide : 2≠0)]
    calc
      _ = ∑' R : ({s : Finset ℕ // s.card = (N-2)}),‖pairContract N i j ψ R‖^2 := countable_norm_sq _
      _ = ∑' R : {R : ({s : Finset ℕ // s.card = (N-2)}) // pairValid N i j R},
          ‖pairContract N i j ψ R.val‖^2 := (tsum_subtype_eq_of_support_subset hsupp).symm
      _ = ∑' R : {R : ({s : Finset ℕ // s.card = (N-2)}) // pairValid N i j R},
          ‖ψ (pairInsert N i j R)‖^2 := by
        apply tsum_congr
        intro R
        rw [pairContract_apply]
        unfold pairCoordinate
        have hcond : i≠j ∧ i∉R.val.val ∧ j∉R.val.val ∧
          (insert i (insert j R.val.val)).card=N := R.property
        rw [dif_pos hcond,norm_mul]
        simp only [norm_pow,norm_neg,norm_one,one_pow,one_mul]
        rfl
      _ = ∑' S : {S : ({s : Finset ℕ // s.card = N}) // i∈S.val ∧ j∈S.val},‖ψ S.val‖^2 :=
        (occupiedOrderedPairEquiv N i j hij).tsum_eq (fun S => ‖ψ S.val‖^2)
      _ = ∑' S : ({s : Finset ℕ // s.card = N}),if i∈S.val ∧ j∈S.val then ‖ψ S‖^2 else 0 := by
        change (∑' S : ↑({S : ({s : Finset ℕ // s.card = N}) | i∈S.val ∧ j∈S.val} : Set _),‖ψ S.val‖^2) = _
        simpa only [Set.indicator_apply,Set.mem_setOf_eq] using
          tsum_subtype {S : ({s : Finset ℕ // s.card = N}) | i∈S.val ∧ j∈S.val} (fun S => ‖ψ S‖^2)
      _ = _ := by
        apply tsum_congr
        intro S
        by_cases h : i∈S.val ∧ j∈S.val
        · rw [if_pos h,if_pos ⟨hij,h.1,h.2⟩]
        · have hh : ¬(i≠j ∧ i∈S.val ∧ j∈S.val) := fun hp => h hp.2
          rw [if_neg h,if_neg hh]
/-- The norm of a canonical pair contraction counts exactly the configurations containing it. -/
private theorem canonical_pair_energy (N i : ℕ) (ψ : (lp (fun _ : {s : Finset ℕ // s.card = N} => ℂ) 2)) :
    ‖pairContract N (2*i) (2*i+1) ψ‖^2 =
      ∑' S : ({s : Finset ℕ // s.card = N}), if 2*i ∈ S.val ∧ 2*i+1 ∈ S.val then ‖ψ S‖^2 else 0 := by
  have hij : 2*i ≠ 2*i+1 := by omega
  rw [ordered_pair_energy]
  apply tsum_congr
  intro S
  by_cases h : 2*i ∈ S.val ∧ 2*i+1 ∈ S.val
  · rw [if_pos h, if_pos ⟨hij,h.1,h.2⟩]
  · have hn : ¬(2*i ≠ 2*i+1 ∧ 2*i ∈ S.val ∧ 2*i+1 ∈ S.val) := fun hp => h hp.2
    rw [if_neg h, if_neg hn]
/-- Every finite family of occupied pair energies is bounded by the particle number divided by two. -/
theorem sum_pair_energies (m : ℕ) (ψ : (lp (fun _ : {s : Finset ℕ // s.card = (2*m)} => ℂ) 2)) (t : Finset ℕ) :
    (∑ i ∈ t, ‖pairContract (2*m) (2*i) (2*i+1) ψ‖^2) ≤ (m:ℝ)*‖ψ‖^2 := by
  let g (S : ({s : Finset ℕ // s.card = (2*m)})) := ‖ψ S‖^2
  let h (i : ℕ) (S : ({s : Finset ℕ // s.card = (2*m)})) :=
    if 2*i ∈ S.val ∧ 2*i+1 ∈ S.val then g S else 0
  have hg : Summable g := countable_norm_sq_summable ψ
  have hh (i : ℕ) : Summable (h i) := by
    apply Summable.of_nonneg_of_le _ _ hg
    · intro S; dsimp [h]; split_ifs <;> positivity
    · intro S; dsimp [h]; split_ifs <;> simp [g]
  have hb (S : ({s : Finset ℕ // s.card = (2*m)})) : (∑ i ∈ t,h i S) ≤ (m:ℝ)*g S := by
    have hc : (t.filter (fun i => 2*i ∈ S.val ∧ 2*i+1 ∈ S.val)).card ≤ m := by
      apply le_trans (Finset.card_le_card (show t.filter (fun i => 2*i ∈ S.val ∧ 2*i+1 ∈ S.val) ⊆ doublePairLabels S.val from ?_))
        (countable_doublePair_sector m S)
      intro i hi
      exact (mem_doublePairLabels S.val i).mpr (Finset.mem_filter.mp hi).2
    have he : (∑ i ∈ t,h i S) =
        ((t.filter (fun i => 2*i ∈ S.val ∧ 2*i+1 ∈ S.val)).card:ℝ)*g S := by
      simp only [h,← Finset.sum_filter]
      simp
    rw [he]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (sq_nonneg _)
  simp_rw [canonical_pair_energy]
  change (∑ i ∈ t,∑' S,h i S) ≤ _
  rw [← Summable.tsum_finsetSum (fun i _ => hh i)]
  calc
    _ ≤ ∑' S,(m:ℝ)*g S := by
      apply Summable.tsum_le_tsum hb
      · exact Summable.of_nonneg_of_le (fun S => Finset.sum_nonneg fun i _ => by
          dsimp [h]; split_ifs <;> positivity) hb (hg.mul_left (m:ℝ))
      · exact hg.mul_left (m:ℝ)
    _ = _ := by rw [tsum_mul_left,← countable_norm_sq ψ]
end
section
open scoped BigOperators Classical
set_option backward.isDefEq.respectTransparency false
variable {A B : Type*}
private theorem coordinateSingleton_orthonormal (e : A ↪ B) :
    Orthonormal ℂ (fun a => (lp.single 2 (e a) (1:ℂ) : lp (fun _ : B => ℂ) 2)) := by
  rw [orthonormal_iff_ite]
  intro a b
  rw [lp.inner_single_left]
  simp [lp.single_apply,Pi.single_apply,RCLike.inner_apply,e.injective.eq_iff]
def coordinateRename (e : A ↪ B) : lp (fun _ : A => ℂ) 2 →ₗᵢ[ℂ] lp (fun _ : B => ℂ) 2 :=
  (coordinateSingleton_orthonormal e).orthogonalFamily.linearIsometry
private theorem coordinateRename_apply (e : A ↪ B) (ψ : lp (fun _ : A => ℂ) 2) (b : B) :
    coordinateRename e ψ b = ∑' a,if b=e a then ψ a else 0 := by
  let ev := lp.evalCLM (fun _ : B => ℂ) 2 (𝕜 := ℂ) b
  change ev ((coordinateSingleton_orthonormal e).orthogonalFamily.linearIsometry ψ)= _
  rw [OrthogonalFamily.linearIsometry_apply,ev.map_tsum
    ((coordinateSingleton_orthonormal e).orthogonalFamily.summable_of_lp ψ)]
  apply tsum_congr
  intro a
  simp only [LinearIsometry.toSpanSingleton_apply,map_smul]
  change ψ a * ((lp.single 2 (e a) (1:ℂ) : lp (fun _ : B => ℂ) 2) b) = _
  simp only [lp.single_apply,Pi.single_apply]
  split_ifs <;> simp
theorem coordinateRename_image (e : A ↪ B) (ψ : lp (fun _ : A => ℂ) 2) (a : A) :
    coordinateRename e ψ (e a)=ψ a := by
  rw [coordinateRename_apply]
  simp [e.injective.eq_iff,eq_comm]
theorem coordinateRename_outside (e : A ↪ B) (ψ : lp (fun _ : A => ℂ) 2) (b : B)
    (hb : b ∉ Set.range e) : coordinateRename e ψ b=0 := by
  rw [coordinateRename_apply]
  have hz : (fun a : A => if b=e a then ψ a else 0) = fun _ => (0:ℂ) := by
    funext a
    have ha : b≠e a := by intro ha; exact hb ⟨a,ha.symm⟩
    rw [if_neg ha]
  rw [hz,tsum_zero]
end
section
open scoped BigOperators ComplexConjugate Matrix
/-- Finite complex quadratic-form weighted Schur upper bound. -/
theorem weighted_schur {ι : Type*} [Fintype ι] (K : ι → ι → ℝ)
    (hK : ∀ i j, 0 ≤ K i j) (hsym : ∀ i j, K i j = K j i)
    (f : ι → ℝ) (hf : ∀ i, 0 < f i) (z : ι → ℂ) :
    (∑ i, ∑ j, (K i j : ℂ) * star (z i) * z j).re ≤
      ∑ i, ‖z i‖^2 * ((∑ j, K i j * f j) / f i) := by
  have hn (i j : ι) : ‖(K i j : ℂ)‖ = K i j := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hK i j)]
  have h := D5.S3.Weil.ProjectiveRayleigh.ScaledComplexQuadraticRowBound.norm_complex_quadratic_le_scaled_rows
    (fun i => star (z i)) (fun i j => (K i j : ℂ))
    (fun i => (∑ j, K i j * f j) / f i) f 1 hf
    (by intro i j; simp only [hn,hsym i j])
    (by intro i; simp only [hn,one_mul]; rw [div_mul_cancel₀ _ (ne_of_gt (hf i))])
  have he : (∑ i, ∑ j, (star (z i) * conj (star (z j))) * (K i j : ℂ)) =
      ∑ i, ∑ j, (K i j : ℂ) * star (z i) * z j := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp only [starRingEnd_apply,star_star]
    ring
  rw [he] at h
  simpa only [one_mul,norm_star,mul_comm] using (Complex.re_le_norm _).trans h
/-- The scalar row estimate after the configuration-dependent cancellation. -/
private theorem scalar_row_bound (m a α A P Q s₂ : ℝ)
    (hm : 0 ≤ m) (ha : 0 ≤ a) (ham : a ≤ m)
    (hsmall : a*α ≤ 1/2) (hA : A ≤ 1) (hP : 0 ≤ P)
    (hPu : P ≤ m*α) (hQu : Q ≤ m*α^2)
    (hAu : A ≤ 1-a*s₂+a^2*α^2) :
    m*A+a*(A-1)*P-a*P^2+a*(m+a*P)*Q ≤
      m-m*a*s₂+(5/2)*m^3*α^2 := by
  have hneg : a*(A-1)*P ≤ 0 := by
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos ha (by linarith)) hP
  have hsquare : 0 ≤ a*P^2 := mul_nonneg ha (sq_nonneg _)
  have hcoef : 0 ≤ a*(m+a*P) := mul_nonneg ha (add_nonneg hm (mul_nonneg ha hP))
  have hqbound := mul_le_mul_of_nonneg_left hQu hcoef
  have hpbound := mul_le_mul_of_nonneg_left hPu ha
  have hasmall := mul_le_mul_of_nonneg_left hsmall hm
  have hmain := mul_le_mul_of_nonneg_left hAu hm
  have hterm : a*(m+a*P)*(m*α^2) ≤ (3/2)*m^3*α^2 := by
    have hmp : m+a*P ≤ (3/2)*m := by nlinarith
    have h1 := mul_le_mul_of_nonneg_left hmp ha
    have h2 := mul_le_mul_of_nonneg_right ham (mul_nonneg (by norm_num : (0:ℝ) ≤ 3/2) hm)
    have h3 := mul_le_mul_of_nonneg_right (le_trans h1 h2) (mul_nonneg hm (sq_nonneg α))
    nlinarith
  have ha2 : a^2 ≤ m^2 := by nlinarith
  have hrest := mul_le_mul_of_nonneg_left ha2 (mul_nonneg hm (sq_nonneg α))
  nlinarith
/-- Denominator expansion keeps the fourth-power correction without renormalizing truncations. -/
theorem denominator_sum_bound {ι : Type*} [Fintype ι] (p : ι → ℝ)
    (a α : ℝ) (ha : 0 ≤ a) (hα : 0 ≤ α)
    (hp : ∀ i, 0 ≤ p i) (hpa : ∀ i, p i ≤ α)
    (hsum : (∑ i, p i) ≤ 1) :
    (∑ i, p i / (1+a*p i)) ≤ 1-a*(∑ i, p i^2)+a^2*α^2 := by
  have hden (i : ι) : 0 < 1+a*p i := by nlinarith [mul_nonneg ha (hp i)]
  have hexp (i : ι) : p i / (1+a*p i) =
      p i-a*p i^2+a^2*(p i^3/(1+a*p i)) := by
    linear_combination (p i-a*p i^2) * (mul_inv_cancel₀ (ne_of_gt (hden i)))
  have hcubic (i : ι) : p i^3/(1+a*p i) ≤ α^2*p i := by
    have h1 : p i^3/(1+a*p i) ≤ p i^3 :=
      div_le_self (pow_nonneg (hp i) _) (by nlinarith [mul_nonneg ha (hp i)])
    have h2 : p i^2 ≤ α^2 := by nlinarith [hp i, hpa i]
    have h3 := mul_le_mul_of_nonneg_right h2 (hp i)
    nlinarith
  have htail : (∑ i, p i^3/(1+a*p i)) ≤ α^2 := by
    calc
      _ ≤ ∑ i, α^2*p i := Finset.sum_le_sum fun i _ => hcubic i
      _ = α^2*(∑ i, p i) := by rw [Finset.mul_sum]
      _ ≤ α^2 := by nlinarith [mul_le_mul_of_nonneg_left hsum (sq_nonneg α)]
  have htail2 := mul_le_mul_of_nonneg_left htail (sq_nonneg a)
  simp_rw [hexp]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum]
  linarith
/-- Pair-sector scalar row bound for an arbitrary occupied subset. -/
private theorem occupation_row_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℝ) (m : ℕ) (hm : 1 ≤ m) (α : ℝ) (hα : 0 ≤ α)
    (hp : ∀ i, 0 ≤ p i) (hpa : ∀ i, p i ≤ α)
    (hsum : (∑ i, p i) ≤ 1) (hsmall : 2*(m : ℝ)*α ≤ 1)
    (D : Finset ι) (hD : D.card ≤ m) :
    (∑ i ∈ D, p i) + ((m : ℝ)+((m : ℝ)-1)*(∑ i ∈ D, p i)) *
      ((∑ i, p i/(1+((m : ℝ)-1)*p i)) -
       (∑ i ∈ D, p i/(1+((m : ℝ)-1)*p i))) ≤
      (m : ℝ)-(m : ℝ)*((m : ℝ)-1)*(∑ i, p i^2)+(5/2)*(m : ℝ)^3*α^2 := by
  let a : ℝ := (m : ℝ)-1
  let A : ℝ := ∑ i, p i/(1+a*p i)
  let P : ℝ := ∑ i ∈ D, p i
  let Q : ℝ := ∑ i ∈ D, p i^2/(1+a*p i)
  let U : ℝ := ∑ i ∈ D, p i/(1+a*p i)
  have ha : 0 ≤ a := by dsimp [a]; exact sub_nonneg.mpr (by exact_mod_cast hm)
  have ham : a ≤ (m : ℝ) := by dsimp [a]; linarith
  have hmm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hden (i : ι) : 0 < 1+a*p i := by nlinarith [mul_nonneg ha (hp i)]
  have hfrac (i : ι) : p i/(1+a*p i) ≤ p i :=
    div_le_self (hp i) (by nlinarith [mul_nonneg ha (hp i)])
  have hA : A ≤ 1 := le_trans (Finset.sum_le_sum fun i _ => hfrac i) hsum
  have hAu := denominator_sum_bound p a α ha hα hp hpa hsum
  have hP : 0 ≤ P := Finset.sum_nonneg fun i _ => hp i
  have hPu : P ≤ (m : ℝ)*α := by
    calc
      _ ≤ ∑ _i ∈ D, α := Finset.sum_le_sum fun i _ => hpa i
      _ = (D.card : ℝ)*α := by simp
      _ ≤ (m : ℝ)*α := mul_le_mul_of_nonneg_right (by exact_mod_cast hD) hα
  have hQu : Q ≤ (m : ℝ)*α^2 := by
    calc
      _ ≤ ∑ _i ∈ D, α^2 := Finset.sum_le_sum fun i _ => by
        have hsq : p i^2 ≤ α^2 := by nlinarith [hp i, hpa i]
        exact le_trans (div_le_self (sq_nonneg _) (by nlinarith [mul_nonneg ha (hp i)])) hsq
      _ = (D.card : ℝ)*α^2 := by simp
      _ ≤ (m : ℝ)*α^2 := mul_le_mul_of_nonneg_right (by exact_mod_cast hD) (sq_nonneg α)
  have hU : U = P-a*Q := by
    dsimp [U,P,Q]
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    linear_combination p i * (mul_inv_cancel₀ (ne_of_gt (hden i)))
  have hsa : a*α ≤ 1/2 := by
    have h := mul_le_mul_of_nonneg_right ham hα
    nlinarith
  have h := scalar_row_bound (m : ℝ) a α A P Q (∑ i, p i^2)
    hmm ha ham hsa hA hP hPu hQu hAu
  change P+((m : ℝ)+a*P)*(A-U) ≤ _
  rw [hU]
  calc
    _ = (m : ℝ)*A+a*(A-1)*P-a*P^2+a*((m : ℝ)+a*P)*Q := by
      dsimp [a]; ring
    _ ≤ _ := h
end
section
open scoped BigOperators
/-- Zero coefficients are inert and get weight one to keep the comparison vector positive. -/
def comparisonWeight (a p : ℝ) : ℝ := if p=0 then 1 else Real.sqrt p/(1+a*p)
def comparisonVector {ι : Type*} (a : ℝ) (p : ι → ℝ) (D : Finset ι) : ℝ :=
  ∏ i ∈ D, comparisonWeight a (p i)
private theorem comparisonWeight_pos (a p : ℝ) (ha : 0 ≤ a) (hp : 0 ≤ p) :
    0 < comparisonWeight a p := by
  by_cases h : p=0
  · simp [comparisonWeight,h]
  · have hp' : 0 < p := lt_of_le_of_ne hp (Ne.symm h)
    simp only [comparisonWeight, if_neg h]
    exact div_pos (Real.sqrt_pos.mpr hp') (by nlinarith [mul_nonneg ha hp])
theorem comparisonVector_pos {ι : Type*} (a : ℝ) (p : ι → ℝ)
    (ha : 0 ≤ a) (hp : ∀ i, 0 ≤ p i) (D : Finset ι) :
    0 < comparisonVector a p D :=
  Finset.prod_pos fun i _ => comparisonWeight_pos a (p i) ha (hp i)
/-- A pair hop cancels the square roots in the comparison weights. -/
private theorem comparison_hop (a p q : ℝ) (ha : 0 ≤ a) (hp : 0 ≤ p) (hq : 0 ≤ q) :
    Real.sqrt p * Real.sqrt q * comparisonWeight a q / comparisonWeight a p =
      if p=0 then 0 else (1+a*p)*q/(1+a*q) := by
  by_cases hp0 : p=0
  · simp [hp0,comparisonWeight]
  · by_cases hq0 : q=0
    · simp [hq0,comparisonWeight,hp0]
    · have hsp : 0 < Real.sqrt p := Real.sqrt_pos.mpr (lt_of_le_of_ne hp (Ne.symm hp0))
      have hdp : 0 < 1+a*p := by nlinarith [mul_nonneg ha hp]
      have hdq : 0 < 1+a*q := by nlinarith [mul_nonneg ha hq]
      simp only [comparisonWeight, if_neg hp0, if_neg hq0]
      field_simp [ne_of_gt hsp,ne_of_gt hdp,ne_of_gt hdq]
      nlinarith [Real.sq_sqrt hq]
/-- Product ratios for replacing an occupied label by an unoccupied one. -/
private theorem comparison_move {ι : Type*} [DecidableEq ι] (a : ℝ) (p : ι → ℝ)
    (ha : 0 ≤ a) (hp : ∀ i, 0 ≤ p i) (D : Finset ι) (i j : ι)
    (hi : i ∈ D) (hj : j ∉ D) :
    comparisonVector a p (insert j (D.erase i)) / comparisonVector a p D =
      comparisonWeight a (p j) / comparisonWeight a (p i) := by
  have hj' : j ∉ D.erase i := fun h => hj (Finset.mem_of_mem_erase h)
  have hwi := comparisonWeight_pos a (p i) ha (hp i)
  have he := comparisonVector_pos a p ha hp (D.erase i)
  simp only [comparisonVector, Finset.prod_insert hj']
  rw [← Finset.mul_prod_erase D (fun k => comparisonWeight a (p k)) hi]
  exact mul_div_mul_right _ _ (ne_of_gt he)
end
section
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- The incidence matrix removes exactly one occupied pair. -/
def pairIncidence (p : ι → ℝ) (R D : Finset ι) : ℝ :=
  ∑ i, if i ∈ D ∧ R = D.erase i then Real.sqrt (p i) else 0
/-- Its Gram matrix is the occupation-pair quadratic form. -/
def pairKernel (p : ι → ℝ) (D E : Finset ι) : ℝ :=
  dotProduct (fun R => pairIncidence p R D) (fun R => pairIncidence p R E)
private theorem erase_insert_condition (i : ι) (R D : Finset ι) :
    (i ∈ D ∧ R = D.erase i) ↔ (i ∉ R ∧ D = insert i R) := by
  constructor
  · rintro ⟨hi,rfl⟩
    exact ⟨by simp, (Finset.insert_erase hi).symm⟩
  · rintro ⟨hi,rfl⟩
    simp [hi]
private theorem pairIncidence_creation (p : ι → ℝ) (R D : Finset ι) :
    pairIncidence p R D =
      ∑ i, if i ∉ R ∧ D = insert i R then Real.sqrt (p i) else 0 := by
  unfold pairIncidence
  apply Finset.sum_congr rfl
  intro i _
  simp only [erase_insert_condition]
private theorem pairIncidence_row (p : ι → ℝ) (f : Finset ι → ℝ) (R : Finset ι) :
    (∑ D : Finset ι, pairIncidence p R D * f D) =
      ∑ i ∈ Rᶜ, Real.sqrt (p i) * f (insert i R) := by
  simp_rw [pairIncidence_creation, Finset.sum_mul]
  rw [Finset.sum_comm]
  have hr : Rᶜ = Finset.univ.filter (fun i => i ∉ R) := by ext i; simp
  rw [hr, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i ∈ R
  · simp [hi]
  · simp [hi, ite_mul]
theorem pairKernel_row (p : ι → ℝ) (f : Finset ι → ℝ) (D : Finset ι) :
    (∑ E : Finset ι, pairKernel p D E * f E) =
      ∑ i ∈ D, Real.sqrt (p i) *
        (∑ j ∈ (D.erase i)ᶜ, Real.sqrt (p j) * f (insert j (D.erase i))) := by
  simp only [pairKernel, dotProduct, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [mul_assoc, ← Finset.mul_sum, pairIncidence_row]
  simp only [pairIncidence, Finset.sum_mul]
  rw [Finset.sum_comm]
  rw [← Fintype.sum_ite_mem D]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i ∈ D
  · simp [hi, ite_mul]
  · simp [hi]
end
section
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
private theorem weighted_hop_bound (a : ℝ) (p : ι → ℝ) (ha : 0 ≤ a)
    (hp : ∀ i, 0 ≤ p i) (D : Finset ι) (i j : ι) (hi : i ∈ D) (hj : j ∉ D) :
    Real.sqrt (p i) * Real.sqrt (p j) * comparisonVector a p (insert j (D.erase i)) /
      comparisonVector a p D ≤ (1+a*p i) * (p j/(1+a*p j)) := by
  calc
    _ = Real.sqrt (p i) * Real.sqrt (p j) *
        (comparisonVector a p (insert j (D.erase i)) / comparisonVector a p D) := by ring
    _ = Real.sqrt (p i) * Real.sqrt (p j) *
        (comparisonWeight a (p j) / comparisonWeight a (p i)) := by
      rw [comparison_move a p ha hp D i j hi hj]
    _ = if p i=0 then 0 else (1+a*p i)*p j/(1+a*p j) := by
      simpa only [mul_div_assoc] using comparison_hop a (p i) (p j) ha (hp i) (hp j)
    _ ≤ _ := by
      split_ifs
      · exact mul_nonneg (by nlinarith [mul_nonneg ha (hp i)])
          (div_nonneg (hp j) (by nlinarith [mul_nonneg ha (hp j)]))
      · exact le_of_eq (by ring)
/-- The zero-patched product weight bounds every actual pair-incidence row. -/
theorem pairKernel_weighted_row (a : ℝ) (p : ι → ℝ) (ha : 0 ≤ a)
    (hp : ∀ i, 0 ≤ p i) (D : Finset ι) :
    (∑ E : Finset ι, pairKernel p D E * comparisonVector a p E) /
      comparisonVector a p D ≤
      (∑ i ∈ D, p i) + ((D.card : ℝ)+a*(∑ i ∈ D, p i)) *
        (∑ j ∈ Dᶜ, p j/(1+a*p j)) := by
  let f := comparisonVector a p
  have hf : 0 < f D := comparisonVector_pos a p ha hp D
  have hdiag (i : ι) : Real.sqrt (p i) * (Real.sqrt (p i)*f D) / f D = p i := by
    rw [← mul_assoc, Real.mul_self_sqrt (hp i), mul_div_cancel_right₀ _ (ne_of_gt hf)]
  rw [pairKernel_row, Finset.sum_div]
  calc
    _ ≤ ∑ i ∈ D, (p i+(1+a*p i)*(∑ j ∈ Dᶜ, p j/(1+a*p j))) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [Finset.compl_erase, Finset.sum_insert (by simpa using hi), Finset.insert_erase hi,
        mul_add, add_div, hdiag, Finset.mul_sum, Finset.sum_div]
      apply add_le_add_right
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j hj
      have hj' : j ∉ D := Finset.mem_compl.mp hj
      simpa only [f, mul_assoc] using weighted_hop_bound a p ha hp D i j hi hj'
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul]
      congr 1
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp
theorem pairKernel_row_bound (p : ι → ℝ) (m : ℕ) (hm : 1 ≤ m)
    (α : ℝ) (hα : 0 ≤ α) (hp : ∀ i, 0 ≤ p i) (hpa : ∀ i, p i ≤ α)
    (hsum : (∑ i, p i) ≤ 1) (hsmall : 2*(m : ℝ)*α ≤ 1)
    (D : Finset ι) (hD : D.card ≤ m) :
    (∑ E : Finset ι, pairKernel p D E * comparisonVector ((m : ℝ)-1) p E) /
      comparisonVector ((m : ℝ)-1) p D ≤
      (m : ℝ)-(m : ℝ)*((m : ℝ)-1)*(∑ i, p i^2)+(5/2)*(m : ℝ)^3*α^2 := by
  have ha : 0 ≤ (m : ℝ)-1 := sub_nonneg.mpr (by exact_mod_cast hm)
  have hT : 0 ≤ ∑ j ∈ Dᶜ, p j/(1+((m : ℝ)-1)*p j) :=
    Finset.sum_nonneg fun j _ => div_nonneg (hp j) (by nlinarith [mul_nonneg ha (hp j)])
  have hcomp : (∑ j ∈ Dᶜ, p j/(1+((m : ℝ)-1)*p j)) =
      (∑ j, p j/(1+((m : ℝ)-1)*p j)) -
      (∑ j ∈ D, p j/(1+((m : ℝ)-1)*p j)) := by
    have h := Finset.sum_add_sum_compl D (fun j => p j/(1+((m : ℝ)-1)*p j))
    linarith
  calc
    _ ≤ _ := pairKernel_weighted_row _ p ha hp D
    _ ≤ (∑ i ∈ D, p i) + ((m : ℝ)+((m : ℝ)-1)*(∑ i ∈ D, p i)) *
        (∑ j ∈ Dᶜ, p j/(1+((m : ℝ)-1)*p j)) := by
      apply add_le_add_right
      apply mul_le_mul_of_nonneg_right _ hT
      exact add_le_add_left (by exact_mod_cast hD) _
    _ ≤ _ := by rw [hcomp]; exact occupation_row_bound p m hm α hα hp hpa hsum hsmall D hD
end
end D5.S3.Quantum.FermionicCorrelationalBound.OccupationHilbertContractions
