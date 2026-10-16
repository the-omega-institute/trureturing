/- GID: D5/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding
   generality: I
   mirror-B: D5/B/S3/Quantum/FermionicCorrelationalBound/CanonicalRdmAndPadding
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Canonical wedges, Gram RDMs and coefficient padding. -/
/-
Admission witness: D5.S3.Quantum.FermionicCorrelationalBound.CanonicalRdmAndPadding.countableBL_tendsto.
fullC_entries: proof_shape: bind-only; escape_witness: none; consumer: CanonicalRdmAndPadding.paired_entries.
paired_word_product: proof_shape: bind-only; escape_witness: none; consumer: CanonicalRdmAndPadding.paired_entries.
paired_entries: proof_shape: bind-only; escape_witness: none; consumer: CanonicalRdmAndPadding.pair_entry_transition.
pairWord_zero_or_one: proof_shape: bind-only; escape_witness: none; consumer: CanonicalRdmAndPadding.pair_entry_transition.
pairWord_one_iff: proof_shape: bind-only; escape_witness: none; consumer: CanonicalRdmAndPadding.pair_entry_transition.
pair_entry_transition: proof_shape: bind-only; escape_witness: none; consumer: CompletedCorrelationalBound.pair_matrix_row, CompletedCorrelationalBound.standardB_real.
up_down_ne: proof_shape: bind-only; escape_witness: none; consumer: CanonicalRdmAndPadding.doublePairs_add, CanonicalRdmAndPadding.doublePairs_remove, CanonicalRdmAndPadding.transition_add, CanonicalRdmAndPadding.transition_remove, CompletedCorrelationalBound.doublePairs_count, CompletedCorrelationalBound.occupiedModes_addPair, CompletedCorrelationalBound.occupiedModes_removePair, CompletedCorrelationalBound.removePair_count.
upMode_injective: proof_shape: bind-only; escape_witness: none; consumer: CanonicalRdmAndPadding.doublePairs_add, CanonicalRdmAndPadding.doublePairs_remove, CompletedCorrelationalBound.doublePairs_count.
downMode_injective: proof_shape: bind-only; escape_witness: none; consumer: CanonicalRdmAndPadding.doublePairs_add, CanonicalRdmAndPadding.doublePairs_remove, CompletedCorrelationalBound.doublePairs_count.
transition_remove: proof_shape: bind-only; escape_witness: none; consumer: CompletedCorrelationalBound.realB_column, CompletedCorrelationalBound.transition_particle_count.
transition_add: proof_shape: bind-only; escape_witness: none; consumer: CompletedCorrelationalBound.pair_matrix_row, CompletedCorrelationalBound.realB_row.
doublePairs_remove: proof_shape: bind-only; escape_witness: none; consumer: CompletedCorrelationalBound.actual_row_le_pair_row.
doublePairs_add: proof_shape: bind-only; escape_witness: none; consumer: CompletedCorrelationalBound.actual_row_le_pair_row.
finite_ordered_pair_energies: proof_shape: content; escape_witness: OccupationHilbertContractions.ordered_pair_energy; consumer: CanonicalRdmAndPadding.ordered_pair_energies_summable.
ordered_pair_energies_summable: proof_shape: content; escape_witness: OccupationHilbertContractions.ordered_pair_energy; consumer: CanonicalRdmAndPadding.countable_ordered_pair_trace, CanonicalRdmAndPadding.orderedContractionFamily, CanonicalRdmAndPadding.tensorSynthesis_norm, PhysicalContractionRdmBridge.sourcePairNorms, PhysicalContractionRdmBridge.sourceSynthesis_norm.
countable_ordered_pair_trace: proof_shape: content; escape_witness: OccupationHilbertContractions.ordered_pair_energy; consumer: PhysicalContractionRdmBridge.sourcePair_trace.
tensorSeries_summable: proof_shape: content; escape_witness: OccupationHilbertContractions.ordered_pair_energy; consumer: CanonicalRdmAndPadding.tensorSynthesisLinear.
tensorSynthesis_norm: proof_shape: content; escape_witness: OccupationHilbertContractions.ordered_pair_energy; consumer: CanonicalRdmAndPadding.tensorSynthesisCLM.
tensorSynthesis_single: proof_shape: bind-only; escape_witness: none; consumer: CanonicalRdmAndPadding.tensorSynthesis_orderedPairWedge.
inner_star_star_countable: proof_shape: bind-only; escape_witness: none; consumer: PhysicalContractionRdmBridge.basisConjugate_inner.
completedRayleigh_contraction: proof_shape: bind-only; escape_witness: none; consumer: CanonicalRdmAndPadding.completed_identity_2_4, PhysicalContractionRdmBridge.sourceRayleigh_transport.
countable_pair_reverse: proof_shape: bind-only; escape_witness: none; consumer: CanonicalRdmAndPadding.pairContract_adjacent_swap.
pairContract_adjacent_swap: proof_shape: bind-only; escape_witness: none; consumer: CanonicalRdmAndPadding.tensorSynthesis_orderedPairWedge.
fourth_moment_summable: proof_shape: bind-only; escape_witness: none; consumer: CanonicalRdmAndPadding.fourth_moment_limit.
finite_mass_le_one: proof_shape: bind-only; escape_witness: none; consumer: CompletedCorrelationalBound.countable_finite_corrected_bound.
fourth_moment_limit: proof_shape: bind-only; escape_witness: none; consumer: CanonicalRdmAndPadding.norm_limit_chr3.
norm_limit_chr3: proof_shape: bind-only; escape_witness: none; consumer: CompletedCorrelationalBound.assembly_of_countable_finite_bounds.
pairSeries_summable: proof_shape: content; escape_witness: OccupationHilbertContractions.ordered_pair_energy; consumer: CanonicalRdmAndPadding.countableBL_tendsto, CanonicalRdmAndPadding.countableB_apply, CanonicalRdmAndPadding.tensorSynthesis_canonical, CompletedCorrelationalBound.countableBLinear.
countableBL_tendsto: proof_shape: content; escape_witness: OccupationHilbertContractions.ordered_pair_energy; consumer: CompletedCorrelationalBound.assembly_of_countable_finite_bounds.
countableB_apply: proof_shape: content; escape_witness: OccupationHilbertContractions.ordered_pair_energy; consumer: CanonicalRdmAndPadding.countable_identity_2_4.
countable_identity_2_4: proof_shape: content; escape_witness: OccupationHilbertContractions.ordered_pair_energy; consumer: CompletedCorrelationalBound.assembly_of_countable_finite_bounds, CompletedCorrelationalBound.completed_result.
orderedPairWedge_orthonormal: proof_shape: bind-only; escape_witness: none; consumer: CanonicalRdmAndPadding.canonicalTensor, CanonicalRdmAndPadding.canonicalTensor_star, CanonicalRdmAndPadding.tensorSynthesis_canonical, CompletedTensorSlaterGeometry.sourceCanonicalFamily_coordinates, CompletedTensorSlaterGeometry.sourcePairWedge_orthonormal.
orderedPairWedge_star: proof_shape: bind-only; escape_witness: none; consumer: CanonicalRdmAndPadding.canonicalTensor_star.
canonicalTensor_star: proof_shape: bind-only; escape_witness: none; consumer: CanonicalRdmAndPadding.completed_identity_2_4.
tensorSynthesis_orderedPairWedge: proof_shape: bind-only; escape_witness: none; consumer: CanonicalRdmAndPadding.tensorSynthesis_canonical.
tensorSynthesis_canonical: proof_shape: content; escape_witness: OccupationHilbertContractions.ordered_pair_energy; consumer: CanonicalRdmAndPadding.completed_identity_2_4.
completed_identity_2_4: proof_shape: content; escape_witness: OccupationHilbertContractions.ordered_pair_energy; consumer: CompletedCorrelationalBound.completed_result.
tensorCoordinateEmbedding_basis: proof_shape: bind-only; escape_witness: none; consumer: CanonicalRdmAndPadding.tensorCoordinateEmbedding_sourcePairWedge.
tensorCoordinateEmbedding_sourcePairWedge: proof_shape: bind-only; escape_witness: none; consumer: CompletedTensorSlaterGeometry.exists_pair_preserving_tensor, CompletedTensorSlaterGeometry.sourceCanonicalFamily_coordinates.
canonicalModeLabel_injective: proof_shape: bind-only; escape_witness: none; consumer: CanonicalRdmAndPadding.adaptedLabel_injective.
adaptedLabel_on_pair: proof_shape: bind-only; escape_witness: none; consumer: CompletedTensorSlaterGeometry.exists_pair_preserving_tensor, PhysicalContractionRdmBridge.adaptedChart_nonempty.
adaptedLabel_injective: proof_shape: bind-only; escape_witness: none; consumer: CompletedTensorSlaterGeometry.exists_pair_preserving_tensor, PhysicalContractionRdmBridge.adaptedChart_nonempty.
paddedCoeff_even: proof_shape: bind-only; escape_witness: none; consumer: CanonicalRdmAndPadding.paddedCoeff_moment, CanonicalRdmAndPadding.paddedCoeff_summable_sq, CompletedTensorSlaterGeometry.sourceCanonicalFamily_coordinates.
paddedCoeff_outside: proof_shape: bind-only; escape_witness: none; consumer: CanonicalRdmAndPadding.paddedCoeff_summable_sq.
paddedCoeff_summable_sq: proof_shape: bind-only; escape_witness: none; consumer: CanonicalRdmAndPadding.padCanonicalSequence.
paddedCoeff_moment: proof_shape: bind-only; escape_witness: none; consumer: CanonicalRdmAndPadding.padCanonicalSequence, CanonicalRdmAndPadding.padCanonicalSequence_fourth.
padCanonicalSequence_fourth: proof_shape: bind-only; escape_witness: none; consumer: SourceCorrelationalBound.source_cap_result.
padCanonicalSequence_cap: proof_shape: bind-only; escape_witness: none; consumer: SourceCorrelationalBound.source_cap_result.
admission_basis: escape-witness
Direct frozen dependencies:
  D5/S3/Quantum/FiniteDimensional.qubitZ, statement_id: sha256:381a2bec567456715f58fe6c0c413d59d37882b8499fc81a486c49e7c081d78c.
  D5/S3/Quantum/SpinChains/SupersymmetricFermion/JordanWigner.FullOperator, statement_id: sha256:d0e241c65c207456599a205d965adefde23f6764456a0c5a832a08a676fadfb3.
  D5/S3/Quantum/SpinChains/SupersymmetricFermion/JordanWigner.Local, statement_id: sha256:cea3034ad5d4c2d36ac899cc7964a23cdad5b9a52b0410ee01f4b03ffd41f349.
  D5/S3/Quantum/SpinChains/SupersymmetricFermion/JordanWigner.fermionWord, statement_id: sha256:d1484b5db3ace7148c685690abf5667976f26043e824bad34ea4385d5015100d.
  D5/S3/Quantum/SpinChains/SupersymmetricFermion/JordanWigner.fullC, statement_id: sha256:e5eb14acc0a2901b62190a83ed2543f27309f7f32708edd35fa0376362ebfe97.
Information-escape registration is paused.
-/
import D5.S3.Quantum.FermionicCorrelationalBound.OccupationHilbertContractions
import Mathlib.Topology.Algebra.Star.LinearMap
import D5.S3.Quantum.FiniteDimensional
import D5.S3.Quantum.SpinChains.SupersymmetricFermion.JordanWigner
noncomputable section
open scoped Classical BigOperators TensorProduct ComplexConjugate Matrix
namespace D5.S3.Quantum.FermionicCorrelationalBound.CanonicalRdmAndPadding
open D5.S3.Quantum.FermionicCorrelationalBound.OccupationHilbertContractions
open D5.S3.Quantum.FockSpace.ForbiddenNeighbourDeterminant
section
open scoped BigOperators Matrix
open D5.S3.Quantum.SpinChains.SupersymmetricFermion.JordanWigner
/-- Entry formula for the frozen tensor-defined annihilator. -/
private theorem fullC_entries {d : ℕ} (j : Fin d) (s t : ((Fin d → Bool))) :
    fullC j s t = ∏ k, fermionWord j k (s k) (t k) := by
  simp [fullC, D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.tensorOp,
    Matrix.submatrix_apply]
end
section
open scoped BigOperators Matrix
open D5.S3.Quantum.SpinChains.SupersymmetricFermion.JordanWigner
open D5.S3.Quantum.FiniteDimensional (qubitZ)
def upMode {L s : ℕ} (i : Fin L) : Fin (2*L+s) := ⟨2*i.val,by omega⟩
def downMode {L s : ℕ} (i : Fin L) : Fin (2*L+s) := ⟨2*i.val+1,by omega⟩
def pairWord {L s : ℕ} (i : Fin L) (k : Fin (2*L+s)) : Matrix Bool Bool ℂ :=
  if k = upMode i ∨ k = downMode i then Matrix.single false true 1 else 1
/-- Consecutive-mode Jordan--Wigner words cancel their parity strings. -/
private theorem paired_word_product {L s : ℕ} (i : Fin L) (k : Fin (2*L+s)) :
    fermionWord (downMode i) k * fermionWord (upMode i) k = pairWord i k := by
  classical
  have hu : (upMode (s := s) i).val = 2*i.val := rfl
  have hd : (downMode (s := s) i).val = 2*i.val+1 := rfl
  have hud : (upMode (s := s) i) < downMode i := by apply Fin.mk_lt_mk.mpr; omega
  by_cases hku : k = upMode i
  · subst k
    have hne : upMode (s := s) i ≠ downMode i := ne_of_lt hud
    ext b c
    cases b <;> cases c <;>
      norm_num [fermionWord, pairWord, hud, hne, qubitZ, finTwoEquiv,
        Matrix.mul_apply, Matrix.submatrix_apply, Matrix.single, Fintype.sum_bool]
  · by_cases hkd : k = downMode i
    · subst k
      have hdu : ¬downMode (s := s) i < upMode i := not_lt.mpr (le_of_lt hud)
      have hne : downMode (s := s) i ≠ upMode i := ne_of_gt hud
      simp [fermionWord, pairWord, hdu, hne]
    · by_cases hlt : k < upMode i
      · have hlt' : k < downMode i := lt_trans hlt hud
        ext b c
        cases b <;> cases c <;>
          norm_num [fermionWord, pairWord, hlt, hlt', hku, hkd, qubitZ, finTwoEquiv,
            Matrix.mul_apply, Matrix.submatrix_apply, Matrix.single, Fintype.sum_bool]
      · have hlt' : ¬k < downMode i := by
          intro h
          apply hku
          apply Fin.ext
          have hh := Fin.lt_iff_val_lt_val.mp h
          have hl := not_lt.mp hlt
          have hl' := Fin.le_iff_val_le_val.mp hl
          omega
        simp [fermionWord, pairWord, hlt, hlt', hku, hkd]
/-- Every consecutive-pair annihilator has a tensor entry formula with positive local entries. -/
theorem paired_entries {L s : ℕ} (i : Fin L) (x y : ((Fin (2*L+s) → Bool))) :
    ((fullC (downMode (s := s) i) * fullC (upMode (s := s) i)) :
      Matrix (((Fin (2*L+s) → Bool))) (((Fin (2*L+s) → Bool))) ℂ) x y =
      ∏ k : Fin (2*L+s), pairWord (s := s) i k (x k) (y k) := by
  classical
  simp only [Matrix.mul_apply, fullC_entries]
  simp_rw [← Finset.prod_mul_distrib]
  change (∑ z : Fin (2*L+s) → Bool, ∏ k : Fin (2*L+s),
    (fermionWord (downMode i) k : Matrix Bool Bool ℂ) (x k) (z k) *
      (fermionWord (upMode i) k : Matrix Bool Bool ℂ) (z k) (y k)) = _
  rw [← Fintype.prod_sum (fun k (b : Bool) =>
    (fermionWord (downMode i) k : Matrix Bool Bool ℂ) (x k) b *
      (fermionWord (upMode i) k : Matrix Bool Bool ℂ) b (y k))]
  apply Finset.prod_congr rfl
  intro k _
  exact congrArg (fun M : Matrix Bool Bool ℂ => M (x k) (y k)) (paired_word_product i k)
/-- Each local pair-word entry is zero or one. -/
private theorem pairWord_zero_or_one {L s : ℕ} (i : Fin L) (k : Fin (2*L+s)) (b c : Bool) :
    pairWord i k b c = 0 ∨ pairWord i k b c = 1 := by
  unfold pairWord
  split_ifs <;> cases b <;> cases c <;> norm_num [Matrix.single, Matrix.one_apply]
/-- The actual finite canonical pair sum on the full occupation space, spectators included. -/
def standardB {L s : ℕ} (coeff : Fin L → ℝ) :
    Matrix (((Fin (2*L+s) → Bool))) (((Fin (2*L+s) → Bool))) ℂ :=
  ∑ i, (coeff i : ℂ) • (fullC (downMode (s := s) i) * fullC (upMode (s := s) i))
end
section
open scoped BigOperators Matrix Classical
open D5.S3.Quantum.SpinChains.SupersymmetricFermion.JordanWigner
def pairTransition {L s : ℕ} (i : Fin L) (x y : ((Fin (2*L+s) → Bool))) : Prop :=
  x (upMode i) = false ∧ y (upMode i) = true ∧
  x (downMode i) = false ∧ y (downMode i) = true ∧
  ∀ k, k ≠ upMode i → k ≠ downMode i → x k = y k
private theorem pairWord_one_iff {L s : ℕ} (i : Fin L) (x y : ((Fin (2*L+s) → Bool))) :
    (∀ k, pairWord i k (x k) (y k) = 1) ↔ pairTransition i x y := by
  have hne : upMode (s := s) i ≠ downMode i := by
    intro h
    have hh := congrArg Fin.val h
    simp only [upMode, downMode] at hh
    omega
  constructor
  · intro h
    have hu := h (upMode i)
    have hd := h (downMode i)
    simp [pairWord] at hu hd
    have hbool (b c : Bool) : (Matrix.single false true (1:ℂ)) b c = 1 ↔
        b=false ∧ c=true := by cases b <;> cases c <;> norm_num [Matrix.single]
    obtain ⟨hxu,hyu⟩ := (hbool _ _).mp hu
    obtain ⟨hxd,hyd⟩ := (hbool _ _).mp hd
    refine ⟨hxu,hyu,hxd,hyd,?_⟩
    intro k hku hkd
    have hk := h k
    simp only [pairWord, not_or.mpr ⟨hku,hkd⟩, if_false, Matrix.one_apply] at hk
    by_contra hxy
    simp [hxy] at hk
  · rintro ⟨hxu,hyu,hxd,hyd,hrest⟩ k
    by_cases hu : k=upMode i
    · subst k; simp [pairWord,hxu,hyu,Matrix.single]
    · by_cases hd : k=downMode i
      · subst k; simp [pairWord,hxd,hyd,Matrix.single]
      · simp [pairWord,hu,hd,Matrix.one_apply, hrest k hu hd]
theorem pair_entry_transition {L s : ℕ} (i : Fin L) (x y : ((Fin (2*L+s) → Bool))) :
    (((fullC (downMode (s := s) i) * fullC (upMode (s := s) i)) :
      Matrix (((Fin (2*L+s) → Bool))) (((Fin (2*L+s) → Bool))) ℂ) x y) =
      if pairTransition i x y then 1 else 0 := by
  classical
  rw [paired_entries]
  by_cases h : pairTransition i x y
  · have hh := (pairWord_one_iff i x y).mpr h
    simp [h,hh]
  · have hh : ¬∀ k, pairWord i k (x k) (y k) = 1 :=
      fun ht => h ((pairWord_one_iff i x y).mp ht)
    push Not at hh
    obtain ⟨k,hk⟩ := hh
    rw [if_neg h]
    exact Finset.prod_eq_zero (Finset.mem_univ k)
      ((pairWord_zero_or_one i k (x k) (y k)).resolve_right hk)
end
section
open scoped BigOperators Matrix Classical
def removePair {L s : ℕ} (i : Fin L) (y : ((Fin (2*L+s) → Bool))) : ((Fin (2*L+s) → Bool)) :=
  Function.update (Function.update y (upMode i) false) (downMode i) false
def addPair {L s : ℕ} (i : Fin L) (x : ((Fin (2*L+s) → Bool))) : ((Fin (2*L+s) → Bool)) :=
  Function.update (Function.update x (upMode i) true) (downMode i) true
def pairFull {L s : ℕ} (i : Fin L) (x : ((Fin (2*L+s) → Bool))) : Prop :=
  x (upMode i)=true ∧ x (downMode i)=true
def pairEmpty {L s : ℕ} (i : Fin L) (x : ((Fin (2*L+s) → Bool))) : Prop :=
  x (upMode i)=false ∧ x (downMode i)=false
theorem up_down_ne {L s : ℕ} (i j : Fin L) : upMode (s := s) i ≠ downMode j := by
  intro h
  have hh := congrArg Fin.val h
  simp only [upMode,downMode] at hh
  omega
theorem upMode_injective {L s : ℕ} : Function.Injective (upMode (L := L) (s := s)) := by
  intro i j h
  apply Fin.ext
  have hh := congrArg Fin.val h
  simp only [upMode] at hh
  omega
theorem downMode_injective {L s : ℕ} : Function.Injective (downMode (L := L) (s := s)) := by
  intro i j h
  apply Fin.ext
  have hh := congrArg Fin.val h
  simp only [downMode] at hh
  omega
theorem transition_remove {L s : ℕ} (i : Fin L) (x y : ((Fin (2*L+s) → Bool))) :
    pairTransition i x y ↔ pairFull i y ∧ x=removePair i y := by
  constructor
  · rintro ⟨hxu,hyu,hxd,hyd,hrest⟩
    refine ⟨⟨hyu,hyd⟩,?_⟩
    funext k
    by_cases hu : k=upMode i
    · subst k; simp [removePair,up_down_ne,hxu]
    · by_cases hd : k=downMode i
      · subst k; simp [removePair,hxd]
      · simp [removePair,Function.update_of_ne,hu,hd,hrest k hu hd]
  · rintro ⟨⟨hyu,hyd⟩,rfl⟩
    refine ⟨?_,hyu,?_,hyd,?_⟩
    · simp [removePair,up_down_ne]
    · simp [removePair]
    · intro k hu hd
      simp [removePair,Function.update_of_ne,hu,hd]
theorem transition_add {L s : ℕ} (i : Fin L) (x y : ((Fin (2*L+s) → Bool))) :
    pairTransition i x y ↔ pairEmpty i x ∧ y=addPair i x := by
  constructor
  · rintro ⟨hxu,hyu,hxd,hyd,hrest⟩
    refine ⟨⟨hxu,hxd⟩,?_⟩
    funext k
    by_cases hu : k=upMode i
    · subst k; simp [addPair,up_down_ne,hyu]
    · by_cases hd : k=downMode i
      · subst k; simp [addPair,hyd]
      · simp [addPair,Function.update_of_ne,hu,hd,(hrest k hu hd).symm]
  · rintro ⟨⟨hxu,hxd⟩,rfl⟩
    refine ⟨hxu,?_,hxd,?_,?_⟩
    · simp [addPair,up_down_ne]
    · simp [addPair]
    · intro k hu hd
      simp [addPair,Function.update_of_ne,hu,hd]
def doublePairs {L s : ℕ} (x : ((Fin (2*L+s) → Bool))) : Finset (Fin L) :=
  Finset.univ.filter (fun i => x (upMode i)=true ∧ x (downMode i)=true)
theorem doublePairs_remove {L s : ℕ} (i : Fin L) (x : ((Fin (2*L+s) → Bool))) :
    doublePairs (removePair i x) = (doublePairs x).erase i := by
  apply Finset.ext
  intro j
  simp only [doublePairs,Finset.mem_erase,Finset.mem_filter,Finset.mem_univ,true_and,pairFull]
  by_cases hji : j=i
  · subst j; simp [removePair,up_down_ne]
  · have hu : upMode (s := s) j ≠ upMode i := fun h => hji (upMode_injective h)
    have hd : downMode (s := s) j ≠ downMode i := fun h => hji (downMode_injective h)
    simp [removePair,Function.update_of_ne,hu,hd,up_down_ne,
      (up_down_ne i j).symm,hji]
theorem doublePairs_add {L s : ℕ} (i : Fin L) (x : ((Fin (2*L+s) → Bool))) :
    doublePairs (addPair i x) = insert i (doublePairs x) := by
  apply Finset.ext
  intro j
  simp only [doublePairs,Finset.mem_insert,Finset.mem_filter,Finset.mem_univ,true_and,pairFull]
  by_cases hji : j=i
  · subst j; simp [addPair,up_down_ne]
  · have hu : upMode (s := s) j ≠ upMode i := fun h => hji (upMode_injective h)
    have hd : downMode (s := s) j ≠ downMode i := fun h => hji (downMode_injective h)
    simp [addPair,Function.update_of_ne,hu,hd,up_down_ne,
      (up_down_ne i j).symm,hji]
end
section
open scoped BigOperators Classical ENNReal
set_option backward.isDefEq.respectTransparency false
/-- The ordered contraction family has the source's N(N-1) total-mass bound. -/
private theorem finite_ordered_pair_energies (N : ℕ) (ψ : (lp (fun _ : {s : Finset ℕ // s.card = N} => ℂ) 2)) (t : Finset (ℕ×ℕ)) :
    (∑ ij ∈ t,‖pairContract N ij.1 ij.2 ψ‖^2) ≤ (N*(N-1):ℕ)*‖ψ‖^2 := by
  let g (S : ({s : Finset ℕ // s.card = N})) := ‖ψ S‖^2
  let h (ij : ℕ×ℕ) (S : ({s : Finset ℕ // s.card = N})) :=
    if ij.1≠ij.2 ∧ ij.1∈S.val ∧ ij.2∈S.val then g S else 0
  have hg : Summable g := countable_norm_sq_summable ψ
  have hh (ij : ℕ×ℕ) : Summable (h ij) := by
    apply Summable.of_nonneg_of_le _ _ hg
    · intro S; dsimp [h]; split_ifs <;> positivity
    · intro S; dsimp [h]; split_ifs <;> simp [g]
  have hb (S : ({s : Finset ℕ // s.card = N})) : (∑ ij ∈ t,h ij S) ≤ (N*(N-1):ℕ)*g S := by
    have hc : (t.filter (fun ij => ij.1≠ij.2 ∧ ij.1∈S.val ∧ ij.2∈S.val)).card ≤ N*(N-1) := by
      have hsub : t.filter (fun ij => ij.1≠ij.2 ∧ ij.1∈S.val ∧ ij.2∈S.val) ⊆ S.val.offDiag := by
        intro ij hij
        rcases (Finset.mem_filter.mp hij).2 with ⟨hne,hi,hj⟩
        exact Finset.mem_offDiag.mpr ⟨hi,hj,hne⟩
      simpa only [Finset.offDiag_card,S.property,Nat.mul_sub_left_distrib,mul_one] using Finset.card_le_card hsub
    have he : (∑ ij ∈ t,h ij S) =
        ((t.filter (fun ij => ij.1≠ij.2 ∧ ij.1∈S.val ∧ ij.2∈S.val)).card:ℝ)*g S := by
      simp only [h,← Finset.sum_filter]
      simp
    rw [he]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (sq_nonneg _)
  simp_rw [ordered_pair_energy]
  change (∑ ij ∈ t,∑' S,h ij S) ≤ _
  rw [← Summable.tsum_finsetSum (fun ij _ => hh ij)]
  calc
    _ ≤ ∑' S,(N*(N-1):ℕ)*g S := by
      apply Summable.tsum_le_tsum hb
      · exact Summable.of_nonneg_of_le (fun S => Finset.sum_nonneg fun ij _ => by
          dsimp [h]; split_ifs <;> positivity) hb (hg.mul_left ((N*(N-1):ℕ):ℝ))
      · exact hg.mul_left ((N*(N-1):ℕ):ℝ)
    _ = _ := by rw [tsum_mul_left,← countable_norm_sq ψ]
end
section
open scoped BigOperators Classical
set_option backward.isDefEq.respectTransparency false
theorem ordered_pair_energies_summable (N : ℕ) (ψ : (lp (fun _ : {s : Finset ℕ // s.card = N} => ℂ) 2)) :
    Summable fun ij : ℕ×ℕ => ‖pairContract N ij.1 ij.2 ψ‖^2 :=
  summable_of_sum_le (fun _ => sq_nonneg _) (finite_ordered_pair_energies N ψ)
set_option maxHeartbeats 800000 in
theorem countable_ordered_pair_trace (N : ℕ) (ψ : (lp (fun _ : {s : Finset ℕ // s.card = N} => ℂ) 2)) :
    (∑' ij : ℕ×ℕ,‖pairContract N ij.1 ij.2 ψ‖^2) = (N*(N-1):ℕ)*‖ψ‖^2 := by
  let h (ij : ℕ×ℕ) (S : ({s : Finset ℕ // s.card = N})) :=
    if ij.1≠ij.2 ∧ ij.1∈S.val ∧ ij.2∈S.val then ‖ψ S‖^2 else 0
  have hg : Summable fun S : ({s : Finset ℕ // s.card = N}) => ‖ψ S‖^2 := countable_norm_sq_summable ψ
  have hh (ij : ℕ×ℕ) : Summable (h ij) := by
    apply Summable.of_nonneg_of_le _ _ hg
    · intro S; dsimp [h]; split_ifs <;> positivity
    · intro S; dsimp [h]; split_ifs <;> simp
  have hjoint : Summable (fun a : (ℕ×ℕ)×({s : Finset ℕ // s.card = N}) => h a.1 a.2) := by
    apply (summable_prod_of_nonneg (by
      intro a; dsimp [h]; split_ifs <;> positivity)).mpr
    refine ⟨hh,?_⟩
    simpa only [h,← ordered_pair_energy] using ordered_pair_energies_summable N ψ
  have hrow (S : ({s : Finset ℕ // s.card = N})) :
      (∑' ij : ℕ×ℕ,h ij S) = (N*(N-1):ℕ)*‖ψ S‖^2 := by
    have he : (∑' ij : ℕ×ℕ,h ij S) = ∑ ij ∈ S.val.offDiag,‖ψ S‖^2 := by
      rw [tsum_eq_sum (s := S.val.offDiag) (fun ij hij => ?_)]
      · apply Finset.sum_congr rfl
        intro ij hij
        rcases Finset.mem_offDiag.mp hij with ⟨hi,hj,hne⟩
        exact if_pos ⟨hne,hi,hj⟩
      · have hp : ¬(ij.1≠ij.2 ∧ ij.1∈S.val ∧ ij.2∈S.val) := by
          intro hp
          exact hij (Finset.mem_offDiag.mpr ⟨hp.2.1,hp.2.2,hp.1⟩)
        simp only [h,if_neg hp]
    rw [he]
    simp only [Finset.sum_const,nsmul_eq_mul,Finset.offDiag_card,S.property,Nat.mul_sub_left_distrib,mul_one]
  simp_rw [ordered_pair_energy]
  change (∑' ij,∑' S,h ij S) = _
  have hswap : (∑' ij,∑' S,h ij S) = ∑' S,∑' ij,h ij S := hjoint.tsum_comm.symm
  rw [hswap]
  simp_rw [hrow]
  rw [tsum_mul_left,← countable_norm_sq ψ]
end
section
open scoped BigOperators Classical ENNReal
set_option backward.isDefEq.respectTransparency false
def orderedContractionFamily (N : ℕ) (ψ : (lp (fun _ : {s : Finset ℕ // s.card = N} => ℂ) 2)) : lp (fun _ : ℕ×ℕ => ℝ) 2 :=
  ⟨fun ij => ‖pairContract N ij.1 ij.2 ψ‖,memℓp_gen (by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two,norm_norm] using ordered_pair_energies_summable N ψ)⟩
private theorem tensorSeries_summable (N : ℕ) (ψ : (lp (fun _ : {s : Finset ℕ // s.card = N} => ℂ) 2)) (φ : (lp (fun _ : ℕ×ℕ => ℂ) 2)) :
    Summable fun ij : ℕ×ℕ => φ ij • pairContract N ij.1 ij.2 ψ := by
  apply Summable.of_norm
  have h := lp.summable_mul (p := 2) (q := 2) (by rw [Real.holderConjugate_iff]; norm_num)
    (lp.toNorm φ) (orderedContractionFamily N ψ)
  simpa only [norm_smul,lp.toNorm,orderedContractionFamily,norm_norm] using h
def tensorSynthesis (N : ℕ) (ψ : (lp (fun _ : {s : Finset ℕ // s.card = N} => ℂ) 2)) (φ : (lp (fun _ : ℕ×ℕ => ℂ) 2)) : (lp (fun _ : {s : Finset ℕ // s.card = (N-2)} => ℂ) 2) :=
  ∑' ij : ℕ×ℕ,φ ij • pairContract N ij.1 ij.2 ψ
private theorem tensorSynthesis_norm (N : ℕ) (ψ : (lp (fun _ : {s : Finset ℕ // s.card = N} => ℂ) 2)) (φ : (lp (fun _ : ℕ×ℕ => ℂ) 2)) :
    ‖tensorSynthesis N ψ φ‖ ≤ ‖orderedContractionFamily N ψ‖*‖φ‖ := by
  have hh := lp.tsum_mul_le_mul_norm' (p := 2) (q := 2)
    (by rw [Real.holderConjugate_iff]; norm_num) (lp.toNorm φ) (orderedContractionFamily N ψ)
  simp only [lp.toNorm,orderedContractionFamily,norm_norm] at hh
  change (∑' ij,‖φ ij‖*‖pairContract N ij.1 ij.2 ψ‖) ≤
    ‖lp.toNorm φ‖*‖orderedContractionFamily N ψ‖ at hh
  rw [lp.norm_toNorm] at hh
  calc
    _ ≤ ∑' ij,‖φ ij‖*‖pairContract N ij.1 ij.2 ψ‖ := by
      simpa only [tensorSynthesis,norm_smul] using norm_tsum_le_tsum_norm (f := fun ij : ℕ×ℕ => φ ij • pairContract N ij.1 ij.2 ψ) (by
        have h := lp.summable_mul (p := 2) (q := 2)
          (by rw [Real.holderConjugate_iff]; norm_num) (lp.toNorm φ) (orderedContractionFamily N ψ)
        simpa only [norm_smul,lp.toNorm,orderedContractionFamily,norm_norm] using h)
    _ ≤ _ := by simpa only [mul_comm] using hh
def tensorSynthesisLinear (N : ℕ) (ψ : (lp (fun _ : {s : Finset ℕ // s.card = N} => ℂ) 2)) :
    (lp (fun _ : ℕ×ℕ => ℂ) 2) →ₗ[ℂ] (lp (fun _ : {s : Finset ℕ // s.card = (N-2)} => ℂ) 2) where
  toFun := tensorSynthesis N ψ
  map_add' φ χ := by
    simp only [tensorSynthesis,lp.coeFn_add,Pi.add_apply,add_smul]
    exact (tensorSeries_summable N ψ φ).tsum_add (tensorSeries_summable N ψ χ)
  map_smul' a φ := by
    simp only [tensorSynthesis,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,mul_smul]
    exact (tensorSeries_summable N ψ φ).tsum_const_smul a
def tensorSynthesisCLM (N : ℕ) (ψ : (lp (fun _ : {s : Finset ℕ // s.card = N} => ℂ) 2)) :
    (lp (fun _ : ℕ×ℕ => ℂ) 2) →L[ℂ] (lp (fun _ : {s : Finset ℕ // s.card = (N-2)} => ℂ) 2) :=
  (tensorSynthesisLinear N ψ).mkContinuous ‖orderedContractionFamily N ψ‖ (tensorSynthesis_norm N ψ)
def tensorConjugateCLM (N : ℕ) (ψ : (lp (fun _ : {s : Finset ℕ // s.card = N} => ℂ) 2)) :
    (lp (fun _ : ℕ×ℕ => ℂ) 2) →L[ℂ] (lp (fun _ : {s : Finset ℕ // s.card = (N-2)} => ℂ) 2) :=
  (star (WithConv.toConv (tensorSynthesisCLM N ψ))).ofConv
/-- A bounded positive RDM on the completed ordered tensor-two carrier. -/
def countableGammaCLM (N : ℕ) (ψ : (lp (fun _ : {s : Finset ℕ // s.card = N} => ℂ) 2)) : (lp (fun _ : ℕ×ℕ => ℂ) 2) →L[ℂ] (lp (fun _ : ℕ×ℕ => ℂ) 2) :=
  (ContinuousLinearMap.adjoint (tensorConjugateCLM N ψ)).comp (tensorConjugateCLM N ψ)
private theorem tensorSynthesis_single (N : ℕ) (ψ : (lp (fun _ : {s : Finset ℕ // s.card = N} => ℂ) 2)) (ij : ℕ×ℕ) (z : ℂ) :
    tensorSynthesis N ψ (lp.single 2 ij z)=z • pairContract N ij.1 ij.2 ψ := by
  simp [tensorSynthesis,lp.single_apply,Pi.single_apply]
theorem inner_star_star_countable {A : Type*} (x y : lp (fun _ : A => ℂ) 2) :
    inner ℂ (star x) (star y)=inner ℂ y x := by
  simp only [lp.inner_eq_tsum,lp.star_apply,RCLike.inner_apply,← Complex.star_def,star_star]
  apply tsum_congr
  intro a
  ring
def completedRayleigh (N : ℕ) (ψ : (lp (fun _ : {s : Finset ℕ // s.card = N} => ℂ) 2)) (φ : (lp (fun _ : ℕ×ℕ => ℂ) 2)) : ℝ :=
  (inner ℂ φ (countableGammaCLM N ψ φ)).re
theorem completedRayleigh_contraction (N : ℕ) (ψ : (lp (fun _ : {s : Finset ℕ // s.card = N} => ℂ) 2)) (φ : (lp (fun _ : ℕ×ℕ => ℂ) 2)) :
    completedRayleigh N ψ φ=‖tensorSynthesis N ψ (star φ)‖^2 := by
  rw [completedRayleigh,countableGammaCLM,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right]
  have he : (inner ℂ (tensorConjugateCLM N ψ φ) (tensorConjugateCLM N ψ φ)).re =
      ‖tensorConjugateCLM N ψ φ‖^2 :=
    (norm_sq_eq_re_inner (𝕜 := ℂ) (tensorConjugateCLM N ψ φ)).symm
  change (inner ℂ (tensorConjugateCLM N ψ φ) (tensorConjugateCLM N ψ φ)).re = _
  rw [he]
  change ‖star (tensorSynthesis N ψ (star φ))‖^2= _
  rw [norm_star]
end
section
open scoped BigOperators Classical
def canonicalCoefficients (c : CanonicalSequence) : (lp (fun _ : ℕ => ℂ) 2) :=
  ⟨fun i => (c.coeff i:ℂ),memℓp_gen (by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two,Complex.norm_real,Real.norm_eq_abs,sq_abs]
      using c.summable_sq)⟩
end
section
open scoped Classical
set_option backward.isDefEq.respectTransparency false
/-- Reversing an adjacent canonical annihilation pair changes its sign. -/
private theorem countable_pair_reverse {N : ℕ} (ψ : (lp (fun _ : {s : Finset ℕ // s.card = N} => ℂ) 2)) (i : ℕ) (R : Finset ℕ)
    (hi : 2*i ∉ R) (hj : 2*i+1 ∉ R)
    (hN : (insert (2*i) (insert (2*i+1) R)).card=N) :
    pairCoordinate ψ (2*i+1) (2*i) R = -ψ ⟨insert (2*i) (insert (2*i+1) R),hN⟩ := by
  have hne : 2*i+1 ≠ 2*i := by omega
  have hfilter : R.filter (fun k => k<2*i+1)=R.filter (fun k => k<2*i) := by
    ext k
    simp only [Finset.mem_filter]
    constructor
    · intro ⟨hk,hlt⟩
      have hki : k≠2*i := by intro h; subst k; exact hi hk
      exact ⟨hk,by omega⟩
    · intro ⟨hk,hlt⟩; exact ⟨hk,by omega⟩
  have hinsert : (insert (2*i) R).filter (fun k => k<2*i+1)=insert (2*i) (R.filter (fun k => k<2*i)) := by
    rw [Finset.filter_insert]
    simp only [show 2*i<2*i+1 by omega,if_true,hfilter]
  have hn : (insert (2*i+1) (insert (2*i) R)).card=N := by
    rw [Finset.insert_comm]
    exact hN
  have hcond : 2*i+1 ≠ 2*i ∧ 2*i+1 ∉ R ∧ 2*i ∉ R ∧
      (insert (2*i+1) (insert (2*i) R)).card=N := ⟨hne,hj,hi,hn⟩
  unfold pairCoordinate
  rw [dif_pos hcond,hinsert,Finset.card_insert_of_notMem
    (by simp : 2*i ∉ R.filter (fun k => k<2*i))]

  have he : (⟨insert (2*i+1) (insert (2*i) R),hn⟩ : ({s : Finset ℕ // s.card = N}))=
      ⟨insert (2*i) (insert (2*i+1) R),hN⟩ := Subtype.ext (Finset.insert_comm _ _ _)
  rw [he]
  rw [show (R.filter fun k => k<2*i).card+((R.filter fun k => k<2*i).card+1)=
      2*(R.filter fun k => k<2*i).card+1 by omega,pow_add,pow_mul]
  norm_num

private theorem pairContract_adjacent_swap (N i : ℕ) :
    pairContract N (2*i+1) (2*i) = -pairContract N (2*i) (2*i+1) := by
  ext ψ R
  simp only [neg_apply,lp.coeFn_neg,Pi.neg_apply,pairContract_apply]
  by_cases h : 2*i ∉ R.val ∧ 2*i+1 ∉ R.val ∧ (insert (2*i) (insert (2*i+1) R.val)).card=N
  · rw [countable_pair_sign ψ i R.val h.1 h.2.1 h.2.2,
      countable_pair_reverse ψ i R.val h.1 h.2.1 h.2.2]
  · have h1 : ¬(2*i ≠ 2*i+1 ∧ 2*i ∉ R.val ∧ 2*i+1 ∉ R.val ∧
        (insert (2*i) (insert (2*i+1) R.val)).card=N) := fun hp => h hp.2
    have h2 : ¬(2*i+1 ≠ 2*i ∧ 2*i+1 ∉ R.val ∧ 2*i ∉ R.val ∧
        (insert (2*i+1) (insert (2*i) R.val)).card=N) := by
      intro hp
      apply h
      refine ⟨hp.2.2.1,hp.2.1,?_⟩
      simpa only [Finset.insert_comm] using hp.2.2.2
    simp only [pairCoordinate,dif_neg h1,dif_neg h2,neg_zero]
end
section
open scoped BigOperators Topology
open Filter
private theorem fourth_moment_summable (c : CanonicalSequence) (α : ℝ)
    (hpa : ∀ i,c.coeff i^2 ≤ α) : Summable fun i => c.coeff i^4 := by
  have hle (i : ℕ) : c.coeff i^4 ≤ α*c.coeff i^2 := by
    have h := mul_le_mul_of_nonneg_right (hpa i) (sq_nonneg (c.coeff i))
    nlinarith
  exact Summable.of_nonneg_of_le (fun i => pow_nonneg (c.nonneg i) 4) hle
    (c.summable_sq.mul_left α)
theorem finite_mass_le_one (c : CanonicalSequence) (L : ℕ) :
    (∑ i ∈ Finset.range L,c.coeff i^2) ≤ 1 := by
  rw [← c.mass]
  exact c.summable_sq.sum_le_tsum _ (fun i _ => sq_nonneg _)
private theorem fourth_moment_limit (c : CanonicalSequence) (α : ℝ)
    (hpa : ∀ i,c.coeff i^2 ≤ α) :
    Tendsto (fun L : ℕ => ∑ i ∈ Finset.range L,c.coeff i^4) atTop (𝓝 (∑' i,c.coeff i^4)) :=
  (fourth_moment_summable c α hpa).hasSum.tendsto_sum_nat
/-- Passing the correction term to the limit assumes an actual contraction norm limit. -/
theorem norm_limit_chr3 {E : Type*} [NormedAddCommGroup E]
    (c : CanonicalSequence) (m : ℕ) (α : ℝ) (hpa : ∀ i,c.coeff i^2 ≤ α)
    (v : ℕ → E) (vLimit : E) (hv : Tendsto v atTop (𝓝 vLimit))
    (hfinite : ∀ L, ‖v L‖^2 ≤ (m:ℝ)-(m:ℝ)*((m:ℝ)-1)*
      (∑ i ∈ Finset.range L,c.coeff i^4)+(5/2)*(m:ℝ)^3*α^2) :
    2*‖vLimit‖^2 ≤ (2*(m:ℝ))*
      (1-((m:ℝ)-1)*(∑' i,c.coeff i^4)+(5/8:ℝ)*(2*(m:ℝ)*α)^2) := by
  have hnorm := hv.norm.pow 2
  have hright : Tendsto (fun L : ℕ => (m:ℝ)-(m:ℝ)*((m:ℝ)-1)*
      (∑ i ∈ Finset.range L,c.coeff i^4)+(5/2)*(m:ℝ)^3*α^2) atTop
      (𝓝 ((m:ℝ)-(m:ℝ)*((m:ℝ)-1)*(∑' i,c.coeff i^4)+(5/2)*(m:ℝ)^3*α^2)) :=
    (tendsto_const_nhds.sub (tendsto_const_nhds.mul (fourth_moment_limit c α hpa))).add tendsto_const_nhds
  have hh := le_of_tendsto_of_tendsto' hnorm hright hfinite
  nlinarith
end
section
open scoped BigOperators Classical Topology
open Filter
private def coefficientVector (coeff : ℕ → ℝ) (hq : Summable fun i => coeff i^2) : lp (fun _ : ℕ => ℝ) 2 :=
  ⟨coeff,memℓp_gen (by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two,Real.norm_eq_abs,sq_abs] using hq)⟩
def contractionFamily (m : ℕ) (ψ : (lp (fun _ : {s : Finset ℕ // s.card = (2*m)} => ℂ) 2)) :
    lp (fun _ : ℕ => ℝ) 2 :=
  ⟨fun i => ‖pairContract (2*m) (2*i) (2*i+1) ψ‖,memℓp_gen' (C := (m:ℝ)*‖ψ‖^2) (by
    intro t
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two,norm_norm] using sum_pair_energies m ψ t)⟩
theorem pairSeries_summable (coeff : ℕ → ℝ) (hq : Summable fun i => coeff i^2)
    (m : ℕ) (ψ : (lp (fun _ : {s : Finset ℕ // s.card = (2*m)} => ℂ) 2)) :
    Summable fun i => (coeff i:ℂ) • pairContract (2*m) (2*i) (2*i+1) ψ := by
  apply Summable.of_norm
  have h := lp.summable_mul (p := 2) (q := 2) (by
    rw [Real.holderConjugate_iff]; norm_num) (coefficientVector coeff hq) (contractionFamily m ψ)
  simpa only [norm_smul,Complex.norm_real,coefficientVector,contractionFamily,norm_norm] using h
def countableB (coeff : ℕ → ℝ) (m : ℕ) (ψ : (lp (fun _ : {s : Finset ℕ // s.card = (2*m)} => ℂ) 2)) : (lp (fun _ : {s : Finset ℕ // s.card = (2*m-2)} => ℂ) 2) :=
  ∑' i,(coeff i:ℂ) • pairContract (2*m) (2*i) (2*i+1) ψ
def countableBL (coeff : ℕ → ℝ) (m L : ℕ) (ψ : (lp (fun _ : {s : Finset ℕ // s.card = (2*m)} => ℂ) 2)) : (lp (fun _ : {s : Finset ℕ // s.card = (2*m-2)} => ℂ) 2) :=
  ∑ i ∈ Finset.range L,(coeff i:ℂ) • pairContract (2*m) (2*i) (2*i+1) ψ
theorem countableBL_tendsto (coeff : ℕ → ℝ) (hq : Summable fun i => coeff i^2)
    (m : ℕ) (ψ : (lp (fun _ : {s : Finset ℕ // s.card = (2*m)} => ℂ) 2)) :
    Tendsto (fun L => countableBL coeff m L ψ) atTop (𝓝 (countableB coeff m ψ)) :=
  (pairSeries_summable coeff hq m ψ).hasSum.tendsto_sum_nat
private theorem countableB_apply (coeff : ℕ → ℝ) (hq : Summable fun i => coeff i^2)
    (m : ℕ) (ψ : (lp (fun _ : {s : Finset ℕ // s.card = (2*m)} => ℂ) 2)) (R : ({s : Finset ℕ // s.card = (2*m-2)})) :
    countableB coeff m ψ R = ∑' i,(coeff i:ℂ)*pairCoordinate ψ (2*i) (2*i+1) R.val := by
  let e := lp.evalCLM (fun _ : ({s : Finset ℕ // s.card = (2*m-2)}) => ℂ) 2 (𝕜 := ℂ) R
  change e (∑' i,(coeff i:ℂ) • pairContract (2*m) (2*i) (2*i+1) ψ) = _
  rw [e.map_tsum (pairSeries_summable coeff hq m ψ)]
  simp only [map_smul,smul_eq_mul]
  apply tsum_congr
  intro i
  change (coeff i:ℂ) * pairContract (2*m) (2*i) (2*i+1) ψ R = _
  exact congrArg (fun z : ℂ => (coeff i:ℂ)*z) (pairContract_apply (2*m) (2*i) (2*i+1) ψ R)
theorem countable_identity_2_4 (c : CanonicalSequence) (m : ℕ) (ψ : (lp (fun _ : {s : Finset ℕ // s.card = (2*m)} => ℂ) 2)) :
    canonicalRayleigh c ψ = 2*‖countableB c.coeff m ψ‖^2 := by
  rw [countable_norm_sq]
  simp only [canonicalRayleigh,countableB_apply c.coeff c.summable_sq]
end
section
open scoped BigOperators Classical
set_option backward.isDefEq.respectTransparency false
def orderedPairWedge (i : ℕ) : (lp (fun _ : ℕ×ℕ => ℂ) 2) :=
  ((Real.sqrt 2 : ℂ)⁻¹) •
    ((lp.single 2 (2*i,2*i+1) (1:ℂ) : (lp (fun _ : ℕ×ℕ => ℂ) 2))-lp.single 2 (2*i+1,2*i) (1:ℂ))
theorem orderedPairWedge_orthonormal : Orthonormal ℂ orderedPairWedge := by
  rw [orthonormal_iff_ite]
  intro i j
  have hij : (2*i,2*i+1)=(2*j,2*j+1) ↔ i=j := by
    constructor <;> intro h
    · have hh := congrArg Prod.fst h; omega
    · subst j; rfl
  have hji : (2*i+1,2*i)=(2*j+1,2*j) ↔ i=j := by
    constructor <;> intro h
    · have hh := congrArg Prod.snd h; omega
    · subst j; rfl
  have hcross : (2*i,2*i+1)≠(2*j+1,2*j) := by intro h; have hh := congrArg Prod.fst h; omega
  have hcross' : (2*i+1,2*i)≠(2*j,2*j+1) := by intro h; have hh := congrArg Prod.fst h; omega
  simp only [orderedPairWedge,inner_smul_left,inner_smul_right,inner_sub_left,inner_sub_right,
    lp.inner_single_left,lp.single_apply,Pi.single_apply,RCLike.inner_apply]
  have hsqrt : (Real.sqrt 2 : ℂ)^2=2 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  have hne : (Real.sqrt 2 : ℂ)≠0 := by exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2)))
  have hs : star ((Real.sqrt 2:ℂ)⁻¹)=(Real.sqrt 2:ℂ)⁻¹ := by simp
  by_cases he : i=j
  · subst j
    simp [hcross,hcross']
    field_simp
    linear_combination -hsqrt
  · simp [hs,hij,hji,hcross,hcross',he,ne_comm]
def canonicalTensor (c : CanonicalSequence) : (lp (fun _ : ℕ×ℕ => ℂ) 2) :=
  orderedPairWedge_orthonormal.orthogonalFamily.linearIsometry (canonicalCoefficients c)
private theorem orderedPairWedge_star (i : ℕ) : star (orderedPairWedge i)=orderedPairWedge i := by
  ext ij
  simp [orderedPairWedge,lp.star_apply,lp.coeFn_smul,Pi.smul_apply,lp.coeFn_sub,Pi.sub_apply,lp.single_apply,Pi.single_apply]
private theorem canonicalTensor_star (c : CanonicalSequence) : star (canonicalTensor c)=canonicalTensor c := by
  rw [canonicalTensor,OrthogonalFamily.linearIsometry_apply,tsum_star]
  apply tsum_congr
  intro i
  simp only [LinearIsometry.toSpanSingleton_apply,canonicalCoefficients,star_smul,
    Complex.star_def,Complex.conj_ofReal,orderedPairWedge_star]
private theorem tensorSynthesis_orderedPairWedge (N : ℕ) (ψ : (lp (fun _ : {s : Finset ℕ // s.card = N} => ℂ) 2)) (i : ℕ) :
    tensorSynthesisCLM N ψ (orderedPairWedge i)=(Real.sqrt 2:ℂ) • pairContract N (2*i) (2*i+1) ψ := by
  simp only [orderedPairWedge,map_smul,map_sub]
  change (Real.sqrt 2:ℂ)⁻¹ •
    (tensorSynthesis N ψ (lp.single 2 (2*i,2*i+1) (1:ℂ))-
     tensorSynthesis N ψ (lp.single 2 (2*i+1,2*i) (1:ℂ))) = _
  rw [tensorSynthesis_single,tensorSynthesis_single,one_smul,one_smul,pairContract_adjacent_swap,neg_apply]
  rw [sub_neg_eq_add,← two_smul ℂ,smul_smul]
  apply congrArg (fun a : ℂ => a • pairContract N (2*i) (2*i+1) ψ)
  have hsqrt : (Real.sqrt 2:ℂ)^2=2 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  have hne : (Real.sqrt 2:ℂ)≠0 := by exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2)))
  field_simp
  linear_combination -hsqrt
private theorem tensorSynthesis_canonical (c : CanonicalSequence) (m : ℕ) (ψ : (lp (fun _ : {s : Finset ℕ // s.card = (2*m)} => ℂ) 2)) :
    tensorSynthesis (2*m) ψ (canonicalTensor c) = (Real.sqrt 2:ℂ) • countableB c.coeff m ψ := by
  change tensorSynthesisCLM (2*m) ψ (canonicalTensor c)= _
  rw [canonicalTensor,OrthogonalFamily.linearIsometry_apply]
  rw [(tensorSynthesisCLM (2*m) ψ).map_tsum
    (orderedPairWedge_orthonormal.orthogonalFamily.summable_of_lp (canonicalCoefficients c))]
  simp only [map_smul,LinearIsometry.toSpanSingleton_apply,canonicalCoefficients,
    tensorSynthesis_orderedPairWedge,smul_smul]
  rw [countableB,← (pairSeries_summable c.coeff c.summable_sq m ψ).tsum_const_smul (Real.sqrt 2:ℂ)]
  apply tsum_congr
  intro i
  rw [smul_smul]
  exact congrArg (fun a : ℂ => a • pairContract (2*m) (2*i) (2*i+1) ψ) (mul_comm _ _)
/-- The completed ordered-tensor RDM expectation has the literal source factor two. -/
theorem completed_identity_2_4 (c : CanonicalSequence) (m : ℕ) (ψ : (lp (fun _ : {s : Finset ℕ // s.card = (2*m)} => ℂ) 2)) :
    completedRayleigh (2*m) ψ (canonicalTensor c)=2*‖countableB c.coeff m ψ‖^2 := by
  rw [completedRayleigh_contraction,canonicalTensor_star,tensorSynthesis_canonical,norm_smul,mul_pow,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),Real.sq_sqrt (by norm_num)]
end
section
open scoped TensorProduct BigOperators Classical
open UniformSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
def tensorCoordinateEmbedding {ι : Type*} (b : HilbertBasis ι ℂ E) (e : ι ↪ ℕ) :
    (UniformSpace.Completion (E ⊗[ℂ] E)) →ₗᵢ[ℂ] (lp (fun _ : ℕ×ℕ => ℂ) 2) :=
  (coordinateRename (e.prodMap e)).comp (tensorHilbertBasis b b).repr.toLinearIsometry
private theorem tensorCoordinateEmbedding_basis {ι : Type*} (b : HilbertBasis ι ℂ E)
    (e : ι ↪ ℕ) (i j : ι) :
    tensorCoordinateEmbedding b e ((b i ⊗ₜ[ℂ] b j : E ⊗[ℂ] E) : (UniformSpace.Completion (E ⊗[ℂ] E))) =
      lp.single 2 (e i,e j) (1:ℂ) := by
  change coordinateRename (e.prodMap e) ((tensorHilbertBasis b b).repr
    (tensorBasisVector b b (i,j))) = _
  rw [← tensorHilbertBasis_apply,(tensorHilbertBasis b b).repr_self]
  rw [coordinateRename,OrthogonalFamily.linearIsometry_apply_single]
  simp only [LinearIsometry.toSpanSingleton_apply,one_smul]
  ext ij
  simp [lp.single_apply,Pi.single_apply,Function.Embedding.prodMap]
def sourcePairWedge {ι : Type*} (v : ι × Fin 2 → E) (i : ι) : (UniformSpace.Completion (E ⊗[ℂ] E)) :=
  ((Real.sqrt 2:ℂ)⁻¹) •
    (((v (i,0) ⊗ₜ[ℂ] v (i,1) : E ⊗[ℂ] E) : (UniformSpace.Completion (E ⊗[ℂ] E))) -
     ((v (i,1) ⊗ₜ[ℂ] v (i,0) : E ⊗[ℂ] E) : (UniformSpace.Completion (E ⊗[ℂ] E))))
/-- The literal completed-tensor wedge maps to the normalized ordered coordinate wedge. -/
theorem tensorCoordinateEmbedding_sourcePairWedge {ι w : Type*}
    (v : ι × Fin 2 → E) (b : HilbertBasis w ℂ E) (e : w ↪ ℕ)
    (r : ι × Fin 2 → w) (hb : ∀ p,b (r p)=v p) (a : ι → ℕ)
    (he0 : ∀ i,e (r (i,0))=2*a i) (he1 : ∀ i,e (r (i,1))=2*a i+1) (i : ι) :
    tensorCoordinateEmbedding b e (sourcePairWedge v i) = orderedPairWedge (a i) := by
  simp only [sourcePairWedge,map_smul,map_sub]
  rw [← hb (i,0),← hb (i,1),tensorCoordinateEmbedding_basis,tensorCoordinateEmbedding_basis,
    he0,he1]
  rfl
end
section
open scoped Classical
open TopologicalSpace
def canonicalModeLabel {ι : Type*} (e : ι ↪ ℕ) (p : ι × Fin 2) : ℕ :=
  4 * e p.1 + p.2.val
private theorem canonicalModeLabel_injective {ι : Type*} (e : ι ↪ ℕ) :
    Function.Injective (canonicalModeLabel e) := by
  intro p q h
  have hp := p.2.isLt
  have hq := q.2.isLt
  change 4 * e p.1 + p.2.val = 4 * e q.1 + q.2.val at h
  have hfst : e p.1 = e q.1 := by omega
  have hsnd : p.2.val = q.2.val := by omega
  exact Prod.ext (e.injective hfst) (Fin.ext hsnd)
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
def adaptedLabel {ι : Type*} (v : ι × Fin 2 → E) (e : ι ↪ ℕ)
    (w : Set E) (g : w ↪ ℕ) (y : w) : ℕ :=
  if h : y.val ∈ Set.range v then canonicalModeLabel e (Classical.choose h)
  else 4 * g y + 2
theorem adaptedLabel_on_pair {ι : Type*} {v : ι × Fin 2 → E}
    (hv : Function.Injective v) (e : ι ↪ ℕ) (w : Set E) (g : w ↪ ℕ)
    (hw : Set.range v ⊆ w) (p : ι × Fin 2) :
    adaptedLabel v e w g ⟨v p,hw ⟨p,rfl⟩⟩ = canonicalModeLabel e p := by
  have hp : v p ∈ Set.range v := ⟨p,rfl⟩
  rw [adaptedLabel,dif_pos hp]
  exact congrArg (canonicalModeLabel e) (hv (Classical.choose_spec hp))
theorem adaptedLabel_injective {ι : Type*} {v : ι × Fin 2 → E}
    (e : ι ↪ ℕ) (w : Set E) (g : w ↪ ℕ) :
    Function.Injective (adaptedLabel v e w g) := by
  intro y z h
  unfold adaptedLabel at h
  split_ifs at h with hy hz hz
  · have hp := canonicalModeLabel_injective e h
    apply Subtype.ext
    exact (Classical.choose_spec hy).symm.trans
      ((congrArg v hp).trans (Classical.choose_spec hz))
  · have hp := (Classical.choose hy).2.isLt
    change 4 * e (Classical.choose hy).1 + (Classical.choose hy).2.val = 4 * g z + 2 at h
    omega
  · have hp := (Classical.choose hz).2.isLt
    change 4 * g y + 2 = 4 * e (Classical.choose hz).1 + (Classical.choose hz).2.val at h
    omega
  · exact g.injective (by omega)
end
section
open scoped BigOperators Classical
def paddedCoeff (coeff : ℕ → ℝ) (i : ℕ) : ℝ := if i%2=0 then coeff (i/2) else 0
theorem paddedCoeff_even (coeff : ℕ → ℝ) (i : ℕ) : paddedCoeff coeff (2*i)=coeff i := by
  simp [paddedCoeff]
private theorem paddedCoeff_outside (coeff : ℕ → ℝ) (i : ℕ) (hi : i ∉ Set.range (fun k : ℕ => 2*k)) :
    paddedCoeff coeff i=0 := by
  unfold paddedCoeff
  by_cases he : i%2=0
  · have h : i=2*(i/2) := by omega
    exact False.elim (hi ⟨i/2,h.symm⟩)
  · rw [if_neg he]
private theorem paddedCoeff_summable_sq (coeff : ℕ → ℝ) (hc : Summable fun i => coeff i^2) :
    Summable fun i => paddedCoeff coeff i^2 := by
  have hinj : Function.Injective (fun i : ℕ => 2*i) := by intro i j h; change 2*i=2*j at h; omega
  apply (hinj.summable_iff (fun i hi => by rw [paddedCoeff_outside coeff i hi]; norm_num)).mp
  simpa only [Function.comp_def,paddedCoeff_even] using hc
/-- Positive moments are invariant under zero padding between active canonical pairs. -/
private theorem paddedCoeff_moment (coeff : ℕ → ℝ) (k : ℕ) (hk : 0<k) :
    (∑' i,paddedCoeff coeff i^k) = ∑' i,coeff i^k := by
  let f : ↑(Function.support (fun i => coeff i^k)) → ℕ := fun i => 2*i.val
  have hf : Function.Injective f := by
    intro i j h
    apply Subtype.ext
    change 2*i.val=2*j.val at h
    omega
  apply tsum_eq_tsum_of_ne_zero_bij f hf
  · intro i hi
    have he : i%2=0 := by
      by_contra he
      apply hi
      simp [paddedCoeff,he,ne_of_gt hk]
    have hh : i=2*(i/2) := by omega
    have hn : coeff (i/2)^k≠0 := by
      intro hn
      apply hi
      simp only [paddedCoeff,if_pos he,hn]
    exact ⟨⟨i/2,hn⟩,hh.symm⟩
  · intro i
    exact congrArg (fun x : ℝ => x^k) (paddedCoeff_even coeff i.val)
def padCanonicalSequence (c : CanonicalSequence) : CanonicalSequence where
  coeff := paddedCoeff c.coeff
  nonneg i := by
    unfold paddedCoeff
    split_ifs
    · exact c.nonneg _
    · exact le_refl 0
  summable_sq := paddedCoeff_summable_sq c.coeff c.summable_sq
  mass := (paddedCoeff_moment c.coeff 2 (by decide)).trans c.mass
theorem padCanonicalSequence_fourth (c : CanonicalSequence) :
    (∑' i,(padCanonicalSequence c).coeff i^4)=∑' i,c.coeff i^4 :=
  paddedCoeff_moment c.coeff 4 (by decide)
theorem padCanonicalSequence_cap (c : CanonicalSequence) (α : ℝ) (h : ∀ i,c.coeff i^2≤α) :
    ∀ i,(padCanonicalSequence c).coeff i^2≤α := by
  intro i
  have hα : 0≤α := (sq_nonneg (c.coeff 0)).trans (h 0)
  change paddedCoeff c.coeff i^2≤α
  unfold paddedCoeff
  split_ifs
  · exact h _
  · simpa using hα
end
end D5.S3.Quantum.FermionicCorrelationalBound.CanonicalRdmAndPadding
