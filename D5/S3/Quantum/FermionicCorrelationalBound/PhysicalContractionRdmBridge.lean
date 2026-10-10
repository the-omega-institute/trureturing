/- GID: D5/S3/Quantum/FermionicCorrelationalBound/PhysicalContractionRdmBridge
   generality: I
   mirror-B: D5/B/S3/Quantum/FermionicCorrelationalBound/PhysicalContractionRdmBridge
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Normalized annihilation, physical RDM transport and trace. -/
/-
Admission witness: D5.S3.Quantum.FermionicCorrelationalBound.PhysicalContractionRdmBridge.sourceRayleigh_transport.
singleInsert_injective: proof_shape: bind-only; escape_witness: none; consumer: PhysicalContractionRdmBridge.countableAnnihilate.
singlePhase_norm: proof_shape: bind-only; escape_witness: none; consumer: PhysicalContractionRdmBridge.countableAnnihilate.
countableAnnihilate_apply: proof_shape: bind-only; escape_witness: none; consumer: PhysicalContractionRdmBridge.antiHead_intertwining, PhysicalContractionRdmBridge.single_pair_composition.
single_pair_composition: proof_shape: bind-only; escape_witness: none; consumer: PhysicalContractionRdmBridge.source_pair_intertwining.
sorted_position_count: proof_shape: bind-only; escape_witness: none; consumer: PhysicalContractionRdmBridge.antisymmetric_head_insert.
sorted_removeNth: proof_shape: bind-only; escape_witness: none; consumer: PhysicalContractionRdmBridge.antisymmetric_head_insert.
antisymmetric_head_insert: proof_shape: bind-only; escape_witness: none; consumer: PhysicalContractionRdmBridge.antiHead_intertwining.
tensorSlice_apply: proof_shape: bind-only; escape_witness: none; consumer: PhysicalContractionRdmBridge.antiHead_intertwining, PhysicalContractionRdmBridge.particleHead_antisymmetric, PhysicalContractionRdmBridge.source_single_intertwining, PhysicalContractionRdmBridge.tensorSlice_antisymmetric.
tensorSlice_antisymmetric: proof_shape: bind-only; escape_witness: none; consumer: PhysicalContractionRdmBridge.antiHead, PhysicalContractionRdmBridge.antiHead_intertwining, PhysicalContractionRdmBridge.particleHead_antisymmetric.
sqrt_factorial_step: proof_shape: bind-only; escape_witness: none; consumer: PhysicalContractionRdmBridge.antiHead_intertwining.
head_repeated_zero: proof_shape: bind-only; escape_witness: none; consumer: PhysicalContractionRdmBridge.antiHead_intertwining.
slaterBasis_apply: proof_shape: bind-only; escape_witness: none; consumer: PhysicalContractionRdmBridge.antiHead_intertwining, PhysicalContractionRdmBridge.particleOccupation_outside.
antiHead_intertwining: proof_shape: bind-only; escape_witness: none; consumer: PhysicalContractionRdmBridge.source_single_intertwining.
particleHead_repr: proof_shape: content; escape_witness: OccupationHilbertContractions.tensorBasisVector_dense; consumer: PhysicalContractionRdmBridge.particleHead_coordinates.
particleHead_coordinates: proof_shape: content; escape_witness: OccupationHilbertContractions.tensorBasisVector_dense; consumer: PhysicalContractionRdmBridge.particleHead_antisymmetric, PhysicalContractionRdmBridge.source_single_intertwining.
particleExterior_coordinates_iff: proof_shape: content; escape_witness: OccupationHilbertContractions.tensorBasisVector_dense; consumer: PhysicalContractionRdmBridge.particleAntiEmbedding, PhysicalContractionRdmBridge.particleExterior_complete, PhysicalContractionRdmBridge.particleHead_antisymmetric, PhysicalContractionRdmBridge.particleOccupation_outside, PhysicalContractionRdmBridge.sourceAnnihilate, PhysicalContractionRdmBridge.sourceAnnihilate_continuous.
particleHeadFamily_apply: proof_shape: content; escape_witness: OccupationHilbertContractions.tensorBasisVector_dense; consumer: PhysicalContractionRdmBridge.particleHead_antisymmetric, PhysicalContractionRdmBridge.sourceAnnihilate_add, PhysicalContractionRdmBridge.sourceAnnihilate_continuous, PhysicalContractionRdmBridge.sourceAnnihilate_smul.
particleHead_antisymmetric: proof_shape: content; escape_witness: OccupationHilbertContractions.tensorBasisVector_dense; consumer: PhysicalContractionRdmBridge.sourceAnnihilate, PhysicalContractionRdmBridge.sourceAnnihilate_continuous.
source_single_intertwining: proof_shape: content; escape_witness: OccupationHilbertContractions.tensorBasisVector_dense; consumer: PhysicalContractionRdmBridge.source_pair_intertwining.
source_pair_intertwining: proof_shape: content; escape_witness: OccupationHilbertContractions.tensorBasisVector_dense; consumer: PhysicalContractionRdmBridge.sourcePair_norm, PhysicalContractionRdmBridge.sourceSynthesis_transport.
adaptedChart_nonempty: proof_shape: bind-only; escape_witness: none; consumer: PhysicalContractionRdmBridge.adaptedChart.
canonicalPair_countable: proof_shape: bind-only; escape_witness: none; consumer: SourceCorrelationalBound.canonicalIndex.
particleExterior_complete: proof_shape: bind-only; escape_witness: none; consumer: PhysicalContractionRdmBridge.sourceCreate, PhysicalContractionRdmBridge.sourceGram_kernel_arbitrary, PhysicalContractionRdmBridge.sourceSeries_summable.
sourceAnnihilate_add: proof_shape: bind-only; escape_witness: none; consumer: PhysicalContractionRdmBridge.sourceGram_tmul.
sourceAnnihilate_smul: proof_shape: bind-only; escape_witness: none; consumer: PhysicalContractionRdmBridge.sourceGram_tmul.
sourceAnnihilate_continuous: proof_shape: bind-only; escape_witness: none; consumer: PhysicalContractionRdmBridge.sourceGram_tmul.
sourcePair_norm: proof_shape: content; escape_witness: OccupationHilbertContractions.tensorBasisVector_dense; consumer: PhysicalContractionRdmBridge.sourcePairNorms, PhysicalContractionRdmBridge.sourcePair_trace, PhysicalContractionRdmBridge.sourceSynthesis_norm.
sourceSeries_summable: proof_shape: content; escape_witness: OccupationHilbertContractions.ordered_pair_energy; consumer: PhysicalContractionRdmBridge.sourceSynthesisLinear, PhysicalContractionRdmBridge.sourceSynthesis_transport.
sourceSynthesis_norm: proof_shape: content; escape_witness: OccupationHilbertContractions.ordered_pair_energy; consumer: PhysicalContractionRdmBridge.sourceGramCLM, PhysicalContractionRdmBridge.sourceSynthesisCLM.
basisConjugate_norm: proof_shape: bind-only; escape_witness: none; consumer: PhysicalContractionRdmBridge.sourceGramCLM, PhysicalContractionRdmBridge.sourceRayleigh_contraction.
basisConjugate_inner: proof_shape: bind-only; escape_witness: none; consumer: PhysicalContractionRdmBridge.sourceGamma_kernel, PhysicalContractionRdmBridge.sourceGram_kernel_arbitrary.
coordinateRename_star: proof_shape: bind-only; escape_witness: none; consumer: PhysicalContractionRdmBridge.tensorConjugate_coordinates.
tensorConjugate_coordinates: proof_shape: bind-only; escape_witness: none; consumer: PhysicalContractionRdmBridge.sourceRayleigh_transport.
sourceSynthesis_transport: proof_shape: content; escape_witness: OccupationHilbertContractions.ordered_pair_energy; consumer: PhysicalContractionRdmBridge.sourceRayleigh_transport.
sourceSynthesis_basis: proof_shape: bind-only; escape_witness: none; consumer: PhysicalContractionRdmBridge.sourceGamma_kernel, PhysicalContractionRdmBridge.sourceGram_tmul.
basisConjugate_basis: proof_shape: bind-only; escape_witness: none; consumer: PhysicalContractionRdmBridge.sourceGamma_kernel, PhysicalContractionRdmBridge.sourceGram_tmul.
eq_of_hilbertBasis_semilinear: proof_shape: bind-only; escape_witness: none; consumer: PhysicalContractionRdmBridge.sourceGram_tmul.
sourceGram_tmul: proof_shape: content; escape_witness: OccupationHilbertContractions.ordered_pair_energy; consumer: PhysicalContractionRdmBridge.sourceGram_kernel_arbitrary.
sourceGram_kernel_arbitrary: proof_shape: content; escape_witness: OccupationHilbertContractions.ordered_pair_energy; consumer: PhysicalContractionRdmBridge.sourceGamma_eq_gram, PhysicalContractionRdmBridge.sourceGamma_exists.
sourceGamma_exists: proof_shape: content; escape_witness: OccupationHilbertContractions.ordered_pair_energy; consumer: PhysicalContractionRdmBridge.sourceGamma, PhysicalContractionRdmBridge.sourceGamma_eq_gram.
sourceGamma_eq_gram: proof_shape: content; escape_witness: OccupationHilbertContractions.ordered_pair_energy; consumer: PhysicalContractionRdmBridge.sourceGamma_kernel, PhysicalContractionRdmBridge.sourceRayleigh_contraction.
sourceRayleigh_contraction: proof_shape: content; escape_witness: OccupationHilbertContractions.ordered_pair_energy; consumer: PhysicalContractionRdmBridge.sourceRayleigh_transport.
sourceRayleigh_transport: proof_shape: content; escape_witness: OccupationHilbertContractions.ordered_pair_energy; consumer: SourceCorrelationalBound.source_cap_result.
sourceGamma_kernel: proof_shape: content; escape_witness: OccupationHilbertContractions.ordered_pair_energy; consumer: PhysicalContractionRdmBridge.sourceGamma_trace.
particleCoordinates_outside: proof_shape: bind-only; escape_witness: none; consumer: PhysicalContractionRdmBridge.particleOccupation_outside.
particleOccupation_outside: proof_shape: content; escape_witness: OccupationHilbertContractions.tensorBasisVector_dense; consumer: PhysicalContractionRdmBridge.padded_pair_zero.
padded_pair_zero: proof_shape: content; escape_witness: OccupationHilbertContractions.tensorBasisVector_dense; consumer: PhysicalContractionRdmBridge.sourcePair_trace.
sourcePair_trace: proof_shape: content; escape_witness: OccupationHilbertContractions.ordered_pair_energy; consumer: PhysicalContractionRdmBridge.sourceGamma_trace.
sourceGamma_trace: proof_shape: content; escape_witness: OccupationHilbertContractions.ordered_pair_energy; purpose: source RDM normalization.
admission_basis: escape-witness
Direct frozen dependencies:
  none; same-delivery prerequisites are not baseline frozen dependencies.
Information-escape registration is paused.
-/
import D5.S3.Quantum.FermionicCorrelationalBound.CompletedTensorSlaterGeometry
noncomputable section
open UniformSpace
open scoped Classical BigOperators TensorProduct ComplexConjugate Matrix
namespace D5.S3.Quantum.FermionicCorrelationalBound.PhysicalContractionRdmBridge
open D5.S3.Quantum.FermionicCorrelationalBound.CanonicalRdmAndPadding D5.S3.Quantum.FermionicCorrelationalBound.CompletedTensorSlaterGeometry D5.S3.Quantum.FermionicCorrelationalBound.OccupationHilbertContractions
section
open scoped BigOperators Classical
set_option backward.isDefEq.respectTransparency false
private def singleValid (n i : ℕ) (R : ({s : Finset ℕ // s.card = n})) : Prop := i∉R.val
private def singleInsert (n i : ℕ) (R : {R : ({s : Finset ℕ // s.card = n}) // singleValid n i R}) : ({s : Finset ℕ // s.card = (n+1)}) :=
  ⟨insert i R.val.val,by rw [Finset.card_insert_of_notMem R.property,R.val.property]⟩
private theorem singleInsert_injective (n i : ℕ) : Function.Injective (singleInsert n i) := by
  intro R S h
  apply Subtype.ext
  apply Subtype.ext
  have he := congrArg (fun T : ({s : Finset ℕ // s.card = (n+1)}) => T.val.erase i) h
  simpa only [singleInsert,Finset.erase_insert R.property,Finset.erase_insert S.property] using he
private def singlePhase (i : ℕ) (R : ({s : Finset ℕ // s.card = n})) : ℂ :=
  (-1:ℂ)^((R.val.filter fun k => k < i).card)
private theorem singlePhase_norm (n i : ℕ) (R : ({s : Finset ℕ // s.card = n})) : ‖singlePhase i R‖ ≤ 1 := by
  simp [singlePhase,norm_pow]
/-- Actual single-mode annihilation between normalized exterior occupation sectors. -/
def countableAnnihilate (n i : ℕ) : (lp (fun _ : {s : Finset ℕ // s.card = (n+1)} => ℂ) 2) →L[ℂ] (lp (fun _ : {s : Finset ℕ // s.card = n} => ℂ) 2) :=
  partialPullCLM (singleValid n i) (singleInsert n i) (singleInsert_injective n i)
    (singlePhase i) (singlePhase_norm n i)
private theorem countableAnnihilate_apply (n i : ℕ) (ψ : (lp (fun _ : {s : Finset ℕ // s.card = (n+1)} => ℂ) 2)) (R : ({s : Finset ℕ // s.card = n})) :
    countableAnnihilate n i ψ R = annihilationCoordinate ψ i R.val := by
  change partialPullRaw (singleValid n i) (singleInsert n i) (singlePhase i) ψ R = _
  by_cases hi : i∉R.val
  · have hcard : (insert i R.val).card=n+1 := by rw [Finset.card_insert_of_notMem hi,R.property]
    have hc : i∉R.val ∧ (insert i R.val).card=n+1 := ⟨hi,hcard⟩
    unfold partialPullRaw singleValid annihilationCoordinate
    rw [dif_pos hi,dif_pos hc]
    rfl
  · have hc : ¬(i∉R.val ∧ (insert i R.val).card=n+1) := fun h => hi h.1
    unfold partialPullRaw singleValid annihilationCoordinate
    rw [dif_neg hi,dif_neg hc]
theorem single_pair_composition (n i j : ℕ) (ψ : (lp (fun _ : {s : Finset ℕ // s.card = (n+2)} => ℂ) 2)) :
    countableAnnihilate n j (countableAnnihilate (n+1) i ψ)=pairContract (n+2) i j ψ := by
  ext R
  rw [countableAnnihilate_apply,pairContract_apply]
  by_cases hj : j∉R.val
  · have hjcard : (insert j R.val).card=n+1 := by rw [Finset.card_insert_of_notMem hj,R.property]
    have houter : j∉R.val ∧ (insert j R.val).card=n+1 := ⟨hj,hjcard⟩
    unfold annihilationCoordinate
    rw [dif_pos houter]
    rw [countableAnnihilate_apply]
    by_cases hi : i∉insert j R.val
    · have hicard : (insert i (insert j R.val)).card=n+2 := by
        rw [Finset.card_insert_of_notMem hi,hjcard]
      have hine : i≠j := by intro h; exact hi (by simp [h])
      have hiR : i∉R.val := fun h => hi (Finset.mem_insert_of_mem h)
      have hinner : i∉insert j R.val ∧ (insert i (insert j R.val)).card=n+2 := ⟨hi,hicard⟩
      have hp : i≠j ∧ i∉R.val ∧ j∉R.val ∧ (insert i (insert j R.val)).card=n+2 :=
        ⟨hine,hiR,hj,hicard⟩
      unfold annihilationCoordinate pairCoordinate
      rw [dif_pos hinner,dif_pos hp,← mul_assoc,← pow_add]
    · have hinner : ¬(i∉insert j R.val ∧ (insert i (insert j R.val)).card=n+2) := fun h => hi h.1
      have hp : ¬(i≠j ∧ i∉R.val ∧ j∉R.val ∧ (insert i (insert j R.val)).card=n+2) := by
        intro h
        apply hi
        simp only [Finset.mem_insert,not_or]
        exact ⟨h.1,h.2.1⟩
      unfold annihilationCoordinate pairCoordinate
      rw [dif_neg hinner,dif_neg hp,mul_zero]
  · have houter : ¬(j∉R.val ∧ (insert j R.val).card=n+1) := fun h => hj h.1
    have hp : ¬(i≠j ∧ i∉R.val ∧ j∉R.val ∧ (insert i (insert j R.val)).card=n+2) :=
      fun h => hj h.2.2.1
    unfold annihilationCoordinate pairCoordinate
    rw [dif_neg houter,dif_neg hp]
end
section
open scoped BigOperators Classical
/-- The position of a sorted entry is exactly the number of smaller entries. -/
private theorem sorted_position_count (n : ℕ) (S : Finset ℕ) (hS : S.card=n) (p : Fin n) :
    (S.filter (fun k => k < S.orderEmbOfFin hS p)).card = p.val := by
  have hf : S.filter (fun k => k < S.orderEmbOfFin hS p) =
      (Finset.Iio p).image (S.orderEmbOfFin hS) := by
    ext k
    simp only [Finset.mem_filter,Finset.mem_image,Finset.mem_Iio]
    constructor
    · rintro ⟨hk,hlt⟩
      let q := (S.orderIsoOfFin hS).symm ⟨k,hk⟩
      have hq : S.orderEmbOfFin hS q = k :=
        congrArg Subtype.val ((S.orderIsoOfFin hS).apply_symm_apply ⟨k,hk⟩)
      refine ⟨q,?_,hq⟩
      exact (S.orderEmbOfFin hS).lt_iff_lt.mp (hq ▸ hlt)
    · rintro ⟨q,hq,rfl⟩
      exact ⟨Finset.orderEmbOfFin_mem S hS q,(S.orderEmbOfFin hS).strictMono hq⟩
  rw [hf,Finset.card_image_of_injective _ (S.orderEmbOfFin hS).injective,Fin.card_Iio]
/-- Removing a sorted entry leaves the sorted parametrization of the erased set. -/
private theorem sorted_removeNth (n : ℕ) (S : ({s : Finset ℕ // s.card = (n+1)})) (p : Fin (n+1))
    (R : ({s : Finset ℕ // s.card = n})) (hR : R.val = S.val.erase (S.val.orderEmbOfFin S.property p)) :
    p.removeNth (S.val.orderEmbOfFin S.property) = R.val.orderEmbOfFin R.property := by
  apply Finset.orderEmbOfFin_unique R.property
  · intro q
    rw [hR]
    apply Finset.mem_erase.mpr
    constructor
    · exact (S.val.orderEmbOfFin S.property).injective.ne (Fin.succAbove_ne p q)
    · exact Finset.orderEmbOfFin_mem _ _ _
  · exact (S.val.orderEmbOfFin S.property).strictMono.comp (Fin.strictMono_succAbove p)
/-- The sorted Slater insertion phase is the genuine tensor-permutation sign. -/
private theorem antisymmetric_head_insert (n i : ℕ) (R : ({s : Finset ℕ // s.card = n}))
    (hi : i∉R.val) (ψ : (lp (fun _ : Fin (n+1) → ℕ => ℂ) 2)) (hψ : IsAntisymmetric (n+1) ψ) :
    ψ (Fin.cons i (occupationTuple n R 1)) =
      singlePhase i R * ψ (occupationTuple (n+1) (singleInsert n i ⟨R,hi⟩) 1) := by
  let S := singleInsert n i ⟨R,hi⟩
  have hiS : i∈S.val := by simp [S,singleInsert]
  let p : Fin (n+1) := (S.val.orderIsoOfFin S.property).symm ⟨i,hiS⟩
  have hp : S.val.orderEmbOfFin S.property p=i :=
    congrArg Subtype.val ((S.val.orderIsoOfFin S.property).apply_symm_apply ⟨i,hiS⟩)
  have hR : R.val = S.val.erase (S.val.orderEmbOfFin S.property p) := by
    rw [hp]
    simp [S,singleInsert,hi]
  have hremove := sorted_removeNth n S p R hR
  have ht : Fin.cons i (occupationTuple n R 1) =
      occupationTuple (n+1) S 1 ∘ p.cycleRange.symm := by
    change Fin.cons i (R.val.orderEmbOfFin R.property) =
      (S.val.orderEmbOfFin S.property) ∘ p.cycleRange.symm
    rw [← hremove,← hp]
    exact Fin.cons_removeNth_eq_comp_cycleRange_symm (S.val.orderEmbOfFin S.property) p
  have hcount : p.val=(R.val.filter (fun k => k < i)).card := by
    have h := sorted_position_count (n+1) S.val S.property p
    rw [hp] at h
    have hf : S.val.filter (fun k => k < i)=R.val.filter (fun k => k < i) := by
      simp [S,singleInsert,Finset.filter_insert]
    rw [hf] at h
    exact h.symm
  rw [ht,hψ]
  congr 1
  simp [permutationPhase,Equiv.Perm.sign_inv,Fin.sign_cycleRange,singlePhase,← hcount]
end
section
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
def tensorSlice (n i : ℕ) : (lp (fun _ : Fin (n+1) → ℕ => ℂ) 2) →L[ℂ] (lp (fun _ : Fin n → ℕ => ℂ) 2) :=
  partialPullCLM (fun _ : Fin n → ℕ => True) (fun t => Fin.cons i t.val)
    (by intro s t h; apply Subtype.ext; funext k; simpa using congrFun h k.succ)
    (fun _ => 1) (by intro t; simp)
theorem tensorSlice_apply (n i : ℕ) (ψ : (lp (fun _ : Fin (n+1) → ℕ => ℂ) 2)) (t : Fin n → ℕ) :
    tensorSlice n i ψ t = ψ (Fin.cons i t) := by
  simp [tensorSlice,partialPullCLM,partialPullLinear,partialPull,partialPullRaw]
theorem tensorSlice_antisymmetric (n i : ℕ) (ψ : (lp (fun _ : Fin (n+1) → ℕ => ℂ) 2))
    (hψ : IsAntisymmetric (n+1) ψ) : IsAntisymmetric n (tensorSlice n i ψ) := by
  intro t σ
  rw [tensorSlice_apply,tensorSlice_apply]
  let τ := Equiv.Perm.decomposeFin.symm (0,σ)
  have ht : Fin.cons i (t ∘ σ) = Fin.cons i t ∘ τ := by
    funext k
    cases k using Fin.cases <;> simp [τ]
  rw [ht,hψ]
  congr 1
  simp [τ,permutationPhase,Equiv.Perm.decomposeFin.symm_sign]
/-- Square-root-normalized first tensor contraction on the full antisymmetric sector. -/
def antiHead (n i : ℕ) : antisymmetricSubmodule (n+1) →L[ℂ] antisymmetricSubmodule n :=
  { toLinearMap :=
    { toFun := fun ψ => ⟨(Real.sqrt (n+1:ℝ):ℂ) • tensorSlice n i ψ.val,by
        intro t σ
        simp only [lp.coeFn_smul,Pi.smul_apply,smul_eq_mul]
        rw [tensorSlice_antisymmetric n i ψ.val ψ.property t σ]
        ring⟩
      map_add' := by intro x y; apply Subtype.ext; simp [map_add,smul_add]
      map_smul' := by
        intro a x
        apply Subtype.ext
        change (Real.sqrt (n+1:ℝ):ℂ) • tensorSlice n i (a • x.val) =
          a • ((Real.sqrt (n+1:ℝ):ℂ) • tensorSlice n i x.val)
        rw [map_smul,smul_comm] }
    cont := by
      apply Continuous.subtype_mk
      fun_prop }
private theorem sqrt_factorial_step (n : ℕ) :
    (Real.sqrt (n.factorial:ℝ):ℂ) * (Real.sqrt (n+1:ℝ):ℂ) =
      (Real.sqrt ((n+1).factorial:ℝ):ℂ) := by
  rw [← Complex.ofReal_mul]
  congr 1
  rw [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,
    Real.sqrt_mul (by positivity),mul_comm]
private theorem head_repeated_zero (n i : ℕ) (R : ({s : Finset ℕ // s.card = n})) (hi : i∈R.val)
    (ψ : (lp (fun _ : Fin (n+1) → ℕ => ℂ) 2)) (hψ : IsAntisymmetric (n+1) ψ) :
    ψ (Fin.cons i (occupationTuple n R 1)) = 0 := by
  apply antisymmetric_repeated_zero (n+1) ψ hψ
  intro hinj
  let q := (R.val.orderIsoOfFin R.property).symm ⟨i,hi⟩
  have hq : R.val.orderEmbOfFin R.property q=i :=
    congrArg Subtype.val ((R.val.orderIsoOfFin R.property).apply_symm_apply ⟨i,hi⟩)
  have he : (Fin.cons i (occupationTuple n R 1) : Fin (n+1) → ℕ) 0 =
      (Fin.cons i (occupationTuple n R 1) : Fin (n+1) → ℕ) q.succ := by
    change i=R.val.orderEmbOfFin R.property q
    exact hq.symm
  exact (Fin.succ_ne_zero q) (hinj he).symm
theorem slaterBasis_apply (n : ℕ) (S : ({s : Finset ℕ // s.card = n})) :
    slaterHilbertBasis n S = slaterAntiVector n S := by
  rw [slaterHilbertBasis,HilbertBasis.coe_mkOfOrthogonalEqBot]
/-- The independently defined normalized head slice is the signed occupation annihilator. -/
theorem antiHead_intertwining (n i : ℕ) (ψ : antisymmetricSubmodule (n+1)) :
    (slaterHilbertBasis n).repr (antiHead n i ψ) =
      countableAnnihilate n i ((slaterHilbertBasis (n+1)).repr ψ) := by
  ext R
  rw [HilbertBasis.repr_apply_apply,countableAnnihilate_apply]
  rw [slaterBasis_apply]
  change inner ℂ (slaterVector n R)
    ((Real.sqrt (n+1:ℝ):ℂ) • tensorSlice n i ψ.val) = _
  rw [inner_smul_right,slater_inner_antisymmetric n R _
    (tensorSlice_antisymmetric n i ψ.val ψ.property),tensorSlice_apply]
  by_cases hi : i∉R.val
  · have hcard : (insert i R.val).card=n+1 := by rw [Finset.card_insert_of_notMem hi,R.property]
    have hc : i∉R.val ∧ (insert i R.val).card=n+1 := ⟨hi,hcard⟩
    unfold annihilationCoordinate
    rw [dif_pos hc,HilbertBasis.repr_apply_apply,slaterBasis_apply]
    change _ = singlePhase i R * inner ℂ (slaterVector (n+1) (singleInsert n i ⟨R,hi⟩)) ψ.val
    rw [slater_inner_antisymmetric (n+1) _ ψ.val ψ.property,
      antisymmetric_head_insert n i R hi ψ.val ψ.property]
    rw [← sqrt_factorial_step n]
    ring
  · have hi' : i∈R.val := by simpa using hi
    have hc : ¬(i∉R.val ∧ (insert i R.val).card=n+1) := fun h => hi h.1
    unfold annihilationCoordinate
    rw [dif_neg hc,head_repeated_zero n i R hi' ψ.val ψ.property]
    simp
end
open D5.S3.Quantum.FermionicCorrelationalBound.CanonicalRdmAndPadding D5.S3.Quantum.FermionicCorrelationalBound.CompletedTensorSlaterGeometry D5.S3.Quantum.FermionicCorrelationalBound.OccupationHilbertContractions
section
open scoped Classical TensorProduct BigOperators
set_option backward.isDefEq.respectTransparency false
universe u v
/-- Scalar vacuum with the universe of the source; it has exactly one coordinate. -/
def vacuumObject (X : HilbertObject.{u}) : HilbertObject.{u} where
  carrier := lp (fun _ : Fin 0 → X.carrier => ℂ) 2
  normed := inferInstance
  innerProduct := inferInstance
  complete := inferInstance
/-- Actual completed tensor powers, including the scalar zero-particle power. -/
def particleObject (X : HilbertObject.{u}) : ℕ → HilbertObject.{u}
  | 0 => vacuumObject X
  | n+1 => tensorTower X n
def particleBasis {ι : Type v} (X : HilbertObject.{u})
    (b : HilbertBasis ι ℂ X.carrier) : (N : ℕ) →
      HilbertBasis (Fin N → ι) ℂ (particleObject X N).carrier
  | 0 => HilbertBasis.ofRepr (coordinateEquiv (Equiv.ofUnique (Fin 0 → X.carrier) (Fin 0 → ι)))
  | n+1 => tensorTowerTupleBasis X b n
def particleHead (X : HilbertObject.{u}) (f : X.carrier) : (n : ℕ) →
    (particleObject X (n+1)).carrier →L[ℂ] (particleObject X n).carrier
  | 0 => (lp.singleContinuousLinearMap ℂ (fun _ : Fin 0 → X.carrier => ℂ) 2
      (fun k => Fin.elim0 k)).comp (innerSL ℂ f)
  | n+1 => tensorHead f
/-- The physical first-factor contraction has the same tuple coefficients for every tensor. -/
private theorem particleHead_repr {ι : Type v} (X : HilbertObject.{u})
    (b : HilbertBasis ι ℂ X.carrier) (n : ℕ) (i : ι)
    (ψ : (particleObject X (n+1)).carrier) (t : Fin n → ι) :
    (particleBasis X b n).repr (particleHead X (b i) n ψ) t =
      (particleBasis X b (n+1)).repr ψ (Fin.cons i t) := by
  cases n with
  | zero =>
    change coordinateRename (Equiv.ofUnique (Fin 0 → X.carrier) (Fin 0 → ι)).toEmbedding
      (lp.single 2 (fun k => Fin.elim0 k) (inner ℂ (b i) ψ)) t =
      (tensorTowerTupleBasis X b 0).repr ψ (Fin.cons i t)
    have he : (Equiv.ofUnique (Fin 0 → X.carrier) (Fin 0 → ι)) (fun k => Fin.elim0 k) = t :=
      Subsingleton.elim _ _
    have hr := coordinateRename_image
      (Equiv.ofUnique (Fin 0 → X.carrier) (Fin 0 → ι)).toEmbedding
      (lp.single 2 (fun k => Fin.elim0 k) (inner ℂ (b i) ψ)) (fun k => Fin.elim0 k)
    change coordinateRename (Equiv.ofUnique (Fin 0 → X.carrier) (Fin 0 → ι)).toEmbedding
      (lp.single 2 (fun k => Fin.elim0 k) (inner ℂ (b i) ψ))
      ((Equiv.ofUnique (Fin 0 → X.carrier) (Fin 0 → ι)) (fun k => Fin.elim0 k)) = _ at hr
    rw [he] at hr
    simp only [lp.single_apply,Pi.single_apply,if_pos rfl] at hr
    rw [hr,tupleBasis_repr]
    change inner ℂ (b i) ψ = b.repr ψ i
    exact (b.repr_apply_apply ψ i).symm
  | succ n =>
    change (tensorTowerTupleBasis X b n).repr (tensorHead (b i) ψ) t =
      (tensorTowerTupleBasis X b (n+1)).repr ψ (Fin.cons i t)
    rw [tupleBasis_repr,tupleBasis_repr]
    change (tensorTowerBasis X b n).repr (tensorHead (b i) ψ)
      ((tensorTowerTupleEquiv ι n).symm t) =
      (tensorHilbertBasis b (tensorTowerBasis X b n)).repr ψ
      (i,(tensorTowerTupleEquiv ι n).symm t)
    exact tensorHead_basis_coordinates b (tensorTowerBasis X b n) i ψ _
def particleCoordinates {ι : Type v} (X : HilbertObject.{u})
    (b : HilbertBasis ι ℂ X.carrier) (e : ι ↪ ℕ) : (N : ℕ) →
    (particleObject X N).carrier →ₗᵢ[ℂ] (lp (fun _ : Fin N → ℕ => ℂ) 2)
  | 0 => (coordinateRename ((Function.Embedding.arrowCongrRight (γ := Fin 0) e))).comp
      (particleBasis X b 0).repr.toLinearIsometry
  | n+1 => sourceTensorCoordinates X b e n
/-- Vacuum padding retains first-factor contraction and does not add physical modes. -/
private theorem particleHead_coordinates {ι : Type v} (X : HilbertObject.{u})
    (b : HilbertBasis ι ℂ X.carrier) (e : ι ↪ ℕ) (n : ℕ) (i : ι)
    (ψ : (particleObject X (n+1)).carrier) (t : Fin n → ℕ) :
    particleCoordinates X b e n (particleHead X (b i) n ψ) t =
      particleCoordinates X b e (n+1) ψ (Fin.cons (e i) t) := by
  have hcoordinates (N : ℕ) : particleCoordinates X b e N =
      (coordinateRename ((Function.Embedding.arrowCongrRight (γ := Fin N) e))).comp
        (particleBasis X b N).repr.toLinearIsometry := by
    cases N <;> rfl
  rw [hcoordinates, hcoordinates]
  by_cases ht : t∈Set.range ((Function.Embedding.arrowCongrRight (γ := Fin n) e))
  · obtain ⟨s,rfl⟩ := ht
    have hcons : Fin.cons (e i) ((Function.Embedding.arrowCongrRight (γ := Fin n) e) s) =
        (Function.Embedding.arrowCongrRight (γ := Fin (n+1)) e) (Fin.cons i s) := by
      funext k
      cases k using Fin.cases <;> simp [Function.Embedding.arrowCongrRight, Function.Embedding.piCongrRight]
    change coordinateRename ((Function.Embedding.arrowCongrRight (γ := Fin n) e))
      ((particleBasis X b n).repr (particleHead X (b i) n ψ)) ((Function.Embedding.arrowCongrRight (γ := Fin n) e) s) =
      coordinateRename ((Function.Embedding.arrowCongrRight (γ := Fin (n+1)) e)) ((particleBasis X b (n+1)).repr ψ)
      (Fin.cons (e i) ((Function.Embedding.arrowCongrRight (γ := Fin n) e) s))
    rw [hcons,coordinateRename_image,coordinateRename_image,particleHead_repr]
  · have ht' : Fin.cons (e i) t∉Set.range ((Function.Embedding.arrowCongrRight (γ := Fin (n+1)) e)) := by
      rintro ⟨s,hs⟩
      apply ht
      refine ⟨Fin.tail s,?_⟩
      funext k
      simpa [Function.Embedding.arrowCongrRight, Function.Embedding.piCongrRight,Fin.tail] using congrFun hs k.succ
    change coordinateRename ((Function.Embedding.arrowCongrRight (γ := Fin n) e)) _ t =
      coordinateRename ((Function.Embedding.arrowCongrRight (γ := Fin (n+1)) e)) _ (Fin.cons (e i) t)
    rw [coordinateRename_outside _ _ _ ht,coordinateRename_outside _ _ _ ht']
/-- The scalar vacuum and the positive physical exterior sectors. -/
def particleExterior {ι : Type v} (X : HilbertObject.{u})
    (b : HilbertBasis ι ℂ X.carrier) (e : ι ↪ ℕ) : (N : ℕ) →
    Submodule ℂ (particleObject X N).carrier
  | 0 => ⊤
  | n+1 => sourceExterior X b e n
private theorem particleExterior_coordinates_iff {ι : Type v} (X : HilbertObject.{u})
    (b : HilbertBasis ι ℂ X.carrier) (e : ι ↪ ℕ) (N : ℕ)
    (ψ : (particleObject X N).carrier) :
    ψ∈particleExterior X b e N ↔ IsAntisymmetric N (particleCoordinates X b e N ψ) := by
  cases N with
  | zero =>
    constructor
    · intro _ t σ
      have hs : σ=1 := Subsingleton.elim _ _
      subst σ
      simp [permutationPhase]
    · intro _; trivial
  | succ n => exact (sourceTensorCoordinates_antisymmetric X b e n ψ).symm
def particleAntiEmbedding {ι : Type v} (X : HilbertObject.{u})
    (b : HilbertBasis ι ℂ X.carrier) (e : ι ↪ ℕ) (N : ℕ) :
    particleExterior X b e N →ₗᵢ[ℂ] antisymmetricSubmodule N where
  toFun ψ := ⟨particleCoordinates X b e N ψ.val,(particleExterior_coordinates_iff X b e N ψ.val).mp ψ.property⟩
  map_add' x y := Subtype.ext ((particleCoordinates X b e N).map_add x.val y.val)
  map_smul' a x := Subtype.ext ((particleCoordinates X b e N).map_smul a x.val)
  norm_map' x := (particleCoordinates X b e N).norm_map x.val
def particleOccupation {ι : Type v} (X : HilbertObject.{u})
    (b : HilbertBasis ι ℂ X.carrier) (e : ι ↪ ℕ) (N : ℕ) :
    particleExterior X b e N →ₗᵢ[ℂ] (lp (fun _ : {s : Finset ℕ // s.card = N} => ℂ) 2) :=
  (slaterHilbertBasis N).repr.toLinearIsometry.comp (particleAntiEmbedding X b e N)
private def particleHeadFamily (X : HilbertObject.{u}) : (n : ℕ) →
    X.carrier →L⋆[ℂ] ((particleObject X (n+1)).carrier →L[ℂ] (particleObject X n).carrier)
  | 0 =>
    (ContinuousLinearMap.compL ℂ X.carrier ℂ (particleObject X 0).carrier
      (lp.singleContinuousLinearMap ℂ (fun _ : Fin 0 → X.carrier => ℂ) 2
        (fun k => Fin.elim0 k))).comp (innerSL ℂ)
  | n+1 =>
    (ContinuousLinearMap.adjoint.toContinuousLinearEquiv.toContinuousLinearMap).comp
      ((ContinuousLinearMap.compL ℂ (tensorTower X n).carrier
        (X.carrier ⊗[ℂ] (tensorTower X n).carrier)
        (Completion (X.carrier ⊗[ℂ] (tensorTower X n).carrier)) Completion.toComplL).comp
          (TensorProduct.mkL ℂ X.carrier (tensorTower X n).carrier))
private theorem particleHeadFamily_apply {ι : Type v} (X : HilbertObject.{u}) (b : HilbertBasis ι ℂ X.carrier)
    (n : ℕ) (f : X.carrier) : particleHeadFamily X n f = particleHead X f n := by
  cases n with
  | zero => rfl
  | succ n => exact (tensorHead_adjoint b (tensorTowerBasis X b n) f).symm
private theorem particleHead_antisymmetric {ι : Type v} (X : HilbertObject.{u})
    (b : HilbertBasis ι ℂ X.carrier) (e : ι ↪ ℕ) (n : ℕ)
    (ψ : particleExterior X b e (n+1)) (f : X.carrier) :
    IsAntisymmetric n (particleCoordinates X b e n (particleHead X f n ψ.val)) := by
  let T : X.carrier →L⋆[ℂ] lp (fun _ : Fin n → ℕ => ℂ) 2 :=
    (particleCoordinates X b e n).toContinuousLinearMap.comp
      ((ContinuousLinearMap.apply ℂ (particleObject X n).carrier ψ.val).comp (particleHeadFamily X n))
  let K := (antisymmetricSubmodule n).comap T.toLinearMap
  have hK : IsClosed (K : Set X.carrier) := (antisymmetricSubmodule_closed n).preimage T.continuous
  have hspan : Submodule.span ℂ (Set.range b) ≤ K := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    change IsAntisymmetric n (T (b i))
    change IsAntisymmetric n (particleCoordinates X b e n (particleHeadFamily X n (b i) ψ.val))
    rw [particleHeadFamily_apply X b]
    have hc : particleCoordinates X b e n (particleHead X (b i) n ψ.val) =
        tensorSlice n (e i) (particleCoordinates X b e (n+1) ψ.val) := by
      ext t; rw [particleHead_coordinates,tensorSlice_apply]
    rw [hc]
    exact tensorSlice_antisymmetric n (e i) _
      ((particleExterior_coordinates_iff X b e (n+1) ψ.val).mp ψ.property)
  have htop := (Submodule.span ℂ (Set.range b)).topologicalClosure_minimal hspan hK
  rw [b.dense_span] at htop
  have hf := htop (Submodule.mem_top : f∈(⊤ : Submodule ℂ X.carrier))
  change IsAntisymmetric n (particleCoordinates X b e n (particleHeadFamily X n f ψ.val)) at hf
  rwa [particleHeadFamily_apply X b] at hf
/-- The source annihilator is sqrt(N) times physical first-factor contraction. -/
def sourceAnnihilate {ι : Type v} (X : HilbertObject.{u})
    (b : HilbertBasis ι ℂ X.carrier) (e : ι ↪ ℕ) (n : ℕ) (f : X.carrier) :
    particleExterior X b e (n+1) →L[ℂ] particleExterior X b e n :=
  { toLinearMap :=
    { toFun := fun ψ => ⟨(Real.sqrt (n+1:ℝ):ℂ) • particleHead X f n ψ.val,by
        apply (particleExterior_coordinates_iff X b e n _).mpr
        rw [map_smul]
        exact (antisymmetricSubmodule n).smul_mem _ (particleHead_antisymmetric X b e n ψ f)⟩
      map_add' := by intro x y; apply Subtype.ext; simp [map_add,smul_add]
      map_smul' := by
        intro a x
        apply Subtype.ext
        change (Real.sqrt (n+1:ℝ):ℂ) • particleHead X f n (a • x.val) =
          a • ((Real.sqrt (n+1:ℝ):ℂ) • particleHead X f n x.val)
        rw [map_smul,smul_comm] }
    cont := by
      apply Continuous.subtype_mk
      fun_prop }
/-- Physical annihilation intertwines without an assumed CAR or an operator-bridge premise. -/
theorem source_single_intertwining {ι : Type v} (X : HilbertObject.{u})
    (b : HilbertBasis ι ℂ X.carrier) (e : ι ↪ ℕ) (n : ℕ) (i : ι)
    (ψ : particleExterior X b e (n+1)) :
    particleOccupation X b e n (sourceAnnihilate X b e n (b i) ψ) =
      countableAnnihilate n (e i) (particleOccupation X b e (n+1) ψ) := by
  have hc : particleAntiEmbedding X b e n (sourceAnnihilate X b e n (b i) ψ) =
      antiHead n (e i) (particleAntiEmbedding X b e (n+1) ψ) := by
    apply Subtype.ext
    ext t
    change particleCoordinates X b e n
      ((Real.sqrt (n+1:ℝ):ℂ) • particleHead X (b i) n ψ.val) t = _
    rw [map_smul]
    change (Real.sqrt (n+1:ℝ):ℂ) *
      particleCoordinates X b e n (particleHead X (b i) n ψ.val) t =
      (Real.sqrt (n+1:ℝ):ℂ) * tensorSlice n (e i) _ t
    rw [particleHead_coordinates,tensorSlice_apply]
    rfl
  change (slaterHilbertBasis n).repr
    (particleAntiEmbedding X b e n (sourceAnnihilate X b e n (b i) ψ)) =
    countableAnnihilate n (e i) ((slaterHilbertBasis (n+1)).repr
      (particleAntiEmbedding X b e (n+1) ψ))
  rw [hc,antiHead_intertwining]
/-- O1, including the N=2 contraction into the scalar vacuum. -/
private theorem source_pair_intertwining {ι : Type v} (X : HilbertObject.{u})
    (b : HilbertBasis ι ℂ X.carrier) (e : ι ↪ ℕ) (n : ℕ) (i j : ι)
    (ψ : particleExterior X b e (n+2)) :
    particleOccupation X b e n
      (sourceAnnihilate X b e n (b j) (sourceAnnihilate X b e (n+1) (b i) ψ)) =
      pairContract (n+2) (e i) (e j) (particleOccupation X b e (n+2) ψ) := by
  rw [source_single_intertwining,source_single_intertwining,single_pair_composition]
end
section
open scoped Classical
open TopologicalSpace
universe u v
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [SeparableSpace H]
variable {ι : Type v}
structure AdaptedChart (e : ι ↪ ℕ) (v : ι × Fin 2 → H) where
  index : Set H
  basis : HilbertBasis index ℂ H
  label : index ↪ ℕ
  pairs : ι × Fin 2 → index
  basis_pair : ∀ p,basis (pairs p)=v p
  label_u : ∀ i,label (pairs (i,0))=4*e i
  label_v : ∀ i,label (pairs (i,1))=4*e i+1
/-- An adapted chart includes the entire Hilbert space, not only the active pairs. -/
private theorem adaptedChart_nonempty (e : ι ↪ ℕ) (v : ι × Fin 2 → H) (hv : Orthonormal ℂ v) :
    Nonempty (AdaptedChart e v) := by
  obtain ⟨w,b,hw,hb⟩ := adapted_hilbert_basis hv
  letI : Countable w := orthonormal_countable b.orthonormal
  obtain ⟨f,hf⟩ := exists_injective_nat w
  let g : w ↪ ℕ := ⟨f,hf⟩
  let label : w ↪ ℕ := ⟨adaptedLabel v e w g,adaptedLabel_injective e w g⟩
  let r : ι × Fin 2 → w := fun p => ⟨v p,hw ⟨p,rfl⟩⟩
  refine ⟨⟨w,b,label,r,(fun p => congrFun hb (r p)),?_,?_⟩⟩
  · intro i
    have h := adaptedLabel_on_pair hv.linearIndependent.injective e w g hw (i,0)
    change adaptedLabel v e w g ⟨v (i,0),hw ⟨(i,0),rfl⟩⟩=4*e i
    simpa [canonicalModeLabel] using h
  · intro i
    have h := adaptedLabel_on_pair hv.linearIndependent.injective e w g hw (i,1)
    change adaptedLabel v e w g ⟨v (i,1),hw ⟨(i,1),rfl⟩⟩=4*e i+1
    simpa [canonicalModeLabel] using h
def adaptedChart (e : ι ↪ ℕ) (v : ι × Fin 2 → H) (hv : Orthonormal ℂ v) : AdaptedChart e v :=
  Classical.choice (adaptedChart_nonempty e v hv)
/-- The source's canonical pair family is countable solely from separability. -/
theorem canonicalPair_countable (v : ι × Fin 2 → H) (hv : Orthonormal ℂ v) : Countable ι :=
  orthonormal_countable (hv.comp (fun i => (i,0)) (by intro i j h; exact (Prod.mk.inj h).1))
end
section
open scoped Classical BigOperators TensorProduct ENNReal
set_option backward.isDefEq.respectTransparency false
universe u v
variable {ι : Type v} (X : HilbertObject.{u}) (b : HilbertBasis ι ℂ X.carrier) (e : ι ↪ ℕ)
private instance particleExterior_complete (N : ℕ) : CompleteSpace (particleExterior X b e N) :=
  (show IsClosed (particleExterior X b e N : Set (particleObject X N).carrier) from by
    have he : (particleExterior X b e N : Set (particleObject X N).carrier) =
        (particleCoordinates X b e N) ⁻¹' (antisymmetricSubmodule N : Set _) := by
      ext ψ; exact particleExterior_coordinates_iff X b e N ψ
    rw [he]
    exact (antisymmetricSubmodule_closed N).preimage (particleCoordinates X b e N).continuous).completeSpace_coe
private theorem sourceAnnihilate_add (n : ℕ) (f g : X.carrier)
    (ψ : particleExterior X b e (n+1)) :
    sourceAnnihilate X b e n (f+g) ψ =
      sourceAnnihilate X b e n f ψ + sourceAnnihilate X b e n g ψ := by
  apply Subtype.ext
  change (Real.sqrt (n+1:ℝ):ℂ) • particleHead X (f+g) n ψ.val =
    (Real.sqrt (n+1:ℝ):ℂ) • particleHead X f n ψ.val +
      (Real.sqrt (n+1:ℝ):ℂ) • particleHead X g n ψ.val
  simp_rw [← particleHeadFamily_apply X b n]
  simp only [map_add,ContinuousLinearMap.add_apply,smul_add]
private theorem sourceAnnihilate_smul (n : ℕ) (a : ℂ) (f : X.carrier)
    (ψ : particleExterior X b e (n+1)) :
    sourceAnnihilate X b e n (a • f) ψ = star a • sourceAnnihilate X b e n f ψ := by
  apply Subtype.ext
  change (Real.sqrt (n+1:ℝ):ℂ) • particleHead X (a • f) n ψ.val =
    star a • ((Real.sqrt (n+1:ℝ):ℂ) • particleHead X f n ψ.val)
  simp_rw [← particleHeadFamily_apply X b n]
  simp only [map_smulₛₗ,starRingEnd_apply,ContinuousLinearMap.smul_apply]
  exact smul_comm (Real.sqrt (n+1:ℝ):ℂ) (star a) ((particleHeadFamily X n) f ψ.val)
private theorem sourceAnnihilate_continuous (n : ℕ) (ψ : particleExterior X b e (n+1)) :
    Continuous (fun f : X.carrier => sourceAnnihilate X b e n f ψ) := by
  apply Continuous.subtype_mk
  change Continuous (fun f : X.carrier => (Real.sqrt (n+1:ℝ):ℂ) • particleHead X f n ψ.val)
  simp_rw [← particleHeadFamily_apply X b n]
  exact ((ContinuousLinearMap.apply ℂ (particleObject X n).carrier ψ.val).continuous.comp
    (particleHeadFamily X n).continuous).const_smul _
/-- Creation is the Hilbert adjoint of the physical annihilator at an arbitrary vector. -/
def sourceCreate (n : ℕ) (f : X.carrier) :
    particleExterior X b e n →L[ℂ] particleExterior X b e (n+1) :=
  (sourceAnnihilate X b e n f).adjoint
private def sourcePair (n : ℕ) (ψ : particleExterior X b e (n+2)) (p : ι × ι) :
    particleExterior X b e n :=
  sourceAnnihilate X b e n (b p.2) (sourceAnnihilate X b e (n+1) (b p.1) ψ)
private theorem sourcePair_norm (n : ℕ) (ψ : particleExterior X b e (n+2)) (p : ι × ι) :
    ‖sourcePair X b e n ψ p‖ =
      ‖pairContract (n+2) (e p.1) (e p.2) (particleOccupation X b e (n+2) ψ)‖ := by
  rw [← (particleOccupation X b e n).norm_map]
  rw [sourcePair,source_pair_intertwining]
private def sourcePairNorms (n : ℕ) (ψ : particleExterior X b e (n+2)) : lp (fun _ : ι × ι => ℝ) 2 :=
  ⟨fun p => ‖sourcePair X b e n ψ p‖,memℓp_gen (by
    have hs := (ordered_pair_energies_summable (n+2) (particleOccupation X b e (n+2) ψ)).comp_injective
      (e.prodMap e).injective
    change Summable (fun p : ι × ι => ‖pairContract (n+2) (e p.1) (e p.2)
      (particleOccupation X b e (n+2) ψ)‖^2) at hs
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two,norm_norm,sourcePair_norm] using hs)⟩
private theorem sourceSeries_summable (n : ℕ) (ψ : particleExterior X b e (n+2))
    (φ : (UniformSpace.Completion (X.carrier ⊗[ℂ] X.carrier))) :
    Summable fun p : ι × ι => (tensorHilbertBasis b b).repr φ p • sourcePair X b e n ψ p := by
  apply Summable.of_norm
  have h := lp.summable_mul (p := 2) (q := 2) (by rw [Real.holderConjugate_iff]; norm_num)
    (lp.toNorm ((tensorHilbertBasis b b).repr φ)) (sourcePairNorms X b e n ψ)
  simpa only [norm_smul,lp.toNorm,sourcePairNorms,norm_norm] using h
/-- Physical contraction synthesis, defined with actual tensor contractions and no coordinate RDM. -/
private def sourceSynthesis (n : ℕ) (ψ : particleExterior X b e (n+2))
    (φ : (UniformSpace.Completion (X.carrier ⊗[ℂ] X.carrier))) : particleExterior X b e n :=
  ∑' p : ι × ι,(tensorHilbertBasis b b).repr φ p • sourcePair X b e n ψ p
private theorem sourceSynthesis_norm (n : ℕ) (ψ : particleExterior X b e (n+2))
    (φ : (UniformSpace.Completion (X.carrier ⊗[ℂ] X.carrier))) :
    ‖sourceSynthesis X b e n ψ φ‖ ≤ ‖sourcePairNorms X b e n ψ‖ * ‖φ‖ := by
  have hh := lp.tsum_mul_le_mul_norm' (p := 2) (q := 2)
    (by rw [Real.holderConjugate_iff]; norm_num) (lp.toNorm ((tensorHilbertBasis b b).repr φ)) (sourcePairNorms X b e n ψ)
  simp only [lp.toNorm,sourcePairNorms,norm_norm] at hh
  change (∑' p,‖(tensorHilbertBasis b b).repr φ p‖*‖sourcePair X b e n ψ p‖) ≤
    ‖lp.toNorm ((tensorHilbertBasis b b).repr φ)‖ * ‖sourcePairNorms X b e n ψ‖ at hh
  rw [lp.norm_toNorm,LinearIsometryEquiv.norm_map] at hh
  calc
    _ ≤ ∑' p,‖(tensorHilbertBasis b b).repr φ p‖*‖sourcePair X b e n ψ p‖ := by
      have hs := lp.summable_mul (p := 2) (q := 2) (by rw [Real.holderConjugate_iff]; norm_num)
        (lp.toNorm ((tensorHilbertBasis b b).repr φ)) (sourcePairNorms X b e n ψ)
      have hn : Summable (fun p : ι × ι =>
        ‖(tensorHilbertBasis b b).repr φ p • sourcePair X b e n ψ p‖) := by
        simpa only [norm_smul,lp.toNorm,sourcePairNorms,norm_norm] using hs
      simpa only [sourceSynthesis,norm_smul] using norm_tsum_le_tsum_norm hn
    _ ≤ _ := by simpa only [mul_comm] using hh
private def sourceSynthesisLinear (n : ℕ) (ψ : particleExterior X b e (n+2)) :
    (UniformSpace.Completion (X.carrier ⊗[ℂ] X.carrier)) →ₗ[ℂ] particleExterior X b e n where
  toFun := sourceSynthesis X b e n ψ
  map_add' φ χ := by
    simp only [sourceSynthesis,map_add,lp.coeFn_add,Pi.add_apply,add_smul]
    exact (sourceSeries_summable X b e n ψ φ).tsum_add (sourceSeries_summable X b e n ψ χ)
  map_smul' a φ := by
    simp only [sourceSynthesis,map_smul,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,mul_smul]
    exact (sourceSeries_summable X b e n ψ φ).tsum_const_smul a
private def sourceSynthesisCLM (n : ℕ) (ψ : particleExterior X b e (n+2)) :
    (UniformSpace.Completion (X.carrier ⊗[ℂ] X.carrier)) →L[ℂ] particleExterior X b e n :=
  (sourceSynthesisLinear X b e n ψ).mkContinuous ‖sourcePairNorms X b e n ψ‖
    (sourceSynthesis_norm X b e n ψ)
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
private def basisConjugate {κ : Type*} (a : HilbertBasis κ ℂ E) (x : E) : E :=
  a.repr.symm (star (a.repr x))
private theorem basisConjugate_norm {κ : Type*} (a : HilbertBasis κ ℂ E) (x : E) :
    ‖basisConjugate a x‖=‖x‖ := by simp [basisConjugate]
private theorem basisConjugate_inner {κ : Type*} (a : HilbertBasis κ ℂ E) (x y : E) :
    inner ℂ (basisConjugate a x) (basisConjugate a y)=inner ℂ y x := by
  rw [← a.repr.inner_map_map]
  simp only [basisConjugate,LinearIsometryEquiv.apply_symm_apply]
  rw [inner_star_star_countable,LinearIsometryEquiv.inner_map_map]
private def sourceGramLinear (n : ℕ) (ψ : particleExterior X b e (n+2)) :
    (UniformSpace.Completion (X.carrier ⊗[ℂ] X.carrier)) →ₗ[ℂ] (particleObject X n).carrier where
  toFun φ := basisConjugate (particleBasis X b n)
    (sourceSynthesisCLM X b e n ψ (basisConjugate (tensorHilbertBasis b b) φ)).val
  map_add' φ χ := by
    simp [basisConjugate,map_add]
  map_smul' a φ := by
    simp [basisConjugate,map_smul,star_smul]
private def sourceGramCLM (n : ℕ) (ψ : particleExterior X b e (n+2)) :
    (UniformSpace.Completion (X.carrier ⊗[ℂ] X.carrier)) →L[ℂ] (particleObject X n).carrier :=
  (sourceGramLinear X b e n ψ).mkContinuous ‖sourcePairNorms X b e n ψ‖ (by
    intro φ
    change ‖basisConjugate _ _‖ ≤ _
    rw [basisConjugate_norm]
    exact (sourceSynthesis_norm X b e n ψ (basisConjugate (tensorHilbertBasis b b) φ)).trans_eq
      (by rw [basisConjugate_norm]))
end
section
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
universe u v
/-- Coordinate padding preserves conjugation in the chosen real Hilbert basis. -/
private theorem coordinateRename_star {A B : Type*} (e : A ↪ B) (ψ : lp (fun _ : A => ℂ) 2) :
    coordinateRename e (star ψ)=star (coordinateRename e ψ) := by
  ext j
  rw [lp.star_apply]
  by_cases hj : j∈Set.range e
  · obtain ⟨i,rfl⟩ := hj
    rw [coordinateRename_image,coordinateRename_image,lp.star_apply]
  · rw [coordinateRename_outside _ _ _ hj,coordinateRename_outside _ _ _ hj,star_zero]
variable {ι : Type v} (X : HilbertObject.{u}) (b : HilbertBasis ι ℂ X.carrier) (e : ι ↪ ℕ)
private theorem tensorConjugate_coordinates (φ : (UniformSpace.Completion (X.carrier ⊗[ℂ] X.carrier))) :
    tensorCoordinateEmbedding b e (basisConjugate (tensorHilbertBasis b b) φ) =
      star (tensorCoordinateEmbedding b e φ) := by
  change coordinateRename (e.prodMap e) ((tensorHilbertBasis b b).repr
    ((tensorHilbertBasis b b).repr.symm (star ((tensorHilbertBasis b b).repr φ)))) = _
  rw [LinearIsometryEquiv.apply_symm_apply,coordinateRename_star]
  rfl
/-- The independently constructed physical synthesis intertwines with every coordinate contraction. -/
private theorem sourceSynthesis_transport (n : ℕ) (ψ : particleExterior X b e (n+2))
    (φ : (UniformSpace.Completion (X.carrier ⊗[ℂ] X.carrier))) :
    particleOccupation X b e n (sourceSynthesis X b e n ψ φ) =
      tensorSynthesis (n+2) (particleOccupation X b e (n+2) ψ) (tensorCoordinateEmbedding b e φ) := by
  change (particleOccupation X b e n).toContinuousLinearMap
    (∑' p : ι × ι,(tensorHilbertBasis b b).repr φ p • sourcePair X b e n ψ p) = _
  rw [ContinuousLinearMap.map_tsum _ (sourceSeries_summable X b e n ψ φ)]
  simp only [map_smul,LinearIsometry.coe_toContinuousLinearMap,sourcePair,source_pair_intertwining]
  have him (p : ι × ι) : tensorCoordinateEmbedding b e φ ((e.prodMap e) p) =
      (tensorHilbertBasis b b).repr φ p :=
    coordinateRename_image (e.prodMap e) ((tensorHilbertBasis b b).repr φ) p
  have hout (p : ℕ × ℕ) (hp : p∉Set.range (e.prodMap e)) :
      tensorCoordinateEmbedding b e φ p=0 :=
    coordinateRename_outside (e.prodMap e) ((tensorHilbertBasis b b).repr φ) p hp
  have he := (e.prodMap e).injective.tsum_eq
    (f := fun p : ℕ × ℕ => tensorCoordinateEmbedding b e φ p •
      pairContract (n+2) p.1 p.2 (particleOccupation X b e (n+2) ψ)) (by
        intro p hp
        by_contra ho
        apply hp
        change tensorCoordinateEmbedding b e φ p •
          pairContract (n+2) p.1 p.2 (particleOccupation X b e (n+2) ψ)=0
        rw [hout p ho,zero_smul])
  change (∑' p : ι × ι,tensorCoordinateEmbedding b e φ ((e.prodMap e) p) •
      pairContract (n+2) (e p.1) (e p.2) (particleOccupation X b e (n+2) ψ)) =
    tensorSynthesis (n+2) (particleOccupation X b e (n+2) ψ) (tensorCoordinateEmbedding b e φ) at he
  simp_rw [him] at he
  exact he
/-- Physical synthesis on a product Hilbert-basis tensor is literally the double contraction. -/
private theorem sourceSynthesis_basis (n : ℕ) (ψ : particleExterior X b e (n+2)) (p : ι × ι) :
    sourceSynthesis X b e n ψ (tensorHilbertBasis b b p)=sourcePair X b e n ψ p := by
  simp only [sourceSynthesis,HilbertBasis.repr_self]
  simp [lp.single_apply,Pi.single_apply]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
private theorem basisConjugate_basis {κ : Type*} (a : HilbertBasis κ ℂ E) (i : κ) :
    basisConjugate a (a i)=a i := by
  apply a.repr.injective
  simp only [basisConjugate,LinearIsometryEquiv.apply_symm_apply,HilbertBasis.repr_self]
  ext j
  simp [lp.star_apply,lp.single_apply,Pi.single_apply]
end
section
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
universe u v
variable {ι : Type v} (X : HilbertObject.{u}) (b : HilbertBasis ι ℂ X.carrier) (e : ι ↪ ℕ)
private theorem eq_of_hilbertBasis_semilinear {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    {κ : Type*} (a : HilbertBasis κ ℂ E) (T U : E → F)
    (hT : Continuous T) (hU : Continuous U)
    (hT0 : T 0=0) (hU0 : U 0=0)
    (hTa : ∀ x y,T (x+y)=T x+T y) (hUa : ∀ x y,U (x+y)=U x+U y)
    (hTs : ∀ (c : ℂ) x,T (c • x)=star c • T x)
    (hUs : ∀ (c : ℂ) x,U (c • x)=star c • U x)
    (h : ∀ i,T (a i)=U (a i)) : ∀ x,T x=U x := by
  let K : Submodule ℂ E :=
    { carrier := {x | T x=U x}
      zero_mem' := hT0.trans hU0.symm
      add_mem' := by intro x y hx hy; simp only [Set.mem_setOf_eq] at *; rw [hTa,hUa,hx,hy]
      smul_mem' := by intro c x hx; simp only [Set.mem_setOf_eq] at *; rw [hTs,hUs,hx] }
  have hs : Submodule.span ℂ (Set.range a) ≤ K := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact h i
  have ht := (Submodule.span ℂ (Set.range a)).topologicalClosure_minimal hs (isClosed_eq hT hU)
  rw [a.dense_span] at ht
  intro x
  exact ht (Submodule.mem_top : x∈(⊤ : Submodule ℂ E))
private theorem sourceGram_tmul (n : ℕ) (ψ : particleExterior X b e (n+2))
    (f g : X.carrier) :
    basisConjugate (particleBasis X b n)
      (sourceGramCLM X b e n ψ ((f ⊗ₜ[ℂ] g : X.carrier ⊗[ℂ] X.carrier) :
        Completion (X.carrier ⊗[ℂ] X.carrier))) =
      (sourceAnnihilate X b e n g (sourceAnnihilate X b e (n+1) f ψ)).val := by
  have hbase (i j : ι) :
      basisConjugate (particleBasis X b n)
        (sourceGramCLM X b e n ψ ((b i ⊗ₜ[ℂ] b j : X.carrier ⊗[ℂ] X.carrier) :
          Completion (X.carrier ⊗[ℂ] X.carrier))) =
        (sourceAnnihilate X b e n (b j) (sourceAnnihilate X b e (n+1) (b i) ψ)).val := by
    change basisConjugate (particleBasis X b n)
      (sourceGramCLM X b e n ψ (tensorBasisVector b b (i,j))) = _
    rw [← tensorHilbertBasis_apply]
    change basisConjugate _ (basisConjugate _
      (sourceSynthesis X b e n ψ (basisConjugate (tensorHilbertBasis b b) (tensorHilbertBasis b b (i,j)))).val) = _
    rw [basisConjugate_basis,sourceSynthesis_basis]
    simp only [basisConjugate,LinearIsometryEquiv.apply_symm_apply,
      star_star,LinearIsometryEquiv.symm_apply_apply]
    rfl
  have hg (i : ι) : ∀ g : X.carrier,
      basisConjugate (particleBasis X b n)
        (sourceGramCLM X b e n ψ ((b i ⊗ₜ[ℂ] g : X.carrier ⊗[ℂ] X.carrier) :
          Completion (X.carrier ⊗[ℂ] X.carrier))) =
        (sourceAnnihilate X b e n g (sourceAnnihilate X b e (n+1) (b i) ψ)).val := by
    apply eq_of_hilbertBasis_semilinear b
    · unfold basisConjugate; fun_prop
    · exact continuous_subtype_val.comp (sourceAnnihilate_continuous X b e n _)
    · simp [basisConjugate,Completion.coe_zero]
    · have h := sourceAnnihilate_smul X b e n 0 (0:X.carrier) (sourceAnnihilate X b e (n+1) (b i) ψ)
      simpa only [zero_smul,star_zero,Subtype.ext_iff,ZeroMemClass.coe_zero] using h
    · intro x y; simp [basisConjugate,map_add,TensorProduct.tmul_add,Completion.coe_add]
    · intro x y; exact congrArg Subtype.val (sourceAnnihilate_add X b e n x y _)
    · intro a x; simp [basisConjugate,TensorProduct.tmul_smul,map_smul,star_smul,Completion.coe_smul]
    · intro a x; exact congrArg Subtype.val (sourceAnnihilate_smul X b e n a x _)
    · exact hbase i
  refine eq_of_hilbertBasis_semilinear b
    (fun f : X.carrier => basisConjugate (particleBasis X b n)
      (sourceGramCLM X b e n ψ ((f ⊗ₜ[ℂ] g : X.carrier ⊗[ℂ] X.carrier) : Completion _)))
    (fun f : X.carrier => (sourceAnnihilate X b e n g
      (sourceAnnihilate X b e (n+1) f ψ)).val) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ f
  · unfold basisConjugate; fun_prop
  · exact continuous_subtype_val.comp ((sourceAnnihilate X b e n g).continuous.comp
      (sourceAnnihilate_continuous X b e (n+1) ψ))
  · simp [basisConjugate,Completion.coe_zero]
  · have h := sourceAnnihilate_smul X b e (n+1) 0 (0:X.carrier) ψ
    have hz : sourceAnnihilate X b e (n+1) 0 ψ=0 := by simpa only [zero_smul,star_zero] using h
    rw [hz,map_zero]; rfl
  · intro x y; simp [basisConjugate,map_add,TensorProduct.add_tmul,Completion.coe_add]
  · intro x y; rw [sourceAnnihilate_add,map_add]; rfl
  · intro a x; simp [basisConjugate,TensorProduct.smul_tmul,map_smul,star_smul,Completion.coe_smul]
  · intro a x; rw [sourceAnnihilate_smul,map_smul]; rfl
  · intro i; exact hg i g
private theorem sourceGram_kernel_arbitrary (n : ℕ) (ψ : particleExterior X b e (n+2))
    (f₁ f₂ g₁ g₂ : X.carrier) :
    inner ℂ ((f₁ ⊗ₜ[ℂ] f₂ : X.carrier ⊗[ℂ] X.carrier) : Completion (X.carrier ⊗[ℂ] X.carrier))
      (((sourceGramCLM X b e n ψ).adjoint.comp (sourceGramCLM X b e n ψ))
        ((g₁ ⊗ₜ[ℂ] g₂ : X.carrier ⊗[ℂ] X.carrier) : Completion (X.carrier ⊗[ℂ] X.carrier))) =
      inner ℂ ψ (sourceCreate X b e (n+1) g₁
        (sourceCreate X b e n g₂ (sourceAnnihilate X b e n f₂
          (sourceAnnihilate X b e (n+1) f₁ ψ)))) := by
  rw [ContinuousLinearMap.comp_apply,ContinuousLinearMap.adjoint_inner_right]
  rw [← basisConjugate_inner (particleBasis X b n)
    (sourceGramCLM X b e n ψ ((g₁ ⊗ₜ[ℂ] g₂ : X.carrier ⊗[ℂ] X.carrier) : Completion _))
    (sourceGramCLM X b e n ψ ((f₁ ⊗ₜ[ℂ] f₂ : X.carrier ⊗[ℂ] X.carrier) : Completion _))]
  rw [sourceGram_tmul,sourceGram_tmul]
  rw [sourceCreate,ContinuousLinearMap.adjoint_inner_right,
    sourceCreate,ContinuousLinearMap.adjoint_inner_right]
  rfl
private theorem sourceGamma_exists (n : ℕ) (ψ : particleExterior X b e (n+2)) :
    ∃ Γ : Completion (X.carrier ⊗[ℂ] X.carrier) →L[ℂ] Completion (X.carrier ⊗[ℂ] X.carrier),
      ∀ f₁ f₂ g₁ g₂ : X.carrier,
        inner ℂ ((f₁ ⊗ₜ[ℂ] f₂ : X.carrier ⊗[ℂ] X.carrier) : Completion (X.carrier ⊗[ℂ] X.carrier))
          (Γ ((g₁ ⊗ₜ[ℂ] g₂ : X.carrier ⊗[ℂ] X.carrier) : Completion (X.carrier ⊗[ℂ] X.carrier))) =
        inner ℂ ψ (sourceCreate X b e (n+1) g₁
          (sourceCreate X b e n g₂ (sourceAnnihilate X b e n f₂
            (sourceAnnihilate X b e (n+1) f₁ ψ)))) :=
  ⟨(sourceGramCLM X b e n ψ).adjoint.comp (sourceGramCLM X b e n ψ),
    sourceGram_kernel_arbitrary X b e n ψ⟩
/-- Equation (1.1) defines the bounded operator by its arbitrary-vector creation/annihilation kernel. -/
def sourceGamma (n : ℕ) (ψ : particleExterior X b e (n+2)) :
    Completion (X.carrier ⊗[ℂ] X.carrier) →L[ℂ] Completion (X.carrier ⊗[ℂ] X.carrier) :=
  Classical.choose (sourceGamma_exists X b e n ψ)
private theorem sourceGamma_eq_gram (n : ℕ) (ψ : particleExterior X b e (n+2)) :
    sourceGamma X b e n ψ =
      (sourceGramCLM X b e n ψ).adjoint.comp (sourceGramCLM X b e n ψ) := by
  apply ContinuousLinearMap.ext_on (s := Set.range (tensorHilbertBasis b b))
  · rw [dense_iff_closure_eq,← Submodule.topologicalClosure_coe,(tensorHilbertBasis b b).dense_span]
    rfl
  · rintro _ ⟨q,rfl⟩
    apply (tensorHilbertBasis b b).repr.injective
    ext p
    rw [HilbertBasis.repr_apply_apply,HilbertBasis.repr_apply_apply]
    simp only [tensorHilbertBasis_apply,tensorBasisVector]
    exact (Classical.choose_spec (sourceGamma_exists X b e n ψ) (b p.1) (b p.2) (b q.1) (b q.2)).trans
      (sourceGram_kernel_arbitrary X b e n ψ (b p.1) (b p.2) (b q.1) (b q.2)).symm
def sourceRayleigh (n : ℕ) (ψ : particleExterior X b e (n+2))
    (φ : (UniformSpace.Completion (X.carrier ⊗[ℂ] X.carrier))) : ℝ :=
  (inner ℂ φ (sourceGamma X b e n ψ φ)).re
private theorem sourceRayleigh_contraction (n : ℕ) (ψ : particleExterior X b e (n+2))
    (φ : (UniformSpace.Completion (X.carrier ⊗[ℂ] X.carrier))) :
    sourceRayleigh X b e n ψ φ =
      ‖sourceSynthesis X b e n ψ (basisConjugate (tensorHilbertBasis b b) φ)‖^2 := by
  rw [sourceRayleigh,sourceGamma_eq_gram,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right]
  have he : (inner ℂ (sourceGramCLM X b e n ψ φ) (sourceGramCLM X b e n ψ φ)).re =
      ‖sourceGramCLM X b e n ψ φ‖^2 := (norm_sq_eq_re_inner (𝕜 := ℂ) _).symm
  rw [he]
  change ‖basisConjugate _ _‖^2= _
  rw [basisConjugate_norm]
  rfl
/-- Physical and coordinate RDM expectations agree for every completed source two-tensor. -/
theorem sourceRayleigh_transport (n : ℕ) (ψ : particleExterior X b e (n+2))
    (φ : (UniformSpace.Completion (X.carrier ⊗[ℂ] X.carrier))) :
    sourceRayleigh X b e n ψ φ =
      completedRayleigh (n+2) (particleOccupation X b e (n+2) ψ) (tensorCoordinateEmbedding b e φ) := by
  rw [sourceRayleigh_contraction,completedRayleigh_contraction]
  rw [← (particleOccupation X b e n).norm_map,sourceSynthesis_transport,tensorConjugate_coordinates]
/-- The source RDM has the usual reverse Gram kernel of actual sqrt-normalized contractions. -/
private theorem sourceGamma_kernel (n : ℕ) (ψ : particleExterior X b e (n+2)) (p q : ι × ι) :
    inner ℂ (tensorHilbertBasis b b p) (sourceGamma X b e n ψ (tensorHilbertBasis b b q)) =
      inner ℂ (sourcePair X b e n ψ q) (sourcePair X b e n ψ p) := by
  rw [sourceGamma_eq_gram,ContinuousLinearMap.comp_apply,ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ (basisConjugate (particleBasis X b n)
    (sourceSynthesis X b e n ψ (basisConjugate (tensorHilbertBasis b b) (tensorHilbertBasis b b p))).val)
    (basisConjugate (particleBasis X b n)
    (sourceSynthesis X b e n ψ (basisConjugate (tensorHilbertBasis b b) (tensorHilbertBasis b b q))).val) = _
  rw [basisConjugate_basis,basisConjugate_basis,sourceSynthesis_basis,sourceSynthesis_basis,basisConjugate_inner]
  rfl
/-- A genuine source tensor has no amplitude at a tuple using nonexistent padded modes. -/
private theorem particleCoordinates_outside (N : ℕ) (ψ : (particleObject X N).carrier) (t : Fin N → ℕ)
    (ht : t∉Set.range ((Function.Embedding.arrowCongrRight (γ := Fin N) e))) : particleCoordinates X b e N ψ t=0 := by
  cases N <;> exact coordinateRename_outside _ _ _ ht
/-- The Slater embedding carries the vacuum condition on every mode absent from the source. -/
private theorem particleOccupation_outside (N : ℕ) (ψ : particleExterior X b e N)
    (S : ({s : Finset ℕ // s.card = N})) (k : ℕ) (hk : k∈S.val) (he : k∉Set.range e) :
    particleOccupation X b e N ψ S=0 := by
  change (slaterHilbertBasis N).repr (particleAntiEmbedding X b e N ψ) S=0
  rw [HilbertBasis.repr_apply_apply,slaterBasis_apply]
  change inner ℂ (slaterVector N S) (particleCoordinates X b e N ψ.val)=0
  have ha : IsAntisymmetric N (particleCoordinates X b e N ψ.val) := (particleExterior_coordinates_iff X b e N ψ.val).mp ψ.property
  rw [slater_inner_antisymmetric N S _ ha]
  have ht : occupationTuple N S 1∉Set.range ((Function.Embedding.arrowCongrRight (γ := Fin N) e)) := by
    rintro ⟨t,ht⟩
    let q := (S.val.orderIsoOfFin S.property).symm ⟨k,hk⟩
    have hq : S.val.orderEmbOfFin S.property q=k :=
      congrArg Subtype.val ((S.val.orderIsoOfFin S.property).apply_symm_apply ⟨k,hk⟩)
    apply he
    refine ⟨t q,?_⟩
    have h := congrFun ht q
    change e (t q)=S.val.orderEmbOfFin S.property q at h
    exact h.trans hq
  rw [particleCoordinates_outside X b e N ψ.val _ ht,mul_zero]
/-- Any contraction involving a missing padded mode is the zero vector. -/
private theorem padded_pair_zero (n : ℕ) (ψ : particleExterior X b e (n+2)) (p : ℕ × ℕ)
    (hp : p∉Set.range (e.prodMap e)) :
    pairContract (n+2) p.1 p.2 (particleOccupation X b e (n+2) ψ)=0 := by
  have ho : p.1∉Set.range e ∨ p.2∉Set.range e := by
    by_contra h
    push_neg at h
    obtain ⟨i,hi⟩ := h.1
    obtain ⟨j,hj⟩ := h.2
    exact hp ⟨(i,j),Prod.ext hi hj⟩
  ext R
  rw [pairContract_apply]
  unfold pairCoordinate
  split_ifs with h
  · have hz : particleOccupation X b e (n+2) ψ
        ⟨insert p.1 (insert p.2 R.val),h.2.2.2⟩=0 := by
      rcases ho with hi|hj
      · apply particleOccupation_outside X b e (n+2) ψ _ p.1
        · simp
        · exact hi
      · apply particleOccupation_outside X b e (n+2) ψ _ p.2
        · simp
        · exact hj
    rw [hz,mul_zero]
    rfl
  · rfl
/-- The physical contractions have total mass N(N-1), with every spectator mode retained. -/
private theorem sourcePair_trace (n : ℕ) (ψ : particleExterior X b e (n+2)) :
    (∑' p : ι × ι,‖sourcePair X b e n ψ p‖^2)=((n+2)*(n+1):ℕ)*‖ψ‖^2 := by
  simp_rw [sourcePair_norm]
  have he := (e.prodMap e).injective.tsum_eq
    (f := fun p : ℕ × ℕ => ‖pairContract (n+2) p.1 p.2
      (particleOccupation X b e (n+2) ψ)‖^2) (by
        intro p hp
        by_contra ho
        apply hp
        change ‖pairContract (n+2) p.1 p.2 (particleOccupation X b e (n+2) ψ)‖^2=0
        rw [padded_pair_zero X b e n ψ p ho]
        simp)
  have hleft : (∑' p : ι × ι,‖pairContract (n+2) (e p.1) (e p.2)
      (particleOccupation X b e (n+2) ψ)‖^2) =
      ∑' p : ℕ × ℕ,‖pairContract (n+2) p.1 p.2 (particleOccupation X b e (n+2) ψ)‖^2 := by
    change (∑' p : ι × ι,‖pairContract (n+2) (e p.1) (e p.2)
      (particleOccupation X b e (n+2) ψ)‖^2) =
      ∑' p : ℕ × ℕ,‖pairContract (n+2) p.1 p.2 (particleOccupation X b e (n+2) ψ)‖^2 at he
    exact he
  rw [hleft,countable_ordered_pair_trace,(particleOccupation X b e (n+2)).norm_map]
  rfl
end
section
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
universe u v
variable {ι : Type v} (X : HilbertObject.{u}) (b : HilbertBasis ι ℂ X.carrier) (e : ι ↪ ℕ)
/-- The physical positive RDM has exactly trace N(N-1); this is the source normalization. -/
theorem sourceGamma_trace (n : ℕ) (ψ : particleExterior X b e (n+2)) :
    (∑' p : ι × ι,
      (inner ℂ (tensorHilbertBasis b b p) (sourceGamma X b e n ψ (tensorHilbertBasis b b p))).re) =
      ((n+2)*(n+1):ℕ)*‖ψ‖^2 := by
  have he (p : ι × ι) :
      (inner ℂ (tensorHilbertBasis b b p) (sourceGamma X b e n ψ (tensorHilbertBasis b b p))).re =
        ‖sourcePair X b e n ψ p‖^2 := by
    rw [sourceGamma_kernel]
    exact (norm_sq_eq_re_inner (𝕜 := ℂ) _).symm
  simp_rw [he]
  exact sourcePair_trace X b e n ψ
end
end D5.S3.Quantum.FermionicCorrelationalBound.PhysicalContractionRdmBridge
