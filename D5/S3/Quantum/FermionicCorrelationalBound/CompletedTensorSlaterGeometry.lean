/- GID: D5/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry
   generality: I
   mirror-B: D5/B/S3/Quantum/FermionicCorrelationalBound/CompletedTensorSlaterGeometry
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Completed tensor powers, physical permutations and Slater completeness. -/
/-
Admission witness: D5.S3.Quantum.FermionicCorrelationalBound.CompletedTensorSlaterGeometry.tensorHead_basis_coordinates.
exists_pair_preserving_tensor: proof_shape: content; escape_witness: OccupationHilbertContractions.tensorBasisVector_dense; consumer: CompletedTensorSlaterGeometry.sourcePairWedge_orthonormal.
sourcePairWedge_orthonormal: proof_shape: bind-only; escape_witness: none; consumer: CompletedTensorSlaterGeometry.sourceCanonicalFamily, CompletedTensorSlaterGeometry.sourceCanonicalFamily_coordinates, CompletedTensorSlaterGeometry.sourceCanonicalFamily_series.
extendedCoeff_image: proof_shape: bind-only; escape_witness: none; consumer: CompletedTensorSlaterGeometry.extendedCoeff_moment, CompletedTensorSlaterGeometry.familySequence, CompletedTensorSlaterGeometry.familySequence_cap, CompletedTensorSlaterGeometry.sourceCanonicalFamily_coordinates.
extendedCoeff_outside: proof_shape: bind-only; escape_witness: none; consumer: CompletedTensorSlaterGeometry.extendedCoeff_moment, CompletedTensorSlaterGeometry.familySequence, CompletedTensorSlaterGeometry.familySequence_cap, CompletedTensorSlaterGeometry.sourceCanonicalFamily_coordinates.
extendedCoeff_moment: proof_shape: bind-only; escape_witness: none; consumer: CompletedTensorSlaterGeometry.familySequence, SourceCorrelationalBound.source_cap_result.
familySequence_cap: proof_shape: bind-only; escape_witness: none; consumer: SourceCorrelationalBound.source_cap_result.
sourceCanonicalFamily_series: proof_shape: bind-only; escape_witness: none; consumer: CompletedTensorSlaterGeometry.sourceCanonicalFamily_coordinates, SourceCorrelationalBound.source_cap_result.
sourceCanonicalFamily_coordinates: proof_shape: bind-only; escape_witness: none; consumer: SourceCorrelationalBound.source_cap_result.
occupationTuple_eq_iff: proof_shape: bind-only; escape_witness: none; consumer: CompletedTensorSlaterGeometry.slaterVector_orthonormal.
permutationPhase_norm: proof_shape: bind-only; escape_witness: none; consumer: CompletedTensorSlaterGeometry.slaterVector_orthonormal, CompletedTensorSlaterGeometry.slater_inner_antisymmetric.
slaterVector_eq_sum: proof_shape: bind-only; escape_witness: none; consumer: CompletedTensorSlaterGeometry.slaterVector_apply, CompletedTensorSlaterGeometry.slaterVector_orthonormal, CompletedTensorSlaterGeometry.slater_inner_antisymmetric.
slaterVector_orthonormal: proof_shape: bind-only; escape_witness: none; consumer: CompletedTensorSlaterGeometry.slaterAntiVector_orthonormal.
permutationPhase_mul: proof_shape: bind-only; escape_witness: none; consumer: CompletedTensorSlaterGeometry.slaterVector_antisymmetric.
slaterVector_apply: proof_shape: bind-only; escape_witness: none; consumer: CompletedTensorSlaterGeometry.slaterVector_antisymmetric.
occupationTuple_mul: proof_shape: bind-only; escape_witness: none; consumer: CompletedTensorSlaterGeometry.slaterVector_antisymmetric.
slaterVector_antisymmetric: proof_shape: bind-only; escape_witness: none; consumer: CompletedTensorSlaterGeometry.slaterAntiVector.
antisymmetricSubmodule_closed: proof_shape: bind-only; escape_witness: none; consumer: CompletedTensorSlaterGeometry.antisymmetricComplete, PhysicalContractionRdmBridge.particleExterior_complete, PhysicalContractionRdmBridge.particleHead_antisymmetric.
tuple_occupation_exists: proof_shape: bind-only; escape_witness: none; consumer: CompletedTensorSlaterGeometry.antisymmetric_orthogonal_slaters_zero.
antisymmetric_repeated_zero: proof_shape: bind-only; escape_witness: none; consumer: CompletedTensorSlaterGeometry.antisymmetric_orthogonal_slaters_zero, PhysicalContractionRdmBridge.head_repeated_zero.
slater_inner_antisymmetric: proof_shape: bind-only; escape_witness: none; consumer: CompletedTensorSlaterGeometry.antisymmetric_orthogonal_slaters_zero, PhysicalContractionRdmBridge.antiHead_intertwining, PhysicalContractionRdmBridge.particleOccupation_outside.
antisymmetric_orthogonal_slaters_zero: proof_shape: bind-only; escape_witness: none; consumer: CompletedTensorSlaterGeometry.slaterAntiVector_dense.
antisymmetricComplete: proof_shape: bind-only; escape_witness: none; consumer: CompletedTensorSlaterGeometry.slaterHilbertBasis, PhysicalContractionRdmBridge.slaterBasis_apply.
slaterAntiVector_orthonormal: proof_shape: bind-only; escape_witness: none; consumer: CompletedTensorSlaterGeometry.slaterHilbertBasis, PhysicalContractionRdmBridge.slaterBasis_apply.
slaterAntiVector_dense: proof_shape: bind-only; escape_witness: none; consumer: CompletedTensorSlaterGeometry.slaterHilbertBasis, PhysicalContractionRdmBridge.slaterBasis_apply.
tensorHead_tmul: proof_shape: bind-only; escape_witness: none; consumer: CompletedTensorSlaterGeometry.tensorHead_adjoint, CompletedTensorSlaterGeometry.tensorHead_basis_coordinates.
tensorHilbertBasis_repr_tmul: proof_shape: bind-only; escape_witness: none; consumer: CompletedTensorSlaterGeometry.tensorPure_repr.
clm_eq_of_hilbertBasis: proof_shape: bind-only; escape_witness: none; consumer: CompletedTensorSlaterGeometry.tensorHead_adjoint, CompletedTensorSlaterGeometry.tensorHead_basis_coordinates.
tensorHead_basis_coordinates: proof_shape: content; escape_witness: OccupationHilbertContractions.tensorBasisVector_dense; consumer: PhysicalContractionRdmBridge.particleHead_repr.
tensorHead_adjoint: proof_shape: content; escape_witness: OccupationHilbertContractions.tensorBasisVector_dense; consumer: PhysicalContractionRdmBridge.particleHeadFamily_apply.
tupleBasis_repr: proof_shape: bind-only; escape_witness: none; consumer: CompletedTensorSlaterGeometry.tensorPure_repr, PhysicalContractionRdmBridge.particleHead_repr.
tensorPure_repr: proof_shape: content; escape_witness: CompletedTensorSlaterGeometry.tensorPure_repr; consumer: CompletedTensorSlaterGeometry.tensorPermutation_product.
tensorPermutation_repr: proof_shape: bind-only; escape_witness: none; consumer: CompletedTensorSlaterGeometry.sourceTensorCoordinates_permutation, CompletedTensorSlaterGeometry.tensorPermutation_product.
tensorPermutation_product: proof_shape: content; escape_witness: CompletedTensorSlaterGeometry.tensorPure_repr; purpose: physical tensor convention.
sourceTensorCoordinates_permutation: proof_shape: bind-only; escape_witness: none; consumer: CompletedTensorSlaterGeometry.sourceExteriorCoordinates_iff_physical.
sourceExteriorCoordinates_iff_physical: proof_shape: bind-only; escape_witness: none; consumer: CompletedTensorSlaterGeometry.sourceTensorCoordinates_antisymmetric.
sourceTensorCoordinates_antisymmetric: proof_shape: bind-only; escape_witness: none; consumer: PhysicalContractionRdmBridge.particleExterior_coordinates_iff.
admission_basis: escape-witness
Direct frozen dependencies:
  none; same-delivery prerequisites are not baseline frozen dependencies.
Information-escape registration is paused.
-/
import D5.S3.Quantum.FermionicCorrelationalBound.CanonicalRdmAndPadding
noncomputable section
open scoped Classical BigOperators TensorProduct ComplexConjugate Matrix
namespace D5.S3.Quantum.FermionicCorrelationalBound.CompletedTensorSlaterGeometry
open D5.S3.Quantum.FermionicCorrelationalBound.CanonicalRdmAndPadding D5.S3.Quantum.FermionicCorrelationalBound.OccupationHilbertContractions
section
open scoped TensorProduct BigOperators Classical
open UniformSpace TopologicalSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] [SeparableSpace E]
private theorem exists_pair_preserving_tensor {ι : Type*} (e : ι ↪ ℕ)
    {v : ι × Fin 2 → E} (hv : Orthonormal ℂ v) :
    ∃ T : (UniformSpace.Completion (E ⊗[ℂ] E)) →ₗᵢ[ℂ] (lp (fun _ : ℕ×ℕ => ℂ) 2),
      ∀ i,T (sourcePairWedge v i) = orderedPairWedge (2 * e i) := by
  obtain ⟨w,b,hw,hb⟩ := adapted_hilbert_basis hv
  letI : Countable w := orthonormal_countable b.orthonormal
  obtain ⟨f,hf⟩ := exists_injective_nat w
  let g : w ↪ ℕ := ⟨f,hf⟩
  let label : w ↪ ℕ := ⟨adaptedLabel v e w g,adaptedLabel_injective e w g⟩
  let r : ι × Fin 2 → w := fun p => ⟨v p,hw ⟨p,rfl⟩⟩
  refine ⟨tensorCoordinateEmbedding b label,?_⟩
  intro i
  apply tensorCoordinateEmbedding_sourcePairWedge v b label r
    (fun p => congrFun hb (r p)) (fun i => 2 * e i)
  · intro j
    have h := adaptedLabel_on_pair hv.linearIndependent.injective e w g hw (j,0)
    change adaptedLabel v e w g ⟨v (j,0),hw ⟨(j,0),rfl⟩⟩ = 2*(2*e j)
    rw [h]
    simp [canonicalModeLabel]
    omega
  · intro j
    have h := adaptedLabel_on_pair hv.linearIndependent.injective e w g hw (j,1)
    change adaptedLabel v e w g ⟨v (j,1),hw ⟨(j,1),rfl⟩⟩ = 2*(2*e j)+1
    rw [h]
    simp [canonicalModeLabel]
    omega
private theorem sourcePairWedge_orthonormal {ι : Type*} (e : ι ↪ ℕ)
    {v : ι × Fin 2 → E} (hv : Orthonormal ℂ v) :
    Orthonormal ℂ (sourcePairWedge v) := by
  obtain ⟨T,hT⟩ := exists_pair_preserving_tensor e hv
  have hi : Function.Injective (fun i => 2 * e i) := by
    intro i j h
    change 2 * e i = 2 * e j at h
    apply e.injective
    omega
  have hon := orderedPairWedge_orthonormal.comp (fun i => 2 * e i) hi
  rw [orthonormal_iff_ite] at hon ⊢
  intro i j
  rw [← T.inner_map_map,hT,hT]
  exact hon i j
end
section
open scoped BigOperators Classical TensorProduct
set_option backward.isDefEq.respectTransparency false
/-- Canonical coefficients on an arbitrary finite or countable pair carrier. -/
structure CanonicalFamily (ι : Type*) where
  coeff : ι → ℝ
  nonneg : ∀ i,0 ≤ coeff i
  summable_sq : Summable fun i => coeff i^2
  mass : (∑' i,coeff i^2)=1
variable {ι : Type*}
private theorem extendedCoeff_image (e : ι ↪ ℕ) (c : CanonicalFamily ι) (i : ι) :
    (Function.extend e c.coeff (fun _ => 0)) (e i)=c.coeff i := e.injective.extend_apply _ _ _
private theorem extendedCoeff_outside (e : ι ↪ ℕ) (c : CanonicalFamily ι) (j : ℕ)
    (hj : j∉Set.range e) : (Function.extend e c.coeff (fun _ => 0)) j=0 := by
  exact Function.extend_apply' _ _ _ hj
theorem extendedCoeff_moment (e : ι ↪ ℕ) (c : CanonicalFamily ι) (k : ℕ) (hk : 0<k) :
    (∑' j,(Function.extend e c.coeff (fun _ => 0)) j^k)=∑' i,c.coeff i^k := by
  have h := e.injective.tsum_eq (f := fun j => (Function.extend e c.coeff (fun _ => 0)) j^k) (by
    intro j hj
    by_contra ho
    apply hj
    change (Function.extend e c.coeff (fun _ => 0)) j^k=0
    rw [extendedCoeff_outside e c j ho]
    exact zero_pow (Nat.ne_of_gt hk))
  simpa only [Function.comp_def,extendedCoeff_image] using h.symm
def familySequence (e : ι ↪ ℕ) (c : CanonicalFamily ι) : CanonicalSequence where
  coeff := Function.extend e c.coeff (fun _ => 0)
  nonneg j := by
    by_cases hj : j∈Set.range e
    · obtain ⟨i,rfl⟩ := hj
      rw [extendedCoeff_image]
      exact c.nonneg i
    · rw [extendedCoeff_outside e c j hj]
  summable_sq := by
    apply (e.injective.summable_iff (fun j hj => by rw [extendedCoeff_outside e c j hj]; norm_num)).mp
    simpa only [Function.comp_def,extendedCoeff_image] using c.summable_sq
  mass := (extendedCoeff_moment e c 2 (by omega)).trans c.mass
theorem familySequence_cap (e : ι ↪ ℕ) (c : CanonicalFamily ι) (α : ℝ)
    (hα : 0≤α) (hc : ∀ i,c.coeff i^2≤α) : ∀ j,(familySequence e c).coeff j^2≤α := by
  intro j
  change (Function.extend e c.coeff (fun _ => 0)) j^2≤α
  by_cases hj : j∈Set.range e
  · obtain ⟨i,rfl⟩ := hj
    rw [extendedCoeff_image]
    exact hc i
  · rw [extendedCoeff_outside e c j hj]
    simpa using hα
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] [TopologicalSpace.SeparableSpace E]
def familyCoefficients (c : CanonicalFamily ι) : lp (fun _ : ι => ℂ) 2 :=
  ⟨fun i => (c.coeff i:ℂ),memℓp_gen (by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two,Complex.norm_real,Real.norm_eq_abs,sq_abs]
      using c.summable_sq)⟩
/-- The given canonical form, synthesized in the actual completed source tensor. -/
def sourceCanonicalFamily (e : ι ↪ ℕ) (v : ι × Fin 2 → E) (hv : Orthonormal ℂ v)
    (c : CanonicalFamily ι) : (UniformSpace.Completion (E ⊗[ℂ] E)) :=
  (sourcePairWedge_orthonormal e hv).orthogonalFamily.linearIsometry (familyCoefficients c)
theorem sourceCanonicalFamily_series (e : ι ↪ ℕ) (v : ι × Fin 2 → E) (hv : Orthonormal ℂ v)
    (c : CanonicalFamily ι) :
    sourceCanonicalFamily e v hv c = ∑' i,(c.coeff i:ℂ) • sourcePairWedge v i := by
  rw [sourceCanonicalFamily,OrthogonalFamily.linearIsometry_apply]
  rfl
/-- An adapted basis transports every finite or countable canonical family without fictitious source modes. -/
theorem sourceCanonicalFamily_coordinates {κ : Type*} (e : ι ↪ ℕ)
    (v : ι × Fin 2 → E) (hv : Orthonormal ℂ v) (c : CanonicalFamily ι)
    (b : HilbertBasis κ ℂ E) (label : κ ↪ ℕ) (r : ι × Fin 2 → κ)
    (hb : ∀ p,b (r p)=v p) (h0 : ∀ i,label (r (i,0))=4*e i)
    (h1 : ∀ i,label (r (i,1))=4*e i+1) :
    tensorCoordinateEmbedding b label (sourceCanonicalFamily e v hv c) =
      canonicalTensor (padCanonicalSequence (familySequence e c)) := by
  have hs : Summable (fun i => (c.coeff i:ℂ) • sourcePairWedge v i) := by
    simpa only [LinearIsometry.toSpanSingleton_apply,familyCoefficients] using
      (sourcePairWedge_orthonormal e hv).orthogonalFamily.summable_of_lp (familyCoefficients c)
  have hT (i : ι) : tensorCoordinateEmbedding b label (sourcePairWedge v i)=orderedPairWedge (2*e i) := by
    apply tensorCoordinateEmbedding_sourcePairWedge v b label r hb (fun i => 2*e i)
    · intro i
      rw [h0]
      omega
    · intro i
      rw [h1]
      omega
  rw [sourceCanonicalFamily_series]
  change (tensorCoordinateEmbedding b label).toContinuousLinearMap (∑' i,(c.coeff i:ℂ) • sourcePairWedge v i)= _
  rw [ContinuousLinearMap.map_tsum _ hs]
  simp only [map_smul,LinearIsometry.coe_toContinuousLinearMap,hT]
  rw [canonicalTensor,OrthogonalFamily.linearIsometry_apply]
  simp only [LinearIsometry.toSpanSingleton_apply,canonicalCoefficients]
  let f : ι → ℕ := fun i => 2*e i
  have hi : Function.Injective f := by
    intro i j h
    apply e.injective
    dsimp [f] at h
    omega
  have hz : ∀ j,j∉Set.range f →
      ((padCanonicalSequence (familySequence e c)).coeff j:ℂ) • orderedPairWedge j=0 := by
    intro j hj
    change (paddedCoeff (Function.extend e c.coeff (fun _ => 0)) j:ℂ) • orderedPairWedge j=0
    by_cases he : j%2=0
    · have ho : j/2∉Set.range e := by
        rintro ⟨i,hi⟩
        apply hj
        refine ⟨i,?_⟩
        dsimp [f]
        omega
      simp [paddedCoeff,he,extendedCoeff_outside e c (j/2) ho]
    · simp [paddedCoeff,he]
  have he := hi.tsum_eq (f := fun j => ((padCanonicalSequence (familySequence e c)).coeff j:ℂ) • orderedPairWedge j)
    (by intro j hj; by_contra ho; exact hj (hz j ho))
  simpa only [Function.comp_def,f,padCanonicalSequence,familySequence,paddedCoeff_even,extendedCoeff_image] using he
end
section
open scoped Classical TensorProduct
set_option backward.isDefEq.respectTransparency false
universe u v
structure HilbertObject where
  carrier : Type u
  normed : NormedAddCommGroup carrier
  innerProduct : @InnerProductSpace ℂ carrier (inferInstance : RCLike ℂ) normed.toSeminormedAddCommGroup
  complete : @CompleteSpace carrier normed.toUniformSpace
attribute [instance] HilbertObject.normed HilbertObject.innerProduct HilbertObject.complete
def sourceHilbertObject (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] : HilbertObject where
  carrier := E
  normed := inferInstance
  innerProduct := inferInstance
  complete := inferInstance
def tensorHilbertObject (X Y : HilbertObject.{u}) : HilbertObject.{u} where
  carrier := (UniformSpace.Completion (X.carrier ⊗[ℂ] Y.carrier))
  normed := inferInstance
  innerProduct := inferInstance
  complete := inferInstance
/-- The tower index n represents n+1 actual completed Hilbert tensor factors. -/
def tensorTower (X : HilbertObject.{u}) : ℕ → HilbertObject.{u}
  | 0 => X
  | n+1 => tensorHilbertObject X (tensorTower X n)
def TensorTowerIndex (ι : Type v) : ℕ → Type v
  | 0 => ι
  | n+1 => ι × TensorTowerIndex ι n
def tensorTowerBasis {ι : Type v} (X : HilbertObject.{u}) (b : HilbertBasis ι ℂ X.carrier) :
    (n : ℕ) → HilbertBasis (TensorTowerIndex ι n) ℂ (tensorTower X n).carrier
  | 0 => b
  | n+1 => tensorHilbertBasis b (tensorTowerBasis X b n)
def tensorTowerTupleEquiv (ι : Type v) : (n : ℕ) → TensorTowerIndex ι n ≃ (Fin (n+1) → ι)
  | 0 => (Equiv.funUnique (Fin 1) ι).symm
  | n+1 => (Equiv.prodCongr (Equiv.refl ι) (tensorTowerTupleEquiv ι n)).trans
      (Fin.consEquiv (fun _ : Fin (n+2) => ι))
def coordinateEquiv {A B : Type*} (e : A ≃ B) :
    lp (fun _ : A => ℂ) 2 ≃ₗᵢ[ℂ] lp (fun _ : B => ℂ) 2 :=
  LinearIsometryEquiv.ofSurjective (coordinateRename e.toEmbedding) (by
    intro ψ
    refine ⟨coordinateRename e.symm.toEmbedding ψ,?_⟩
    ext b
    have h1 := coordinateRename_image e.toEmbedding (coordinateRename e.symm.toEmbedding ψ) (e.symm b)
    have h2 := coordinateRename_image e.symm.toEmbedding ψ b
    change coordinateRename e.toEmbedding (coordinateRename e.symm.toEmbedding ψ) (e (e.symm b)) =
      coordinateRename e.symm.toEmbedding ψ (e.symm b) at h1
    rw [e.apply_symm_apply] at h1
    exact h1.trans h2)
/-- Every completed positive tensor power has all ordered Hilbert-basis tuples as coordinates. -/
def tensorTowerTupleBasis {ι : Type v} (X : HilbertObject.{u})
    (b : HilbertBasis ι ℂ X.carrier) (n : ℕ) :
    HilbertBasis (Fin (n+1) → ι) ℂ (tensorTower X n).carrier :=
  HilbertBasis.ofRepr ((tensorTowerBasis X b n).repr.trans
    (coordinateEquiv (tensorTowerTupleEquiv ι n)))
end
section
open scoped BigOperators Classical
def occupationTuple (N : ℕ) (S : ({s : Finset ℕ // s.card = N})) (σ : Equiv.Perm (Fin N)) : Fin N → ℕ :=
  fun i => S.val.orderEmbOfFin S.property (σ i)
private theorem occupationTuple_eq_iff (N : ℕ) (S T : ({s : Finset ℕ // s.card = N}))
    (σ τ : Equiv.Perm (Fin N)) :
    occupationTuple N S σ = occupationTuple N T τ ↔ S=T ∧ σ=τ := by
  constructor
  · intro h
    have hr := congrArg Set.range h
    have hS : Set.range (occupationTuple N S σ) = S.val := by
      change Set.range ((S.val.orderEmbOfFin S.property) ∘ σ) = _
      rw [σ.surjective.range_comp,Finset.range_orderEmbOfFin]
    have hT : Set.range (occupationTuple N T τ) = T.val := by
      change Set.range ((T.val.orderEmbOfFin T.property) ∘ τ) = _
      rw [τ.surjective.range_comp,Finset.range_orderEmbOfFin]
    rw [hS,hT] at hr
    have he : S = T := Subtype.ext (Finset.coe_injective hr)
    subst T
    refine ⟨rfl,?_⟩
    apply Equiv.ext
    intro i
    exact (S.val.orderEmbOfFin S.property).injective (congrFun h i)
  · rintro ⟨rfl,rfl⟩
    rfl
def permutationPhase (N : ℕ) (σ : Equiv.Perm (Fin N)) : ℂ := ((σ.sign : ℤ) : ℂ)
private theorem permutationPhase_norm (N : ℕ) (σ : Equiv.Perm (Fin N)) :
    permutationPhase N σ * (starRingEnd ℂ) (permutationPhase N σ) = 1 := by
  have h : σ.sign = 1 ∨ σ.sign = -1 := Int.units_eq_one_or (σ.sign)
  rcases h with h | h <;> simp [permutationPhase,h]
set_option maxHeartbeats 1000000 in
def slaterVector (N : ℕ) (S : {s : Finset ℕ // s.card=N}) : lp (fun _ : Fin N → ℕ => ℂ) 2 := by
  let w : (Fin N → ℕ) → ℂ := ((Real.sqrt (N.factorial:ℝ):ℂ)⁻¹) •
    MultilinearMap.alternatization
      (MultilinearMap.piFamily (R:=ℂ) (κ:=fun _ : Fin N => ℕ) (M:=fun _ _ => ℂ) (N:=fun _ => ℂ)
        fun _t : Fin N → ℕ => MultilinearMap.mkPiAlgebra ℂ (Fin N) ℂ)
      (fun i => Pi.single (S.val.orderEmbOfFin S.property i) 1)
  let z : lp (fun _ : Fin N → ℕ => ℂ) 2 := ((Real.sqrt (N.factorial:ℝ):ℂ)⁻¹) •
    ∑ σ : Equiv.Perm (Fin N), permutationPhase N σ • lp.single 2 (occupationTuple N S σ) (1:ℂ)
  have h : w = (z : (Fin N → ℕ) → ℂ) := by
    symm
    funext t
    dsimp only [w,z]
    simp only [lp.coeFn_smul,Pi.smul_apply,MultilinearMap.alternatization_apply,
      MultilinearMap.domDomCongr_apply,lp.coeFn_sum,Finset.sum_apply]
    congr 1
    apply Finset.sum_congr rfl
    intro σ _
    rw [MultilinearMap.piFamily_single]
    simp only [MultilinearMap.mkPiAlgebra_apply,Finset.prod_const_one]
    simp [permutationPhase,lp.single_apply,Units.smul_def,zsmul_eq_mul]
    rfl
  exact ⟨w,h.symm ▸ lp.memℓp z⟩
private theorem slaterVector_eq_sum (N : ℕ) (S : {s : Finset ℕ // s.card=N}) : slaterVector N S = ((Real.sqrt (N.factorial:ℝ):ℂ)⁻¹) •
    ∑ σ : Equiv.Perm (Fin N), permutationPhase N σ •
      (lp.single 2 (occupationTuple N S σ) (1:ℂ) : lp (fun _ : Fin N → ℕ => ℂ) 2) := by
  apply lp.ext
  funext t
  change _ = (((Real.sqrt (N.factorial:ℝ):ℂ)⁻¹) •
    ∑ σ : Equiv.Perm (Fin N), permutationPhase N σ •
      (lp.single 2 (occupationTuple N S σ) (1:ℂ) : lp (fun _ : Fin N → ℕ => ℂ) 2)) t
  simp only [slaterVector]
  simp only [lp.coeFn_smul,Pi.smul_apply,MultilinearMap.alternatization_apply,
    MultilinearMap.domDomCongr_apply,lp.coeFn_sum,Finset.sum_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  rw [MultilinearMap.piFamily_single]
  simp only [MultilinearMap.mkPiAlgebra_apply,Finset.prod_const_one]
  simp [permutationPhase,lp.single_apply,Units.smul_def,zsmul_eq_mul]
  rfl
private theorem slaterVector_orthonormal (N : ℕ) : Orthonormal ℂ (slaterVector N) := by
  rw [orthonormal_iff_ite]
  intro S T
  have hfac : (0:ℝ) < N.factorial := by exact_mod_cast Nat.factorial_pos N
  have hne : (Real.sqrt (N.factorial:ℝ):ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr hfac))
  have hsqrt : (Real.sqrt (N.factorial:ℝ):ℂ)^2 = (N.factorial:ℂ) := by
    exact_mod_cast Real.sq_sqrt hfac.le
  simp only [slaterVector_eq_sum,inner_smul_left,inner_smul_right,sum_inner,inner_sum,
    lp.inner_single_left,lp.single_apply,Pi.single_apply,RCLike.inner_apply]
  have hsign : (starRingEnd ℂ) ((Real.sqrt (N.factorial:ℝ):ℂ)⁻¹) =
      (Real.sqrt (N.factorial:ℝ):ℂ)⁻¹ := by simp
  rw [hsign]
  by_cases hST : S=T
  · subst T
    simp [occupationTuple_eq_iff,permutationPhase_norm,Fintype.card_perm,mul_ite,ite_mul,
      ← Finset.mul_sum,← mul_assoc]
    field_simp
    rw [← Finset.sum_div]
    simp only [permutationPhase_norm,Finset.sum_const,Finset.card_univ,Fintype.card_perm,
      Fintype.card_fin,nsmul_eq_mul,mul_one]
    apply (div_eq_iff hne).mpr
    linear_combination -hsqrt
  · have htuple : ∀ σ τ, occupationTuple N S σ ≠ occupationTuple N T τ := by
      intro σ τ h
      exact hST ((occupationTuple_eq_iff N S T σ τ).mp h).1
    simp [htuple,hST]
end
section
open scoped BigOperators Classical
private theorem permutationPhase_mul (N : ℕ) (σ τ : Equiv.Perm (Fin N)) :
    permutationPhase N (σ*τ) = permutationPhase N σ * permutationPhase N τ := by
  simp [permutationPhase,Equiv.Perm.sign_mul]
private theorem slaterVector_apply (N : ℕ) (S : ({s : Finset ℕ // s.card = N})) (t : Fin N → ℕ) :
    slaterVector N S t = ((Real.sqrt (N.factorial:ℝ):ℂ)⁻¹) *
      ∑ σ : Equiv.Perm (Fin N),permutationPhase N σ *
        (if t=occupationTuple N S σ then 1 else 0) := by
  simp only [slaterVector_eq_sum,lp.coeFn_smul,Pi.smul_apply,lp.coeFn_sum,Finset.sum_apply,
    smul_eq_mul,lp.single_apply,Pi.single_apply]
def IsAntisymmetric (N : ℕ) (ψ : (lp (fun _ : Fin N → ℕ => ℂ) 2)) : Prop :=
  ∀ (t : Fin N → ℕ) (σ : Equiv.Perm (Fin N)),
    ψ (t ∘ σ) = permutationPhase N σ * ψ t
private theorem occupationTuple_mul (N : ℕ) (S : ({s : Finset ℕ // s.card = N}))
    (σ τ : Equiv.Perm (Fin N)) :
    occupationTuple N S (τ*σ) = occupationTuple N S τ ∘ σ := by
  funext i
  rfl
private theorem slaterVector_antisymmetric (N : ℕ) (S : ({s : Finset ℕ // s.card = N})) :
    IsAntisymmetric N (slaterVector N S) := by
  intro t σ
  rw [slaterVector_apply,slaterVector_apply]
  have hre : ∀ τ : Equiv.Perm (Fin N),
      (t ∘ σ = occupationTuple N S (τ*σ)) ↔ t=occupationTuple N S τ := by
    intro τ
    rw [occupationTuple_mul]
    constructor
    · intro h
      funext i
      simpa only [Function.comp_apply,σ.apply_symm_apply] using congrFun h (σ.symm i)
    · intro h
      rw [h]
  have he := Fintype.sum_equiv (Equiv.mulRight σ)
    (fun τ : Equiv.Perm (Fin N) => permutationPhase N (τ*σ) *
      (if t ∘ σ=occupationTuple N S (τ*σ) then (1:ℂ) else 0))
    (fun τ : Equiv.Perm (Fin N) => permutationPhase N τ *
      (if t ∘ σ=occupationTuple N S τ then (1:ℂ) else 0)) (fun τ => rfl)
  rw [← he]
  simp only [hre,permutationPhase_mul]
  have hsum : (∑ τ : Equiv.Perm (Fin N),
      (permutationPhase N τ * permutationPhase N σ) *
        (if t=occupationTuple N S τ then (1:ℂ) else 0)) =
      permutationPhase N σ * ∑ τ : Equiv.Perm (Fin N),
        permutationPhase N τ * (if t=occupationTuple N S τ then (1:ℂ) else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro τ _
    ring
  rw [hsum]
  ring
def antisymmetricSubmodule (N : ℕ) : Submodule ℂ ((lp (fun _ : Fin N → ℕ => ℂ) 2)) where
  carrier := {ψ | IsAntisymmetric N ψ}
  zero_mem' := by intro t σ; simp
  add_mem' := by
    intro x y hx hy t σ
    simp only [lp.coeFn_add,Pi.add_apply,hx t σ,hy t σ,mul_add]
  smul_mem' := by
    intro a x hx t σ
    simp only [lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,hx t σ]
    ring
theorem antisymmetricSubmodule_closed (N : ℕ) : IsClosed (antisymmetricSubmodule N : Set ((lp (fun _ : Fin N → ℕ => ℂ) 2))) := by
  change IsClosed {ψ : (lp (fun _ : Fin N → ℕ => ℂ) 2) | ∀ (t : Fin N → ℕ) (σ : Equiv.Perm (Fin N)),
    ψ (t ∘ σ)=permutationPhase N σ * ψ t}
  simp only [Set.setOf_forall]
  apply isClosed_iInter
  intro t
  apply isClosed_iInter
  intro σ
  apply isClosed_eq
  · exact (lp.evalCLM (fun _ : Fin N → ℕ => ℂ) 2 (𝕜 := ℂ) (t ∘ σ)).continuous
  · exact continuous_const.mul (lp.evalCLM (fun _ : Fin N → ℕ => ℂ) 2 (𝕜 := ℂ) t).continuous
end
section
open scoped BigOperators Classical
private theorem tuple_occupation_exists (N : ℕ) (t : Fin N → ℕ) (ht : Function.Injective t) :
    ∃ (S : ({s : Finset ℕ // s.card = N})) (σ : Equiv.Perm (Fin N)), t=occupationTuple N S σ := by
  let S : ({s : Finset ℕ // s.card = N}) := ⟨Finset.univ.image t,by
    rw [Finset.card_image_of_injective _ ht,Finset.card_univ,Fintype.card_fin]⟩
  let f : Fin N → S.val := fun i => ⟨t i,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j h
      exact ht (congrArg Subtype.val h)
    · intro y
      obtain ⟨i,_,hi⟩ := Finset.mem_image.mp y.property
      exact ⟨i,Subtype.ext hi⟩
  let σ : Equiv.Perm (Fin N) := (Equiv.ofBijective f hf).trans (S.val.orderIsoOfFin S.property).symm.toEquiv
  refine ⟨S,σ,?_⟩
  funext i
  change (f i).val = (S.val.orderIsoOfFin S.property (σ i)).val
  rw [show S.val.orderIsoOfFin S.property (σ i) = f i from
    (S.val.orderIsoOfFin S.property).apply_symm_apply (f i)]
theorem antisymmetric_repeated_zero (N : ℕ) (ψ : (lp (fun _ : Fin N → ℕ => ℂ) 2)) (hψ : IsAntisymmetric N ψ)
    (t : Fin N → ℕ) (ht : ¬Function.Injective t) : ψ t = 0 := by
  unfold Function.Injective at ht
  push_neg at ht
  obtain ⟨i,j,he,hne⟩ := ht
  have hs : t ∘ Equiv.swap i j = t := by
    funext k
    exact Equiv.apply_swap_eq_self he k
  have h := hψ t (Equiv.swap i j)
  rw [hs] at h
  have hphase : permutationPhase N (Equiv.swap i j) = -1 := by
    simp [permutationPhase,Equiv.Perm.sign_swap hne]
  rw [hphase] at h
  linear_combination (1/2:ℂ) * h
theorem slater_inner_antisymmetric (N : ℕ) (S : ({s : Finset ℕ // s.card = N}))
    (ψ : (lp (fun _ : Fin N → ℕ => ℂ) 2)) (hψ : IsAntisymmetric N ψ) :
    inner ℂ (slaterVector N S) ψ = (Real.sqrt (N.factorial:ℝ):ℂ) *
      ψ (occupationTuple N S 1) := by
  have he : ∀ σ : Equiv.Perm (Fin N),
      ψ (occupationTuple N S σ) = permutationPhase N σ * ψ (occupationTuple N S 1) := by
    intro σ
    have h := hψ (occupationTuple N S 1) σ
    have ht : occupationTuple N S 1 ∘ σ = occupationTuple N S σ := by funext i; rfl
    rw [ht] at h
    exact h
  simp only [slaterVector_eq_sum,inner_smul_left,sum_inner,lp.inner_single_left,RCLike.inner_apply]
  simp only [map_one,mul_one]
  have hp : ∀ σ : Equiv.Perm (Fin N),
      (starRingEnd ℂ) (permutationPhase N σ) * permutationPhase N σ = 1 := by
    intro σ
    rw [mul_comm]
    exact permutationPhase_norm N σ
  have hsum : (∑ σ : Equiv.Perm (Fin N),
      (starRingEnd ℂ) (permutationPhase N σ) * ψ (occupationTuple N S σ)) =
      ∑ _σ : Equiv.Perm (Fin N),ψ (occupationTuple N S 1) := by
    apply Finset.sum_congr rfl
    intro σ _
    rw [he σ,← mul_assoc,hp σ,one_mul]
  rw [hsum]
  have hsqrt : (Real.sqrt (N.factorial:ℝ):ℂ)^2 = (N.factorial:ℂ) := by
    exact_mod_cast Real.sq_sqrt (by exact_mod_cast (Nat.factorial_pos N).le)
  have hne : (Real.sqrt (N.factorial:ℝ):ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr (by exact_mod_cast Nat.factorial_pos N)))
  simp only [← mul_assoc,hp,one_mul,map_inv₀,Complex.conj_ofReal]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_perm,Fintype.card_fin,nsmul_eq_mul]
  field_simp
  linear_combination -ψ (occupationTuple N S 1) * hsqrt
theorem antisymmetric_orthogonal_slaters_zero (N : ℕ) (ψ : (lp (fun _ : Fin N → ℕ => ℂ) 2))
    (hψ : IsAntisymmetric N ψ) (horth : ∀ S,inner ℂ (slaterVector N S) ψ=0) : ψ=0 := by
  ext t
  by_cases ht : Function.Injective t
  · obtain ⟨S,σ,rfl⟩ := tuple_occupation_exists N t ht
    have h := horth S
    rw [slater_inner_antisymmetric N S ψ hψ] at h
    have hne : (Real.sqrt (N.factorial:ℝ):ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr (by exact_mod_cast Nat.factorial_pos N)))
    have hz := (mul_eq_zero.mp h).resolve_left hne
    have he := hψ (occupationTuple N S 1) σ
    have ht : occupationTuple N S 1 ∘ σ=occupationTuple N S σ := by funext i; rfl
    rw [ht,hz,mul_zero] at he
    exact he
  · exact antisymmetric_repeated_zero N ψ hψ t ht
instance antisymmetricComplete (N : ℕ) : CompleteSpace (antisymmetricSubmodule N) :=
  (antisymmetricSubmodule_closed N).completeSpace_coe
def slaterAntiVector (N : ℕ) (S : ({s : Finset ℕ // s.card = N})) : antisymmetricSubmodule N :=
  ⟨slaterVector N S,slaterVector_antisymmetric N S⟩
theorem slaterAntiVector_orthonormal (N : ℕ) : Orthonormal ℂ (slaterAntiVector N) := by
  rw [orthonormal_iff_ite]
  intro S T
  exact (orthonormal_iff_ite.mp (slaterVector_orthonormal N)) S T
theorem slaterAntiVector_dense (N : ℕ) :
    (Submodule.span ℂ (Set.range (slaterAntiVector N)))ᗮ = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro ψ hψ
  have horth : ∀ S,inner ℂ (slaterVector N S) ψ.val=0 := by
    intro S
    exact (Submodule.mem_orthogonal _ _).mp hψ _ (Submodule.subset_span ⟨S,rfl⟩)
  have hz := antisymmetric_orthogonal_slaters_zero N ψ.val ψ.property horth
  have he : ψ=0 := Subtype.ext hz
  exact he ▸ Submodule.zero_mem _
/-- The completed occupation carrier is unitarily the full antisymmetric ordered coordinate space. -/
def slaterHilbertBasis (N : ℕ) : HilbertBasis (({s : Finset ℕ // s.card = N})) ℂ (antisymmetricSubmodule N) :=
  HilbertBasis.mkOfOrthogonalEqBot (slaterAntiVector_orthonormal N) (slaterAntiVector_dense N)
end
section
open scoped Classical
set_option backward.isDefEq.respectTransparency false
def sourceTensorCoordinates {ι : Type*} (X : HilbertObject) (b : HilbertBasis ι ℂ X.carrier)
    (e : ι ↪ ℕ) (n : ℕ) : (tensorTower X n).carrier →ₗᵢ[ℂ] (lp (fun _ : Fin (n+1) → ℕ => ℂ) 2) :=
  (coordinateRename ((Function.Embedding.arrowCongrRight (γ := Fin (n+1)) e))).comp
    (tensorTowerTupleBasis X b n).repr.toLinearIsometry
/-- The source exterior sector is the antisymmetric subspace of its actual completed tensor power. -/
private def sourceExteriorCoordinates {ι : Type*} (X : HilbertObject) (b : HilbertBasis ι ℂ X.carrier)
    (e : ι ↪ ℕ) (n : ℕ) : Submodule ℂ (tensorTower X n).carrier :=
  (antisymmetricSubmodule (n+1)).comap (sourceTensorCoordinates X b e n).toLinearMap
end
section
open scoped TensorProduct Classical
open UniformSpace
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
/-- First-factor Hilbert contraction, constructed on the algebraic tensor and extended. -/
def tensorHead (f : E) : (UniformSpace.Completion (E ⊗[ℂ] F)) →L[ℂ] F :=
  (((TensorProduct.lidIsometry ℂ F).toContinuousLinearEquiv.toContinuousLinearMap).comp
    ((innerSL ℂ f).rTensor F)).extend
    (Completion.toComplL : E ⊗[ℂ] F →L[ℂ] (UniformSpace.Completion (E ⊗[ℂ] F)))
private theorem tensorHead_tmul (f x : E) (y : F) :
    tensorHead f ((x ⊗ₜ[ℂ] y : E ⊗[ℂ] F) : (UniformSpace.Completion (E ⊗[ℂ] F))) = inner ℂ f x • y := by
  unfold tensorHead
  change ContinuousLinearMap.extend _ (Completion.toComplL : E ⊗[ℂ] F →L[ℂ] (UniformSpace.Completion (E ⊗[ℂ] F))) ((Completion.toComplL : E ⊗[ℂ] F →L[ℂ] (UniformSpace.Completion (E ⊗[ℂ] F))) (x ⊗ₜ[ℂ] y)) = _
  rw [ContinuousLinearMap.extend_eq _ (e := (Completion.toComplL : E ⊗[ℂ] F →L[ℂ] (UniformSpace.Completion (E ⊗[ℂ] F))))
    (by exact Completion.denseRange_coe) (by exact Completion.isUniformInducing_coe (E ⊗[ℂ] F))]
  simp [ContinuousLinearMap.comp_apply,TensorProduct.lidIsometry_apply,
    ContinuousLinearMap.rTensor_tmul]
private theorem tensorHilbertBasis_repr_tmul {ι κ : Type*} (b : HilbertBasis ι ℂ E)
    (c : HilbertBasis κ ℂ F) (x : E) (y : F) (i : ι) (j : κ) :
    (tensorHilbertBasis b c).repr ((x ⊗ₜ[ℂ] y : E ⊗[ℂ] F) : (UniformSpace.Completion (E ⊗[ℂ] F))) (i,j) =
      (b.repr x i) * (c.repr y j) := by
  rw [HilbertBasis.repr_apply_apply,tensorHilbertBasis_apply]
  simp only [tensorBasisVector,Completion.inner_coe,TensorProduct.inner_tmul,
    HilbertBasis.repr_apply_apply]
/-- Equality of bounded maps is decided on a complete Hilbert basis. -/
private theorem clm_eq_of_hilbertBasis {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
    {ι : Type*} (b : HilbertBasis ι ℂ E) (T U : E →L[ℂ] G)
    (h : ∀ i,T (b i)=U (b i)) : T=U  := by
  apply ContinuousLinearMap.ext_on (s := Set.range b) ?_ ?_
  · rw [dense_iff_closure_eq, ← Submodule.topologicalClosure_coe, b.dense_span]
    rfl
  · rintro _ ⟨i,rfl⟩
    exact h i
/-- Physical contraction reads the first Hilbert-basis coordinate without a hypothesis. -/
theorem tensorHead_basis_coordinates {ι κ : Type*} (b : HilbertBasis ι ℂ E)
    (c : HilbertBasis κ ℂ F) (i : ι) (ψ : (UniformSpace.Completion (E ⊗[ℂ] F))) (j : κ) :
    c.repr (tensorHead (b i) ψ) j = (tensorHilbertBasis b c).repr ψ (i,j) := by
  let T := (lp.evalCLM (fun _ : κ => ℂ) 2 (𝕜 := ℂ) j).comp
    (c.repr.toContinuousLinearEquiv.toContinuousLinearMap.comp (tensorHead (b i)))
  let U := (lp.evalCLM (fun _ : ι × κ => ℂ) 2 (𝕜 := ℂ) (i,j)).comp
    (tensorHilbertBasis b c).repr.toContinuousLinearEquiv.toContinuousLinearMap
  have he : T=U := by
    apply clm_eq_of_hilbertBasis (tensorHilbertBasis b c)
    intro p
    change c.repr (tensorHead (b i) (tensorHilbertBasis b c p)) j =
      (tensorHilbertBasis b c).repr (tensorHilbertBasis b c p) (i,j)
    rw [tensorHilbertBasis_apply]
    change c.repr (tensorHead (b i) ((b p.1 ⊗ₜ[ℂ] c p.2 : E ⊗[ℂ] F) : (UniformSpace.Completion (E ⊗[ℂ] F)))) j = _
    rw [tensorHead_tmul,HilbertBasis.repr_apply_apply]
    rw [← tensorHilbertBasis_apply b c p,(tensorHilbertBasis b c).repr_self]
    by_cases hi : i=p.1 <;> by_cases hj : j=p.2 <;>
      simp [inner_smul_right,orthonormal_iff_ite.mp b.orthonormal,
        orthonormal_iff_ite.mp c.orthonormal,lp.single_apply,Pi.single_apply,Prod.ext_iff,hi,hj,eq_comm,b.orthonormal.norm_eq_one,c.orthonormal.norm_eq_one]
  exact congrArg (fun V : (UniformSpace.Completion (E ⊗[ℂ] F)) →L[ℂ] ℂ => V ψ) he
/-- Physical head contraction is adjoint to insertion of its one-particle vector. -/
theorem tensorHead_adjoint {ι κ : Type*} (b : HilbertBasis ι ℂ E)
    (c : HilbertBasis κ ℂ F) (f : E) :
    tensorHead f = ((Completion.toComplL : (E ⊗[ℂ] F) →L[ℂ] Completion (E ⊗[ℂ] F)).comp
      (TensorProduct.mkL ℂ E F f)).adjoint := by
  apply clm_eq_of_hilbertBasis (tensorHilbertBasis b c)
  intro p
  rw [tensorHilbertBasis_apply]
  apply ext_inner_left ℂ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ y (tensorHead f ((b p.1 ⊗ₜ[ℂ] c p.2 : E ⊗[ℂ] F) : Completion (E ⊗[ℂ] F))) = _
  rw [tensorHead_tmul]
  simp [ContinuousLinearMap.comp_apply,TensorProduct.mkL_apply_apply,
    tensorBasisVector,Completion.inner_coe,TensorProduct.inner_tmul,inner_smul_right]
end
section
open scoped Classical TensorProduct BigOperators
open UniformSpace
set_option backward.isDefEq.respectTransparency false
universe u v
def tensorPure (X : HilbertObject.{u}) : (n : ℕ) → (Fin (n+1) → X.carrier) → (tensorTower X n).carrier
  | 0,x => x 0
  | n+1,x => ((x 0 ⊗ₜ[ℂ] tensorPure X n (Fin.tail x) :
      X.carrier ⊗[ℂ] (tensorTower X n).carrier) :
      (UniformSpace.Completion (X.carrier ⊗[ℂ] (tensorTower X n).carrier)))
theorem tupleBasis_repr {ι : Type v} (X : HilbertObject.{u})
    (b : HilbertBasis ι ℂ X.carrier) (n : ℕ) (ψ : (tensorTower X n).carrier)
    (t : Fin (n+1) → ι) :
    (tensorTowerTupleBasis X b n).repr ψ t =
      (tensorTowerBasis X b n).repr ψ ((tensorTowerTupleEquiv ι n).symm t) := by
  change coordinateRename (tensorTowerTupleEquiv ι n).toEmbedding
    ((tensorTowerBasis X b n).repr ψ) t = _
  have h := coordinateRename_image (tensorTowerTupleEquiv ι n).toEmbedding
    ((tensorTowerBasis X b n).repr ψ) ((tensorTowerTupleEquiv ι n).symm t)
  change coordinateRename (tensorTowerTupleEquiv ι n).toEmbedding
    ((tensorTowerBasis X b n).repr ψ)
    ((tensorTowerTupleEquiv ι n) ((tensorTowerTupleEquiv ι n).symm t)) = _ at h
  rw [Equiv.apply_symm_apply] at h
  exact h
/-- Actual product vectors have the product of the one-factor Hilbert coefficients. -/
private theorem tensorPure_repr {ι : Type v} (X : HilbertObject.{u})
    (b : HilbertBasis ι ℂ X.carrier) (n : ℕ) (x : Fin (n+1) → X.carrier)
    (t : Fin (n+1) → ι) :
    (tensorTowerTupleBasis X b n).repr (tensorPure X n x) t =
      ∏ k : Fin (n+1), b.repr (x k) (t k) := by
  rw [tupleBasis_repr]
  induction n with
  | zero =>
    change b.repr (x 0) (t default) = ∏ k : Fin 1,b.repr (x k) (t k)
    rw [Fintype.prod_unique]
    rfl
  | succ n ih =>
    change (tensorHilbertBasis b (tensorTowerBasis X b n)).repr
      ((x 0 ⊗ₜ[ℂ] tensorPure X n (Fin.tail x) :
      X.carrier ⊗[ℂ] (tensorTower X n).carrier) : (UniformSpace.Completion (_ ⊗[ℂ] _)))
      (t 0,(tensorTowerTupleEquiv ι n).symm (Fin.tail t)) = _
    rw [tensorHilbertBasis_repr_tmul,ih (Fin.tail x) (Fin.tail t)]
    conv_rhs => rw [Fin.prod_univ_succ]
    rfl
/-- The unique bounded extension of factor permutation from product tensors. -/
def tensorPermutation {ι : Type v} (X : HilbertObject.{u})
    (b : HilbertBasis ι ℂ X.carrier) (n : ℕ) (σ : Equiv.Perm (Fin (n+1))) :
    (tensorTower X n).carrier ≃ₗᵢ[ℂ] (tensorTower X n).carrier :=
  (tensorTowerTupleBasis X b n).repr.trans
    ((coordinateEquiv ((Equiv.arrowCongr σ (Equiv.refl ι)))).trans
      (tensorTowerTupleBasis X b n).repr.symm)
private theorem tensorPermutation_repr {ι : Type v} (X : HilbertObject.{u})
    (b : HilbertBasis ι ℂ X.carrier) (n : ℕ) (σ : Equiv.Perm (Fin (n+1)))
    (ψ : (tensorTower X n).carrier) (t : Fin (n+1) → ι) :
    (tensorTowerTupleBasis X b n).repr (tensorPermutation X b n σ ψ) t =
      (tensorTowerTupleBasis X b n).repr ψ (t ∘ σ) := by
  change (tensorTowerTupleBasis X b n).repr
    ((tensorTowerTupleBasis X b n).repr.symm
      (coordinateRename ((Equiv.arrowCongr σ (Equiv.refl ι))).toEmbedding
      ((tensorTowerTupleBasis X b n).repr ψ))) t = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  have h := coordinateRename_image ((Equiv.arrowCongr σ (Equiv.refl ι))).toEmbedding
    ((tensorTowerTupleBasis X b n).repr ψ) (t ∘ σ)
  have ht : (Equiv.arrowCongr σ (Equiv.refl ι)) (t ∘ σ) = t := by
    funext k
    simp [Equiv.arrowCongr]
  change coordinateRename ((Equiv.arrowCongr σ (Equiv.refl ι))).toEmbedding
    ((tensorTowerTupleBasis X b n).repr ψ) ((Equiv.arrowCongr σ (Equiv.refl ι)) (t ∘ σ)) = _ at h
  rw [ht] at h
  exact h
/-- Coordinate permutation is the physical permutation of every actual product tensor. -/
theorem tensorPermutation_product {ι : Type v} (X : HilbertObject.{u})
    (b : HilbertBasis ι ℂ X.carrier) (n : ℕ) (σ : Equiv.Perm (Fin (n+1)))
    (x : Fin (n+1) → X.carrier) :
    tensorPermutation X b n σ (tensorPure X n x) = tensorPure X n (x ∘ σ.symm) := by
  apply (tensorTowerTupleBasis X b n).repr.injective
  ext t
  rw [tensorPermutation_repr,tensorPure_repr,tensorPure_repr]
  exact Fintype.prod_equiv σ (fun k => b.repr (x k) (t (σ k)))
    (fun k => b.repr (x (σ.symm k)) (t k)) (fun k => by simp)
/-- Vacuum padding commutes with actual factor permutation, including spectator coordinates. -/
private theorem sourceTensorCoordinates_permutation {ι : Type*} (X : HilbertObject)
    (b : HilbertBasis ι ℂ X.carrier) (e : ι ↪ ℕ) (n : ℕ)
    (σ : Equiv.Perm (Fin (n+1))) (ψ : (tensorTower X n).carrier)
    (t : Fin (n+1) → ℕ) :
    sourceTensorCoordinates X b e n (tensorPermutation X b n σ ψ) t =
      sourceTensorCoordinates X b e n ψ (t ∘ σ) := by
  by_cases ht : t∈Set.range ((Function.Embedding.arrowCongrRight (γ := Fin (n+1)) e))
  · obtain ⟨s,rfl⟩ := ht
    change coordinateRename ((Function.Embedding.arrowCongrRight (γ := Fin (n+1)) e))
      ((tensorTowerTupleBasis X b n).repr (tensorPermutation X b n σ ψ))
      ((Function.Embedding.arrowCongrRight (γ := Fin (n+1)) e) s) =
      coordinateRename ((Function.Embedding.arrowCongrRight (γ := Fin (n+1)) e)) ((tensorTowerTupleBasis X b n).repr ψ)
      ((Function.Embedding.arrowCongrRight (γ := Fin (n+1)) e) (s ∘ σ))
    rw [coordinateRename_image,coordinateRename_image,tensorPermutation_repr]
  · have ht' : t ∘ σ∉Set.range ((Function.Embedding.arrowCongrRight (γ := Fin (n+1)) e)) := by
      rintro ⟨s,hs⟩
      apply ht
      refine ⟨s ∘ σ.symm,?_⟩
      funext k
      simpa [Function.Embedding.arrowCongrRight, Function.Embedding.piCongrRight,Function.comp_apply] using congrFun hs (σ.symm k)
    change coordinateRename ((Function.Embedding.arrowCongrRight (γ := Fin (n+1)) e)) _ t =
      coordinateRename ((Function.Embedding.arrowCongrRight (γ := Fin (n+1)) e)) _ (t ∘ σ)
    rw [coordinateRename_outside _ _ _ ht,coordinateRename_outside _ _ _ ht']
/-- Physical permutation antisymmetry in the actual completed tensor power. -/
def sourceExterior {ι : Type*} (X : HilbertObject) (b : HilbertBasis ι ℂ X.carrier)
    (_e : ι ↪ ℕ) (n : ℕ) : Submodule ℂ (tensorTower X n).carrier where
  carrier := {ψ | ∀ σ : Equiv.Perm (Fin (n+1)),
    tensorPermutation X b n σ ψ = permutationPhase (n+1) σ • ψ}
  zero_mem' := by intro σ; simp only [map_zero,smul_zero]
  add_mem' := by intro x y hx hy σ; simp only [map_add,hx σ,hy σ,smul_add]
  smul_mem' := by
    intro a x hx σ
    rw [(tensorPermutation X b n σ).map_smul,hx σ]
    exact smul_comm a (permutationPhase (n+1) σ) x
/-- The source exterior is precisely the physical antisymmetric tensor-factor subspace. -/
private theorem sourceExteriorCoordinates_iff_physical {ι : Type*} (X : HilbertObject)
    (b : HilbertBasis ι ℂ X.carrier) (e : ι ↪ ℕ) (n : ℕ)
    (ψ : (tensorTower X n).carrier) :
    ψ∈sourceExteriorCoordinates X b e n ↔ ∀ σ : Equiv.Perm (Fin (n+1)),
      tensorPermutation X b n σ ψ = permutationPhase (n+1) σ • ψ := by
  constructor
  · intro h σ
    apply (sourceTensorCoordinates X b e n).injective
    ext t
    rw [sourceTensorCoordinates_permutation,map_smul]
    exact h t σ
  · intro h t σ
    change sourceTensorCoordinates X b e n ψ (t ∘ σ) =
      permutationPhase (n+1) σ * sourceTensorCoordinates X b e n ψ t
    rw [← sourceTensorCoordinates_permutation]
    rw [h σ,map_smul]
    rfl
/-- The physical definition and the coordinate model have the same vectors. -/
theorem sourceTensorCoordinates_antisymmetric {ι : Type*} (X : HilbertObject)
    (b : HilbertBasis ι ℂ X.carrier) (e : ι ↪ ℕ) (n : ℕ)
    (ψ : (tensorTower X n).carrier) :
    IsAntisymmetric (n+1) (sourceTensorCoordinates X b e n ψ) ↔ ψ∈sourceExterior X b e n :=
  sourceExteriorCoordinates_iff_physical X b e n ψ
end
end D5.S3.Quantum.FermionicCorrelationalBound.CompletedTensorSlaterGeometry
