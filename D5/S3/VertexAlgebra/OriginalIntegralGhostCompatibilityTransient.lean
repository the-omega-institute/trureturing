import D5.S3.VertexAlgebra.OriginalIntegralGhostCohomologyTransient

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.OriginalBrstReassembly

open LatticeGeneratingFieldLocality LatticeSugawaraCurrents LatticeBcGhostBrstCharge
open scoped BigOperators TensorProduct DirectSum Classical

noncomputable section

variable (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
  (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
  (hcritical : D.rank = 26) (space : Submodule ℂ (State D))
  (stable : ∀ state, state ∈ space → Q D H state ∈ space)
  (projected : ∀ degree state, state ∈ space → ghostProjection D degree state ∈ space)

theorem finite_ghost_class_reconstruction
    (state : Cohomology D H hHG hGH hcritical space stable) :
    ∑ degree ∈ (ghostClassSplit D H hHG hGH hcritical space stable projected state).support,
      ghostClassInclude D H hHG hGH hcritical space stable degree
        (ghostClassSplit D H hHG hGH hcritical space stable projected state degree) = state := by
  have equality := congrArg (ghostClassAssemble D H hHG hGH hcritical space stable)
    (DirectSum.sum_support_of
      (ghostClassSplit D H hHG hGH hcritical space stable projected state))
  rw [ghostAssemble_split] at equality
  have inclusion (degree : ℤ)
      (component : ghostCohomology D H hHG hGH hcritical space stable degree) :
      ghostClassAssemble D H hHG hGH hcritical space stable
        (DirectSum.of (ghostCohomology D H hHG hGH hcritical space stable) degree component) =
      ghostClassInclude D H hHG hGH hcritical space stable degree component := by
    change ghostClassAssemble D H hHG hGH hcritical space stable
      (DirectSum.lof ℂ ℤ (ghostCohomology D H hHG hGH hcritical space stable) degree component) = _
    exact DirectSum.toModule_lof ℂ degree component
  simpa only [map_sum, inclusion] using equality

theorem ghostClassSplit_support (state : cycles D H space) :
    (ghostClassSplit D H hHG hGH hcritical space stable projected
      ((boundaries D H hHG hGH hcritical space stable).mkQ state)).support ⊆
        (stateEquiv D (ghostTag D) state.val).support := by
  intro degree member
  by_contra absent
  have zeroComponent := DFinsupp.notMem_support_iff.mp absent
  have zeroProjection : ghostProjection D degree state.val = 0 := by
    have equality := congrArg (fun component : ghostPart D degree => (component : State D))
      zeroComponent
    simpa only [stateEquiv_component, ghostProjection, ZeroMemClass.coe_zero] using equality
  have zeroCycle : ghostCycleProject D H space projected degree state = 0 := by
    apply Subtype.ext
    exact zeroProjection
  apply (DFinsupp.mem_support_iff.mp member)
  rw [ghostClassSplit_mk, ghostCycleClassSplit_component, zeroCycle, map_zero]

variable (numberStable : ∀ state, state ∈ space → nativeJ D state ∈ space)

theorem ghostClassSplit_J_component
    (state : Cohomology D H hHG hGH hcritical space stable) (degree : ℤ) :
    ghostClassSplit D H hHG hGH hcritical space stable projected
      (cohomologyJ D H hHG hGH hcritical space stable numberStable state) degree =
    (degree : ℂ) •
      ghostClassSplit D H hHG hGH hcritical space stable projected state degree := by
  obtain ⟨representative, rfl⟩ :=
    (boundaries D H hHG hGH hcritical space stable).mkQ_surjective state
  change ghostCycleClassSplit D H hHG hGH hcritical space stable projected
    (cycleJ D H space numberStable representative) degree =
      (degree : ℂ) • ghostCycleClassSplit D H hHG hGH hcritical space stable projected
        representative degree
  rw [ghostCycleClassSplit_component, ghostCycleClassSplit_component, ← map_smul]
  congr 1
  apply Subtype.ext
  change ghostProjection D degree (nativeJ D representative.val) =
    (degree : ℂ) • ghostProjection D degree representative.val
  have commute := LinearMap.congr_fun (projection_J D (ghostTag D) degree) representative.val
  change ghostProjection D degree (nativeJ D representative.val) =
    nativeJ D (ghostProjection D degree representative.val) at commute
  rw [commute]
  exact (ghostPart_iff_number D degree _).mp
    (projection_mem D (ghostTag D) degree representative.val)

theorem ghostEigenclass_component_zero (degree other : ℤ)
    (state : Cohomology D H hHG hGH hcritical space stable)
    (homogeneous : cohomologyJ D H hHG hGH hcritical space stable numberStable state =
      (degree : ℂ) • state) (different : other ≠ degree) :
    ghostClassSplit D H hHG hGH hcritical space stable projected state other = 0 := by
  have equality := congrArg
    (fun value => ghostClassSplit D H hHG hGH hcritical space stable projected value other)
    homogeneous
  rw [ghostClassSplit_J_component] at equality
  have scalarEquality :
      (other : ℂ) • ghostClassSplit D H hHG hGH hcritical space stable projected state other =
      (degree : ℂ) • ghostClassSplit D H hHG hGH hcritical space stable projected state other := by
    have linear := congrArg (fun pieces => pieces other)
      ((ghostClassSplit D H hHG hGH hcritical space stable projected).map_smul
        (degree : ℂ) state)
    exact equality.trans linear
  have killed : ((other : ℂ) - (degree : ℂ)) •
      ghostClassSplit D H hHG hGH hcritical space stable projected state other = 0 := by
    rw [sub_smul, scalarEquality, sub_self]
  exact (smul_eq_zero.mp killed).resolve_left
    (sub_ne_zero.mpr (Int.cast_injective.ne different))

theorem ghostEigenclass_equals_component (degree : ℤ)
    (state : Cohomology D H hHG hGH hcritical space stable)
    (homogeneous : cohomologyJ D H hHG hGH hcritical space stable numberStable state =
      (degree : ℂ) • state) :
    state = ghostClassInclude D H hHG hGH hcritical space stable degree
      (ghostClassSplit D H hHG hGH hcritical space stable projected state degree) := by
  apply (ghostCohomologyEquiv D H hHG hGH hcritical space stable projected).injective
  change ghostClassSplit D H hHG hGH hcritical space stable projected state =
    ghostClassSplit D H hHG hGH hcritical space stable projected _
  rw [ghostSplit_include]
  apply DFinsupp.ext
  intro other
  by_cases same : degree = other
  · subst other
    simp [DirectSum.lof_eq_of, DirectSum.of_apply]
  · rw [ghostEigenclass_component_zero D H hHG hGH hcritical space stable projected
      numberStable degree other state homogeneous (Ne.symm same)]
    simp [DirectSum.lof_eq_of, DirectSum.of_apply, same]

include projected in
theorem ghostEigenclass_original_representative (degree : ℤ)
    (state : Cohomology D H hHG hGH hcritical space stable)
    (homogeneous : cohomologyJ D H hHG hGH hcritical space stable numberStable state =
      (degree : ℂ) • state) :
    ∃ representative : cycles D H space,
      representative.val ∈ ghostPart D degree ∧
        (boundaries D H hHG hGH hcritical space stable).mkQ representative = state := by
  obtain ⟨original, originalClass⟩ :=
    (boundaries D H hHG hGH hcritical space stable).mkQ_surjective state
  refine ⟨ghostCycleInclude D H space degree
    (ghostCycleProject D H space projected degree original),
    projection_mem D (ghostTag D) degree original.val, ?_⟩
  have equality := ghostEigenclass_equals_component D H hHG hGH hcritical space stable
    projected numberStable degree state homogeneous
  rw [← originalClass, ghostClassSplit_mk, ghostCycleClassSplit_component] at equality
  change ghostClassInclude D H hHG hGH hcritical space stable degree
    ((ghostBoundaries D H hHG hGH hcritical space stable degree).mkQ
      (ghostCycleProject D H space projected degree original)) = state
  rw [← originalClass]
  exact equality.symm

theorem signed_occupation_original_parity (sites : Finset ℕ) :
    (BcGhostNumber.degree sites % 2).toNat = BcGhostSuperGenerators.subsetParity sites := by
  have partition := Finset.card_filter_add_card_filter_not
    (s := sites) (fun site => site % 2 = 1)
  have same : sites.filter (fun site => ¬site % 2 = 1) =
      sites.filter (fun site => site % 2 = 0) := by
    ext site
    simp only [Finset.mem_filter]
    have bound := Nat.mod_lt site (by decide : 0 < 2)
    constructor
    · rintro ⟨present, notOdd⟩
      exact ⟨present, by omega⟩
    · rintro ⟨present, even⟩
      exact ⟨present, by omega⟩
  rw [same] at partition
  unfold BcGhostNumber.degree BcGhostSuperGenerators.subsetParity
  omega

theorem originalParity_ghostProjection (degree : ℤ) :
    (TensorProduct.map (LinearMap.id : Module.End ℂ (Carrier D))
      (BcGhostSuperGenerators.parityPart (degree % 2).toNat)).comp
        (ghostProjection D degree) = ghostProjection D degree := by
  apply (fullBasis D).ext
  intro label
  simp only [LinearMap.comp_apply]
  by_cases same : ghostTag D label = degree
  · rw [projection_fixed D (ghostTag D) degree
      (same ▸ basis_mem_part D (ghostTag D) label), fullBasis_apply,
      TensorProduct.map_tmul, LinearMap.id_apply]
    rw [BcGhostSuperGenerators.parityPart_identity]
    apply BcGhostSuperGenerators.single_mem
    have parity := signed_occupation_original_parity label.2
    change (ghostTag D label % 2).toNat = _ at parity
    rw [same] at parity
    rw [← parity]
    have bound : (degree % 2).toNat < 2 := by omega
    exact (Nat.mod_eq_of_lt bound).symm
  · rw [projection_other D (ghostTag D) degree (ghostTag D label) same
      (basis_mem_part D (ghostTag D) label), map_zero]

theorem ghostPart_original_parity (degree : ℤ) (state : State D)
    (member : state ∈ ghostPart D degree) :
    TensorProduct.map (LinearMap.id : Module.End ℂ (Carrier D))
      (BcGhostSuperGenerators.parityPart (degree % 2).toNat) state = state := by
  have equality := LinearMap.congr_fun (originalParity_ghostProjection D degree) state
  simpa only [LinearMap.comp_apply,
    projection_fixed D (ghostTag D) degree member] using equality

theorem ghostPart_original_parity_range (degree : ℤ) (state : State D)
    (member : state ∈ ghostPart D degree) :
    state ∈ LinearMap.range
      (TensorProduct.map (LinearMap.id : Module.End ℂ (Carrier D))
        (BcGhostSuperGenerators.parityPart (degree % 2).toNat)) :=
  ⟨state, ghostPart_original_parity D degree state member⟩

theorem ghostProjection_P0 (degree : ℤ) :
    (ghostProjection D degree).comp (P0 D) = (P0 D).comp (ghostProjection D degree) := by
  apply projection_commutes
  intro input output different
  change (fullBasis D).repr
    (energyWeight D (fun energy => if energy = 0 then 1 else 0) (fullBasis D input)) output = 0
  rw [energyWeight_basis, map_smul, Finsupp.smul_apply, (fullBasis D).repr_self]
  have notEqual : input ≠ output := by
    intro same
    subst output
    exact different rfl
  simp [Finsupp.single_apply, notEqual]

variable (target : Submodule ℂ (State D))
  (targetStable : ∀ state, state ∈ target → Q D H state ∈ target)
  (targetProjected : ∀ degree state, state ∈ target → ghostProjection D degree state ∈ target)
  (operator : Module.End ℂ (State D))
  (maps : ∀ state, state ∈ space → operator state ∈ target)
  (commutes : operator.comp (Q D H) = (Q D H).comp operator)
  (degreePreserving : ∀ degree,
    (ghostProjection D degree).comp operator = operator.comp (ghostProjection D degree))

def ghostDegreeCycleMap (degree : ℤ) :
    ghostCycles D H space degree →ₗ[ℂ] ghostCycles D H target degree :=
  (operator.comp (ghostCycles D H space degree).subtype).codRestrict
    (ghostCycles D H target degree) (fun state => by
      refine ⟨⟨maps state.val state.property.1.1, ?_⟩, ?_⟩
      · have equality := LinearMap.congr_fun commutes state.val
        change operator (Q D H state.val) = Q D H (operator state.val) at equality
        rw [state.property.1.2, map_zero] at equality
        exact equality.symm
      · have equality := LinearMap.congr_fun (degreePreserving degree) state.val
        change ghostProjection D degree (operator state.val) =
          operator (ghostProjection D degree state.val) at equality
        rw [projection_fixed D (ghostTag D) degree state.property.2] at equality
        change operator state.val ∈ ghostPart D degree
        rw [← equality]
        exact projection_mem D (ghostTag D) degree (operator state.val))

def ghostDegreeClassMap (degree : ℤ) :
    ghostCohomology D H hHG hGH hcritical space stable degree →ₗ[ℂ]
      ghostCohomology D H hHG hGH hcritical target targetStable degree :=
  (ghostBoundaries D H hHG hGH hcritical space stable degree).mapQ
    (ghostBoundaries D H hHG hGH hcritical target targetStable degree)
    (ghostDegreeCycleMap D H space target operator maps commutes degreePreserving degree)
    (fun state member => by
      obtain ⟨preimage, equality⟩ :=
        (ghostBoundary_iff D H hHG hGH hcritical space stable degree state).mp member
      apply (ghostBoundary_iff D H hHG hGH hcritical target targetStable degree _).mpr
      have previous := LinearMap.congr_fun (degreePreserving (degree - 1)) preimage.val
      change ghostProjection D (degree - 1) (operator preimage.val) =
        operator (ghostProjection D (degree - 1) preimage.val) at previous
      rw [projection_fixed D (ghostTag D) (degree - 1) preimage.property.2] at previous
      refine ⟨⟨operator preimage.val, maps preimage.val preimage.property.1, ?_⟩, ?_⟩
      · rw [← previous]
        exact projection_mem D (ghostTag D) (degree - 1) (operator preimage.val)
      · change Q D H (operator preimage.val) = operator state.val
        have commuting := LinearMap.congr_fun commutes preimage.val
        simp only [LinearMap.comp_apply] at commuting
        rw [← commuting, equality])

theorem ghostClassSplit_natural (state : Cohomology D H hHG hGH hcritical space stable) :
    ghostClassSplit D H hHG hGH hcritical target targetStable targetProjected
      (homologyMap D H hHG hGH hcritical space target stable targetStable operator maps
        commutes state) =
    DirectSum.lmap
      (ghostDegreeClassMap D H hHG hGH hcritical space stable target targetStable
        operator maps commutes degreePreserving)
      (ghostClassSplit D H hHG hGH hcritical space stable projected state) := by
  obtain ⟨representative, rfl⟩ :=
    (boundaries D H hHG hGH hcritical space stable).mkQ_surjective state
  apply DFinsupp.ext
  intro degree
  change ghostCycleClassSplit D H hHG hGH hcritical target targetStable targetProjected
    (cyclesMap D H space target operator maps commutes representative) degree =
      ghostDegreeClassMap D H hHG hGH hcritical space stable target targetStable operator
        maps commutes degreePreserving degree
        (ghostCycleClassSplit D H hHG hGH hcritical space stable projected representative degree)
  rw [ghostCycleClassSplit_component, ghostCycleClassSplit_component]
  change (ghostBoundaries D H hHG hGH hcritical target targetStable degree).mkQ _ =
    (ghostBoundaries D H hHG hGH hcritical target targetStable degree).mkQ _
  congr 1
  apply Subtype.ext
  exact LinearMap.congr_fun (degreePreserving degree) representative.val

def ghostZeroReductionDegree (degree : ℤ) :
    ghostCohomology D H hHG hGH hcritical ⊤ (top_stable D H) degree →ₗ[ℂ]
      ghostCohomology D H hHG hGH hcritical (zeroSpace D H)
        (zero_stable D H hHG hGH) degree :=
  ghostDegreeClassMap D H hHG hGH hcritical ⊤ (top_stable D H) (zeroSpace D H)
    (zero_stable D H hHG hGH) (P0 D) (fun state _ => P0_mem D H hHG hGH state)
      (P0_Q D H hHG hGH) (ghostProjection_P0 D) degree

theorem zeroReduction_ghost_split (state : absoluteCohomology D H hHG hGH hcritical) :
    ghostClassSplit D H hHG hGH hcritical (zeroSpace D H) (zero_stable D H hHG hGH)
      (zero_projected D H hHG hGH (ghostTag D))
      (zeroReduction D H hHG hGH hcritical state) =
    DirectSum.lmap (ghostZeroReductionDegree D H hHG hGH hcritical)
      (absoluteGhostEquiv D H hHG hGH hcritical state) := by
  exact ghostClassSplit_natural D H hHG hGH hcritical ⊤ (top_stable D H)
    (fun _ _ _ => Submodule.mem_top) (zeroSpace D H) (zero_stable D H hHG hGH)
    (zero_projected D H hHG hGH (ghostTag D)) (P0 D)
    (fun state _ => P0_mem D H hHG hGH state) (P0_Q D H hHG hGH)
    (ghostProjection_P0 D) state

theorem absoluteGhost_original_representative (degree : ℤ)
    (state : absoluteCohomology D H hHG hGH hcritical)
    (homogeneous : cohomologyJ D H hHG hGH hcritical ⊤ (top_stable D H)
      (fun _ _ => Submodule.mem_top) state = (degree : ℂ) • state) :
    ∃ representative : cycles D H ⊤,
      representative.val ∈ ghostPart D degree ∧
      TensorProduct.map (LinearMap.id : Module.End ℂ (Carrier D))
        (BcGhostSuperGenerators.parityPart (degree % 2).toNat) representative.val =
          representative.val ∧
      (boundaries D H hHG hGH hcritical ⊤ (top_stable D H)).mkQ representative = state := by
  obtain ⟨representative, degreeMember, representativeClass⟩ :=
    ghostEigenclass_original_representative D H hHG hGH hcritical ⊤ (top_stable D H)
      (fun _ _ _ => Submodule.mem_top) (fun _ _ => Submodule.mem_top) degree state homogeneous
  exact ⟨representative, degreeMember,
    ghostPart_original_parity D degree representative.val degreeMember, representativeClass⟩

#print axioms ghostEigenclass_original_representative
#print axioms signed_occupation_original_parity
#print axioms originalParity_ghostProjection
#print axioms zeroReduction_ghost_split
#print axioms absoluteGhost_original_representative

end

end D5.S3.VertexAlgebra.OriginalBrstReassembly
