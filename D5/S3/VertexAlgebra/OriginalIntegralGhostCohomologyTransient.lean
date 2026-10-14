import D5.S3.VertexAlgebra.LatticeBcGhostCohomologyGhostGrading
import D5.S3.VertexAlgebra.BcGhostSuperGenerators

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.OriginalBrstReassembly

open LatticeGeneratingFieldLocality LatticeSugawaraCurrents LatticeBcGhostBrstCharge
open scoped BigOperators TensorProduct DirectSum Classical

noncomputable section

variable (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)

def ghostTag (label : FullLabel D) : ℤ := BcGhostNumber.degree label.2

abbrev ghostPart (degree : ℤ) := part D (ghostTag D) degree

abbrev ghostProjection (degree : ℤ) := projection D (ghostTag D) degree

theorem nativeJ_coeff (state : State D) (label : FullLabel D) :
    (fullBasis D).repr (nativeJ D state) label =
      (ghostTag D label : ℂ) * (fullBasis D).repr state label := by
  have diagonal : (coefficientMap D label).comp (nativeJ D) =
      (ghostTag D label : ℂ) • coefficientMap D label := by
    apply (fullBasis D).ext
    intro input
    change coefficientMap D label (nativeJ D (fullBasis D input)) =
      (ghostTag D label : ℂ) • coefficientMap D label (fullBasis D input)
    rw [J_basis, map_smul]
    change (ghostTag D input : ℂ) * (fullBasis D).repr (fullBasis D input) label =
      (ghostTag D label : ℂ) * (fullBasis D).repr (fullBasis D input) label
    rw [(fullBasis D).repr_self]
    by_cases same : input = label
    · subst input
      rfl
    · simp [Finsupp.single_apply, same]
  exact LinearMap.congr_fun diagonal state

theorem ghostPart_iff_number (degree : ℤ) (state : State D) :
    state ∈ ghostPart D degree ↔ nativeJ D state = (degree : ℂ) • state := by
  constructor
  · intro member
    apply (fullBasis D).repr.injective
    ext label
    rw [nativeJ_coeff, map_smul, Finsupp.smul_apply]
    by_cases same : ghostTag D label = degree
    · rw [same]
      rfl
    · rw [(mem_part D (ghostTag D) degree state).mp member label same]
      simp
  · intro eigenvector
    rw [mem_part]
    intro label different
    have equality := congrArg (fun vector : State D => (fullBasis D).repr vector label)
      eigenvector
    rw [nativeJ_coeff, map_smul, Finsupp.smul_apply, smul_eq_mul] at equality
    apply (mul_eq_zero.mp (show
      ((ghostTag D label : ℂ) - (degree : ℂ)) * (fullBasis D).repr state label = 0 by
        rw [sub_mul, equality, sub_self])).resolve_left
    exact sub_ne_zero.mpr (Int.cast_injective.ne different)

theorem Q_ghostPart (degree : ℤ) (state : State D) (member : state ∈ ghostPart D degree) :
    Q D H state ∈ ghostPart D (degree + 1) := by
  apply (ghostPart_iff_number D (degree + 1) _).mpr
  rw [nativeJ_Q, (ghostPart_iff_number D degree state).mp member, map_add, map_smul]
  simp [Int.cast_add, add_smul]

theorem Q_ghost_coeff_zero (input output : FullLabel D)
    (different : ghostTag D output ≠ ghostTag D input + 1) :
    (fullBasis D).repr (Q D H (fullBasis D input)) output = 0 := by
  exact (mem_part D (ghostTag D) (ghostTag D input + 1) _).mp
    (Q_ghostPart D H (ghostTag D input) (fullBasis D input)
      (basis_mem_part D (ghostTag D) input)) output different

theorem ghostProjection_Q_shift (degree : ℤ) :
    (ghostProjection D (degree + 1)).comp (Q D H) =
      (Q D H).comp (ghostProjection D degree) := by
  apply (fullBasis D).ext
  intro input
  simp only [LinearMap.comp_apply]
  by_cases same : ghostTag D input = degree
  · rw [projection_fixed D (ghostTag D) degree
      (same ▸ basis_mem_part D (ghostTag D) input)]
    exact projection_fixed D (ghostTag D) (degree + 1)
      (Q_ghostPart D H degree (fullBasis D input)
        (same ▸ basis_mem_part D (ghostTag D) input))
  · rw [projection_other D (ghostTag D) degree (ghostTag D input) same
      (basis_mem_part D (ghostTag D) input), map_zero]
    exact projection_other D (ghostTag D) (degree + 1) (ghostTag D input + 1)
      (by omega) (Q_ghostPart D H (ghostTag D input) (fullBasis D input)
        (basis_mem_part D (ghostTag D) input))

theorem ghostProjection_Q_predecessor (degree : ℤ) :
    (ghostProjection D degree).comp (Q D H) =
      (Q D H).comp (ghostProjection D (degree - 1)) := by
  simpa using ghostProjection_Q_shift D H (degree - 1)

theorem ghostProjection_cycle (degree : ℤ) (state : State D) (cycle : Q D H state = 0) :
    Q D H (ghostProjection D degree state) = 0 := by
  have equality := LinearMap.congr_fun (ghostProjection_Q_shift D H degree) state
  change ghostProjection D (degree + 1) (Q D H state) =
    Q D H (ghostProjection D degree state) at equality
  rw [cycle, map_zero] at equality
  exact equality.symm

variable (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
  (hcritical : D.rank = 26)
  (space : Submodule ℂ (State D))
  (stable : ∀ state, state ∈ space → Q D H state ∈ space)
  (projected : ∀ degree state, state ∈ space → ghostProjection D degree state ∈ space)

def ghostDifferential (degree : ℤ) :
    subspaceParts D (ghostTag D) space degree →ₗ[ℂ]
      subspaceParts D (ghostTag D) space (degree + 1) :=
  ((Q D H).comp (subspaceParts D (ghostTag D) space degree).subtype).codRestrict
    (subspaceParts D (ghostTag D) space (degree + 1)) (fun state =>
      ⟨stable state.val state.property.1,
        Q_ghostPart D H degree state.val state.property.2⟩)

include hHG hGH hcritical in
theorem ghostDifferential_square_zero (degree : ℤ) :
    (ghostDifferential D H space stable (degree + 1)).comp
      (ghostDifferential D H space stable degree) = 0 := by
  apply LinearMap.ext
  intro state
  apply Subtype.ext
  change Q D H (Q D H state.val) = 0
  exact actual_square_zero D H hHG hGH hcritical state.val

abbrev ghostCycles (degree : ℤ) :=
  subspaceParts D (ghostTag D) (cycles D H space) degree

def ghostBoundaryMap (degree : ℤ) :
    subspaceParts D (ghostTag D) space (degree - 1) →ₗ[ℂ] ghostCycles D H space degree :=
  ((Q D H).comp (subspaceParts D (ghostTag D) space (degree - 1)).subtype).codRestrict
    (ghostCycles D H space degree) (fun state => by
      have square := congrArg Subtype.val (LinearMap.congr_fun
        (ghostDifferential_square_zero D H hHG hGH hcritical space stable (degree - 1)) state)
      refine ⟨⟨stable state.val state.property.1, square⟩, ?_⟩
      simpa using Q_ghostPart D H (degree - 1) state.val state.property.2)

def ghostBoundaries (degree : ℤ) : Submodule ℂ (ghostCycles D H space degree) :=
  LinearMap.range (ghostBoundaryMap D H hHG hGH hcritical space stable degree)

abbrev ghostCohomology (degree : ℤ) :=
  ghostCycles D H space degree ⧸ ghostBoundaries D H hHG hGH hcritical space stable degree

def ghostCycleInclude (degree : ℤ) : ghostCycles D H space degree →ₗ[ℂ] cycles D H space :=
  (ghostCycles D H space degree).inclusion inf_le_left

theorem ghostBoundary_iff (degree : ℤ) (state : ghostCycles D H space degree) :
    state ∈ ghostBoundaries D H hHG hGH hcritical space stable degree ↔
      ∃ preimage : subspaceParts D (ghostTag D) space (degree - 1),
        Q D H preimage.val = state.val := by
  constructor
  · rintro ⟨preimage, equality⟩
    exact ⟨preimage, congrArg Subtype.val equality⟩
  · rintro ⟨preimage, equality⟩
    exact ⟨preimage, Subtype.ext equality⟩

include projected in
theorem ghostBoundary_original_intersection (degree : ℤ) :
    ghostBoundaries D H hHG hGH hcritical space stable degree =
      (boundaries D H hHG hGH hcritical space stable).comap
        (ghostCycleInclude D H space degree) := by
  ext state
  rw [ghostBoundary_iff, Submodule.mem_comap,
    boundary_iff D H hHG hGH hcritical space stable]
  constructor
  · rintro ⟨preimage, equality⟩
    exact ⟨⟨preimage.val, preimage.property.1⟩, equality⟩
  · rintro ⟨preimage, equality⟩
    refine ⟨⟨ghostProjection D (degree - 1) preimage.val,
      projected (degree - 1) preimage.val preimage.property,
      projection_mem D (ghostTag D) (degree - 1) preimage.val⟩, ?_⟩
    have shifted := LinearMap.congr_fun (ghostProjection_Q_predecessor D H degree)
      preimage.val
    change ghostProjection D degree (Q D H preimage.val) =
      Q D H (ghostProjection D (degree - 1) preimage.val) at shifted
    rw [← shifted, equality]
    exact projection_fixed D (ghostTag D) degree state.property.2

include projected in
theorem ghostCycles_projected (degree : ℤ) (state : State D)
    (member : state ∈ cycles D H space) :
    ghostProjection D degree state ∈ cycles D H space :=
  ⟨projected degree state member.1, ghostProjection_cycle D H degree state member.2⟩

def ghostCycleProject (degree : ℤ) : cycles D H space →ₗ[ℂ] ghostCycles D H space degree :=
  ((ghostProjection D degree).comp (cycles D H space).subtype).codRestrict
    (ghostCycles D H space degree) (fun state =>
      ⟨ghostCycles_projected D H space projected degree state.val state.property,
        projection_mem D (ghostTag D) degree state.val⟩)

def ghostCycleEquiv : cycles D H space ≃ₗ[ℂ] ⨁ degree, ghostCycles D H space degree :=
  subspaceEquiv D (ghostTag D) (cycles D H space)
    (ghostCycles_projected D H space projected)

theorem ghostCycleEquiv_component (state : cycles D H space) (degree : ℤ) :
    ghostCycleEquiv D H space projected state degree =
      ghostCycleProject D H space projected degree state := by
  apply Subtype.ext
  exact subspaceSplitFun_component D (ghostTag D) (cycles D H space)
    (ghostCycles_projected D H space projected) state degree

theorem ghostCycleEquiv_inverse_lof (degree : ℤ) (state : ghostCycles D H space degree) :
    (ghostCycleEquiv D H space projected).symm
      (DirectSum.lof ℂ ℤ (fun index => ghostCycles D H space index) degree state) =
      ghostCycleInclude D H space degree state := by
  apply Subtype.ext
  apply (stateEquiv D (ghostTag D)).injective
  apply DFinsupp.ext
  intro other
  apply Subtype.ext
  rw [stateEquiv_component, stateEquiv_component]
  have inverseEquation := (ghostCycleEquiv D H space projected).apply_symm_apply
    (DirectSum.lof ℂ ℤ (fun index => ghostCycles D H space index) degree state)
  have componentEquation := congrArg (fun pieces => (pieces other : State D)) inverseEquation
  rw [ghostCycleEquiv_component] at componentEquation
  change ghostProjection D other _ = _ at componentEquation
  simp only [ghostProjection, Submodule.subtype_apply] at componentEquation
  rw [componentEquation]
  by_cases same : degree = other
  · subst other
    rw [DirectSum.lof_apply]
    exact (projection_fixed D (ghostTag D) degree state.property.2).symm
  · rw [DirectSum.lof_eq_of, DirectSum.of_apply, dif_neg same]
    change (0 : State D) = ghostProjection D other state.val
    exact (projection_other D (ghostTag D) other degree same state.property.2).symm

def ghostCycleClassSplit : cycles D H space →ₗ[ℂ]
    ⨁ degree, ghostCohomology D H hHG hGH hcritical space stable degree :=
  (DirectSum.lmap (fun degree =>
    (ghostBoundaries D H hHG hGH hcritical space stable degree).mkQ)).comp
      (ghostCycleEquiv D H space projected).toLinearMap

theorem ghostCycleClassSplit_component (state : cycles D H space) (degree : ℤ) :
    ghostCycleClassSplit D H hHG hGH hcritical space stable projected state degree =
      (ghostBoundaries D H hHG hGH hcritical space stable degree).mkQ
        (ghostCycleProject D H space projected degree state) := by
  change (ghostBoundaries D H hHG hGH hcritical space stable degree).mkQ
    (ghostCycleEquiv D H space projected state degree) = _
  rw [ghostCycleEquiv_component]

theorem ghostCycleClassSplit_boundary (state : cycles D H space)
    (member : state ∈ boundaries D H hHG hGH hcritical space stable) :
    ghostCycleClassSplit D H hHG hGH hcritical space stable projected state = 0 := by
  obtain ⟨preimage, equality⟩ :=
    (boundary_iff D H hHG hGH hcritical space stable state).mp member
  apply DFinsupp.ext
  intro degree
  rw [ghostCycleClassSplit_component]
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  apply (ghostBoundary_iff D H hHG hGH hcritical space stable degree _).mpr
  refine ⟨⟨ghostProjection D (degree - 1) preimage.val,
    projected (degree - 1) preimage.val preimage.property,
    projection_mem D (ghostTag D) (degree - 1) preimage.val⟩, ?_⟩
  change Q D H (ghostProjection D (degree - 1) preimage.val) =
    ghostProjection D degree state.val
  have shifted := LinearMap.congr_fun (ghostProjection_Q_predecessor D H degree) preimage.val
  simp only [LinearMap.comp_apply] at shifted
  rw [← shifted, equality]

def ghostClassSplit : Cohomology D H hHG hGH hcritical space stable →ₗ[ℂ]
    ⨁ degree, ghostCohomology D H hHG hGH hcritical space stable degree := by
  letI : ∀ degree, AddCommGroup
      (ghostCohomology D H hHG hGH hcritical space stable degree) :=
    fun degree => inferInstanceAs (AddCommGroup
      (ghostCycles D H space degree ⧸
        ghostBoundaries D H hHG hGH hcritical space stable degree))
  exact (boundaries D H hHG hGH hcritical space stable).liftQ
    (ghostCycleClassSplit D H hHG hGH hcritical space stable projected)
    (fun state member => ghostCycleClassSplit_boundary D H hHG hGH hcritical
      space stable projected state member)

theorem ghostClassSplit_mk (state : cycles D H space) :
    ghostClassSplit D H hHG hGH hcritical space stable projected
      ((boundaries D H hHG hGH hcritical space stable).mkQ state) =
    ghostCycleClassSplit D H hHG hGH hcritical space stable projected state := rfl

def ghostClassInclude (degree : ℤ) :
    ghostCohomology D H hHG hGH hcritical space stable degree →ₗ[ℂ]
      Cohomology D H hHG hGH hcritical space stable :=
  (ghostBoundaries D H hHG hGH hcritical space stable degree).mapQ
    (boundaries D H hHG hGH hcritical space stable) (ghostCycleInclude D H space degree)
    (fun state member => by
      obtain ⟨preimage, equality⟩ :=
        (ghostBoundary_iff D H hHG hGH hcritical space stable degree state).mp member
      apply (boundary_iff D H hHG hGH hcritical space stable _).mpr
      exact ⟨⟨preimage.val, preimage.property.1⟩, equality⟩)

def ghostClassAssemble : (⨁ degree,
    ghostCohomology D H hHG hGH hcritical space stable degree) →ₗ[ℂ]
      Cohomology D H hHG hGH hcritical space stable :=
  DirectSum.toModule ℂ ℤ _ (ghostClassInclude D H hHG hGH hcritical space stable)

theorem ghostAssemble_cycleClasses (pieces : ⨁ degree, ghostCycles D H space degree) :
    ghostClassAssemble D H hHG hGH hcritical space stable
      (DirectSum.lmap (fun degree =>
        (ghostBoundaries D H hHG hGH hcritical space stable degree).mkQ) pieces) =
    (boundaries D H hHG hGH hcritical space stable).mkQ
      ((ghostCycleEquiv D H space projected).symm pieces) := by
  have identity :
      (ghostClassAssemble D H hHG hGH hcritical space stable).comp
        (DirectSum.lmap (fun degree =>
          (ghostBoundaries D H hHG hGH hcritical space stable degree).mkQ)) =
      (boundaries D H hHG hGH hcritical space stable).mkQ.comp
        (ghostCycleEquiv D H space projected).symm.toLinearMap := by
    apply DirectSum.linearMap_ext
    intro degree
    apply LinearMap.ext
    intro state
    simp only [LinearMap.comp_apply, DirectSum.lmap_lof, ghostClassAssemble,
      DirectSum.toModule_lof]
    change ghostClassInclude D H hHG hGH hcritical space stable degree
      ((ghostBoundaries D H hHG hGH hcritical space stable degree).mkQ state) =
        (boundaries D H hHG hGH hcritical space stable).mkQ
          ((ghostCycleEquiv D H space projected).symm
            (DirectSum.lof ℂ ℤ (fun index => ghostCycles D H space index) degree state))
    rw [ghostCycleEquiv_inverse_lof D H space projected degree state]
    rfl
  exact LinearMap.congr_fun identity pieces

theorem ghostAssemble_split (state : Cohomology D H hHG hGH hcritical space stable) :
    ghostClassAssemble D H hHG hGH hcritical space stable
      (ghostClassSplit D H hHG hGH hcritical space stable projected state) = state := by
  obtain ⟨representative, rfl⟩ :=
    (boundaries D H hHG hGH hcritical space stable).mkQ_surjective state
  rw [ghostClassSplit_mk]
  change ghostClassAssemble D H hHG hGH hcritical space stable
    (DirectSum.lmap (fun degree =>
      (ghostBoundaries D H hHG hGH hcritical space stable degree).mkQ)
        (ghostCycleEquiv D H space projected representative)) = _
  rw [ghostAssemble_cycleClasses D H hHG hGH hcritical space stable projected,
    LinearEquiv.symm_apply_apply]

theorem ghostSplit_include (degree : ℤ)
    (state : ghostCohomology D H hHG hGH hcritical space stable degree) :
    ghostClassSplit D H hHG hGH hcritical space stable projected
      (ghostClassInclude D H hHG hGH hcritical space stable degree state) =
    DirectSum.lof ℂ ℤ (ghostCohomology D H hHG hGH hcritical space stable) degree state := by
  obtain ⟨representative, rfl⟩ :=
    (ghostBoundaries D H hHG hGH hcritical space stable degree).mkQ_surjective state
  change ghostCycleClassSplit D H hHG hGH hcritical space stable projected
    (ghostCycleInclude D H space degree representative) = _
  change DirectSum.lmap (fun other =>
    (ghostBoundaries D H hHG hGH hcritical space stable other).mkQ)
      (ghostCycleEquiv D H space projected
        (ghostCycleInclude D H space degree representative)) = _
  rw [← ghostCycleEquiv_inverse_lof D H space projected degree representative,
    LinearEquiv.apply_symm_apply, DirectSum.lmap_lof]

theorem ghostSplit_assemble (pieces : ⨁ degree,
    ghostCohomology D H hHG hGH hcritical space stable degree) :
    ghostClassSplit D H hHG hGH hcritical space stable projected
      (ghostClassAssemble D H hHG hGH hcritical space stable pieces) = pieces := by
  have identity :
      (ghostClassSplit D H hHG hGH hcritical space stable projected).comp
        (ghostClassAssemble D H hHG hGH hcritical space stable) = LinearMap.id := by
    apply DirectSum.linearMap_ext
    intro degree
    apply LinearMap.ext
    intro state
    simp only [LinearMap.comp_apply, ghostClassAssemble, DirectSum.toModule_lof,
      ghostSplit_include, LinearMap.id_apply]
  exact LinearMap.congr_fun identity pieces

def ghostCohomologyEquiv : Cohomology D H hHG hGH hcritical space stable ≃ₗ[ℂ]
    ⨁ degree, ghostCohomology D H hHG hGH hcritical space stable degree :=
  { ghostClassSplit D H hHG hGH hcritical space stable projected with
    invFun := ghostClassAssemble D H hHG hGH hcritical space stable
    left_inv := ghostAssemble_split D H hHG hGH hcritical space stable projected
    right_inv := ghostSplit_assemble D H hHG hGH hcritical space stable projected }

def absoluteGhostEquiv : absoluteCohomology D H hHG hGH hcritical ≃ₗ[ℂ]
    ⨁ degree, ghostCohomology D H hHG hGH hcritical ⊤ (top_stable D H) degree :=
  ghostCohomologyEquiv D H hHG hGH hcritical ⊤ (top_stable D H)
    (fun _ _ _ => Submodule.mem_top)

#print axioms ghostProjection_Q_shift
#print axioms ghostBoundary_original_intersection
#print axioms ghostCohomologyEquiv
#print axioms absoluteGhostEquiv

end

end D5.S3.VertexAlgebra.OriginalBrstReassembly
