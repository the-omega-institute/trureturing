import D5.S3.VertexAlgebra.OriginalIntegralGhostDegreeTransient

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.VertexAlgebra.TensorConformal.OriginalIntegralGhostOperationsTransient

open LatticeGeneratingFieldLocality LatticeSugawaraCurrents
open LatticeBcGhostBrstCharge (State Q B)
open LatticeBcGhostNeutralCohomology (OriginalCycles OriginalBoundaries OriginalCohomology)
open OriginalBrstReassembly OriginalTopologicalApplications
open OriginalIntegralB0CompatibilityTransient OriginalIntegralBVGerstBracketTransient
open OriginalIntegralGhostDegreeTransient
open LatticeBcGhostCohomologyModes
open LatticeBcGhostTensorStateField (stateField)
open scoped VertexOperator DirectSum

variable (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
  (leftInverse : H * gramComplex D = 1) (rightInverse : gramComplex D * H = 1)
  (critical : D.rank = 26)

abbrev IntegralCycles (degree : ℤ) := ghostCycles D H ⊤ degree

abbrev IntegralBoundaries (degree : ℤ) :=
  ghostBoundaries D H leftInverse rightInverse critical ⊤ (top_stable D H) degree

abbrev IntegralCohomology (degree : ℤ) :=
  ghostCohomology D H leftInverse rightInverse critical ⊤ (top_stable D H) degree

def literalCycle (degree : ℤ) : IntegralCycles D H degree →ₗ[ℂ] OriginalCycles D H :=
  (absoluteCycleEquiv D H).toLinearMap.comp (ghostCycleInclude D H ⊤ degree)

def literalClass (degree : ℤ) :
    IntegralCohomology D H leftInverse rightInverse critical degree →ₗ[ℂ]
      OriginalCohomology D H :=
  (absoluteOriginalEquiv D H leftInverse rightInverse critical).toLinearMap.comp
    (ghostClassInclude D H leftInverse rightInverse critical ⊤ (top_stable D H) degree)

theorem literalClass_mk (degree : ℤ) (state : IntegralCycles D H degree) :
    literalClass D H leftInverse rightInverse critical degree
      ((IntegralBoundaries D H leftInverse rightInverse critical degree).mkQ state) =
    (OriginalBoundaries D H).mkQ (literalCycle D H degree state) := rfl

theorem projected_boundary_preimage (degree : ℤ) (state : IntegralCycles D H degree)
    (preimage : State D) (equation : Q D H preimage = state.val) :
    Q D H (ghostProjection D (degree - 1) preimage) = state.val := by
  exact (LinearMap.congr_fun (ghostProjection_Q_predecessor D H degree) preimage).symm.trans
    ((congrArg (ghostProjection D degree) equation).trans
      (projection_fixed D (ghostTag D) degree state.property.2))

theorem integralBoundary_of_literal (degree : ℤ) (state : IntegralCycles D H degree)
    (boundary : literalCycle D H degree state ∈ OriginalBoundaries D H) :
    state ∈ IntegralBoundaries D H leftInverse rightInverse critical degree := by
  obtain ⟨preimage, equation⟩ := boundary
  apply (ghostBoundary_iff D H leftInverse rightInverse critical ⊤
    (top_stable D H) degree state).mpr
  exact ⟨⟨ghostProjection D (degree - 1) preimage, Submodule.mem_top,
    projection_mem D (ghostTag D) (degree - 1) preimage⟩,
    projected_boundary_preimage D H degree state preimage equation⟩

def integralCycleProduct (mode leftDegree rightDegree : ℤ) :
    IntegralCycles D H leftDegree →ₗ[ℂ] IntegralCycles D H rightDegree →ₗ[ℂ]
      IntegralCycles D H (leftDegree + rightDegree) where
  toFun left :=
    (((stateField D left.val)[[mode]]).comp (IntegralCycles D H rightDegree).subtype).codRestrict
      (IntegralCycles D H (leftDegree + rightDegree)) (fun right =>
        ⟨⟨Submodule.mem_top, mode_closed D H (literalCycle D H leftDegree left)
          (literalCycle D H rightDegree right) mode⟩,
          native_field_integer_degree D leftDegree rightDegree mode left.val right.val
            left.property.2 right.property.2⟩)
  map_add' first second := by
    apply LinearMap.ext
    intro right
    apply Subtype.ext
    simp [map_add]
  map_smul' scalar left := by
    apply LinearMap.ext
    intro right
    apply Subtype.ext
    simp [map_smul]

theorem integralCycleProduct_boundary_left (mode leftDegree rightDegree : ℤ)
    (left : IntegralCycles D H leftDegree) (right : IntegralCycles D H rightDegree)
    (boundary : left ∈ IntegralBoundaries D H leftInverse rightInverse critical leftDegree) :
    integralCycleProduct D H mode leftDegree rightDegree left right ∈
      IntegralBoundaries D H leftInverse rightInverse critical (leftDegree + rightDegree) := by
  obtain ⟨preimage, equation⟩ := (ghostBoundary_iff D H leftInverse rightInverse critical ⊤
    (top_stable D H) leftDegree left).mp boundary
  apply integralBoundary_of_literal D H leftInverse rightInverse critical
  exact cycleMode_boundary_left D H mode (literalCycle D H leftDegree left)
    (literalCycle D H rightDegree right) ⟨preimage.val, equation⟩

theorem integralCycleProduct_boundary_right (mode leftDegree rightDegree : ℤ)
    (left : IntegralCycles D H leftDegree) (right : IntegralCycles D H rightDegree)
    (boundary : right ∈ IntegralBoundaries D H leftInverse rightInverse critical rightDegree) :
    integralCycleProduct D H mode leftDegree rightDegree left right ∈
      IntegralBoundaries D H leftInverse rightInverse critical (leftDegree + rightDegree) := by
  obtain ⟨preimage, equation⟩ := (ghostBoundary_iff D H leftInverse rightInverse critical ⊤
    (top_stable D H) rightDegree right).mp boundary
  apply integralBoundary_of_literal D H leftInverse rightInverse critical
  exact cycleMode_boundary_right D H mode (literalCycle D H leftDegree left)
    (literalCycle D H rightDegree right) ⟨preimage.val, equation⟩

def integralProduct (mode leftDegree rightDegree : ℤ) :
    IntegralCohomology D H leftInverse rightInverse critical leftDegree →ₗ[ℂ]
    IntegralCohomology D H leftInverse rightInverse critical rightDegree →ₗ[ℂ]
    IntegralCohomology D H leftInverse rightInverse critical (leftDegree + rightDegree) :=
  ((integralCycleProduct D H mode leftDegree rightDegree).compr₂
    (IntegralBoundaries D H leftInverse rightInverse critical (leftDegree + rightDegree)).mkQ).liftQ₂
    (IntegralBoundaries D H leftInverse rightInverse critical leftDegree)
    (IntegralBoundaries D H leftInverse rightInverse critical rightDegree)
    (by
      intro left boundary
      apply LinearMap.ext
      intro right
      change (IntegralBoundaries D H leftInverse rightInverse critical
        (leftDegree + rightDegree)).mkQ
          (integralCycleProduct D H mode leftDegree rightDegree left right) = 0
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      exact integralCycleProduct_boundary_left D H leftInverse rightInverse critical
        mode leftDegree rightDegree left right boundary)
    (by
      intro right boundary
      apply LinearMap.ext
      intro left
      change (IntegralBoundaries D H leftInverse rightInverse critical
        (leftDegree + rightDegree)).mkQ
          (integralCycleProduct D H mode leftDegree rightDegree left right) = 0
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      exact integralCycleProduct_boundary_right D H leftInverse rightInverse critical
        mode leftDegree rightDegree left right boundary)

theorem integralProduct_literal (mode leftDegree rightDegree : ℤ)
    (left : IntegralCohomology D H leftInverse rightInverse critical leftDegree)
    (right : IntegralCohomology D H leftInverse rightInverse critical rightDegree) :
    literalClass D H leftInverse rightInverse critical (leftDegree + rightDegree)
      (integralProduct D H leftInverse rightInverse critical mode leftDegree rightDegree left right) =
    product D H mode (literalClass D H leftInverse rightInverse critical leftDegree left)
      (literalClass D H leftInverse rightInverse critical rightDegree right) := by
  refine Quotient.inductionOn left ?_
  intro left
  refine Quotient.inductionOn right ?_
  intro right
  rfl

def integralCycleB0 (degree : ℤ) :
    IntegralCycles D H degree →ₗ[ℂ] IntegralCycles D H (degree - 1) :=
  (((B D 0).comp (P0 D)).comp (IntegralCycles D H degree).subtype).codRestrict
    (IntegralCycles D H (degree - 1)) (fun state => by
      refine ⟨⟨Submodule.mem_top, ?_⟩,
        B0_P0_ghostPart D degree state.val state.property.2⟩
      apply B0_zeroCycle D H (P0 D state.val) (P0_mem D H leftInverse rightInverse state.val)
      have commute := LinearMap.congr_fun (P0_Q D H leftInverse rightInverse) state.val
      change P0 D (Q D H state.val) = Q D H (P0 D state.val) at commute
      rw [← commute, state.property.1.2, map_zero])

theorem integralCycleB0_boundary (degree : ℤ) (state : IntegralCycles D H degree)
    (boundary : state ∈ IntegralBoundaries D H leftInverse rightInverse critical degree) :
    integralCycleB0 D H leftInverse rightInverse degree state ∈
      IntegralBoundaries D H leftInverse rightInverse critical (degree - 1) := by
  obtain ⟨preimage, equation⟩ := (ghostBoundary_iff D H leftInverse rightInverse critical ⊤
    (top_stable D H) degree state).mp boundary
  have zeroClass : (OriginalBoundaries D H).mkQ (literalCycle D H degree state) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr ⟨preimage.val, equation⟩
  have applied := congrArg (originalB0 D H leftInverse rightInverse critical) zeroClass
  rw [originalB0_mk, map_zero] at applied
  apply integralBoundary_of_literal D H leftInverse rightInverse critical
  exact (Submodule.Quotient.mk_eq_zero _).mp applied

def integralB0 (degree : ℤ) :
    IntegralCohomology D H leftInverse rightInverse critical degree →ₗ[ℂ]
      IntegralCohomology D H leftInverse rightInverse critical (degree - 1) :=
  (IntegralBoundaries D H leftInverse rightInverse critical degree).mapQ
    (IntegralBoundaries D H leftInverse rightInverse critical (degree - 1))
    (integralCycleB0 D H leftInverse rightInverse degree)
    (integralCycleB0_boundary D H leftInverse rightInverse critical degree)

theorem integralB0_literal (degree : ℤ)
    (state : IntegralCohomology D H leftInverse rightInverse critical degree) :
    literalClass D H leftInverse rightInverse critical (degree - 1)
      (integralB0 D H leftInverse rightInverse critical degree state) =
    originalB0 D H leftInverse rightInverse critical
      (literalClass D H leftInverse rightInverse critical degree state) := by
  refine Quotient.inductionOn state ?_
  intro representative
  exact (originalB0_mk D H leftInverse rightInverse critical
    (literalCycle D H degree representative)).symm

def integralComponent (degree : ℤ) : OriginalCohomology D H →ₗ[ℂ]
    IntegralCohomology D H leftInverse rightInverse critical degree :=
  (DirectSum.component ℂ ℤ (IntegralCohomology D H leftInverse rightInverse critical) degree).comp
    ((ghostClassSplit D H leftInverse rightInverse critical ⊤ (top_stable D H)
      (fun _ _ _ => Submodule.mem_top)).comp
      (absoluteOriginalEquiv D H leftInverse rightInverse critical).symm.toLinearMap)

theorem integralComponent_literalClass (degree : ℤ)
    (state : IntegralCohomology D H leftInverse rightInverse critical degree) :
    integralComponent D H leftInverse rightInverse critical degree
      (literalClass D H leftInverse rightInverse critical degree state) = state := by
  change ghostClassSplit D H leftInverse rightInverse critical ⊤ (top_stable D H)
    (fun _ _ _ => Submodule.mem_top)
    ((absoluteOriginalEquiv D H leftInverse rightInverse critical).symm
      (absoluteOriginalEquiv D H leftInverse rightInverse critical
        (ghostClassInclude D H leftInverse rightInverse critical ⊤ (top_stable D H)
          degree state))) degree = state
  rw [LinearEquiv.symm_apply_apply, ghostSplit_include]
  exact DirectSum.lof_apply ℂ degree state

theorem integralComponent_mk (degree : ℤ) (state : OriginalCycles D H) :
    integralComponent D H leftInverse rightInverse critical degree
      ((OriginalBoundaries D H).mkQ state) =
    (IntegralBoundaries D H leftInverse rightInverse critical degree).mkQ
      (ghostCycleProject D H ⊤ (fun _ _ _ => Submodule.mem_top) degree
        ((absoluteCycleEquiv D H).symm state)) := by
  change ghostClassSplit D H leftInverse rightInverse critical ⊤ (top_stable D H)
    (fun _ _ _ => Submodule.mem_top)
    ((boundaries D H leftInverse rightInverse critical ⊤ (top_stable D H)).mkQ
      ((absoluteCycleEquiv D H).symm state)) degree = _
  rw [ghostClassSplit_mk, ghostCycleClassSplit_component]

theorem literalClass_number (degree : ℤ)
    (state : IntegralCohomology D H leftInverse rightInverse critical degree) :
    originalJTransport D H leftInverse rightInverse critical
      (literalClass D H leftInverse rightInverse critical degree state) =
    (degree : ℂ) • literalClass D H leftInverse rightInverse critical degree state := by
  refine Quotient.inductionOn state ?_
  intro representative
  have cycleEquality :
      (⟨nativeJ D representative.val,
        nativeJ_cycle D H representative.val representative.property.1.2⟩ : OriginalCycles D H) =
      (degree : ℂ) • literalCycle D H degree representative := by
    apply Subtype.ext
    exact (ghostPart_iff_number D degree representative.val).mp representative.property.2
  exact (originalJTransport_mk D H leftInverse rightInverse critical
    (literalCycle D H degree representative)).trans
      ((congrArg (OriginalBoundaries D H).mkQ cycleEquality).trans
        ((OriginalBoundaries D H).mkQ.map_smul (degree : ℂ)
          (literalCycle D H degree representative)))

theorem literalClass_integralComponent (degree : ℤ) (state : OriginalCohomology D H)
    (homogeneous : originalJTransport D H leftInverse rightInverse critical state =
      (degree : ℂ) • state) :
    literalClass D H leftInverse rightInverse critical degree
      (integralComponent D H leftInverse rightInverse critical degree state) = state := by
  let absolute := (absoluteOriginalEquiv D H leftInverse rightInverse critical).symm state
  have absoluteHomogeneous : absoluteJ D H leftInverse rightInverse critical absolute =
      (degree : ℂ) • absolute := by
    have transported := congrArg
      (absoluteOriginalEquiv D H leftInverse rightInverse critical).symm homogeneous
    simpa only [originalJTransport, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply, map_smul, absolute] using transported
  have equality := ghostEigenclass_equals_component D H leftInverse rightInverse critical
    ⊤ (top_stable D H) (fun _ _ _ => Submodule.mem_top)
    (fun _ _ => Submodule.mem_top) degree absolute absoluteHomogeneous
  change absoluteOriginalEquiv D H leftInverse rightInverse critical
    (ghostClassInclude D H leftInverse rightInverse critical ⊤ (top_stable D H) degree
      (ghostClassSplit D H leftInverse rightInverse critical ⊤ (top_stable D H)
        (fun _ _ _ => Submodule.mem_top) absolute degree)) = state
  calc
    _ = absoluteOriginalEquiv D H leftInverse rightInverse critical absolute :=
      congrArg (absoluteOriginalEquiv D H leftInverse rightInverse critical) equality.symm
    _ = state := LinearEquiv.apply_symm_apply _ state

theorem literalClass_injective (degree : ℤ) :
    Function.Injective (literalClass D H leftInverse rightInverse critical degree) := by
  intro first second equality
  have projected := congrArg (integralComponent D H leftInverse rightInverse critical degree) equality
  simpa only [integralComponent_literalClass] using projected

def integralBracket (leftDegree rightDegree : ℤ) :
    IntegralCohomology D H leftInverse rightInverse critical leftDegree →ₗ[ℂ]
    IntegralCohomology D H leftInverse rightInverse critical rightDegree →ₗ[ℂ]
    IntegralCohomology D H leftInverse rightInverse critical (leftDegree + rightDegree - 1) :=
  ((mixedBracket D H leftInverse rightInverse critical).compl₁₂
    (literalClass D H leftInverse rightInverse critical leftDegree)
    (literalClass D H leftInverse rightInverse critical rightDegree)).compr₂
      (integralComponent D H leftInverse rightInverse critical (leftDegree + rightDegree - 1))

theorem integralBracket_literal (leftDegree rightDegree : ℤ)
    (left : IntegralCohomology D H leftInverse rightInverse critical leftDegree)
    (right : IntegralCohomology D H leftInverse rightInverse critical rightDegree) :
    literalClass D H leftInverse rightInverse critical (leftDegree + rightDegree - 1)
      (integralBracket D H leftInverse rightInverse critical leftDegree rightDegree left right) =
    mixedBracket D H leftInverse rightInverse critical
      (literalClass D H leftInverse rightInverse critical leftDegree left)
      (literalClass D H leftInverse rightInverse critical rightDegree right) := by
  apply literalClass_integralComponent D H leftInverse rightInverse critical
  exact mixedBracket_integer_degree D H leftInverse rightInverse critical leftDegree rightDegree
    _ _ (literalClass_number D H leftInverse rightInverse critical leftDegree left)
      (literalClass_number D H leftInverse rightInverse critical rightDegree right)

theorem integralBracket_signed_defect (leftDegree rightDegree : ℤ)
    (left : IntegralCohomology D H leftInverse rightInverse critical leftDegree)
    (right : IntegralCohomology D H leftInverse rightInverse critical rightDegree) :
    literalClass D H leftInverse rightInverse critical (leftDegree + rightDegree - 1)
      (integralBracket D H leftInverse rightInverse critical leftDegree rightDegree left right) =
    (-1 : ℂ) ^ (leftDegree % 2).toNat •
      quotientDefectValue D H leftInverse rightInverse critical (leftDegree % 2).toNat
        (literalClass D H leftInverse rightInverse critical leftDegree left)
        (literalClass D H leftInverse rightInverse critical rightDegree right) := by
  rw [integralBracket_literal]
  apply mixedBracket_homogeneous D H leftInverse rightInverse critical
    (leftDegree % 2).toNat (rightDegree % 2).toNat
  exact original_parity_fixed_of_integer D H leftInverse rightInverse critical leftDegree _
    (literalClass_number D H leftInverse rightInverse critical leftDegree left)

def zeroIntegralInclude (degree : ℤ) :
    ghostCohomology D H leftInverse rightInverse critical (zeroSpace D H)
      (zero_stable D H leftInverse rightInverse) degree →ₗ[ℂ]
    IntegralCohomology D H leftInverse rightInverse critical degree :=
  ghostDegreeClassMap D H leftInverse rightInverse critical (zeroSpace D H)
    (zero_stable D H leftInverse rightInverse) ⊤ (top_stable D H) LinearMap.id
    (fun _ _ => Submodule.mem_top) (by simp) (fun _ => by simp) degree

theorem zeroIntegralInclude_literal (degree : ℤ)
    (state : ghostCohomology D H leftInverse rightInverse critical (zeroSpace D H)
      (zero_stable D H leftInverse rightInverse) degree) :
    literalClass D H leftInverse rightInverse critical degree
      (zeroIntegralInclude D H leftInverse rightInverse critical degree state) =
    (originalZeroEquiv D H leftInverse rightInverse critical).symm
      (ghostClassInclude D H leftInverse rightInverse critical (zeroSpace D H)
        (zero_stable D H leftInverse rightInverse) degree state) := by
  refine Quotient.inductionOn state ?_
  intro representative
  change (OriginalBoundaries D H).mkQ ⟨representative.val, representative.property.1.2⟩ =
    (originalZeroEquiv D H leftInverse rightInverse critical).symm
      ((boundaries D H leftInverse rightInverse critical (zeroSpace D H)
        (zero_stable D H leftInverse rightInverse)).mkQ
          (ghostCycleInclude D H (zeroSpace D H) degree representative))
  exact (originalZeroEquiv_symm_mk D H leftInverse rightInverse critical
    (ghostCycleInclude D H (zeroSpace D H) degree representative)).symm

#print axioms native_field_integer_degree
#print axioms integralProduct_literal
#print axioms integralB0_literal
#print axioms integralBracket_literal
#print axioms integralBracket_signed_defect
#print axioms zeroIntegralInclude_literal

end D5.S3.VertexAlgebra.TensorConformal.OriginalIntegralGhostOperationsTransient
