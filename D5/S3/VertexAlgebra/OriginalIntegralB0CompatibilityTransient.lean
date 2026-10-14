import D5.S3.VertexAlgebra.OriginalIntegralGhostCompatibilityTransient
import D5.S3.VertexAlgebra.TensorConformal.OriginalTopologicalApplications

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.VertexAlgebra.TensorConformal.OriginalIntegralB0CompatibilityTransient

open LatticeGeneratingFieldLocality LatticeSugawaraCurrents
open LatticeBcGhostBrstCharge (State Q B)
open LatticeBcGhostNeutralCohomology (OriginalCycles OriginalBoundaries OriginalCohomology)
open OriginalTopologicalApplications
open OriginalBrstReassembly

variable (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
variable (leftInverse : H * gramComplex D = 1) (rightInverse : gramComplex D * H = 1)
  (critical : D.rank = 26)

theorem B0_ghostPart (degree : ℤ) (state : State D)
    (member : state ∈ ghostPart D degree) : B D 0 state ∈ ghostPart D (degree - 1) := by
  apply (ghostPart_iff_number D (degree - 1) _).mpr
  have equality := LinearMap.congr_fun (J_B0 D) state
  change nativeJ D (B D 0 state) - B D 0 (nativeJ D state) = -(B D 0 state) at equality
  have commute : nativeJ D (B D 0 state) = B D 0 (nativeJ D state) - B D 0 state := by
    simpa only [sub_eq_add_neg, add_comm] using sub_eq_iff_eq_add.mp equality
  rw [commute, (ghostPart_iff_number D degree state).mp member, map_smul,
    Int.cast_sub, Int.cast_one, sub_smul, one_smul]

theorem P0_ghostPart (degree : ℤ) (state : State D)
    (member : state ∈ ghostPart D degree) : P0 D state ∈ ghostPart D degree := by
  apply (ghostPart_iff_number D degree _).mpr
  have commute := LinearMap.congr_fun (P0_J D) state
  change P0 D (nativeJ D state) = nativeJ D (P0 D state) at commute
  rw [← commute, (ghostPart_iff_number D degree state).mp member, map_smul]

theorem B0_P0_ghostPart (degree : ℤ) (state : State D)
    (member : state ∈ ghostPart D degree) :
    B D 0 (P0 D state) ∈ ghostPart D (degree - 1) :=
  B0_ghostPart D degree (P0 D state) (P0_ghostPart D degree state member)

theorem zeroJ_B0 (state : zeroCohomology D H leftInverse rightInverse critical) :
    zeroJ D H leftInverse rightInverse critical
      (zeroB0 D H leftInverse rightInverse critical state) =
    zeroB0 D H leftInverse rightInverse critical
      (zeroJ D H leftInverse rightInverse critical state) -
        zeroB0 D H leftInverse rightInverse critical state := by
  obtain ⟨representative, rfl⟩ :=
    (boundaries D H leftInverse rightInverse critical (zeroSpace D H)
      (zero_stable D H leftInverse rightInverse)).mkQ_surjective state
  change (boundaries D H leftInverse rightInverse critical (zeroSpace D H)
    (zero_stable D H leftInverse rightInverse)).mkQ
      (cycleJ D H (zeroSpace D H) (zero_number_stable D H leftInverse rightInverse)
        (zeroCycleB0 D H representative)) =
    (boundaries D H leftInverse rightInverse critical (zeroSpace D H)
      (zero_stable D H leftInverse rightInverse)).mkQ
        (zeroCycleB0 D H (cycleJ D H (zeroSpace D H)
          (zero_number_stable D H leftInverse rightInverse) representative)) -
    (boundaries D H leftInverse rightInverse critical (zeroSpace D H)
      (zero_stable D H leftInverse rightInverse)).mkQ (zeroCycleB0 D H representative)
  rw [← map_sub]
  congr 1
  apply Subtype.ext
  change nativeJ D (B D 0 representative.val) =
    B D 0 (nativeJ D representative.val) - B D 0 representative.val
  have equality := LinearMap.congr_fun (J_B0 D) representative.val
  change nativeJ D (B D 0 representative.val) - B D 0 (nativeJ D representative.val) =
    -(B D 0 representative.val) at equality
  simpa only [sub_eq_add_neg, add_comm] using sub_eq_iff_eq_add.mp equality

theorem zeroB0_integer_degree (degree : ℤ)
    (state : zeroCohomology D H leftInverse rightInverse critical)
    (homogeneous : zeroJ D H leftInverse rightInverse critical state = (degree : ℂ) • state) :
    zeroJ D H leftInverse rightInverse critical
      (zeroB0 D H leftInverse rightInverse critical state) =
        ((degree - 1 : ℤ) : ℂ) • zeroB0 D H leftInverse rightInverse critical state := by
  rw [zeroJ_B0, homogeneous, map_smul, Int.cast_sub, Int.cast_one, sub_smul, one_smul]

def originalJTransport : Module.End ℂ (OriginalCohomology D H) :=
  (absoluteOriginalEquiv D H leftInverse rightInverse critical).toLinearMap.comp
    ((absoluteJ D H leftInverse rightInverse critical).comp
      (absoluteOriginalEquiv D H leftInverse rightInverse critical).symm.toLinearMap)

theorem originalJTransport_mk (state : OriginalCycles D H) :
    originalJTransport D H leftInverse rightInverse critical
      ((OriginalBoundaries D H).mkQ state) =
    (OriginalBoundaries D H).mkQ
      ⟨nativeJ D state.val, nativeJ_cycle D H state.val state.property⟩ := rfl

theorem originalJTransport_absolute
    (state : absoluteCohomology D H leftInverse rightInverse critical) :
    originalJTransport D H leftInverse rightInverse critical
      (absoluteOriginalEquiv D H leftInverse rightInverse critical state) =
    absoluteOriginalEquiv D H leftInverse rightInverse critical
      (absoluteJ D H leftInverse rightInverse critical state) := by
  simp only [originalJTransport, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply]

theorem originalZeroEquiv_J (state : OriginalCohomology D H) :
    originalZeroEquiv D H leftInverse rightInverse critical
      (originalJTransport D H leftInverse rightInverse critical state) =
    zeroJ D H leftInverse rightInverse critical
      (originalZeroEquiv D H leftInverse rightInverse critical state) := by
  simp only [originalZeroEquiv, originalJTransport, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  exact zeroReduction_J D H leftInverse rightInverse critical _

theorem originalZeroEquiv_B0 (state : OriginalCohomology D H) :
    originalZeroEquiv D H leftInverse rightInverse critical
      (originalB0 D H leftInverse rightInverse critical state) =
    zeroB0 D H leftInverse rightInverse critical
      (originalZeroEquiv D H leftInverse rightInverse critical state) := by
  simp only [originalB0, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]

theorem originalZeroEquiv_mk (state : OriginalCycles D H) :
    originalZeroEquiv D H leftInverse rightInverse critical
      ((OriginalBoundaries D H).mkQ state) =
    (boundaries D H leftInverse rightInverse critical (zeroSpace D H)
      (zero_stable D H leftInverse rightInverse)).mkQ
        (cyclesMap D H ⊤ (zeroSpace D H) (P0 D)
          (fun vector _ => P0_mem D H leftInverse rightInverse vector)
          (P0_Q D H leftInverse rightInverse) ((absoluteCycleEquiv D H).symm state)) := rfl

theorem originalB0_mk (state : OriginalCycles D H) :
    originalB0 D H leftInverse rightInverse critical ((OriginalBoundaries D H).mkQ state) =
    (OriginalBoundaries D H).mkQ
      ⟨B D 0 (P0 D state.val), B0_zeroCycle D H (P0 D state.val)
        (P0_mem D H leftInverse rightInverse state.val)
        (cyclesMap D H ⊤ (zeroSpace D H) (P0 D)
          (fun vector _ => P0_mem D H leftInverse rightInverse vector)
          (P0_Q D H leftInverse rightInverse) ((absoluteCycleEquiv D H).symm state)).property.2⟩ := by
  unfold originalB0
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [originalZeroEquiv_mk]
  exact originalZeroEquiv_symm_mk D H leftInverse rightInverse critical _

theorem originalJ_B0 (state : OriginalCohomology D H) :
    originalJTransport D H leftInverse rightInverse critical
      (originalB0 D H leftInverse rightInverse critical state) =
    originalB0 D H leftInverse rightInverse critical
      (originalJTransport D H leftInverse rightInverse critical state) -
        originalB0 D H leftInverse rightInverse critical state := by
  apply (originalZeroEquiv D H leftInverse rightInverse critical).injective
  rw [originalZeroEquiv_J, originalZeroEquiv_B0, map_sub,
    originalZeroEquiv_B0, originalZeroEquiv_J, originalZeroEquiv_B0]
  exact zeroJ_B0 D H leftInverse rightInverse critical _

theorem originalJ_B0_commutator :
    originalJTransport D H leftInverse rightInverse critical *
        originalB0 D H leftInverse rightInverse critical -
      originalB0 D H leftInverse rightInverse critical *
        originalJTransport D H leftInverse rightInverse critical =
      -originalB0 D H leftInverse rightInverse critical := by
  apply LinearMap.ext
  intro state
  change originalJTransport D H leftInverse rightInverse critical
    (originalB0 D H leftInverse rightInverse critical state) -
      originalB0 D H leftInverse rightInverse critical
        (originalJTransport D H leftInverse rightInverse critical state) =
    -(originalB0 D H leftInverse rightInverse critical state)
  rw [originalJ_B0]
  abel

theorem originalB0_integer_degree (degree : ℤ) (state : OriginalCohomology D H)
    (homogeneous : originalJTransport D H leftInverse rightInverse critical state =
      (degree : ℂ) • state) :
    originalJTransport D H leftInverse rightInverse critical
      (originalB0 D H leftInverse rightInverse critical state) =
        ((degree - 1 : ℤ) : ℂ) • originalB0 D H leftInverse rightInverse critical state := by
  rw [originalJ_B0, homogeneous, map_smul, Int.cast_sub, Int.cast_one, sub_smul, one_smul]

theorem original_integer_zero_representative (degree : ℤ) (state : OriginalCohomology D H)
    (homogeneous : originalJTransport D H leftInverse rightInverse critical state =
      (degree : ℂ) • state) :
    ∃ representative : cycles D H (zeroSpace D H),
      representative.val ∈ ghostPart D degree ∧ originalClass D H representative = state := by
  have zeroHomogeneous : zeroJ D H leftInverse rightInverse critical
      (originalZeroEquiv D H leftInverse rightInverse critical state) =
    (degree : ℂ) • originalZeroEquiv D H leftInverse rightInverse critical state := by
    rw [← originalZeroEquiv_J, homogeneous, map_smul]
  obtain ⟨representative, member, equation⟩ := ghostEigenclass_original_representative
    D H leftInverse rightInverse critical (zeroSpace D H)
    (zero_stable D H leftInverse rightInverse)
    (zero_projected D H leftInverse rightInverse (ghostTag D))
    (zero_number_stable D H leftInverse rightInverse) degree
    (originalZeroEquiv D H leftInverse rightInverse critical state) zeroHomogeneous
  refine ⟨representative, member, ?_⟩
  change (OriginalBoundaries D H).mkQ ⟨representative.val, representative.property.2⟩ = state
  rw [← originalZeroEquiv_symm_mk D H leftInverse rightInverse critical, equation]
  exact (originalZeroEquiv D H leftInverse rightInverse critical).symm_apply_apply state

theorem originalB0_integer_zero_representative (degree : ℤ) (state : OriginalCohomology D H)
    (homogeneous : originalJTransport D H leftInverse rightInverse critical state =
      (degree : ℂ) • state) :
    ∃ representative : cycles D H (zeroSpace D H),
      representative.val ∈ ghostPart D (degree - 1) ∧
        originalClass D H representative = originalB0 D H leftInverse rightInverse critical state :=
  original_integer_zero_representative D H leftInverse rightInverse critical (degree - 1)
    (originalB0 D H leftInverse rightInverse critical state)
    (originalB0_integer_degree D H leftInverse rightInverse critical degree state homogeneous)

end D5.S3.VertexAlgebra.TensorConformal.OriginalIntegralB0CompatibilityTransient
