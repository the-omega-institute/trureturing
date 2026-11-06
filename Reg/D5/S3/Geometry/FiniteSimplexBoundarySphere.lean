/- SOURCE STATUS: UNCOMPILED.
   The Law below preserves the source binder modes and order. The packed
   mathematical family is not a faithful direct-source coordinate certificate:
   no source operand has type SourceState. Source layout, universe matching,
   native occurrence selectors and all audit/enrollment checks remain open. -/
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Geometry.FiniteSimplexBoundarySphere

noncomputable section
open Set
open _root_.D5.S3.Geometry.FiniteSimplexBoundarySphere
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Geometry.FiniteSimplexBoundarySphere
universe u

/- This record is only a mathematical adapter for evaluating the actual
   equality at two points. It is not an admitted packing of source coordinates.
   The source has separate type, instance, proof, x and y binders, and has no
   SourceState operand. In particular instance/proof fields cannot be promoted
   to parameter coordinates in CompiledSourceScope.resolve.

   A source-shaped layout was considered using the actual equality predicate,
   booleanPredicate, and its actual x operand as state, with only the label
   type as parameter. Its state type @Simplex Λ finite still depends on the
   source Fintype dictionary. Transport requires that dependency, while resolve
   rejects instance/dictionary coordinates. The remaining equality also uses
   the original y, hm and Nonempty binder. Selecting the partial function psi hm
   as functionOperand leaves the same dictionary dependency in its input type;
   that mode also forbids booleanPredicate. Packing all these values here does not fix either layout. These are static
   obstacles for these layouts, not native diagnostics or a proof that every
   source selection is impossible. No occurrence path or coordinate is guessed. -/
structure SourceState (Λ : Type u) where
  finite : Fintype Λ
  inhabited : Nonempty Λ
  cardinal_bound : 2 ≤ @Fintype.card Λ finite
  left : @Simplex Λ finite
  right : @Simplex Λ finite

private def pack {Λ : Type u} [Fintype Λ] [Nonempty Λ]
    (hm : 2 ≤ Fintype.card Λ) (x y : Simplex Λ) : SourceState Λ :=
  { finite := inferInstance
    inhabited := inferInstance
    cardinal_bound := hm
    left := x
    right := y }

abbrev signature : Signature where
  Params := Type u
  State := fun Λ => SourceState Λ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} := by
  classical
  exact realize signature
    (fun _ _ s =>
      letI := s.finite
      letI := s.inhabited
      decide (psi s.cardinal_bound s.left = psi s.cardinal_bound s.right))
    (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  /- These are precisely the original source binders: implicit label type,
     Fintype and Nonempty instances, then explicit hm, x and y. There is no
     DecidableEq binder. The Boolean reification has a logical bridge below;
     matching this telescope does not certify the packed State/readout fields. -/
  Law R := ∀ {Λ : Type u} [Fintype Λ] [Nonempty Λ]
    (hm : 2 ≤ Fintype.card Λ) (x y : Simplex Λ),
    R.readout () Λ (pack hm x y) = true ↔ boundaryRelation x y

theorem actual_law : arena.{u}.Law actual := by
  classical
  intro Λ finite inhabited hm x y
  letI := finite
  letI := inhabited
  change decide (psi hm x = psi hm y) = true ↔ boundaryRelation x y
  simpa only [decide_eq_true_eq] using (psi_eq_iff hm x y)

theorem bridge_attempt :
    (type_of% (@psi_eq_iff.{u})) ↔ arena.{u}.Law actual := by
  classical
  constructor
  · intro source Λ finite inhabited hm x y
    letI := finite
    letI := inhabited
    change decide (psi hm x = psi hm y) = true ↔ boundaryRelation x y
    simpa only [decide_eq_true_eq] using source hm x y
  · intro law Λ finite inhabited hm x y
    letI := finite
    letI := inhabited
    have h := law hm x y
    change decide (psi hm x = psi hm y) = true ↔ boundaryRelation x y at h
    simpa only [decide_eq_true_eq] using h

private abbrev testΛ : Type u := ULift.{u} (Fin 2)

private def testHm : 2 ≤ Fintype.card testΛ := by simp

private def testBarycenter : Simplex testΛ := barycenterPoint

private def testVertex : Simplex testΛ :=
  ⟨WithLp.toLp 2 (Pi.single (⟨0⟩ : testΛ) (1 : ℝ)), by
    constructor
    · intro i
      simp only [PiLp.toLp_apply, Pi.single_apply]
      split_ifs <;> norm_num
    · simp⟩

private theorem testVertex_boundary : boundary testVertex := by
  exact ⟨(⟨1⟩ : testΛ), by simp [testVertex, Pi.single_apply]⟩

private theorem testBarycenter_interior : ¬ boundary testBarycenter := by
  rintro ⟨i, hi⟩
  change (Fintype.card testΛ : ℝ)⁻¹ = 0 at hi
  have hm : (Fintype.card testΛ : ℝ) ≠ 0 := by positivity
  exact (inv_ne_zero hm) hi

private theorem different_outputs :
    psi testHm testBarycenter ≠ psi testHm testVertex := by
  intro h
  rcases (psi_eq_iff testHm testBarycenter testVertex).1 h with h | ⟨hb, _⟩
  · apply testBarycenter_interior
    rw [h]
    exact testVertex_boundary
  · exact testBarycenter_interior hb

private def equalState : SourceState testΛ :=
  { finite := inferInstance
    inhabited := inferInstance
    cardinal_bound := testHm
    left := testBarycenter
    right := testBarycenter }

private def differentState : SourceState testΛ :=
  { finite := inferInstance
    inhabited := inferInstance
    cardinal_bound := testHm
    left := testBarycenter
    right := testVertex }

private theorem actual_equalState : actual.readout () testΛ equalState = true := by
  classical
  simp [actual, realize, equalState]

private theorem actual_differentState :
    actual.readout () testΛ differentState = false := by
  classical
  simp [actual, realize, differentState, different_outputs]

theorem rejected_law_attempt : ¬ arena.{u}.Law rejected := by
  intro law
  have h := (law (Λ := testΛ) testHm testBarycenter testBarycenter).mpr (Or.inl rfl)
  simpa [rejected, realize, pack] using h

theorem dependence_attempt : ObservationalDependence signature.{u} actual := by
  intro role
  refine ⟨testΛ, equalState, differentState, ?_⟩
  intro h
  rw [actual_equalState, actual_differentState] at h
  cases h

private theorem sensitivity_attempt : Sensitivity arena.{u} actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, rejected_law_attempt⟩
    intro j hj
    exact (hj (Subsingleton.elim j i)).elim
  · intro i
    exact nomatch i

/- Proof terms for the mathematical adapter only. Neither this record nor the
   logical bridge supplies source coordinate, reconstruction or enrollment
   evidence. All terms still need kernel checking. -/
def family_attempt : Registration arena.{u} (type_of% (@psi_eq_iff.{u})) where
  actual := actual
  bridge := bridge_attempt
  variation := ⟨actual_law, rejected, rejected_law_attempt⟩
  sensitivity := sensitivity_attempt
  dependence := dependence_attempt

/- Incomplete direct-source submission, not an accepted audit. The supported
   source contract requires a real selection and exact Params/State/output/
   readout correspondence, which this mathematical adapter does not establish.
   With sourceSelection absent its first source check would fail
   source.selection_missing; this has not been executed here. Filling selectors
   alone would not repair the SourceState mismatch. The raw
   obligation slots remain unknown rather than synthetic True evidence.
   A successful source contract would derive the escape identity; none has
   been derived here. The raw origin remains empty and continuation open. -/
def registration_attempt :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@psi_eq_iff.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Geometry.FiniteSimplexBoundarySphere.__information_unit
  realizationName := `Reg.D5.S3.Geometry.FiniteSimplexBoundarySphere.family_attempt
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family_attempt⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .unknown
  readout := some (by
    classical
    exact realize signature
      (fun _ _ s =>
        letI := s.finite
        letI := s.inhabited
        decide (psi s.cardinal_bound s.left = psi s.cardinal_bound s.right))
      (fun e => nomatch e))
  variation := .unknown
  sensitivity := .unknown
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

/- All other public targets still require individual faithful attempts and
   native selectors. This inventory is not a coverage receipt. -/
def unresolvedAuditTargets : Array Lean.Name := #[
  `D5.S3.Geometry.FiniteSimplexBoundarySphere.psiDenominator_lower_bound,
  `D5.S3.Geometry.FiniteSimplexBoundarySphere.psiRaw_norm_sq,
  `D5.S3.Geometry.FiniteSimplexBoundarySphere.continuous_psiRaw,
  `D5.S3.Geometry.FiniteSimplexBoundarySphere.psi_barycenter,
  `D5.S3.Geometry.FiniteSimplexBoundarySphere.psi_boundary,
  `D5.S3.Geometry.FiniteSimplexBoundarySphere.psi_north_iff,
  `D5.S3.Geometry.FiniteSimplexBoundarySphere.psi_south_iff,
  `D5.S3.Geometry.FiniteSimplexBoundarySphere.psi_nonSouthInverse,
  `D5.S3.Geometry.FiniteSimplexBoundarySphere.nonSouthInverse_coordinate,
  `D5.S3.Geometry.FiniteSimplexBoundarySphere.psi_surjective,
  `D5.S3.Geometry.FiniteSimplexBoundarySphere.simplexBoundaryHomeomorph_representative,
  `D5.S3.Geometry.FiniteSimplexBoundarySphere.simplexBoundaryHomeomorph_barycenter,
  `D5.S3.Geometry.FiniteSimplexBoundarySphere.simplexBoundaryHomeomorph_boundary,
  `D5.S3.Geometry.FiniteSimplexBoundarySphere.reindexSphere_exists,
  `D5.S3.Geometry.FiniteSimplexBoundarySphere.reindexSphere_norm_preserving,
  `D5.S3.Geometry.FiniteSimplexBoundarySphere.simplexBoundaryStdSphere_representative,
  `D5.S3.Geometry.FiniteSimplexBoundarySphere.simplexBoundaryStdSphere_barycenter,
  `D5.S3.Geometry.FiniteSimplexBoundarySphere.simplexBoundaryStdSphere_boundary,
  `D5.S3.Geometry.FiniteSimplexBoundarySphere.zeroExtend_apply_inside,
  `D5.S3.Geometry.FiniteSimplexBoundarySphere.zeroExtend_apply_ghost,
  `D5.S3.Geometry.FiniteSimplexBoundarySphere.zeroExtend_norm_sq,
  `D5.S3.Geometry.FiniteSimplexBoundarySphere.zeroExtend_faceSimplex,
  `D5.S3.Geometry.FiniteSimplexBoundarySphere.faceCoordinateHomeomorph_restrict,
  `D5.S3.Geometry.FiniteSimplexBoundarySphere.faceCoordinateHomeomorph_boundary,
  `D5.S3.Geometry.FiniteSimplexBoundarySphere.zeroExtend_psi_formula,
  `D5.S3.Geometry.FiniteSimplexBoundarySphere.ambientBoundaryHomeomorph_representative,
  `D5.S3.Geometry.FiniteSimplexBoundarySphere.ambientBoundaryHomeomorph_barycenter,
  `D5.S3.Geometry.FiniteSimplexBoundarySphere.ambientBoundaryHomeomorph_boundary,
  `D5.S3.Geometry.FiniteSimplexBoundarySphere.ambientBoundaryHomeomorph_zeroExtend,
  `D5.S3.Geometry.FiniteSimplexBoundarySphere.ambientBoundaryHomeomorph_zeroExtend_barycenter,
  `D5.S3.Geometry.FiniteSimplexBoundarySphere.ambientBoundaryHomeomorph_zeroExtend_boundary
]

end Reg.D5.S3.Geometry.FiniteSimplexBoundarySphere


/- Visibility-only reuse adds nine public helper theorem audit targets.
   These direct source-operand attempts are UNCOMPILED; each still lacks
   a complete four-slot family and compiled source-selection/binding evidence.
   No packed SourceState from the earlier attempt is reused for these Laws. -/
namespace Reg.D5.S3.Geometry.FiniteSimplexBoundarySphere.SharedCollarOperands
universe u
open _root_.D5.S3.Geometry.FiniteSimplexBoundarySphere
variable {Λ : Type u} [Fintype Λ] [DecidableEq Λ] [Nonempty Λ]

abbrev cardinalPositiveSource := type_of% (@cardR_pos.{u})
def cardinalPositive := cardR Λ

abbrev cardinalNonzeroSource := type_of% (@cardR_ne.{u})
def cardinalNonzero := cardR Λ

abbrev minimumAttainedSource := type_of% (@minCoord_attained.{u})
def minimumAttained (x : Simplex Λ) := x.1

abbrev minimumBelowSource := type_of% (@minCoord_le.{u})
def minimumBelow (x : Simplex Λ) (i : Λ) := x.1 i

abbrev sigmaNonnegativeSource := type_of% (@sigma_nonneg.{u})
def sigmaNonnegative (x : Simplex Λ) := sigma x

abbrev sigmaBoundarySource := type_of% (@sigma_eq_zero_iff.{u})
def sigmaBoundary (x : Simplex Λ) := sigma x

abbrev minimumContinuousSource := type_of% (@continuous_minCoord.{u})
def minimumFunction := minCoord (Λ := Λ)

abbrev barycenterGaugeSource := type_of% (@barycenter_gauge.{u})
def barycenterGauge := sigma (barycenterPoint (Λ := Λ))

abbrev vertexBoundarySource := type_of% (@vertex_boundary.{u})
def vertexBoundary (hm : 2 ≤ Fintype.card Λ) (i : Λ) := vertex i

end Reg.D5.S3.Geometry.FiniteSimplexBoundarySphere.SharedCollarOperands
