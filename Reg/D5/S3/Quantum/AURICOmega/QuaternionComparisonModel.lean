import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.AURICOmega.QuaternionComparisonModel
import Reg.D5.S3.Quantum.AURICOmega.TernaryComparisonProduct
import Reg.Support.DependentFamily

/-! Source-bound audits of the component formula for the quaternion inner product, of the inner
product of features, of the radius of the sphere of unit quaternions, of the preconnectedness of
the unit quaternions and of the continuity of the reading, and full-telescope source applications
for the four closed statements about the model.
Those applications supply only the original statements; they supply no enrolled-template
readout, source selection, whole-family intervention, sensitivity or observational dependence.
The unfinished registrations are tracked at
https://github.com/the-omega-institute/trureturing/issues/31741.

The continuity of the reading is audited through the comparison structure whose reading is
taken; the rejected reading is the indicator of the diagonal, which separates the point `1` from
the rest of the connected group of unit quaternions, and the observed structures are the unit
quaternion model and its discrete reading. -/

namespace Reg.D5.S3.Quantum.AURICOmega.QuaternionComparisonModel

open _root_.D5.S3.Quantum.AURICOmega.QuaternionComparisonModel
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.AURICOmega.TernaryComparisonGroup (TernaryComparison)
open Reg.D5.S3.Quantum.AURICOmega.TernaryComparisonProduct (discrete)

open scoped InnerProductSpace Quaternion

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false
noncomputable section

namespace InnerComponents

/-- Observe the real inner product against a fixed first quaternion. -/
abbrev signature : Signature where
  Params := ℍ[ℝ]
  State _ := ℍ[ℝ]
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p s => ⟪p, s⟫_ℝ) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)

/-- Retain the complete telescope of `inner_eq_components`. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∀ p q : ℍ[ℝ],
    r.readout () p q = p.re * q.re + p.imI * q.imI + p.imJ * q.imJ + p.imK * q.imK

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 0 0
  norm_num [rejected, realize] at hh

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 1, 0, ?_⟩
  change ⟪(1 : ℍ[ℝ]), 1⟫_ℝ ≠ ⟪(1 : ℍ[ℝ]), 0⟫_ℝ
  rw [inner_eq_components, inner_eq_components]
  norm_num

def source_registration : Registration arena (type_of% inner_eq_components) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨inner_eq_components, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

end InnerComponents

def inner_eq_components_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      inner_eq_components (Realization InnerComponents.signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.AURICOmega.QuaternionComparisonModel.inner_eq_components_unit
  realizationName := `Reg.D5.S3.Quantum.AURICOmega.QuaternionComparisonModel.InnerComponents.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨InnerComponents.arena⟩
  objectArena := .source ⟨InnerComponents.arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source InnerComponents.arena ⟨InnerComponents.source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize InnerComponents.signature
    (fun _ p s => ⟪p, s⟫_ℝ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.AURICOmega.QuaternionComparisonModel
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }


/-! The half-shifted inner product against a fixed first quaternion, for `inner_feature`. -/
namespace FeatureReading

abbrev signature : Signature where
  Params := ℍ[ℝ]
  State _ := ℍ[ℝ]
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p s => (1 + ⟪p, s⟫_ℝ) / 2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)

/-- Retain the complete argument telescope of `inner_feature`. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∀ p q : ℍ[ℝ], ⟪feature p, feature q⟫_ℝ = r.readout () p q

/-- The features of zero have inner product one half, not two. -/
theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh : ⟪feature 0, feature 0⟫_ℝ = 2 := h 0 0
  rw [inner_feature, inner_zero_left] at hh
  norm_num at hh

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 1, 0, ?_⟩
  change (1 + ⟪(1 : ℍ[ℝ]), 1⟫_ℝ) / 2 ≠ (1 + ⟪(1 : ℍ[ℝ]), 0⟫_ℝ) / 2
  rw [inner_zero_right, real_inner_self_eq_norm_sq, norm_one]
  norm_num

def source_registration : Registration arena (type_of% inner_feature) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨inner_feature, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

end FeatureReading

def inner_feature_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      inner_feature (Realization FeatureReading.signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.AURICOmega.QuaternionComparisonModel.inner_feature_unit
  realizationName := `Reg.D5.S3.Quantum.AURICOmega.QuaternionComparisonModel.FeatureReading.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨FeatureReading.arena⟩
  objectArena := .source ⟨FeatureReading.arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source FeatureReading.arena ⟨FeatureReading.source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize FeatureReading.signature
    (fun _ p s => (1 + ⟪p, s⟫_ℝ) / 2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.AURICOmega.QuaternionComparisonModel
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg", "arg", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

/-! The radius of the sphere in `coe_unitary_eq_sphere`. -/
namespace SphereRadius

/-- Observe the sphere about zero in the quaternions as a function of its radius. -/
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Set ℍ[ℝ]
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ r => Metric.sphere (0 : ℍ[ℝ]) r) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => Metric.sphere (0 : ℍ[ℝ]) 2) (fun e => nomatch e)

/-- Retain the complete statement of `coe_unitary_eq_sphere`. -/
abbrev arena : Arena where
  signature := signature
  Law r := (unitary ℍ[ℝ] : Set ℍ[ℝ]) = r.readout () () 1

/-- The quaternion one is a unit quaternion of norm one, not two. -/
theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h' : (unitary ℍ[ℝ] : Set ℍ[ℝ]) = Metric.sphere (0 : ℍ[ℝ]) 2 := h
  have h2 : (1 : ℍ[ℝ]) ∈ (unitary ℍ[ℝ] : Set ℍ[ℝ]) := one_mem (unitary ℍ[ℝ])
  rw [h', mem_sphere_zero_iff_norm, norm_one] at h2
  norm_num at h2

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 1, 2, fun h => ?_⟩
  have h' : Metric.sphere (0 : ℍ[ℝ]) 1 = Metric.sphere (0 : ℍ[ℝ]) 2 := h
  have h2 : (1 : ℍ[ℝ]) ∈ Metric.sphere (0 : ℍ[ℝ]) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_one]
  rw [h', mem_sphere_zero_iff_norm, norm_one] at h2
  norm_num at h2

def source_registration : Registration arena (type_of% coe_unitary_eq_sphere) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨coe_unitary_eq_sphere, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

end SphereRadius

def coe_unitary_eq_sphere_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      coe_unitary_eq_sphere (Realization SphereRadius.signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.AURICOmega.QuaternionComparisonModel.coe_unitary_eq_sphere_unit
  realizationName := `Reg.D5.S3.Quantum.AURICOmega.QuaternionComparisonModel.SphereRadius.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨SphereRadius.arena⟩
  objectArena := .source ⟨SphereRadius.arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source SphereRadius.arena ⟨SphereRadius.source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize SphereRadius.signature
    (fun _ _ r => Metric.sphere (0 : ℍ[ℝ]) r) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.AURICOmega.QuaternionComparisonModel
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

/-- The unit quaternion `1` differs from `i`. -/
theorem one_ne_unitI : (1 : unitary ℍ[ℝ]) ≠ unitI := by
  intro h
  have h' := congrArg (fun q : unitary ℍ[ℝ] => (q : ℍ[ℝ]).re) h
  change ((1 : unitary ℍ[ℝ]) : ℍ[ℝ]).re = (unitI : ℍ[ℝ]).re at h'
  simp [unitI] at h'

/-- A topology on the unit quaternions in which every set is open is not preconnected. -/
theorem not_preconnectedSpace_of_forall_isOpen (τ : TopologicalSpace (unitary ℍ[ℝ]))
    (hτ : ∀ s : Set (unitary ℍ[ℝ]), @IsOpen _ τ s) : ¬ @PreconnectedSpace _ τ := by
  intro hp
  have hc : @IsClopen _ τ {1} := ⟨⟨hτ _⟩, hτ _⟩
  rcases (@isClopen_iff _ τ hp _).mp hc with h0 | h1
  · exact Set.singleton_ne_empty _ h0
  · have hi : unitI ∈ ({1} : Set (unitary ℍ[ℝ])) := by rw [h1]; trivial
    exact one_ne_unitI (Set.mem_singleton_iff.mp hi).symm

/-- Every set is open in the discrete topology. -/
theorem isOpen_bot_set {X : Type} (s : Set X) : @IsOpen X ⊥ s :=
  @isOpen_discrete X ⊥ (discreteTopology_bot X) s

/-! The ambient topology of the quaternions in `preconnectedSpace_unitary`. -/
namespace AmbientTopology

/-- Observe the subspace topology of the unit quaternions as a function of the topology of the
quaternions. -/
abbrev signature : Signature where
  Params := Unit
  State _ := TopologicalSpace ℍ[ℝ]
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := TopologicalSpace (unitary ℍ[ℝ])
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ t => @instTopologicalSpaceSubtype ℍ[ℝ] (· ∈ unitary ℍ[ℝ]) t)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => ⊥) (fun e => nomatch e)

/-- Retain the complete statement of `preconnectedSpace_unitary`. -/
abbrev arena : Arena where
  signature := signature
  Law r := @PreconnectedSpace (unitary ℍ[ℝ]) (r.readout () () (by infer_instance))

/-- The discrete topology on the unit quaternions is not preconnected. -/
theorem rejected_law : ¬ arena.Law rejected :=
  not_preconnectedSpace_of_forall_isOpen ⊥ isOpen_bot_set

/-- The discrete topology of the quaternions induces the discrete topology on the unit
quaternions, which differs from the connected subspace topology. -/
theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (by infer_instance), ⊥, fun h => ?_⟩
  have hp : @PreconnectedSpace (unitary ℍ[ℝ])
      (@instTopologicalSpaceSubtype ℍ[ℝ] (· ∈ unitary ℍ[ℝ]) ⊥) := by
    have h' : @instTopologicalSpaceSubtype ℍ[ℝ] (· ∈ unitary ℍ[ℝ]) (by infer_instance) =
        @instTopologicalSpaceSubtype ℍ[ℝ] (· ∈ unitary ℍ[ℝ]) ⊥ := h
    rw [← h']
    exact preconnectedSpace_unitary
  refine not_preconnectedSpace_of_forall_isOpen
    (@instTopologicalSpaceSubtype ℍ[ℝ] (· ∈ unitary ℍ[ℝ]) ⊥) (fun s => ?_) hp
  exact (@isOpen_induced_iff _ _ ⊥ s Subtype.val).2
    ⟨Subtype.val '' s, isOpen_bot_set _, Set.preimage_image_eq _ Subtype.val_injective⟩

abbrev sourceStatement : Prop := type_of% preconnectedSpace_unitary

def source_registration : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨preconnectedSpace_unitary, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

end AmbientTopology

def preconnectedSpace_unitary_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      preconnectedSpace_unitary (Realization AmbientTopology.signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.AURICOmega.QuaternionComparisonModel.preconnectedSpace_unitary_unit
  realizationName := `Reg.D5.S3.Quantum.AURICOmega.QuaternionComparisonModel.AmbientTopology.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨AmbientTopology.arena⟩
  objectArena := .source ⟨AmbientTopology.arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source AmbientTopology.arena ⟨AmbientTopology.source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize AmbientTopology.signature
    (fun _ _ t => @instTopologicalSpaceSubtype ℍ[ℝ] (· ∈ unitary ℍ[ℝ]) t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.AURICOmega.QuaternionComparisonModel
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

/-- The point `1` is not open in the connected group of unit quaternions. -/
theorem not_isOpen_singleton_one : ¬ IsOpen ({1} : Set (unitary ℍ[ℝ])) := by
  intro h
  have := preconnectedSpace_unitary
  have hc : IsClopen ({1} : Set (unitary ℍ[ℝ])) := ⟨isClosed_singleton, h⟩
  rcases isClopen_iff.mp hc with h0 | h1
  · exact Set.singleton_ne_empty _ h0
  · have hi : unitI ∈ ({1} : Set (unitary ℍ[ℝ])) := by rw [h1]; trivial
    exact one_ne_unitI (Set.mem_singleton_iff.mp hi).symm

/-- A continuous map taking one value at `1` and another value everywhere else does not exist. -/
theorem not_continuous_of_isolates {X : Type} [TopologicalSpace X] [T1Space X]
    (g : unitary ℍ[ℝ] → X) (b : X) (hb : g 1 ≠ b) (hg : ∀ x, x ≠ 1 → g x = b) :
    ¬ Continuous g := by
  intro hc
  apply not_isOpen_singleton_one
  have hpre : g ⁻¹' {b}ᶜ = {1} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff]
    constructor
    · intro hx
      by_contra hne
      exact hx (hg x hne)
    · rintro rfl
      exact hb
  rw [← hpre]
  exact isOpen_compl_singleton.preimage hc

/-! The comparison structure whose reading is taken in `continuous_kappa_quaternionModel`. -/
namespace Reading

abbrev signature : Signature where
  Params := Unit
  State _ := TernaryComparison (unitary ℍ[ℝ])
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := unitary ℍ[ℝ] → unitary ℍ[ℝ] → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ C => C.kappa) (fun e => nomatch e)

open Classical in
def rejected : Realization signature :=
  realize signature (fun _ _ _ x y => if x = y then 1 else 0) (fun e => nomatch e)

/-- Retain the complete statement of `continuous_kappa_quaternionModel`. -/
abbrev arena : Arena where
  signature := signature
  Law r := Continuous fun p : unitary ℍ[ℝ] × unitary ℍ[ℝ] =>
    r.readout () () quaternionModel p.1 p.2

/-- The indicator of the diagonal is not continuous on pairs of unit quaternions. -/
theorem rejected_law : ¬ arena.Law rejected := by
  classical
  intro h
  have h' : Continuous fun p : unitary ℍ[ℝ] × unitary ℍ[ℝ] =>
      if p.1 = p.2 then (1 : ℝ) else 0 := h
  have hg := h'.comp (continuous_id.prodMk continuous_const :
    Continuous fun x : unitary ℍ[ℝ] => (x, (1 : unitary ℍ[ℝ])))
  refine not_continuous_of_isolates _ (0 : ℝ) ?_ ?_ hg
  · simp
  · intro x hx
    simp [hx]

/-- The quaternion model and its discrete reading differ at `(1, i)`. -/
theorem dependence : ObservationalDependence signature actual := by
  classical
  intro i
  refine ⟨(), quaternionModel, discrete quaternionModel, fun h => ?_⟩
  have h' : quaternionModel.kappa = (discrete quaternionModel).kappa := h
  have h1 := congrFun (congrFun h' 1) unitI
  have h0 : quaternionModel.kappa 1 unitI = 1 / 2 := by
    change (1 + ⟪((1 : unitary ℍ[ℝ]) : ℍ[ℝ]), (unitI : ℍ[ℝ])⟫_ℝ) / 2 = 1 / 2
    rw [inner_eq_components]
    simp [unitI]
  have h2 : (discrete quaternionModel).kappa 1 unitI = 0 := by
    simp [discrete, one_ne_unitI]
  rw [h0, h2] at h1
  norm_num at h1

abbrev sourceStatement : Prop := type_of% continuous_kappa_quaternionModel

def source_registration : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨continuous_kappa_quaternionModel, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

end Reading

def continuous_kappa_quaternionModel_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      continuous_kappa_quaternionModel (Realization Reading.signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.AURICOmega.QuaternionComparisonModel.continuous_kappa_quaternionModel_unit
  realizationName := `Reg.D5.S3.Quantum.AURICOmega.QuaternionComparisonModel.Reading.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨Reading.arena⟩
  objectArena := .source ⟨Reading.arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Reading.arena ⟨Reading.source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize Reading.signature (fun _ _ C => C.kappa) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.AURICOmega.QuaternionComparisonModel
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

abbrev noncommutativeSourceScope : Prop := type_of% quaternionModel_noncommutative

theorem noncommutative_source_application : noncommutativeSourceScope :=
  quaternionModel_noncommutative

abbrev touchesZeroSourceScope : Prop := type_of% quaternionModel_touchesZero

theorem touchesZero_source_application : touchesZeroSourceScope :=
  quaternionModel_touchesZero

abbrev chainConnectedSourceScope : Prop := type_of% quaternionModel_chainConnected

theorem chainConnected_source_application : chainConnectedSourceScope :=
  quaternionModel_chainConnected

abbrev hasFeatureRankFiveSourceScope : Prop := type_of% quaternionModel_hasFeatureRank_five

theorem hasFeatureRank_five_source_application : hasFeatureRankFiveSourceScope :=
  quaternionModel_hasFeatureRank_five

end

end Reg.D5.S3.Quantum.AURICOmega.QuaternionComparisonModel
