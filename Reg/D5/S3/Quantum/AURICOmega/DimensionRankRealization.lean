import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.AURICOmega.DimensionRankRealization
import Reg.D5.S3.Quantum.AURICOmega.QuaternionComparisonModel
import Reg.D5.S3.Quantum.AURICOmega.TernaryComparisonProduct
import Reg.D5.S3.Quantum.AURICOmega.TernaryComparisonRankFive
import Reg.Support.DependentFamily

/-! Source-bound audits of the realization of the dimension and feature rank bounds.

The injectivity of the imaginary part is audited through the defining predicate of the hemisphere
`{q | 0 < re q}`; on the whole group the imaginary part identifies `1` and `-1`. The continuity of
transfer and reading is audited through the comparison structure whose transfer or reading is
taken; the rejected readings are maps that separate the point `1` from the rest of the
connected group of unit quaternions, and the observed structures are the unit quaternion model,
its transport along inversion and its discrete reading. The characterization of the realized
pairs is audited through the dimension `d` of the conclusion `3 ≤ d`; the rejected reading `0`
fails at the pair `(3, 5)`. -/

namespace Reg.D5.S3.Quantum.AURICOmega.DimensionRankRealization

open _root_.D5.S3.Quantum.AURICOmega.TernaryComparisonGroup
open _root_.D5.S3.Quantum.AURICOmega.QuaternionComparisonModel
open _root_.D5.S3.Quantum.AURICOmega.DimensionRankRealization
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.D5.S3.Quantum.AURICOmega.TernaryComparisonProduct (discrete transport)
open Reg.D5.S3.Quantum.AURICOmega.QuaternionComparisonModel (one_ne_unitI)

open scoped InnerProductSpace Quaternion

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false
noncomputable section

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

/-! The defining predicate `fun q => 0 < re q` of the hemisphere in `injOn_im_of_re_pos`. -/
namespace Hemisphere

abbrev signature : Signature where
  Params := Unit
  State _ := unitary ℍ[ℝ] → Prop
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Set (unitary ℍ[ℝ])
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ P => Set.ofPred P) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => Set.univ) (fun e => nomatch e)

/-- Retain the complete statement of `injOn_im_of_re_pos`. -/
abbrev arena : Arena where
  signature := signature
  Law r := Set.InjOn (fun q : unitary ℍ[ℝ] => (q : ℍ[ℝ]).im)
    (r.readout () () fun q : unitary ℍ[ℝ] => 0 < (q : ℍ[ℝ]).re)

/-- On all unit quaternions the imaginary part identifies `1` and `-1`. -/
theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h' : Set.InjOn (fun q : unitary ℍ[ℝ] => (q : ℍ[ℝ]).im) Set.univ := h
  have heq := h' (Set.mem_univ (1 : unitary ℍ[ℝ])) (Set.mem_univ (-1 : unitary ℍ[ℝ]))
    (by simp [Unitary.coe_neg])
  exact Reg.D5.S3.Quantum.AURICOmega.TernaryComparisonRankFive.one_ne_neg_one heq

/-- The hemisphere contains `1`; the set of the predicate `False` does not. -/
theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), fun q : unitary ℍ[ℝ] => 0 < (q : ℍ[ℝ]).re, fun _ => False, fun h => ?_⟩
  have h' : {q : unitary ℍ[ℝ] | 0 < (q : ℍ[ℝ]).re} = {_q : unitary ℍ[ℝ] | False} := h
  have h1 : (1 : unitary ℍ[ℝ]) ∈ {q : unitary ℍ[ℝ] | 0 < (q : ℍ[ℝ]).re} := by simp
  rw [h'] at h1
  exact h1

abbrev sourceStatement : Prop := type_of% injOn_im_of_re_pos

def source_registration : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨injOn_im_of_re_pos, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

end Hemisphere

/-! The comparison structure whose transfer is taken in `continuous_tri_quaternionModel`. -/
namespace Transfer

abbrev signature : Signature where
  Params := Unit
  State _ := TernaryComparison (unitary ℍ[ℝ])
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := unitary ℍ[ℝ] → unitary ℍ[ℝ] → unitary ℍ[ℝ] → unitary ℍ[ℝ]
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ C => C.tri) (fun e => nomatch e)

open Classical in
def rejected : Realization signature :=
  realize signature (fun _ _ _ x _ _ => if x = 1 then 1 else unitI) (fun e => nomatch e)

/-- Retain the complete statement of `continuous_tri_quaternionModel`. -/
abbrev arena : Arena where
  signature := signature
  Law r := Continuous fun p : unitary ℍ[ℝ] × unitary ℍ[ℝ] × unitary ℍ[ℝ] =>
    r.readout () () quaternionModel p.1 p.2.1 p.2.2

/-- A map that is `1` at `1` and `i` elsewhere is not continuous on the connected group. -/
theorem rejected_law : ¬ arena.Law rejected := by
  classical
  intro h
  have h' : Continuous fun p : unitary ℍ[ℝ] × unitary ℍ[ℝ] × unitary ℍ[ℝ] =>
      if p.1 = 1 then (1 : unitary ℍ[ℝ]) else unitI := h
  have hg := h'.comp (continuous_id.prodMk continuous_const :
    Continuous fun x : unitary ℍ[ℝ] => (x, ((1 : unitary ℍ[ℝ]), (1 : unitary ℍ[ℝ]))))
  refine not_continuous_of_isolates _ unitI ?_ ?_ hg
  · simpa using one_ne_unitI
  · intro x hx
    simp [hx]

/-- The quaternion model and its transport along inversion have different transfers. -/
theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), quaternionModel, transport (Equiv.inv (unitary ℍ[ℝ])) quaternionModel,
    fun h => ?_⟩
  obtain ⟨a, b, c, hne⟩ := quaternionModel_noncommutative
  have h' : quaternionModel.tri = (transport (Equiv.inv (unitary ℍ[ℝ])) quaternionModel).tri := h
  have ht := congrFun (congrFun (congrFun h' a) b) c
  change a * b⁻¹ * c = (a⁻¹ * b⁻¹⁻¹ * c⁻¹)⁻¹ at ht
  apply hne
  change a * b⁻¹ * c = c * b⁻¹ * a
  rw [ht]
  group

abbrev sourceStatement : Prop := type_of% continuous_tri_quaternionModel

def source_registration : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨continuous_tri_quaternionModel, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

end Transfer

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

/-! The dimension `d` in the conclusion `3 ≤ d` of `exists_model_iff`. -/
namespace Pairs

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ s => s) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Retain the complete statement of `exists_model_iff`, both sides of the equivalence and both
conjuncts of its right side. -/
abbrev arena : Arena where
  signature := signature
  Law rd := ∀ d r : ℕ,
    (∃ (M : Type) (_ : TopologicalSpace M) (_ : LocallyCompactSpace M) (_ : PreconnectedSpace M)
        (C : TernaryComparison M) (o : M) (V : Set M) (f : M → EuclideanSpace ℝ (Fin d)),
        (Continuous fun p : M × M × M => C.tri p.1 p.2.1 p.2.2) ∧
        (∀ x, ContinuousAt (C.kappa x) x) ∧ C.Noncommutative ∧ C.HasFeatureRank r ∧
        V ∈ nhds o ∧ ContinuousOn f V ∧ Set.InjOn f V) ↔ 3 ≤ rd.readout () () d ∧ 5 ≤ r

/-- The pair `(3, 5)` is realized, so the reading `0` would give `3 ≤ 0`. -/
theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := (h 3 5).1 ((exists_model_iff 3 5).2 ⟨le_rfl, le_rfl⟩)
  exact absurd hh.1 (by decide)

theorem dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨(), 3, 0, ?_⟩
  decide

abbrev sourceStatement : Prop := type_of% exists_model_iff

def source_registration : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨exists_model_iff, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

end Pairs

def injOn_im_of_re_pos_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      injOn_im_of_re_pos (Realization Hemisphere.signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.AURICOmega.DimensionRankRealization.injOn_im_of_re_pos_unit
  realizationName := `Reg.D5.S3.Quantum.AURICOmega.DimensionRankRealization.Hemisphere.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨Hemisphere.arena⟩
  objectArena := .source ⟨Hemisphere.arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Hemisphere.arena ⟨Hemisphere.source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize Hemisphere.signature (fun _ _ P => Set.ofPred P) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.AURICOmega.DimensionRankRealization
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

def continuous_tri_quaternionModel_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      continuous_tri_quaternionModel (Realization Transfer.signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.AURICOmega.DimensionRankRealization.continuous_tri_quaternionModel_unit
  realizationName := `Reg.D5.S3.Quantum.AURICOmega.DimensionRankRealization.Transfer.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨Transfer.arena⟩
  objectArena := .source ⟨Transfer.arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Transfer.arena ⟨Transfer.source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize Transfer.signature (fun _ _ C => C.tri) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.AURICOmega.DimensionRankRealization
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "body", "fn", "fn", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

def continuous_kappa_quaternionModel_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      continuous_kappa_quaternionModel (Realization Reading.signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.AURICOmega.DimensionRankRealization.continuous_kappa_quaternionModel_unit
  realizationName := `Reg.D5.S3.Quantum.AURICOmega.DimensionRankRealization.Reading.source_registration
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
    owner := `D5.S3.Quantum.AURICOmega.DimensionRankRealization
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

def exists_model_iff_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      exists_model_iff (Realization Pairs.signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.AURICOmega.DimensionRankRealization.exists_model_iff_unit
  realizationName := `Reg.D5.S3.Quantum.AURICOmega.DimensionRankRealization.Pairs.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨Pairs.arena⟩
  objectArena := .source ⟨Pairs.arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Pairs.arena ⟨Pairs.source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize Pairs.signature (fun _ _ s => s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.AURICOmega.DimensionRankRealization
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Quantum.AURICOmega.DimensionRankRealization
