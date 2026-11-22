import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.AURICOmega.DimensionRankRealization
import Reg.D5.S3.Quantum.AURICOmega.QuaternionComparisonModel
import Reg.D5.S3.Quantum.AURICOmega.TernaryComparisonProduct
import Reg.D5.S3.Quantum.AURICOmega.TernaryComparisonRankFive
import Reg.Support.DependentFamily

/-! Source-bound audits of the realization of the dimension and feature rank bounds.

The classification of the sets on which the imaginary part is injective is audited through the
set `S` of the injectivity assertion; the rejected reading `Set.univ` fails at `S = ∅`, because on
the whole group the imaginary part identifies `1` and `-1`. The largest such set containing the
open hemisphere is audited through the defining predicate of the closed hemisphere
`{q | 0 ≤ re q}`; the rejected reading `Set.univ` is not a set of injectivity for the same
reason. The continuity of the transfer is audited through the comparison structure whose
transfer is taken; the rejected reading is a map that separates the point `1` from the rest of the
connected group of unit quaternions, and the observed structures are the unit quaternion model and
its transport along inversion. The four equivalent conditions on the realized pairs are audited
through the dimension `d` of the third condition `3 ≤ d`; the rejected reading `0` fails at the
pair `(3, 5)`. -/

namespace Reg.D5.S3.Quantum.AURICOmega.DimensionRankRealization

open _root_.D5.S3.Quantum.AURICOmega.TernaryComparisonGroup
open _root_.D5.S3.Quantum.AURICOmega.QuaternionComparisonModel
open _root_.D5.S3.Quantum.AURICOmega.DimensionRankRealization
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.D5.S3.Quantum.AURICOmega.TernaryComparisonProduct (transport)
open Reg.D5.S3.Quantum.AURICOmega.QuaternionComparisonModel (one_ne_unitI not_continuous_of_isolates)

open scoped Quaternion

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false
noncomputable section

universe u

/-- On all unit quaternions the imaginary part identifies `1` and `-1`. -/
theorem not_injOn_im_univ :
    ¬ Set.InjOn (fun q : unitary ℍ[ℝ] => (q : ℍ[ℝ]).im) Set.univ := fun h =>
  Reg.D5.S3.Quantum.AURICOmega.TernaryComparisonRankFive.one_ne_neg_one
    (h (Set.mem_univ (1 : unitary ℍ[ℝ])) (Set.mem_univ (-1 : unitary ℍ[ℝ]))
      (by simp [Unitary.coe_neg]))

/-! The set `S` on which `injOn_im_iff` asserts the injectivity of the imaginary part. -/
namespace Classification

abbrev signature : Signature where
  Params := Unit
  State _ := Set (unitary ℍ[ℝ])
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Set (unitary ℍ[ℝ])
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ S => S) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => Set.univ) (fun e => nomatch e)

/-- Retain the complete statement of `injOn_im_iff`. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∀ S : Set (unitary ℍ[ℝ]),
    Set.InjOn (fun q : unitary ℍ[ℝ] => (q : ℍ[ℝ]).im) (r.readout () () S) ↔
      ∀ q ∈ S, -star q ∈ S → (q : ℍ[ℝ]).re = 0

/-- At `S = ∅` the condition on the right holds, while the rejected reading asks for
injectivity on all unit quaternions. -/
theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact not_injOn_im_univ ((h ∅).2 fun q hq => False.elim hq)

/-- The empty set and the whole group are read out differently. -/
theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), ∅, Set.univ, fun h => ?_⟩
  have h' : (∅ : Set (unitary ℍ[ℝ])) = Set.univ := h
  have h1 : (1 : unitary ℍ[ℝ]) ∈ (∅ : Set (unitary ℍ[ℝ])) := by
    rw [h']
    exact Set.mem_univ _
  exact h1

abbrev sourceStatement : Prop := type_of% injOn_im_iff

def source_registration : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨injOn_im_iff, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

end Classification

/-! The defining predicate `fun q => 0 ≤ re q` of the closed hemisphere in
`isGreatest_injOn_im`. -/
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

/-- Retain the complete statement of `isGreatest_injOn_im`. -/
abbrev arena : Arena where
  signature := signature
  Law r := IsGreatest {S : Set (unitary ℍ[ℝ]) | {q : unitary ℍ[ℝ] | 0 < (q : ℍ[ℝ]).re} ⊆ S ∧
      Set.InjOn (fun q : unitary ℍ[ℝ] => (q : ℍ[ℝ]).im) S}
    (r.readout () () fun q : unitary ℍ[ℝ] => 0 ≤ (q : ℍ[ℝ]).re)

/-- The whole group is not a set on which the imaginary part is injective. -/
theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h' : Set.InjOn (fun q : unitary ℍ[ℝ] => (q : ℍ[ℝ]).im) Set.univ := h.1.2
  exact not_injOn_im_univ h'

/-- The hemisphere contains `1`; the set of the predicate `False` does not. -/
theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), fun q : unitary ℍ[ℝ] => 0 ≤ (q : ℍ[ℝ]).re, fun _ => False, fun h => ?_⟩
  have h' : {q : unitary ℍ[ℝ] | 0 ≤ (q : ℍ[ℝ]).re} = {_q : unitary ℍ[ℝ] | False} := h
  have h1 : (1 : unitary ℍ[ℝ]) ∈ {q : unitary ℍ[ℝ] | 0 ≤ (q : ℍ[ℝ]).re} := by simp
  rw [h'] at h1
  exact h1

abbrev sourceStatement : Prop := type_of% isGreatest_injOn_im

def source_registration : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨isGreatest_injOn_im, rejected, rejected_law⟩
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

/-! The dimension `d` in the third condition `3 ≤ d` of `exists_model_tfae`. -/
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

/-- Retain the complete statement of `exists_model_tfae` in the universe `u`, all four
conditions and both conjuncts of the third. -/
abbrev arena : Arena where
  signature := signature
  Law rd := ∀ d r : ℕ,
    List.TFAE [
      ∃ (M : Type u) (_ : TopologicalSpace M) (_ : LocallyCompactSpace M)
        (_ : PreconnectedSpace M) (C : TernaryComparison M) (o : M) (V : Set M)
        (f : M → EuclideanSpace ℝ (Fin d)),
        (Continuous fun p : M × M × M => C.tri p.1 p.2.1 p.2.2) ∧
        (∀ x, ContinuousAt (C.kappa x) x) ∧ C.Noncommutative ∧ C.HasFeatureRank r ∧
        V ∈ nhds o ∧ ContinuousOn f V ∧ Set.InjOn f V,
      ∃ (M : Type u) (_ : TopologicalSpace M) (_ : CompactSpace M) (_ : T2Space M)
        (_ : PathConnectedSpace M) (C : TernaryComparison M) (o : M) (V : Set M)
        (f : M → EuclideanSpace ℝ (Fin d)),
        (Continuous fun p : M × M × M => C.tri p.1 p.2.1 p.2.2) ∧
        (Continuous fun p : M × M => C.kappa p.1 p.2) ∧ C.Noncommutative ∧ C.HasFeatureRank r ∧
        IsOpen V ∧ o ∈ V ∧ Continuous f ∧ Set.InjOn f V,
      3 ≤ rd.readout () () d ∧ 5 ≤ r,
      ∃ (V : Set (unitary ℍ[ℝ])) (f : unitary ℍ[ℝ] → EuclideanSpace ℝ (Fin d)),
        quaternionModel.HasFeatureRank r ∧ IsOpen V ∧ 1 ∈ V ∧ Continuous f ∧ Set.InjOn f V]

/-- The pair `(3, 5)` is realized, so the reading `0` would give `3 ≤ 0`. -/
theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have h35 : 3 ≤ 3 ∧ 5 ≤ 5 := ⟨le_rfl, le_rfl⟩
  have hh := ((h 3 5).out 1 3).1 (((exists_model_tfae.{u} 3 5).out 1 3).2 h35)
  exact absurd hh.1 (by decide)

theorem dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨(), 3, 0, ?_⟩
  decide

abbrev sourceStatement : Prop := type_of% @exists_model_tfae.{u}

def source_registration : Registration arena.{u} sourceStatement.{u} where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_model_tfae.{u}, rejected, rejected_law.{u}⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law.{u}⟩
    · intro e
      exact nomatch e
  dependence := dependence

end Pairs

def injOn_im_iff_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      injOn_im_iff (Realization Classification.signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.AURICOmega.DimensionRankRealization.injOn_im_iff_unit
  realizationName := `Reg.D5.S3.Quantum.AURICOmega.DimensionRankRealization.Classification.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨Classification.arena⟩
  objectArena := .source ⟨Classification.arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Classification.arena ⟨Classification.source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize Classification.signature (fun _ _ S => S) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.AURICOmega.DimensionRankRealization
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

def isGreatest_injOn_im_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      isGreatest_injOn_im (Realization Hemisphere.signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.AURICOmega.DimensionRankRealization.isGreatest_injOn_im_unit
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

def exists_model_tfae_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@exists_model_tfae.{u}) (Realization Pairs.signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.AURICOmega.DimensionRankRealization.exists_model_tfae_unit
  realizationName := `Reg.D5.S3.Quantum.AURICOmega.DimensionRankRealization.Pairs.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨Pairs.arena.{u}⟩
  objectArena := .source ⟨Pairs.arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Pairs.arena.{u} ⟨Pairs.source_registration.{u}⟩
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
      path := #["body", "body", "arg", "arg", "arg", "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Quantum.AURICOmega.DimensionRankRealization
