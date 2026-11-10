import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Geometry.FiniteIndependentPathGreedy

/- UNCOMPILED source-only Nodup-observation registration candidate.
Native elaboration, kernel/axiom checks and source correspondence remain OPEN.
The semantic source occurrence is exactly vs.Nodup in the original explicit
hd binder domain of @survivors_paths.{u}; abstract its original vs operand,
with only the original V : Type u as parameter. Boolean predicate reification
must use the explicit Classical.propDecidable dictionary below. No compiled
selector evidence is supplied: sourceSelection stays none until the actual
compiled theorem supplies its coordinate and occurrence/operand selectors.
No raw binder ordinal or syntax path is guessed here. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Finset
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Geometry.FiniteCoordinateGreedyMatching
open _root_.D5.S3.Geometry.FiniteIndependentPathGreedy

namespace Reg.D5.S3.Geometry.FiniteIndependentPathGreedy
universe u

abbrev signature : Signature where
  Params := Type u
  State V := List V
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature
    (fun _ V vs => @Decidable.decide vs.Nodup (Classical.propDecidable vs.Nodup))
    (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => true) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {V : Type u} [fv : Fintype V] [dv : DecidableEq V] (vs : List V)
    (hd : R.readout () V vs = true),
    survivors (paths vs) vs = pathCritical vs

private theorem actual_true_iff {V : Type u} (vs : List V) :
    actual.readout () V vs = true ↔ vs.Nodup := by
  change @Decidable.decide vs.Nodup (Classical.propDecidable vs.Nodup) = true ↔ vs.Nodup
  cases Classical.propDecidable vs.Nodup with
  | isTrue hp => exact ⟨fun _ => hp, fun _ => rfl⟩
  | isFalse hn =>
    constructor
    · intro he
      cases he
    · intro hp
      exact (hn hp).elim

private theorem bridge : (type_of% (@survivors_paths.{u})) ↔ arena.{u}.Law actual := by
  constructor
  · intro h V fv dv vs hd
    exact @h V fv dv vs ((actual_true_iff vs).mp hd)
  · intro h V fv dv vs hd
    exact @h V fv dv vs ((actual_true_iff vs).mpr hd)

/- These calculations unfold the preserved paths and simultaneous-round
algorithm on two positions carrying the SAME label. No distinctness premise
is used for this counterfactual calculation. -/
private theorem paths_repeated {V : Type u} [Fintype V] [DecidableEq V] (v : V) :
    paths [v, v] = ({∅, {v}} : Finset (Finset V)) := by
  ext a
  simp [paths, or_assoc, or_left_comm, or_comm]

private theorem lowers_repeated {V : Type u} [Fintype V] [DecidableEq V] (v : V) :
    lowers (paths [v, v]) v = ({∅} : Finset (Finset V)) := by
  rw [paths_repeated]
  ext a
  rw [mem_lowers]
  constructor
  · rintro ⟨ha, hv, _⟩
    rcases Finset.mem_insert.mp ha with he | he
    · exact Finset.mem_singleton.mpr he
    · have he' : a = ({v} : Finset V) := Finset.mem_singleton.mp he
      subst a
      exact (hv (by simp)).elim
  · intro ha
    have he : a = (∅ : Finset V) := Finset.mem_singleton.mp ha
    subst a
    simp

private theorem roundPairs_repeated {V : Type u} [Fintype V] [DecidableEq V] (v : V) :
    roundPairs (paths [v, v]) v = ({(∅, v)} : Finset (Finset V × V)) := by
  rw [roundPairs, lowers_repeated]
  simp

private theorem pairedFaces_repeated {V : Type u} [Fintype V] [DecidableEq V] (v : V) :
    pairedFaces (paths [v, v]) v = ({∅, {v}} : Finset (Finset V)) := by
  simp only [pairedFaces, lowers_repeated]
  ext a
  simp

private theorem remaining_repeated {V : Type u} [Fintype V] [DecidableEq V] (v : V) :
    remaining (paths [v, v]) v = (∅ : Finset (Finset V)) := by
  unfold remaining
  rw [pairedFaces_repeated, paths_repeated]
  simp

private theorem lowers_empty {V : Type u} [Fintype V] [DecidableEq V] (v : V) :
    lowers (∅ : Finset (Finset V)) v = ∅ := by
  ext a
  simp

private theorem roundPairs_empty {V : Type u} [Fintype V] [DecidableEq V] (v : V) :
    roundPairs (∅ : Finset (Finset V)) v = ∅ := by
  rw [roundPairs, lowers_empty]
  simp

private theorem remaining_empty {V : Type u} [Fintype V] [DecidableEq V] (v : V) :
    remaining (∅ : Finset (Finset V)) v = ∅ := by
  ext a
  simp [remaining]

private theorem rounds_repeated {V : Type u} [Fintype V] [DecidableEq V] (v : V) :
    rounds (paths [v, v]) [v, v] =
      [({(∅, v)} : Finset (Finset V × V)), ∅] := by
  change [roundPairs (paths [v, v]) v,
    roundPairs (remaining (paths [v, v]) v) v] = _
  rw [roundPairs_repeated, remaining_repeated, roundPairs_empty]

private theorem remaining_second {V : Type u} [Fintype V] [DecidableEq V] (v : V) :
    remaining (remaining (paths [v, v]) v) v = (∅ : Finset (Finset V)) := by
  rw [remaining_repeated, remaining_empty]

private theorem survivors_repeated {V : Type u} [Fintype V] [DecidableEq V] (v : V) :
    survivors (paths [v, v]) [v, v] = (∅ : Finset (Finset V)) := by
  change remaining (remaining (paths [v, v]) v) v = ∅
  exact remaining_second v

private theorem pathCritical_repeated {V : Type u} [Fintype V] [DecidableEq V] (v : V) :
    pathCritical [v, v] = ({{v}} : Finset (Finset V)) := rfl

private theorem recurrence_repeated_fails {V : Type u} [Fintype V] [DecidableEq V] (v : V) :
    survivors (paths [v, v]) [v, v] ≠ pathCritical [v, v] := by
  rw [survivors_repeated, pathCritical_repeated]
  intro he
  have hm : ({v} : Finset V) ∈ (∅ : Finset (Finset V)) :=
    he.symm ▸ Finset.mem_singleton_self ({v} : Finset V)
  simpa using hm

private def testVertex : ULift.{u} Unit := ULift.up ()

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have he := @h (ULift.{u} Unit) inferInstance inferInstance [testVertex, testVertex] (by rfl)
  exact recurrence_repeated_fails testVertex he

private theorem actual_nil {V : Type u} :
    actual.readout () V [] = true :=
  (actual_true_iff []).mpr (by simp)

private theorem actual_repeated {V : Type u} (v : V) :
    actual.readout () V [v, v] = false := by
  have hn : ¬ ([v, v] : List V).Nodup := by simp
  cases he : actual.readout () V [v, v] with
  | false => rfl
  | true => exact (hn ((actual_true_iff [v, v]).mp he)).elim

private theorem actual_nonconstant :
    actual.{u}.readout () (ULift.{u} Unit) [] ≠
      actual.readout () (ULift.{u} Unit) [testVertex, testVertex] := by
  rw [actual_nil, actual_repeated]
  intro he
  cases he

private theorem source_law : arena.{u}.Law actual := bridge.mp (@survivors_paths.{u})

private theorem family_variation : Variation arena.{u} actual :=
  ⟨source_law, rejected, rejected_law⟩

private theorem family_sensitivity : Sensitivity arena.{u} actual :=
  ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩

private theorem family_dependence : ObservationalDependence signature.{u} actual := by
  intro i
  cases i
  exact ⟨ULift.{u} Unit, [], [testVertex, testVertex], actual_nonconstant⟩

def family : Registration arena.{u} (type_of% (@survivors_paths.{u})) where
  actual := actual
  bridge := bridge
  variation := family_variation
  sensitivity := family_sensitivity
  dependence := family_dependence

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@survivors_paths.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Geometry.FiniteIndependentPathGreedy.__information_unit
  realizationName := `Reg.D5.S3.Geometry.FiniteIndependentPathGreedy.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ V vs => @Decidable.decide vs.Nodup (Classical.propDecidable vs.Nodup))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Geometry.FiniteIndependentPathGreedy
