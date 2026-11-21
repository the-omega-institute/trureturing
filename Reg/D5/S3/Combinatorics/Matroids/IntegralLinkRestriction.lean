import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.UniverseSingleReadout
import D5.S3.Combinatorics.Matroids.IntegralLinkRestriction
import Mathlib.Combinatorics.Matroid.Constructions
import Mathlib.Combinatorics.Matroid.Map

namespace Reg.D5.S3.Combinatorics.Matroids.IntegralLinkRestriction

open LeanInformationAudit
open _root_.D5.S3.Combinatorics.Matroids.OrderedCycleFactorization
open _root_.D5.S3.Combinatorics.Matroids.IntegralLinkRestriction
open _root_.D5.S3.Combinatorics.Matroids.CircuitCycleDecomposition (topCycles)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.Support.UniverseSingleReadout (signature sensitivity)
open Finset Matroid
open scoped Matroid

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
universe u

abbrev Params := Σ V : Type u, Σ _ : LinearOrder V, Finset V
abbrev sig := signature Params.{u} (fun p => Chain p.1) (fun p => Chain p.1)

def actual : Realization sig.{u} :=
  realize sig (fun _ ⟨V, ord, A⟩ z => @linkRestrict V ord A z) (fun e => nomatch e)

def rejected : Realization sig.{u} :=
  realize sig (fun _ _ _ => 0) (fun e => nomatch e)

abbrev faceArena : Arena where
  signature := sig.{u}
  Law r := ∀ {V : Type u} [ord : LinearOrder V] [_fin : Fintype V]
      {M : Matroid V} {A : Finset V} (_ : M.Indep (A : Set V)) (w : Chain V),
    (∃ z : Chain V, TopCycle M z ∧ r.readout () ⟨V, ord, A⟩ z = w) ↔
      TopCycle (M ／ (A : Set V)) w ∧ ((∃ x ∈ A, M.IsColoop x) → w = 0)

abbrev singletonArena : Arena where
  signature := sig.{u}
  Law r := ∀ {V : Type u} [ord : LinearOrder V] [_fin : Fintype V]
      {M : Matroid V} {x : V} (_ : M.IsNonloop x) (_ : ¬ M.IsColoop x)
      {w : Chain V} (_ : TopCycle (M ／ ({x} : Set V)) w),
    ∃ z : Chain V, TopCycle M z ∧ r.readout () ⟨V, ord, {x}⟩ z = w

private abbrev Sample := ULift.{u} Bool
private def a : Sample.{u} := ULift.up false
private def b : Sample.{u} := ULift.up true
private theorem a_ne_b : a.{u} ≠ b.{u} := by decide
private def sample : Matroid Sample.{u} :=
  (freeOn (Set.univ : Set Unit)).comap (fun _ => ())

private lemma sample_base (x : Sample.{u}) : sample.{u}.IsBase {x} := by
  rw [sample, Matroid.comap_isBase_iff]
  simp only [Set.image_singleton, freeOn_ground, Set.preimage_univ, Set.subset_univ, and_true]
  refine ⟨?_, Set.injOn_singleton _ _⟩
  rw [show (fun _ : Sample.{u} => ()) '' Set.univ = ({()} : Set Unit) by
    simp]
  exact (freeOn_indep (by simp)).isBasis_self

private lemma sample_nonloop : sample.{u}.IsNonloop a :=
  (sample_base a).indep.isNonloop_of_mem (Set.mem_singleton _)

private lemma sample_noncoloop : ¬ sample.{u}.IsColoop a := by
  intro h
  exact a_ne_b (Set.mem_singleton_iff.mp (h.mem_of_isBase (sample_base b)))

private def samplePair : Finset Sample.{u} := {a, b}

private lemma boundary_topCycle : TopCycle sample.{u} (simplexBoundary samplePair) := by
  refine ⟨fun F hF => ?_, fun R => ?_⟩
  · by_contra hne
    obtain ⟨x, hx, rfl⟩ := simplexBoundary_support.mp hne
    rcases (show x = a ∨ x = b from by simpa [samplePair] using hx) with rfl | rfl
    · exact hF (by simpa [samplePair, a_ne_b] using sample_base b)
    · exact hF (by simpa [samplePair, a_ne_b] using sample_base a)
  · have hu : samplePair = (univ : Finset Sample.{u}) := by
      ext x
      rcases x with ⟨x⟩
      cases x <;> simp [samplePair, a, b]
    rw [← hu, simplexBoundary, boundaryOn_squared]

private lemma link_sample :
    linkRestrict ({a} : Finset Sample.{u}) (simplexBoundary samplePair) ∅ ≠ 0 := by
  simp only [linkRestrict, Finset.disjoint_empty_left, ite_true, Finset.empty_union]
  apply mul_ne_zero (pow_ne_zero _ (by decide))
  apply simplexBoundary_support.mpr
  refine ⟨b, by simp [samplePair], ?_⟩
  ext x
  simp [samplePair, and_or_left]
  exact fun h => h.symm ▸ a_ne_b

private theorem face_rejected : ¬ faceArena.{u}.Law rejected := by
  intro h
  let w := linkRestrict ({a} : Finset Sample.{u}) (simplexBoundary samplePair)
  have hA : sample.{u}.Indep (↑({a} : Finset Sample.{u}) : Set Sample.{u}) := by
    simpa using sample_nonloop.indep
  have hw := (exists_topCycle_linkRestrict_iff_coloop hA w).1 ⟨_, boundary_topCycle, rfl⟩
  obtain ⟨_, _, hz⟩ := (h hA w).2 hw
  have he : 0 = w := hz
  exact link_sample (congrFun he.symm ∅)

private theorem singleton_rejected : ¬ singletonArena.{u}.Law rejected := by
  intro h
  let w := linkRestrict ({a} : Finset Sample.{u}) (simplexBoundary samplePair)
  have hA : sample.{u}.Indep (↑({a} : Finset Sample.{u}) : Set Sample.{u}) := by
    simpa using sample_nonloop.indep
  have hw := (exists_topCycle_linkRestrict_iff_coloop hA w).1 ⟨_, boundary_topCycle, rfl⟩
  obtain ⟨_, _, hz⟩ := h sample_nonloop sample_noncoloop (by simpa using hw.1)
  have he : 0 = w := hz
  exact link_sample (congrFun he.symm ∅)

private theorem dependence : ObservationalDependence sig.{u} actual := by
  intro i
  refine ⟨⟨Sample.{u}, inferInstance, {a}⟩, simplexBoundary samplePair, 0, ?_⟩
  intro h
  have he := congrFun h ∅
  change linkRestrict {a} (simplexBoundary samplePair) ∅ = linkRestrict {a} 0 ∅ at he
  apply link_sample
  simpa [linkRestrict] using he

def faceSource : Registration faceArena.{u}
    (type_of% @exists_topCycle_linkRestrict_iff_coloop.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_topCycle_linkRestrict_iff_coloop.{u}, rejected, face_rejected⟩
  sensitivity := sensitivity _ actual rejected face_rejected
  dependence := dependence

def singletonSource : Registration singletonArena.{u}
    (type_of% @exists_topCycle_linkRestrict_singleton.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_topCycle_linkRestrict_singleton.{u}, rejected, singleton_rejected⟩
  sensitivity := sensitivity _ actual rejected singleton_rejected
  dependence := dependence

def faceRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, _, 0, 0}
      (@exists_topCycle_linkRestrict_iff_coloop.{u}) (Realization sig.{u}) Type Unit where
  unitName := .str
    `D5.S3.Combinatorics.Matroids.IntegralLinkRestriction.exists_topCycle_linkRestrict_iff_coloop
    "__information_unit"
  realizationName := `Reg.D5.S3.Combinatorics.Matroids.IntegralLinkRestriction.faceSource
  realizationSource := none
  generated := false
  arena := .source ⟨faceArena⟩
  objectArena := .source ⟨faceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source faceArena ⟨faceSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize sig actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

def singletonRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, _, 0, 0}
      (@exists_topCycle_linkRestrict_singleton.{u}) (Realization sig.{u}) Type Unit where
  unitName := .str
    `D5.S3.Combinatorics.Matroids.IntegralLinkRestriction.exists_topCycle_linkRestrict_singleton
    "__information_unit"
  realizationName := `Reg.D5.S3.Combinatorics.Matroids.IntegralLinkRestriction.singletonSource
  realizationSource := none
  generated := false
  arena := .source ⟨singletonArena⟩
  objectArena := .source ⟨singletonArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source singletonArena ⟨singletonSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize sig actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev stateSig := signature (Type u) Chain Chain

def stateActual : Realization stateSig.{u} :=
  realize stateSig (fun _ _ z => z) (fun e => nomatch e)

def stateRejected : Realization stateSig.{u} :=
  realize stateSig (fun _ _ _ _ => 1) (fun e => nomatch e)

abbrev coloopArena : Arena where
  signature := stateSig.{u}
  Law r := ∀ {V : Type u} [_ord : LinearOrder V] [_fin : Fintype V]
    {M : Matroid V} {x : V} (_ : M.IsColoop x) {z : Chain V} (_ : TopCycle M z),
      r.readout () V z = 0

private theorem coloop_rejected : ¬ coloopArena.{u}.Law stateRejected := by
  intro h
  let M := freeOn ({a} : Set Sample.{u})
  have ha : M.IsColoop a := Matroid.isColoop_iff_forall_mem_isBase.2 (by
    intro B hB
    rw [Matroid.freeOn_isBase_iff.1 hB]
    exact Set.mem_singleton a)
  have hz := h ha ((topCycles M).zero_mem)
  have hzero := congrFun hz ∅
  exact one_ne_zero hzero

def coloopSource : Registration coloopArena.{u}
    (type_of% @topCycle_eq_zero_of_isColoop.{u}) where
  actual := stateActual
  bridge := Iff.rfl
  variation := ⟨@topCycle_eq_zero_of_isColoop.{u}, stateRejected, coloop_rejected⟩
  sensitivity := sensitivity _ stateActual stateRejected coloop_rejected
  dependence := by
    intro i
    refine ⟨Sample.{u}, 0, fun _ => 1, ?_⟩
    intro h
    exact zero_ne_one (congrFun h ∅)

def coloopRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, _, 0, 0}
      (@topCycle_eq_zero_of_isColoop.{u}) (Realization stateSig.{u}) Type Unit where
  unitName := .str
    `D5.S3.Combinatorics.Matroids.IntegralLinkRestriction.topCycle_eq_zero_of_isColoop
    "__information_unit"
  realizationName := `Reg.D5.S3.Combinatorics.Matroids.IntegralLinkRestriction.coloopSource
  realizationSource := none
  generated := false
  arena := .source ⟨coloopArena⟩
  objectArena := .source ⟨coloopArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source coloopArena ⟨coloopSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize stateSig stateActual.readout stateActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Combinatorics.Matroids.IntegralLinkRestriction
