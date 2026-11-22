import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.UniverseSingleReadout
import D5.S3.Combinatorics.Matroids.JointCircuitRestrictionImage

/-! The family of simultaneous signed aggregate restrictions as a single observation. -/

namespace Reg.D5.S3.Combinatorics.Matroids.JointCircuitRestrictionImage

open LeanInformationAudit
open _root_.D5.S3.Combinatorics.Matroids.OrderedCycleFactorization
open _root_.D5.S3.Combinatorics.Matroids.JointCircuitRestrictionImage
open _root_.D5.S3.Combinatorics.Matroids.IntegralCircuitImage (aggregateRestrict)
open _root_.D5.S3.Combinatorics.Matroids.CircuitCycleDecomposition (restrictChain restrictionSign)
open _root_.D5.S3.HomologicalAlgebra.OrderedFaceSign (insertionSign)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.Support.UniverseSingleReadout (signature sensitivity)
open Finset Matroid
open scoped Matroid

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
universe u

abbrev Params := Σ V : Type u, Σ _ : LinearOrder V, Σ _ : Matroid V, Finset V
abbrev sig := signature Params.{u} (fun p => Chain p.1) (fun p => Set p.1 → Chain p.1)

def actual : Realization sig.{u} :=
  realize sig (fun _ ⟨V, ord, M, E⟩ z => @jointRestrict V ord M E z) (fun e => nomatch e)

def rejected : Realization sig.{u} :=
  realize sig (fun _ _ _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := sig.{u}
  Law r := ∀ {V : Type u} [ord : LinearOrder V] [Fintype V]
      (M : Matroid V) (E : Finset V) (_ : M.E = (E : Set V)) (_ : M✶.eRank = 2)
      (_ : ∀ a ∈ E, M✶.IsNonloop a) (y : Set V → ℤ),
      (∃ z : Chain V, TopCycle M z ∧ ∀ P ∈ dualClasses M E,
        r.readout () ⟨V, ord, M, E⟩ z P =
          y P • contractionGenerator (E \ classVertices M E P) (classVertices M E P)) ↔
        (∑ P ∈ dualClasses M E, ((classVertices M E P).card : ℤ) * y P) = 0 ∧
          ∀ P ∈ dualClasses M E, ∀ Q ∈ dualClasses M E, (E.card : ℤ) ∣ y P - y Q

private abbrev Sample := ULift.{u} Bool
private def a : Sample.{u} := ULift.up false
private def b : Sample.{u} := ULift.up true
private def sample : Matroid Sample.{u} := loopyOn Set.univ
private def ground : Finset Sample.{u} := univ

private lemma sample_rank : sample.{u}✶.eRank = 2 := by
  have hB : sample.{u}✶.IsBase Set.univ := by simp [sample]
  rw [← hB.encard_eq_eRank]
  simp [Set.encard_univ, Fintype.card_ulift, Fintype.card_bool]

private lemma class_label : ({b} : Set Sample.{u}) ∈ dualClasses sample ground := by
  classical
  apply mem_image.mpr
  exact ⟨b, mem_univ _, by simp [sample]⟩

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hground : sample.{u}.E = (ground : Set Sample.{u}) := by simp [sample, ground]
  have hn : ∀ a ∈ ground, sample.{u}✶.IsNonloop a := by
    simp [sample, freeOn_isNonloop_iff]
  obtain ⟨_, _, hread⟩ :=
    (h sample ground hground sample_rank hn (fun _ => 0)).2 (by simp)
  have hzero := congrFun (hread {b} class_label) (∅ : Finset Sample.{u})
  exact Int.one_ne_zero (by simpa only [rejected, realize, zero_smul, Pi.zero_apply] using hzero)

private lemma sample_complement : ground.{u} \ classVertices sample ground {b} = {a} := by
  classical
  have hclass : classVertices sample ground ({b} : Set Sample.{u}) = {b} := by
    ext x
    simp [classVertices, sample, ground]
  rw [hclass]
  ext x
  rcases x with ⟨x⟩
  cases x <;> simp [a, b, ground]

private lemma sample_readout :
    jointRestrict sample.{u} ground (simplex ∅) {b} ∅ = 1 := by
  classical
  have hc : sample.{u}.IsCircuit (↑({a} : Finset Sample.{u}) : Set Sample.{u}) := by
    simp [sample, singleton_isCircuit, loopyOn_isLoop_iff]
  have hbase : (sample.{u} ／ (↑({a} : Finset Sample.{u}) : Set Sample.{u})).IsBase
      (↑(∅ : Finset Sample.{u}) : Set Sample.{u}) := by
    apply (contract_base_iff (circuit_erase_basis hc (mem_singleton_self a)) (by simp)).2
    simp [sample]
  unfold jointRestrict
  calc
    _ = aggregateRestrict sample {a} (simplex ∅) ∅ := by
      apply congrArg (fun K => aggregateRestrict sample K (simplex ∅) ∅)
      convert sample_complement.{u} using 1
      ext x
      simp only [mem_sdiff]
    _ = _ := by
      have hbase' : (sample.{u} ／ ({a} : Set Sample.{u})).IsBase ∅ := by simpa using hbase
      simp [aggregateRestrict, restrictChain, hbase', restrictionSign, simplex,
        shuffleSign, insertionSign]

private theorem dependence : ObservationalDependence sig.{u} actual := by
  intro i
  refine ⟨⟨Sample.{u}, inferInstance, sample, ground⟩, simplex ∅, 0, ?_⟩
  intro h
  have he := congrFun (congrFun h {b}) (∅ : Finset Sample.{u})
  change jointRestrict sample ground (simplex ∅) {b} ∅ =
    jointRestrict sample ground 0 {b} ∅ at he
  rw [sample_readout] at he
  simp [jointRestrict, aggregateRestrict, restrictChain] at he

def source_registration : Registration arena.{u}
    (type_of% @exists_topCycle_joint_aggregateRestrict_iff.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_topCycle_joint_aggregateRestrict_iff.{u}, rejected, rejected_law⟩
  sensitivity := sensitivity _ actual rejected rejected_law
  dependence := dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, _, 0, 0}
      (@exists_topCycle_joint_aggregateRestrict_iff.{u}) (Realization sig.{u}) Type Unit where
  unitName := .str ``exists_topCycle_joint_aggregateRestrict_iff "__information_unit"
  realizationName := ``source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize sig actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Matroids.JointCircuitRestrictionImage
    definition := none
    coordinates := #[0, 3, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "arg", "body", "arg", "body", "body", "fn", "arg", "fn"]
      stateBinder := 9
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Combinatorics.Matroids.JointCircuitRestrictionImage
