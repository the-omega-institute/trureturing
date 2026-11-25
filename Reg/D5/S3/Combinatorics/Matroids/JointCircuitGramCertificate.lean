import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.UniverseSingleReadout
import D5.S3.Combinatorics.Matroids.JointCircuitGramCertificate
import Mathlib.Combinatorics.Matroid.Constructions

/-! The integral aggregate readout in the adjoint identity of the joint Gram certificate. -/

namespace Reg.D5.S3.Combinatorics.Matroids.JointCircuitGramCertificate

open LeanInformationAudit
open _root_.D5.S3.Combinatorics.Matroids.OrderedCycleFactorization
open _root_.D5.S3.Combinatorics.Matroids.CircuitCycleDecomposition
  (topCycles restrictChain restrictionSign)
open _root_.D5.S3.Combinatorics.Matroids.IntegralCircuitImage (aggregateRestrict)
open _root_.D5.S3.Combinatorics.Matroids.JointCircuitGramCertificate
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.Support.UniverseSingleReadout (signature sensitivity)
open Finset Matroid Matrix
open scoped Matroid

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
universe u

abbrev Params := Σ V : Type u, Σ fin : Fintype V, Σ ord : LinearOrder V,
  Σ M : Matroid V, Σ _ : Circuit M, @topCycles V fin ord M

abbrev sig := signature Params.{u}
  (fun ⟨V, fin, ord, M, K, _⟩ => @topCycles V fin ord (M ／ (K.val : Set V))) (fun _ => ℤ)

def actual : Realization sig.{u} :=
  realize sig (fun _ ⟨V, _, ord, M, K, z⟩ w =>
    dotProduct (@aggregateRestrict V ord M K.val z.val) w.val) (fun e => nomatch e)

def rejected : Realization sig.{u} :=
  realize sig (fun _ _ _ => 0) (fun e => nomatch e)

open Classical in
abbrev arena : Arena where
  signature := sig.{u}
  Law r := ∀ {V : Type u} [fin : Fintype V] [ord : LinearOrder V] (M : Matroid V)
      (e : V) (_ : e ∈ M.E),
    (∀ (K : Circuit M) (z : topCycles M) (w : topCycles (M ／ (K.val : Set V))),
      r.readout () ⟨V, fin, ord, M, K, z⟩ w =
        dotProduct z.val (signedJoin K.val (simplexBoundary K.val) w.val)) ∧
    (gram M).det ≠ 0 ∧ (IsEmpty (Passive M) → (gram M).det = 1) ∧
    ∀ y : (K : Circuit M) → topCycles (M ／ (K.val : Set V)),
      (∃! z : topCycles M, ∀ K : Circuit M, aggregateRestrict M K.val z.val = (y K).val) ↔
      (∀ (K : Circuit M) (T : Passive (M ／ (K.val : Set V))),
        dotProduct (y K).val (normalizedCycle T).val =
          ∑ B : Passive M, pivotPairing e y B *
            signedJoin K.val (simplexBoundary K.val) (normalizedCycle T).val B.val) ∧
      ∀ B : Passive M, (gram M).det ∣ ((gram M).adjugate.mulVec (pivotPairing e y)) B

private abbrev Sample := ULift.{u} Bool
private def vertex : Sample.{u} := ULift.up false
private def sample : Matroid Sample.{u} := loopyOn Set.univ

private def circuit : Circuit sample.{u} :=
  ⟨{vertex}, by simp [sample, singleton_isCircuit, loopyOn_isLoop_iff]⟩

private lemma empty_isBase : sample.{u}.IsBase (∅ : Set Sample.{u}) := by
  simp [sample]

private lemma contracted_empty_isBase :
    (sample.{u} ／ (circuit.val : Set Sample.{u})).IsBase (∅ : Set Sample.{u}) := by
  have h := (contract_base_iff (circuit_erase_basis circuit.prop
    (show vertex ∈ circuit.val from mem_singleton_self vertex))
    (disjoint_empty_left circuit.val)).2
  simpa only [coe_empty] using h (by simpa [circuit] using empty_isBase)

private def emptyCycle {N : Matroid Sample.{u}} (h : N.IsBase (∅ : Set Sample.{u})) :
    topCycles N :=
  let hB : PassiveBase N ∅ := ⟨by simpa using h, by simp⟩
  let hf := normalized_factorization N ∅ hB
  let hn := hf.1.exists.choose_spec
  ⟨simplex ∅, hf.2.1 _ hn rfl ▸ hn.toTopCycle⟩

private lemma sample_pairing :
    dotProduct (aggregateRestrict sample.{u} circuit.val (emptyCycle empty_isBase).val)
      (emptyCycle contracted_empty_isBase).val = 1 := by
  classical
  rw [dotProduct, ← sum_subset (show ({∅} : Finset (Finset Sample.{u})) ⊆ univ from subset_univ _)]
  · have hb : (sample.{u} ／ ({vertex} : Set Sample.{u})).IsBase ∅ := by
      simpa [circuit] using contracted_empty_isBase
    simp [aggregateRestrict, circuit, emptyCycle, simplex, restrictChain,
      restrictionSign, shuffleSign, hb,
      _root_.D5.S3.HomologicalAlgebra.OrderedFaceSign.insertionSign]
  · intro T _ hT
    have hn : T ≠ ∅ := fun h => hT (mem_singleton.mpr h)
    simp [emptyCycle, simplex, hn]

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have he : vertex ∈ sample.{u}.E := by simp [sample]
  have ha := (joint_circuit_gram_certificate sample.{u} vertex he).1
    circuit (emptyCycle empty_isBase) (emptyCycle contracted_empty_isBase)
  have hr := (h sample.{u} vertex he).1
    circuit (emptyCycle empty_isBase) (emptyCycle contracted_empty_isBase)
  have hz : (0 : ℤ) = _ := hr
  exact zero_ne_one (hz.trans (ha.symm.trans sample_pairing))

private theorem dependence : ObservationalDependence sig.{u} actual := by
  intro i
  refine ⟨⟨Sample.{u}, inferInstance, inferInstance, sample, circuit, emptyCycle empty_isBase⟩,
    emptyCycle contracted_empty_isBase, 0, ?_⟩
  change dotProduct (aggregateRestrict sample circuit.val (emptyCycle empty_isBase).val)
    (emptyCycle contracted_empty_isBase).val ≠
    dotProduct (aggregateRestrict sample circuit.val (emptyCycle empty_isBase).val) 0
  rw [sample_pairing, dotProduct_zero]
  exact one_ne_zero

def source_registration :
    Registration arena.{u} (type_of% @joint_circuit_gram_certificate.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@joint_circuit_gram_certificate.{u}, rejected, rejected_law⟩
  sensitivity := sensitivity _ actual rejected rejected_law
  dependence := dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, _, 0, 0}
      (@joint_circuit_gram_certificate.{u}) (Realization sig.{u}) Type Unit where
  unitName := .str
    `D5.S3.Combinatorics.Matroids.JointCircuitGramCertificate.joint_circuit_gram_certificate
    "__information_unit"
  realizationName :=
    `Reg.D5.S3.Combinatorics.Matroids.JointCircuitGramCertificate.source_registration
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
    owner := `D5.S3.Combinatorics.Matroids.JointCircuitGramCertificate
    definition := none
    coordinates := #[0, 3, 6, 7]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg",
        "body", "body", "body", "fn", "arg"]
      stateBinder := 8
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Combinatorics.Matroids.JointCircuitGramCertificate
