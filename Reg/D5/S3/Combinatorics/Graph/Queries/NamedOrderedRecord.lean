import D5.S3.Combinatorics.Graph.Queries.NamedOrderedRecord
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

open LeanInformationAudit
open _root_.D5.S0.Diagonal.Probability.EquivariantEscape (uniformPmf)
open _root_.D5.S3.Combinatorics.Graph.Queries.NamedOrderedRecord
open _root_.D5.S3.Combinatorics.Probability.NamingRestrictionLaw (namingMass)
open _root_.D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped ENNReal BigOperators

namespace Reg.D5.S3.Combinatorics.Graph.Queries.NamedOrderedRecord

noncomputable section
universe u

private abbrev signature : Signature where
  Params := Σ (N : Type u), DecidableEq N
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ≥0∞
  Anchor := Empty
  finiteAnchor := inferInstance

private def actual : Realization signature.{u} :=
  realize signature (fun _ _ size => namingMass size) (fun e => nomatch e)

private def zeroMass : Realization signature.{u} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {N : Type u} [Fintype N] [decN : DecidableEq N]
    (reply ref : N → Option (Set N)) (p : PassiveProtocol N (fun _ => Option (List N)))
    (refTable : OrderTable ref),
    let trace := runPassiveProtocol (fun q => readOrdered ref q) p refTable
    let seen := (trace.map Sigma.fst).toFinset
    let mass := R.readout () ⟨N, decN⟩ (∏ q ∈ seen, ((ref q).elim 0 Set.ncard).factorial)
    (uniformPmf (∀ q, LocalOrder (reply q))).toOuterMeasure
        {t | runPassiveProtocol (fun q => readOrdered reply q) p t = trace} =
      @ite ℝ≥0∞ (∀ q ∈ seen, reply q = ref q) (Classical.propDecidable _) mass 0

private theorem zeroMass_invalid : ¬ arena.{u}.Law zeroMass := by
  classical
  intro h
  let N := ULift.{u} Empty
  let reply : N → Option (Set N) := isEmptyElim
  let t : OrderTable reply := isEmptyElim
  have hResult := h reply reply .stop t
  simp only [runPassiveProtocol, Set.ofPred_true, zeroMass, realize, ite_self] at hResult
  rw [PMF.toOuterMeasure_apply, Set.indicator_univ, PMF.tsum_coe] at hResult
  exact one_ne_zero hResult

private theorem actual_varies {N : Type u} (decN : DecidableEq N) :
    actual.readout () ⟨N, decN⟩ 1 ≠ actual.readout () ⟨N, decN⟩ 2 := by
  change namingMass 1 ≠ namingMass 2
  simp only [namingMass, Nat.cast_one, Nat.cast_ofNat, inv_one]
  intro h
  have hInv := congrArg Inv.inv h
  norm_num at hInv

def evidence : Registration arena.{u} (type_of% (@orderedRecord_mass.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@orderedRecord_mass.{u}, zeroMass, zeroMass_invalid⟩
  sensitivity := ⟨fun i => ⟨zeroMass, fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl, zeroMass_invalid⟩, fun e => nomatch e⟩
  dependence := fun _ => ⟨⟨ULift.{u} Unit, inferInstance⟩, 1, 2, actual_varies _⟩

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@orderedRecord_mass.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.Queries.NamedOrderedRecord.orderedRecord_mass
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Queries.NamedOrderedRecord.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨evidence.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ size => namingMass size) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Queries.NamedOrderedRecord
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "value"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Combinatorics.Graph.Queries.NamedOrderedRecord
