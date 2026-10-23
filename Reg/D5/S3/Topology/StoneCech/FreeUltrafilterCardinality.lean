import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Topology.StoneCech.FreeUltrafilterCardinality

/-!
Source-only candidate for the closed cardinal-supply theorem. The sole role
observes the actual underlying filter of each ultrafilter. The law retains
the entire infinite ultrafilter subtype and the original cardinal bound.
Elaboration, template binding and complete raw source reconstruction remain
unverified. The sourceSelection path, coordinates and stateBinder below are
unvalidated proposals, not accepted compiler evidence.
-/

namespace Reg.D5.S3.Topology.StoneCech.FreeUltrafilterCardinality

open Set Filter
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Topology.StoneCech.FreeUltrafilterCardinality

set_option autoImplicit false
set_option relaxedAutoImplicit false

abbrev signature : Signature.{0, 0, 0, 0, 0} where
  Params := Unit
  State := fun p => Ultrafilter ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun i p => Filter ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev actual : Realization signature :=
  realize signature (fun i p u => (u : Filter ℕ)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := 2 ^ Cardinal.continuum ≤
    Cardinal.mk {u : Ultrafilter ℕ // r.readout () () u ≤ Filter.cofinite}

abbrev sourceScope := type_of% (@continuum_power_le_mk_freeUltrafilter_nat)

theorem source_bridge : sourceScope ↔ arena.Law actual := Iff.rfl

theorem actual_positive : arena.Law actual :=
  continuum_power_le_mk_freeUltrafilter_nat

abbrev rejected : Realization signature :=
  realize signature (fun i p u => (pure (0 : ℕ) : Filter ℕ)) (fun e => nomatch e)

private theorem pure_zero_not_free :
    ¬ (pure (0 : ℕ) : Filter ℕ) ≤ Filter.cofinite := by
  intro h
  have hm : ({0} : Set ℕ)ᶜ ∈ (pure (0 : ℕ) : Filter ℕ) :=
    h (Set.finite_singleton 0).compl_mem_cofinite
  have hz : (0 : ℕ) ∈ ({0} : Set ℕ)ᶜ := Filter.mem_pure.mp hm
  exact hz (Set.mem_singleton 0)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  change 2 ^ Cardinal.continuum ≤
    Cardinal.mk {u : Ultrafilter ℕ // (pure (0 : ℕ) : Filter ℕ) ≤ Filter.cofinite} at h
  letI : IsEmpty {u : Ultrafilter ℕ // (pure (0 : ℕ) : Filter ℕ) ≤ Filter.cofinite} :=
    ⟨fun u => pure_zero_not_free u.property⟩
  rw [Cardinal.mk_eq_zero] at h
  have hpos : (0 : Cardinal) < 2 ^ Cardinal.continuum :=
    lt_of_le_of_lt (Cardinal.zero_le Cardinal.continuum) (Cardinal.cantor Cardinal.continuum)
  exact (not_le_of_gt hpos) h

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (pure (0 : ℕ) : Ultrafilter ℕ), (pure (1 : ℕ) : Ultrafilter ℕ), ?_⟩
  change ((pure (0 : ℕ) : Ultrafilter ℕ) : Filter ℕ) ≠
    ((pure (1 : ℕ) : Ultrafilter ℕ) : Filter ℕ)
  rw [Ultrafilter.coe_pure, Ultrafilter.coe_pure]
  exact fun h => Nat.zero_ne_one (Filter.pure_injective h)

def familyRegistration : Registration arena sourceScope where
  actual := actual
  bridge := source_bridge
  variation := ⟨actual_positive, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}
      (@continuum_power_le_mk_freeUltrafilter_nat)
      (Realization signature) Unit True where
  unitName := `D5.S3.Topology.StoneCech.FreeUltrafilterCardinality.continuum_power_le_mk_freeUltrafilter_nat.__information_unit
  realizationName := `Reg.D5.S3.Topology.StoneCech.FreeUltrafilterCardinality.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨True.intro⟩ True.intro
  readout := some (realize signature (fun i p u => (u : Filter ℕ)) (fun e => nomatch e))
  variation := .evidence ⟨True.intro⟩ True.intro
  sensitivity := .evidence ⟨True.intro⟩ True.intro
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Topology.StoneCech.FreeUltrafilterCardinality
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "arg", "arg", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Topology.StoneCech.FreeUltrafilterCardinality
