import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Geometry.CompactWedgeFiniteFactor

noncomputable section
open Set Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Geometry.CompactWedgeFiniteFactor

namespace Reg.D5.S3.Geometry.CompactWedgeFiniteFactor

universe u v

structure Parameters where
  J : Type u
  Z : J → Type v
  topology : ∀ j, TopologicalSpace (Z j)
  b : ∀ j, Z j
  separated : ∀ j, @T1Space (Z j) (topology j)

attribute [instance] Parameters.topology Parameters.separated

abbrev signature : Signature where
  Params := Parameters.{u,v}
  State p := Set (FamilyWedge p.b)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Set p.J
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u,v} :=
  realize signature (fun _ p K => support p.b K) (fun e => nomatch e)

def rejected : Realization signature.{u,v} :=
  realize signature (fun _ _ _ => Set.univ) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u,v}
  Law R := ∀ p : Parameters.{u,v}, ∀ K : Set (FamilyWedge p.b),
    IsCompact K → (R.readout () p K).Finite

private theorem bridge : (type_of% (@compact_support.{u,v})) ↔ arena.{u,v}.Law actual := by
  constructor
  · intro h p K hK
    exact h p.b hK
  · intro h J Z topology b separated K hK
    exact h ⟨J, Z, topology, b, separated⟩ K hK

private abbrev infiniteParameters : Parameters.{u,v} :=
  ⟨ULift.{u} ℕ, fun _ => ULift.{v} Unit, fun _ => inferInstance,
    fun _ => ⟨()⟩, fun _ => inferInstance⟩

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  have hh := h infiniteParameters ∅ isCompact_empty
  exact Set.infinite_univ hh

private abbrev pointParameters : Parameters.{u,v} :=
  ⟨ULift.{u} Unit, fun _ => ULift.{v} Bool, fun _ => inferInstance,
    fun _ => ⟨false⟩, fun _ => inferInstance⟩

private theorem dependence : ObservationalDependence signature.{u,v} actual := by
  intro i
  let j : pointParameters.{u,v}.J := ⟨()⟩
  let y := point pointParameters.b j (⟨true⟩ : ULift.{v} Bool)
  refine ⟨pointParameters, ∅, {y}, ?_⟩
  intro h
  have hy : j ∈ support pointParameters.b {y} :=
    ⟨⟨true⟩, by intro hh; cases hh, rfl⟩
  have hn : j ∉ support pointParameters.b ∅ := by
    rintro ⟨_, _, hf⟩
    exact hf
  exact hn (h.symm ▸ hy)

def family : Registration arena.{u,v} (type_of% (@compact_support.{u,v})) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp (@compact_support.{u,v}), rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration
    (@compact_support.{u,v}) (Realization signature.{u,v}) Unit Unit where
  unitName := `Reg.D5.S3.Geometry.CompactWedgeFiniteFactor.__information_unit
  realizationName := `Reg.D5.S3.Geometry.CompactWedgeFiniteFactor.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p K => support p.b K) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.CompactWedgeFiniteFactor
    definition := none
    coordinates := #[0, 1, 2, 3, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg"],
      stateBinder := 5,
      functionOperand := false,
      stateOperand := none,
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration
end Reg.D5.S3.Geometry.CompactWedgeFiniteFactor
