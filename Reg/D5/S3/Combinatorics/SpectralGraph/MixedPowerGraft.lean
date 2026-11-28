import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.SpectralGraph.MixedPowerGraft

namespace Reg.D5.S3.Combinatorics.SpectralGraph.MixedPowerGraft

open _root_.D5.S3.Combinatorics.SpectralGraph.MixedPowerGraft
open _root_.D5.S3.Combinatorics.Graph.ZeroForcing.GridPowerZeroForcingRefutation (graphPower)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open SimpleGraph

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

universe u

abbrev signature : Signature where
  Params := Σ _ : Type u, ℕ
  State p := SimpleGraph p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := SimpleGraph p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p G => graphPower G p.2) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => ⊥) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  let V := ULift.{u} (Fin 2)
  let a : V := ⟨0⟩
  let b : V := ⟨1⟩
  have hne : a ≠ b := fun h => (by decide : (0 : Fin 2) ≠ 1) (congrArg ULift.down h)
  refine ⟨⟨V, 1⟩, ⊥, ⊤, ?_⟩
  intro he
  change graphPower (⊥ : SimpleGraph V) 1 = graphPower (⊤ : SimpleGraph V) 1 at he
  have hadj : (graphPower (⊤ : SimpleGraph V) 1).Adj a b :=
    (graphPower_adj_dist_iff _ connected_top _ _ _).mpr ⟨hne, (dist_eq_one_iff_adj.mpr hne).le⟩
  rw [← he] at hadj
  exact (edist_le_one_iff_adj_or_eq.mp hadj.2).elim (fun h => h) hne

namespace Adjacency

abbrev arena : Arena where
  signature := signature.{u}
  Law r := ∀ {V : Type u} (G : SimpleGraph V), G.Connected → ∀ (k : ℕ) (i j : V),
    (r.readout () ⟨V, k⟩ G).Adj i j ↔ i ≠ j ∧ G.dist i j ≤ k

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let a : ULift.{u} (Fin 2) := ⟨0⟩
  let b : ULift.{u} (Fin 2) := ⟨1⟩
  have hne : a ≠ b := fun he => (by decide : (0 : Fin 2) ≠ 1) (congrArg ULift.down he)
  exact (h ⊤ connected_top 1 a b).mpr ⟨hne, (dist_eq_one_iff_adj.mpr hne).le⟩

def sourceRegistration : Registration arena.{u} (type_of% @graphPower_adj_dist_iff.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨graphPower_adj_dist_iff, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@graphPower_adj_dist_iff.{u}) (Realization signature.{u}) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.SpectralGraph.MixedPowerGraft.Adjacency.unit
  realizationName := `Reg.D5.S3.Combinatorics.SpectralGraph.MixedPowerGraft.Adjacency.sourceRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨sourceRegistration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p G => graphPower G p.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.SpectralGraph.MixedPowerGraft
    definition := none
    coordinates := #[0, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Adjacency

namespace ConnectedPower

abbrev arena : Arena where
  signature := signature.{u}
  Law r := ∀ {V : Type u} (G : SimpleGraph V), G.Connected → ∀ {k : ℕ}, 1 ≤ k →
    (r.readout () ⟨V, k⟩ G).Connected

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let a : ULift.{u} (Fin 2) := ⟨0⟩
  let b : ULift.{u} (Fin 2) := ⟨1⟩
  have hne : a ≠ b := fun he => (by decide : (0 : Fin 2) ≠ 1) (congrArg ULift.down he)
  have hc : (⊥ : SimpleGraph (ULift.{u} (Fin 2))).Connected :=
    h ⊤ connected_top (k := 1) le_rfl
  exact hne (by simpa using hc a b)

def sourceRegistration : Registration arena.{u} (type_of% @graphPower_connected.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨graphPower_connected, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@graphPower_connected.{u}) (Realization signature.{u}) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.SpectralGraph.MixedPowerGraft.ConnectedPower.unit
  realizationName := `Reg.D5.S3.Combinatorics.SpectralGraph.MixedPowerGraft.ConnectedPower.sourceRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨sourceRegistration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p G => graphPower G p.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.SpectralGraph.MixedPowerGraft
    definition := none
    coordinates := #[0, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end ConnectedPower

end
end Reg.D5.S3.Combinatorics.SpectralGraph.MixedPowerGraft
