import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.MutualVisibility.Geodesics
import Reg.Support.DependentFamily

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Graph.MutualVisibility
universe u
namespace Reg.D5.S3.Combinatorics.Graph.MutualVisibility.Geodesics

abbrev visibilitySignature : Signature where
  Params := Sigma fun V : Type u => DecidableEq V
  State p := SimpleGraph p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Finset p.1 → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def visibilityActual : Realization visibilitySignature :=
  realize visibilitySignature (fun _ p H S => @Visible p.1 p.2 H S) (fun e => nomatch e)

abbrev inwardArena : Arena where
  signature := visibilitySignature
  Law r := ∀ a, letI := a.2; ∀ (H : SimpleGraph a.1), H.Connected →
    ∀ w u v y p, Dominates H w u v → H.Adj u y → H.Adj v y → H.Adj p u →
    H.dist p w + 1 = H.dist u w → r.readout () a H {u,v,y} →
    p ≠ v ∧ p ≠ y ∧ ∃ Q P : {S : Finset a.1 // r.readout () a H S},
      Q.val = {p,v,y} ∧ P.val = {p,y} ∧ MixedMove H {u,v,y} Q.val ∧
      MixedMove H Q.val P.val ∧ H.dist p w + H.dist y w < H.dist u w + H.dist v w

def inwardEvidence : Registration inwardArena (type_of% (@inward_replacement.{u})) where
  actual := visibilityActual
  bridge := by
    constructor
    · intro h a H hH w u v y p hdom huy hvy hpu hp hS
      exact @h a.1 a.2 H hH w u v y p hdom huy hvy hpu hp hS
    · intro h V inst H hH w u v y p hdom huy hvy hpu hp hS
      exact h ⟨V, inst⟩ H hH w u v y p hdom huy hvy hpu hp hS

noncomputable def inwardRegistration : Contract.Registration (@inward_replacement.{u})
    (type_of% visibilityActual) (type_of% (@Visible.{u})) Unit := {
  unitName := `D5.S3.Combinatorics.Graph.MutualVisibility.inward_replacement,
  realizationName := `Reg.D5.S3.Combinatorics.Graph.MutualVisibility.Geodesics.inwardEvidence,
  realizationSource := none, generated := false,
  arena := .source ⟨inwardArena⟩, objectArena := .source ⟨inwardArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source inwardArena ⟨inwardEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent, readout := some visibilityActual,
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := some (@Visible.{u}), sourceSelection := none,
  continuation := .unknown, familyRecord := none, options := #[] }

end Reg.D5.S3.Combinatorics.Graph.MutualVisibility.Geodesics
