import Reg.Support.DependentFamily
import D5.S3.Combinatorics.Graph.Rainbow.TwoEdgeChoices

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Combinatorics.Graph.Rainbow.TwoEdgeChoices

open _root_.D5.S3.Combinatorics.Graph.Rainbow.TwoEdgeChoices
open _root_.D5.S3.ConceptDynamics.InformationEscape
open scoped BigOperators

universe u v

/-- The complete universe-polymorphic source telescope is retained for this attempt. -/
abbrev massScope := type_of% (@repeated_colour_mass_le_outdegree.{u,v})
abbrev classesScope := type_of% (@exists_three_disjoint_classes.{u,v})
abbrev coreScope := type_of% (@deterministic_rainbow_choice_core.{u,v})

/-- All vertex and colour carriers and the finite vertex dictionary remain parameters. -/
def massSignature : DependentFamily.Signature where
  Params := Σ V : Type u, Σ C : Type v, Fintype V
  State p := Digraph p.1 × (p.1 → p.1 → p.2.1) × p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def massActual : DependentFamily.Realization massSignature.{u,v} :=
  DependentFamily.realize massSignature
    (fun _ p s => by
      letI : Fintype p.1 := p.2.2
      exact ∑ w : p.1, (repeated s.1 s.2.1 s.2.2 w).card)
    (fun e => nomatch e)

/-- The observed total mass is substituted into the entire original theorem statement. -/
def massArena : DependentFamily.Arena where
  signature := massSignature.{u,v}
  Law R := ∀ {V : Type u} {C : Type v} [f : Fintype V]
    (G : Digraph V) (c : V → V → C), OutProper G c → ∀ u : V,
      R.readout () ⟨V, C, f⟩ (G, c, u) ≤ (outNeighbors G u).card

theorem mass_source_bridge : massScope.{u,v} ↔ massArena.Law massActual := Iff.rfl

/-- Explicitly unresolved: no family registration is claimed until intervention,
sensitivity, observational-dependence and source-selection evidence are supplied. -/
def massCertificate : Option (DependentFamily.Registration massArena.{u,v} massScope.{u,v}) := none

/-- These full source scopes are checked now; their faithful family witnesses remain open. -/
def classesCertificate : Option classesScope.{u,v} := none
def coreCertificate : Option coreScope.{u,v} := none

#print axioms mass_source_bridge

end Reg.D5.S3.Combinatorics.Graph.Rainbow.TwoEdgeChoices
