import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Geometry.HereditaryLexicographicProduct

/-! Complete source-telescope reconstruction for the unsuspended hereditary
product conclusion. Its truth-valued readout is constant on valid inputs,
so this attempted dependent-family template cannot supply observational
dependence. No validated registration or source-binding certificate is asserted. -/

noncomputable section
open Set
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Geometry.FiniteGraphVertexSubstitution
open _root_.D5.S3.Geometry.FiniteSimplicialJoin
open _root_.D5.S3.Geometry.HereditaryLexicographicProduct

namespace Reg.D5.S3.Geometry.HereditaryLexicographicProduct
universe u v w
attribute [local instance] Classical.propDecidable

structure Parameters where
  V : Type u
  U : Type u
  finiteV : Fintype V
  decidableV : DecidableEq V
  finiteU : Fintype U
  decidableU : DecidableEq U
  G : SimpleGraph V
  H : SimpleGraph U
  orderG : 2 ≤ @Fintype.card V finiteV
  orderH : 2 ≤ @Fintype.card U finiteU
  sourceG : @sourceSW.{u, v} V finiteV decidableV G
  sourceH : @sourceSW.{u, w} U finiteU decidableU H

attribute [instance] Parameters.finiteV Parameters.decidableV
  Parameters.finiteU Parameters.decidableU

abbrev signature : Signature where
  Params := Parameters.{u, v, w}
  State p := Set (p.V × p.U)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u, v, w} :=
  realize signature (fun _ p T => sourceP.{u, 0, 0}
    (Space (independenceComplex ((lexicographicProduct p.G p.H).induce T)).toPreAbstractSimplicialComplex))
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u, v, w}
  Law R := ∀ p T, R.readout () p T

/-- The complete original telescope, including both source hypotheses and every target subset. -/
theorem sourceBridge :
    (type_of% (@_root_.D5.S3.Geometry.HereditaryLexicographicProduct.result.{u, v, w})) ↔
      arena.{u, v, w}.Law actual := by
  constructor
  · intro h p T
    exact h p.G p.H p.orderG p.orderH p.sourceG p.sourceH T
  · intro h V U fv dv fu du G H og oh sg sh T
    exact h ⟨V, U, fv, dv, fu, du, G, H, og, oh, sg, sh⟩ T

/-- All truthful outputs are the same proposition; arbitrary distinct target subsets remain in scope. -/
theorem truthReadout_constant (p : Parameters.{u, v, w}) (S T : Set (p.V × p.U)) :
    actual.readout () p S = actual.readout () p T := by
  apply propext
  constructor
  · intro _
    exact _root_.D5.S3.Geometry.HereditaryLexicographicProduct.result
      p.G p.H p.orderG p.orderH p.sourceG p.sourceH T
  · intro _
    exact _root_.D5.S3.Geometry.HereditaryLexicographicProduct.result
      p.G p.H p.orderG p.orderH p.sourceG p.sourceH S

/-- This specific truth-only template cannot complete the required dependence slot. -/
theorem truthReadout_noDependence : ¬ ObservationalDependence signature.{u, v, w} actual := by
  intro h
  obtain ⟨p, S, T, hne⟩ := h ()
  exact hne (truthReadout_constant p S T)

/-- A four-slot dependent-family registration with this actual readout is impossible. -/
theorem truthReadout_noRegistration : ¬ ∃ R : Registration arena.{u, v, w}
    (type_of% (@_root_.D5.S3.Geometry.HereditaryLexicographicProduct.result.{u, v, w})),
    R.actual = actual := by
  rintro ⟨R, hr⟩
  have hd := R.dependence
  rw [hr] at hd
  exact truthReadout_noDependence hd

#print axioms sourceBridge
#print axioms truthReadout_noRegistration
end Reg.D5.S3.Geometry.HereditaryLexicographicProduct
