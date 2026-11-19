import D5.S3.Quantum.Algebra.PBIdempotentSupport
import Reg.Support.DependentFamily

/-! Source reconstruction with the entire original response family as readout. -/

set_option autoImplicit false
noncomputable section
open scoped ComplexOrder
universe u v w

namespace Reg.D5.S3.Quantum.Algebra.PBIdempotentSupport
open _root_.D5.S3.Topology
open _root_.D5.S3.Quantum.Algebra
open _root_.D5.S3.Quantum.Algebra.PBOriginalReadoutRealization
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

structure Inputs where
  X : Type u
  E : Type v
  P : Type w
  [normedX : NormedAddCommGroup X]
  [spaceX : NormedSpace ℝ X]
  [complete : CompleteSpace X]
  [normedE : NormedAddCommGroup E]
  [spaceE : NormedSpace ℝ E]
  S : X →ₗ[ℝ] X →ₗ[ℝ] X
  unit : X
  J : E →ₗ[ℝ] E →ₗ[ℝ] E
  D : E → E → E
  C : Set E
  i : E →ₗᵢ[ℝ] X
  evaluation : P → E →ₗ[ℝ] ℝ

attribute [instance] Inputs.normedX Inputs.spaceX Inputs.complete Inputs.normedE Inputs.spaceE

abbrev signature : Signature where
  Params := Inputs.{u,v,w}
  State P := P.E × P.E
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ P := P.E
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u,v,w} :=
  realize signature (fun _ P ab => P.D ab.1 ab.2) (fun e => nomatch e)

abbrev sourceScope : Prop := type_of% (@PBIdempotentSupport.original_p2_support.{u,v,w})

abbrev arena : Arena where
  signature := signature.{u,v,w}
  Law r := ∀ (P : Inputs.{u,v,w}), let D := fun a b => r.readout () P (a,b)
    ∀ (_A : JBAlgebra.Data P.X P.S P.unit),
    (∀ a b, P.i (P.J a b) = P.S (P.i a) (P.i b)) →
    (∀ a, a ∈ P.C ↔ ∃ z : P.X, P.S z z = P.i a) →
    (∀ a, a ∈ P.C ↔ ∀ α, 0 ≤ P.evaluation α a) →
    (∀ α a b, (originalTable P.J D (P.evaluation α) a b).PosSemidef) →
    ∀ p, P.J p p = p → ∀ a b,
      P.S (P.i p) (P.i a) = P.i a → P.S (P.i p) (P.i b) = P.i b →
      ((‖a‖ * ‖b‖) • p + D a b ∈ P.C) ∧
      ((‖a‖ * ‖b‖) • p - D a b ∈ P.C) ∧
      D a b ∈ originalCorner P.i.toLinearMap P.S p

theorem source_bridge : sourceScope.{u,v,w} ↔ arena.{u,v,w}.Law actual.{u,v,w} := by
  constructor
  · intro h P
    dsimp only
    intro A
    exact h P.S P.unit A P.J P.D P.C P.i P.evaluation
  · intro h X E P normedX spaceX complete normedE spaceE S unit A J D C i evaluation
    exact h (@Inputs.mk X E P normedX spaceX complete normedE spaceE S unit J D C i evaluation) A

theorem every_readout (r : Realization signature.{u,v,w}) : arena.Law r := by
  intro P
  dsimp only
  intro A hj hc hd hP2 p hp a b ha hb
  exact PBIdempotentSupport.original_p2_support P.S P.unit A P.J
    (fun a b => r.readout () P (a,b)) P.C P.i P.evaluation hj hc hd hP2 p hp a b ha hb

theorem registration_obstruction :
    ¬ Nonempty (Registration arena.{u,v,w} sourceScope.{u,v,w}) := by
  rintro ⟨r⟩
  obtain ⟨bad, hbad⟩ := r.variation.2
  exact hbad (every_readout bad)

end Reg.D5.S3.Quantum.Algebra.PBIdempotentSupport
