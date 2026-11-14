import D5.S3.Quantum.Foundation.BinaryCenterGeometry
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! The same-effect conclusion observes the complete original proper-effect
predicate. Source reconstruction and conditional erasure are separate from
whole-family variation, sensitivity and actual observational dependence. -/

noncomputable section
universe v

namespace Reg.D5.S3.Quantum.Foundation.BinaryCenterGeometry

open _root_.D5.S3.Quantum.Foundation.CircuitBalancedConfirmation
open _root_.D5.S3.Quantum.Foundation.FacetZeroGluing
open _root_.D5.S3.Quantum.Foundation.ExclusionBallFaces
open _root_.D5.S3.Quantum.Foundation.BinaryCenterGeometry
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

structure Inputs where
  V : Type v
  [add : NormedAddCommGroup V]
  [space : NormedSpace ℝ V]
  [finite : FiniteDimensional ℝ V]
  cone : PointedCone ℝ V
  unit : V →ₗ[ℝ] ℝ

attribute [instance] Inputs.add Inputs.space Inputs.finite

abbrev signature : Signature where
  Params := Inputs.{v}
  State P := P.V →ₗ[ℝ] ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{v} :=
  realize signature (fun _ P e => proper P.cone P.unit e) (fun a => nomatch a)

abbrev arena : Arena where
  signature := signature.{v}
  Law O := ∀ P : Inputs.{v},
    let C := P.cone
    let u := P.unit
    IsClosed (C : Set P.V) →
    (∀ x ∈ C, x ≠ 0 → 0 < u x) →
    Submodule.span ℝ (C : Set P.V) = ⊤ → exclusionBalls C u →
    ∀ p s q : pure C u, p ≠ s → exclusion C u s = exclusion C u p →
    (q : P.V) ∈ exclusion C u p →
    ∃ e : P.V →ₗ[ℝ] ℝ, O.readout () P e ∧
      {x | x ∈ base C u ∧ e x = 0} = exclusion C u p ∧
      {x | x ∈ base C u ∧ e x = 1} = exclusion C u q

abbrev sourceScope : Prop := type_of% (@repeated_pair_separating_effect.{v})

theorem source_bridge : sourceScope.{v} ↔ arena.{v}.Law actual.{v} := by
  constructor
  · intro h P
    exact @h P.V P.add P.space P.finite P.cone P.unit
  · intro h V add space finite C u
    exact h (@Inputs.mk V add space finite C u)

theorem actual_positive : arena.{v}.Law actual.{v} :=
  source_bridge.mp (@repeated_pair_separating_effect.{v})

def erased : Realization signature.{v} :=
  realize signature (fun _ _ _ => False) (fun a => nomatch a)

/-- Removing all proper-effect readouts destroys the same-effect conclusion
at every actual repeated input. This does not assert existence of such an input. -/
theorem erased_negative_of_input (P : Inputs.{v})
    (hc : IsClosed (P.cone : Set P.V))
    (hs : ∀ x ∈ P.cone, x ≠ 0 → 0 < P.unit x)
    (hg : Submodule.span ℝ (P.cone : Set P.V) = ⊤)
    (hB : exclusionBalls P.cone P.unit)
    (p s q : pure P.cone P.unit) (hps : p ≠ s)
    (hsp : exclusion P.cone P.unit s = exclusion P.cone P.unit p)
    (hq : (q : P.V) ∈ exclusion P.cone P.unit p) :
    ¬ arena.{v}.Law erased.{v} := by
  intro h
  obtain ⟨e, he, _⟩ := h P hc hs hg hB p s q hps hsp hq
  exact he

#print axioms source_bridge
#print axioms actual_positive
#print axioms erased_negative_of_input

end Reg.D5.S3.Quantum.Foundation.BinaryCenterGeometry
