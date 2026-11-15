import D5.S3.Quantum.Foundation.NativeTangentDisjointness
import Reg.D5.S3.Quantum.Foundation.CommonPositiveExtension

/-! Full original-family realization and source reconstruction. The enrolled
readout, whole-family sensitivity and source-selection slots remain obligations:
https://github.com/the-omega-institute/trureturing/issues/29702 -/

noncomputable section
universe v

namespace Reg.D5.S3.Quantum.Foundation.NativeTangentDisjointness

open _root_.D5.S3.Quantum.Foundation.CircuitBalancedConfirmation
open _root_.D5.S3.Quantum.Foundation.FacetZeroGluing
open _root_.D5.S3.Quantum.Foundation.ExclusionBallFaces
open _root_.D5.S3.Quantum.Foundation.OrthogonalJointCompletion
open _root_.D5.S3.Quantum.Foundation.NativeTangentDisjointness
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit.Contract
open CommonPositiveExtension

def actual : Realization signature.{v} :=
  realize signature (fun _ P _ =>
    ∃ a : pure P.cone P.unit → (P.V →ₗ[ℝ] ℝ),
      (∀ p : pure P.cone P.unit, common P.cone P.unit p (a p)) ∧
      (∀ (p : pure P.cone P.unit) f, common P.cone P.unit p f → f = a p) ∧
      ∀ p q q' : pure P.cone P.unit, (q : P.V) ∈ exclusion P.cone P.unit p →
        (q' : P.V) ∈ exclusion P.cone P.unit p → q ≠ q' →
        ∀ (b : ExclusionChart P.cone P.unit q) (b' : ExclusionChart P.cone P.unit q'),
          tangent b (a p) ⊓ tangent b' (a p) = ⊥) (fun e => nomatch e)

abbrev sourceScope : Prop := type_of% (@whole_native_tangent_disjointness.{v})

theorem source_bridge : sourceScope.{v} ↔ arena.{v}.Law actual.{v} := by
  constructor
  · intro h P
    exact @h P.V P.add P.space P.finite P.nontrivial P.cone P.unit
  · intro h V add space finite nontrivial C u hc hs hg hB hW
    exact h (@Inputs.mk V add space finite nontrivial C u) hc hs hg hB hW

theorem actual_positive : arena.{v}.Law actual.{v} :=
  source_bridge.mp (@whole_native_tangent_disjointness.{v})

theorem erased_negative (P : Inputs.{v})
    (hc : IsClosed (P.cone : Set P.V))
    (hs : ∀ x ∈ P.cone, x ≠ 0 → 0 < P.unit x)
    (hg : Submodule.span ℝ (P.cone : Set P.V) = ⊤)
    (hB : exclusionBalls P.cone P.unit) (hW : weakPair P.cone P.unit) :
    ¬ arena.{v}.Law erased.{v} := fun h => h P hc hs hg hB hW

/-- This whole-theorem observation cannot provide a varying state readout. -/
theorem dependence_impossible : ¬ ObservationalDependence signature.{v} actual.{v} := by
  intro h
  obtain ⟨P,x,y,he⟩ := h ()
  exact he (by cases x; cases y; rfl)

/-- The required four-slot type; no value or validation status is asserted. -/
abbrev pendingEvidence := Registration arena.{v} sourceScope.{v}

#print axioms source_bridge
#print axioms actual_positive
#print axioms erased_negative
#print axioms dependence_impossible

end Reg.D5.S3.Quantum.Foundation.NativeTangentDisjointness
