import D5.S3.Quantum.Foundation.ReciprocalExclusionLimits
import Reg.D5.S3.Quantum.Foundation.ReciprocalPureCompactness

/-! Exact original comparison observations and whole-limit source reconstruction.
No whole-family intervention, observational-dependence proof, source selection
or completed four-slot registration is asserted. -/
noncomputable section
universe v
open Set Filter Topology TopologicalSpace

namespace Reg.D5.S3.Quantum.Foundation.ReciprocalExclusionLimits
open _root_.D5.S3.Quantum.Foundation.CircuitBalancedConfirmation
open _root_.D5.S3.Quantum.Foundation.FacetZeroGluing
open _root_.D5.S3.Quantum.Foundation.ReciprocalExclusionLimits
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.D5.S3.Quantum.Foundation.ReciprocalEndpointExposure
open Reg.D5.S3.Quantum.Foundation.ReciprocalPureCompactness

abbrev arena : Arena where
  signature := pureCompactSignature.{v}
  Law O := ∀ P : Inputs.{v}, IsClosed (P.cone : Set P.V) →
    (∀ x ∈ P.cone, x ≠ 0 → 0 < P.unit x) →
    Submodule.span ℝ (P.cone : Set P.V) = ⊤ → threeBallExclusions P.cone P.unit →
    (∀ p q : pure P.cone P.unit, O.readout () P (p,q) = O.readout () P (q,p)) →
    ∀ {p : pure P.cone P.unit} {an : ℕ → pure P.cone P.unit},
    Tendsto an atTop (𝓝 p) →
    ∀ (F : ℕ → NonemptyCompacts P.V) (Q : NonemptyCompacts P.V),
    (∀ n, (F n : Set P.V) = exclusion P.cone P.unit (an n)) →
    Tendsto F atTop (𝓝 Q) →
    (Q : Set P.V) = exclusion P.cone P.unit p ∨
      ∃ q : pure P.cone P.unit, (q : P.V) ∈ exclusion P.cone P.unit p ∧
        (Q : Set P.V) = {(q : P.V)}

abbrev sourceScope : Prop := type_of% (@exclusion_limit_dichotomy.{v})

theorem source_bridge : sourceScope.{v} ↔ arena.{v}.Law pureCompactActual.{v} := by
  constructor
  · intro h P
    exact @h P.V P.add P.space P.finite P.cone P.unit
  · intro h V add space finite C u hc hs hg h3 hPR p an ha F Q hF ht
    exact h (@Inputs.mk V add space finite C u) hc hs hg h3 hPR ha F Q hF ht

theorem actual_positive : arena.{v}.Law pureCompactActual.{v} :=
  source_bridge.mp (@exclusion_limit_dichotomy.{v})

#print axioms source_bridge
#print axioms actual_positive

end Reg.D5.S3.Quantum.Foundation.ReciprocalExclusionLimits
