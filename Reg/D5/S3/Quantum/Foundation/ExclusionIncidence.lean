import D5.S3.Quantum.Foundation.ExclusionIncidence
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Exact original-domain realizations of the two upper-association statements.
Whole-family variation, sensitivity and observational dependence are unresolved. -/

noncomputable section
universe v

namespace Reg.D5.S3.Quantum.Foundation.ExclusionIncidence

open Filter Topology
open _root_.D5.S3.Quantum.Foundation.CircuitBalancedConfirmation
open _root_.D5.S3.Quantum.Foundation.FacetZeroGluing
open _root_.D5.S3.Quantum.Foundation.ExclusionBallFaces
open _root_.D5.S3.Quantum.Foundation.ExclusionIncidence
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
  State P := pure P.cone P.unit
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ P := Set P.V
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{v} :=
  realize signature (fun _ P p => exclusion P.cone P.unit p) (fun e => nomatch e)

namespace Limit

abbrev arena : Arena where
  signature := signature.{v}
  Law O := ∀ P : Inputs.{v},
    IsClosed (P.cone : Set P.V) →
    (∀ x ∈ P.cone, x ≠ 0 → 0 < P.unit x) →
    Submodule.span ℝ (P.cone : Set P.V) = ⊤ →
    ∀ {p : pure P.cone P.unit} {pn : ℕ → pure P.cone P.unit}
      {y : P.V} {yn : ℕ → P.V},
      Tendsto pn atTop (𝓝 p) → Tendsto yn atTop (𝓝 y) →
      (∀ n, yn n ∈ O.readout () P (pn n)) → y ∈ O.readout () P p

abbrev sourceScope : Prop := type_of% (@exclusion_upper_limit.{v})

theorem source_bridge : sourceScope.{v} ↔ arena.{v}.Law actual.{v} := by
  constructor
  · intro h P hc hs hg p pn y yn hp hy hyn
    exact @h P.V P.add P.space P.finite P.cone P.unit hc hs hg p pn y yn hp hy hyn
  · intro h V add space finite C u hc hs hg p pn y yn hp hy hyn
    exact h (@Inputs.mk V add space finite C u) hc hs hg hp hy hyn

theorem actual_positive : arena.{v}.Law actual.{v} :=
  source_bridge.mp (@exclusion_upper_limit.{v})

end Limit

namespace Uniform

abbrev arena : Arena where
  signature := signature.{v}
  Law O := ∀ P : Inputs.{v},
    IsClosed (P.cone : Set P.V) →
    (∀ x ∈ P.cone, x ≠ 0 → 0 < P.unit x) →
    Submodule.span ℝ (P.cone : Set P.V) = ⊤ →
    ∀ {p : pure P.cone P.unit} {pn : ℕ → pure P.cone P.unit},
      Tendsto pn atTop (𝓝 p) → ∀ {ε : ℝ}, 0 < ε →
      ∀ᶠ n in atTop, ∀ y ∈ O.readout () P (pn n),
        ∃ z ∈ O.readout () P p, dist y z < ε

abbrev sourceScope : Prop := type_of% (@exclusion_upper_eventually.{v})

theorem source_bridge : sourceScope.{v} ↔ arena.{v}.Law actual.{v} := by
  constructor
  · intro h P hc hs hg p pn hp ε hε
    exact @h P.V P.add P.space P.finite P.cone P.unit hc hs hg p pn hp ε hε
  · intro h V add space finite C u hc hs hg p pn hp ε hε
    exact h (@Inputs.mk V add space finite C u) hc hs hg hp hε

theorem actual_positive : arena.{v}.Law actual.{v} :=
  source_bridge.mp (@exclusion_upper_eventually.{v})

end Uniform

namespace IncidenceLimit

abbrev arena : Arena where
  signature := signature.{v}
  Law O := ∀ P : Inputs.{v},
    IsClosed (P.cone : Set P.V) →
    (∀ x ∈ P.cone, x ≠ 0 → 0 < P.unit x) →
    Submodule.span ℝ (P.cone : Set P.V) = ⊤ →
    exclusionBalls P.cone P.unit →
    (edgeLifting P.cone P.unit ↔ IsOpenMap (firstProjection P.cone P.unit)) ∧
    (edgeLifting P.cone P.unit → IsOpenMap (secondProjection P.cone P.unit) ∧
      ∀ (p : pure P.cone P.unit) (pn : ℕ → pure P.cone P.unit),
        Tendsto pn atTop (𝓝 p) →
        Tendsto (fun n => Metric.hausdorffDist (O.readout () P (pn n))
          (O.readout () P p)) atTop (𝓝 0))

abbrev sourceScope : Prop := type_of% (@original_open_incidence_whole_limit.{v})

theorem source_bridge : sourceScope.{v} ↔ arena.{v}.Law actual.{v} := by
  constructor
  · intro h P hc hs hg hB
    exact @h P.V P.add P.space P.finite P.cone P.unit hc hs hg hB
  · intro h V add space finite C u hc hs hg hB
    exact h (@Inputs.mk V add space finite C u) hc hs hg hB

theorem actual_positive : arena.{v}.Law actual.{v} :=
  source_bridge.mp (@original_open_incidence_whole_limit.{v})

end IncidenceLimit

end Reg.D5.S3.Quantum.Foundation.ExclusionIncidence
