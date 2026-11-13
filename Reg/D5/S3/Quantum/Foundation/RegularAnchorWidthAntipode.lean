import D5.S3.Quantum.Foundation.RegularAnchorWidthAntipode
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Actual support and full-effect width observations retain the original carrier.
Whole-family intervention, role sensitivity, observational dependence and lawful
source selection are not supplied by the exact source reconstruction alone. -/

noncomputable section
universe v

namespace Reg.D5.S3.Quantum.Foundation.RegularAnchorWidthAntipode

open _root_.D5.S3.Quantum.Foundation.CircuitBalancedConfirmation
open _root_.D5.S3.Quantum.Foundation.FacetZeroGluing
open _root_.D5.S3.Quantum.Foundation.RegularAnchorNormalChart
open _root_.D5.S3.Quantum.Foundation.RegularAnchorWidthAntipode
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

structure Inputs where
  V : Type v
  [add : NormedAddCommGroup V]
  [space : NormedSpace ℝ V]
  [finite : FiniteDimensional ℝ V]
  cone : PointedCone ℝ V
  unit : V →ₗ[ℝ] ℝ
  p : pure cone unit
  effect : V →ₗ[ℝ] ℝ
  chart : FullBall3Chart cone unit p
  native : NativeChart cone unit p effect chart

attribute [instance] Inputs.add Inputs.space Inputs.finite

abbrev signature : Signature where
  Params := Inputs.{v}
  State _ := ThreeSpace
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ × ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{v} :=
  realize signature (fun _ P w => (rho P.native w, width P.chart)) (fun a => nomatch a)

abbrev arena : Arena where
  signature := signature.{v}
  Law O := ∀ P : Inputs.{v},
    IsClosed (P.cone : Set P.V) →
    (∀ x ∈ P.cone, x ≠ 0 → 0 < P.unit x) →
    Submodule.span ℝ (P.cone : Set P.V) = ⊤ → EB3 P.cone P.unit →
    (∀ w : ThreeSpace, ‖w‖ = 1 →
      ((O.readout () P w).1 = 1 ↔ ∃ f : P.V →ₗ[ℝ] ℝ,
        proper P.cone P.unit f ∧ f (P.chart.param w) = 1 ∧
          f (P.chart.param (-w)) = 0)) ∧
    ((O.readout () P 0).2 = 1 ↔ ∃ w : ThreeSpace,
      ‖w‖ = 1 ∧ (O.readout () P w).1 = 1)

abbrev sourceScope : Prop :=
  type_of% (@rho_one_iff_antipodal.{v}) ∧ type_of% (@width_one_iff_rho_one.{v})

theorem source_bridge : sourceScope.{v} ↔ arena.{v}.Law actual.{v} := by
  constructor
  · rintro ⟨hR,hW⟩ P hc hs hg h3
    constructor
    · intro w hw
      exact @hR P.V P.add P.space P.finite P.cone P.unit P.p P.effect P.chart
        hc hs hg h3 P.native w hw
    · exact @hW P.V P.add P.space P.finite P.cone P.unit P.p P.effect P.chart
        hc hs hg h3 P.native
  · intro h
    constructor
    · intro V add space finite C u p e a hc hs hg h3 n w hw
      exact (h (@Inputs.mk V add space finite C u p e a n) hc hs hg h3).1 w hw
    · intro V add space finite C u p e a hc hs hg h3 n
      exact (h (@Inputs.mk V add space finite C u p e a n) hc hs hg h3).2

theorem actual_positive : arena.{v}.Law actual.{v} :=
  source_bridge.mp ⟨@rho_one_iff_antipodal.{v}, @width_one_iff_rho_one.{v}⟩

end Reg.D5.S3.Quantum.Foundation.RegularAnchorWidthAntipode
