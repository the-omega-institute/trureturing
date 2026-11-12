import D5.S3.Quantum.Foundation.RealRogFailureQuantitative
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Exact reconstruction and positivity for the original primal source family.
Whole-family intervention, sensitivity, observational dependence and a lawful
four-slot source selection remain unsupplied. There is no declared_validated
registration in this mirror. -/

noncomputable section
universe u
namespace Reg.D5.S3.Quantum.Foundation.RealRogFailureQuantitative

open _root_.D5.S3.Quantum.Foundation.RealRogFailureQuantitative
open _root_.D5.S3.Quantum.Foundation.CircuitBalancedConfirmation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

structure PrimalInputs where
  Carrier : Type u
  [normed : NormedAddCommGroup Carrier]
  [space : NormedSpace ℝ Carrier]
  [finite : FiniteDimensional ℝ Carrier]
  cone : PointedCone ℝ Carrier
  unit : Carrier →ₗ[ℝ] ℝ

attribute [instance] PrimalInputs.normed PrimalInputs.space PrimalInputs.finite

abbrev primalSignature : Signature where
  Params := PrimalInputs.{u}
  State P := P.Carrier
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def primalActual : Realization primalSignature.{u} :=
  realize primalSignature (fun _ P z =>
    _root_.D5.S3.Quantum.Dynamics.BaseNormContraction.baseNorm P.cone.toConvexCone P.unit z)
    (fun e => nomatch e)

abbrev primalArena : Arena where
  signature := primalSignature.{u}
  Law O := ∀ P : PrimalInputs.{u},
    let C := P.cone
    let u := P.unit
    IsCompact (base C u) →
    (∀ a ∈ C, a ≠ 0 → 0 < u a) →
    Submodule.span ℝ (C : Set P.Carrier) = ⊤ →
    ∀ z : P.Carrier, ∃ X Y : P.Carrier, X ∈ C ∧ Y ∈ C ∧ z = X - Y ∧
      u X + u Y = O.readout () P z ∧
      (∀ a b : P.Carrier, a ∈ C → b ∈ C → z = a - b → u X + u Y ≤ u a + u b) ∧
      u X = (O.readout () P z + u z) / 2 ∧
      u Y = (O.readout () P z - u z) / 2

abbrev primalSourceScope : Prop := type_of% (@original_primal_attainment.{u})

theorem primal_source_bridge : primalSourceScope.{u} ↔ primalArena.{u}.Law primalActual.{u} := by
  constructor
  · intro h P
    exact @h P.Carrier P.normed P.space P.finite P.cone P.unit
  · intro h Carrier normed space finite C unit
    exact h (@PrimalInputs.mk Carrier normed space finite C unit)

theorem primal_actual_positive : primalArena.{u}.Law primalActual.{u} :=
  primal_source_bridge.mp (@original_primal_attainment.{u})

end Reg.D5.S3.Quantum.Foundation.RealRogFailureQuantitative
