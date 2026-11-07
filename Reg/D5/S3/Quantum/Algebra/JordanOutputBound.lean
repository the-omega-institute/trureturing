import D5.S3.Quantum.Algebra.JordanOutputBound
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Exact raw-relation source reconstruction for the actual-output estimate.
The source applications and equivalence below are partial audit evidence.
Whole-family variation, sensitivity, observational dependence and occurrence
ties are not supplied by these declarations. -/

set_option autoImplicit false
noncomputable section
universe u

namespace Reg.D5.S3.Quantum.Algebra.JordanOutputBound

open _root_.D5.S3.Quantum.Algebra.JordanOutputBound
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

structure RawInputs where
  E : Type u
  [normed : NormedAddCommGroup E]
  [space : NormedSpace ℝ E]
  S : E →ₗ[ℝ] E →ₗ[ℝ] E
  comm : ∀ x y, S x y = S y x
  jordan : ∀ x y, S (S x y) (S x x) = S x (S y (S x x))
  productNorm : ∀ x y, ‖S x y‖ ≤ ‖x‖ * ‖y‖
  squareNorm : ∀ x, ‖S x x‖ = ‖x‖ ^ 2
  D : E → E → E
  skew : ∀ a b, D a b = -D b a
  row : ∀ a b c, D (D a b) c = S b (S a c) - S a (S b c)
  associator : ∀ a b c, S (S a b) c - S a (S b c) = D (D a b) c - D a (D b c)

attribute [instance] RawInputs.normed RawInputs.space

abbrev RawState (P : RawInputs.{u}) :=
  {q : P.E // q ∈ Set.range (fun p : P.E × P.E => P.D p.1 p.2)} × P.E

abbrev rawSignature : Signature where
  Params := RawInputs.{u}
  State := RawState
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def rawActual : Realization rawSignature.{u} :=
  realize rawSignature
    (fun role P z => if role then ‖P.D z.1.1 z.2‖ else ‖P.D z.2 z.1.1‖)
    (fun e => nomatch e)

abbrev rawArena : Arena where
  signature := rawSignature.{u}
  Law R := ∀ (P : RawInputs.{u}) (z : RawState P),
    R.readout true P z ≤ Real.sqrt 3 * ‖z.1.1‖ * ‖z.2‖ ∧
    R.readout false P z ≤ Real.sqrt 3 * ‖z.1.1‖ * ‖z.2‖

abbrev rawSourceScope : Prop := type_of% (@actual_output_bound.{u})
abbrev polynomialSourceScope : Prop := type_of% (@polynomial_actual_output_control.{u})

theorem raw_source_bridge : rawSourceScope.{u} ↔ rawArena.{u}.Law rawActual := by
  constructor
  · intro h P z
    exact h P.S P.comm P.jordan P.productNorm P.squareNorm
      P.D P.skew P.row P.associator z.1.property z.2
  · intro h E normed space S hc hj hn hs D hd hr hR q hq b
    exact h ⟨E, normed, space, S, hc, hj, hn, hs, D, hd, hr, hR⟩ (⟨q, hq⟩, b)

theorem raw_actual_positive : rawArena.{u}.Law rawActual :=
  raw_source_bridge.mp (@actual_output_bound.{u})

theorem polynomial_source_application : polynomialSourceScope.{u} :=
  @polynomial_actual_output_control.{u}

end Reg.D5.S3.Quantum.Algebra.JordanOutputBound
