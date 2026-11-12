import D5.S3.Topology.EJAFiniteSpectral
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Full original-carrier EJA source reconstruction.
Whole-family intervention, sensitivity, observational dependence and source-coordinate
selection are not supplied by these partial audit bridges. -/

set_option autoImplicit false
noncomputable section
universe u

namespace Reg.D5.S3.Topology.EJAFiniteSpectral

open _root_.D5.S3.Topology.EJAFiniteSpectral
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators

structure Inputs where
  X : Type u
  [normed : NormedAddCommGroup X]
  [inner : InnerProductSpace ℝ X]
  [finite : FiniteDimensional ℝ X]
  S : X →ₗ[ℝ] X →ₗ[ℝ] X
  unit : X
  model : Data X S unit

attribute [instance] Inputs.normed Inputs.inner Inputs.finite

abbrev signature : Signature where
  Params := Inputs.{u}
  State P := P.X × P.X
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ P := P.X
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ P z => P.S z.1 z.2) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ (P : Inputs.{u}) (a : P.X),
    ∃ (n : ℕ) (e : Fin n → P.X) (r : Fin n → ℝ),
      (∀ i, R.readout () P (e i, e i) = e i) ∧
      (∀ i j, i ≠ j → R.readout () P (e i, e j) = 0) ∧
      ∑ i, e i = P.unit ∧ ∑ i, r i • e i = a ∧
      ∑ i, (r i ^ 2) • e i = R.readout () P (a, a) ∧
      (P.unit = 0 → n = 0)

abbrev sourceScope : Prop := type_of% (@finite_spectral_resolution.{u})

theorem source_bridge : sourceScope.{u} ↔ arena.{u}.Law actual.{u} := by
  constructor
  · intro h P
    exact h P.model
  · intro h X normed inner finite S unit A
    exact h (@Inputs.mk X normed inner finite S unit A)

theorem actual_positive : arena.{u}.Law actual.{u} :=
  source_bridge.mp (@finite_spectral_resolution.{u})

namespace ScalarCompatibility

structure Inputs where
  X : Type u
  [ring : NonUnitalNonAssocCommRing X]
  [scalar : Module ℝ X]
  [tower : IsScalarTower ℝ X X]

attribute [instance] Inputs.ring Inputs.scalar Inputs.tower

abbrev signature : Signature where
  Params := Inputs.{u}
  State P := P.X × P.X × ℝ
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ P := P.X
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun role _ z => if role then z.2.2 • z.1 else z.1 * z.2.1)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ (P : Inputs.{u}) (r : ℝ) (a b : P.X),
    R.readout false P (a, R.readout true P (b, b, r), r) =
      R.readout true P (R.readout false P (a, b, r), b, r)

abbrev sourceScope : Prop := type_of% (@mul_smul_comm'.{u})

theorem source_bridge : sourceScope.{u} ↔ arena.{u}.Law actual.{u} := by
  constructor
  · intro h P r a b
    exact h r a b
  · intro h X ring scalar tower r a b
    exact h (@Inputs.mk X ring scalar tower) r a b

theorem actual_positive : arena.{u}.Law actual.{u} :=
  source_bridge.mp (@mul_smul_comm'.{u})

end ScalarCompatibility

end Reg.D5.S3.Topology.EJAFiniteSpectral
