import D5.S3.Topology.JBFiniteSpectral
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Full finite-dimensional six-law source reconstruction and the actual square-defect
application. Whole-family intervention, sensitivity, observational dependence and
source-coordinate selection are not supplied by these partial audit bridges. -/

set_option autoImplicit false
noncomputable section
universe u v

namespace Reg.D5.S3.Topology.JBFiniteSpectral

open _root_.D5.S3.Topology
open _root_.D5.S3.Topology.JBAlgebra
open _root_.D5.S3.Topology.JBFiniteSpectral
open _root_.D5.S3.Topology.JBSquareDefect
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators

structure Inputs where
  X : Type u
  [normed : NormedAddCommGroup X]
  [space : NormedSpace ℝ X]
  [finite : FiniteDimensional ℝ X]
  S : X →ₗ[ℝ] X →ₗ[ℝ] X
  unit : X
  model : Data X S unit

attribute [instance] Inputs.normed Inputs.space Inputs.finite

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
      ∑ i, e i = P.unit ∧ ∑ i, r i • e i = a ∧
      ∑ i, (r i * r i) • e i = R.readout () P (a, a)

abbrev sourceScope : Prop := type_of% (@finite_spectral_resolutions.{u})

theorem source_bridge : sourceScope.{u} ↔ arena.{u}.Law actual.{u} := by
  constructor
  · intro h P
    exact h P.model
  · intro h X normed space finite S unit A
    exact h (@Inputs.mk X normed space finite S unit A)

theorem actual_positive : arena.{u}.Law actual.{u} :=
  source_bridge.mp (@finite_spectral_resolutions.{u})

/-- The existing defect consumer receives the constructed supplier on the same source carrier. -/
theorem square_defect_application
    {X : Type u} {Y : Type v} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    {S : X →ₗ[ℝ] X →ₗ[ℝ] X} {unit : X}
    {T : Y →ₗ[ℝ] Y →ₗ[ℝ] Y} {vunit : Y}
    (A : Data X S unit) (B : Data Y T vunit) (Φ : X →ₗ[ℝ] Y)
    (hunit : Φ unit = vunit) (hpos : ∀ x, ∃ y, T y y = Φ (S x x)) (a : X) :
    ∃ z, T z z = Φ (S a a) - T (Φ a) (Φ a) :=
  square_defect_of_spectral B (finite_spectral_resolutions A) Φ hunit hpos a

end Reg.D5.S3.Topology.JBFiniteSpectral
