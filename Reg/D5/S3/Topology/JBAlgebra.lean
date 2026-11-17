import D5.S3.Topology.JBAlgebra
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Exact full-telescope source reconstruction for powers and their closed span.
These bridges and current applications are partial audit evidence. They do not
supply whole-family intervention, sensitivity, observational dependence or
source-coordinate occurrence ties for a four-slot registration. -/

set_option autoImplicit false
noncomputable section
universe u

namespace Reg.D5.S3.Topology.JBAlgebra

open _root_.D5.S3.Topology.JBAlgebra
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

structure Inputs where
  X : Type u
  [normed : NormedAddCommGroup X]
  [space : NormedSpace ℝ X]
  S : X →ₗ[ℝ] X →ₗ[ℝ] X
  unit : X
  model : Data X S unit

attribute [instance] Inputs.normed Inputs.space

abbrev PowerState (P : Inputs.{u}) := P.X × ℕ × ℕ

abbrev powerSignature : Signature where
  Params := Inputs.{u}
  State := PowerState
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ P => P.X
  Anchor := Empty
  finiteAnchor := inferInstance

def powerActual : Realization powerSignature.{u} :=
  realize powerSignature
    (fun role P z => if role then
      P.S (npow P.S P.unit z.1 z.2.1) (npow P.S P.unit z.1 z.2.2)
      else npow P.S P.unit z.1 (z.2.1 + z.2.2))
    (fun e => nomatch e)

abbrev powerArena : Arena where
  signature := powerSignature.{u}
  Law R := ∀ P z, R.readout true P z = R.readout false P z

abbrev powerSourceScope : Prop := type_of% (@power_mul.{u})

theorem power_source_bridge : powerSourceScope.{u} ↔ powerArena.{u}.Law powerActual.{u} := by
  constructor
  · intro h P z
    exact h P.model z.1 z.2.1 z.2.2
  · intro h X normed space S unit A a m n
    exact h { X := X, normed := normed, space := space, S := S, unit := unit, model := A } (a, m, n)

theorem power_actual_positive : powerArena.{u}.Law powerActual.{u} :=
  power_source_bridge.mp (@power_mul.{u})

abbrev operatorSignature : Signature where
  Params := Inputs.{u}
  State := PowerState
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ P => P.X →L[ℝ] P.X
  Anchor := Empty
  finiteAnchor := inferInstance

def operatorActual : Realization operatorSignature.{u} :=
  realize operatorSignature
    (fun role P z => if role then
      lmul P.model (npow P.S P.unit z.1 z.2.1) *
        lmul P.model (npow P.S P.unit z.1 z.2.2)
      else lmul P.model (npow P.S P.unit z.1 z.2.2) *
        lmul P.model (npow P.S P.unit z.1 z.2.1))
    (fun e => nomatch e)

abbrev operatorArena : Arena where
  signature := operatorSignature.{u}
  Law R := ∀ P z, R.readout true P z = R.readout false P z

abbrev operatorSourceScope : Prop := type_of% (@power_lmul_commute.{u})

theorem operator_source_bridge :
    operatorSourceScope.{u} ↔ operatorArena.{u}.Law operatorActual.{u} := by
  constructor
  · intro h P z
    exact (h P.model z.1 z.2.1 z.2.2).eq
  · intro h X normed space S unit A a m n
    exact h { X := X, normed := normed, space := space, S := S, unit := unit, model := A } (a, m, n)

theorem operator_actual_positive : operatorArena.{u}.Law operatorActual.{u} :=
  operator_source_bridge.mp (@power_lmul_commute.{u})

abbrev Candidate (P : Inputs.{u}) := P.X → P.X → P.X

abbrev generatedSignature : Signature where
  Params := Inputs.{u}
  State := Candidate
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ P => Candidate P
  Anchor := Empty
  finiteAnchor := inferInstance

def generatedActual : Realization generatedSignature.{u} :=
  realize generatedSignature (fun _ _ T => T) (fun e => nomatch e)

abbrev generatedArena : Arena where
  signature := generatedSignature.{u}
  Law R := ∀ P a,
    let C := generated P.S P.unit a
    let T := R.readout () P (fun x y => P.S x y)
    (∀ x ∈ C, ∀ y ∈ C, T x y ∈ C) ∧
    (∀ x ∈ C, ∀ y ∈ C, ∀ z ∈ C, T (T x y) z = T x (T y z)) ∧
    (∀ x ∈ C, ∀ y ∈ C, ∀ v : P.X, T x (T y v) = T y (T x v))

abbrev generatedSourceScope : Prop := type_of% (@generated_algebra.{u})

theorem generated_source_bridge :
    generatedSourceScope.{u} ↔ generatedArena.{u}.Law generatedActual.{u} := by
  constructor
  · intro h P a
    obtain ⟨hp, ha, hc⟩ := h P.model a
    refine ⟨hp, ha, ?_⟩
    intro x hx y hy v
    exact congrArg (fun T : P.X →L[ℝ] P.X => T v) (hc x hx y hy).eq
  · intro h X normed space S unit A a
    obtain ⟨hp, ha, hc⟩ := h { X := X, normed := normed, space := space, S := S, unit := unit, model := A } a
    refine ⟨hp, ha, ?_⟩
    intro x hx y hy
    ext v
    exact hc x hx y hy v

theorem generated_actual_positive : generatedArena.{u}.Law generatedActual.{u} :=
  generated_source_bridge.mp (@generated_algebra.{u})

end Reg.D5.S3.Topology.JBAlgebra
