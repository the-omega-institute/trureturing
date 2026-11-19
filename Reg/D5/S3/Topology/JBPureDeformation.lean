import D5.S3.Topology.JBPureDeformation
import Reg.Support.DependentFamily

/-! Exact source-family reconstruction for the complete original deformation.
The source bridge and actual-positive law are partial audit evidence. A lawful
enrolled template with whole-family intervention and sensitivity is not supplied. -/

set_option autoImplicit false
noncomputable section
open scoped Topology
universe u

namespace Reg.D5.S3.Topology.JBPureDeformation
open _root_.D5.S3.Topology
open _root_.D5.S3.Topology.JBPureDeformation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

structure Inputs where
  X : Type u
  [normed : NormedAddCommGroup X]
  [space : NormedSpace ℝ X]
  [complete : CompleteSpace X]
  S : X →ₗ[ℝ] X →ₗ[ℝ] X
  unit : X
  model : JBAlgebra.Data X S unit
  beta : X →L[ℝ] ℝ
  pure : beta ∈ (states S unit).extremePoints ℝ
  h : X
  zeroMoment : beta h = 0
  positiveMoment : 0 < beta (S h h)

attribute [instance] Inputs.normed Inputs.space Inputs.complete

abbrev signature : Signature where
  Params := Inputs.{u}
  State _ := Unit
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ P := ℝ → P.X →L[ℝ] ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ P _ => deformation P.model P.beta P.h) (fun e => nomatch e)

def conclusion (P : Inputs.{u}) (f : ℝ → P.X →L[ℝ] ℝ) : Prop :=
  (∀ᶠ t : ℝ in 𝓝[≠] 0,
    (∃ a : P.X, P.S a a = P.unit + t • P.h) ∧
    Function.Bijective (JBPositiveShift.quadratic P.S (P.unit + t • P.h)) ∧
    0 < P.beta (JBPositiveShift.quadratic P.S (P.unit + t • P.h) P.unit) ∧
    f t ∈ (states P.S P.unit).extremePoints ℝ ∧
    f t P.h = (2 * t * P.beta (P.S P.h P.h) +
      t ^ 2 * P.beta (P.S P.h (P.S P.h P.h))) /
        (1 + t ^ 2 * P.beta (P.S P.h P.h)) ∧ f t P.h ≠ 0) ∧
  Filter.Tendsto f (𝓝 0) (𝓝 P.beta)

abbrev arena : Arena where
  signature := signature.{u}
  Law r := ∀ P, conclusion P (r.readout () P ())

abbrev sourceScope : Prop := type_of% (@pure_deformation.{u})

theorem source_bridge : sourceScope.{u} ↔ arena.{u}.Law actual.{u} := by
  constructor
  · intro h P
    exact h P.model P.beta P.pure P.h P.zeroMoment P.positiveMoment
  · intro h X normed space complete S unit A beta hp v hz hq
    exact h (@Inputs.mk X normed space complete S unit A beta hp v hz hq)

theorem actual_positive : arena.{u}.Law actual.{u} :=
  source_bridge.mp (@pure_deformation.{u})

#check Registration arena.{u} sourceScope.{u}
#print axioms source_bridge
#print axioms actual_positive

end Reg.D5.S3.Topology.JBPureDeformation
