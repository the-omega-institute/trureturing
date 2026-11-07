import D5.S3.Quantum.Algebra.UnitBridgeRawGeometry
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Source reconstruction for the original total spin relation.
The dependent family includes the whole topological space, original subalgebra,
raw relation, both original inputs and the point of observation.
Whole-family intervention, sensitivity and observational-dependence evidence
are separate obligations; no validated registration is asserted here. -/

set_option autoImplicit false
noncomputable section
universe u

namespace Reg.D5.S3.Quantum.Algebra.UnitBridgeRawGeometry

open _root_.D5.S3.Quantum.Algebra.UnitBridgeRawGeometry
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

structure RawInputs where
  T : Type u
  [topology : TopologicalSpace T]
  E : Original T
  R : Raw E

attribute [instance] RawInputs.topology

abbrev RawState (P : RawInputs.{u}) := P.E.Elem × P.E.Elem × P.T

abbrev rawSignature : Signature where
  Params := RawInputs.{u}
  State := RawState
  Role := Fin 3
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def rawActual : Realization rawSignature.{u} :=
  realize rawSignature
    (fun role P z =>
      let p := P.R.D z.1 z.2.1
      if role = 0 then p.val 0 z.2.2
      else if role = 1 then vdot (fun i => z.1.val i z.2.2) (fun i => p.val i z.2.2)
      else vdot (fun i => z.2.1.val i z.2.2) (fun i => p.val i z.2.2))
    (fun e => nomatch e)

abbrev rawArena : Arena where
  signature := rawSignature.{u}
  Law R := ∀ (P : RawInputs.{u}) (z : RawState P),
    R.readout 0 P z = 0 ∧ R.readout 1 P z = 0 ∧ R.readout 2 P z = 0

abbrev normalSourceScope : Prop := type_of% (@raw_output_normal.{u})

theorem raw_source_bridge : normalSourceScope.{u} ↔ rawArena.{u}.Law rawActual := by
  constructor
  · intro h P z
    exact h P.R z.1 z.2.1 z.2.2
  · intro h T topology E R a b t
    exact h ⟨T, E, R⟩ (a,b,t)

theorem raw_actual_positive : rawArena.{u}.Law rawActual :=
  raw_source_bridge.mp (@raw_output_normal.{u})

theorem components_source_application : type_of% (@original_four_components.{u}) :=
  @original_four_components.{u}

theorem fibre_source_application : type_of% (@raw_h_fibre.{u}) := @raw_h_fibre.{u}

theorem homogeneity_source_application : type_of% (@raw_real_homogeneity.{u}) :=
  @raw_real_homogeneity.{u}

end Reg.D5.S3.Quantum.Algebra.UnitBridgeRawGeometry
