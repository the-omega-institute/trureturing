import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Topology.BanachQuadraticRigidity

/-! Exact source reconstruction for the arbitrary Banach quadratic distance theorem.
The dependent readout is the actual distance of the original two solutions.
This source supplies the original telescope, source equivalence and actual-positive
law. Whole-family variation, sensitivity, observational dependence and the raw
source selector remain obligations; no validated registration is asserted. -/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Topology.BanachQuadraticRigidity

open Set
open _root_.D5.S3.Topology.BanachQuadraticRigidity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

universe u

abbrev distanceScope := type_of% (@quadratic_solution_dist_eq.{u})

theorem distance_actual : distanceScope.{u} := @quadratic_solution_dist_eq.{u}

structure Inputs where
  E : Type u
  groupE : NormedAddCommGroup E
  spaceE : @NormedSpace ℝ E _ groupE.toAddCommGroup
  completeE : @CompleteSpace E groupE.toUniformSpace
  B : letI := groupE; letI := spaceE; E →L[ℝ] E →L[ℝ] E
  symmetric : ∀ x y : E, B x y = B y x
  exponentialIsometry : letI := groupE; letI := spaceE;
    ∀ (x : E) (t : ℝ), Isometry (fun y : E => (NormedSpace.exp (t • B x)) y)
  domain : Set ℝ
  openDomain : IsOpen domain
  connectedDomain : IsPreconnected domain

attribute [instance] Inputs.groupE Inputs.spaceE Inputs.completeE

structure SourceState (P : Inputs.{u}) where
  x : ℝ → P.E
  y : ℝ → P.E
  dx : ∀ t ∈ P.domain, HasDerivAt x (P.B (x t) (x t)) t
  dy : ∀ t ∈ P.domain, HasDerivAt y (P.B (y t) (y t)) t
  t : ℝ
  v : ℝ
  ht : t ∈ P.domain
  hv : v ∈ P.domain

abbrev signature : Signature where
  Params := Inputs.{u}
  State := SourceState
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ st => dist (st.x st.t) (st.y st.t)) (fun a => nomatch a)

def arena : Arena where
  signature := signature.{u}
  Law := fun r => ∀ P st, r.readout () P st = dist (st.x st.v) (st.y st.v)

theorem source_bridge : distanceScope.{u} ↔ arena.{u}.Law actual.{u} := by
  constructor
  · intro h P st
    exact h P.B P.symmetric P.exponentialIsometry P.openDomain P.connectedDomain
      st.dx st.dy st.ht st.hv
  · intro h E groupE spaceE completeE B hsymm hiso s hs hconn x y hx hy t v ht hv
    let P : Inputs.{u} := ⟨E, groupE, spaceE, completeE, B, hsymm, hiso, s, hs, hconn⟩
    exact h P ⟨x, y, hx, hy, t, v, ht, hv⟩

theorem actual_positive : arena.{u}.Law actual.{u} :=
  source_bridge.mp (@quadratic_solution_dist_eq.{u})

end Reg.D5.S3.Topology.BanachQuadraticRigidity
