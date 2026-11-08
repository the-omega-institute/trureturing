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
  spaceE : letI := groupE; NormedSpace ℝ E
  completeE : letI := groupE; CompleteSpace E
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

abbrev rigidityScope := type_of% (@eq_zero_of_symmetric_exp_isometry.{u})

theorem rigidity_actual : rigidityScope.{u} := @eq_zero_of_symmetric_exp_isometry.{u}

structure RigidityInputs where
  E : Type u
  groupE : NormedAddCommGroup E
  spaceE : letI := groupE; NormedSpace ℝ E
  completeE : letI := groupE; CompleteSpace E

attribute [instance] RigidityInputs.groupE RigidityInputs.spaceE RigidityInputs.completeE

abbrev rigidityState (P : RigidityInputs.{u}) := (P.E →L[ℝ] P.E →L[ℝ] P.E) × P.E × P.E

abbrev rigiditySignature : Signature where
  Params := RigidityInputs.{u}
  State := rigidityState
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ P => P.E
  Anchor := Empty
  finiteAnchor := inferInstance

def rigidityActual : Realization rigiditySignature.{u} :=
  realize rigiditySignature (fun _ _ st => st.1 st.2.1 st.2.2) (fun a => nomatch a)

def rigidityArena : Arena where
  signature := rigiditySignature.{u}
  Law := fun r => ∀ P (B : P.E →L[ℝ] P.E →L[ℝ] P.E),
    (∀ x y : P.E, B x y = B y x) →
    (∀ (x : P.E) (t : ℝ), Isometry (fun y : P.E => (NormedSpace.exp (t • B x)) y)) →
    ∀ x y : P.E, r.readout () P (B, x, y) = 0

theorem rigidity_source_bridge : rigidityScope.{u} ↔ rigidityArena.{u}.Law rigidityActual.{u} := by
  constructor
  · intro h P B hsymm hiso x y
    change B x y = 0
    rw [h B hsymm hiso]
    rfl
  · intro h E groupE spaceE completeE B hsymm hiso
    let P : RigidityInputs.{u} := ⟨E, groupE, spaceE, completeE⟩
    ext x y
    exact h P B hsymm hiso x y

theorem rigidity_actual_positive : rigidityArena.{u}.Law rigidityActual.{u} :=
  rigidity_source_bridge.mp (@eq_zero_of_symmetric_exp_isometry.{u})

end Reg.D5.S3.Topology.BanachQuadraticRigidity
