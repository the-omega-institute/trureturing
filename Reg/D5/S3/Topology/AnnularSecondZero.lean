import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Topology.AnnularSecondZero

/-!
Exact source telescopes and faithful whole-map source families are retained here.
The enrolled dependent-family template realizes the original map in every occurrence.
For this whole-map arena every realization satisfies the source law, so variation and
sensitivity are unavailable. This is an obstruction to this particular arena, not to
every possible information audit. No four-slot registration is asserted. A different
faithful observation decomposition, exact source-coordinate selection, and its variation,
sensitivity and dependence evidence remain necessary. The audit issue is
https://github.com/the-omega-institute/trureturing/issues/23724.
-/

set_option autoImplicit false

open Metric
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Topology.AnnularSecondZero

noncomputable section

namespace Reg.D5.S3.Topology.AnnularSecondZero

universe u

abbrev constantExteriorScope := type_of% (@constantExterior_second_zero.{u})
abbrev annularScope := type_of% (@annular_second_zero)

theorem constantExterior_source : constantExteriorScope.{u} := @constantExterior_second_zero.{u}
theorem annular_source : annularScope := @annular_second_zero

structure ExteriorInputs where
  E : Type u
  group : NormedAddCommGroup E
  space : letI := group; NormedSpace ℝ E
  finite : letI := group; letI := space; FiniteDimensional ℝ E
  nontrivial : Nontrivial E
  q : E → E
  a : E
  c : E
  M : ℝ
  L : letI := group; letI := space; E ≃L[ℝ] E

abbrev exteriorSignature : Signature.{u+1,u,0,u,0} where
  Params := ExteriorInputs.{u}
  State P := P.E
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ P := P.E
  Anchor := Empty
  finiteAnchor := inferInstance

def exteriorActual : Realization exteriorSignature.{u} :=
  realize exteriorSignature.{u} (fun _ P x => P.q x) (fun e => nomatch e)

def exteriorArena : Arena.{u+1,u,0,u,0} where
  signature := exteriorSignature.{u}
  Law R := ∀ P : ExteriorInputs.{u},
    letI := P.group
    letI := P.space
    letI := P.finite
    letI := P.nontrivial
    Continuous (R.readout () P) → P.c ≠ 0 →
    (∀ x, P.M ≤ ‖x‖ → R.readout () P x = P.c) →
    R.readout () P P.a = 0 →
    HasFDerivAt (R.readout () P) (P.L : P.E →L[ℝ] P.E) P.a →
    ∃ b, b ≠ P.a ∧ R.readout () P b = 0

theorem exterior_every_realization (R : Realization exteriorSignature.{u}) :
    exteriorArena.{u}.Law R := by
  intro P
  let := P.group
  let := P.space
  let := P.finite
  let := P.nontrivial
  exact constantExterior_second_zero (R.readout () P) P.a P.c P.M P.L

theorem exterior_bridge : constantExteriorScope.{u} ↔ exteriorArena.{u}.Law exteriorActual.{u} := by
  constructor
  · intro h P
    exact @h P.E P.group P.space P.finite P.nontrivial P.q P.a P.c P.M P.L
  · intro h E group space finite nontrivial q a c M L
    exact h ⟨E, group, space, finite, nontrivial, q, a, c, M, L⟩

theorem exterior_variation_unavailable : ¬ Variation exteriorArena.{u} exteriorActual.{u} := by
  rintro ⟨_, R, hR⟩
  exact hR (exterior_every_realization R)

theorem exterior_sensitivity_unavailable : ¬ Sensitivity exteriorArena.{u} exteriorActual.{u} := by
  rintro ⟨h, _⟩
  obtain ⟨R, _, _, hR⟩ := h ()
  exact hR (exterior_every_realization R)

theorem exterior_actual_dependence :
    ObservationalDependence exteriorSignature.{u} exteriorActual.{u} := by
  intro i
  let E := EuclideanSpace ℝ (ULift.{u} (Fin 1))
  let P : ExteriorInputs.{u} := ⟨E, inferInstance, inferInstance, inferInstance, inferInstance,
    id, 0, 0, 1, ContinuousLinearEquiv.refl ℝ E⟩
  let y : E := WithLp.toLp 2 (fun _ => (1 : ℝ))
  refine ⟨P, 0, y, ?_⟩
  change (0 : E) ≠ y
  intro h
  have := congrArg (fun v : E => v (ULift.up 0)) h
  norm_num [y] at this

structure AnnularInputs where
  f : ℂ → ℂ
  a : ℂ
  r : ℝ
  R : ℝ
  L : ℂ ≃L[ℝ] ℂ

abbrev annularSignature : Signature where
  Params := AnnularInputs
  State _ := ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def annularActual : Realization annularSignature :=
  realize annularSignature (fun _ P z => P.f z) (fun e => nomatch e)

def annularArena : Arena where
  signature := annularSignature
  Law Q := ∀ P : AnnularInputs,
    0 < P.r → P.r < ‖P.a‖ → ‖P.a‖ < P.R →
    ContinuousOn (Q.readout () P) (closedBall 0 P.R \ ball 0 P.r) →
    Q.readout () P P.a = 0 →
    HasFDerivAt (Q.readout () P) (P.L : ℂ →L[ℝ] ℂ) P.a →
    (∀ z : ℂ, ‖z‖ = P.r ∨ ‖z‖ = P.R → (Q.readout () P z).re < 0) →
    ∃ b : ℂ, P.r < ‖b‖ ∧ ‖b‖ < P.R ∧ b ≠ P.a ∧ Q.readout () P b = 0

theorem annular_every_realization (Q : Realization annularSignature) :
    annularArena.Law Q := by
  intro P
  exact annular_second_zero (Q.readout () P) P.a P.r P.R P.L

theorem annular_bridge : annularScope ↔ annularArena.Law annularActual := by
  constructor
  · intro h P
    exact h P.f P.a P.r P.R P.L
  · intro h f a r R L
    exact h ⟨f, a, r, R, L⟩

theorem annular_variation_unavailable : ¬ Variation annularArena annularActual := by
  rintro ⟨_, Q, hQ⟩
  exact hQ (annular_every_realization Q)

theorem annular_sensitivity_unavailable : ¬ Sensitivity annularArena annularActual := by
  rintro ⟨h, _⟩
  obtain ⟨Q, _, _, hQ⟩ := h ()
  exact hQ (annular_every_realization Q)

theorem annular_actual_dependence : ObservationalDependence annularSignature annularActual := by
  intro i
  let P : AnnularInputs := ⟨id, 1, 1 / 2, 2, ContinuousLinearEquiv.refl ℝ ℂ⟩
  refine ⟨P, 0, 1, ?_⟩
  norm_num [annularActual, realize, P]

end Reg.D5.S3.Topology.AnnularSecondZero
