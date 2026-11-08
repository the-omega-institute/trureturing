import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Analytic.BanachGeometry.LeftUnitalAbsoluteValued

/-! Faithful source reconstruction for the arbitrary real Banach multiplier
theorem. Whole-family variation, sensitivity, observational dependence and the
source selector are not supplied. No validated registration is asserted.
The unfinished audit is linked to issue 28177. -/

noncomputable section
namespace Reg.D5.S3.Analytic.BanachGeometry.LeftUnitalAbsoluteValued

open _root_.D5.S3.Analytic.BanachGeometry.LeftUnitalAbsoluteValued
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

universe u

abbrev sourceScope := type_of% (@exists_left_multiplier_equiv.{u})

structure Inputs where
  E : Type u
  groupE : NormedAddCommGroup E
  spaceE : letI := groupE; NormedSpace ℝ E
  completeE : letI := groupE; CompleteSpace E
  nontrivialE : Nontrivial E

attribute [instance] Inputs.groupE Inputs.spaceE Inputs.completeE Inputs.nontrivialE

structure SourceState (P : Inputs.{u}) where
  m : P.E →ₗ[ℝ] P.E →ₗ[ℝ] P.E
  multiplicative : ∀ x y : P.E, ‖m x y‖ = ‖x‖ * ‖y‖
  e : P.E
  leftUnit : ∀ y : P.E, m e y = y
  x : P.E
  nonzero : x ≠ 0

abbrev signature : Signature where
  Params := Inputs.{u}
  State := SourceState
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ P => P.E →ₗ[ℝ] P.E
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ st => st.m st.x) (fun a => nomatch a)

def arena : Arena where
  signature := signature.{u}
  Law := fun r => ∀ P st, ∃ T : P.E ≃L[ℝ] P.E,
    (∀ y : P.E, T y = r.readout () P st y) ∧
    ‖(T : P.E →L[ℝ] P.E)‖ = ‖st.x‖ ∧
    ‖(T.symm : P.E →L[ℝ] P.E)‖ = ‖st.x‖⁻¹

theorem source_bridge : sourceScope.{u} ↔ arena.{u}.Law actual.{u} := by
  constructor
  · intro h P st
    exact h st.m st.multiplicative st.e st.leftUnit st.x st.nonzero
  · intro h E groupE spaceE completeE nontrivialE m hm e he x hx
    let P : Inputs.{u} := ⟨E, groupE, spaceE, completeE, nontrivialE⟩
    exact h P ⟨m, hm, e, he, x, hx⟩

theorem actual_positive : arena.{u}.Law actual.{u} :=
  source_bridge.mp (@exists_left_multiplier_equiv.{u})

#print axioms source_bridge
#print axioms actual_positive

end Reg.D5.S3.Analytic.BanachGeometry.LeftUnitalAbsoluteValued
