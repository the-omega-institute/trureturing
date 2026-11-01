import D5.S3.FiniteGroups.FrattiniAutomorphismKernel
import Reg.Support.DependentFamily

/-! Full source reconstruction and the boundary of the parameter-only audit realization. -/

namespace Reg.D5.S3.FiniteGroups.FrattiniAutomorphismKernel
open _root_.D5.S3.FiniteGroups.FrattiniAutomorphismKernel
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
universe u

structure SourceParams where
  Carrier : Type u
  group : Group Carrier
  finite : Finite Carrier
  p : ℕ
  pgroup : letI := group; IsPGroup p Carrier

attribute [instance] SourceParams.group SourceParams.finite

abbrev signature : Signature where
  Params := SourceParams.{u}
  State _ := Unit
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ M := Subgroup (MulAut M.Carrier)
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature.{u} := realize signature
  (fun _ M _ => (quotientAut (frattini M.Carrier)).ker) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ M, IsPGroup M.p (R.readout () M ())

theorem original_reconstruction :
    (type_of% (@isPGroup_quotientAut_frattini_kernel.{u})) ↔ arena.{u}.Law actual.{u} := by
  constructor
  · intro h M
    exact h M.pgroup
  · intro h G _ _ p hG
    exact h ⟨G, inferInstance, inferInstance, p, hG⟩

theorem original_positive : arena.{u}.Law actual.{u} :=
  original_reconstruction.{u}.mp (@isPGroup_quotientAut_frattini_kernel.{u})

/-- This source-telescope realization cannot provide the required fourth slot. -/
theorem no_unit_state_dependence : ¬ ObservationalDependence signature.{u} actual.{u} := by
  intro h
  obtain ⟨M, x, y, hxy⟩ := h ()
  exact hxy (by cases x; cases y; rfl)

example : IsPGroup 2 PUnit := IsPGroup.of_subsingleton 2 PUnit
example : PUnit := 1
example : IsPGroup 2 (quotientAut (frattini PUnit)).ker :=
  isPGroup_quotientAut_frattini_kernel (IsPGroup.of_subsingleton 2 PUnit)

end Reg.D5.S3.FiniteGroups.FrattiniAutomorphismKernel
