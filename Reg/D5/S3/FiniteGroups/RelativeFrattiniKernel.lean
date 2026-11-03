import D5.S3.FiniteGroups.RelativeFrattiniKernel
import Reg.Support.DependentFamily

/-! Full source telescopes and the observational boundary of parameter-only realizations. -/

namespace Reg.D5.S3.FiniteGroups.RelativeFrattiniKernel
open _root_.D5.S3.FiniteGroups.RelativeFrattiniKernel
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
universe u

structure SourceParams where
  Carrier : Type u
  group : Group Carrier
  finite : Finite Carrier
  P : letI := group; Subgroup Carrier
  normal : letI := group; P.Normal
  p : ℕ
  pgroup : letI := group; IsPGroup p P

attribute [instance] SourceParams.group SourceParams.finite SourceParams.normal

abbrev automorphismSignature : Signature where
  Params := SourceParams.{u}
  State _ := Unit
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ M := Subgroup (preservingAut M.P)
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def automorphismActual : Realization automorphismSignature.{u} :=
  realize automorphismSignature (fun _ M _ => (quotientAction M.P).ker) (fun e => nomatch e)

abbrev automorphismArena : Arena where
  signature := automorphismSignature.{u}
  Law R := ∀ M, IsPGroup M.p (R.readout () M ())

theorem automorphism_reconstruction :
    (type_of% (@isPGroup_automorphism_kernel.{u})) ↔
      automorphismArena.{u}.Law automorphismActual.{u} := by
  constructor
  · intro h M
    exact h M.P M.pgroup
  · intro h Q _ _ P _ p hP
    exact h ⟨Q, inferInstance, inferInstance, P, inferInstance, p, hP⟩

theorem automorphism_positive : automorphismArena.{u}.Law automorphismActual.{u} :=
  automorphism_reconstruction.{u}.mp (@isPGroup_automorphism_kernel.{u})

theorem automorphism_no_unit_dependence :
    ¬ ObservationalDependence automorphismSignature.{u} automorphismActual.{u} := by
  intro h
  obtain ⟨M, x, y, hxy⟩ := h ()
  exact hxy (by cases x; cases y; rfl)

structure OuterParams extends SourceParams where
  H : Subgroup (RelativeOuter P)

abbrev outerSignature : Signature where
  Params := OuterParams.{u}
  State _ := Unit
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ M := Subgroup M.H
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def outerActual : Realization outerSignature.{u} :=
  realize outerSignature (fun _ M _ => ((outerAction M.P).comp M.H.subtype).ker)
    (fun e => nomatch e)

abbrev outerArena : Arena where
  signature := outerSignature.{u}
  Law R := ∀ M, IsPGroup M.p (R.readout () M ())

theorem outer_reconstruction :
    (type_of% (@isPGroup_outer_kernel.{u})) ↔ outerArena.{u}.Law outerActual.{u} := by
  constructor
  · intro h M
    exact h M.P M.pgroup M.H
  · intro h Q _ _ P _ p hP H
    exact h ⟨⟨Q, inferInstance, inferInstance, P, inferInstance, p, hP⟩, H⟩

theorem outer_positive : outerArena.{u}.Law outerActual.{u} :=
  outer_reconstruction.{u}.mp (@isPGroup_outer_kernel.{u})

theorem outer_no_unit_dependence :
    ¬ ObservationalDependence outerSignature.{u} outerActual.{u} := by
  intro h
  obtain ⟨M, x, y, hxy⟩ := h ()
  exact hxy (by cases x; cases y; rfl)

end Reg.D5.S3.FiniteGroups.RelativeFrattiniKernel
