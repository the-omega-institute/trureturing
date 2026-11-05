import LeanInformationAuditInterface.Contract.Registration
import D5.S3.HomologicalAlgebra.FinitePerturbationCohomology
import Reg.Support.DependentFamily
import Reg.Support.SourceSelection
import Mathlib.Algebra.Module.ULift

/- Source preparation only: no compiler, reconstruction judge or acceptance was run.
The three original theorem telescopes are retained in the laws below. Only finite
roles and empty anchors are used; no original module or quotient is made finite. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.HomologicalAlgebra.FinitePerturbation
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.HomologicalAlgebra.FinitePerturbationCohomology
universe u v w

structure Parameters where
  R : Type u
  U : Type v
  V : Type w
  ring : CommRing R
  groupU : AddCommGroup U
  moduleU : @Module R U ring.toSemiring groupU.toAddCommMonoid
  groupV : AddCommGroup V
  moduleV : @Module R V ring.toSemiring groupV.toAddCommMonoid
  input : @Input R U V ring groupU moduleU groupV moduleV

attribute [instance] Parameters.ring Parameters.groupU Parameters.moduleU
  Parameters.groupV Parameters.moduleV

private def liftedRingHom : ULift.{u} ℤ →+* ℤ := ULift.ringEquiv.toRingHom

-- The accepted HPL Reg sample.{u,v,w}, at the original arbitrary universe levels.
private def sample : Parameters.{u,v,w} := by
  let R := ULift.{u} ℤ
  let U := ULift.{v} ℤ
  let V := ULift.{w} ℤ
  letI : Module R U := Module.compHom U liftedRingHom
  letI : Module R V := Module.compHom V liftedRingHom
  let i : U →ₗ[R] V := {
    toFun := fun x => ⟨x.down⟩
    map_add' := by intro x y; rfl
    map_smul' := by intro r x; rfl }
  let p : V →ₗ[R] U := {
    toFun := fun x => ⟨x.down⟩
    map_add' := by intro x y; rfl
    map_smul' := by intro r x; rfl }
  let c : Input (R := R) (U := U) (V := V) := {
    d0 := 0, h := 0, delta := 0, i := i, p := p
    d0_sq := by simp
    pi := by ext x; rfl
    di := by simp
    pd := by simp
    contraction := by
      ext x
      change (0 : ℤ) = x.down - x.down
      simp
    hh := by simp
    hi := by simp
    ph := by simp
    perturbed_sq := by simp }
  exact ⟨R,U,V,inferInstance,inferInstance,inferInstance,inferInstance,inferInstance,c⟩

private theorem sample_nilpotent :
    (sample.{u,v,w}.input.h * sample.{u,v,w}.input.delta)^1 = 0 := by
  ext x
  rfl

private theorem sample_D : sample.{u,v,w}.input.D = 0 := by
  ext x
  rfl

namespace Boundary

abbrev signature : Signature where
  Params := Parameters.{u,v,w}
  State p := p.V
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u,v,w} := realize signature
  (fun _ p x => ∃ y : p.V, p.input.D y = x) (fun e => nomatch e)

def rejected : Realization signature.{u,v,w} := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u,v,w}
  Law r := ∀ {R : Type u} {U : Type v} {V : Type w} [CommRing R]
    [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V]
    (c : Input (R := R) (U := U) (V := V)) (n : ℕ) (hn : 1 ≤ n)
    (nilpotent : (c.h * c.delta)^n = 0) (x : V) (hx : c.D x = 0),
    r.readout () ⟨R,U,V,inferInstance,inferInstance,inferInstance,
      inferInstance,inferInstance,c⟩ x ↔
      ∃ u : U, c.transferred n u = c.P n x

theorem actual_law : arena.Law actual.{u,v,w} := by
  intro R U V _ _ _ _ _ c n hn nilpotent x hx
  exact c.boundary_iff_transferred_boundary n hn nilpotent x hx

theorem rejected_law : ¬ arena.Law rejected.{u,v,w} := by
  intro law
  have h := law sample.{u,v,w}.input 1 (by decide) sample_nilpotent.{u,v,w} 0 (map_zero _)
  exact h.mpr ⟨0, by simp⟩

theorem dependence : ObservationalDependence signature.{u,v,w} actual := by
  intro role
  refine ⟨sample.{u,v,w}, 0, (show sample.{u,v,w}.V from ⟨1⟩), ?_⟩
  change (∃ y : sample.{u,v,w}.V, sample.{u,v,w}.input.D y = 0) ≠
    (∃ y : sample.{u,v,w}.V, sample.{u,v,w}.input.D y = (show sample.{u,v,w}.V from ⟨1⟩))
  intro h
  obtain ⟨y, hy⟩ := h.mp ⟨0, map_zero _⟩
  have hzero : (0 : sample.{u,v,w}.V) = ⟨1⟩ := by simpa [sample_D.{u,v,w}, map_zero, sub_zero] using hy
  exact zero_ne_one (congrArg ULift.down hzero)

def source_registration : Registration arena.{u,v,w} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      exact ⟨rejected, fun other hne => (hne (Subsingleton.elim other role)).elim,
        rfl, rejected_law⟩
    · intro e; exact nomatch e
  dependence := dependence

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.HomologicalAlgebra.FinitePerturbation.Input.boundary_iff_transferred_boundary.{u,v,w})
    (type_of% (realize signature.{u,v,w}
      (fun _ p x => ∃ y : p.V, p.input.D y = x) (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.HomologicalAlgebra.FinitePerturbationCohomology.boundary_iff_transferred_boundary
  realizationName := `Reg.D5.S3.HomologicalAlgebra.FinitePerturbationCohomology.Boundary.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v,w}⟩
  objectArena := .source ⟨arena.{u,v,w}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v,w} ⟨source_registration.{u,v,w}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u,v,w}
    (fun _ p x => ∃ y : p.V, p.input.D y = x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.HomologicalAlgebra.FinitePerturbationCohomology
    definition := none
    coordinates := #[0,1,2,3,4,5,6,7,8]
    readouts := #[{
      path := #["body","body","body","body","body","body","body",
        "body","body","body","body","body","body","body","fn","arg"]
      stateBinder := 12
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Boundary

structure QuotientParameters where
  base : Parameters.{u,v,w}
  n : ℕ
  hn : 1 ≤ n
  nilpotent : (base.input.h * base.input.delta)^n = 0

private def quotientSample : QuotientParameters.{u,v,w} :=
  ⟨sample.{u,v,w}, 1, by decide, sample_nilpotent.{u,v,w}⟩

private theorem sample_transferred : sample.{u,v,w}.input.transferred 1 = 0 := by
  ext x
  rfl

-- A mathematical separation in the literal quotient, not a finite truth table.
private theorem quotient_injective_of_zero
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (d : Module.End R M) (square : d * d = 0) (hd : d = 0) :
    Function.Injective (fun x : LinearMap.ker d =>
      (Submodule.Quotient.mk x : Cohomology d square)) := by
  intro x y hxy
  have hmem := (Submodule.Quotient.eq _).mp hxy
  change ∃ z, boundaryMap d square z = x - y at hmem
  obtain ⟨z, hz⟩ := hmem
  have hv := congrArg (fun q : LinearMap.ker d => (q : M)) hz
  change d z = (x : M) - (y : M) at hv
  apply Subtype.ext
  exact sub_eq_zero.mp (by simpa [hd] using hv.symm)


namespace Forward

abbrev signature : Signature where
  Params := QuotientParameters.{u,v,w}
  State p := LinearMap.ker (p.base.input.D)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Cohomology (p.base.input.D) (p.base.input.perturbed_sq)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u,v,w} := realize signature
  (fun _ p x => (Submodule.Quotient.mk x : Cohomology (p.base.input.D) (p.base.input.perturbed_sq))) (fun e => nomatch e)
def rejected : Realization signature.{u,v,w} := realize signature
  (fun _ _ _ => 0) (fun e => nomatch e)

-- Only the existing input quotient constructor is replaced. The equivalence,
-- representative, chain proof and all hypotheses stay in their original scopes.
abbrev arena : Arena where
  signature := signature.{u,v,w}
  Law r := ∀ {R : Type u} {U : Type v} {V : Type w} [CommRing R]
    [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V]
    (c : Input (R := R) (U := U) (V := V)) (n : ℕ) (hn : 1 ≤ n)
    (nilpotent : (c.h * c.delta) ^ n = 0) (x : V) (hx : c.D x = 0),
    c.cohomologyEquiv n hn nilpotent ((r.readout () ⟨⟨R,U,V,inferInstance,inferInstance,inferInstance,inferInstance,inferInstance,c⟩,n,hn,nilpotent⟩ ⟨x,hx⟩)) =
      Submodule.Quotient.mk
        (⟨c.P n x, by
          have eq := DFunLike.congr_fun
            (c.finite_perturbation n hn nilpotent).projection_chain x
          simpa [hx] using eq.symm⟩ : LinearMap.ker (c.transferred n))

theorem actual_law : arena.Law actual.{u,v,w} := by
  intro R U V _ _ _ _ _ c n hn nilpotent x hx
  exact c.cohomologyEquiv_mk n hn nilpotent x hx

private def zeroCycle : signature.{u,v,w}.State quotientSample := ⟨0, map_zero _⟩
private def oneCycle : signature.{u,v,w}.State quotientSample :=
  ⟨(show sample.{u,v,w}.V from ⟨1⟩), by
    change (sample.{u,v,w}.input.D) _ = 0
    rw [sample_D.{u,v,w}]
    rfl⟩

private theorem quotient_distinct :
    actual.{u,v,w}.readout () quotientSample zeroCycle ≠
      actual.readout () quotientSample oneCycle := by
  intro h
  have he := quotient_injective_of_zero (sample.{u,v,w}.input.D) (sample.{u,v,w}.input.perturbed_sq) sample_D.{u,v,w} h
  exact zero_ne_one (congrArg (fun x : LinearMap.ker (sample.{u,v,w}.input.D) =>
    (x : sample.{u,v,w}.V).down) he)

theorem dependence : ObservationalDependence signature.{u,v,w} actual := by
  intro role
  exact ⟨quotientSample, zeroCycle, oneCycle, quotient_distinct⟩

theorem rejected_law : ¬ arena.Law rejected.{u,v,w} := by
  intro law
  have hb := law sample.{u,v,w}.input 1 (by decide) sample_nilpotent.{u,v,w}
    (show sample.{u,v,w}.V from ⟨1⟩) oneCycle.property
  have ha := sample.{u,v,w}.input.cohomologyEquiv_mk 1 (by decide) sample_nilpotent.{u,v,w}
    (show sample.{u,v,w}.V from ⟨1⟩) oneCycle.property
  have he : (sample.{u,v,w}.input.cohomologyEquiv 1 (by decide) sample_nilpotent.{u,v,w}) (Submodule.Quotient.mk oneCycle) =
      (sample.{u,v,w}.input.cohomologyEquiv 1 (by decide) sample_nilpotent.{u,v,w}) (0 : Cohomology (sample.{u,v,w}.input.D) (sample.{u,v,w}.input.perturbed_sq)) := ha.trans hb.symm
  have bad := (sample.{u,v,w}.input.cohomologyEquiv 1 (by decide) sample_nilpotent.{u,v,w}).injective he
  exact quotient_distinct bad.symm

def source_registration : Registration arena.{u,v,w} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      exact ⟨rejected, fun other hne => (hne (Subsingleton.elim other role)).elim,
        rfl, rejected_law⟩
    · intro e; exact nomatch e
  dependence := dependence

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.HomologicalAlgebra.FinitePerturbation.Input.cohomologyEquiv_mk.{u,v,w})
    (type_of% (realize signature.{u,v,w} (fun _ p x => (Submodule.Quotient.mk x : Cohomology (p.base.input.D) (p.base.input.perturbed_sq)))
      (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.HomologicalAlgebra.FinitePerturbationCohomology.cohomologyEquiv_mk
  realizationName := `Reg.D5.S3.HomologicalAlgebra.FinitePerturbationCohomology.Forward.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v,w}⟩
  objectArena := .source ⟨arena.{u,v,w}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v,w} ⟨source_registration.{u,v,w}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u,v,w} (fun _ p x => (Submodule.Quotient.mk x : Cohomology (p.base.input.D) (p.base.input.perturbed_sq))) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.HomologicalAlgebra.FinitePerturbationCohomology
    definition := none
    coordinates := #[0,1,2,3,4,5,6,7,8,9,10,11]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body","body","body","body","body","fn","arg","arg","fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Forward


namespace Inverse

abbrev signature : Signature where
  Params := QuotientParameters.{u,v,w}
  State p := LinearMap.ker (p.base.input.transferred p.n)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Cohomology (p.base.input.transferred p.n) ((p.base.input.finite_perturbation p.n p.hn p.nilpotent).transferred_sq)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u,v,w} := realize signature
  (fun _ p x => (Submodule.Quotient.mk x : Cohomology (p.base.input.transferred p.n) ((p.base.input.finite_perturbation p.n p.hn p.nilpotent).transferred_sq))) (fun e => nomatch e)
def rejected : Realization signature.{u,v,w} := realize signature
  (fun _ _ _ => 0) (fun e => nomatch e)

-- Only the existing input quotient constructor is replaced. The equivalence,
-- representative, chain proof and all hypotheses stay in their original scopes.
abbrev arena : Arena where
  signature := signature.{u,v,w}
  Law r := ∀ {R : Type u} {U : Type v} {V : Type w} [CommRing R]
    [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V]
    (c : Input (R := R) (U := U) (V := V)) (n : ℕ) (hn : 1 ≤ n)
    (nilpotent : (c.h * c.delta) ^ n = 0) (u : U) (hu : c.transferred n u = 0),
    (c.cohomologyEquiv n hn nilpotent).symm
        ((r.readout () ⟨⟨R,U,V,inferInstance,inferInstance,inferInstance,inferInstance,inferInstance,c⟩,n,hn,nilpotent⟩ ⟨u,hu⟩)) =
      Submodule.Quotient.mk
        (⟨c.I n u, by
          have eq := DFunLike.congr_fun
            (c.finite_perturbation n hn nilpotent).inclusion_chain u
          simpa [hu] using eq⟩ : LinearMap.ker c.D)

theorem actual_law : arena.Law actual.{u,v,w} := by
  intro R U V _ _ _ _ _ c n hn nilpotent u hu
  exact c.cohomologyEquiv_symm_mk n hn nilpotent u hu

private def zeroCycle : signature.{u,v,w}.State quotientSample := ⟨0, map_zero _⟩
private def oneCycle : signature.{u,v,w}.State quotientSample :=
  ⟨(show sample.{u,v,w}.U from ⟨1⟩), by
    change (sample.{u,v,w}.input.transferred 1) _ = 0
    rw [sample_transferred.{u,v,w}]
    rfl⟩

private theorem quotient_distinct :
    actual.{u,v,w}.readout () quotientSample zeroCycle ≠
      actual.readout () quotientSample oneCycle := by
  intro h
  have he := quotient_injective_of_zero (sample.{u,v,w}.input.transferred 1) ((sample.{u,v,w}.input.finite_perturbation 1 (by decide) sample_nilpotent.{u,v,w}).transferred_sq) sample_transferred.{u,v,w} h
  exact zero_ne_one (congrArg (fun x : LinearMap.ker (sample.{u,v,w}.input.transferred 1) =>
    (x : sample.{u,v,w}.U).down) he)

theorem dependence : ObservationalDependence signature.{u,v,w} actual := by
  intro role
  exact ⟨quotientSample, zeroCycle, oneCycle, quotient_distinct⟩

theorem rejected_law : ¬ arena.Law rejected.{u,v,w} := by
  intro law
  have hb := law sample.{u,v,w}.input 1 (by decide) sample_nilpotent.{u,v,w}
    (show sample.{u,v,w}.U from ⟨1⟩) oneCycle.property
  have ha := sample.{u,v,w}.input.cohomologyEquiv_symm_mk 1 (by decide) sample_nilpotent.{u,v,w}
    (show sample.{u,v,w}.U from ⟨1⟩) oneCycle.property
  have he : (sample.{u,v,w}.input.cohomologyEquiv 1 (by decide) sample_nilpotent.{u,v,w}).symm (Submodule.Quotient.mk oneCycle) =
      (sample.{u,v,w}.input.cohomologyEquiv 1 (by decide) sample_nilpotent.{u,v,w}).symm (0 : Cohomology (sample.{u,v,w}.input.transferred 1) ((sample.{u,v,w}.input.finite_perturbation 1 (by decide) sample_nilpotent.{u,v,w}).transferred_sq)) := ha.trans hb.symm
  have bad := (sample.{u,v,w}.input.cohomologyEquiv 1 (by decide) sample_nilpotent.{u,v,w}).symm.injective he
  exact quotient_distinct bad.symm

def source_registration : Registration arena.{u,v,w} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      exact ⟨rejected, fun other hne => (hne (Subsingleton.elim other role)).elim,
        rfl, rejected_law⟩
    · intro e; exact nomatch e
  dependence := dependence

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.HomologicalAlgebra.FinitePerturbation.Input.cohomologyEquiv_symm_mk.{u,v,w})
    (type_of% (realize signature.{u,v,w} (fun _ p x => (Submodule.Quotient.mk x : Cohomology (p.base.input.transferred p.n) ((p.base.input.finite_perturbation p.n p.hn p.nilpotent).transferred_sq)))
      (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.HomologicalAlgebra.FinitePerturbationCohomology.cohomologyEquiv_symm_mk
  realizationName := `Reg.D5.S3.HomologicalAlgebra.FinitePerturbationCohomology.Inverse.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v,w}⟩
  objectArena := .source ⟨arena.{u,v,w}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v,w} ⟨source_registration.{u,v,w}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u,v,w} (fun _ p x => (Submodule.Quotient.mk x : Cohomology (p.base.input.transferred p.n) ((p.base.input.finite_perturbation p.n p.hn p.nilpotent).transferred_sq))) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.HomologicalAlgebra.FinitePerturbationCohomology
    definition := none
    coordinates := #[0,1,2,3,4,5,6,7,8,9,10,11]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body","body","body","body","body","fn","arg","arg","fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Inverse


end Reg.D5.S3.HomologicalAlgebra.FinitePerturbationCohomology
