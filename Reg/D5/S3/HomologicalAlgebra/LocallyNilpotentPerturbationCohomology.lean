import LeanInformationAuditInterface.Contract.Registration
import D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbationCohomology
import Reg.Support.DependentFamily
import Reg.Support.SourceSelection
import Mathlib.Algebra.Module.ULift

/- Uncompiled source preparation. All six public targets of this module are
included, including the two separately source-authored descent readouts. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.HomologicalAlgebra.FinitePerturbation
open _root_.D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbation
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbationCohomology
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


structure LocalParameters where
  base : Parameters.{u,v,w}
  nilpotent : ∀ x : base.V, ∃ n : ℕ, ((base.input.h * base.input.delta)^n) x = 0

private theorem sample_locally_nilpotent :
    ∀ x : sample.{u,v,w}.V, ∃ n : ℕ, ((sample.{u,v,w}.input.h * sample.{u,v,w}.input.delta)^n) x = 0 := by
  intro x
  exact ⟨1, DFunLike.congr_fun sample_nilpotent.{u,v,w} x⟩

private def localSample : LocalParameters.{u,v,w} := ⟨sample.{u,v,w}, sample_locally_nilpotent.{u,v,w}⟩

private theorem sample_transferred :
    transferred sample.{u,v,w}.input sample_locally_nilpotent.{u,v,w} = 0 := by
  ext x
  rfl

private theorem sample_P (x : sample.{u,v,w}.V) :
    (P sample.{u,v,w}.input sample_locally_nilpotent.{u,v,w} x).down = x.down := by
  change ((1 - 0 * K sample.{u,v,w}.input sample_locally_nilpotent.{u,v,w} * 0) x).down = x.down
  simp only [zero_mul, sub_zero]
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



namespace Primitive
abbrev signature : Signature where
  Params := LocalParameters.{u,v,w}
  State p := p.base.V
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.base.U
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u,v,w} := realize signature
  (fun _ p x => P p.base.input p.nilpotent x) (fun e => nomatch e)
def rejected : Realization signature.{u,v,w} := realize signature
  (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u,v,w}
  Law r := ∀ {R : Type u} {U : Type v} {V : Type w} [CommRing R]
    [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V]
    (c : Input (R := R) (U := U) (V := V))
    (nilpotent : ∀ x : V, ∃ n : ℕ, ((c.h * c.delta)^n) x = 0) (x : V) (hx : c.D x = 0),
    c.D (H c nilpotent x) = x - I c nilpotent ((r.readout () ⟨⟨R,U,V,inferInstance,inferInstance,inferInstance,inferInstance,inferInstance,c⟩,nilpotent⟩ x))

theorem actual_law : arena.Law actual.{u,v,w} := by
  intro R U V _ _ _ _ _ c nilpotent x hx
  exact cycle_primitive c nilpotent x hx

theorem rejected_law : ¬ arena.Law rejected.{u,v,w} := by
  intro law
  have h := law sample.{u,v,w}.input sample_locally_nilpotent.{u,v,w}
    (show sample.{u,v,w}.V from ⟨1⟩) (by rw [sample_D.{u,v,w}]; rfl)
  change sample.{u,v,w}.input.D (H sample.{u,v,w}.input sample_locally_nilpotent.{u,v,w} (show sample.{u,v,w}.V from ⟨1⟩)) =
    (show sample.{u,v,w}.V from ⟨1⟩) - I sample.{u,v,w}.input sample_locally_nilpotent.{u,v,w} (0 : sample.{u,v,w}.U) at h
  rw [map_zero, sub_zero] at h
  change (0 : sample.{u,v,w}.V) = ⟨1⟩ at h
  exact zero_ne_one (congrArg ULift.down h)

theorem dependence : ObservationalDependence signature.{u,v,w} actual := by
  intro role
  refine ⟨localSample.{u,v,w}, 0, (show sample.{u,v,w}.V from ⟨1⟩), ?_⟩
  change P sample.{u,v,w}.input sample_locally_nilpotent.{u,v,w} 0 ≠
    P sample.{u,v,w}.input sample_locally_nilpotent.{u,v,w} (show sample.{u,v,w}.V from ⟨1⟩)
  intro h
  have hd := congrArg ULift.down h
  simp only [sample_P.{u,v,w}] at hd
  exact zero_ne_one hd

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
    (@_root_.D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbation.cycle_primitive.{u,v,w})
    (type_of% (realize signature.{u,v,w} (fun _ p x => P p.base.input p.nilpotent x)
      (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbationCohomology.cycle_primitive
  realizationName := `Reg.D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbationCohomology.Primitive.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v,w}⟩
  objectArena := .source ⟨arena.{u,v,w}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v,w} ⟨source_registration.{u,v,w}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u,v,w} (fun _ p x => P p.base.input p.nilpotent x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbationCohomology
    definition := none
    coordinates := #[0,1,2,3,4,5,6,7,8,9]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body","body","body","arg","arg","arg"]
      stateBinder := 10
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Primitive

namespace Boundary
abbrev signature : Signature where
  Params := LocalParameters.{u,v,w}
  State p := p.base.V
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u,v,w} := realize signature
  (fun _ p x => ∃ y : p.base.V, p.base.input.D y = x) (fun e => nomatch e)
def rejected : Realization signature.{u,v,w} := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u,v,w}
  Law r := ∀ {R : Type u} {U : Type v} {V : Type w} [CommRing R]
    [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V]
    (c : Input (R := R) (U := U) (V := V))
    (nilpotent : ∀ x : V, ∃ n : ℕ, ((c.h * c.delta)^n) x = 0) (x : V) (hx : c.D x = 0),
    (r.readout () ⟨⟨R,U,V,inferInstance,inferInstance,inferInstance,inferInstance,inferInstance,c⟩,nilpotent⟩ x) ↔
      ∃ u : U, transferred c nilpotent u = P c nilpotent x

theorem actual_law : arena.Law actual.{u,v,w} := by
  intro R U V _ _ _ _ _ c nilpotent x hx
  exact boundary_iff_transferred_boundary c nilpotent x hx

theorem rejected_law : ¬ arena.Law rejected.{u,v,w} := by
  intro law
  have h := law sample.{u,v,w}.input sample_locally_nilpotent.{u,v,w} 0 (map_zero _)
  exact h.mpr ⟨0, by simp⟩

theorem dependence : ObservationalDependence signature.{u,v,w} actual := by
  intro role
  refine ⟨localSample.{u,v,w}, 0, (show sample.{u,v,w}.V from ⟨1⟩), ?_⟩
  change (∃ y : sample.{u,v,w}.V, sample.{u,v,w}.input.D y = 0) ≠
    (∃ y : sample.{u,v,w}.V, sample.{u,v,w}.input.D y = (show sample.{u,v,w}.V from ⟨1⟩))
  intro h
  obtain ⟨y, hy⟩ := h.mp ⟨0, map_zero _⟩
  have hz : (0 : sample.{u,v,w}.V) = ⟨1⟩ := by simpa [sample_D.{u,v,w}, map_zero, sub_zero] using hy
  exact zero_ne_one (congrArg ULift.down hz)

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
    (@_root_.D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbation.boundary_iff_transferred_boundary.{u,v,w})
    (type_of% (realize signature.{u,v,w} (fun _ p x => ∃ y : p.base.V, p.base.input.D y = x)
      (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbationCohomology.boundary_iff_transferred_boundary
  realizationName := `Reg.D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbationCohomology.Boundary.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v,w}⟩
  objectArena := .source ⟨arena.{u,v,w}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v,w} ⟨source_registration.{u,v,w}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u,v,w} (fun _ p x => ∃ y : p.base.V, p.base.input.D y = x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbationCohomology
    definition := none
    coordinates := #[0,1,2,3,4,5,6,7,8,9]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body","body","body","fn","arg"]
      stateBinder := 10
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Boundary

namespace Projection

abbrev signature : Signature where
  Params := LocalParameters.{u,v,w}
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

-- The original quotient-constructor function operand is the single observation.
abbrev arena : Arena where
  signature := signature.{u,v,w}
  Law r := ∀ {R : Type u} {U : Type v} {V : Type w} [CommRing R]
    [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V]
    (c : Input (R := R) (U := U) (V := V))
    (nilpotent : ∀ x : V, ∃ n : ℕ, ((c.h * c.delta)^n) x = 0) (x : LinearMap.ker c.D),
    cohomologyProjection c nilpotent ((r.readout () ⟨⟨R,U,V,inferInstance,inferInstance,inferInstance,inferInstance,inferInstance,c⟩,nilpotent⟩ x)) =
      Submodule.Quotient.mk
        (⟨P c nilpotent (x : V), by
          have hx : c.D (x : V) = 0 := x.property
          have eq := DFunLike.congr_fun
            (locally_nilpotent_perturbation c nilpotent).2.2.1 (x : V)
          simpa [hx] using eq.symm⟩ :
            LinearMap.ker (transferred c nilpotent))

theorem actual_law : arena.Law actual.{u,v,w} := by
  intro R U V _ _ _ _ _ c nilpotent x
  exact cohomologyProjection_mk c nilpotent x

private def zeroCycle : signature.{u,v,w}.State localSample.{u,v,w} := ⟨0, map_zero _⟩
private def oneCycle : signature.{u,v,w}.State localSample.{u,v,w} :=
  ⟨(show sample.{u,v,w}.V from ⟨1⟩), by
    change (sample.{u,v,w}.input.D) _ = 0
    rw [sample_D.{u,v,w}]
    rfl⟩

private theorem quotient_distinct :
    actual.{u,v,w}.readout () localSample.{u,v,w} zeroCycle ≠
      actual.readout () localSample.{u,v,w} oneCycle := by
  intro h
  have he := quotient_injective_of_zero (sample.{u,v,w}.input.D) (sample.{u,v,w}.input.perturbed_sq) sample_D.{u,v,w} h
  exact zero_ne_one (congrArg (fun x : LinearMap.ker (sample.{u,v,w}.input.D) =>
    (x : sample.{u,v,w}.V).down) he)

theorem dependence : ObservationalDependence signature.{u,v,w} actual := by
  intro role
  exact ⟨localSample.{u,v,w}, zeroCycle, oneCycle, quotient_distinct⟩

theorem rejected_law : ¬ arena.Law rejected.{u,v,w} := by
  intro law
  have hb := law sample.{u,v,w}.input sample_locally_nilpotent.{u,v,w} oneCycle
  have ha := cohomologyProjection_mk sample.{u,v,w}.input sample_locally_nilpotent.{u,v,w} oneCycle
  have he : (cohomologyEquiv sample.{u,v,w}.input sample_locally_nilpotent.{u,v,w}) (Submodule.Quotient.mk oneCycle) =
      (cohomologyEquiv sample.{u,v,w}.input sample_locally_nilpotent.{u,v,w}) (0 : Cohomology (sample.{u,v,w}.input.D) (sample.{u,v,w}.input.perturbed_sq)) := ha.trans hb.symm
  have bad := (cohomologyEquiv sample.{u,v,w}.input sample_locally_nilpotent.{u,v,w}).injective he
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
    (@_root_.D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbation.cohomologyProjection_mk.{u,v,w})
    (type_of% (realize signature.{u,v,w} (fun _ p x => (Submodule.Quotient.mk x : Cohomology (p.base.input.D) (p.base.input.perturbed_sq)))
      (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbationCohomology.cohomologyProjection_mk
  realizationName := `Reg.D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbationCohomology.Projection.source_registration
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
    owner := `D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbationCohomology
    definition := none
    coordinates := #[0,1,2,3,4,5,6,7,8,9]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body","body","fn","arg","arg","fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Projection

namespace Inclusion

abbrev signature : Signature where
  Params := LocalParameters.{u,v,w}
  State p := LinearMap.ker (transferred p.base.input p.nilpotent)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Cohomology (transferred p.base.input p.nilpotent) ((locally_nilpotent_perturbation p.base.input p.nilpotent).1)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u,v,w} := realize signature
  (fun _ p x => (Submodule.Quotient.mk x : Cohomology (transferred p.base.input p.nilpotent) ((locally_nilpotent_perturbation p.base.input p.nilpotent).1))) (fun e => nomatch e)
def rejected : Realization signature.{u,v,w} := realize signature
  (fun _ _ _ => 0) (fun e => nomatch e)

-- The original quotient-constructor function operand is the single observation.
abbrev arena : Arena where
  signature := signature.{u,v,w}
  Law r := ∀ {R : Type u} {U : Type v} {V : Type w} [CommRing R]
    [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V]
    (c : Input (R := R) (U := U) (V := V))
    (nilpotent : ∀ x : V, ∃ n : ℕ, ((c.h * c.delta)^n) x = 0) (u : LinearMap.ker (transferred c nilpotent)),
    cohomologyInclusion c nilpotent ((r.readout () ⟨⟨R,U,V,inferInstance,inferInstance,inferInstance,inferInstance,inferInstance,c⟩,nilpotent⟩ u)) =
      Submodule.Quotient.mk
        (⟨I c nilpotent (u : U), by
          have hu : transferred c nilpotent (u : U) = 0 := u.property
          have eq := DFunLike.congr_fun
            (locally_nilpotent_perturbation c nilpotent).2.1 (u : U)
          simpa [hu] using eq⟩ : LinearMap.ker c.D)

theorem actual_law : arena.Law actual.{u,v,w} := by
  intro R U V _ _ _ _ _ c nilpotent u
  exact cohomologyInclusion_mk c nilpotent u

private def zeroCycle : signature.{u,v,w}.State localSample.{u,v,w} := ⟨0, map_zero _⟩
private def oneCycle : signature.{u,v,w}.State localSample.{u,v,w} :=
  ⟨(show sample.{u,v,w}.U from ⟨1⟩), by
    change (transferred sample.{u,v,w}.input sample_locally_nilpotent.{u,v,w}) _ = 0
    rw [sample_transferred.{u,v,w}]
    rfl⟩

private theorem quotient_distinct :
    actual.{u,v,w}.readout () localSample.{u,v,w} zeroCycle ≠
      actual.readout () localSample.{u,v,w} oneCycle := by
  intro h
  have he := quotient_injective_of_zero (transferred sample.{u,v,w}.input sample_locally_nilpotent.{u,v,w}) ((locally_nilpotent_perturbation sample.{u,v,w}.input sample_locally_nilpotent.{u,v,w}).1) sample_transferred.{u,v,w} h
  exact zero_ne_one (congrArg (fun x : LinearMap.ker (transferred sample.{u,v,w}.input sample_locally_nilpotent.{u,v,w}) =>
    (x : sample.{u,v,w}.U).down) he)

theorem dependence : ObservationalDependence signature.{u,v,w} actual := by
  intro role
  exact ⟨localSample.{u,v,w}, zeroCycle, oneCycle, quotient_distinct⟩

theorem rejected_law : ¬ arena.Law rejected.{u,v,w} := by
  intro law
  have hb := law sample.{u,v,w}.input sample_locally_nilpotent.{u,v,w} oneCycle
  have ha := cohomologyInclusion_mk sample.{u,v,w}.input sample_locally_nilpotent.{u,v,w} oneCycle
  have he : (cohomologyEquiv sample.{u,v,w}.input sample_locally_nilpotent.{u,v,w}).symm (Submodule.Quotient.mk oneCycle) =
      (cohomologyEquiv sample.{u,v,w}.input sample_locally_nilpotent.{u,v,w}).symm (0 : Cohomology (transferred sample.{u,v,w}.input sample_locally_nilpotent.{u,v,w}) ((locally_nilpotent_perturbation sample.{u,v,w}.input sample_locally_nilpotent.{u,v,w}).1)) := ha.trans hb.symm
  have bad := (cohomologyEquiv sample.{u,v,w}.input sample_locally_nilpotent.{u,v,w}).symm.injective he
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
    (@_root_.D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbation.cohomologyInclusion_mk.{u,v,w})
    (type_of% (realize signature.{u,v,w} (fun _ p x => (Submodule.Quotient.mk x : Cohomology (transferred p.base.input p.nilpotent) ((locally_nilpotent_perturbation p.base.input p.nilpotent).1)))
      (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbationCohomology.cohomologyInclusion_mk
  realizationName := `Reg.D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbationCohomology.Inclusion.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v,w}⟩
  objectArena := .source ⟨arena.{u,v,w}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v,w} ⟨source_registration.{u,v,w}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u,v,w} (fun _ p x => (Submodule.Quotient.mk x : Cohomology (transferred p.base.input p.nilpotent) ((locally_nilpotent_perturbation p.base.input p.nilpotent).1))) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbationCohomology
    definition := none
    coordinates := #[0,1,2,3,4,5,6,7,8,9]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body","body","fn","arg","arg","fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Inclusion

namespace Forward

abbrev signature : Signature where
  Params := LocalParameters.{u,v,w}
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

-- The original quotient-constructor function operand is the single observation.
abbrev arena : Arena where
  signature := signature.{u,v,w}
  Law r := ∀ {R : Type u} {U : Type v} {V : Type w} [CommRing R]
    [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V]
    (c : Input (R := R) (U := U) (V := V))
    (nilpotent : ∀ x : V, ∃ n : ℕ, ((c.h * c.delta)^n) x = 0) (x : V) (hx : c.D x = 0),
    cohomologyEquiv c nilpotent
        ((r.readout () ⟨⟨R,U,V,inferInstance,inferInstance,inferInstance,inferInstance,inferInstance,c⟩,nilpotent⟩ ⟨x,hx⟩)) =
      Submodule.Quotient.mk
        (⟨P c nilpotent x, by
          have eq := DFunLike.congr_fun
            (locally_nilpotent_perturbation c nilpotent).2.2.1 x
          simpa [hx] using eq.symm⟩ :
            LinearMap.ker (transferred c nilpotent))

theorem actual_law : arena.Law actual.{u,v,w} := by
  intro R U V _ _ _ _ _ c nilpotent x hx
  exact cohomologyEquiv_mk c nilpotent x hx

private def zeroCycle : signature.{u,v,w}.State localSample.{u,v,w} := ⟨0, map_zero _⟩
private def oneCycle : signature.{u,v,w}.State localSample.{u,v,w} :=
  ⟨(show sample.{u,v,w}.V from ⟨1⟩), by
    change (sample.{u,v,w}.input.D) _ = 0
    rw [sample_D.{u,v,w}]
    rfl⟩

private theorem quotient_distinct :
    actual.{u,v,w}.readout () localSample.{u,v,w} zeroCycle ≠
      actual.readout () localSample.{u,v,w} oneCycle := by
  intro h
  have he := quotient_injective_of_zero (sample.{u,v,w}.input.D) (sample.{u,v,w}.input.perturbed_sq) sample_D.{u,v,w} h
  exact zero_ne_one (congrArg (fun x : LinearMap.ker (sample.{u,v,w}.input.D) =>
    (x : sample.{u,v,w}.V).down) he)

theorem dependence : ObservationalDependence signature.{u,v,w} actual := by
  intro role
  exact ⟨localSample.{u,v,w}, zeroCycle, oneCycle, quotient_distinct⟩

theorem rejected_law : ¬ arena.Law rejected.{u,v,w} := by
  intro law
  have hb := law sample.{u,v,w}.input sample_locally_nilpotent.{u,v,w} (show sample.{u,v,w}.V from ⟨1⟩) oneCycle.property
  have ha := cohomologyEquiv_mk sample.{u,v,w}.input sample_locally_nilpotent.{u,v,w} (show sample.{u,v,w}.V from ⟨1⟩) oneCycle.property
  have he : (cohomologyEquiv sample.{u,v,w}.input sample_locally_nilpotent.{u,v,w}) (Submodule.Quotient.mk oneCycle) =
      (cohomologyEquiv sample.{u,v,w}.input sample_locally_nilpotent.{u,v,w}) (0 : Cohomology (sample.{u,v,w}.input.D) (sample.{u,v,w}.input.perturbed_sq)) := ha.trans hb.symm
  have bad := (cohomologyEquiv sample.{u,v,w}.input sample_locally_nilpotent.{u,v,w}).injective he
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
    (@_root_.D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbation.cohomologyEquiv_mk.{u,v,w})
    (type_of% (realize signature.{u,v,w} (fun _ p x => (Submodule.Quotient.mk x : Cohomology (p.base.input.D) (p.base.input.perturbed_sq)))
      (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbationCohomology.cohomologyEquiv_mk
  realizationName := `Reg.D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbationCohomology.Forward.source_registration
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
    owner := `D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbationCohomology
    definition := none
    coordinates := #[0,1,2,3,4,5,6,7,8,9]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body","body","body","fn","arg","arg","fn"]
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
  Params := LocalParameters.{u,v,w}
  State p := LinearMap.ker (transferred p.base.input p.nilpotent)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Cohomology (transferred p.base.input p.nilpotent) ((locally_nilpotent_perturbation p.base.input p.nilpotent).1)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u,v,w} := realize signature
  (fun _ p x => (Submodule.Quotient.mk x : Cohomology (transferred p.base.input p.nilpotent) ((locally_nilpotent_perturbation p.base.input p.nilpotent).1))) (fun e => nomatch e)
def rejected : Realization signature.{u,v,w} := realize signature
  (fun _ _ _ => 0) (fun e => nomatch e)

-- The original quotient-constructor function operand is the single observation.
abbrev arena : Arena where
  signature := signature.{u,v,w}
  Law r := ∀ {R : Type u} {U : Type v} {V : Type w} [CommRing R]
    [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V]
    (c : Input (R := R) (U := U) (V := V))
    (nilpotent : ∀ x : V, ∃ n : ℕ, ((c.h * c.delta)^n) x = 0) (u : U)
    (hu : transferred c nilpotent u = 0),
    (cohomologyEquiv c nilpotent).symm
        ((r.readout () ⟨⟨R,U,V,inferInstance,inferInstance,inferInstance,inferInstance,inferInstance,c⟩,nilpotent⟩ ⟨u,hu⟩)) =
      Submodule.Quotient.mk
        (⟨I c nilpotent u, by
          have eq := DFunLike.congr_fun
            (locally_nilpotent_perturbation c nilpotent).2.1 u
          simpa [hu] using eq⟩ : LinearMap.ker c.D)

theorem actual_law : arena.Law actual.{u,v,w} := by
  intro R U V _ _ _ _ _ c nilpotent u hu
  exact cohomologyEquiv_symm_mk c nilpotent u hu

private def zeroCycle : signature.{u,v,w}.State localSample.{u,v,w} := ⟨0, map_zero _⟩
private def oneCycle : signature.{u,v,w}.State localSample.{u,v,w} :=
  ⟨(show sample.{u,v,w}.U from ⟨1⟩), by
    change (transferred sample.{u,v,w}.input sample_locally_nilpotent.{u,v,w}) _ = 0
    rw [sample_transferred.{u,v,w}]
    rfl⟩

private theorem quotient_distinct :
    actual.{u,v,w}.readout () localSample.{u,v,w} zeroCycle ≠
      actual.readout () localSample.{u,v,w} oneCycle := by
  intro h
  have he := quotient_injective_of_zero (transferred sample.{u,v,w}.input sample_locally_nilpotent.{u,v,w}) ((locally_nilpotent_perturbation sample.{u,v,w}.input sample_locally_nilpotent.{u,v,w}).1) sample_transferred.{u,v,w} h
  exact zero_ne_one (congrArg (fun x : LinearMap.ker (transferred sample.{u,v,w}.input sample_locally_nilpotent.{u,v,w}) =>
    (x : sample.{u,v,w}.U).down) he)

theorem dependence : ObservationalDependence signature.{u,v,w} actual := by
  intro role
  exact ⟨localSample.{u,v,w}, zeroCycle, oneCycle, quotient_distinct⟩

theorem rejected_law : ¬ arena.Law rejected.{u,v,w} := by
  intro law
  have hb := law sample.{u,v,w}.input sample_locally_nilpotent.{u,v,w} (show sample.{u,v,w}.U from ⟨1⟩) oneCycle.property
  have ha := cohomologyEquiv_symm_mk sample.{u,v,w}.input sample_locally_nilpotent.{u,v,w} (show sample.{u,v,w}.U from ⟨1⟩) oneCycle.property
  have he : (cohomologyEquiv sample.{u,v,w}.input sample_locally_nilpotent.{u,v,w}).symm (Submodule.Quotient.mk oneCycle) =
      (cohomologyEquiv sample.{u,v,w}.input sample_locally_nilpotent.{u,v,w}).symm (0 : Cohomology (transferred sample.{u,v,w}.input sample_locally_nilpotent.{u,v,w}) ((locally_nilpotent_perturbation sample.{u,v,w}.input sample_locally_nilpotent.{u,v,w}).1)) := ha.trans hb.symm
  have bad := (cohomologyEquiv sample.{u,v,w}.input sample_locally_nilpotent.{u,v,w}).symm.injective he
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
    (@_root_.D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbation.cohomologyEquiv_symm_mk.{u,v,w})
    (type_of% (realize signature.{u,v,w} (fun _ p x => (Submodule.Quotient.mk x : Cohomology (transferred p.base.input p.nilpotent) ((locally_nilpotent_perturbation p.base.input p.nilpotent).1)))
      (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbationCohomology.cohomologyEquiv_symm_mk
  realizationName := `Reg.D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbationCohomology.Inverse.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v,w}⟩
  objectArena := .source ⟨arena.{u,v,w}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v,w} ⟨source_registration.{u,v,w}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u,v,w} (fun _ p x => (Submodule.Quotient.mk x : Cohomology (transferred p.base.input p.nilpotent) ((locally_nilpotent_perturbation p.base.input p.nilpotent).1))) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbationCohomology
    definition := none
    coordinates := #[0,1,2,3,4,5,6,7,8,9]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body","body","body","fn","arg","arg","fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Inverse

end Reg.D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbationCohomology
