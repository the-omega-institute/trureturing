import LeanInformationAuditInterface.Contract.Registration
import D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbation
import Reg.Support.DependentFamily
import Reg.Support.SourceSelection
import Mathlib.Algebra.Module.ULift

/- Source-only client construction. The eight-conjunct perturbation theorem is
explicitly pending below; there is no placeholder registration for it. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.HomologicalAlgebra.FinitePerturbation
open _root_.D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbation
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbation
universe u v w

-- Native binder order here is R,V,instances,U,instances,c, not R,U,V.
structure Parameters where
  R : Type u
  V : Type v
  ring : CommRing R
  groupV : AddCommGroup V
  moduleV : @Module R V ring.toSemiring groupV.toAddCommMonoid
  U : Type w
  groupU : AddCommGroup U
  moduleU : @Module R U ring.toSemiring groupU.toAddCommMonoid
  input : @Input R U V ring groupU moduleU groupV moduleV

attribute [instance] Parameters.ring Parameters.groupU Parameters.moduleU
  Parameters.groupV Parameters.moduleV

private def liftedRingHom : ULift.{u} ℤ →+* ℤ := ULift.ringEquiv.toRingHom

-- The accepted HPL Reg sample, at the original arbitrary universe levels.
private def sample : Parameters.{u,v,w} := by
  let R := ULift.{u} ℤ
  let U := ULift.{w} ℤ
  let V := ULift.{v} ℤ
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
  exact ⟨R,V,inferInstance,inferInstance,inferInstance,U,inferInstance,inferInstance,c⟩

private theorem sample_nilpotent :
    (sample.{u,v,w}.input.h * sample.input.delta)^1 = 0 := by
  ext x
  rfl

private theorem sample_D : sample.{u,v,w}.input.D = 0 := by
  ext x
  rfl


structure UnitParameters where
  R : Type u
  V : Type v
  ring : CommRing R
  groupV : AddCommGroup V
  moduleV : @Module R V ring.toSemiring groupV.toAddCommMonoid

attribute [instance] UnitParameters.ring UnitParameters.groupV UnitParameters.moduleV

private def unitSample : UnitParameters.{u,v} := by
  let p := sample.{u,v,0}
  exact ⟨p.R,p.V,p.ring,p.groupV,p.moduleV⟩

namespace UnitLaw

abbrev signature : Signature where
  Params := UnitParameters.{u,v}
  State p := Module.End p.R p.V
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u,v} := realize signature
  (fun _ _ a => IsUnit (1 + a)) (fun e => nomatch e)
def rejected : Realization signature.{u,v} := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u,v}
  Law r := ∀ {R : Type u} {V : Type v} [CommRing R] [AddCommGroup V] [Module R V]
    (a : Module.End R V) (nilpotent : ∀ x : V, ∃ n : ℕ, (a^n) x = 0),
    r.readout () ⟨R,V,inferInstance,inferInstance,inferInstance⟩ a

theorem actual_law : arena.Law actual.{u,v} := by
  intro R V _ _ _ a nilpotent
  exact isUnit_one_add_of_locally_nilpotent a nilpotent

theorem rejected_law : ¬ arena.Law rejected.{u,v} := by
  intro law
  exact law (R := unitSample.R) (V := unitSample.V) 0
    (fun x => ⟨1, by simp⟩)

theorem dependence : ObservationalDependence signature.{u,v} actual := by
  intro role
  refine ⟨unitSample, 0, -1, ?_⟩
  change IsUnit (1 + (0 : Module.End unitSample.R unitSample.V)) ≠ IsUnit (1 + (-1 : Module.End unitSample.R unitSample.V))
  intro h
  have bad := h.mp (by simp : IsUnit (1 + (0 : Module.End unitSample.R unitSample.V)))
  have inj := ((Module.End.isUnit_iff _).mp bad).1
  have hz : (show unitSample.V from ⟨0⟩) = (show unitSample.V from ⟨1⟩) :=
    inj (by simp)
  exact zero_ne_one (congrArg ULift.down hz)

def source_registration : Registration arena.{u,v} (arena.Law actual) where
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
    (@_root_.D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbation.isUnit_one_add_of_locally_nilpotent.{u,v})
    (type_of% (realize signature.{u,v} (fun _ _ a => IsUnit (1 + a))
      (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbation.isUnit_one_add_of_locally_nilpotent
  realizationName := `Reg.D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbation.UnitLaw.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v}⟩
  objectArena := .source ⟨arena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v} ⟨source_registration.{u,v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u,v} (fun _ _ a => IsUnit (1 + a))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbation
    definition := none
    coordinates := #[0,1,2,3,4]
    readouts := #[{ path := #["body","body","body","body","body","body","body"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end UnitLaw

structure LocalParameters where
  base : Parameters.{u,v,w}
  nilpotent : ∀ x : base.V, ∃ n : ℕ, ((base.input.h * base.input.delta)^n) x = 0

private theorem sample_locally_nilpotent :
    ∀ x : sample.{u,v,w}.V, ∃ n : ℕ, ((sample.input.h * sample.input.delta)^n) x = 0 := by
  intro x
  exact ⟨1, DFunLike.congr_fun sample_nilpotent x⟩

private def localSample : LocalParameters.{u,v,w} := ⟨sample, sample_locally_nilpotent⟩

private theorem sample_K (x : sample.{u,v,w}.V) :
    K sample.input sample_locally_nilpotent x = x := by
  simpa [inversePolynomial] using
    K_apply_eq_inversePolynomial sample.input sample_locally_nilpotent x 1
      (DFunLike.congr_fun sample_nilpotent x)

namespace InversePolynomial

abbrev signature : Signature where
  Params := LocalParameters.{u,v,w}
  State p := p.base.V
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.base.V
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u,v,w} := realize signature
  (fun _ p x => K p.base.input p.nilpotent x) (fun e => nomatch e)
def rejected : Realization signature.{u,v,w} := realize signature
  (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u,v,w}
  Law r := ∀ {R : Type u} {V : Type v} [CommRing R] [AddCommGroup V] [Module R V]
    {U : Type w} [AddCommGroup U] [Module R U]
    (c : Input (R := R) (U := U) (V := V))
    (nilpotent : ∀ x : V, ∃ n : ℕ, ((c.h * c.delta)^n) x = 0)
    (x : V) (n : ℕ) (hx : ((c.h * c.delta)^n) x = 0),
    r.readout () ⟨⟨R,V,inferInstance,inferInstance,inferInstance,U,
      inferInstance,inferInstance,c⟩,nilpotent⟩ x =
        inversePolynomial (c.h * c.delta) n x

theorem actual_law : arena.Law actual.{u,v,w} := by
  intro R V _ _ _ U _ _ c nilpotent x n hx
  exact K_apply_eq_inversePolynomial c nilpotent x n hx

theorem rejected_law : ¬ arena.Law rejected.{u,v,w} := by
  intro law
  have h := law sample.input sample_locally_nilpotent
    (show sample.V from ⟨1⟩) 1
    (DFunLike.congr_fun sample_nilpotent (show sample.V from ⟨1⟩))
  change (0 : sample.V) = inversePolynomial (sample.input.h * sample.input.delta) 1 ⟨1⟩ at h
  have hz : (0 : sample.V) = ⟨1⟩ := by simpa [inversePolynomial] using h
  exact zero_ne_one (congrArg ULift.down hz)

theorem dependence : ObservationalDependence signature.{u,v,w} actual := by
  intro role
  refine ⟨localSample, 0, (show sample.V from ⟨1⟩), ?_⟩
  change K sample.input sample_locally_nilpotent 0 ≠
    K sample.input sample_locally_nilpotent (show sample.V from ⟨1⟩)
  rw [sample_K, sample_K]
  intro h
  exact zero_ne_one (congrArg ULift.down h)

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
    (@_root_.D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbation.K_apply_eq_inversePolynomial.{u,v,w})
    (type_of% (realize signature.{u,v,w}
      (fun _ p x => K p.base.input p.nilpotent x) (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbation.K_apply_eq_inversePolynomial
  realizationName := `Reg.D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbation.InversePolynomial.source_registration
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
    (fun _ p x => K p.base.input p.nilpotent x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbation
    definition := none
    coordinates := #[0,1,2,3,4,5,6,7,8,9]
    readouts := #[{ path := #["body","body","body","body","body","body","body",
      "body","body","body","body","body","body","fn","arg"]
      stateBinder := 10
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end InversePolynomial

/- PENDING, exact original target:
D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbation.locally_nilpotent_perturbation.
No registration is asserted. The raw native conclusion is the eight conjuncts
on the original linear maps, with c and its pointwise nilpotence proof in the
full dependent telescope. Selecting the whole proved conjunction or varying
only that proof gives a constant actual predicate and cannot prove the enrolled
ObservationalDependence obligation. A source-bound selection/model and bridge
that retain all eight identities, expose genuine variable observations of the
structured linear-map operands, and admit a whole-family sensitivity witness
have not been constructed here. No reduction to Booleans, uniform cutoff,
nontrivial-module restriction, new D5 claim or guessed source path is supplied.
The canonical writer may use its existing linked-issue exception for this row;
this source preparation imposes no delivery or publication condition. -/

end Reg.D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbation
