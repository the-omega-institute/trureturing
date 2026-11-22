import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9FirstOrderMinor
import Reg.Support.DependentFamily
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Field.ULift

/-! The observation is the linear determinant coefficient as the perturbation varies. -/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.checkUnivs false

namespace Reg.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9FirstOrderMinor

open _root_.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9FirstOrderMinor
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Polynomial
open scoped Matrix

universe u v

noncomputable section

private abbrev Params (S : Type v → Type v) :=
  Σ ι : Type u, Σ R : Type v, Σ _ : Fintype ι, Σ _ : DecidableEq ι, Σ _ : S R, Matrix ι ι R

private abbrev signature (S : Type v → Type v) : Signature where
  Params := Params.{u, v} S
  State p := Matrix p.1 p.1 p.2.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.2.1
  Anchor := Empty
  finiteAnchor := inferInstance

private def actual {S : Type v → Type v} (toRing : ∀ R, S R → CommRing R) :
    Realization (signature.{u, v} S) :=
  realize (signature S) (fun _ p E =>
    letI := p.2.2.1
    letI := p.2.2.2.1
    letI := toRing p.2.1 p.2.2.2.2.1
    let C₀ : p.2.1 →+* p.2.1[X] := C
    (p.2.2.2.2.2.map C₀ + (X : p.2.1[X]) • E.map C₀).det.coeff 1) Empty.elim

private def rejected {S : Type v → Type v} (toRing : ∀ R, S R → CommRing R) :
    Realization (signature.{u, v} S) :=
  realize (signature S) (fun _ p _ =>
    letI := toRing p.2.1 p.2.2.2.2.1
    0) Empty.elim

private abbrev ringActual : Realization (signature.{u, v} CommRing) := actual fun _ s => s
private abbrev ringRejected : Realization (signature.{u, v} CommRing) := rejected fun _ s => s

private abbrev fieldActual : Realization (signature.{u, v} Field) := actual fun _ s => s.toCommRing
private abbrev fieldRejected : Realization (signature.{u, v} Field) := rejected fun _ s => s.toCommRing

private abbrev identityArena : Arena where
  signature := signature.{u, v} CommRing
  Law T := ∀ {ι : Type u} {R : Type v} [f : Fintype ι] [d : DecidableEq ι] [s : CommRing R]
    (A E : Matrix ι ι R) (x : ι → R) (j : ι) (_ : A.mulVec x = 0),
    x j * T.readout () ⟨ι, R, f, d, s, A⟩ E = (A.updateCol j (E.mulVec x)).det

private abbrev pairingArena : Arena where
  signature := signature.{u, v} Field
  Law T := ∀ {ι : Type u} {K : Type v} [f : Fintype ι] [d : DecidableEq ι] [s : Field K]
    (A E : Matrix ι ι K) (x y : ι → K) (j : ι) (_ : A.mulVec x = 0)
    (_ : y ᵥ* A = 0) (_ : y ⬝ᵥ E.mulVec x ≠ 0)
    (_ : LinearIndependent K (fun i : {i : ι // i ≠ j} => A.col i.1)),
    T.readout () ⟨ι, K, f, d, s, A⟩ E ≠ 0

private abbrev ProbeIndex := ULift.{u} (Fin 1)
private abbrev ProbeScalar := ULift.{v} ℚ
private abbrev ProbeMatrix := Matrix ProbeIndex.{u} ProbeIndex.{u} ProbeScalar.{v}

private def probePerturbation : ProbeMatrix.{u, v} := fun _ _ => 1

private theorem probe_coeff (E : ProbeMatrix.{u, v}) :
    ((0 : ProbeMatrix.{u, v}).map (C : ProbeScalar.{v} →+* ProbeScalar.{v}[X]) +
      (X : ProbeScalar.{v}[X]) •
        E.map (C : ProbeScalar.{v} →+* ProbeScalar.{v}[X])).det.coeff 1 =
      E default default := by
  rw [Matrix.det_unique]
  simp [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
  rfl

private theorem identity_rejected : ¬ identityArena.{u, v}.Law ringRejected := by
  intro law
  have h := law (0 : ProbeMatrix.{u, v}) probePerturbation 1 default (by simp)
  change (1 : ProbeScalar.{v}) * 0 = _ at h
  rw [mul_zero, Matrix.det_unique] at h
  have hentry : (0 : ProbeMatrix.{u, v}).updateCol default (probePerturbation.mulVec 1)
      default default = (probePerturbation : ProbeMatrix.{u, v}).mulVec 1 default :=
    Matrix.updateCol_self
  exact (zero_ne_one : (0 : ProbeScalar.{v}) ≠ 1) (by
    simpa [Matrix.mulVec, dotProduct, probePerturbation] using h.trans hentry)

private theorem pairing_rejected : ¬ pairingArena.{u, v}.Law fieldRejected := by
  intro law
  let j : ProbeIndex.{u} := default
  let : IsEmpty {i : ProbeIndex.{u} // i ≠ j} :=
    ⟨fun i => i.2 (Subsingleton.elim i.1 j)⟩
  exact law (0 : ProbeMatrix.{u, v}) probePerturbation 1 1 j (by simp) (by simp)
    (by simp [Matrix.mulVec, dotProduct, probePerturbation]) linearIndependent_empty_type rfl

def identitySource : Registration identityArena.{u, v}
    (type_of% (@mul_coeff_one_det_pencil_eq_det_updateCol.{u, v})) where
  actual := ringActual
  bridge := Iff.rfl
  variation := ⟨@mul_coeff_one_det_pencil_eq_det_updateCol.{u, v}, ringRejected, identity_rejected⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨ringRejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, identity_rejected⟩
    · intro e
      exact nomatch e
  dependence := by
    intro _
    refine ⟨⟨ProbeIndex.{u}, ProbeScalar.{v}, inferInstance, inferInstance, inferInstance, 0⟩,
      probePerturbation, 0, ?_⟩
    simp only [ringActual, actual, realize, probe_coeff, probePerturbation]
    exact one_ne_zero

def pairingSource : Registration pairingArena.{u, v}
    (type_of% (@coeff_one_det_pencil_ne_zero_of_pairing.{u, v})) where
  actual := fieldActual
  bridge := Iff.rfl
  variation := ⟨@coeff_one_det_pencil_ne_zero_of_pairing.{u, v}, fieldRejected, pairing_rejected⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨fieldRejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, pairing_rejected⟩
    · intro e
      exact nomatch e
  dependence := by
    intro _
    refine ⟨⟨ProbeIndex.{u}, ProbeScalar.{v}, inferInstance, inferInstance, inferInstance, 0⟩,
      probePerturbation, 0, ?_⟩
    simp only [fieldActual, actual, realize, probe_coeff, probePerturbation]
    exact one_ne_zero

def identityRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@mul_coeff_one_det_pencil_eq_det_updateCol.{u, v})
    (Realization (signature.{u, v} CommRing)) Unit Unit where
  unitName :=
    `D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9FirstOrderMinor.mul_coeff_one_det_pencil_eq_det_updateCol.__information_unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9FirstOrderMinor.identitySource
  realizationSource := none
  generated := false
  arena := .source ⟨identityArena.{u, v}⟩
  objectArena := .source ⟨identityArena.{u, v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source identityArena.{u, v} ⟨identitySource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize (signature CommRing) ringActual.readout ringActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9FirstOrderMinor
    definition := none
    coordinates := #[0, 1, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "fn", "arg", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def pairingRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@coeff_one_det_pencil_ne_zero_of_pairing.{u, v})
    (Realization (signature.{u, v} Field)) Unit Unit where
  unitName :=
    `D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9FirstOrderMinor.coeff_one_det_pencil_ne_zero_of_pairing.__information_unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9FirstOrderMinor.pairingSource
  realizationSource := none
  generated := false
  arena := .source ⟨pairingArena.{u, v}⟩
  objectArena := .source ⟨pairingArena.{u, v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source pairingArena.{u, v} ⟨pairingSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize (signature Field) fieldActual.readout fieldActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9FirstOrderMinor
    definition := none
    coordinates := #[0, 1, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9FirstOrderMinor
