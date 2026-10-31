import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Measurement.AnticoherenceSpinCovariance
import Reg.Support.SingleDependentReadout

/-! Source-bound registrations for the public theorems in the mirrored owner. -/

set_option linter.style.longLine false

set_option pp.proofs false in
#print D5.S3.Quantum.Measurement.AnticoherenceSpinCovariance.pauli_rotation
set_option pp.proofs false in
#print D5.S3.Quantum.Measurement.AnticoherenceSpinCovariance.orthogonal_sandwich
set_option pp.proofs false in
#print D5.S3.Quantum.Measurement.AnticoherenceSpinCovariance.tensor_unitary
set_option pp.proofs false in
#print D5.S3.Quantum.Measurement.AnticoherenceSpinCovariance.local_action
set_option pp.proofs false in
#print D5.S3.Quantum.Measurement.AnticoherenceSpinCovariance.collective_tensor_rotation
set_option pp.proofs false in
#print D5.S3.Quantum.Measurement.AnticoherenceSpinCovariance.quadratic_rotation
set_option pp.proofs false in
#print D5.S3.Quantum.Measurement.AnticoherenceSpinCovariance.partialTrace_isometries
set_option pp.proofs false in
#print D5.S3.Quantum.Measurement.AnticoherenceSpinCovariance.dicke_site_sum

namespace Reg.D5.S3.Quantum.Measurement.AnticoherenceSpinCovariance
open _root_.D5.S3.Quantum.Measurement.AnticoherenceSpinCovariance
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction (pauli)
open _root_.D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence
  (tensorOp localOp)
open _root_.D5.S3.Quantum.Information.PartialTraceMutualInformation (partialTraceRight)
open Matrix
open scoped BigOperators
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Equality of matrix observations, retaining the unrestricted index type. -/
abbrev matrixSignature.{u} : Signature where
  Params := Type u
  State n := Matrix n n ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ n := Matrix n n ℂ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def matrixActual.{u} : Realization matrixSignature.{u} :=
  realize matrixSignature (fun _ _ X Y => X = Y) (fun e => Empty.elim e)
def matrixRejected.{u} : Realization matrixSignature.{u} :=
  realize matrixSignature (fun _ _ _ _ => False) (fun e => Empty.elim e)
private theorem matrix_dependence.{u} : ObservationalDependence matrixSignature.{u} matrixActual := by
  intro i
  refine ⟨ULift.{u} Unit, 0, 1, ?_⟩
  intro h
  have he := congrFun h 0
  change ((0 : Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ) = 0) = (1 = 0) at he
  exact one_ne_zero (Eq.mp he rfl)

abbrev scalarSignature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℂ → Prop)
def scalarActual : Realization scalarSignature :=
  realize scalarSignature (fun _ _ x y => x = y) (fun e => nomatch e)
def scalarRejected : Realization scalarSignature :=
  realize scalarSignature (fun _ _ _ _ => False) (fun e => nomatch e)
private theorem scalar_dependence : ObservationalDependence scalarSignature scalarActual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have he := congrFun h 0
  change ((0 : ℂ) = 0) = (1 = 0) at he
  exact one_ne_zero (Eq.mp he rfl)

namespace PauliRotation

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => Matrix (Fin 3) (Fin 3) ℝ) (fun _ => Matrix (Fin 3) (Fin 3) ℝ)
def actual : Realization signature :=
  realize signature (fun _ _ r => rᵀ * r) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ u : Matrix.specialUnitaryGroup (Fin 2) ℂ,
    ∃ r : Matrix (Fin 3) (Fin 3) ℝ, R.readout () () r = 1 ∧
      ∀ a : Fin 3, u.val * pauli a * u.valᴴ =
        ∑ c : Fin 3, (r a c : ℂ) • pauli c

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨r, hr, _⟩ := h 1
  have he := congrFun (congrFun hr 0) 0
  change (0 : ℝ) = 1 at he
  exact zero_ne_one he

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  change (0 : Matrix (Fin 3) (Fin 3) ℝ)ᵀ * 0 ≠ 1ᵀ * 1
  simp

def source_registration : Registration arena (type_of% (@_root_.D5.S3.Quantum.Measurement.AnticoherenceSpinCovariance.pauli_rotation)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Measurement.AnticoherenceSpinCovariance.pauli_rotation, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Measurement.AnticoherenceSpinCovariance.pauli_rotation) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Measurement.AnticoherenceSpinCovariance.pauli_rotation.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Measurement.AnticoherenceSpinCovariance.PauliRotation.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ r => rᵀ * r) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurement.AnticoherenceSpinCovariance
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "arg", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms source_registration
#print axioms registration

end PauliRotation

namespace OrthogonalSandwich

abbrev arena.{u, v} : Arena where
  signature := matrixSignature.{v}
  Law R := ∀ {k : Type u} {n : Type v} [Fintype k] [Fintype n]
    [DecidableEq k] (q : Matrix k k ℂ) (_hq : qᵀ * q = 1)
    (s : k → Matrix n n ℂ) (x : Matrix n n ℂ),
    R.readout () n
      (∑ a : k, (∑ c : k, q a c • s c) * x * (∑ e : k, q a e • s e))
      (∑ c : k, s c * x * s c)

private theorem rejected_law.{u, v} : ¬ arena.{u, v}.Law matrixRejected := by
  intro h
  exact @h (ULift.{u} Unit) (ULift.{v} Unit) inferInstance inferInstance inferInstance
    1 (by simp) (fun _ => 0) 0

private theorem dependence.{v} : ObservationalDependence matrixSignature.{v} matrixActual := by
  exact matrix_dependence

def source_registration.{u, v} : Registration arena.{u, v} (type_of% (@_root_.D5.S3.Quantum.Measurement.AnticoherenceSpinCovariance.orthogonal_sandwich.{u, v})) where
  actual := realize matrixSignature.{v} (fun _ _ X Y => X = Y) (fun e => Empty.elim e)
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Measurement.AnticoherenceSpinCovariance.orthogonal_sandwich.{u, v}, matrixRejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨matrixRejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration.{u, v} :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Measurement.AnticoherenceSpinCovariance.orthogonal_sandwich.{u, v}) (Realization matrixSignature.{v}) Unit Unit where
  unitName := `D5.S3.Quantum.Measurement.AnticoherenceSpinCovariance.orthogonal_sandwich.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Measurement.AnticoherenceSpinCovariance.OrthogonalSandwich.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize matrixSignature.{v} (fun _ _ X Y => X = Y) (fun e => Empty.elim e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurement.AnticoherenceSpinCovariance
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms source_registration
#print axioms registration

end OrthogonalSandwich

namespace TensorUnitary

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℕ
    (fun n => Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ)
    (fun n => Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ)
def actual : Realization signature :=
  realize signature (fun _ _ X => Xᴴ) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) (u : Matrix.specialUnitaryGroup (Fin 2) ℂ),
    R.readout () n (tensorOp (fun _ : Fin n => u.val)) *
      tensorOp (fun _ : Fin n => u.val) = 1

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 0 1
  change (0 : Matrix (Fin 0 → Fin 2) (Fin 0 → Fin 2) ℂ) * _ = 1 at hb
  rw [Matrix.zero_mul] at hb
  exact zero_ne_one hb

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨0, 0, 1, ?_⟩
  change (0 : Matrix (Fin 0 → Fin 2) (Fin 0 → Fin 2) ℂ)ᴴ ≠ 1ᴴ
  simp

def source_registration : Registration arena (type_of% (@_root_.D5.S3.Quantum.Measurement.AnticoherenceSpinCovariance.tensor_unitary)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Measurement.AnticoherenceSpinCovariance.tensor_unitary, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Measurement.AnticoherenceSpinCovariance.tensor_unitary) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Measurement.AnticoherenceSpinCovariance.tensor_unitary.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Measurement.AnticoherenceSpinCovariance.TensorUnitary.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ X => Xᴴ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurement.AnticoherenceSpinCovariance
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      stateOperand := some #["arg"]
      functionOperand := false
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms source_registration
#print axioms registration

end TensorUnitary

namespace LocalAction

abbrev arena : Arena where
  signature := scalarSignature
  Law R := ∀ {n : ℕ} (k : Fin n) (a : Matrix (Fin 2) (Fin 2) ℂ)
    (f : (Fin n → Fin 2) → ℂ) (x : Fin n → Fin 2),
    R.readout () () ((localOp k a *ᵥ f) x)
      (∑ b : Fin 2, a (x k) b * f (Function.update x k b))

private theorem rejected_law : ¬ arena.Law scalarRejected := by
  intro h
  exact h (n := 1) 0 0 (fun _ => 0) (fun _ => 0)

private theorem dependence : ObservationalDependence scalarSignature scalarActual := by
  exact scalar_dependence

def source_registration : Registration arena (type_of% (@_root_.D5.S3.Quantum.Measurement.AnticoherenceSpinCovariance.local_action)) where
  actual := scalarActual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Measurement.AnticoherenceSpinCovariance.local_action, scalarRejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨scalarRejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Measurement.AnticoherenceSpinCovariance.local_action) (Realization scalarSignature) Unit Unit where
  unitName := `D5.S3.Quantum.Measurement.AnticoherenceSpinCovariance.local_action.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Measurement.AnticoherenceSpinCovariance.LocalAction.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize scalarSignature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurement.AnticoherenceSpinCovariance
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms source_registration
#print axioms registration

end LocalAction

namespace CollectiveTensorRotation

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℕ
    (fun n => Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ)
    (fun n => Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ → Prop)
def actual : Realization signature :=
  realize signature (fun _ _ X Y => X = Y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) (u : Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (r : Matrix (Fin 3) (Fin 3) ℝ)
    (_hr : ∀ a, u.val * pauli a * u.valᴴ =
      ∑ c : Fin 3, (r a c : ℂ) • pauli c) (a : Fin 3),
    R.readout () n
      (tensorOp (fun _ : Fin n => u.val) * collectiveSpin n a *
        (tensorOp (fun _ : Fin n => u.val))ᴴ)
      (∑ c : Fin 3, (r a c : ℂ) • collectiveSpin n c)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨r, _, hr⟩ := pauli_rotation 1
  exact h 0 1 r hr 0

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨0, 0, 1, ?_⟩
  intro h
  have he := congrFun h 0
  change ((0 : Matrix (Fin 0 → Fin 2) (Fin 0 → Fin 2) ℂ) = 0) = (1 = 0) at he
  exact one_ne_zero (Eq.mp he rfl)

def source_registration : Registration arena (type_of% (@_root_.D5.S3.Quantum.Measurement.AnticoherenceSpinCovariance.collective_tensor_rotation)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Measurement.AnticoherenceSpinCovariance.collective_tensor_rotation, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Measurement.AnticoherenceSpinCovariance.collective_tensor_rotation) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Measurement.AnticoherenceSpinCovariance.collective_tensor_rotation.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Measurement.AnticoherenceSpinCovariance.CollectiveTensorRotation.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ X Y => X = Y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurement.AnticoherenceSpinCovariance
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms source_registration
#print axioms registration

end CollectiveTensorRotation

namespace QuadraticRotation

abbrev arena.{u} : Arena where
  signature := matrixSignature.{u}
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n]
    (d : Matrix n n ℂ) (_hd : dᴴ * d = 1) (r : Matrix (Fin 3) (Fin 3) ℝ)
    (_hr : rᵀ * r = 1) (j : Fin 3 → Matrix n n ℂ)
    (_hj : ∀ a, d * j a * dᴴ = ∑ c : Fin 3, (r a c : ℂ) • j c)
    (a b : Fin 3),
    R.readout () n
      (d * ((1 / 2 : ℂ) • (j a * j b + j b * j a) -
        (if a = b then (20 / 3 : ℂ) else 0) • 1) * dᴴ)
      (∑ c : Fin 3, ∑ e : Fin 3, ((r a c : ℂ) * (r b e : ℂ)) •
        ((1 / 2 : ℂ) • (j c * j e + j e * j c) -
          (if c = e then (20 / 3 : ℂ) else 0) • 1))

private theorem rejected_law.{u} : ¬ arena.{u}.Law matrixRejected := by
  intro h
  exact @h (ULift.{u} Unit) inferInstance inferInstance 1 (by simp) 1 (by simp)
    (fun _ => 0) (by intro a; simp) 0 0

private theorem dependence.{u} : ObservationalDependence matrixSignature.{u} matrixActual := by
  exact matrix_dependence

def source_registration.{u} : Registration arena.{u} (type_of% (@_root_.D5.S3.Quantum.Measurement.AnticoherenceSpinCovariance.quadratic_rotation.{u})) where
  actual := realize matrixSignature.{u} (fun _ _ X Y => X = Y) (fun e => Empty.elim e)
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Measurement.AnticoherenceSpinCovariance.quadratic_rotation.{u}, matrixRejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨matrixRejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration.{u} :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Measurement.AnticoherenceSpinCovariance.quadratic_rotation.{u}) (Realization matrixSignature.{u}) Unit Unit where
  unitName := `D5.S3.Quantum.Measurement.AnticoherenceSpinCovariance.quadratic_rotation.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Measurement.AnticoherenceSpinCovariance.QuadraticRotation.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize matrixSignature.{u} (fun _ _ X Y => X = Y) (fun e => Empty.elim e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurement.AnticoherenceSpinCovariance
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms source_registration
#print axioms registration

end QuadraticRotation

namespace PartialTraceIsometries

abbrev arena.{u, v, w, z} : Arena where
  signature := matrixSignature.{u}
  Law R := ∀ {a : Type u} {b : Type v} {i : Type w} {j : Type z}
    [Fintype a] [Fintype b] [Fintype i] [Fintype j]
    [DecidableEq j] (v : Matrix a i ℂ) (w : Matrix b j ℂ)
    (_hw : wᴴ * w = 1) (z : Matrix (i × j) (i × j) ℂ),
    R.readout () a
      (partialTraceRight (Matrix.kronecker v w * z * (Matrix.kronecker v w)ᴴ))
      (v * partialTraceRight z * vᴴ)

private theorem rejected_law.{u, v, w, z} : ¬ arena.{u, v, w, z}.Law matrixRejected := by
  intro h
  exact @h (ULift.{u} Unit) (ULift.{v} Unit) (ULift.{w} Unit) (ULift.{z} Unit)
    inferInstance inferInstance inferInstance inferInstance inferInstance
    0 (fun _ _ => 1)
    (by
      ext i j
      change (∑ _ : ULift.{v} Unit, star (1 : ℂ) * 1) = if i = j then 1 else 0
      simp [Subsingleton.elim i j]) 0

private theorem dependence.{u} : ObservationalDependence matrixSignature.{u} matrixActual := by
  exact matrix_dependence

def source_registration.{u, v, w, z} : Registration arena.{u, v, w, z} (type_of% (@_root_.D5.S3.Quantum.Measurement.AnticoherenceSpinCovariance.partialTrace_isometries.{u, v, w, z})) where
  actual := realize matrixSignature.{u} (fun _ _ X Y => X = Y) (fun e => Empty.elim e)
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Measurement.AnticoherenceSpinCovariance.partialTrace_isometries.{u, v, w, z}, matrixRejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨matrixRejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration.{u, v, w, z} :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Measurement.AnticoherenceSpinCovariance.partialTrace_isometries.{u, v, w, z}) (Realization matrixSignature.{u}) Unit Unit where
  unitName := `D5.S3.Quantum.Measurement.AnticoherenceSpinCovariance.partialTrace_isometries.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Measurement.AnticoherenceSpinCovariance.PartialTraceIsometries.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize matrixSignature.{u} (fun _ _ X Y => X = Y) (fun e => Empty.elim e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurement.AnticoherenceSpinCovariance
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms source_registration
#print axioms registration

end PartialTraceIsometries

namespace DickeSiteSum

abbrev arena : Arena where
  signature := scalarSignature
  Law R := ∀ (n : ℕ) (a : Matrix (Fin 2) (Fin 2) ℂ)
    (x : Fin n → Fin 2) (r : Fin (n + 1)),
    R.readout () ()
      (∑ k : Fin n, ∑ b : Fin 2, a (x k) b *
        dickeIsometry n (Function.update x k b) r)
      (((n : ℂ) - (∑ k, (x k).val : ℕ)) *
        (a 0 0 * dickeCoefficient n (∑ k, (x k).val) r.val +
          a 0 1 * dickeCoefficient n ((∑ k, (x k).val) + 1) r.val) +
        (∑ k, (x k).val : ℕ) *
        (a 1 0 * dickeCoefficient n ((∑ k, (x k).val) - 1) r.val +
          a 1 1 * dickeCoefficient n (∑ k, (x k).val) r.val))

private theorem rejected_law : ¬ arena.Law scalarRejected := by
  intro h
  exact h 0 0 (fun i => Fin.elim0 i) 0

private theorem dependence : ObservationalDependence scalarSignature scalarActual := by
  exact scalar_dependence

def source_registration : Registration arena (type_of% (@_root_.D5.S3.Quantum.Measurement.AnticoherenceSpinCovariance.dicke_site_sum)) where
  actual := scalarActual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Measurement.AnticoherenceSpinCovariance.dicke_site_sum, scalarRejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨scalarRejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Measurement.AnticoherenceSpinCovariance.dicke_site_sum) (Realization scalarSignature) Unit Unit where
  unitName := `D5.S3.Quantum.Measurement.AnticoherenceSpinCovariance.dicke_site_sum.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Measurement.AnticoherenceSpinCovariance.DickeSiteSum.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize scalarSignature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurement.AnticoherenceSpinCovariance
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms source_registration
#print axioms registration

end DickeSiteSum

end
end Reg.D5.S3.Quantum.Measurement.AnticoherenceSpinCovariance
