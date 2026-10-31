import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Measurement.AnticoherenceSpinCovariance
import Reg.Support.SingleDependentReadout

/-! Source-bound registrations for the public theorems in the mirrored owner. -/

set_option linter.style.longLine false
set_option linter.checkUnivs false

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

abbrev signature.{u_1} : Signature where
  Params := Type u_1
  State k := Matrix k k ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ k := Matrix k k ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual.{u_1} : Realization signature.{u_1} :=
  realize signature (fun _ _ q => qᵀ) (fun e => nomatch e)
def rejected.{u_1} : Realization signature.{u_1} :=
  realize signature (fun _ _ _ => fun _ _ => 2) (fun e => nomatch e)

abbrev arena.{u_1, u_2} : Arena where
  signature := signature.{u_1}
  Law R := ∀ {k : Type u_1} {n : Type u_2} [Fintype k] [Fintype n]
    [DecidableEq k] (q : Matrix k k ℂ) (_hq : R.readout () k q * q = 1)
    (s : k → Matrix n n ℂ) (x : Matrix n n ℂ),
    (∑ a : k, (∑ c : k, q a c • s c) * x * (∑ e : k, q a e • s e)) =
      ∑ c : k, s c * x * s c

private theorem rejected_law.{u_1, u_2} : ¬ arena.{u_1, u_2}.Law rejected := by
  intro h
  have hb := @h (ULift.{u_1} Unit) (ULift.{u_2} Unit) inferInstance inferInstance
    inferInstance (fun _ _ => 1 / 2)
    (by
      ext a b
      change (∑ _ : ULift.{u_1} Unit, (2 : ℂ) * (1 / 2)) = if a = b then 1 else 0
      simp [Subsingleton.elim a b]) (fun _ => 1) 1
  have he := congrFun (congrFun hb ⟨()⟩) ⟨()⟩
  norm_num [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply] at he

private theorem dependence.{u_1} : ObservationalDependence signature.{u_1} actual := by
  intro i
  refine ⟨ULift.{u_1} Unit, 0, (fun _ _ => 1), ?_⟩
  intro h
  have he := congrFun (congrFun h ⟨()⟩) ⟨()⟩
  change (0 : ℂ) = 1 at he
  exact zero_ne_one he

def source_registration.{u_1, u_2} : Registration arena (type_of% (@_root_.D5.S3.Quantum.Measurement.AnticoherenceSpinCovariance.orthogonal_sandwich.{u_1, u_2})) where
  actual := realize signature.{u_1} (fun _ _ q => qᵀ) (fun e => nomatch e)
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Measurement.AnticoherenceSpinCovariance.orthogonal_sandwich.{u_1, u_2}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration.{u_1, u_2} :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Measurement.AnticoherenceSpinCovariance.orthogonal_sandwich.{u_1, u_2}) (Realization signature.{u_1}) Unit Unit where
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
  readout := some (realize signature.{u_1} (fun _ _ q => qᵀ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurement.AnticoherenceSpinCovariance
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "domain", "fn", "arg", "fn", "arg"]
      stateBinder := 5
      functionOperand := false
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

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature (Σ _ : Fin 3, Fin 3) (fun _ => ℂ) (fun _ => ℂ)
def actual : Realization signature :=
  realize signature (fun _ p κ => if p.1 = p.2 then κ else 0) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena.{u} : Arena where
  signature := signature
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n]
    (d : Matrix n n ℂ) (_hd : dᴴ * d = 1) (r : Matrix (Fin 3) (Fin 3) ℝ)
    (_hr : rᵀ * r = 1) (j : Fin 3 → Matrix n n ℂ)
    (_hj : ∀ a, d * j a * dᴴ = ∑ c : Fin 3, (r a c : ℂ) • j c)
    (κ : ℂ) (a b : Fin 3),
    d * ((1 / 2 : ℂ) • (j a * j b + j b * j a) -
      R.readout () ⟨a, b⟩ κ • 1) * dᴴ =
      ∑ c : Fin 3, ∑ e : Fin 3, ((r a c : ℂ) * (r b e : ℂ)) •
        ((1 / 2 : ℂ) • (j c * j e + j e * j c) -
          (if c = e then κ else 0) • 1)

private theorem rejected_law.{u} : ¬ arena.{u}.Law rejected := by
  intro h
  have hb := @h (ULift.{u} Unit) inferInstance inferInstance 1 (by simp) 1 (by simp)
    (fun _ => 0) (by intro a; simp) 0 0 0
  have he := congrFun (congrFun hb ⟨()⟩) ⟨()⟩
  norm_num [rejected, realize] at he

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨0, 0⟩, 0, 1, ?_⟩
  change (if (0 : Fin 3) = 0 then (0 : ℂ) else 0) ≠
    (if (0 : Fin 3) = 0 then (1 : ℂ) else 0)
  simp

def source_registration.{u} : Registration arena (type_of% (@_root_.D5.S3.Quantum.Measurement.AnticoherenceSpinCovariance.quadratic_rotation.{u})) where
  actual := realize signature (fun _ p κ => if p.1 = p.2 then κ else 0) (fun e => nomatch e)
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Measurement.AnticoherenceSpinCovariance.quadratic_rotation.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration.{u} :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Measurement.AnticoherenceSpinCovariance.quadratic_rotation.{u}) (Realization signature) Unit Unit where
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
  readout := some (realize signature (fun _ p κ => if p.1 = p.2 then κ else 0) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurement.AnticoherenceSpinCovariance
    definition := none
    coordinates := #[10, 11]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg", "arg", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms source_registration
#print axioms registration

end QuadraticRotation

namespace PartialTraceIsometries

abbrev signature.{u_2, u_4} : Signature where
  Params := Σ _ : Type u_2, Type u_4
  State p := Matrix p.1 p.2 ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Matrix p.2 p.1 ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual.{u_2, u_4} : Realization signature.{u_2, u_4} :=
  realize signature (fun _ _ w => wᴴ) (fun e => nomatch e)
def rejected.{u_2, u_4} : Realization signature.{u_2, u_4} :=
  realize signature (fun _ _ _ => fun _ _ => 2) (fun e => nomatch e)

abbrev arena.{u_1, u_2, u_3, u_4} : Arena where
  signature := signature.{u_2, u_4}
  Law R := ∀ {a : Type u_1} {b : Type u_2} {i : Type u_3} {j : Type u_4}
    [Fintype a] [Fintype b] [Fintype i] [Fintype j]
    [DecidableEq j] (v : Matrix a i ℂ) (w : Matrix b j ℂ)
    (_hw : R.readout () ⟨b, j⟩ w * w = 1) (z : Matrix (i × j) (i × j) ℂ),
    partialTraceRight (Matrix.kronecker v w * z * (Matrix.kronecker v w)ᴴ) =
      v * partialTraceRight z * vᴴ

set_option backward.isDefEq.respectTransparency false in
private theorem rejected_law.{u_1, u_2, u_3, u_4} : ¬ arena.{u_1, u_2, u_3, u_4}.Law rejected := by
  intro h
  have hb := @h (ULift.{u_1} Unit) (ULift.{u_2} Unit) (ULift.{u_3} Unit) (ULift.{u_4} Unit)
    inferInstance inferInstance inferInstance inferInstance inferInstance
    (fun _ _ => 1) (fun _ _ => 1 / 2)
    (by
      ext a b
      change (∑ _ : ULift.{u_2} Unit, (2 : ℂ) * (1 / 2)) = if a = b then 1 else 0
      simp [Subsingleton.elim a b]) (fun _ _ => 1)
  have he := congrFun (congrFun hb ⟨()⟩) ⟨()⟩
  simp only [partialTraceRight, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.kronecker, Matrix.kroneckerMap, Matrix.of_apply,
    Fintype.sum_prod_type, Fintype.sum_unique] at he
  norm_num at he

private theorem dependence.{u_2, u_4} : ObservationalDependence signature.{u_2, u_4} actual := by
  intro i
  refine ⟨⟨ULift.{u_2} Unit, ULift.{u_4} Unit⟩, 0, (fun _ _ => 1), ?_⟩
  intro h
  have he := congrFun (congrFun h ⟨()⟩) ⟨()⟩
  change star (0 : ℂ) = star 1 at he
  simp at he

def source_registration.{u_1, u_2, u_3, u_4} : Registration arena (type_of% (@_root_.D5.S3.Quantum.Measurement.AnticoherenceSpinCovariance.partialTrace_isometries.{u_1, u_2, u_3, u_4})) where
  actual := realize signature.{u_2, u_4} (fun _ _ w => wᴴ) (fun e => nomatch e)
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Measurement.AnticoherenceSpinCovariance.partialTrace_isometries.{u_1, u_2, u_3, u_4}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration.{u_1, u_2, u_3, u_4} :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Measurement.AnticoherenceSpinCovariance.partialTrace_isometries.{u_1, u_2, u_3, u_4}) (Realization signature.{u_2, u_4}) Unit Unit where
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
  readout := some (realize signature.{u_2, u_4} (fun _ _ w => wᴴ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurement.AnticoherenceSpinCovariance
    definition := none
    coordinates := #[1, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "domain", "fn", "arg", "fn", "arg"]
      stateBinder := 10
      functionOperand := false
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
