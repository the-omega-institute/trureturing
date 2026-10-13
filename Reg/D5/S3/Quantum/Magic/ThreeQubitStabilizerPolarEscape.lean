import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape
open _root_.D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix
open scoped ComplexOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- The exact Bell value observes the real polar parameter. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ s => s) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- The complete theorem, observing only the parameter in the Bell-value numerator. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (s : ℝ) (_hl : 1 / 3 < s) (_hu : 7 * s ^ 2 < 1),
    (∀ (n : ℕ) (η : Op n), η ∈ STAB n → IsState η) ∧
    (IsState sigma ∧ tr (sigma * S) = 1) ∧
    Sᴴ = S ∧ S * S = (7 : ℂ) • (1 : Op 3) ∧ S.trace = 0 ∧
    (∀ A B : Op 3, tr (bell * tensor A (conjugate B)) = tr (A * Bᴴ) / 8) ∧
    bell ∈ STAB 6 ∧ (W s).PosDef ∧ (conjugate (W s)).PosDef ∧
    (∀ η ∈ STAB 3, tr (η * W s) ≤ 1 ∧ tr (η * conjugate (W s)) ≤ 1) ∧
    tr (bell * tensor (W s) (conjugate (W s))) =
      (1 + 7 * (R.readout () () s) ^ 2) / (1 + s) ^ 2 ∧
    1 < tr (bell * tensor (W s) (conjugate (W s)))

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hvalue, hstrict⟩ :=
    h (3 / 8) (by norm_num) (by norm_num)
  change tr (bell * tensor (W (3 / 8)) (conjugate (W (3 / 8)))) =
    (1 + 7 * (0 : ℝ) ^ 2) / (1 + 3 / 8) ^ 2 at hvalue
  rw [hvalue] at hstrict
  norm_num at hstrict

def source_registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨stabilizer_polar_tensor_escape, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := by
    intro i
    exact ⟨(), 0, 1, zero_ne_one⟩

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.stabilizer_polar_tensor_escape)
      (type_of% (realize signature (fun _ _ s => s) (fun e => nomatch e)))
      Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str
    `D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.stabilizer_polar_tensor_escape
    "Reg.D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape/\
    Reg.D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.arena/[anonymous]")
    "__information_unit",
  realizationName :=
    `Reg.D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.source_registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨source_registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ s => s) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape,
    definition := none,
    coordinates := #[],
    readouts := #[{
      path := #["body", "body", "body", "arg", "arg", "arg", "arg", "arg",
        "arg", "arg", "arg", "arg", "arg", "fn", "arg", "arg", "fn", "arg",
        "arg", "arg", "fn", "arg"],
      stateBinder := 0,
      functionOperand := false,
      stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

namespace LocalGates
open _root_.D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence (localOp)

/-- A local embedding observes a single-qubit matrix at a specified coordinate. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature (Σ n : ℕ, Fin n)
    (fun _ => Matrix (Fin 2) (Fin 2) ℂ) (fun p => Op p.1)

def actual : Realization signature :=
  realize signature (fun _ p A => localOp p.2 A) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1, 0⟩, 0, 1, ?_⟩
  change localOp (0 : Fin 1) 0 ≠ localOp (0 : Fin 1) 1
  rw [local_identity]
  have hzero : localOp (0 : Fin 1) (0 : Matrix (Fin 2) (Fin 2) ℂ) = 0 := by
    ext x y
    change (∏ j : Fin 1, Function.update (fun _ => (1 : Matrix (Fin 2) (Fin 2) ℂ))
      0 0 j (x j) (y j)) = 0
    simp
  rw [hzero]
  exact zero_ne_one

namespace Identity

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (i : Fin n),
    R.readout () ⟨n, i⟩ (1 : Matrix (Fin 2) (Fin 2) ℂ) = (1 : Op n)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h (0 : Fin 1)
  change (0 : Op 1) = 1 at he
  exact zero_ne_one he

def source_registration : Registration arena (type_of% @local_identity) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨local_identity, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.local_identity)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.LocalGates.Identity.unit,
  realizationName :=
    Lean.Name.str
      `Reg.D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.LocalGates.Identity
      "source_registration",
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨source_registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ p A => localOp p.2 A) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape,
    definition := none,
    coordinates := #[0, 1],
    readouts := #[{
      path := #["body", "body", "fn", "arg"],
      stateBinder := 0,
      functionOperand := false,
      stateOperand := some #["arg"],
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

end Identity

namespace Product

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (i : Fin n) (A B : Matrix (Fin 2) (Fin 2) ℂ),
    localOp i A * localOp i B = R.readout () ⟨n, i⟩ (A * B)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h (0 : Fin 1) 1 1
  change localOp (0 : Fin 1) 1 * localOp (0 : Fin 1) 1 = (0 : Op 1) at he
  rw [local_identity, one_mul] at he
  exact one_ne_zero he

def source_registration : Registration arena (type_of% @local_product) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨local_product, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.local_product)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.LocalGates.Product.unit,
  realizationName :=
    `Reg.D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.LocalGates.Product.source_registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨source_registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ p A => localOp p.2 A) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape,
    definition := none,
    coordinates := #[0, 1],
    readouts := #[{
      path := #["body", "body", "body", "body", "arg"],
      stateBinder := 0,
      functionOperand := false,
      stateOperand := some #["arg"],
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

end Product

namespace Adjoint

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (i : Fin n) (A : Matrix (Fin 2) (Fin 2) ℂ),
    (localOp i A)ᴴ = R.readout () ⟨n, i⟩ Aᴴ

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h (0 : Fin 1) 1
  change (localOp (0 : Fin 1) 1)ᴴ = (0 : Op 1) at he
  rw [local_identity, Matrix.conjTranspose_one] at he
  exact one_ne_zero he

def source_registration : Registration arena (type_of% @local_adjoint) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨local_adjoint, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.local_adjoint)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.LocalGates.Adjoint.unit,
  realizationName :=
    `Reg.D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.LocalGates.Adjoint.source_registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨source_registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ p A => localOp p.2 A) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape,
    definition := none,
    coordinates := #[0, 1],
    readouts := #[{
      path := #["body", "body", "body", "arg"],
      stateBinder := 0,
      functionOperand := false,
      stateOperand := some #["arg"],
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

end Adjoint

#print axioms Adjoint.source_registration
#print axioms Adjoint.registration
end LocalGates

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape
