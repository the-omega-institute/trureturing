import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.AURICOmega.QuaternionRayKernel
import Reg.Support.DependentFamily

/-! Source-bound audits of the phase-blind ray kernel on the unit quaternions. -/

namespace Reg.D5.S3.Quantum.AURICOmega.QuaternionRayKernel

open _root_.D5.S3.Quantum.AURICOmega.QuaternionComparisonModel
open _root_.D5.S3.Quantum.AURICOmega.QuaternionRayKernel
open _root_.D5.S3.Quantum.Information.ActualPureQubitCostInfimum (bloch)
open _root_.D5.S3.Quantum.FiniteDimensional (bornProbability)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

open scoped InnerProductSpace Quaternion

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false
noncomputable section

/-- The unit quaternion `j`, off the phase circle of `1` and `i`. -/
def unitJ : unitary ℍ[ℝ] :=
  ⟨⟨0, 0, 1, 0⟩, Unitary.mem_iff.mpr ⟨by ext <;> simp, by ext <;> simp⟩⟩

/-- The unit quaternion `1` lies on the phase circle. -/
theorem one_phase : ((1 : unitary ℍ[ℝ]) : ℍ[ℝ]).imJ = 0 ∧ ((1 : unitary ℍ[ℝ]) : ℍ[ℝ]).imK = 0 := by
  simp only [OneMemClass.coe_one, Quaternion.imJ_one, Quaternion.imK_one, and_self]

/-- The ray kernel of a unit quaternion with itself is one. -/
theorem rayKernel_one_one : rayKernel 1 1 = 1 :=
  (rayKernel_eq_one_iff 1 1).2 ⟨1, one_phase, (mul_one 1).symm⟩

/-- The ray kernel separates `1` from `j`. -/
theorem rayKernel_one_ne : rayKernel 1 1 ≠ rayKernel 1 unitJ := by
  rw [rayKernel_one_one]
  intro h
  obtain ⟨c, hc, hj⟩ := (rayKernel_eq_one_iff 1 unitJ).1 h.symm
  rw [one_mul] at hj
  subst hj
  have h1 : ((unitJ : unitary ℍ[ℝ]) : ℍ[ℝ]).imJ = 1 := rfl
  rw [h1] at hc
  exact one_ne_zero hc.1

/-- The common signature: the ray kernel against a fixed first argument. -/
abbrev signature : Signature where
  Params := unitary ℍ[ℝ]
  State _ := unitary ℍ[ℝ]
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ x s => rayKernel x s) (fun e => nomatch e)

/-- The ray kernel shifted by one. -/
def shifted : Realization signature :=
  realize signature (fun _ x s => rayKernel x s + 1) (fun e => nomatch e)

/-- The constant zero reading. -/
def constZero : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨1, 1, unitJ, rayKernel_one_ne⟩

/-! `rayKernel_eq_inner`. -/
namespace Inner

/-- Retain the complete argument telescope of `rayKernel_eq_inner`. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∀ x y : unitary ℍ[ℝ], r.readout () x y = ⟪(x : ℍ[ℝ]), (y : ℍ[ℝ])⟫_ℝ ^ 2 +
    ⟪(x : ℍ[ℝ]), (y : ℍ[ℝ]) * (unitI : ℍ[ℝ])⟫_ℝ ^ 2

theorem rejected_law : ¬ arena.Law shifted := by
  intro h
  have hh : rayKernel 1 1 + 1 = ⟪((1 : unitary ℍ[ℝ]) : ℍ[ℝ]), ((1 : unitary ℍ[ℝ]) : ℍ[ℝ])⟫_ℝ ^ 2 +
      ⟪((1 : unitary ℍ[ℝ]) : ℍ[ℝ]), ((1 : unitary ℍ[ℝ]) : ℍ[ℝ]) * (unitI : ℍ[ℝ])⟫_ℝ ^ 2 := h 1 1
  have ha := rayKernel_eq_inner 1 1
  linarith

def source_registration : Registration arena (type_of% @rayKernel_eq_inner) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@rayKernel_eq_inner, shifted, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨shifted, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

end Inner

/-! `rayKernel_eq_hopf`. -/
namespace Hopf

/-- Retain the complete argument telescope of `rayKernel_eq_hopf`. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∀ x y : unitary ℍ[ℝ], r.readout () x y = (1 + ⟪hopf x, hopf y⟫_ℝ) / 2

theorem rejected_law : ¬ arena.Law shifted := by
  intro h
  have hh : rayKernel 1 1 + 1 = (1 + ⟪hopf 1, hopf 1⟫_ℝ) / 2 := h 1 1
  have ha := rayKernel_eq_hopf 1 1
  linarith

def source_registration : Registration arena (type_of% @rayKernel_eq_hopf) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@rayKernel_eq_hopf, shifted, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨shifted, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

end Hopf

/-! `rayKernel_mul_phase_left`. -/
namespace PhaseLeft

/-- Retain the complete argument telescope of `rayKernel_mul_phase_left`. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∀ x y c : unitary ℍ[ℝ], (c : ℍ[ℝ]).imJ = 0 ∧ (c : ℍ[ℝ]).imK = 0 →
    rayKernel (x * c) y = r.readout () x y

theorem rejected_law : ¬ arena.Law shifted := by
  intro h
  have hh : rayKernel (1 * 1) 1 = rayKernel 1 1 + 1 := h 1 1 1 one_phase
  rw [mul_one] at hh
  linarith

def source_registration : Registration arena (type_of% @rayKernel_mul_phase_left) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@rayKernel_mul_phase_left, shifted, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨shifted, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

end PhaseLeft

/-! `rayKernel_mul_phase_right`. -/
namespace PhaseRight

/-- Retain the complete argument telescope of `rayKernel_mul_phase_right`. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∀ x y c : unitary ℍ[ℝ], (c : ℍ[ℝ]).imJ = 0 ∧ (c : ℍ[ℝ]).imK = 0 →
    rayKernel x (y * c) = r.readout () x y

theorem rejected_law : ¬ arena.Law shifted := by
  intro h
  have hh : rayKernel 1 (1 * 1) = rayKernel 1 1 + 1 := h 1 1 1 one_phase
  rw [mul_one] at hh
  linarith

def source_registration : Registration arena (type_of% @rayKernel_mul_phase_right) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@rayKernel_mul_phase_right, shifted, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨shifted, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

end PhaseRight

/-! `rayKernel_eq_one_iff`. -/
namespace Fiber

/-- Retain the complete argument telescope of `rayKernel_eq_one_iff`. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∀ x y : unitary ℍ[ℝ], r.readout () x y = 1 ↔
    ∃ c : unitary ℍ[ℝ], ((c : ℍ[ℝ]).imJ = 0 ∧ (c : ℍ[ℝ]).imK = 0) ∧ y = x * c

theorem rejected_law : ¬ arena.Law constZero := by
  intro h
  have hh : (0 : ℝ) = 1 := (h 1 1).2 ⟨1, one_phase, (mul_one 1).symm⟩
  norm_num at hh

def source_registration : Registration arena (type_of% @rayKernel_eq_one_iff) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@rayKernel_eq_one_iff, constZero, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨constZero, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

end Fiber

/-! `rayKernel_eq_bornProbability_spinor`, observed in its modulus conjunct. -/
namespace Spinor

/-- Retain the complete argument telescope and all four conjuncts of
`rayKernel_eq_bornProbability_spinor`. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∀ x y : unitary ℍ[ℝ],
    (∀ q : ℍ[ℝ], spinor (q * (unitI : ℍ[ℝ])) = Complex.I • spinor q) ∧
      bloch (Matrix.vecMulVec (spinor (x : ℍ[ℝ])).ofLp (star (spinor (x : ℍ[ℝ])).ofLp)) =
        WithLp.toLp 2 ![(hopf x).imK, (hopf x).imJ, (hopf x).imI] ∧
      r.readout () x y = ‖star (spinor (x : ℍ[ℝ])).ofLp ⬝ᵥ (spinor (y : ℍ[ℝ])).ofLp‖ ^ 2 ∧
      ((rayKernel x y : ℝ) : ℂ) =
        bornProbability
          (Matrix.vecMulVec (spinor (y : ℍ[ℝ])).ofLp (star (spinor (y : ℍ[ℝ])).ofLp))
          (Matrix.vecMulVec (spinor (x : ℍ[ℝ])).ofLp (star (spinor (x : ℍ[ℝ])).ofLp))

theorem rejected_law : ¬ arena.Law shifted := by
  intro h
  have hh : rayKernel 1 1 + 1 =
      ‖star (spinor ((1 : unitary ℍ[ℝ]) : ℍ[ℝ])).ofLp ⬝ᵥ
        (spinor ((1 : unitary ℍ[ℝ]) : ℍ[ℝ])).ofLp‖ ^ 2 := (h 1 1).2.2.1
  have ha := (rayKernel_eq_bornProbability_spinor 1 1).2.2.1
  linarith

def source_registration :
    Registration arena (type_of% @rayKernel_eq_bornProbability_spinor) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@rayKernel_eq_bornProbability_spinor, shifted, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨shifted, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

end Spinor

def rayKernel_eq_inner_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@rayKernel_eq_inner) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.AURICOmega.QuaternionRayKernel.rayKernel_eq_inner_unit
  realizationName := `Reg.D5.S3.Quantum.AURICOmega.QuaternionRayKernel.Inner.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨Inner.arena⟩
  objectArena := .source ⟨Inner.arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Inner.arena ⟨Inner.source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ x s => rayKernel x s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.AURICOmega.QuaternionRayKernel
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

def rayKernel_eq_hopf_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@rayKernel_eq_hopf) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.AURICOmega.QuaternionRayKernel.rayKernel_eq_hopf_unit
  realizationName := `Reg.D5.S3.Quantum.AURICOmega.QuaternionRayKernel.Hopf.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨Hopf.arena⟩
  objectArena := .source ⟨Hopf.arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Hopf.arena ⟨Hopf.source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ x s => rayKernel x s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.AURICOmega.QuaternionRayKernel
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

def rayKernel_mul_phase_left_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@rayKernel_mul_phase_left) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.AURICOmega.QuaternionRayKernel.rayKernel_mul_phase_left_unit
  realizationName := `Reg.D5.S3.Quantum.AURICOmega.QuaternionRayKernel.PhaseLeft.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨PhaseLeft.arena⟩
  objectArena := .source ⟨PhaseLeft.arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source PhaseLeft.arena ⟨PhaseLeft.source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ x s => rayKernel x s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.AURICOmega.QuaternionRayKernel
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

def rayKernel_mul_phase_right_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@rayKernel_mul_phase_right) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.AURICOmega.QuaternionRayKernel.rayKernel_mul_phase_right_unit
  realizationName := `Reg.D5.S3.Quantum.AURICOmega.QuaternionRayKernel.PhaseRight.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨PhaseRight.arena⟩
  objectArena := .source ⟨PhaseRight.arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source PhaseRight.arena ⟨PhaseRight.source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ x s => rayKernel x s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.AURICOmega.QuaternionRayKernel
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

def rayKernel_eq_one_iff_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@rayKernel_eq_one_iff) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.AURICOmega.QuaternionRayKernel.rayKernel_eq_one_iff_unit
  realizationName := `Reg.D5.S3.Quantum.AURICOmega.QuaternionRayKernel.Fiber.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨Fiber.arena⟩
  objectArena := .source ⟨Fiber.arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Fiber.arena ⟨Fiber.source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ x s => rayKernel x s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.AURICOmega.QuaternionRayKernel
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

def rayKernel_eq_bornProbability_spinor_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@rayKernel_eq_bornProbability_spinor) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.AURICOmega.QuaternionRayKernel.rayKernel_eq_bornProbability_spinor_unit
  realizationName := `Reg.D5.S3.Quantum.AURICOmega.QuaternionRayKernel.Spinor.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨Spinor.arena⟩
  objectArena := .source ⟨Spinor.arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Spinor.arena ⟨Spinor.source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ x s => rayKernel x s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.AURICOmega.QuaternionRayKernel
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "arg", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end

end Reg.D5.S3.Quantum.AURICOmega.QuaternionRayKernel
