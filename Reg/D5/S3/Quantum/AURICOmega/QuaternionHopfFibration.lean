import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.AURICOmega.QuaternionHopfFibration
import Reg.D5.S3.Quantum.AURICOmega.QuaternionRayKernel
import Reg.Support.DependentFamily

/-! Source-bound audits of the Hopf map on the unit quaternions: its range, the homeomorphism
from the quotient by the phase circle, and the extremum and mean of the reading over a fibre. -/

namespace Reg.D5.S3.Quantum.AURICOmega.QuaternionHopfFibration

open _root_.D5.S3.Quantum.AURICOmega.QuaternionComparisonModel
open _root_.D5.S3.Quantum.AURICOmega.QuaternionRayKernel
open _root_.D5.S3.Quantum.AURICOmega.QuaternionHopfFibration
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

open scoped InnerProductSpace Quaternion

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false
noncomputable section

/-! `range_hopf`: the range of a map from the unit quaternions. -/
namespace Range

abbrev signature : Signature where
  Params := Unit
  State _ := unitary ℍ[ℝ] → ℍ[ℝ]
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Set ℍ[ℝ]
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ f => Set.range f) (fun e => nomatch e)

/-- The reading that returns every quaternion. -/
def rejected : Realization signature :=
  realize signature (fun _ _ _ => Set.univ) (fun e => nomatch e)

/-- Retain the complete statement of `range_hopf`; only the range of the Hopf map is read out. -/
abbrev arena : Arena where
  signature := signature
  Law r := r.readout () () hopf = {n : ℍ[ℝ] | n.re = 0 ∧ ‖n‖ = 1}

/-- The quaternion `1` is not imaginary. -/
theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h1 : (1 : ℍ[ℝ]) ∈ ({n : ℍ[ℝ] | n.re = 0 ∧ ‖n‖ = 1} : Set ℍ[ℝ]) := by
    rw [← h]
    exact Set.mem_univ _
  have h2 : (1 : ℍ[ℝ]).re = 0 := h1.1
  rw [Quaternion.re_one] at h2
  exact one_ne_zero h2

/-- The ranges of the constant maps `0` and `1` differ. -/
theorem dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨(), fun _ => 0, fun _ => 1, ?_⟩
  change Set.range (fun _ : unitary ℍ[ℝ] => (0 : ℍ[ℝ])) ≠
    Set.range (fun _ : unitary ℍ[ℝ] => (1 : ℍ[ℝ]))
  rw [Set.range_const, Set.range_const]
  intro h
  exact zero_ne_one (Set.singleton_eq_singleton_iff.mp h)

/-- The exact statement of the source theorem. -/
abbrev sourceStatement : Prop := type_of% @range_hopf

def source_registration : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@range_hopf, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

end Range

/-! `exists_homeomorph_quotient_phaseCircle`: the map read on each unit quaternion. -/
namespace Homeo

abbrev signature : Signature where
  Params := Unit
  State _ := unitary ℍ[ℝ]
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℍ[ℝ]
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ s => hopf s) (fun e => nomatch e)

/-- The constant reading `0`. -/
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Retain the complete statement of `exists_homeomorph_quotient_phaseCircle`; only the
quaternion that the homeomorphism must match on the class of `x` is read out. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∃ e : (unitary ℍ[ℝ] ⧸ phaseCircle) ≃ₜ {n : ℍ[ℝ] // n.re = 0 ∧ ‖n‖ = 1},
    ∀ x : unitary ℍ[ℝ], ((e (x : unitary ℍ[ℝ] ⧸ phaseCircle)) : ℍ[ℝ]) = r.readout () () x

/-- A point of the unit imaginary sphere is not `0`. -/
theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨e, he⟩ := h
  have h1 := (e ((1 : unitary ℍ[ℝ]) : unitary ℍ[ℝ] ⧸ phaseCircle)).2.2
  have h2 : ((e ((1 : unitary ℍ[ℝ]) : unitary ℍ[ℝ] ⧸ phaseCircle)) : ℍ[ℝ]) = 0 := he 1
  rw [h2, norm_zero] at h1
  exact zero_ne_one h1

/-- The Hopf images of `1` and `j` are `i` and `-i`. -/
theorem dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨(), 1, unitJ, ?_⟩
  intro h
  have h' := congrArg (fun q : ℍ[ℝ] => q.imI) h
  change (((1 : unitary ℍ[ℝ]) : ℍ[ℝ]) * (unitI : ℍ[ℝ]) * star ((1 : unitary ℍ[ℝ]) : ℍ[ℝ])).imI =
    ((unitJ : ℍ[ℝ]) * (unitI : ℍ[ℝ]) * star (unitJ : ℍ[ℝ])).imI at h'
  have hI : ((unitI : unitary ℍ[ℝ]) : ℍ[ℝ]) = ⟨0, 1, 0, 0⟩ := rfl
  have hJ : ((unitJ : unitary ℍ[ℝ]) : ℍ[ℝ]) = ⟨0, 0, 1, 0⟩ := rfl
  rw [hI, hJ, OneMemClass.coe_one] at h'
  simp only [Quaternion.imI_mul, Quaternion.re_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
    Quaternion.re_star, Quaternion.imI_star, Quaternion.imJ_star, Quaternion.imK_star,
    Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one, Quaternion.imK_one] at h'
  norm_num at h'

/-- The exact statement of the source theorem. -/
abbrev sourceStatement : Prop := type_of% @exists_homeomorph_quotient_phaseCircle

def source_registration : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_homeomorph_quotient_phaseCircle, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

end Homeo

/-! `rayKernel_isGreatest_and_integral`, observed in its integral conjunct through the ray kernel
against a fixed first argument (signature and realizations of the ray-kernel mirror). -/
namespace Fibre

open Reg.D5.S3.Quantum.AURICOmega.QuaternionRayKernel (signature actual shifted dependence)

/-- Retain the complete argument telescope and all three conjuncts of
`rayKernel_isGreatest_and_integral`; only the value on the right of the integral identity is read
out. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∀ x y : unitary ℍ[ℝ],
    IsGreatest {r | ∃ c ∈ phaseCircle,
        r = quaternionModel.kappa y (quaternionModel.tri (x * c) y (x * c))} (rayKernel x y) ∧
      IsGreatest {r | ∃ c ∈ phaseCircle,
        r = (2 * quaternionModel.kappa (x * c) y - 1) ^ 2} (rayKernel x y) ∧
      ∫ χ in (0 : ℝ)..(2 * Real.pi),
          ⟪(x : ℍ[ℝ]) * ⟨Real.cos χ, Real.sin χ, 0, 0⟩, (y : ℍ[ℝ])⟫_ℝ ^ 2 =
        Real.pi * r.readout () x y

/-- Shifting the ray kernel by one would add `π` to the integral. -/
theorem rejected_law : ¬ arena.Law shifted := by
  intro h
  have hh : ∫ χ in (0 : ℝ)..(2 * Real.pi),
      ⟪((1 : unitary ℍ[ℝ]) : ℍ[ℝ]) * ⟨Real.cos χ, Real.sin χ, 0, 0⟩,
        ((1 : unitary ℍ[ℝ]) : ℍ[ℝ])⟫_ℝ ^ 2 = Real.pi * (rayKernel 1 1 + 1) := (h 1 1).2.2
  have ha := (rayKernel_isGreatest_and_integral 1 1).2.2
  have hpi := Real.pi_pos
  linarith

/-- The exact statement of the source theorem. -/
abbrev sourceStatement : Prop := type_of% @rayKernel_isGreatest_and_integral

def source_registration : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@rayKernel_isGreatest_and_integral, shifted, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨shifted, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

end Fibre

def range_hopf_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@range_hopf) (Realization Range.signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.AURICOmega.QuaternionHopfFibration.range_hopf_unit
  realizationName := `Reg.D5.S3.Quantum.AURICOmega.QuaternionHopfFibration.Range.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨Range.arena⟩
  objectArena := .source ⟨Range.arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Range.arena ⟨Range.source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize Range.signature (fun _ _ f => Set.range f) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.AURICOmega.QuaternionHopfFibration
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

def exists_homeomorph_quotient_phaseCircle_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@exists_homeomorph_quotient_phaseCircle) (Realization Homeo.signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.AURICOmega.QuaternionHopfFibration.exists_homeomorph_quotient_phaseCircle_unit
  realizationName := `Reg.D5.S3.Quantum.AURICOmega.QuaternionHopfFibration.Homeo.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨Homeo.arena⟩
  objectArena := .source ⟨Homeo.arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Homeo.arena ⟨Homeo.source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize Homeo.signature (fun _ _ s => hopf s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.AURICOmega.QuaternionHopfFibration
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

def rayKernel_isGreatest_and_integral_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@rayKernel_isGreatest_and_integral)
      (Realization Reg.D5.S3.Quantum.AURICOmega.QuaternionRayKernel.signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.AURICOmega.QuaternionHopfFibration.rayKernel_isGreatest_and_integral_unit
  realizationName := `Reg.D5.S3.Quantum.AURICOmega.QuaternionHopfFibration.Fibre.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨Fibre.arena⟩
  objectArena := .source ⟨Fibre.arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Fibre.arena ⟨Fibre.source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize Reg.D5.S3.Quantum.AURICOmega.QuaternionRayKernel.signature
    (fun _ x s => rayKernel x s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.AURICOmega.QuaternionHopfFibration
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "arg", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Quantum.AURICOmega.QuaternionHopfFibration
