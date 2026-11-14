import D5.S1.Recurrence.Parity.DiagonalIterateEven
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

open PowerSeries
open _root_.D5.S1.Recurrence.Parity.DiagonalIterateEven
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S1.Recurrence.Parity.DiagonalIterateEven
noncomputable section

namespace HZero

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => PowerSeries (ZMod 2)) (fun _ => ZMod 2)

def actual : Realization signature :=
  realize signature (fun _ _ u => constantCoeff u) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := r.readout () () H = 0

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he : (1 : ZMod 2) = 0 := h
  exact one_ne_zero he

def family : Registration arena (type_of% @H_zero) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨H_zero, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change constantCoeff (0 : PowerSeries (ZMod 2)) ≠ constantCoeff 1
    simp

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@H_zero) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S1.Recurrence.Parity.DiagonalIterateEven.HZero.unit
  realizationName := `Reg.D5.S1.Recurrence.Parity.DiagonalIterateEven.HZero.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ u => constantCoeff u) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit

end HZero

namespace HQuadratic

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => PowerSeries (ZMod 2)) (fun _ => PowerSeries (ZMod 2))

def actual : Realization signature :=
  realize signature (fun _ _ u => u + u ^ 2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := r.readout () () H = X

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he : (0 : PowerSeries (ZMod 2)) = X := h
  have hc := congrArg (coeff 1) he
  simpa using hc

def family : Registration arena (type_of% @H_quadratic) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨H_quadratic, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, X, ?_⟩
    intro he
    have hc := congrArg (coeff 1) he
    change coeff 1 ((0 : PowerSeries (ZMod 2)) + 0 ^ 2) =
      coeff 1 ((X : PowerSeries (ZMod 2)) + X ^ 2) at hc
    have hx : coeff 1 ((X : PowerSeries (ZMod 2)) ^ 2) = 0 :=
      (coeff_X_pow 1 2).trans (if_neg (by decide))
    simp only [map_add, map_zero, zero_pow (by decide : 2 ≠ 0),
      coeff_one_X, hx, add_zero, zero_add] at hc
    exact zero_ne_one hc

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@H_quadratic) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S1.Recurrence.Parity.DiagonalIterateEven.HQuadratic.unit
  realizationName := `Reg.D5.S1.Recurrence.Parity.DiagonalIterateEven.HQuadratic.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ u => u + u ^ 2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit

end HQuadratic

namespace ModTwoIdentity

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => PowerSeries ℤ) (fun _ => PowerSeries (ZMod 2))

def actual : Realization signature :=
  realize signature (fun _ _ u => u.map (Int.castRingHom (ZMod 2))) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := r.readout () () generatingSeries = H

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he : (0 : PowerSeries (ZMod 2)) = H := h
  have hh := H_quadratic
  rw [← he] at hh
  have hc := congrArg (coeff 1) hh
  simpa using hc

def family : Registration arena (type_of% @mod_two_identity) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨mod_two_identity, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, X, ?_⟩
    intro he
    have hc := congrArg (coeff 1) he
    change coeff 1 ((0 : PowerSeries ℤ).map (Int.castRingHom (ZMod 2))) =
      coeff 1 ((X : PowerSeries ℤ).map (Int.castRingHom (ZMod 2))) at hc
    simp at hc

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@mod_two_identity) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S1.Recurrence.Parity.DiagonalIterateEven.ModTwoIdentity.unit
  realizationName := `Reg.D5.S1.Recurrence.Parity.DiagonalIterateEven.ModTwoIdentity.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ u => u.map (Int.castRingHom (ZMod 2))) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit

end ModTwoIdentity

end
end Reg.D5.S1.Recurrence.Parity.DiagonalIterateEven
