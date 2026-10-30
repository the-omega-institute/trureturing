import Reg.D5.S3.Analytic.BesselRedheffer.Series
import D5.S3.Analytic.BesselRedheffer.FirstZero

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Analytic.BesselRedheffer.Defs
open _root_.D5.S3.Analytic.BesselRedheffer.Series
open _root_.D5.S3.Analytic.BesselRedheffer.FirstZero
open _root_.Reg.D5.S3.Analytic.BesselRedheffer.Series
open LeanInformationAudit Filter Topology Set

noncomputable section
namespace Reg.D5.S3.Analytic.BesselRedheffer.FirstZero

abbrev zeroSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)
def zeroActual : Realization zeroSignature :=
  realize zeroSignature (fun _ _ ν => firstZero ν) (fun e => nomatch e)
def zeroRejected : Realization zeroSignature :=
  realize zeroSignature (fun _ _ _ => 0) (fun e => nomatch e)
def largeRejected : Realization zeroSignature :=
  realize zeroSignature (fun _ _ _ => 10000) (fun e => nomatch e)

private theorem firstZero_neg_one : firstZero (-1) = 0 := by
  have he (x : ℝ) : nbessel (-1) x = 1 := by
    rw [nbessel, tsum_eq_single 0]
    · simp
    · intro n hn
      cases n with
      | zero => exact (hn rfl).elim
      | succ n => simp [ascPochhammer_succ_left, Polynomial.eval_comp]
  have hs : {x : ℝ | 0 < x ∧ nbessel (-1) x = 0} = ∅ := by
    ext x
    simp [he]
  simp [firstZero, hs]

private theorem zero_dependence : ObservationalDependence zeroSignature zeroActual := by
  intro i
  refine ⟨(), -1, 30, ?_⟩
  change firstZero (-1) ≠ firstZero 30
  rw [firstZero_neg_one]
  exact (firstZero_pos (ν := 30) (by norm_num)).ne

namespace Positive

def arena : Arena where
  signature := zeroSignature
  Law R := ∀ {ν : ℝ} (_hν : 30 ≤ ν), 0 < R.readout () () ν
private theorem rejected_law : ¬ arena.Law zeroRejected := by
  intro h
  have H := @h 30 (by norm_num)
  norm_num [zeroRejected, realize] at H
def family : Registration arena (type_of% (@firstZero_pos)) where
  actual := zeroActual
  bridge := Iff.rfl
  variation := ⟨@firstZero_pos, zeroRejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law zeroActual zeroRejected rejected_law
  dependence := zero_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@firstZero_pos) (Realization zeroSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.BesselRedheffer.FirstZero.Positive.unit
  realizationName := `Reg.D5.S3.Analytic.BesselRedheffer.FirstZero.Positive.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize zeroSignature (fun _ _ ν => firstZero ν) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.BesselRedheffer.FirstZero
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Positive

namespace UpperBound

def arena : Arena where
  signature := zeroSignature
  Law R := ∀ {ν : ℝ} (_hν : 30 ≤ ν),
    (R.readout () () ν) ^ 2 ≤ (6 : ℝ) / 5 * (ν + 1) * (ν + 7)
private theorem rejected_law : ¬ arena.Law largeRejected := by
  intro h
  have H := @h 30 (by norm_num)
  norm_num [largeRejected, realize] at H
def family : Registration arena (type_of% (@firstZero_sq_le)) where
  actual := zeroActual
  bridge := Iff.rfl
  variation := ⟨@firstZero_sq_le, largeRejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law zeroActual largeRejected rejected_law
  dependence := zero_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@firstZero_sq_le) (Realization zeroSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.BesselRedheffer.FirstZero.UpperBound.unit
  realizationName := `Reg.D5.S3.Analytic.BesselRedheffer.FirstZero.UpperBound.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize zeroSignature (fun _ _ ν => firstZero ν) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.BesselRedheffer.FirstZero
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end UpperBound

namespace Attainment

def arena : Arena where
  signature := signature
  Law R := ∀ {ν : ℝ} (_hν : 30 ≤ ν),
    R.readout () ν (firstZero ν) = 0
private theorem rejected_law : ¬ arena.Law oneReadout := by
  intro h
  have H := @h 30 (by norm_num)
  norm_num [oneReadout, realize] at H
def family : Registration arena (type_of% (@nbessel_firstZero)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@nbessel_firstZero, oneReadout, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual oneReadout rejected_law
  dependence := actual_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@nbessel_firstZero) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.BesselRedheffer.FirstZero.Attainment.unit
  realizationName := `Reg.D5.S3.Analytic.BesselRedheffer.FirstZero.Attainment.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ ν x => nbessel ν x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.BesselRedheffer.FirstZero
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
  options := #[]
end Attainment

namespace IntervalPositive

def arena : Arena where
  signature := signature
  Law R := ∀ {ν x : ℝ} (_hν : -1 < ν) (_hx : 0 ≤ x) (_hxj : x < firstZero ν),
    0 < R.readout () ν x
private theorem rejected_law : ¬ arena.Law zeroReadout := by
  intro h
  have H := @h 30 0 (by norm_num) (by norm_num) (firstZero_pos (by norm_num))
  norm_num [zeroReadout, realize] at H
def family : Registration arena (type_of% (@nbessel_pos_of_lt)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@nbessel_pos_of_lt, zeroReadout, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual zeroReadout rejected_law
  dependence := actual_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@nbessel_pos_of_lt) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.BesselRedheffer.FirstZero.IntervalPositive.unit
  realizationName := `Reg.D5.S3.Analytic.BesselRedheffer.FirstZero.IntervalPositive.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ ν x => nbessel ν x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.BesselRedheffer.FirstZero
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end IntervalPositive

namespace Energy

def arena : Arena where
  signature := signature
  Law R := ∀ {ν z : ℝ} (_hν : 30 ≤ ν) (_hz : 0 < z)
    (_hpos : ∀ x ∈ Icc (0 : ℝ) z, 0 < R.readout () ν x),
    z ^ 2 ≤ (6 : ℝ) / 5 * (ν + 1) * (ν + 7)
private theorem rejected_law : ¬ arena.Law oneReadout := by
  intro h
  have H := @h 30 100 (by norm_num) (by norm_num) (by
    intro x hx
    norm_num [oneReadout, realize])
  norm_num at H
def family : Registration arena (type_of% (@nbessel_energy_bound)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@nbessel_energy_bound, oneReadout, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual oneReadout rejected_law
  dependence := actual_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@nbessel_energy_bound) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.BesselRedheffer.FirstZero.Energy.unit
  realizationName := `Reg.D5.S3.Analytic.BesselRedheffer.FirstZero.Energy.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ ν x => nbessel ν x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.BesselRedheffer.FirstZero
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "domain", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Energy

end Reg.D5.S3.Analytic.BesselRedheffer.FirstZero
