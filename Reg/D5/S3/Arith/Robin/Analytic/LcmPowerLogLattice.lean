import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.Analytic.LcmPowerLogLattice
import Reg.Support.SingleDependentReadout

/-! Full source telescopes for the logarithmic lattice observations. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Robin.Analytic.LcmPowerLogLattice

namespace Reg.D5.S3.Arith.Robin.Analytic.LcmPowerLogLattice

namespace IrrationalRatio

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℕ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ p q => Real.log (p : ℝ) / Real.log (q : ℝ))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {p q : ℕ}, p.Prime → q.Prime → p ≠ q → Irrational (R.readout () p q)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (p := 2) (q := 3) (by norm_num) (by norm_num) (by norm_num)
  exact not_irrational_zero hh

def family : Registration arena (type_of% @irrational_prime_log_ratio) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@irrational_prime_log_ratio, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨2, 1, 2, ?_⟩
    have hlog : Real.log (2 : ℝ) ≠ 0 := (Real.log_pos (by norm_num)).ne'
    norm_num [actual, realize, hlog]

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@irrational_prime_log_ratio) (Realization signature) Type Unit where
  unitName := `LcmPowerLogLattice.irrational_prime_log_ratio.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.LcmPowerLogLattice.IrrationalRatio.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p q => Real.log (p : ℝ) / Real.log (q : ℝ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℕ
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.Analytic.LcmPowerLogLattice
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end IrrationalRatio

namespace PositiveTail

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (ℝ × ℝ × ℝ × ℝ × ℕ)
    (fun _ => ℕ) (fun _ => Prop)

def actual : Realization signature :=
  realize signature (fun _ z i => ∃ j : ℕ, z.2.2.2.2 ≤ i ∧ z.2.2.2.2 ≤ j ∧
    z.2.2.1 < (i : ℝ) * z.1 - (j : ℝ) * z.2.1 ∧
    (i : ℝ) * z.1 - (j : ℝ) * z.2.1 < z.2.2.2.1) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {a b u v : ℝ}, 0 < a → 0 < b → Irrational (a / b) → u < v →
    ∀ N : ℕ, ∃ i : ℕ, R.readout () (a, b, u, v, N) i

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨i, hi⟩ := h (a := Real.sqrt 2) (b := 1) (u := 1) (v := 2)
    (Real.sqrt_pos.mpr (by norm_num)) (by norm_num)
    (by simpa using irrational_sqrt_two) (by norm_num) 0
  exact hi

def family : Registration arena (type_of% @positive_tail_lattice) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@positive_tail_lattice, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro role
    obtain ⟨i, j, hi, hj, hlo, hhi⟩ :=
      positive_tail_lattice (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))
        (by norm_num : (0 : ℝ) < 1) (by simpa using irrational_sqrt_two)
        (by norm_num : (1 : ℝ) < 2) 1
    refine ⟨(Real.sqrt 2, 1, 1, 2, 1), 0, i, ?_⟩
    intro heq
    have hyes : actual.readout role (Real.sqrt 2, 1, 1, 2, 1) i :=
      ⟨j, hi, hj, hlo, hhi⟩
    have hno : ¬ actual.readout role (Real.sqrt 2, 1, 1, 2, 1) 0 := by
      simp [actual, realize]
    exact hno (Eq.mpr heq hyes)

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@positive_tail_lattice) (Realization signature) Type Unit where
  unitName := `LcmPowerLogLattice.positive_tail_lattice.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.LcmPowerLogLattice.PositiveTail.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ z i => ∃ j : ℕ,
    z.2.2.2.2 ≤ i ∧ z.2.2.2.2 ≤ j ∧
    z.2.2.1 < (i : ℝ) * z.1 - (j : ℝ) * z.2.1 ∧
    (i : ℝ) * z.1 - (j : ℝ) * z.2.1 < z.2.2.2.1) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℕ
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.Analytic.LcmPowerLogLattice
    definition := none
    coordinates := #[0, 1, 2, 3, 8]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "body"]
      stateBinder := 9
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end PositiveTail

namespace PrimeTail

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (ℕ × ℕ × ℝ × ℝ × ℕ)
    (fun _ => ℕ) (fun _ => Prop)

def actual : Realization signature :=
  realize signature (fun _ z i => ∃ j : ℕ, z.2.2.2.2 ≤ i ∧ z.2.2.2.2 ≤ j ∧
    z.2.2.1 < (i : ℝ) * Real.log (z.1 : ℝ) - (j : ℝ) * Real.log (z.2.1 : ℝ) ∧
    (i : ℝ) * Real.log (z.1 : ℝ) - (j : ℝ) * Real.log (z.2.1 : ℝ) < z.2.2.2.1)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {p q : ℕ}, p.Prime → q.Prime → p ≠ q → ∀ {u v : ℝ}, u < v →
    ∀ N : ℕ, ∃ i : ℕ, R.readout () (p, q, u, v, N) i

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨i, hi⟩ := h (p := 2) (q := 3) (by norm_num) (by norm_num) (by norm_num)
    (u := 1) (v := 2) (by norm_num) 0
  exact hi

def family : Registration arena (type_of% @prime_log_lattice_tail) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@prime_log_lattice_tail, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro role
    obtain ⟨i, j, hi, hj, hlo, hhi⟩ :=
      prime_log_lattice_tail (p := 2) (q := 3) (by norm_num) (by norm_num)
        (by norm_num) (u := 1) (v := 2) (by norm_num) 1
    refine ⟨(2, 3, 1, 2, 1), 0, i, ?_⟩
    intro heq
    have hyes : actual.readout role (2, 3, 1, 2, 1) i := ⟨j, hi, hj, hlo, hhi⟩
    have hno : ¬ actual.readout role (2, 3, 1, 2, 1) 0 := by
      simp [actual, realize]
    exact hno (Eq.mpr heq hyes)

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@prime_log_lattice_tail) (Realization signature) Type Unit where
  unitName := `LcmPowerLogLattice.prime_log_lattice_tail.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.LcmPowerLogLattice.PrimeTail.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ z i => ∃ j : ℕ,
    z.2.2.2.2 ≤ i ∧ z.2.2.2.2 ≤ j ∧
    z.2.2.1 < (i : ℝ) * Real.log (z.1 : ℝ) - (j : ℝ) * Real.log (z.2.1 : ℝ) ∧
    (i : ℝ) * Real.log (z.1 : ℝ) - (j : ℝ) * Real.log (z.2.1 : ℝ) < z.2.2.2.1)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℕ
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.Analytic.LcmPowerLogLattice
    definition := none
    coordinates := #[0, 1, 5, 6, 8]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "body"]
      stateBinder := 9
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end PrimeTail
end Reg.D5.S3.Arith.Robin.Analytic.LcmPowerLogLattice
