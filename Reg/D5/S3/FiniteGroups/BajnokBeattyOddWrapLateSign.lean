import LeanInformationAuditInterface.Contract.Registration
import D5.S3.FiniteGroups.BajnokBeattyOddWrapLateSign
import Reg.D5.S3.FiniteGroups.BajnokBeattyFirstReturnDefect
import Reg.Support.DependentFamily

/-! Faithful Reg attempt for actual_late_odd_wrap_sign.
The parameter p and the dependent t-state retain exactly the original
p>=3, Odd p, t>=2 and 9*p+1<6*t domain.  The two observations are the
actual quotient return counts at the source length (p*(6*t-1)).toNat.
The Law retains the full original telescope and its strict comparison.

Variation and per-role sensitivity fail at the admissible p=3,t=6 state:
replace role 0 by actual role 1 plus one, or replace role 1 by zero.
Observational dependence holds at fixed p=3 and states t=6,7, hence
lengths 105,123 inside this same cone.  It evaluates the proved odd-wrap
binomial formulas and never enumerates word fibers.

sourceSelection and familyRecord remain none: checked binding to the
original W readout occurrences is unfinished, tracked at
https://github.com/the-omega-institute/trureturing/issues/25856 .
No declared_validated claim is made by this source attempt or by compilation.
-/

namespace Reg.D5.S3.FiniteGroups.BajnokBeattyOddWrapLateSign

open _root_.D5.S3.FiniteGroups.BajnokBeattyOddWrapLateSign
open _root_.D5.S3.FiniteGroups.BajnokBeattyOddWrapReturnCounts
open _root_.D5.S3.FiniteGroups.NearSquareLatticeRigidity
open _root_.Reg.D5.S3.FiniteGroups.BajnokBeattyFirstReturnDefect
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped Classical

abbrev lateSignSignature : Signature where
  Params := {p : ℤ // 3 ≤ p ∧ Odd p}
  State p := {t : ℤ // 2 ≤ t ∧ 9*p.1+1 < 6*t}
  Role := Fin 2
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def lateSignActual : Realization lateSignSignature :=
  realize lateSignSignature
    (fun i p t => actualReturn.readout i ⟨p.1,t.1⟩
      ((p.1*(6*t.1-1)).toNat))
    (fun e => nomatch e)

noncomputable def lateSignRejected (i : Fin 2) : Realization lateSignSignature :=
  realize lateSignSignature
    (fun j p t => if j = i then
      (if j = 0 then lateSignActual.readout 1 p t + 1 else 0)
      else lateSignActual.readout j p t)
    (fun e => nomatch e)

abbrev lateSignArena : Arena where
  signature := lateSignSignature
  Law R := ∀ (p t : ℤ) (hp3 : 3 ≤ p) (hpo : Odd p) (ht : 2 ≤ t)
      (hcone : 9*p+1 < 6*t),
    let m : ℤ := 6*t-1
    let v119 : Plane := ![p*(m-1)/2, p*(m+1)/2]
    let v219 : Plane := ![p*(m-9)/2, -(p*(m+9)/2)]
    let v133 : Plane := ![p*(m-3)/2, p*(m+3)/2]
    let v233 : Plane := ![p*(m-3)/2, -(p*(m+3)/2)]
    let K19 := Submodule.span ℤ (Set.range ![v119, v219])
    let K33 := Submodule.span ℤ (Set.range ![v133, v233])
    let F19 : Plane →+ (Plane ⧸ K19) := K19.mkQ.toAddMonoidHom
    let F33 : Plane →+ (Plane ⧸ K33) := K33.mkQ.toAddMonoidHom
    let L : ℕ := (p*m).toNat
    let pp : lateSignSignature.Params := ⟨p,hp3,hpo⟩
    let tt : lateSignSignature.State pp := ⟨t,ht,hcone⟩
    R.readout 0 pp tt < R.readout 1 pp tt

private theorem lateSign_actual_law : lateSignArena.Law lateSignActual := by
  exact actual_late_odd_wrap_sign

private theorem lateSign_rejected_law (i : Fin 2) :
    ¬ lateSignArena.Law (lateSignRejected i) := by
  intro h
  have hh := h 3 6 (by norm_num) (by decide) (by norm_num) (by norm_num)
  fin_cases i
  · change returns33 3 6 105 + 1 < returns33 3 6 105 at hh
    omega
  · change returns19 3 6 105 < 0 at hh
    omega

set_option maxRecDepth 10000 in
private theorem lateSign_actual_dependence :
    ObservationalDependence lateSignSignature lateSignActual := by
  intro i
  let p : lateSignSignature.Params := ⟨3,by decide⟩
  refine ⟨p, ⟨6,by decide⟩, ⟨7,by decide⟩, ?_⟩
  have h105 := actual_odd_wrap_counts 3 6 (by norm_num) (by decide) (by norm_num)
  have h123 := actual_odd_wrap_counts 3 7 (by norm_num) (by decide) (by norm_num)
  fin_cases i
  · change returns19 3 6 105 ≠ returns19 3 7 123
    have hc105 : returns19 3 6 105 =
        2*(Nat.choose 105 54+Nat.choose 105 66) := h105.1
    have hc123 : returns19 3 7 123 =
        2*(Nat.choose 123 63+Nat.choose 123 75) := h123.1
    rw [hc105,hc123]
    norm_num [Nat.choose_eq_factorial_div_factorial (by decide : 54 ≤ 105),
      Nat.choose_eq_factorial_div_factorial (by decide : 66 ≤ 105),
      Nat.choose_eq_factorial_div_factorial (by decide : 63 ≤ 123),
      Nat.choose_eq_factorial_div_factorial (by decide : 75 ≤ 123), Nat.factorial]
  · change returns33 3 6 105 ≠ returns33 3 7 123
    have hc105 : returns33 3 6 105 = 4*Nat.choose 105 57 := h105.2
    have hc123 : returns33 3 7 123 = 4*Nat.choose 123 66 := h123.2
    rw [hc105,hc123]
    norm_num [Nat.choose_eq_factorial_div_factorial (by decide : 57 ≤ 105),
      Nat.choose_eq_factorial_div_factorial (by decide : 66 ≤ 123), Nat.factorial]

noncomputable def lateSignSource : Registration lateSignArena
    (type_of% actual_late_odd_wrap_sign) where
  actual := lateSignActual
  bridge := Iff.rfl
  variation := ⟨lateSign_actual_law, lateSignRejected 0, lateSign_rejected_law 0⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨lateSignRejected i, ?_, rfl, lateSign_rejected_law i⟩
      intro j hj
      funext p t
      simp [lateSignRejected, realize, hj]
    · intro e
      exact nomatch e
  dependence := lateSign_actual_dependence

noncomputable def lateSignRegistration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@actual_late_odd_wrap_sign)
      (Realization lateSignSignature) Unit Unit := {
  unitName := `D5.S3.FiniteGroups.BajnokBeattyOddWrapLateSign.actual_late_odd_wrap_sign.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.BajnokBeattyOddWrapLateSign.lateSignSource
  realizationSource := none
  generated := false
  arena := .source ⟨lateSignArena⟩
  objectArena := .source ⟨lateSignArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source lateSignArena ⟨lateSignSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize lateSignSignature
    (fun i p t => actualReturn.readout i ⟨p.1,t.1⟩
      ((p.1*(6*t.1-1)).toNat))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.FiniteGroups.BajnokBeattyOddWrapLateSign
