import LeanInformationAuditInterface.Contract.Registration
import D5.S3.FiniteGroups.BajnokBeattyOddWrapEarlySign
import Reg.D5.S3.FiniteGroups.BajnokBeattyFirstReturnDefect
import Reg.Support.DependentFamily

/-! Faithful Reg attempt for actual_early_odd_wrap_sign.
The Unit parameter and pair state retain the full original domain:
p>=3, Odd p, t>=2, and 3*t<=2*p+1.  Both roles observe actualReturn
at the exact source length (p*(6*t-1)).toNat.  The Law retains the
complete p,t telescope, original quotient-map lets and role 1 < role 0.

Variation and sensitivity fail at the admissible state (p,t)=(3,2):
replace role 0 by zero, or role 1 by actual role 0 plus one.
Dependence uses admissible states (3,2),(5,2), giving actual lengths
33,55.  The existing actual_odd_wrap_counts supplier is evaluated at
these states; no private initial-sign Reg proof or word enumeration is used.

sourceSelection and familyRecord remain none.  Checked binding to the
original W occurrences is unfinished and tracked at
https://github.com/the-omega-institute/trureturing/issues/25856 .
No declared_validated status is claimed by this attempt or by compilation.
-/

namespace Reg.D5.S3.FiniteGroups.BajnokBeattyOddWrapEarlySign

open _root_.D5.S3.FiniteGroups.BajnokBeattyOddWrapEarlySign
open _root_.D5.S3.FiniteGroups.BajnokBeattyOddWrapReturnCounts
open _root_.D5.S3.FiniteGroups.NearSquareLatticeRigidity
open _root_.Reg.D5.S3.FiniteGroups.BajnokBeattyFirstReturnDefect
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped Classical

abbrev earlySignSignature : Signature where
  Params := Unit
  State _ := {q : ℤ × ℤ //
    3 ≤ q.1 ∧ Odd q.1 ∧ 2 ≤ q.2 ∧ 3*q.2 ≤ 2*q.1+1}
  Role := Fin 2
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def earlySignActual : Realization earlySignSignature :=
  realize earlySignSignature
    (fun i _ q => actualReturn.readout i ⟨q.1.1,q.1.2⟩
      ((q.1.1*(6*q.1.2-1)).toNat))
    (fun e => nomatch e)

noncomputable def earlySignRejected (i : Fin 2) : Realization earlySignSignature :=
  realize earlySignSignature
    (fun j u q => if j = i then
      (if j = 0 then 0 else earlySignActual.readout 0 u q + 1)
      else earlySignActual.readout j u q)
    (fun e => nomatch e)

abbrev earlySignArena : Arena where
  signature := earlySignSignature
  Law R := ∀ (p t : ℤ) (hp3 : 3 ≤ p) (hpo : Odd p) (ht : 2 ≤ t)
      (hcone : 3*t ≤ 2*p+1),
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
    let q : earlySignSignature.State () := ⟨(p,t),hp3,hpo,ht,hcone⟩
    R.readout 1 () q < R.readout 0 () q

private theorem earlySign_actual_law : earlySignArena.Law earlySignActual := by
  exact actual_early_odd_wrap_sign

private theorem earlySign_rejected_law (i : Fin 2) :
    ¬ earlySignArena.Law (earlySignRejected i) := by
  intro h
  have hh := h 3 2 (by norm_num) (by decide) (by norm_num) (by norm_num)
  fin_cases i
  · change returns33 3 2 33 < 0 at hh
    omega
  · change returns19 3 2 33 + 1 < returns19 3 2 33 at hh
    omega

set_option maxRecDepth 10000 in
private theorem earlySign_actual_dependence :
    ObservationalDependence earlySignSignature earlySignActual := by
  intro i
  refine ⟨(), ⟨(3,2),by decide⟩, ⟨(5,2),by decide⟩, ?_⟩
  have h33 := actual_odd_wrap_counts 3 2 (by norm_num) (by decide) (by norm_num)
  have h55 := actual_odd_wrap_counts 5 2 (by norm_num) (by decide) (by norm_num)
  fin_cases i
  · change returns19 3 2 33 ≠ returns19 5 2 55
    have hc33 : returns19 3 2 33 =
        2*(Nat.choose 33 18+Nat.choose 33 30) := h33.1
    have hc55 : returns19 5 2 55 =
        2*(Nat.choose 55 30+Nat.choose 55 50) := h55.1
    rw [hc33,hc55]
    norm_num [Nat.choose_eq_factorial_div_factorial (by decide : 18 ≤ 33),
      Nat.choose_eq_factorial_div_factorial (by decide : 30 ≤ 33),
      Nat.choose_eq_factorial_div_factorial (by decide : 30 ≤ 55),
      Nat.choose_eq_factorial_div_factorial (by decide : 50 ≤ 55), Nat.factorial]
  · change returns33 3 2 33 ≠ returns33 5 2 55
    have hc33 : returns33 3 2 33 = 4*Nat.choose 33 21 := h33.2
    have hc55 : returns33 5 2 55 = 4*Nat.choose 55 35 := h55.2
    rw [hc33,hc55]
    norm_num [Nat.choose_eq_factorial_div_factorial (by decide : 21 ≤ 33),
      Nat.choose_eq_factorial_div_factorial (by decide : 35 ≤ 55), Nat.factorial]

noncomputable def earlySignSource : Registration earlySignArena
    (type_of% actual_early_odd_wrap_sign) where
  actual := earlySignActual
  bridge := Iff.rfl
  variation := ⟨earlySign_actual_law, earlySignRejected 0, earlySign_rejected_law 0⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨earlySignRejected i, ?_, rfl, earlySign_rejected_law i⟩
      intro j hj
      funext u q
      simp [earlySignRejected, realize, hj]
    · intro e
      exact nomatch e
  dependence := earlySign_actual_dependence

noncomputable def earlySignRegistration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@actual_early_odd_wrap_sign)
      (Realization earlySignSignature) Unit Unit := {
  unitName := `D5.S3.FiniteGroups.BajnokBeattyOddWrapEarlySign.actual_early_odd_wrap_sign.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.BajnokBeattyOddWrapEarlySign.earlySignSource
  realizationSource := none
  generated := false
  arena := .source ⟨earlySignArena⟩
  objectArena := .source ⟨earlySignArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source earlySignArena ⟨earlySignSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize earlySignSignature
    (fun i _ q => actualReturn.readout i ⟨q.1.1,q.1.2⟩
      ((q.1.1*(6*q.1.2-1)).toNat))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.FiniteGroups.BajnokBeattyOddWrapEarlySign
