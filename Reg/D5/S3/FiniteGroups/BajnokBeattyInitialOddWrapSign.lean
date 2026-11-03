import LeanInformationAuditInterface.Contract.Registration
import D5.S3.FiniteGroups.BajnokBeattyInitialOddWrapSign
import Reg.D5.S3.FiniteGroups.BajnokBeattyFirstReturnDefect
import Reg.Support.DependentFamily

/-! Faithful Reg attempt for actual_initial_odd_wrap_sign.
The sole state coordinate is the original integer p with exactly p>=3 and
Odd p; t is fixed at the source value 2.  Both roles observe actualReturn
at length (11*p).toNat.  The Law retains the full original p telescope,
the original quotient-map lets, and the source direction role 1 < role 0.

Variation and per-role sensitivity fail at p=3: replace role 0 by zero,
or replace role 1 by actual role 0 plus one.  Observational dependence
uses states p=3,5, hence actual lengths 33,55 at t=2.  The already proved
odd-wrap binomial formulas supply these counts without word enumeration.

sourceSelection and familyRecord remain none: checked binding to the
original W readout occurrences is unfinished, tracked at
https://github.com/the-omega-institute/trureturing/issues/25856 .
No declared_validated status is claimed by this attempt or by compilation.
-/

namespace Reg.D5.S3.FiniteGroups.BajnokBeattyInitialOddWrapSign

open _root_.D5.S3.FiniteGroups.BajnokBeattyInitialOddWrapSign
open _root_.D5.S3.FiniteGroups.BajnokBeattyOddWrapReturnCounts
open _root_.D5.S3.FiniteGroups.NearSquareLatticeRigidity
open _root_.Reg.D5.S3.FiniteGroups.BajnokBeattyFirstReturnDefect
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped Classical

abbrev initialSignSignature : Signature where
  Params := Unit
  State _ := {p : ℤ // 3 ≤ p ∧ Odd p}
  Role := Fin 2
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def initialSignActual : Realization initialSignSignature :=
  realize initialSignSignature
    (fun i _ p => actualReturn.readout i ⟨p.1,2⟩ ((11*p.1).toNat))
    (fun e => nomatch e)

noncomputable def initialSignRejected (i : Fin 2) : Realization initialSignSignature :=
  realize initialSignSignature
    (fun j u p => if j = i then
      (if j = 0 then 0 else initialSignActual.readout 0 u p + 1)
      else initialSignActual.readout j u p)
    (fun e => nomatch e)

abbrev initialSignArena : Arena where
  signature := initialSignSignature
  Law R := ∀ (p : ℤ) (hp3 : 3 ≤ p) (hpo : Odd p),
    let m : ℤ := 11
    let v119 : Plane := ![p*(m-1)/2, p*(m+1)/2]
    let v219 : Plane := ![p*(m-9)/2, -(p*(m+9)/2)]
    let v133 : Plane := ![p*(m-3)/2, p*(m+3)/2]
    let v233 : Plane := ![p*(m-3)/2, -(p*(m+3)/2)]
    let K19 := Submodule.span ℤ (Set.range ![v119, v219])
    let K33 := Submodule.span ℤ (Set.range ![v133, v233])
    let F19 : Plane →+ (Plane ⧸ K19) := K19.mkQ.toAddMonoidHom
    let F33 : Plane →+ (Plane ⧸ K33) := K33.mkQ.toAddMonoidHom
    let pp : initialSignSignature.State () := ⟨p,hp3,hpo⟩
    R.readout 1 () pp < R.readout 0 () pp

private theorem initialSign_actual_law : initialSignArena.Law initialSignActual := by
  exact actual_initial_odd_wrap_sign

private theorem initialSign_rejected_law (i : Fin 2) :
    ¬ initialSignArena.Law (initialSignRejected i) := by
  intro h
  have hh := h 3 (by norm_num) (by decide)
  fin_cases i
  · change returns33 3 2 33 < 0 at hh
    omega
  · change returns19 3 2 33 + 1 < returns19 3 2 33 at hh
    omega

set_option maxRecDepth 10000 in
private theorem initialSign_actual_dependence :
    ObservationalDependence initialSignSignature initialSignActual := by
  intro i
  refine ⟨(), ⟨3,by decide⟩, ⟨5,by decide⟩, ?_⟩
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

noncomputable def initialSignSource : Registration initialSignArena
    (type_of% actual_initial_odd_wrap_sign) where
  actual := initialSignActual
  bridge := Iff.rfl
  variation := ⟨initialSign_actual_law, initialSignRejected 0, initialSign_rejected_law 0⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨initialSignRejected i, ?_, rfl, initialSign_rejected_law i⟩
      intro j hj
      funext u p
      simp [initialSignRejected, realize, hj]
    · intro e
      exact nomatch e
  dependence := initialSign_actual_dependence

noncomputable def initialSignRegistration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@actual_initial_odd_wrap_sign)
      (Realization initialSignSignature) Unit Unit := {
  unitName := `D5.S3.FiniteGroups.BajnokBeattyInitialOddWrapSign.actual_initial_odd_wrap_sign.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.BajnokBeattyInitialOddWrapSign.initialSignSource
  realizationSource := none
  generated := false
  arena := .source ⟨initialSignArena⟩
  objectArena := .source ⟨initialSignArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source initialSignArena ⟨initialSignSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize initialSignSignature
    (fun i _ p => actualReturn.readout i ⟨p.1,2⟩ ((11*p.1).toNat))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.FiniteGroups.BajnokBeattyInitialOddWrapSign
