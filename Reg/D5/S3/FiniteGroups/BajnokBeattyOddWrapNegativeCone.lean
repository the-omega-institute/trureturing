import LeanInformationAuditInterface.Contract.Registration
import D5.S3.FiniteGroups.BajnokBeattyOddWrapNegativeCone
import Reg.D5.S3.FiniteGroups.BajnokBeattyFirstReturnDefect
import Reg.Support.DependentFamily

/-! Faithful full-domain registration attempt for actual_negative_odd_wrap_cone.

The complete original integer telescope is p,t, 3<=p, Odd p, 2<=t,
and 25*t<=24*p.  Parameters retain exactly the admissible p values;
the dependent state subtype retains exactly the two original t constraints,
including equality at the cone boundary.  The Law supplies no threshold,
binomial estimate, count formula or comparison as an additional hypothesis.

Both roles read the public original_return_pair at exactly p,t, hence the
full original quotient maps and source length (p*(6*t-1)).toNat.  Variation
and sensitivity use the admissible state p=5,t=2: replace role 0 by zero,
or replace role 1 by actual role 0 plus one.  Each intervention preserves
the other role and the empty anchor family and contradicts the original
strict direction role 1 < role 0.

Actual observational dependence fixes p=5 and uses t=2,3.  Both states
satisfy 2<=t and 25*t<=24*p; the corresponding source lengths are 55,85.
The existing actual_odd_wrap_counts theorem supplies the exact binomial
counts without enumerating word fibers or assuming any new count formula.

sourceSelection and familyRecord remain none.  Checked binding to the
original component readout occurrences remains unfinished, tracked at
https://github.com/the-omega-institute/trureturing/issues/25856 .
No declared_validated source binding is claimed.
-/

namespace Reg.D5.S3.FiniteGroups.BajnokBeattyOddWrapNegativeCone

open _root_.D5.S3.FiniteGroups.BajnokBeattyOddWrapNegativeCone
open _root_.D5.S3.FiniteGroups.BajnokBeattyOddWrapSingleCrossing
open _root_.D5.S3.FiniteGroups.BajnokBeattyOddWrapReturnCounts
open _root_.Reg.D5.S3.FiniteGroups.BajnokBeattyFirstReturnDefect
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped Classical

abbrev negativeConeSignature : Signature where
  Params := {p : ℤ // 3 ≤ p ∧ Odd p}
  State p := {t : ℤ // 2 ≤ t ∧ 25*t ≤ 24*p.1}
  Role := Fin 2
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def negativeConeActual : Realization negativeConeSignature :=
  realize negativeConeSignature
    (fun i p t => if i = 0 then (original_return_pair p.1 t.1).1
      else (original_return_pair p.1 t.1).2)
    (fun e => nomatch e)

noncomputable def negativeConeRejected (i : Fin 2) :
    Realization negativeConeSignature :=
  realize negativeConeSignature
    (fun j p t => if j = i then
      (if j = 0 then 0 else negativeConeActual.readout 0 p t + 1)
      else negativeConeActual.readout j p t)
    (fun e => nomatch e)

abbrev negativeConeArena : Arena where
  signature := negativeConeSignature
  Law R := ∀ (p t : ℤ) (hp3 : 3 ≤ p) (hpo : Odd p)
      (ht2 : 2 ≤ t) (hcone : 25*t ≤ 24*p),
    let pp : negativeConeSignature.Params := ⟨p,hp3,hpo⟩
    let tt : negativeConeSignature.State pp := ⟨t,ht2,hcone⟩
    R.readout 1 pp tt < R.readout 0 pp tt

private theorem negativeCone_actual_law :
    negativeConeArena.Law negativeConeActual := by
  exact actual_negative_odd_wrap_cone

private theorem negativeCone_rejected_law (i : Fin 2) :
    ¬ negativeConeArena.Law (negativeConeRejected i) := by
  intro h
  have hh := h 5 2 (by norm_num) (by decide) (by norm_num) (by norm_num)
  fin_cases i
  · change (original_return_pair 5 2).2 < 0 at hh
    omega
  · change (original_return_pair 5 2).1 + 1 <
      (original_return_pair 5 2).1 at hh
    omega

set_option maxRecDepth 10000 in
private theorem negativeCone_actual_dependence :
    ObservationalDependence negativeConeSignature negativeConeActual := by
  intro i
  let p : negativeConeSignature.Params := ⟨5,by decide⟩
  refine ⟨p, ⟨2,by decide⟩, ⟨3,by decide⟩, ?_⟩
  have h55 := actual_odd_wrap_counts 5 2 (by norm_num) (by decide) (by norm_num)
  have h85 := actual_odd_wrap_counts 5 3 (by norm_num) (by decide) (by norm_num)
  fin_cases i
  · change returns19 5 2 55 ≠ returns19 5 3 85
    have hc55 : returns19 5 2 55 =
        2*(Nat.choose 55 30+Nat.choose 55 50) := h55.1
    have hc85 : returns19 5 3 85 =
        2*(Nat.choose 85 45+Nat.choose 85 65) := h85.1
    rw [hc55,hc85]
    norm_num [Nat.choose_eq_factorial_div_factorial (by decide : 30 ≤ 55),
      Nat.choose_eq_factorial_div_factorial (by decide : 50 ≤ 55),
      Nat.choose_eq_factorial_div_factorial (by decide : 45 ≤ 85),
      Nat.choose_eq_factorial_div_factorial (by decide : 65 ≤ 85), Nat.factorial]
  · change returns33 5 2 55 ≠ returns33 5 3 85
    have hc55 : returns33 5 2 55 = 4*Nat.choose 55 35 := h55.2
    have hc85 : returns33 5 3 85 = 4*Nat.choose 85 50 := h85.2
    rw [hc55,hc85]
    norm_num [Nat.choose_eq_factorial_div_factorial (by decide : 35 ≤ 55),
      Nat.choose_eq_factorial_div_factorial (by decide : 50 ≤ 85), Nat.factorial]

noncomputable def negativeConeSource : Registration negativeConeArena
    (type_of% actual_negative_odd_wrap_cone) where
  actual := negativeConeActual
  bridge := Iff.rfl
  variation := ⟨negativeCone_actual_law,
    negativeConeRejected 0, negativeCone_rejected_law 0⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨negativeConeRejected i, ?_, rfl, negativeCone_rejected_law i⟩
      intro j hj
      funext p t
      simp [negativeConeRejected, realize, hj]
    · intro e
      exact nomatch e
  dependence := negativeCone_actual_dependence

noncomputable def negativeConeRegistration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@actual_negative_odd_wrap_cone)
      (Realization negativeConeSignature) Unit Unit := {
  unitName := `D5.S3.FiniteGroups.BajnokBeattyOddWrapNegativeCone.actual_negative_odd_wrap_cone.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.BajnokBeattyOddWrapNegativeCone.negativeConeSource
  realizationSource := none
  generated := false
  arena := .source ⟨negativeConeArena⟩
  objectArena := .source ⟨negativeConeArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source negativeConeArena ⟨negativeConeSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize negativeConeSignature
    (fun i p t => if i = 0 then (original_return_pair p.1 t.1).1
      else (original_return_pair p.1 t.1).2)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.FiniteGroups.BajnokBeattyOddWrapNegativeCone
