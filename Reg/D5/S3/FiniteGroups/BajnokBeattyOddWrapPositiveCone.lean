import LeanInformationAuditInterface.Contract.Registration
import D5.S3.FiniteGroups.BajnokBeattyOddWrapPositiveCone
import Reg.D5.S3.FiniteGroups.BajnokBeattyFirstReturnDefect
import Reg.Support.DependentFamily

/-! Faithful full-domain registration attempt for actual_positive_odd_wrap_cone.

This source expects the source-owner theorem with the original complete
integer telescope p,t, 5<=p, Odd p, and p<=t.  The parameter subtype retains
exactly the admissible p values and its dependent state subtype retains
exactly the original admissible integer t values.  The Law supplies no
threshold, binomial bound, count formula or comparison hypothesis.

Both roles read the public original_return_pair at exactly p,t, hence the
complete original quotient maps and source length (p*(6*t-1)).toNat.
Variation and sensitivity use the admissible p=5,t=5 fiber: replace role 0
by actual role 1 plus one, or replace role 1 by zero.  Each intervention
preserves the other role and the empty anchor family and contradicts the
original strict comparison role 0 < role 1.

Observational dependence fixes p=5 and uses states t=5,6, whose actual source
lengths are 145,175.  The existing exact odd-wrap count theorem supplies the
binomial formulas for these states; no word fibers are enumerated.

sourceSelection and familyRecord remain none.  Checked binding to the
original component readout occurrences remains unfinished, tracked at
https://github.com/the-omega-institute/trureturing/issues/25856 .
The compiled mathematical evidence does not claim declared_validated binding.
-/

namespace Reg.D5.S3.FiniteGroups.BajnokBeattyOddWrapPositiveCone

open _root_.D5.S3.FiniteGroups.BajnokBeattyOddWrapPositiveCone
open _root_.D5.S3.FiniteGroups.BajnokBeattyOddWrapSingleCrossing
open _root_.D5.S3.FiniteGroups.BajnokBeattyOddWrapReturnCounts
open _root_.Reg.D5.S3.FiniteGroups.BajnokBeattyFirstReturnDefect
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped Classical

abbrev positiveConeSignature : Signature where
  Params := {p : ℤ // 5 ≤ p ∧ Odd p}
  State p := {t : ℤ // p.1 ≤ t}
  Role := Fin 2
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def positiveConeActual : Realization positiveConeSignature :=
  realize positiveConeSignature
    (fun i p t => if i = 0 then (original_return_pair p.1 t.1).1
      else (original_return_pair p.1 t.1).2)
    (fun e => nomatch e)

noncomputable def positiveConeRejected (i : Fin 2) :
    Realization positiveConeSignature :=
  realize positiveConeSignature
    (fun j p t => if j = i then
      (if j = 0 then positiveConeActual.readout 1 p t + 1 else 0)
      else positiveConeActual.readout j p t)
    (fun e => nomatch e)

abbrev positiveConeArena : Arena where
  signature := positiveConeSignature
  Law R := ∀ (p t : ℤ) (hp5 : 5 ≤ p) (hpo : Odd p) (hpt : p ≤ t),
    let pp : positiveConeSignature.Params := ⟨p,hp5,hpo⟩
    let tt : positiveConeSignature.State pp := ⟨t,hpt⟩
    R.readout 0 pp tt < R.readout 1 pp tt

private theorem positiveCone_actual_law :
    positiveConeArena.Law positiveConeActual := by
  exact actual_positive_odd_wrap_cone

private theorem positiveCone_rejected_law (i : Fin 2) :
    ¬ positiveConeArena.Law (positiveConeRejected i) := by
  intro h
  have hh := h 5 5 (by norm_num) (by decide) (by norm_num)
  fin_cases i
  · change (original_return_pair 5 5).2 + 1 <
      (original_return_pair 5 5).2 at hh
    omega
  · change (original_return_pair 5 5).1 < 0 at hh
    omega

set_option maxRecDepth 10000 in
private theorem positiveCone_actual_dependence :
    ObservationalDependence positiveConeSignature positiveConeActual := by
  intro i
  let p : positiveConeSignature.Params := ⟨5,by decide⟩
  refine ⟨p, ⟨5,by decide⟩, ⟨6,by decide⟩, ?_⟩
  have h145 := actual_odd_wrap_counts 5 5 (by norm_num) (by decide) (by norm_num)
  have h175 := actual_odd_wrap_counts 5 6 (by norm_num) (by decide) (by norm_num)
  fin_cases i
  · change returns19 5 5 145 ≠ returns19 5 6 175
    have hc145 : returns19 5 5 145 =
        2*(Nat.choose 145 75+Nat.choose 145 95) := h145.1
    have hc175 : returns19 5 6 175 =
        2*(Nat.choose 175 90+Nat.choose 175 110) := h175.1
    rw [hc145,hc175]
    norm_num [Nat.choose_eq_factorial_div_factorial (by decide : 75 ≤ 145),
      Nat.choose_eq_factorial_div_factorial (by decide : 95 ≤ 145),
      Nat.choose_eq_factorial_div_factorial (by decide : 90 ≤ 175),
      Nat.choose_eq_factorial_div_factorial (by decide : 110 ≤ 175), Nat.factorial]
  · change returns33 5 5 145 ≠ returns33 5 6 175
    have hc145 : returns33 5 5 145 = 4*Nat.choose 145 80 := h145.2
    have hc175 : returns33 5 6 175 = 4*Nat.choose 175 95 := h175.2
    rw [hc145,hc175]
    norm_num [Nat.choose_eq_factorial_div_factorial (by decide : 80 ≤ 145),
      Nat.choose_eq_factorial_div_factorial (by decide : 95 ≤ 175), Nat.factorial]

noncomputable def positiveConeSource : Registration positiveConeArena
    (type_of% actual_positive_odd_wrap_cone) where
  actual := positiveConeActual
  bridge := Iff.rfl
  variation := ⟨positiveCone_actual_law,
    positiveConeRejected 0, positiveCone_rejected_law 0⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨positiveConeRejected i, ?_, rfl, positiveCone_rejected_law i⟩
      intro j hj
      funext p t
      simp [positiveConeRejected, realize, hj]
    · intro e
      exact nomatch e
  dependence := positiveCone_actual_dependence

noncomputable def positiveConeRegistration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@actual_positive_odd_wrap_cone)
      (Realization positiveConeSignature) Unit Unit := {
  unitName := `D5.S3.FiniteGroups.BajnokBeattyOddWrapPositiveCone.actual_positive_odd_wrap_cone.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.BajnokBeattyOddWrapPositiveCone.positiveConeSource
  realizationSource := none
  generated := false
  arena := .source ⟨positiveConeArena⟩
  objectArena := .source ⟨positiveConeArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source positiveConeArena ⟨positiveConeSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize positiveConeSignature
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

end Reg.D5.S3.FiniteGroups.BajnokBeattyOddWrapPositiveCone
