import LeanInformationAuditInterface.Contract.Registration
import D5.S3.FiniteGroups.BajnokBeattyOddWrapSingleCrossing
import Reg.D5.S3.FiniteGroups.BajnokBeattyFirstReturnDefect
import Reg.Support.DependentFamily

/-! Dependent-family registration attempt for actual_odd_wrap_single_crossing.

The observations use the public original_return_pair and preserve the complete
original existential-unique predicate. The typed attempt does not itself
establish declared_validated status; the exact native verdict is reported separately.

Parameters are exactly the admissible original integers p>=3 with Odd p.
The natural state coordinate is the original natural t: the Law retains its
explicit t>=2 guard, the exact T>2 guard, the non-strict comparison at T, and
the strict comparisons on both sides.  States 0 and 1 carry the actual source
definition but are not used as dependence witnesses or observations in the Law.
No threshold is supplied as an input or assumed to exist.

Both roles observe the components of the public original_return_pair, hence
the full original four-generator quotient definitions at length p*(6*t-1).
Changing role 0 to zero, or role 1 to actual role 0 plus one, violates the
required comparison at t=2 for every proposed T>2, including uniqueness.
Each intervention preserves the other role and the empty anchor family.
Actual observational dependence uses fixed p=3 and t=2,3, hence source lengths
33,51.  Its proof evaluates the already proved actual odd-wrap formulas.

sourceSelection and familyRecord remain none.  Checked selection and binding
of the original component readout occurrences remain unfinished, tracked at
https://github.com/the-omega-institute/trureturing/issues/25856 .
The typed dependent-family obligations below do not establish that selection.
-/

namespace Reg.D5.S3.FiniteGroups.BajnokBeattyOddWrapSingleCrossing

open _root_.D5.S3.FiniteGroups.BajnokBeattyOddWrapSingleCrossing
open _root_.D5.S3.FiniteGroups.BajnokBeattyOddWrapReturnCounts
open _root_.Reg.D5.S3.FiniteGroups.BajnokBeattyFirstReturnDefect
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped Classical

abbrev singleCrossingSignature : Signature where
  Params := {p : ℤ // 3 ≤ p ∧ Odd p}
  State _ := ℕ
  Role := Fin 2
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def singleCrossingActual : Realization singleCrossingSignature :=
  realize singleCrossingSignature
    (fun i p t => if i = 0 then (original_return_pair p.1 (t : ℤ)).1
      else (original_return_pair p.1 (t : ℤ)).2)
    (fun e => nomatch e)

noncomputable def singleCrossingRejected (i : Fin 2) :
    Realization singleCrossingSignature :=
  realize singleCrossingSignature
    (fun j p t => if j = i then
      (if j = 0 then 0 else singleCrossingActual.readout 0 p t + 1)
      else singleCrossingActual.readout j p t)
    (fun e => nomatch e)

abbrev singleCrossingArena : Arena where
  signature := singleCrossingSignature
  Law R := ∀ (p : ℤ) (hp3 : 3 ≤ p) (hpo : Odd p),
    let pp : singleCrossingSignature.Params := ⟨p,hp3,hpo⟩
    ∃! T : ℕ, 2 < T ∧
      (∀ t : ℕ, 2 ≤ t → t < T → R.readout 1 pp t < R.readout 0 pp t) ∧
      R.readout 0 pp T ≤ R.readout 1 pp T ∧
      (∀ t : ℕ, T < t → R.readout 0 pp t < R.readout 1 pp t)

private theorem singleCrossing_actual_law :
    singleCrossingArena.Law singleCrossingActual := by
  exact actual_odd_wrap_single_crossing

private theorem singleCrossing_rejected_law (i : Fin 2) :
    ¬ singleCrossingArena.Law (singleCrossingRejected i) := by
  intro h
  obtain ⟨T,hT,_hunique⟩ := h 3 (by norm_num) (by decide)
  have hh := hT.2.1 2 (by norm_num) hT.1
  fin_cases i
  · change (original_return_pair 3 2).2 < 0 at hh
    omega
  · change (original_return_pair 3 2).1 + 1 <
      (original_return_pair 3 2).1 at hh
    omega

set_option maxRecDepth 10000 in
private theorem singleCrossing_actual_dependence :
    ObservationalDependence singleCrossingSignature singleCrossingActual := by
  intro i
  let p : singleCrossingSignature.Params := ⟨3,by decide⟩
  refine ⟨p, 2, 3, ?_⟩
  have h33 := actual_odd_wrap_counts 3 2 (by norm_num) (by decide) (by norm_num)
  have h51 := actual_odd_wrap_counts 3 3 (by norm_num) (by decide) (by norm_num)
  fin_cases i
  · change returns19 3 2 33 ≠ returns19 3 3 51
    have hc33 : returns19 3 2 33 =
        2*(Nat.choose 33 18+Nat.choose 33 30) := h33.1
    have hc51 : returns19 3 3 51 =
        2*(Nat.choose 51 27+Nat.choose 51 39) := h51.1
    rw [hc33,hc51]
    norm_num [Nat.choose_eq_factorial_div_factorial (by decide : 18 ≤ 33),
      Nat.choose_eq_factorial_div_factorial (by decide : 30 ≤ 33),
      Nat.choose_eq_factorial_div_factorial (by decide : 27 ≤ 51),
      Nat.choose_eq_factorial_div_factorial (by decide : 39 ≤ 51), Nat.factorial]
  · change returns33 3 2 33 ≠ returns33 3 3 51
    have hc33 : returns33 3 2 33 = 4*Nat.choose 33 21 := h33.2
    have hc51 : returns33 3 3 51 = 4*Nat.choose 51 30 := h51.2
    rw [hc33,hc51]
    norm_num [Nat.choose_eq_factorial_div_factorial (by decide : 21 ≤ 33),
      Nat.choose_eq_factorial_div_factorial (by decide : 30 ≤ 51), Nat.factorial]

noncomputable def singleCrossingSource : Registration singleCrossingArena
    (type_of% actual_odd_wrap_single_crossing) where
  actual := singleCrossingActual
  bridge := Iff.rfl
  variation := ⟨singleCrossing_actual_law,
    singleCrossingRejected 0, singleCrossing_rejected_law 0⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨singleCrossingRejected i, ?_, rfl, singleCrossing_rejected_law i⟩
      intro j hj
      funext p t
      simp [singleCrossingRejected, realize, hj]
    · intro e
      exact nomatch e
  dependence := singleCrossing_actual_dependence

noncomputable def singleCrossingRegistration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@actual_odd_wrap_single_crossing)
      (Realization singleCrossingSignature) Unit Unit := {
  unitName := `D5.S3.FiniteGroups.BajnokBeattyOddWrapSingleCrossing.actual_odd_wrap_single_crossing.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.BajnokBeattyOddWrapSingleCrossing.singleCrossingSource
  realizationSource := none
  generated := false
  arena := .source ⟨singleCrossingArena⟩
  objectArena := .source ⟨singleCrossingArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source singleCrossingArena ⟨singleCrossingSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize singleCrossingSignature
    (fun i p t => if i = 0 then (original_return_pair p.1 (t : ℤ)).1
      else (original_return_pair p.1 (t : ℤ)).2)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.FiniteGroups.BajnokBeattyOddWrapSingleCrossing
