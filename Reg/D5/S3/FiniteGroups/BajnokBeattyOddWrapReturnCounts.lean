import LeanInformationAuditInterface.Contract.Registration
import D5.S3.FiniteGroups.BajnokBeattyOddWrapReturnCounts
import Reg.D5.S3.FiniteGroups.BajnokBeattyFirstReturnDefect
import Reg.Support.DependentFamily

/-! Faithful full-telescope DependentFamily registration attempt.
The parameter p has exactly the original positivity and oddness assumptions;
its states are exactly the original admissible t values.  Both observations
reuse actualReturn at the source length (p*(6*t-1)).toNat.  The complete
original p,t telescope and both count conclusions are retained in the Law.

Variation and per-role sensitivity use the same admissible p=3,t=2 state.
Observational dependence keeps p=3 fixed and varies t from 2 to 3, so the
lengths 33 and 51 remain in this theorem's actual observation domain.
Only the proved binomial formulas are evaluated; no word fibers are enumerated.

sourceSelection and familyRecord remain none.  The original W occurrences
have not been bound by a checked source-coordinate selection; this specific
unfinished discovery boundary is tracked at
https://github.com/the-omega-institute/trureturing/issues/25856 .
Neither this source attempt nor compilation alone claims declared_validated.
-/

namespace Reg.D5.S3.FiniteGroups.BajnokBeattyOddWrapReturnCounts

open _root_.D5.S3.FiniteGroups.BajnokBeattyOddWrapReturnCounts
open _root_.D5.S3.FiniteGroups.NearSquareLatticeRigidity
open _root_.Reg.D5.S3.FiniteGroups.BajnokBeattyFirstReturnDefect
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped Classical

abbrev oddWrapSignature : Signature where
  Params := {p : ℤ // 3 ≤ p ∧ Odd p}
  State _ := {t : ℤ // 2 ≤ t}
  Role := Fin 2
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def oddWrapActual : Realization oddWrapSignature :=
  realize oddWrapSignature
    (fun i p t => actualReturn.readout i ⟨p.1,t.1⟩
      ((p.1*(6*t.1-1)).toNat))
    (fun e => nomatch e)

noncomputable def oddWrapRejected (i : Fin 2) : Realization oddWrapSignature :=
  realize oddWrapSignature
    (fun j p t => if j = i then oddWrapActual.readout j p t + 1
      else oddWrapActual.readout j p t)
    (fun e => nomatch e)

abbrev oddWrapArena : Arena where
  signature := oddWrapSignature
  Law R := ∀ (p t : ℤ) (hp3 : 3 ≤ p) (hpo : Odd p) (ht : 2 ≤ t),
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
    let pp : oddWrapSignature.Params := ⟨p,hp3,hpo⟩
    let tt : oddWrapSignature.State pp := ⟨t,ht⟩
    R.readout 0 pp tt = 2*(Nat.choose L (p*(m+1)/2).toNat +
      Nat.choose L (p*(m+9)/2).toNat) ∧
    R.readout 1 pp tt = 4*Nat.choose L (p*(m+3)/2).toNat

private theorem oddWrap_actual_law : oddWrapArena.Law oddWrapActual := by
  exact actual_odd_wrap_counts

private theorem oddWrap_rejected_law (i : Fin 2) :
    ¬ oddWrapArena.Law (oddWrapRejected i) := by
  intro h
  have hh := h 3 2 (by norm_num) (by decide) (by norm_num)
  have hd := actual_odd_wrap_counts 3 2 (by norm_num) (by decide) (by norm_num)
  fin_cases i
  · have bad := hh.1
    have good := hd.1
    change returns19 3 2 33 + 1 =
      2*(Nat.choose 33 18+Nat.choose 33 30) at bad
    change returns19 3 2 33 =
      2*(Nat.choose 33 18+Nat.choose 33 30) at good
    omega
  · have bad := hh.2
    have good := hd.2
    change returns33 3 2 33 + 1 = 4*Nat.choose 33 21 at bad
    change returns33 3 2 33 = 4*Nat.choose 33 21 at good
    omega

private theorem oddWrap_actual_dependence :
    ObservationalDependence oddWrapSignature oddWrapActual := by
  intro i
  let p : oddWrapSignature.Params := ⟨3,by decide⟩
  refine ⟨p, ⟨2,by decide⟩, ⟨3,by decide⟩, ?_⟩
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

noncomputable def oddWrapSource : Registration oddWrapArena
    (type_of% actual_odd_wrap_counts) where
  actual := oddWrapActual
  bridge := Iff.rfl
  variation := ⟨oddWrap_actual_law, oddWrapRejected 0, oddWrap_rejected_law 0⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨oddWrapRejected i, ?_, rfl, oddWrap_rejected_law i⟩
      intro j hj
      funext p t
      simp [oddWrapRejected, realize, hj]
    · intro e
      exact nomatch e
  dependence := oddWrap_actual_dependence

noncomputable def oddWrapRegistration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@actual_odd_wrap_counts)
      (Realization oddWrapSignature) Unit Unit := {
  unitName := `D5.S3.FiniteGroups.BajnokBeattyOddWrapReturnCounts.actual_odd_wrap_counts.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.BajnokBeattyOddWrapReturnCounts.oddWrapSource
  realizationSource := none
  generated := false
  arena := .source ⟨oddWrapArena⟩
  objectArena := .source ⟨oddWrapArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source oddWrapArena ⟨oddWrapSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize oddWrapSignature
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

end Reg.D5.S3.FiniteGroups.BajnokBeattyOddWrapReturnCounts
