import LeanInformationAuditInterface.Contract.Registration
import D5.S3.FiniteGroups.BajnokBeattyOddWrapThresholdBracket
import Reg.D5.S3.FiniteGroups.BajnokBeattyFirstReturnDefect
import Reg.Support.DependentFamily

/-! Faithful full-domain registration attempt for
`actual_odd_wrap_threshold_bracket`.

Parameters are exactly the odd integers p>=5. States are all natural
t>=2, covering the entire original before/after domain rather than the
narrow upper-envelope band. Two roles read the complete original pair.
The Law preserves the original unique threshold, its strict before/after
signs, its nonnegative comparison at the threshold, and both real bounds.

The dependent state at T uses its original proof 2<T. The existential
proof binder is equivalent to the original conjunction 2<T; the bridge
unfolds the actual readouts and removes that proof binder. No comparison,
formula, Gaussian estimate, threshold or root property is assumed anew.

Replace either whole role family by zero. For role 0, the original
before condition at t=2 forces a natural count to be less than zero.
For role 1, the original after condition at t=T+1 does the same. Both
interventions preserve the other role and every empty-family anchor.
Actual dependence fixes p=5 and compares t=2,3, whose original lengths
are 55,85; both states belong to the full original state domain.

sourceSelection and familyRecord remain none. Source-occurrence binding
remains unfinished under https://github.com/the-omega-institute/trureturing/issues/25856 .
No declared_validated binding is claimed.
-/

namespace Reg.D5.S3.FiniteGroups.BajnokBeattyOddWrapThresholdBracket

open _root_.D5.S3.FiniteGroups.BajnokBeattyOddWrapThresholdBracket
open _root_.D5.S3.FiniteGroups.BajnokBeattyOddWrapGaussianRoot
open _root_.D5.S3.FiniteGroups.BajnokBeattyOddWrapSingleCrossing
open _root_.D5.S3.FiniteGroups.BajnokBeattyOddWrapReturnCounts
open _root_.Reg.D5.S3.FiniteGroups.BajnokBeattyFirstReturnDefect
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped Classical

abbrev thresholdBracketSignature : Signature where
  Params := {p : ℤ // 5 ≤ p ∧ Odd p}
  State _ := {t : ℕ // 2 ≤ t}
  Role := Fin 2
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def thresholdBracketActual : Realization thresholdBracketSignature :=
  realize thresholdBracketSignature
    (fun i p t => if i = 0 then (original_return_pair p.1 (t.1 : ℤ)).1
      else (original_return_pair p.1 (t.1 : ℤ)).2)
    (fun e => nomatch e)

noncomputable def thresholdBracketRejected (i : Fin 2) :
    Realization thresholdBracketSignature :=
  realize thresholdBracketSignature
    (fun j p t => if j = i then 0 else thresholdBracketActual.readout j p t)
    (fun e => nomatch e)

abbrev thresholdBracketArena : Arena where
  signature := thresholdBracketSignature
  Law R := ∀ (p : ℤ) (hp5 : 5 ≤ p) (hpo : Odd p),
    let pp : thresholdBracketSignature.Params := ⟨p,hp5,hpo⟩
    ∃! T : ℕ, ∃ hT : 2 < T,
      (∀ (t : ℕ) (ht2 : 2 ≤ t), t < T →
        R.readout 1 pp ⟨t,ht2⟩ < R.readout 0 pp ⟨t,ht2⟩) ∧
      R.readout 0 pp ⟨T,hT.le⟩ ≤ R.readout 1 pp ⟨T,hT.le⟩ ∧
      (∀ (t : ℕ) (hTt : T < t),
        R.readout 0 pp ⟨t,(hT.trans hTt).le⟩ <
          R.readout 1 pp ⟨t,(hT.trans hTt).le⟩) ∧
      alpha*(p : ℝ)+1/6-1/(6*(p : ℝ)) < (T : ℝ) ∧
      (T : ℤ) ≤ Int.ceil (alpha*(p : ℝ)+1/6-1/(25*(p : ℝ)))

private theorem thresholdBracket_actual_bridge :
    (type_of% actual_odd_wrap_threshold_bracket) ↔
      thresholdBracketArena.Law thresholdBracketActual := by
  simp [thresholdBracketArena, thresholdBracketActual, realize,
    and_assoc, and_left_comm, and_comm]

private theorem thresholdBracket_actual_law :
    thresholdBracketArena.Law thresholdBracketActual :=
  thresholdBracket_actual_bridge.mp actual_odd_wrap_threshold_bracket

private theorem thresholdBracket_rejected_law (i : Fin 2) :
    ¬ thresholdBracketArena.Law (thresholdBracketRejected i) := by
  intro h
  obtain ⟨T,hT,_⟩ := h 5 (by norm_num) (by decide)
  obtain ⟨hT2,hbefore,hmid,hafter,hlower,hupper⟩ := hT
  fin_cases i
  · have hh := hbefore 2 (by norm_num) hT2
    change (original_return_pair 5 2).2 < 0 at hh
    omega
  · have hh := hafter (T+1) (by omega)
    change (original_return_pair 5 ((T+1 : ℕ) : ℤ)).1 < 0 at hh
    omega

set_option maxRecDepth 10000 in
private theorem thresholdBracket_actual_dependence :
    ObservationalDependence thresholdBracketSignature thresholdBracketActual := by
  intro i
  let p : thresholdBracketSignature.Params := ⟨5,by decide⟩
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

noncomputable def thresholdBracketSource : Registration thresholdBracketArena
    (type_of% actual_odd_wrap_threshold_bracket) where
  actual := thresholdBracketActual
  bridge := thresholdBracket_actual_bridge
  variation := ⟨thresholdBracket_actual_law,
    thresholdBracketRejected 0, thresholdBracket_rejected_law 0⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨thresholdBracketRejected i, ?_, rfl, thresholdBracket_rejected_law i⟩
      intro j hj
      funext p t
      simp [thresholdBracketRejected, realize, hj]
    · intro e
      exact nomatch e
  dependence := thresholdBracket_actual_dependence

noncomputable def thresholdBracketRegistration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@actual_odd_wrap_threshold_bracket)
      (Realization thresholdBracketSignature) Unit Unit := {
  unitName := `D5.S3.FiniteGroups.BajnokBeattyOddWrapThresholdBracket.actual_odd_wrap_threshold_bracket.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.BajnokBeattyOddWrapThresholdBracket.thresholdBracketSource
  realizationSource := none
  generated := false
  arena := .source ⟨thresholdBracketArena⟩
  objectArena := .source ⟨thresholdBracketArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source thresholdBracketArena ⟨thresholdBracketSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize thresholdBracketSignature
    (fun i p t => if i = 0 then (original_return_pair p.1 (t.1 : ℤ)).1
      else (original_return_pair p.1 (t.1 : ℤ)).2)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.FiniteGroups.BajnokBeattyOddWrapThresholdBracket
