import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.Hardy.FiniteStripMomentBound
import Reg.Support.SingleDependentReadout

/-! The strip radius and the time-window norm in the two interpolation bounds. -/

namespace Reg.D5.S3.Analytic.Hardy.FiniteStripMomentBound

open _root_.D5.S3.Analytic.Hardy.FiniteStripMomentBound
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Reg.Support
open LeanInformationAudit MeasureTheory Set

noncomputable section
universe u

namespace Growth

abbrev signature := SingleDependentReadout.signature ℝ (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ β q => radius β q) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {ι : Type u} [Fintype ι] [DecidableEq ι]
    {F : ℂ → ℂ} {L β M : ℝ} (_hL : 0 ≤ L) (_hβ : 0 < β) (_hM : 0 ≤ M)
    (_hF : Differentiable ℂ F)
    (_hgrowth : ∀ z : ℂ, ‖F z‖ ≤ M * Real.exp (L * max 0 (-z.re)))
    (q : ι → ℝ) (_hq : ∀ k, 0 ≤ q k) (_hinj : Function.Injective q) (j : ι)
    (_hone : F (q j) = 1) (_hzero : ∀ k ≠ j, F (q k) = 0),
    Real.exp (-L * (R.readout () β (q j) - q j) / 2) ≤
      M * ∏ k ∈ Finset.univ.erase j, |q j - q k| / (radius β (q j) + radius β (q k))

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let j : ULift.{u} Unit := ULift.up ()
  have hgrowth (z : ℂ) : ‖(1 : ℂ)‖ ≤ 1 * Real.exp (1 * max 0 (-z.re)) := by
    simpa using Real.one_le_exp (le_max_left 0 (-z.re))
  have hbad := h (F := fun _ => 1) (L := 1) (β := 1) (M := 1)
    (by norm_num) (by norm_num) (by norm_num) (differentiable_const _) hgrowth
    (fun _ => 0) (by simp) (fun _ _ _ => Subsingleton.elim _ _) j rfl
    (fun k hk => (hk (Subsingleton.elim k j)).elim)
  have hle : Real.exp ((1 : ℝ) / 2) ≤ 1 := by
    simpa [rejected, realize, Finset.univ_unique, Finset.erase_singleton, j] using hbad
  exact (not_le_of_gt (Real.one_lt_exp_iff.mpr (by norm_num))) hle

def family : Registration arena (type_of% @entire_strip_bound.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨entire_strip_bound, rejected, rejected_law⟩
  sensitivity := SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro _
    refine ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), ?_⟩
    exact show radius 0 0 ≠ radius 0 1 by
      simp [radius]

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@entire_strip_bound.{u})
    (type_of% (realize signature (fun _ β q => radius β q) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Analytic.Hardy.FiniteStripMomentBound.entire_strip_bound.__information_unit
  realizationName := `Reg.D5.S3.Analytic.Hardy.FiniteStripMomentBound.Growth.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ β q => radius β q) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Hardy.FiniteStripMomentBound
    definition := none
    coordinates := #[5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "arg", "fn", "arg", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Growth

namespace Moment

abbrev signature := SingleDependentReadout.signature ℝ (fun _ => ℝ → ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ L h => windowNorm L h) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {ι : Type u} [Fintype ι] [DecidableEq ι]
    {L β : ℝ} (_hL : 0 < L) (_hβ : 0 < β) (q : ι → ℝ)
    (_hq : ∀ k, 0 ≤ q k) (_hinj : Function.Injective q) (j : ι)
    (h : ℝ → ℝ) (_hh : MemLp h 2 (volume.restrict (Ioo 0 L)))
    (_hm : ∀ k, (∫ s in Ioo 0 L, h s * Real.exp (-q k * s)) = if k = j then 1 else 0),
    (∏ k ∈ Finset.univ.erase j, (radius β (q j) + radius β (q k)) / |q j - q k|) *
        Real.exp (-L * (radius β (q j) - q j) / 2) / Real.sqrt L ≤ R.readout () L h

private theorem unit_window_integral : (∫ _ in Ioo (0 : ℝ) 1, (1 : ℝ)) = 1 := by
  simp

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let j : ULift.{u} Unit := ULift.up ()
  have hlp : MemLp (fun _ : ℝ => (1 : ℝ)) 2 (volume.restrict (Ioo 0 1)) := by
    haveI : IsFiniteMeasure (volume.restrict (Ioo (0 : ℝ) 1)) := ⟨by
      rw [Measure.restrict_apply_univ, Real.volume_Ioo]
      exact ENNReal.ofReal_lt_top⟩
    exact memLp_const 1
  have hm (k : ULift.{u} Unit) : (∫ s in Ioo (0 : ℝ) 1,
      (1 : ℝ) * Real.exp (-(0 : ℝ) * s)) = if k = j then 1 else 0 := by
    simpa [Subsingleton.elim k j] using unit_window_integral
  have hbad := h (L := 1) (β := 1) (by norm_num) (by norm_num)
    (fun _ => 0) (by simp) (fun _ _ _ => Subsingleton.elim _ _) j (fun _ => 1) hlp hm
  have hle : Real.exp (-(1 : ℝ) / 2) ≤ 0 := by
    simpa [rejected, realize, radius, Finset.univ_unique, Finset.erase_singleton, j] using hbad
  exact (Real.exp_pos _).not_ge hle

def family : Registration arena (type_of% @windowNorm_lower_bound.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨windowNorm_lower_bound, rejected, rejected_law⟩
  sensitivity := SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro _
    refine ⟨(1 : ℝ), fun _ => (0 : ℝ), fun _ => (1 : ℝ), ?_⟩
    change windowNorm 1 (fun _ => 0) ≠ windowNorm 1 (fun _ => 1)
    simp [windowNorm, unit_window_integral]

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@windowNorm_lower_bound.{u})
    (type_of% (realize signature (fun _ L h => windowNorm L h) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Analytic.Hardy.FiniteStripMomentBound.windowNorm_lower_bound.__information_unit
  realizationName := `Reg.D5.S3.Analytic.Hardy.FiniteStripMomentBound.Moment.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ L h => windowNorm L h) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Hardy.FiniteStripMomentBound
    definition := none
    coordinates := #[3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "arg"]
      stateBinder := 11
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Moment

end

end Reg.D5.S3.Analytic.Hardy.FiniteStripMomentBound
