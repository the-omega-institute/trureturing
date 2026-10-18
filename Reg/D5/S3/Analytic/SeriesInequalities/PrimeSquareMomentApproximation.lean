import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.SeriesInequalities.PrimeSquareMomentApproximation
import Reg.Support.SingleDependentReadout
import Mathlib.NumberTheory.PrimesCongruentOne

namespace Reg.D5.S3.Analytic.SeriesInequalities.PrimeSquareMomentApproximation

open _root_.D5.S3.Analytic.SeriesInequalities.PrimeSquareMomentApproximation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

namespace PositiveScale

def actual : Realization signature := realize signature (fun _ _ x => x) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := 0 < R.readout () () c
private theorem rejected_law : ¬ arena.Law rejected := by
  change ¬ (0 : ℝ) < 0
  exact lt_irrefl 0
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by norm_num [actual, realize]⟩
def family : Registration arena (0 < c) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨c_pos, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Analytic.SeriesInequalities.PrimeSquareMomentApproximation.c_pos)
    (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Analytic.SeriesInequalities.PrimeSquareMomentApproximation.PositiveScale.unit
  realizationName := `Reg.D5.S3.Analytic.SeriesInequalities.PrimeSquareMomentApproximation.PositiveScale.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℝ
  sourceSelection := some {
    owner := `D5.S3.Analytic.SeriesInequalities.PrimeSquareMomentApproximation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #[]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end PositiveScale

namespace StrictGap

def actual : Realization signature := realize signature (fun _ _ x => x) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => c) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := R.readout () () c3 < c
private theorem rejected_law : ¬ arena.Law rejected := by
  simp [arena, rejected, realize]
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by norm_num [actual, realize]⟩
def family : Registration arena (c3 < c) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨c3_lt_c, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Analytic.SeriesInequalities.PrimeSquareMomentApproximation.c3_lt_c)
    (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Analytic.SeriesInequalities.PrimeSquareMomentApproximation.StrictGap.unit
  realizationName := `Reg.D5.S3.Analytic.SeriesInequalities.PrimeSquareMomentApproximation.StrictGap.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℝ
  sourceSelection := some {
    owner := `D5.S3.Analytic.SeriesInequalities.PrimeSquareMomentApproximation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #[]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end StrictGap

namespace UniformLogarithm

def actual : Realization signature :=
  realize signature (fun _ _ x => Real.log x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ δ : ℝ, 0 < δ → δ < 1 - c3 / c →
    ∀ B : ℝ, 2 < B → ∀ ε : ℝ, 0 < ε →
    ∃ S : ℝ, ∀ s : ℝ, S ≤ s →
      ∀ p : ℕ, p.Prime → p % 4 = 1 →
        Real.exp ((1 - δ) * c * s) < p →
        (p : ℝ) ≤ B * Real.exp (c * s) →
        |R.readout () () (localMoment p s) -
          Real.log (1 + Real.exp (2 * c * s) / (p : ℝ) ^ 2)| < ε

private theorem admissible_delta : ∃ δ : ℝ, 0 < δ ∧ δ < 1 - c3 / c := by
  have hg : 0 < 1 - c3 / c := sub_pos.mpr ((div_lt_one c_pos).mpr c3_lt_c)
  exact ⟨(1 - c3 / c) / 2, by linarith, by linarith⟩

private theorem window_point (δ S : ℝ) (hδ : 0 < δ) :
    ∃ (s : ℝ) (p : ℕ), S ≤ s ∧ 0 < s ∧ p.Prime ∧ p % 4 = 1 ∧
      Real.exp ((1 - δ) * c * s) < p ∧ (p : ℝ) ≤ 3 * Real.exp (c * s) := by
  obtain ⟨p, hp, hpn, hp4⟩ :=
    Nat.exists_prime_gt_modEq_one (k := 4) ⌈Real.exp (c * max S 1)⌉₊ (by decide)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpe : Real.exp (c * max S 1) < p :=
    (Nat.le_ceil _).trans_lt (by exact_mod_cast hpn)
  have hlog : c * max S 1 < Real.log p := (Real.lt_log_iff_exp_lt hp0).mpr hpe
  let s : ℝ := Real.log p / c
  have hlarge : max S 1 < s := by
    dsimp [s]
    exact (lt_div_iff₀ c_pos).mpr (by nlinarith)
  have hs : 0 < s := lt_trans (by norm_num) ((le_max_right S 1).trans_lt hlarge)
  have hexp : Real.exp (c * s) = p := by
    have he : c * s = Real.log p := by dsimp [s]; field_simp [c_pos.ne']
    rw [he, Real.exp_log hp0]
  refine ⟨s, p, (le_max_left S 1).trans hlarge.le, hs, hp, ?_, ?_, ?_⟩
  · simpa [Nat.ModEq] using hp4
  · rw [← hexp]
    apply Real.exp_lt_exp.mpr
    have hprod := mul_pos hδ (mul_pos c_pos hs)
    nlinarith
  · rw [hexp]
    linarith

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨δ, hd, hdt⟩ := admissible_delta
  obtain ⟨S, hS⟩ := h δ hd hdt 3 (by norm_num) (1 / 2) (by norm_num)
  obtain ⟨s, p, hs, hspos, hp, hp4, hplower, hpupper⟩ := window_point δ S hd
  have hb := hS s hs p hp hp4 hplower hpupper
  change |(-1 : ℝ) - Real.log (1 + Real.exp (2 * c * s) / (p : ℝ) ^ 2)| < 1 / 2 at hb
  have hl : 0 ≤ Real.log (1 + Real.exp (2 * c * s) / (p : ℝ) ^ 2) :=
    Real.log_nonneg (le_add_of_nonneg_right (by positivity))
  have hh := neg_le_abs ((-1 : ℝ) - Real.log (1 + Real.exp (2 * c * s) / (p : ℝ) ^ 2))
  linarith

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 1, Real.exp 1, by simp [actual, realize, Real.log_exp]⟩

def family : Registration arena originalClaim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Analytic.SeriesInequalities.PrimeSquareMomentApproximation.result)
    (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Analytic.SeriesInequalities.PrimeSquareMomentApproximation.UniformLogarithm.unit
  realizationName := `Reg.D5.S3.Analytic.SeriesInequalities.PrimeSquareMomentApproximation.UniformLogarithm.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => Real.log x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℝ
  sourceSelection := some {
    owner := `D5.S3.Analytic.SeriesInequalities.PrimeSquareMomentApproximation
    definition := some {
      owner := `D5.S3.Analytic.SeriesInequalities.PrimeSquareMomentApproximation
      name := `D5.S3.Analytic.SeriesInequalities.PrimeSquareMomentApproximation.originalClaim
      path := #[] }
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg",
        "body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end UniformLogarithm

end
end Reg.D5.S3.Analytic.SeriesInequalities.PrimeSquareMomentApproximation
