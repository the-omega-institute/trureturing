import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.Mertens.IntegratedExplicit.WidePrimeWindowMass
import Reg.Support.SingleDependentReadout

/-! Replacing the prime tail by zero destroys the global logarithmic lower bound. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter MeasureTheory LeanInformationAudit
open scoped Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.PrimeOnlyTailCorrection (primeTail)
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.WidePrimeWindowMass

namespace Reg.D5.S3.Weil.Mertens.IntegratedExplicit.WidePrimeWindowMass

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ => primeTail) (fun e => nomatch e)

def zeroTail : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law V := ∀ (b : ℝ) (_ : 1 < b),
    let tail := V.readout () ()
    ((¬ RiemannHypothesis) → ∀ K : ℝ, ∃ S : ℝ,
      ∀ B : ℝ, S ≤ B → ∀ A : ℝ, 2 ≤ A → A ^ b ≤ B →
        K ≤ (∫ x in A..B, max (-tail x) 0 / Real.sqrt x) - 2 * Real.log (B / A)) ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ A B : ℝ, 2 ≤ A → A ^ b ≤ B →
      2 * Real.log (B / A) - C ≤ ∫ x in A..B, max (-tail x) 0 / Real.sqrt x)

private theorem zero_tail_fails : ¬ arena.Law zeroTail := by
  intro h
  obtain ⟨C, hC0, hC⟩ := (h 2 (by norm_num)).2
  let B := max 4 (2 * Real.exp (C + 1))
  have hw : (2 : ℝ) ^ (2 : ℝ) ≤ B := by
    rw [Real.rpow_two]
    exact (by norm_num : (2 : ℝ) ^ 2 = 4).le.trans (le_max_left _ _)
  have hlog : C + 1 ≤ Real.log (B / 2) := by
    have hratio : Real.exp (C + 1) ≤ B / 2 := by
      exact (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2
        (by simpa only [mul_comm] using le_max_right (4 : ℝ) (2 * Real.exp (C + 1)))
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hratio
  have hz := hC 2 B le_rfl hw
  change 2 * Real.log (B / 2) - C ≤
    ∫ x in (2 : ℝ)..B, max (-(0 : ℝ)) 0 / Real.sqrt x at hz
  simp at hz
  linarith

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro _
  by_contra! h
  have hconst : primeTail = fun _ => primeTail 0 := funext fun x => h () x 0
  have hlim : Tendsto primeTail atTop (𝓝 0) := tendsto_integral_Ioi_zero tendsto_id
  have hlim' : Tendsto primeTail atTop (𝓝 (primeTail 0)) :=
    hconst ▸ tendsto_const_nhds
  have hz : primeTail 0 = 0 := tendsto_nhds_unique hlim' hlim
  apply zero_tail_fails
  change arena.Law (realize signature (fun _ _ _ => 0) (fun e => nomatch e))
  have hzero : primeTail = fun _ => 0 := by simpa only [hz] using hconst
  have ha : arena.Law actual := prime_tail_wide_window_mass
  unfold actual at ha
  rw [hzero] at ha
  exact ha

def family : Registration arena (type_of% @prime_tail_wide_window_mass) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨prime_tail_wide_window_mass, zeroTail, zero_tail_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual zeroTail zero_tail_fails
  dependence := actual_dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@prime_tail_wide_window_mass) (Realization signature) Unit Unit where
  unitName := .str
    `D5.S3.Weil.Mertens.IntegratedExplicit.WidePrimeWindowMass.prime_tail_wide_window_mass
    "__information_unit"
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.WidePrimeWindowMass.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ => primeTail) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.WidePrimeWindowMass
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Weil.Mertens.IntegratedExplicit.WidePrimeWindowMass
