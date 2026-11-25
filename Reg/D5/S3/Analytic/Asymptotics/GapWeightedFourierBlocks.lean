import D5.S3.Analytic.Asymptotics.GapWeightedFourierBlocks
import D5.S3.Analytic.Asymptotics.VanishingGapSignTransfer
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

/-! Source-bound readout of the Fourier coefficient recovery error. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u

open LeanInformationAudit Filter
open scoped Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.GapWeightedFourier (blockAverage gap phase eventually_blockAverage_modulated_series)
open _root_.D5.S3.Analytic.Asymptotics.VanishingGapSignTransfer (log_mesh_of_ratio_one)

namespace Reg.D5.S3.Analytic.Asymptotics.GapWeightedFourierBlocks

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ z => ‖z‖) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {ι : Type u} {y : ℕ → ℝ},
    StrictMono y → Tendsto (gap y) atTop (𝓝 0) →
    ∀ (c : ι → ℂ) (freq : ι → ℝ), Summable (fun i => ‖c i‖) →
    ∀ (ν : ℝ) (s : ℕ → ℂ),
      Tendsto (fun k => s k - ∑' i, c i * phase (freq i) (y k)) atTop (𝓝 0) →
    ∀ {ε : ℝ}, 0 < ε →
      ∃ A : ℕ, ∃ H : ℝ, 0 < H ∧ ∀ ⦃a b : ℕ⦄, A ≤ a → a < b → H ≤ y b - y a →
        R.readout () () (blockAverage y (fun k => s k * phase (-ν) (y k)) a b -
          (∑' i, if freq i = ν then c i else 0)) ≤ ε

private theorem rejected_law : ¬ (arena.{u}).Law rejected := by
  intro h
  let x : ℕ → ℝ := fun k => (k : ℝ) + 1
  let y : ℕ → ℝ := fun k => Real.log (x k)
  have hx : Tendsto x atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hr : Tendsto (fun k => x (k + 1) / x k) atTop (𝓝 1) := by
    have ht : Tendsto (fun k => 1 + 1 / x k) atTop (𝓝 1) := by
      simpa only [add_zero] using (hx.const_div_atTop (1 : ℝ)).const_add 1
    apply ht.congr
    intro k
    have hpos : 0 < x k := by dsimp [x]; positivity
    calc
      _ = (x k + 1) / x k := by rw [add_div, div_self hpos.ne']
      _ = x (k + 1) / x k := by simp [x, Nat.cast_add]
  obtain ⟨hy, hg⟩ := log_mesh_of_ratio_one hx hr
  have hm : StrictMono y := by
    intro i j hij
    apply Real.log_lt_log (by dsimp [x]; positivity)
    exact add_lt_add_left (Nat.cast_lt.mpr hij) 1
  have hs : Tendsto (fun k => (0 : ℂ) - ∑' i : ULift.{u} Unit,
      (0 : ℂ) * phase 0 (y k)) atTop (𝓝 0) := by
    simp
  obtain ⟨A, H, hH, hblock⟩ := h (ι := ULift.{u} Unit) (y := y) hm hg
    (fun _ => 0) (fun _ => 0) (by simp) 0 (fun _ => 0) hs (ε := 1 / 2) (by norm_num)
  obtain ⟨b, hb⟩ := ((tendsto_atTop.1 hy) (y A + H)).exists
  have hab : A < b := lt_of_not_ge fun hba => by
    have hle := hm.monotone hba
    linarith only [hb, hle, hH]
  have hbad : (1 : ℝ) ≤ 1 / 2 := hblock (a := A) (b := b) le_rfl hab (by linarith only [hb])
  norm_num at hbad

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  change ‖(0 : ℂ)‖ ≠ ‖(1 : ℂ)‖
  simp

def family : Registration arena.{u} (type_of% @eventually_blockAverage_modulated_series.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@eventually_blockAverage_modulated_series.{u}, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@eventually_blockAverage_modulated_series.{u}) (Realization signature) Unit Unit where
  unitName :=
    `Reg.D5.S3.Analytic.Asymptotics.GapWeightedFourierBlocks.unit
  realizationName :=
    `Reg.D5.S3.Analytic.Asymptotics.GapWeightedFourierBlocks.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Asymptotics.GapWeightedFourierBlocks
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "arg", "body", "arg", "body", "arg",
        "body", "body", "body", "body", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Analytic.Asymptotics.GapWeightedFourierBlocks
