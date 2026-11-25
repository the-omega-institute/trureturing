import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.Mertens.IntegratedExplicit.QuarticSignedMass
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Set MeasureTheory LeanInformationAudit
open _root_.D5.S3.Arith.Robin.CompleteMertensPeak (U)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.QuarticSignedMass
open scoped Topology

namespace Reg.D5.S3.Weil.Mertens.IntegratedExplicit.QuarticSignedMass

namespace Comparison

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℕ → ℕ → ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ s => gridChordMass s) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law V := ∀ {s : ℝ}, |s| ≤ 1 → ∀ {A B : ℕ}, 1 ≤ A → A ≤ B →
    |(∫ x in grid A..grid B, signedDensity s U x) - V.readout () () s A B| ≤
      4275 * (Real.log (B : ℝ) - Real.log (A : ℝ)) +
        3375 / (A : ℝ) + 225 * (Real.log 4 + 6)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ _ _ => 10000) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h (s := 0) (by norm_num) (A := 1) (B := 1) le_rfl le_rfl
  have hread : rejected.readout () () 0 1 1 = (10000 : ℝ) := rfl
  rw [hread] at hbad
  norm_num at hbad
  linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)]

private theorem first_block_pos : 0 < gridChordMass 1 1 2 := by
  let a := grid 1
  let b := grid 2
  let f := signedDensity 1 (chord U a b)
  have ha : 0 < a := by norm_num [a, grid]
  have hab : a < b := by norm_num [a, b, grid]
  have hchord : Continuous (chord U a b) := by unfold chord; fun_prop
  have hscaled : ContinuousOn (fun x => (1 : ℝ) * chord U a b x) (Icc a b) :=
    continuousOn_const.mul hchord.continuousOn
  have hf : ContinuousOn f (Icc a b) :=
    (hscaled.sup continuousOn_const).mul <|
      continuousOn_id.rpow_const fun x hx => Or.inl (ha.trans_le hx.1).ne'
  have hU : 0 < U a := by
    have h₁ : U a = 1 + Real.eulerMascheroniConstant := by simp [a, grid, U, Chebyshev.psi]
    rw [h₁]
    linarith [Real.one_half_lt_eulerMascheroniConstant]
  have hend : chord U a b a = U a := by simp [chord, sub_ne_zero.mpr hab.ne']
  have hfa : 0 < f a := by
    dsimp [f, signedDensity]
    rw [one_mul, hend, max_eq_left hU.le]
    exact mul_pos hU (Real.rpow_pos_of_pos ha _)
  have hpos := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    hab (continuousOn_const (c := (0 : ℝ))) hf
    (fun x hx => mul_nonneg (le_max_right _ _) (Real.rpow_nonneg (ha.trans hx.1).le _))
    ⟨a, ⟨le_rfl, hab.le⟩, hfa⟩
  have hcell : Finset.Ico 1 2 = ({1} : Finset ℕ) := by decide
  simpa only [gridChordMass, hcell, Finset.sum_singleton, intervalIntegral.integral_zero]
    using hpos

private theorem dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(), 0, 1, ?_⟩
  intro heq
  have he := congrFun (congrFun heq 1) 2
  change gridChordMass 0 1 2 = gridChordMass 1 1 2 at he
  have hzero : gridChordMass 0 1 2 = 0 := by simp [gridChordMass, signedDensity]
  exact first_block_pos.ne' (hzero ▸ he.symm)

def evidence : Registration arena (type_of% @quartic_grid_log_error) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@quartic_grid_log_error, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@quartic_grid_log_error) (Realization signature) Unit Unit where
  unitName := .str
    `D5.S3.Weil.Mertens.IntegratedExplicit.QuarticSignedMass.quartic_grid_log_error
    "__information_unit"
  realizationName := .str
    `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.QuarticSignedMass.Comparison "evidence"
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ s => gridChordMass s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.QuarticSignedMass
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "arg", "arg",
                 "fn", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Comparison

namespace Growth

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℂ)

def actual : Realization signature :=
  realize signature (fun _ _ z => riemannZeta z) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law V := ∀ {z : ℂ}, V.readout () () z = 0 → 1 / 2 < z.re → ∀ {ε : ℝ}, 0 < ε →
    ∀ᶠ k : ℕ in atTop, ∀ sign : ℝ, sign = 1 ∨ sign = -1 →
      (k : ℝ) ^ (16 * (z.re - 1 / 2) - ε) ≤ gridChordMass sign (k^3) (k^4)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem U_le {x : ℝ} (hx : 1 ≤ x) : U x ≤ 9 * x := by
  have hx₀ : 0 ≤ x := zero_le_one.trans hx
  have hcoeff : Mertens.E₁Λ x + (1 + Real.eulerMascheroniConstant) ≤ 9 := by
    linarith [Mertens.E₁Λ.le hx, Real.eulerMascheroniConstant_lt_two_thirds,
      Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)]
  calc
    U x = (Mertens.E₁Λ x + (1 + Real.eulerMascheroniConstant)) * x - Chebyshev.psi x := by
      rw [U, Mertens.sum_mangoldt_div_eq]
      ring
    _ ≤ _ := by
      linarith [mul_le_mul_of_nonneg_right hcoeff hx₀, Chebyshev.psi_nonneg x]

private theorem grid_mono : StrictMono grid := by
  intro n m hnm
  unfold grid
  have h : (n : ℝ) < (m : ℝ) := by exact_mod_cast hnm
  gcongr

private theorem cell_le {a b H : ℝ} (ha : 1 ≤ a) (hab : a < b) (hb : b ≤ H) :
    (∫ x in a..b, signedDensity 1 (chord U a b) x) ≤ 9 * H ^ 2 := by
  have hH : 0 ≤ H := zero_le_one.trans (ha.trans (hab.le.trans hb))
  have hbound : 0 ≤ 9 * H := by positivity
  have hden := sub_pos.mpr hab
  have hnorm : ‖∫ x in a..b, signedDensity 1 (chord U a b) x‖ ≤ 9 * H * |b - a| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    rw [uIoc_of_le hab.le] at hx
    have hx₁ : 1 ≤ x := ha.trans hx.1.le
    have hx₀ := zero_lt_one.trans_le hx₁
    let p := (b - x) / (b - a)
    let q := (x - a) / (b - a)
    have hp : 0 ≤ p := div_nonneg (sub_nonneg.mpr hx.2) hden.le
    have hq : 0 ≤ q := div_nonneg (sub_nonneg.mpr hx.1.le) hden.le
    have hpq : p + q = 1 := by
      dsimp [p, q]
      rw [← add_div]
      convert div_self hden.ne' using 1
      ring
    have h9 : (0 : ℝ) ≤ 9 := by norm_num
    have hua := (U_le ha).trans (mul_le_mul_of_nonneg_left (hab.le.trans hb) h9)
    have hub := (U_le (ha.trans hab.le)).trans (mul_le_mul_of_nonneg_left hb h9)
    have hchord : chord U a b x ≤ 9 * H := calc
      _ = p * U a + q * U b := rfl
      _ ≤ p * (9 * H) + q * (9 * H) :=
        add_le_add (mul_le_mul_of_nonneg_left hua hp) (mul_le_mul_of_nonneg_left hub hq)
      _ = _ := by rw [← add_mul, hpq, one_mul]
    have hw : x ^ (-(3 / 2) : ℝ) ≤ 1 := by
      simpa using Real.rpow_le_rpow_of_nonpos zero_lt_one hx₁ (by norm_num : -(3 / 2 : ℝ) ≤ 0)
    have hw₀ := Real.rpow_nonneg hx₀.le (-(3 / 2) : ℝ)
    simp only [Real.norm_eq_abs, signedDensity, one_mul,
      abs_of_nonneg (mul_nonneg (le_max_right _ _) hw₀)]
    exact (mul_le_mul_of_nonneg_left hw (le_max_right _ _)).trans
      (by simpa only [mul_one] using max_le hchord hbound)
  calc
    _ ≤ ‖∫ x in a..b, signedDensity 1 (chord U a b) x‖ := by
      rw [Real.norm_eq_abs]
      exact le_abs_self _
    _ ≤ 9 * H * |b - a| := hnorm
    _ ≤ 9 * H ^ 2 := by
      rw [abs_of_nonneg hden.le, pow_two, ← mul_assoc]
      exact mul_le_mul_of_nonneg_left (by linarith) hbound

private theorem block_le {A B : ℕ} (hA : 1 ≤ A) :
    gridChordMass 1 A B ≤ 9 * (B : ℝ)^9 := by
  have hcard : (Finset.Ico A B).card ≤ B := by
    have hsub : Finset.Ico A B ⊆ Finset.range B :=
      fun n hn => Finset.mem_range.mpr (Finset.mem_Ico.mp hn).2
    exact (Finset.card_le_card hsub).trans_eq (Finset.card_range B)
  calc
    _ ≤ ∑ n ∈ Finset.Ico A B, 9 * (grid B)^2 := by
      unfold gridChordMass
      refine Finset.sum_le_sum fun n hn => ?_
      obtain ⟨hnA, hnB⟩ := Finset.mem_Ico.mp hn
      have h₁ : 1 ≤ grid n := by
        simpa [grid] using grid_mono.monotone (hA.trans hnA)
      exact cell_le h₁ (grid_mono (Nat.lt_succ_self n)) (grid_mono.monotone (Nat.succ_le_of_lt hnB))
    _ = ((Finset.Ico A B).card : ℝ) * (9 * (grid B)^2) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (B : ℝ) * (9 * (grid B)^2) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
    _ = _ := by unfold grid; ring

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h (z := 20) rfl (by norm_num) (ε := 275) (by norm_num)
  obtain ⟨k, hk, hk₁₀⟩ := (hbad.and (eventually_ge_atTop (10 : ℕ))).exists
  have hlower := hk 1 (Or.inl rfl)
  norm_num at hlower
  have hkR : (10 : ℝ) ≤ k := by exact_mod_cast hk₁₀
  have hA : 1 ≤ k^3 := one_le_pow₀ (by omega : 1 ≤ k)
  have hupper : gridChordMass 1 (k^3) (k^4) ≤ 9 * (k : ℝ)^36 := by
    convert block_le (B := k^4) hA using 1
    push_cast
    ring
  have hstrict : 9 * (k : ℝ)^36 < (k : ℝ)^37 := calc
    _ < (k : ℝ) * (k : ℝ)^36 := mul_lt_mul_of_pos_right (by linarith) (pow_pos (by linarith) _)
    _ = _ := (pow_succ' (k : ℝ) 36).symm
  exact (not_lt_of_ge (hlower.trans hupper)) hstrict

def evidence : Registration arena (type_of% @off_line_zero_forces_signed_quartic_chord_mass) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@off_line_zero_forces_signed_quartic_chord_mass, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro _
    refine ⟨(), (0 : ℂ), (-2 : ℂ), ?_⟩
    change riemannZeta 0 ≠ riemannZeta (-2)
    have hz : riemannZeta (-2) = 0 := by simpa using riemannZeta_neg_two_mul_nat_add_one 0
    rw [hz, riemannZeta_zero]
    norm_num

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@off_line_zero_forces_signed_quartic_chord_mass) (Realization signature) Unit Unit where
  unitName := .str
    `D5.S3.Weil.Mertens.IntegratedExplicit.QuarticSignedMass.off_line_zero_forces_signed_quartic_chord_mass
    "__information_unit"
  realizationName := .str
    `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.QuarticSignedMass.Growth "evidence"
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => riemannZeta z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.QuarticSignedMass
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "domain", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Growth

end Reg.D5.S3.Weil.Mertens.IntegratedExplicit.QuarticSignedMass
