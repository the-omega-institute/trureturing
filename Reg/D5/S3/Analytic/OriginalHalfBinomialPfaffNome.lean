import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.OriginalHalfBinomialPfaffNome
import Reg.Support.SingleDependentReadout

/-! Source-bound observations of the signed period jumps and the norm bound of the extension. -/

noncomputable section

open _root_.D5.S3.Analytic.OriginalHalfBinomialSlitPeriod
open _root_.D5.S3.Analytic.OriginalHalfBinomialPfaffNome
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Complex LeanInformationAudit

namespace Reg.D5.S3.Analytic.OriginalHalfBinomialPfaffNome

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℂ)

private def ratio : Realization signature :=
  realize signature (fun _ _ z => tau z) (fun e => nomatch e)

private def zero : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem ratio_dependence : ObservationalDependence signature ratio := by
  intro i
  refine ⟨(), I, I / (I - 1), ?_⟩
  change tau I ≠ tau (I / (I - 1))
  rw [tau_pfaff_upper (r := I) (by simp)]
  exact fun h => one_ne_zero (add_left_cancel (h.trans (add_zero _).symm))

namespace Upper

private def arena : Arena where
  signature := signature
  Law R := ∀ {r : ℂ}, 0 < r.im → R.readout () () r = tau (r / (r - 1)) + 1

private theorem rejected_fails : ¬ arena.Law zero := by
  intro h
  have he := h (r := I) (by simp)
  have hj := tau_pfaff_upper (r := I) (by simp)
  have hz : tau I = 0 := hj.trans he.symm
  have hd : I ∈ doubleSlit := by
    exact ⟨Complex.mem_slitPlane_iff.2 (Or.inr (by simp)),
      Complex.mem_slitPlane_iff.2 (Or.inr (by simp))⟩
  simpa [hz] using tau_im_pos hd

def family : Registration arena (type_of% @tau_pfaff_upper) where
  actual := ratio
  bridge := Iff.rfl
  variation := ⟨@tau_pfaff_upper, zero, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law ratio zero rejected_fails
  dependence := ratio_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@tau_pfaff_upper) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.OriginalHalfBinomialPfaffNome.Upper.unit
  realizationName := `Reg.D5.S3.Analytic.OriginalHalfBinomialPfaffNome.Upper.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => tau z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.OriginalHalfBinomialPfaffNome
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Upper

namespace Lower

private def arena : Arena where
  signature := signature
  Law R := ∀ {r : ℂ}, r.im < 0 → R.readout () () r = tau (r / (r - 1)) - 1

private theorem rejected_fails : ¬ arena.Law zero := by
  intro h
  have he := h (r := (-I)) (by simp)
  have hj := tau_pfaff_lower (r := (-I)) (by simp)
  have hz : tau (-I) = 0 := hj.trans he.symm
  have hd : (-I) ∈ doubleSlit := by
    exact ⟨Complex.mem_slitPlane_iff.2 (Or.inr (by simp)),
      Complex.mem_slitPlane_iff.2 (Or.inr (by simp))⟩
  simpa [hz] using tau_im_pos hd

def family : Registration arena (type_of% @tau_pfaff_lower) where
  actual := ratio
  bridge := Iff.rfl
  variation := ⟨@tau_pfaff_lower, zero, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law ratio zero rejected_fails
  dependence := ratio_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@tau_pfaff_lower) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.OriginalHalfBinomialPfaffNome.Lower.unit
  realizationName := `Reg.D5.S3.Analytic.OriginalHalfBinomialPfaffNome.Lower.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => tau z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.OriginalHalfBinomialPfaffNome
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Lower

namespace Extension

private def actual : Realization signature :=
  realize signature (fun _ _ z => negativeChartNome z) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

private def arena : Arena where
  signature := signature
  Law R := ∀ (x : ℝ), x < 0 →
    ∃ U : Set ℂ, IsOpen U ∧ (x : ℂ) ∈ U ∧
      AnalyticOnNhd ℂ negativeChartNome U ∧
      (∀ z ∈ U, ‖R.readout () () z‖ < 1) ∧
      (∀ z ∈ U ∩ doubleSlit,
        negativeChartNome z = Complex.exp (Complex.I * (Real.pi : ℂ) * tau z)) ∧
      ∀ m : ℕ, AnalyticOnNhd ℂ (fun z => negativeChartNome z ^ m) U ∧
        (∀ z ∈ U ∩ doubleSlit,
          negativeChartNome z ^ m = Complex.exp (Complex.I * (Real.pi : ℂ) * tau z) ^ m) ∧
        ∀ z ∈ U, negativeChartNome z ^ m =
          (-1 : ℂ) ^ m * Complex.exp (Complex.I * (Real.pi : ℂ) * tau (z / (z - 1))) ^ m

private theorem rejected_fails : ¬ arena.Law rejected := by
  intro h
  obtain ⟨U, _, hU, _, hnorm, _⟩ := h (-1) (by norm_num)
  simpa [rejected, realize] using hnorm (-1 : ℝ) hU

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  let s : ℂ := I / (I - 1)
  have hs : s - 1 ≠ 0 := by
    have he : s - 1 = 1 / (I - 1) := by
      dsimp [s]
      have hn : I - 1 ≠ 0 := by
        intro h
        have hh := congrArg Complex.im h
        simp at hh
      field_simp
      ring
    rw [he]
    exact div_ne_zero one_ne_zero (by
      intro h
      have hh := congrArg Complex.im h
      simp at hh)
  have hinv : s / (s - 1) = I := by
    apply (div_eq_iff hs).2
    have hn : I - 1 ≠ 0 := by
      intro h
      have hh := congrArg Complex.im h
      simp at hh
    dsimp [s]
    field_simp
    ring
  have hπ : Complex.exp (I * (Real.pi : ℂ)) = -1 := by
    rw [mul_comm, Complex.exp_pi_mul_I]
  have he : Complex.exp (I * (Real.pi : ℂ) * tau I) =
      -Complex.exp (I * (Real.pi : ℂ) * tau s) := by
    rw [tau_pfaff_upper (r := I) (by simp), mul_add, mul_one, Complex.exp_add, hπ]
    simp [s]
  refine ⟨(), I, s, ?_⟩
  change negativeChartNome I ≠ negativeChartNome s
  unfold negativeChartNome
  change -Complex.exp (I * (Real.pi : ℂ) * tau s) ≠
    -Complex.exp (I * (Real.pi : ℂ) * tau (s / (s - 1)))
  rw [hinv, he, neg_neg]
  intro h
  exact Complex.exp_ne_zero _ (by linear_combination -(1 / 2 : ℂ) * h)

def family : Registration arena (type_of% @negative_real_nome_extension) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@negative_real_nome_extension, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_fails
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@negative_real_nome_extension) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.OriginalHalfBinomialPfaffNome.Extension.unit
  realizationName := `Reg.D5.S3.Analytic.OriginalHalfBinomialPfaffNome.Extension.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => negativeChartNome z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.OriginalHalfBinomialPfaffNome
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "body", "arg", "arg", "arg", "fn", "arg", "body", "body", "fn", "arg", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Extension

end Reg.D5.S3.Analytic.OriginalHalfBinomialPfaffNome
