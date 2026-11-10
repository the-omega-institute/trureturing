import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Reg.D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
open _root_.D5.S3.Zeros.CompletedZeta
open LeanInformationAudit
open scoped BigOperators ComplexConjugate

namespace StripProduct
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ _ x => x.re * (1 - x.re)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ x => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {rho : ℂ} (_h0 : 0 < rho.re) (_h1 : rho.re < 1),
    0 < R.readout () () rho ∧ rho.re * (1 - rho.re) ≤ 1 / 4
private theorem source_reconstruction :
    (type_of% (@heightRefinement_strip_product_bounds)) ↔ arena.Law actual := Iff.rfl
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := (h (rho := (1 / 2 : ℂ)) (by norm_num) (by norm_num)).1
  norm_num [rejected, realize] at hbad
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0 : ℂ), (1 / 2 : ℂ), ?_⟩
  norm_num [actual, realize]
def family : Registration arena (type_of% (@heightRefinement_strip_product_bounds)) where
  actual := actual
  bridge := source_reconstruction
  variation := ⟨@heightRefinement_strip_product_bounds, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence
def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@heightRefinement_strip_product_bounds) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds.heightRefinement_strip_product_bounds.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds.StripProduct.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => x.re * (1 - x.re)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end StripProduct

namespace PairWeight
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ _ x => pairWeight x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ x => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {rho : ℂ} (_h0 : 0 < rho.re) (_h1 : rho.re < 1),
    0 < pairWeight rho ∧ 1 / (rho.im ^ 2 + 1) ≤ R.readout () () rho
private theorem source_reconstruction :
    (type_of% (@heightRefinement_pairWeight_strip)) ↔ arena.Law actual := Iff.rfl
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := (h (rho := (1 / 2 : ℂ)) (by norm_num) (by norm_num)).2
  norm_num [rejected, realize] at hbad
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0 : ℂ), (1 / 2 : ℂ), ?_⟩
  norm_num [actual, realize, pairWeight, Complex.div_re, Complex.normSq]
def family : Registration arena (type_of% (@heightRefinement_pairWeight_strip)) where
  actual := actual
  bridge := source_reconstruction
  variation := ⟨@heightRefinement_pairWeight_strip, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence
def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@heightRefinement_pairWeight_strip) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds.heightRefinement_pairWeight_strip.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds.PairWeight.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => pairWeight x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end PairWeight

namespace Conjugation
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)
def actual : Realization signature :=
  realize signature (fun _ _ x => actualData.conjugation x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ x => x) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, R.readout () () n ≠ n
private theorem source_reconstruction :
    (type_of% (@heightRefinement_actual_conjugation_ne)) ↔ arena.Law actual := Iff.rfl
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 0 rfl
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  change actualData.conjugation 0 ≠ actualData.conjugation 1
  exact actualData.conjugation.injective.ne (by decide)
def family : Registration arena (type_of% (@heightRefinement_actual_conjugation_ne)) where
  actual := actual
  bridge := source_reconstruction
  variation := ⟨@heightRefinement_actual_conjugation_ne, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence
def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@heightRefinement_actual_conjugation_ne) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds.heightRefinement_actual_conjugation_ne.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds.Conjugation.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => actualData.conjugation x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Conjugation

namespace Denominators
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℂ)
def actual : Realization signature :=
  realize signature (fun _ _ x => actualData.zero x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ x => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, R.readout () () n ≠ 0 ∧ 1 - actualData.zero n ≠ 0 ∧
    6 - actualData.zero n ≠ 0 ∧ 5 + actualData.zero n ≠ 0
private theorem source_reconstruction :
    (type_of% (@heightRefinement_actual_six_denominators)) ↔ arena.Law actual := Iff.rfl
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact (h 0).1 rfl
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, actualData.conjugation 0, ?_⟩
  change actualData.zero 0 ≠ actualData.zero (actualData.conjugation 0)
  rw [actualData.zero_conjugation]
  intro he
  have hi := congrArg Complex.im he
  simp only [Complex.conj_im] at hi
  have hu := actual_ordinate_sq_gt_one 0
  nlinarith
def family : Registration arena (type_of% (@heightRefinement_actual_six_denominators)) where
  actual := actual
  bridge := source_reconstruction
  variation := ⟨@heightRefinement_actual_six_denominators, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence
def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@heightRefinement_actual_six_denominators) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds.heightRefinement_actual_six_denominators.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds.Denominators.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => actualData.zero x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Denominators

namespace LogHalf
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ _ x => Real.log x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ x => x) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (x : ℝ) (_hx : 0 < x), R.readout () () x ≤ x / 2
private theorem source_reconstruction :
    (type_of% (@heightRefinement_log_le_half)) ↔ arena.Law actual := Iff.rfl
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h 2 (by norm_num)
  norm_num [rejected, realize] at hbad
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 1, Real.exp 1, ?_⟩
  norm_num [actual, realize, Real.log_exp]
def family : Registration arena (type_of% (@heightRefinement_log_le_half)) where
  actual := actual
  bridge := source_reconstruction
  variation := ⟨@heightRefinement_log_le_half, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence
def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@heightRefinement_log_le_half) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds.heightRefinement_log_le_half.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds.LogHalf.family
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
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
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
end LogHalf

namespace HeightTenSquare
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ _ x => (actualData.zero x).im ^ 2) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ x => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, 100 < R.readout () () n
private theorem source_reconstruction :
    (type_of% (@heightRefinement_actual_ordinate_sq_gt_hundred)) ↔ arena.Law actual := Iff.rfl
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h 0
  norm_num [rejected, realize] at hbad
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  by_contra h
  have hc : ∀ n : ℕ, (actualData.zero n).im ^ 2 = (actualData.zero 0).im ^ 2 := by
    intro n
    by_contra hn
    exact h ⟨(), n, 0, hn⟩
  have hs : Summable (fun n : ℕ => ((actualData.zero n).im)⁻¹ ^ 2) := by
    apply Summable.of_nonneg_of_le (fun n => sq_nonneg _) (fun n => ?_)
      actual_weighted_inverse_square_summable
    have hm : (1 : ℝ) ≤ actualData.multiplicity n := by
      exact_mod_cast (Nat.succ_le_iff.mpr (actualData.multiplicity_pos n))
    exact le_mul_of_one_le_left (sq_nonneg _) hm
  have hsconst : Summable (fun _ : ℕ => ((actualData.zero 0).im ^ 2)⁻¹) := by
    apply hs.congr
    intro n
    simp only [inv_pow, hc n]
  have hz : ((actualData.zero 0).im ^ 2)⁻¹ = 0 :=
    tendsto_nhds_unique tendsto_const_nhds hsconst.tendsto_atTop_zero
  exact (inv_ne_zero (ne_of_gt (lt_trans (by norm_num) (actual_ordinate_sq_gt_one 0)))) hz
def family : Registration arena (type_of% (@heightRefinement_actual_ordinate_sq_gt_hundred)) where
  actual := actual
  bridge := source_reconstruction
  variation := ⟨@heightRefinement_actual_ordinate_sq_gt_hundred, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence
def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@heightRefinement_actual_ordinate_sq_gt_hundred) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds.heightRefinement_actual_ordinate_sq_gt_hundred.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds.HeightTenSquare.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => (actualData.zero x).im ^ 2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end HeightTenSquare

private theorem sixTerm_pos (n : ℕ) :
    0 < (actualData.multiplicity n : ℝ) * sixWeight (actualData.zero n) := by
  apply mul_pos (by exact_mod_cast actualData.multiplicity_pos n)
  have hs := (actualData.zero_isNontrivial n).2
  obtain ⟨hp, hp4⟩ := heightRefinement_strip_product_bounds hs.1 hs.2
  have hu := heightRefinement_actual_ordinate_sq_gt_hundred n
  let rho := actualData.zero n
  have hre : ((rho * (1 - rho)) * (rho * (1 - rho) + 30)).re =
      (rho.im ^ 2 + rho.re * (1 - rho.re)) *
        (rho.im ^ 2 + rho.re * (1 - rho.re) + 30) -
        rho.im ^ 2 * (1 - 4 * (rho.re * (1 - rho.re))) := by
    simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im,
      Complex.re_ofNat, Complex.im_ofNat]
    ring
  have hreal : 0 < ((rho * (1 - rho)) * (rho * (1 - rho) + 30)).re := by
    rw [hre]
    change 100 < rho.im ^ 2 at hu
    change 0 < rho.re * (1 - rho.re) at hp
    nlinarith [sq_nonneg (rho.im ^ 2 + rho.re * (1 - rho.re)),
      mul_nonneg (sq_nonneg rho.im) hp.le]
  have hn : (rho * (1 - rho)) * (rho * (1 - rho) + 30) ≠ 0 := by
    intro h
    rw [h] at hreal
    exact (lt_irrefl 0) hreal
  change 0 < (1 / ((rho * (1 - rho)) * (rho * (1 - rho) + 30))).re
  rw [one_div, Complex.inv_re]
  exact div_pos hreal (Complex.normSq_pos.mpr hn)

namespace SixSum
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ _ x => (actualData.multiplicity x : ℝ) * sixWeight (actualData.zero x)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ x => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := HasSum (fun n : ℕ => R.readout () () n) (sixDefect / 165)
private theorem source_reconstruction :
    (type_of% (@heightRefinement_actual_six_hasSum)) ↔ arena.Law actual := Iff.rfl
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hz : sixDefect / 165 = 0 := by
    simpa [rejected, realize] using h.tsum_eq.symm
  have hp := sixTerm_pos 0
  have hs := (heightRefinement_actual_six_hasSum).summable
  have ht := hs.le_tsum 0 (fun n _ => (sixTerm_pos n).le)
  rw [heightRefinement_actual_six_hasSum.tsum_eq, hz] at ht
  linarith
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  by_contra h
  have hc : ∀ n : ℕ, actual.readout i () n = actual.readout i () 0 := by
    intro n
    by_contra hn
    exact h ⟨(), n, 0, hn⟩
  have hsconst : Summable (fun _ : ℕ => actual.readout i () 0) := by
    apply heightRefinement_actual_six_hasSum.summable.congr
    intro n
    exact hc n
  have hz : actual.readout i () 0 = 0 :=
    tendsto_nhds_unique tendsto_const_nhds hsconst.tendsto_atTop_zero
  exact (ne_of_gt (sixTerm_pos 0)) hz
def family : Registration arena (type_of% (@heightRefinement_actual_six_hasSum)) where
  actual := actual
  bridge := source_reconstruction
  variation := ⟨@heightRefinement_actual_six_hasSum, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence
def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@heightRefinement_actual_six_hasSum) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds.heightRefinement_actual_six_hasSum.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds.SixSum.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => (actualData.multiplicity x : ℝ) * sixWeight (actualData.zero x)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "fn", "arg", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end SixSum

namespace Endpoint
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Unit) (fun _ => ℂ)
def actual : Realization signature :=
  realize signature (fun _ _ _ => logDeriv xiReading 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := R.readout () () () = (firstLiMass / 2 : ℝ)
theorem source_reconstruction :
    (type_of% (@heightRefinement_one_endpoint_logDeriv)) ↔ arena.Law actual := Iff.rfl
/-- The actual closed source has a singleton state fiber. The enrolled dependent
family template cannot supply its required actual observational dependence. -/
theorem no_actual_dependence : ¬ ObservationalDependence signature actual := by
  intro h
  obtain ⟨p, x, y, hxy⟩ := h ()
  exact hxy rfl
end Endpoint

namespace SixEvaluation
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Unit) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ _ _ => sixDefect) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := R.readout () () () = 593 / 60 + 6 * Real.eulerMascheroniConstant - 11 * Real.log 2 - 5 * Real.log Real.pi + sixQ
theorem source_reconstruction :
    (type_of% (@heightRefinement_sixDefect_evaluation)) ↔ arena.Law actual := Iff.rfl
/-- The actual closed source has a singleton state fiber. The enrolled dependent
family template cannot supply its required actual observational dependence. -/
theorem no_actual_dependence : ¬ ObservationalDependence signature actual := by
  intro h
  obtain ⟨p, x, y, hxy⟩ := h ()
  exact hxy rfl
end SixEvaluation

end Reg.D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
