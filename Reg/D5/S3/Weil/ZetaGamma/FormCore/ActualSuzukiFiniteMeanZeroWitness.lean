import Reg.D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiFiniteGammaEnergy

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiFiniteMeanZeroWitness

open MeasureTheory Set Filter
open scoped ENNReal Topology
open _root_.D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiDomainCounterexample
open _root_.D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiFiniteGammaEnergy
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature where
  Params := ℝ
  State _ := ℝ → ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ F => ∫ x : ℝ in Ioi Real.pi, ‖F x‖ ^ 2)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (0 : ℝ)) (fun e => nomatch e)

-- Only the physical mass readout is replaced; every original source clause,
-- including both literal raw ratio inequalities, remains in the law.
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (r : ℝ) (_hr : 1 < r),
    ∃ F : ℝ → ℂ,
      originalPhysicalH6 F ∧
      (∫ s : ℝ, actualSuzukiEvenBProfile F s) = 0 ∧
      (∀ c : ℝ, originalGammaFormDomain c F) ∧
      (∀ x : ℝ, Real.pi ≤ x →
        HasSum (fun k : ℕ => physicalTerm F k x) (F x)) ∧
      (0 < R.readout () r F) ∧
      (1 < (∫ x : ℝ in Ioi Real.pi, x ^ (6 : ℕ) * ‖F x‖ ^ 2) /
        (Real.pi ^ (6 : ℕ) * ∫ x : ℝ in Ioi Real.pi, ‖F x‖ ^ 2)) ∧
      ((∫ x : ℝ in Ioi Real.pi, x ^ (6 : ℕ) * ‖F x‖ ^ 2) /
        (Real.pi ^ (6 : ℕ) * ∫ x : ℝ in Ioi Real.pi, ‖F x‖ ^ 2) < r)

private theorem source_reconstruction :
    (type_of% (@actual_h6_mean_zero_arbitrarily_small_raw_sixth_ratio)) ↔
      arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨F, _, _, _, _, hmass, _, _⟩ := h (2 : ℝ) (by norm_num)
  norm_num [rejected, realize] at hmass

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  obtain ⟨F, _, _, _, _, hmass, _, _⟩ :=
    actual_h6_mean_zero_arbitrarily_small_raw_sixth_ratio (2 : ℝ) (by norm_num)
  refine ⟨(2 : ℝ), (fun _ : ℝ => (0 : ℂ)), F, ?_⟩
  change (∫ x : ℝ in Ioi Real.pi, ‖(fun _ : ℝ => (0 : ℂ)) x‖ ^ 2) ≠
    ∫ x : ℝ in Ioi Real.pi, ‖F x‖ ^ 2
  have hz : (∫ x : ℝ in Ioi Real.pi, ‖(fun _ : ℝ => (0 : ℂ)) x‖ ^ 2) = 0 := by simp
  rw [hz]
  exact ne_of_lt hmass

def family : Registration arena
    (type_of% (@actual_h6_mean_zero_arbitrarily_small_raw_sixth_ratio)) where
  actual := actual
  bridge := source_reconstruction
  variation := ⟨actual_h6_mean_zero_arbitrarily_small_raw_sixth_ratio, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact False.elim (hji (Subsingleton.elim j i))
    · intro e
      exact nomatch e
  dependence := actual_dependence

-- r and hr are lexical binders 0 and 1; F is stateBinder 2.
-- After Exists F, follow four right And branches to select positive mass.
def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@actual_h6_mean_zero_arbitrarily_small_raw_sixth_ratio)
    (Realization signature) Type Unit where
  unitName :=
    `D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiFiniteGammaEnergy.actual_h6_mean_zero_arbitrarily_small_raw_sixth_ratio.__information_unit
  realizationName :=
    `Reg.D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiFiniteMeanZeroWitness.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ F => ∫ x : ℝ in Ioi Real.pi, ‖F x‖ ^ 2)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiFiniteMeanZeroWitness
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "arg", "body", "arg", "arg", "arg", "arg", "fn", "arg", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end
end Reg.D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiFiniteMeanZeroWitness
