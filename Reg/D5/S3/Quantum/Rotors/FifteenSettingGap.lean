import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Rotors.FifteenSettingGap
import Reg.Support.SingleDependentReadout
import Mathlib.Tactic.FinCases

/-! Source-bound interventions for the base-vector normalization and the base-pair error. -/

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Rotors.FifteenSettingGap
open LeanInformationAudit Finset Real
open scoped InnerProductSpace
namespace Reg.D5.S3.Quantum.Rotors.FifteenSettingGap
noncomputable section

private abbrev V := EuclideanSpace ℝ (Fin 4)
private def e : V := EuclideanSpace.single 0 1
private theorem he : ‖e‖ = 1 := by simp [e, EuclideanSpace.single, PiLp.norm_single]

namespace Frame

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => V) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => ‖x‖) (fun e => nomatch e)
def discarded : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (q : Fin 5 → V) (p : Fin 5 → Fin 5 → V), (∀ i, R.readout () () (q i) = 1) →
    (∀ i j, i < j → ‖p i j‖ = 1) →
    5 / 8 ≤ pairSum (fun i j => ⟪q i, q j⟫_ℝ ^ 2) ∧
      5 / (4 * (1 + √2) ^ 2) ≤ pairSum (fun i j => ‖q i + q j - √2 • p i j‖ ^ 2)

private theorem discarded_fails : ¬arena.Law discarded := by
  intro law
  have h := (law (fun _ => 0) (fun _ _ => e) (fun _ => rfl) (fun _ _ _ => he)).1
  norm_num [pairSum] at h

def family : Registration arena (type_of% @fifteen_setting_gap) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨fifteen_setting_gap, discarded, discarded_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual discarded discarded_fails
  dependence := by
    intro i
    exact ⟨(), (0 : V), e, by change ‖(0 : V)‖ ≠ ‖e‖; simp [he]⟩

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Rotors.FifteenSettingGap.fifteen_setting_gap)
    (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Rotors.FifteenSettingGap.Frame.unit
  realizationName := `Reg.D5.S3.Quantum.Rotors.FifteenSettingGap.Frame.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => ‖x‖) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Rotors.FifteenSettingGap
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "domain", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Frame

namespace Mixture

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => |x|) (fun e => nomatch e)
def discarded : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (w : Fin n → ℝ)
    (q : Fin 5 → Fin n → V)
    (p : Fin 5 → Fin 5 → Fin n → V)
    (hw : ∀ t, 0 ≤ w t) (hw1 : ∑ t, w t = 1) (hq : ∀ i t, ‖q i t‖ = 1)
    (hp : ∀ i j, i < j → ∀ t, ‖p i j t‖ = 1) (δ : ℝ)
    (errors : ∀ i j, i < j →
      R.readout () () (comparison w (q i) (q j) - 1 / 2) ≤ δ ∧
      |comparison w (q i) (p i j) - (1 + √2 / 2) / 2| ≤ δ ∧
      |comparison w (q j) (p i j) - (1 + √2 / 2) / 2| ≤ δ) ,
    5 / (80 * (1 + √2) ^ 2 * (2 + 4 * √2)) ≤ δ

private theorem discarded_fails : ¬arena.Law discarded := by
  intro law
  let c : ℝ := (1 + √2 / 2) / 2
  let w : Fin 2 → ℝ := ![c, 1 - c]
  let mid : Fin 2 → V := ![e, -e]
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have sr := Real.sqrt_nonneg 2
  have hw : ∀ t, 0 ≤ w t := by
    intro t
    fin_cases t <;> simp [w, c] <;> nlinarith
  have hw1 : ∑ t, w t = 1 := by simp [w, Fin.sum_univ_two]
  have hm : ∀ t, ‖mid t‖ = 1 := by intro t; fin_cases t <;> simp [mid, he]
  have hcomp : comparison w (fun _ => e) mid = c := by
    simp [comparison, w, mid, Fin.sum_univ_two, real_inner_self_eq_norm_sq, he]
    ring
  have law' := law w (fun _ _ => e) (fun _ _ => mid) hw hw1 (fun _ _ => he)
    (fun _ _ _ => hm) 0 (by
      intro i j h
      change 0 ≤ (0 : ℝ) ∧ |comparison w (fun _ => e) mid - c| ≤ 0 ∧
        |comparison w (fun _ => e) mid - c| ≤ 0
      simp [hcomp])
  exact (not_lt_of_ge law') (by positivity)

def family : Registration arena (type_of% @fixed_mixture_probability_gap) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨fixed_mixture_probability_gap, discarded, discarded_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual discarded discarded_fails
  dependence := by
    intro i
    exact ⟨(), (0 : ℝ), (1 : ℝ), by change |(0 : ℝ)| ≠ |(1 : ℝ)|; norm_num⟩

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Rotors.FifteenSettingGap.fixed_mixture_probability_gap)
    (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Rotors.FifteenSettingGap.Mixture.unit
  realizationName := `Reg.D5.S3.Quantum.Rotors.FifteenSettingGap.Mixture.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => |x|) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Rotors.FifteenSettingGap
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "domain", "body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Mixture

end
end Reg.D5.S3.Quantum.Rotors.FifteenSettingGap
