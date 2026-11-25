import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Fourier.Concentration.WeightedClosePairTail

/-! Dependence of the weighted close-pair estimate on the lower cutoff. -/

namespace Reg.D5.S3.Fourier.Concentration.WeightedClosePairTail

open Finset Set
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Fourier.Concentration.WeightedClosePairTail
open _root_.Reg.Support

noncomputable section

universe u

abbrev signature := SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => reciprocalLogTail x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {J : Type u} (s : Finset (J × J)) (g m w : J → ℝ) {x T C η : ℝ},
    2 ≤ x → x ≤ T → 0 ≤ C → η ≤ x / 2 →
    (∀ i ∈ s, g i.1 ∈ Icc x T ∧ g i.2 ∈ Icc x T) →
    (∀ i ∈ s, |g i.1 - g i.2| ≤ η) →
    (∀ j, 0 ≤ m j) → (∀ j, 0 ≤ w j) → (∀ j, w j ≤ m j / g j) →
    (∀ y ∈ Icc x T,
      (∑ i ∈ s, if max (g i.1) (g i.2) ≤ y then m i.1 * m i.2 else 0) ≤
        C * y * Real.log y) →
    let tail := V.readout () ()
    (∑ i ∈ s, w i.1 * w i.2) ≤ 4 * C * tail x

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro law
  have h := law (J := ULift.{u} Unit) ∅ (fun _ => 2) (fun _ => 0) (fun _ => 0)
    (x := 2) (T := 2) (C := 1) (η := 0)
    (le_refl 2) (le_refl 2) (by norm_num) (by norm_num)
    (by simp) (by simp) (by simp) (by simp) (by simp)
    (fun y hy => by
      simp only [sum_empty, one_mul]
      exact mul_nonneg (by linarith [hy.1]) (Real.log_nonneg (by linarith [hy.1])))
  norm_num [rejected, realize] at h

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨(), 1, Real.exp 2, ?_⟩
  change reciprocalLogTail 1 ≠ reciprocalLogTail (Real.exp 2)
  have h : 3 < Real.exp 2 := (by norm_num : (3 : ℝ) = 2 + 1) ▸
    Real.add_one_lt_exp (by norm_num : (2 : ℝ) ≠ 0)
  have hp : 0 < Real.exp 2 := Real.exp_pos _
  simp only [reciprocalLogTail, Real.log_one, zero_add, div_one, Real.log_exp]
  exact ne_of_gt ((div_lt_one hp).mpr (by linarith))

def evidence : Registration arena.{u} (type_of% @weighted_close_pairs_le.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@weighted_close_pairs_le.{u}, rejected, rejected_law⟩
  sensitivity := SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@weighted_close_pairs_le.{u}) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Concentration.WeightedClosePairTail.unit
  realizationName := `Reg.D5.S3.Fourier.Concentration.WeightedClosePairTail.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => reciprocalLogTail x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.Concentration.WeightedClosePairTail
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Fourier.Concentration.WeightedClosePairTail
