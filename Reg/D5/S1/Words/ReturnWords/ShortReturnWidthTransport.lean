import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import Reg.Support.SourceSelection
import D5.S1.Words.ReturnWords.ShortReturnWidthTransport

/-! Full source telescopes with explicit arithmetic readouts and family interventions. -/

namespace Reg.D5.S1.Words.ReturnWords.ShortReturnWidthTransport
open _root_.D5.S1.Words.ReturnWords.ShortReturnWidthTransport
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
noncomputable section

namespace Length

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ a b => Nat.lcm a b) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {a b n p : ℕ}, 0 < p → p ∣ a → p ∣ b → a ≤ n → b ≤ 2 * n - 1 →
    R.readout () a b ≤ p * (n / p) * ((2 * n - 1) / p)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h (a := 0) (b := 0) (n := 0) (p := 1)
    (by decide) (by simp) (by simp) (by simp) (by simp)
  norm_num [rejected, realize] at hbad

def source : Registration arena (type_of% @synchronized_length_le_phase_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@synchronized_length_le_phase_bound, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨1, 0, 1, ?_⟩
    norm_num [actual, realize]

def audit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@synchronized_length_le_phase_bound) (Realization signature) Unit Unit := {
  unitName := `D5.S1.Words.ReturnWords.ShortReturnWidthTransport.synchronized_length_le_phase_bound.__information_unit
  realizationName := `Reg.D5.S1.Words.ReturnWords.ShortReturnWidthTransport.Length.source
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ a b => Nat.lcm a b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.ReturnWords.ShortReturnWidthTransport
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Length

namespace Ratio

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℝ (fun _ => ℕ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ g M => g ^ M / (1 - g ^ M)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {g : ℝ}, 0 < g → g < 1 → ∀ {L M : ℕ}, 0 < L → L ≤ M →
    R.readout () g M ≤ g ^ L / (1 - g ^ L)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h (g := 1 / 2) (by norm_num) (by norm_num) (L := 1) (M := 1)
    (by decide) (by decide)
  norm_num [rejected, realize] at hbad

def source : Registration arena (type_of% @contraction_ratio_antitone) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@contraction_ratio_antitone, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨1 / 2, 1, 2, ?_⟩
    norm_num [actual, realize]

def audit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@contraction_ratio_antitone) (Realization signature) Unit Unit := {
  unitName := `D5.S1.Words.ReturnWords.ShortReturnWidthTransport.contraction_ratio_antitone.__information_unit
  realizationName := `Reg.D5.S1.Words.ReturnWords.ShortReturnWidthTransport.Ratio.source
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ g M => g ^ M / (1 - g ^ M)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.ReturnWords.ShortReturnWidthTransport
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Ratio

namespace Width

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature (Σ _ : ℕ, Σ _ : ℕ, ℝ)
    (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ x d =>
    x.2.2 ^ (x.2.1 * (x.1 / x.2.1) * ((2 * x.1 - 1) / x.2.1)) /
      (1 - x.2.2 ^ (x.2.1 * (x.1 / x.2.1) * ((2 * x.1 - 1) / x.2.1))) * d)
    (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {a b n p : ℕ} {g d w : ℝ},
    0 < g → g < 1 → 0 ≤ d → 0 < p → 0 < a → 0 < b → p ∣ a → p ∣ b →
    a ≤ n → b ≤ 2 * n - 1 →
    g ^ Nat.lcm a b * d ≤ (1 - g ^ Nat.lcm a b) * w →
    R.readout () ⟨n, ⟨p, g⟩⟩ d ≤ w

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h (a := 1) (b := 1) (n := 1) (p := 1) (g := 1 / 2) (d := 0) (w := 0)
    (by norm_num) (by norm_num) (by norm_num) (by decide) (by decide) (by decide)
    (by simp) (by simp) (by decide) (by decide) (by simp)
  norm_num [rejected, realize] at hbad

def source : Registration arena (type_of% @short_return_width_lower_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@short_return_width_lower_bound, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    exact ⟨⟨1, ⟨1, 1 / 2⟩⟩, 0, 1, by norm_num [actual, realize]⟩

def audit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@short_return_width_lower_bound) (Realization signature) Unit Unit := {
  unitName := `D5.S1.Words.ReturnWords.ShortReturnWidthTransport.short_return_width_lower_bound.__information_unit
  realizationName := `Reg.D5.S1.Words.ReturnWords.ShortReturnWidthTransport.Width.source
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ x d =>
    x.2.2 ^ (x.2.1 * (x.1 / x.2.1) * ((2 * x.1 - 1) / x.2.1)) /
      (1 - x.2.2 ^ (x.2.1 * (x.1 / x.2.1) * ((2 * x.1 - 1) / x.2.1))) * d)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.ReturnWords.ShortReturnWidthTransport
    definition := none
    coordinates := #[2, 3, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Width

end
end Reg.D5.S1.Words.ReturnWords.ShortReturnWidthTransport
