import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import Reg.Support.SourceSelection
import D5.S1.Words.ReturnWords.ShortReturnWidthTransport

/-! Full source telescopes with explicit arithmetic readouts and family interventions. -/

namespace Reg.D5.S1.Words.ReturnWords.ShortReturnWidthTransport
open _root_.D5.S1.Words.ReturnWords.ShortReturnWidthTransport
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
noncomputable section

namespace Chain

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature (Σ _ : ℕ, ℝ) (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ t δ => (t.1 : ℝ) * δ + t.2) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {k : ℕ} (x : ℕ → ℝ) {δ ℓ u w : ℝ}, u ≤ x 0 →
    (∀ i < k, x i + δ ≤ x (i + 1)) → x k + ℓ ≤ u + w →
    R.readout () ⟨k, ℓ⟩ δ ≤ w

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h (k := 0) (fun _ => 0) (δ := 0) (ℓ := 0) (u := 0) (w := 0)
    (by norm_num) (by simp) (by norm_num)
  norm_num [rejected, realize] at hbad

def source : Registration arena (type_of% @finite_interval_chain_packing) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@finite_interval_chain_packing, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    exact ⟨⟨1, 0⟩, 0, 1, by norm_num [actual, realize]⟩

def audit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@finite_interval_chain_packing) (Realization signature) Unit Unit := {
  unitName := `D5.S1.Words.ReturnWords.ShortReturnWidthTransport.finite_interval_chain_packing.__information_unit
  realizationName := `Reg.D5.S1.Words.ReturnWords.ShortReturnWidthTransport.Chain.source
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ t δ => (t.1 : ℝ) * δ + t.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.ReturnWords.ShortReturnWidthTransport
    definition := none
    coordinates := #[0, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Chain

namespace Packing

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature (Σ _ : ℕ × ℕ, ℝ) (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ t d => (t.1.1 : ℝ) * (t.2 ^ t.1.2 * d)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {k L : ℕ} {g d w u : ℝ} (x : ℕ → ℝ),
    0 < g → 0 ≤ w →
    (∀ i ≤ k, Set.Icc (u + g ^ L * x i) (u + g ^ L * (x i + w)) ⊆
      Set.Icc u (u + w)) →
    (∀ i < k, x i + d ≤ x (i + 1)) →
    R.readout () ⟨(k, L), g⟩ d ≤ (1 - g ^ L) * w

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h (k := 1) (L := 1) (g := 1) (d := 0) (w := 0) (u := 0)
    (fun _ => 0) (by norm_num) (by norm_num)
    (by intro i hi; simp) (by intro i hi; norm_num)
  norm_num [rejected, realize] at hbad

def source : Registration arena (type_of% @affine_cylinder_chain_packing) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@affine_cylinder_chain_packing, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    exact ⟨⟨(1, 1), 1⟩, 0, 1, by norm_num [actual, realize]⟩

def audit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@affine_cylinder_chain_packing) (Realization signature) Unit Unit := {
  unitName := `D5.S1.Words.ReturnWords.ShortReturnWidthTransport.affine_cylinder_chain_packing.__information_unit
  realizationName := `Reg.D5.S1.Words.ReturnWords.ShortReturnWidthTransport.Packing.source
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ t d => (t.1.1 : ℝ) * (t.2 ^ t.1.2 * d)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.ReturnWords.ShortReturnWidthTransport
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Packing

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
  Reg.Support.SingleDependentReadout.signature (Σ _ : ℕ, Σ _ : ℕ, Σ _ : ℕ, ℝ)
    (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ x d =>
    x.2.2.2 ^ (x.2.1 * (x.1 / x.2.1) * ((2 * x.1 - 1) / x.2.1)) /
      (1 - x.2.2.2 ^ (x.2.1 * (x.1 / x.2.1) * ((2 * x.1 - 1) / x.2.1))) * ((x.2.2.1 : ℝ) * d))
    (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {a b n p k : ℕ} {g d w u : ℝ} (x : ℕ → ℝ),
    0 < g → g < 1 → 0 ≤ d → 0 ≤ w → 0 < p →
    0 < a → 0 < b → p ∣ a → p ∣ b → a ≤ n → b ≤ 2 * n - 1 →
    (∀ i ≤ k, Set.Icc (u + g ^ Nat.lcm a b * x i)
      (u + g ^ Nat.lcm a b * (x i + w)) ⊆ Set.Icc u (u + w)) →
    (∀ i < k, x i + d ≤ x (i + 1)) →
    R.readout () ⟨n, ⟨p, ⟨k, g⟩⟩⟩ d ≤ w

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h (a := 1) (b := 1) (n := 1) (p := 1) (k := 1)
    (g := 1 / 2) (d := 0) (w := 0) (u := 0) (fun _ => 0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide)
    (by decide) (by decide) (by simp) (by simp) (by decide) (by decide)
    (by intro i hi; simp) (by intro i hi; norm_num)
  norm_num [rejected, realize] at hbad

def source : Registration arena (type_of% @short_return_width_lower_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@short_return_width_lower_bound, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    exact ⟨⟨1, ⟨1, ⟨1, 1 / 2⟩⟩⟩, 0, 1, by norm_num [actual, realize]⟩

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
    x.2.2.2 ^ (x.2.1 * (x.1 / x.2.1) * ((2 * x.1 - 1) / x.2.1)) /
      (1 - x.2.2.2 ^ (x.2.1 * (x.1 / x.2.1) * ((2 * x.1 - 1) / x.2.1))) * ((x.2.2.1 : ℝ) * d)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.ReturnWords.ShortReturnWidthTransport
    definition := none
    coordinates := #[2, 3, 4, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Width

end
end Reg.D5.S1.Words.ReturnWords.ShortReturnWidthTransport
