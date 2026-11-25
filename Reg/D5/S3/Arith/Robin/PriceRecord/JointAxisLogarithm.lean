import D5.S3.Arith.Robin.PriceRecord.JointAxisLogarithm
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

/-! Observations of the joint Robin logarithm and its exact derivative and root laws. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Reg.D5.S3.Arith.Robin.PriceRecord.JointAxisLogarithm

open LeanInformationAudit Real
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Reg.Support.SingleDependentReadout (signature sensitivity)
open _root_.D5.S3.Arith.Robin.PriceRecord.JointAxisLogarithm

namespace NaturalCone

abbrev readoutSignature := signature (Σ _ : ℕ, ℕ) (fun _ => ℕ) (fun _ => ℝ)

def actual : Realization readoutSignature :=
  realize readoutSignature
    (fun _ hp q => omegaThree (hp.2 : ℝ) (hp.1 : ℝ) (q : ℝ))
    (fun e => nomatch e)

def rejected : Realization readoutSignature :=
  realize readoutSignature
    (fun _ _ _ => 0)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := readoutSignature
  Law R := ∀ {p h q : ℕ}, 0 < h → h < p → 11 * h < 7 * q → 5 * q < 8 * h →
    R.readout () ⟨p, h⟩ q ≠ 0

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (p := 13) (h := 12) (q := 19) (by decide) (by decide) (by decide) (by decide) rfl

private theorem dependence : ObservationalDependence readoutSignature actual := by
  intro _
  refine ⟨⟨1, 0⟩, 0, 1, ?_⟩
  simpa [actual, realize, omegaThree] using (log_pos (by norm_num : (1 : ℝ) < 2)).ne'

def family : Registration arena (type_of% @omegaThree_ne_zero) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@omegaThree_ne_zero, rejected, rejected_law⟩
  sensitivity := sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@omegaThree_ne_zero) (Realization readoutSignature) Unit Unit where
  unitName := `Reg.D5.S3.Arith.Robin.PriceRecord.JointAxisLogarithm.NaturalCone.unit
  realizationName := `Reg.D5.S3.Arith.Robin.PriceRecord.JointAxisLogarithm.NaturalCone.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize readoutSignature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.PriceRecord.JointAxisLogarithm
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn",
        "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end NaturalCone

namespace IntegerCone

abbrev readoutSignature := signature (Σ _ : ℤ, ℤ) (fun _ => ℤ) (fun _ => ℝ)

def actual : Realization readoutSignature :=
  realize readoutSignature
    (fun _ hp q => omegaThree (hp.2 : ℝ) (hp.1 : ℝ) (q : ℝ))
    (fun e => nomatch e)

def rejected : Realization readoutSignature :=
  realize readoutSignature
    (fun _ _ _ => 0)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := readoutSignature
  Law R := ∀ {p h q : ℤ}, 0 < h → h < p → 11 * h < 7 * q → 5 * q < 8 * h →
    R.readout () ⟨p, h⟩ q ≠ 0

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (p := 13) (h := 12) (q := 19) (by decide) (by decide) (by decide) (by decide) rfl

private theorem dependence : ObservationalDependence readoutSignature actual := by
  intro _
  refine ⟨⟨1, 0⟩, 0, 1, ?_⟩
  simpa [actual, realize, omegaThree] using (log_pos (by norm_num : (1 : ℝ) < 2)).ne'

def family : Registration arena (type_of% @omegaThree_ne_zero_int) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@omegaThree_ne_zero_int, rejected, rejected_law⟩
  sensitivity := sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@omegaThree_ne_zero_int) (Realization readoutSignature) Unit Unit where
  unitName := `Reg.D5.S3.Arith.Robin.PriceRecord.JointAxisLogarithm.IntegerCone.unit
  realizationName := `Reg.D5.S3.Arith.Robin.PriceRecord.JointAxisLogarithm.IntegerCone.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize readoutSignature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.PriceRecord.JointAxisLogarithm
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn",
        "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end IntegerCone

namespace FirstDerivative

abbrev readoutSignature := signature (Σ _ : ℝ, ℝ) (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization readoutSignature :=
  realize readoutSignature
    (fun _ hp q => -(hp.1 * q * (q - hp.1) / (hp.2 * (hp.2 + hp.1) * (hp.2 + q))))
    (fun e => nomatch e)

def rejected : Realization readoutSignature :=
  realize readoutSignature
    (fun _ hp q => (-(hp.1 * q * (q - hp.1) / (hp.2 * (hp.2 + hp.1) * (hp.2 + q)))) + 1)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := readoutSignature
  Law R := ∀ {h p q : ℝ}, 0 < p → 0 < h → 0 < q →
    HasDerivAt (fun x : ℝ => omegaThree h x q) (R.readout () ⟨h, p⟩ q) p

private theorem rejected_law : ¬ arena.Law rejected := by
  intro hh
  have he := (omegaThree_hasDerivAt_p (h := 1) (p := 1) (q := 1)
    one_pos one_pos one_pos).unique
      (hh (h := 1) (p := 1) (q := 1) one_pos one_pos one_pos)
  change -((1 : ℝ) * (1 : ℝ) * ((1 : ℝ) - (1 : ℝ)) / ((1 : ℝ) * ((1 : ℝ) + (1 : ℝ)) * ((1 : ℝ) + (1 : ℝ)))) = _ at he
  dsimp [rejected, realize] at he
  linarith only [he]

private theorem dependence : ObservationalDependence readoutSignature actual := by
  intro _
  refine ⟨⟨1, 1⟩, 1, 2, ?_⟩
  change -((1 : ℝ) * (1 : ℝ) * ((1 : ℝ) - (1 : ℝ)) / ((1 : ℝ) * ((1 : ℝ) + (1 : ℝ)) * ((1 : ℝ) + (1 : ℝ)))) ≠
    -((1 : ℝ) * (2 : ℝ) * ((2 : ℝ) - (1 : ℝ)) / ((1 : ℝ) * ((1 : ℝ) + (1 : ℝ)) * ((1 : ℝ) + (2 : ℝ))))
  norm_num

def family : Registration arena (type_of% @omegaThree_hasDerivAt_p) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@omegaThree_hasDerivAt_p, rejected, rejected_law⟩
  sensitivity := sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@omegaThree_hasDerivAt_p) (Realization readoutSignature) Unit Unit where
  unitName := `Reg.D5.S3.Arith.Robin.PriceRecord.JointAxisLogarithm.FirstDerivative.unit
  realizationName := `Reg.D5.S3.Arith.Robin.PriceRecord.JointAxisLogarithm.FirstDerivative.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize readoutSignature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.PriceRecord.JointAxisLogarithm
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn",
        "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end FirstDerivative

namespace SecondDerivative

abbrev readoutSignature := signature (Σ _ : ℝ, ℝ) (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization readoutSignature :=
  realize readoutSignature
    (fun _ hp q => -log 2 + log (1 + hp.1 / hp.2) - hp.1 / (hp.2 + q))
    (fun e => nomatch e)

def rejected : Realization readoutSignature :=
  realize readoutSignature
    (fun _ hp q => (-log 2 + log (1 + hp.1 / hp.2) - hp.1 / (hp.2 + q)) + 1)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := readoutSignature
  Law R := ∀ {h p q : ℝ}, 0 < p → 0 < h → 0 < q →
    HasDerivAt (fun y : ℝ => omegaThree h p y) (R.readout () ⟨h, p⟩ q) q

private theorem rejected_law : ¬ arena.Law rejected := by
  intro hh
  have he := (omegaThree_hasDerivAt_q (h := 1) (p := 1) (q := 1)
    one_pos one_pos one_pos).unique
      (hh (h := 1) (p := 1) (q := 1) one_pos one_pos one_pos)
  change -log 2 + log (1 + (1 : ℝ) / (1 : ℝ)) - (1 : ℝ) / ((1 : ℝ) + (1 : ℝ)) = _ at he
  dsimp [rejected, realize] at he
  linarith only [he]

private theorem dependence : ObservationalDependence readoutSignature actual := by
  intro _
  refine ⟨⟨1, 1⟩, 1, 2, ?_⟩
  change -log 2 + log (1 + (1 : ℝ) / (1 : ℝ)) - (1 : ℝ) / ((1 : ℝ) + (1 : ℝ)) ≠
    -log 2 + log (1 + (1 : ℝ) / (1 : ℝ)) - (1 : ℝ) / ((1 : ℝ) + (2 : ℝ))
  norm_num

def family : Registration arena (type_of% @omegaThree_hasDerivAt_q) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@omegaThree_hasDerivAt_q, rejected, rejected_law⟩
  sensitivity := sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@omegaThree_hasDerivAt_q) (Realization readoutSignature) Unit Unit where
  unitName := `Reg.D5.S3.Arith.Robin.PriceRecord.JointAxisLogarithm.SecondDerivative.unit
  realizationName := `Reg.D5.S3.Arith.Robin.PriceRecord.JointAxisLogarithm.SecondDerivative.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize readoutSignature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.PriceRecord.JointAxisLogarithm
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn",
        "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end SecondDerivative

namespace Rectangle

abbrev readoutSignature := signature (Σ _ : ℝ, ℝ) (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization readoutSignature :=
  realize readoutSignature
    (fun _ hp q => omegaThree hp.1 hp.2 q)
    (fun e => nomatch e)

def rejected : Realization readoutSignature :=
  realize readoutSignature
    (fun _ hp q => omegaThree hp.1 hp.2 q + 1)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := readoutSignature
  Law R := ∀ {h p q s r X : ℝ}, 1 ≤ h → 4 ≤ X → X ≤ s → 3 / 2 ≤ r → r ≤ 2 →
    |p - h * s| ≤ 1 / 2 → |q - h * r| ≤ 1 / 2 →
    |R.readout () ⟨h, p⟩ q - omegaThree h (h * s) (h * r)| ≤
      48 / X ^ 3 * |p - h * s| + 2 * |q - h * r|

private theorem rejected_law : ¬ arena.Law rejected := by
  intro hh
  have he := hh (h := 1) (p := 4) (q := 2) (s := 4) (r := 2) (X := 4)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  norm_num [rejected, realize] at he

private theorem dependence : ObservationalDependence readoutSignature actual := by
  intro _
  refine ⟨⟨0, 1⟩, 0, 1, ?_⟩
  change omegaThree 0 1 0 ≠ omegaThree 0 1 1
  simpa [omegaThree] using (log_pos (by norm_num : (1 : ℝ) < 2)).ne'

def family : Registration arena (type_of% @abs_omegaThree_sub_le) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@abs_omegaThree_sub_le, rejected, rejected_law⟩
  sensitivity := sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@abs_omegaThree_sub_le) (Realization readoutSignature) Unit Unit where
  unitName := `Reg.D5.S3.Arith.Robin.PriceRecord.JointAxisLogarithm.Rectangle.unit
  realizationName := `Reg.D5.S3.Arith.Robin.PriceRecord.JointAxisLogarithm.Rectangle.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize readoutSignature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.PriceRecord.JointAxisLogarithm
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "fn", "arg", "arg", "fn",
        "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Rectangle

namespace RootPhases

abbrev readoutSignature := signature (Σ _ : ℝ, Σ _ : ℝ, Σ _ : ℝ, ℝ) (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization readoutSignature :=
  realize readoutSignature
    (fun _ p e₃ => p.1 * ((p.2.2.1 / p.2.1) * p.2.2.2 - e₃))
    (fun e => nomatch e)

def rejected : Realization readoutSignature :=
  realize readoutSignature
    (fun _ p e₃ => p.1 * ((p.2.2.1 / p.2.1) * p.2.2.2 - e₃) + 1)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := readoutSignature
  Law R := ∀ {h L a b e₂ e₃ : ℝ}, 0 < h → 0 < L → 0 < a → 0 < b →
    a + log (1 + a / L) = log 2 + e₂ → b + log (1 + b / L) = log 3 + e₃ →
    omegaThree h (h * (L / a)) (h * (b / a)) = R.readout () ⟨h, a, b, e₂⟩ e₃

private theorem rejected_law : ¬ arena.Law rejected := by
  intro hh
  let e₂ := 1 + log (1 + 1 / (1 : ℝ)) - log 2
  let e₃ := 1 + log (1 + 1 / (1 : ℝ)) - log 3
  have he₂ : 1 + log (1 + 1 / (1 : ℝ)) = log 2 + e₂ := by dsimp [e₂]; ring
  have he₃ : 1 + log (1 + 1 / (1 : ℝ)) = log 3 + e₃ := by dsimp [e₃]; ring
  have hb := hh one_pos one_pos one_pos one_pos he₂ he₃
  have ha := omegaThree_at_root_phases one_pos one_pos one_pos one_pos he₂ he₃
  have he := ha.symm.trans hb
  dsimp [rejected, realize] at he
  linarith only [he]

private theorem dependence : ObservationalDependence readoutSignature actual := by
  intro _
  refine ⟨⟨1, 1, 1, 0⟩, 0, 1, ?_⟩
  change (1 : ℝ) * ((1 / 1) * 0 - 0) ≠ 1 * ((1 / 1) * 0 - 1)
  norm_num

def family : Registration arena (type_of% @omegaThree_at_root_phases) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@omegaThree_at_root_phases, rejected, rejected_law⟩
  sensitivity := sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@omegaThree_at_root_phases) (Realization readoutSignature) Unit Unit where
  unitName := `Reg.D5.S3.Arith.Robin.PriceRecord.JointAxisLogarithm.RootPhases.unit
  realizationName := `Reg.D5.S3.Arith.Robin.PriceRecord.JointAxisLogarithm.RootPhases.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize readoutSignature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.PriceRecord.JointAxisLogarithm
    definition := none
    coordinates := #[0, 2, 3, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body",
        "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end RootPhases

end Reg.D5.S3.Arith.Robin.PriceRecord.JointAxisLogarithm
