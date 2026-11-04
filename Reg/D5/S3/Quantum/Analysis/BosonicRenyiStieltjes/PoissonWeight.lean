import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Analysis.BosonicRenyiStieltjes.PoissonWeight
import Reg.Support.SingleDependentReadout

/-! Source-bound registrations for the power Poisson density and its Stieltjes transform. -/

namespace Reg.D5.S3.Quantum.Analysis.BosonicRenyiStieltjes.PoissonWeight

open _root_.D5.S3.Quantum.Analysis.BosonicRenyiStieltjes.PoissonWeight
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Real Set MeasureTheory

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace DenominatorPos

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℝ (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature
    (fun _ r α => 1 - 2 * r * Real.cos (Real.pi * α) + r ^ 2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature
    (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {α r : ℝ}, 0 < α → α < 2 → α ≠ 1 → 0 < R.readout () r α

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h (α := 1 / 2) (r := 0) (by norm_num) (by norm_num) (by norm_num)
  norm_num [rejected, realize] at hb

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 0, 1, ?_⟩
  norm_num [actual, realize]

def source_registration : Registration arena (type_of% @power_poisson_denominator_pos) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@power_poisson_denominator_pos, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@power_poisson_denominator_pos) (Realization signature) Unit Unit := {
  unitName := Lean.Name.str
    `Reg.D5.S3.Quantum.Analysis.BosonicRenyiStieltjes.PoissonWeight.DenominatorPos
    "unit"
  realizationName := Lean.Name.str
    `Reg.D5.S3.Quantum.Analysis.BosonicRenyiStieltjes.PoissonWeight.DenominatorPos
    "source_registration"
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ r α => 1 - 2 * r * Real.cos (Real.pi * α) + r ^ 2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.BosonicRenyiStieltjes.PoissonWeight
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg", "arg", "arg", "arg", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms registration

end DenominatorPos

namespace SineFactorPos

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature
    (fun _ _ α => -Real.sin (Real.pi * α) / (α - 1)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature
    (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {α : ℝ}, 0 < α → α < 2 → α ≠ 1 → 0 < R.readout () () α

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h (α := 1 / 2) (by norm_num) (by norm_num) (by norm_num)
  norm_num [rejected, realize] at hb

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1 / 2, ?_⟩
  change -Real.sin (Real.pi * 0) / (0 - 1) ≠
    -Real.sin (Real.pi * (1 / 2)) / (1 / 2 - 1)
  rw [show Real.pi * (1 / 2 : ℝ) = Real.pi / 2 by ring, Real.sin_pi_div_two]
  norm_num

def source_registration : Registration arena (type_of% @sine_factor_pos) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@sine_factor_pos, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@sine_factor_pos) (Realization signature) Unit Unit := {
  unitName := Lean.Name.str
    `Reg.D5.S3.Quantum.Analysis.BosonicRenyiStieltjes.PoissonWeight.SineFactorPos
    "unit"
  realizationName := Lean.Name.str
    `Reg.D5.S3.Quantum.Analysis.BosonicRenyiStieltjes.PoissonWeight.SineFactorPos
    "source_registration"
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ α => -Real.sin (Real.pi * α) / (α - 1)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.BosonicRenyiStieltjes.PoissonWeight
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms registration

end SineFactorPos

namespace CosineLtOne

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature
    (fun _ _ α => Real.cos (Real.pi * α)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature
    (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {α : ℝ}, 0 < α → α < 2 → α ≠ 1 → R.readout () () α < 1

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h (α := 1 / 2) (by norm_num) (by norm_num) (by norm_num)
  norm_num [rejected, realize] at hb

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual, realize]

def source_registration : Registration arena (type_of% @cosine_lt_one) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@cosine_lt_one, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@cosine_lt_one) (Realization signature) Unit Unit := {
  unitName := Lean.Name.str
    `Reg.D5.S3.Quantum.Analysis.BosonicRenyiStieltjes.PoissonWeight.CosineLtOne
    "unit"
  realizationName := Lean.Name.str
    `Reg.D5.S3.Quantum.Analysis.BosonicRenyiStieltjes.PoissonWeight.CosineLtOne
    "source_registration"
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ α => Real.cos (Real.pi * α)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.BosonicRenyiStieltjes.PoissonWeight
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms registration

end CosineLtOne

namespace DensityReflection

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℝ (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature
    (fun _ α q => density α q) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature
    (fun _ α q => density α q + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {α q : ℝ}, 0 < q → α ≠ 1 → Real.cos (Real.pi * α) < 1 →
    density α q⁻¹ / q ^ 2 = R.readout () α q

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h (α := 1 / 2) (q := 1) (by norm_num) (by norm_num)
    (cosine_lt_one (by norm_num) (by norm_num) (by norm_num))
  have ha := density_reflection (α := 1 / 2) (q := 1) (by norm_num) (by norm_num)
    (cosine_lt_one (by norm_num) (by norm_num) (by norm_num))
  change density (1 / 2) (1 : ℝ)⁻¹ / 1 ^ 2 = density (1 / 2) 1 + 1 at hb
  linarith

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1 / 2, 0, 1, ?_⟩
  change density (1 / 2) 0 ≠ density (1 / 2) 1
  have hp : 0 < density (1 / 2) 1 := by
    norm_num [density, show Real.pi * (1 / 2 : ℝ) = Real.pi / 2 by ring,
      Real.sin_pi_div_two, Real.cos_pi_div_two]
    positivity
  have hz : density (1 / 2) 0 = 0 := by norm_num [density]
  rw [hz]
  exact ne_of_lt hp

def source_registration : Registration arena (type_of% @density_reflection) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@density_reflection, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@density_reflection) (Realization signature) Unit Unit := {
  unitName := Lean.Name.str
    `Reg.D5.S3.Quantum.Analysis.BosonicRenyiStieltjes.PoissonWeight.DensityReflection
    "unit"
  realizationName := Lean.Name.str
    `Reg.D5.S3.Quantum.Analysis.BosonicRenyiStieltjes.PoissonWeight.DensityReflection
    "source_registration"
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ α q => density α q) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.BosonicRenyiStieltjes.PoissonWeight
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms registration

end DensityReflection

namespace ResolventReflection

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature (Σ _ : ℝ, ℝ) (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature
    (fun _ p q => density (Sigma.fst p) q * q / (1 + Sigma.snd p * q)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature
    (fun _ p q => density (Sigma.fst p) q * q / (1 + Sigma.snd p * q) + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {α r q : ℝ}, 0 < r → 0 < q → α ≠ 1 → Real.cos (Real.pi * α) < 1 →
    |-(q ^ 2)⁻¹| • (density α q⁻¹ / (r + q⁻¹)) = R.readout () ⟨α, r⟩ q

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h (α := 1 / 2) (r := 1) (q := 1)
    (by norm_num) (by norm_num) (by norm_num)
    (cosine_lt_one (by norm_num) (by norm_num) (by norm_num))
  have ha := density_resolvent_reflection (α := 1 / 2) (r := 1) (q := 1)
    (by norm_num) (by norm_num) (by norm_num)
    (cosine_lt_one (by norm_num) (by norm_num) (by norm_num))
  dsimp only [rejected, realize] at hb
  linarith

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1 / 2, 1⟩, 0, 1, ?_⟩
  change density (1 / 2) 0 * 0 / (1 + 1 * 0) ≠
    density (1 / 2) 1 * 1 / (1 + 1 * 1)
  have hp : 0 < density (1 / 2) 1 := by
    norm_num [density, show Real.pi * (1 / 2 : ℝ) = Real.pi / 2 by ring,
      Real.sin_pi_div_two, Real.cos_pi_div_two]
    positivity
  simp only [mul_zero, zero_div, mul_one]
  exact ne_of_lt (div_pos hp (by norm_num))

def source_registration : Registration arena (type_of% @density_resolvent_reflection) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@density_resolvent_reflection, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@density_resolvent_reflection) (Realization signature) Unit Unit := {
  unitName := Lean.Name.str
    `Reg.D5.S3.Quantum.Analysis.BosonicRenyiStieltjes.PoissonWeight.ResolventReflection
    "unit"
  realizationName := Lean.Name.str
    `Reg.D5.S3.Quantum.Analysis.BosonicRenyiStieltjes.PoissonWeight.ResolventReflection
    "source_registration"
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p q => density (Sigma.fst p) q * q / (1 + Sigma.snd p * q)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.BosonicRenyiStieltjes.PoissonWeight
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms registration

end ResolventReflection

namespace StieltjesIntegral

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℝ (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature
    (fun _ α r => 1 / ((α - 1) * (1 - r)) -
      α * r ^ (α - 1) / ((α - 1) * (1 - r ^ α))) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature
    (fun _ α r => (1 / ((α - 1) * (1 - r)) -
      α * r ^ (α - 1) / ((α - 1) * (1 - r ^ α))) + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {α r : ℝ}, 0 < α → α < 2 → α ≠ 1 → 0 < r → r < 1 →
    IntegrableOn (fun q => density α q / (r + q)) (Ioi 0) ∧
      (∫ q in Ioi (0 : ℝ), density α q / (r + q)) = R.readout () α r

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := (h (α := 1 / 2) (r := 1 / 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)).2
  have ha := (stieltjes_integral (α := 1 / 2) (r := 1 / 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)).2
  dsimp only [rejected, realize] at hb
  linarith

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨2, 0, 1, ?_⟩
  norm_num [actual, realize]

def source_registration : Registration arena (type_of% @stieltjes_integral) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@stieltjes_integral, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@stieltjes_integral) (Realization signature) Unit Unit := {
  unitName := Lean.Name.str
    `Reg.D5.S3.Quantum.Analysis.BosonicRenyiStieltjes.PoissonWeight.StieltjesIntegral
    "unit"
  realizationName := Lean.Name.str
    `Reg.D5.S3.Quantum.Analysis.BosonicRenyiStieltjes.PoissonWeight.StieltjesIntegral
    "source_registration"
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ α r => 1 / ((α - 1) * (1 - r)) -
      α * r ^ (α - 1) / ((α - 1) * (1 - r ^ α))) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.BosonicRenyiStieltjes.PoissonWeight
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms registration

end StieltjesIntegral






end
end Reg.D5.S3.Quantum.Analysis.BosonicRenyiStieltjes.PoissonWeight
