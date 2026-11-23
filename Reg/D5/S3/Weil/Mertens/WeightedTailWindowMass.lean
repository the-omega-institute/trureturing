import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.Mertens.WeightedTailWindowMass
import Reg.D5.S3.Weil.Mertens.WeightedTailInverse

/-! The unweighted tail observed through its negative mass on the test window. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Real Set MeasureTheory LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Weil.Mertens.WeightedTailInverse (a)
open _root_.D5.S3.Weil.Mertens.WeightedTailTransport (tail weightedTail)
open _root_.D5.S3.Weil.Mertens.WeightedTailWindowMass
open _root_.Reg.D5.S3.Weil.Mertens.WeightedTailInverse (signature actual inverseEvidence)

namespace Reg.D5.S3.Weil.Mertens.WeightedTailWindowMass

theorem negative_sqrt_mass {Y X K : ℝ} (hY : 0 < Y) (hYX : Y ≤ X) (hK : 0 ≤ K) :
    (∫ x in Y..X, max (-(-K * sqrt x)) 0 / sqrt x) = (X - Y) * K := by
  calc
    _ = ∫ _ in Y..X, K := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le hYX] at hx
      have hs := sqrt_pos.2 (hY.trans_le hx.1)
      change max (-(-K * sqrt x)) 0 / sqrt x = K
      rw [neg_mul, neg_neg, max_eq_left (mul_nonneg hK hs.le), mul_div_cancel_right₀ _ hs.ne']
    _ = _ := by simp

def rejected : Realization signature :=
  realize signature (fun _ _ _ x => -1 * sqrt x) (fun e => nomatch e)

def exactArena : Arena where
  signature := signature
  Law R := ∀ {k g : ℝ → ℝ} {Y X B c : ℝ}
    (_ : 2 ≤ Y) (_ : Y ≤ X) (_ : X ≤ B) (_ : IntegrableOn k (Ioi Y))
    (_ : IntegrableOn g (Icc Y B))
    (_ : ∀ t ∈ Icc Y B, 0 ≤ g t) (_ : ∀ t ∈ Icc Y B, -weightedTail k t ≤ g t)
    (_ : 0 ≤ c) (_ : -endpointDefect k B ≤ c),
    (∫ x in Y..X, max (-R.readout () () k x) 0 / sqrt x) ≤
      (∫ t in Y..X, (a t / sqrt t) * g t) +
      (∫ t in Y..B, triangleWeight Y X t * g t) + 2 * (sqrt X - sqrt Y) * c

def budgetArena : Arena where
  signature := signature
  Law R := ∀ {k : ℝ → ℝ} {Y X B : ℝ}
    (_ : 2 ≤ Y) (_ : Y ≤ X) (_ : X ≤ B) (_ : IntegrableOn k (Ioi Y)),
    (∫ x in Y..X, max (-R.readout () () k x) 0 / sqrt x) ≤
      massFactor Y * weightedNegativeMass k Y B +
        2 * (sqrt X - sqrt Y) * max (-endpointDefect k B) 0

private theorem exact_rejected : ¬ exactArena.Law rejected := by
  intro law
  have h := law (k := fun _ => 0) (g := fun _ => 0) (Y := 2) (X := 3) (B := 3) (c := 0)
    le_rfl (by norm_num) le_rfl (by simp) (by simp) (by simp)
    (by simp [weightedTail]) le_rfl (by simp [endpointDefect, tail, weightedTail])
  change (∫ x in (2 : ℝ)..3, max (-(-1 * sqrt x)) 0 / sqrt x) ≤ _ at h
  rw [negative_sqrt_mass (by norm_num) (by norm_num) (by norm_num)] at h
  norm_num at h

private theorem budget_rejected : ¬ budgetArena.Law rejected := by
  intro law
  have h := law (k := fun _ => 0) (Y := 2) (X := 3) (B := 3)
    le_rfl (by norm_num) le_rfl (by simp)
  change (∫ x in (2 : ℝ)..3, max (-(-1 * sqrt x)) 0 / sqrt x) ≤ _ at h
  rw [negative_sqrt_mass (by norm_num) (by norm_num) (by norm_num)] at h
  norm_num [weightedNegativeMass, endpointDefect, tail, weightedTail] at h

def exactEvidence : Registration exactArena (type_of% @negative_mass_le_of_majorant) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@negative_mass_le_of_majorant, rejected, exact_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    exactArena.Law actual rejected exact_rejected
  dependence := inverseEvidence.dependence

def budgetEvidence : Registration budgetArena (type_of% @negative_mass_le) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@negative_mass_le, rejected, budget_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    budgetArena.Law actual rejected budget_rejected
  dependence := inverseEvidence.dependence

def exactAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@negative_mass_le_of_majorant) (Realization signature) Unit Unit where
  unitName := .str ``negative_mass_le_of_majorant "__information_unit"
  realizationName := `Reg.D5.S3.Weil.Mertens.WeightedTailWindowMass.exactEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨exactArena⟩
  objectArena := .source ⟨exactArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source exactArena ⟨exactEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ k => tail k) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.WeightedTailWindowMass
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "fn", "arg", "fn", "fn", "fn",
        "arg", "body", "fn", "arg", "fn", "arg", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms exactAudit

def budgetAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@negative_mass_le) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.Mertens.WeightedTailWindowMass.negative_mass_le.__information_unit
  realizationName := `Reg.D5.S3.Weil.Mertens.WeightedTailWindowMass.budgetEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨budgetArena⟩
  objectArena := .source ⟨budgetArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source budgetArena ⟨budgetEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ k => tail k) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.WeightedTailWindowMass
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg",
        "fn", "fn", "fn", "arg", "body", "fn", "arg", "fn", "arg", "arg",
        "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms budgetAudit

end Reg.D5.S3.Weil.Mertens.WeightedTailWindowMass
