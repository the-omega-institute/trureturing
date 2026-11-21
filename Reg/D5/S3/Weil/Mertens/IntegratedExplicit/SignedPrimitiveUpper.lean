import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.Mertens.IntegratedExplicit.SignedPrimitiveUpper
import Reg.Support.SingleDependentReadout

/-! Source audit for the pointwise tail coefficient. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Filter MeasureTheory Set
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.SignedPrimitiveUpper
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Weil.Mertens.IntegratedExplicit.SignedPrimitiveUpper

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ C => 2 * C + 1 / 6) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V :=
    ∀ (A : ℝ → ℝ) {X₀ κ C : ℝ} (hX₁ : 1 ≤ X₀) (hκ : 0 ≤ κ)
    (htail : IntegrableOn (fun t => (A t - t) / t ^ 2) (Ioi X₀))
    (hA : MonotoneOn A (Ici X₀))
    (hprim : let q := (fun x : ℝ => ∫ t in Ioi x, (A t - t) / t ^ 2);
      ∀ a b : ℝ, X₀ ≤ a → a ≤ b →
        |(∫ x in a..b, q x / Real.sqrt x) + κ * Real.log (b / a)| ≤ C),
    let q := (fun x : ℝ => ∫ t in Ioi x, (A t - t) / t ^ 2);
    (∀ x : ℝ, (3 / 2) * X₀ ≤ x →
      -κ / Real.sqrt x - (V.readout () () C) * x ^ (-(1 / 3) : ℝ) ≤ q x) ∧
    (∀ a b : ℝ, (3 / 2) * X₀ ≤ a → a ≤ b →
      (∫ x in a..b, max (-q x) 0 / Real.sqrt x) ≤
        κ * Real.log (b / a) + (12 * C + 1) * (b ^ (1 / 6 : ℝ) - a ^ (1 / 6 : ℝ)))

private theorem rejected_fails : ¬ arena.Law rejected := by
  intro law
  have hkernel : (fun t : ℝ => (id t - t) / t ^ 2) = 0 := by
    funext t
    simp
  have hint : IntegrableOn (fun t : ℝ => (id t - t) / t ^ 2) (Ioi 1) := by
    rw [hkernel]
    exact integrableOn_zero
  have hprim : ∀ a b : ℝ, (1 : ℝ) ≤ a → a ≤ b →
      |(∫ x in a..b, (∫ t in Ioi x, (id t - t) / t ^ 2) / Real.sqrt x) +
        0 * Real.log (b / a)| ≤ 0 := by
    intro a b _ _
    simp
  have hpoint := (law id (X₀ := 1) (κ := 0) (C := 0) (by norm_num) (by norm_num)
    hint (monotone_id.monotoneOn _) hprim).1 2 (by norm_num)
  change -(0 : ℝ) / Real.sqrt 2 - (-1 : ℝ) * (2 : ℝ) ^ (-(1 / 3) : ℝ) ≤
    ∫ t in Ioi (2 : ℝ), (id t - t) / t ^ 2 at hpoint
  have hpow : 0 < (2 : ℝ) ^ (-(1 / 3) : ℝ) := by positivity
  exact hpow.not_ge (by simpa [hkernel] using hpoint)

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
  change (2 * (0 : ℝ) + 1 / 6) ≠ (2 * (1 : ℝ) + 1 / 6)
  norm_num

def family : Registration arena (type_of% @signedPrimitiveUpper) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@signedPrimitiveUpper, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_fails
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@signedPrimitiveUpper) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Weil.Mertens.IntegratedExplicit.SignedPrimitiveUpper.signedPrimitiveUpper.__information_unit
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.SignedPrimitiveUpper.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ C => 2 * C + 1 / 6) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.SignedPrimitiveUpper
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "fn", "arg", "body", "body", "fn", "arg",
        "arg", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Weil.Mertens.IntegratedExplicit.SignedPrimitiveUpper
