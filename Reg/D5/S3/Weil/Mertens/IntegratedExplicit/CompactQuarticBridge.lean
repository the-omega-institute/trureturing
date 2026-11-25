import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.Mertens.IntegratedExplicit.CompactQuarticBridge
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.CompactQuarticBridge
open _root_.D5.S3.Arith.FactorialRatio.CompactFactorialGcd (selbergGcd)
open _root_.D5.S3.Arith.FactorialRatio.RankOneLCMGcd (tailLCM)
open _root_.D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds (firstLiMass)

namespace Reg.D5.S3.Weil.Mertens.IntegratedExplicit.CompactQuarticBridge

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℝ)

def tailActual : Realization signature :=
  realize signature (fun _ _ n => D (n^4) (n^2)) (fun e => nomatch e)

def compactActual : Realization signature :=
  realize signature (fun _ _ n => compactD n) (fun e => nomatch e)

private theorem tail_dependence : ObservationalDependence signature tailActual := by
  intro _
  refine ⟨(), 0, 1, ?_⟩
  change D (0^4) (0^2) ≠ D (1^4) (1^2)
  have htail : tailLCM 1 1 = 1 := by decide
  simp [D, htail]
  linarith [Real.one_half_lt_eulerMascheroniConstant]

private theorem compact_dependence : ObservationalDependence signature compactActual := by
  intro _
  refine ⟨(), 0, 1, ?_⟩
  change compactD 0 ≠ compactD 1
  have hgcd : quarticFactorialGcd 1 = 1 := by decide
  simp [compactD, hgcd]
  linarith [Real.one_half_lt_eulerMascheroniConstant]

def blockArena : Arena where
  signature := signature
  Law V := RiemannHypothesis ↔ ∀ κ : ℝ, 0 < κ → ∀ A : ℕ, ∃ k ≥ max A 2,
    ∀ n : ℕ, k^3 ≤ n → n ≤ k^4 →
      V.readout () () n ≤ ((n : ℝ)^4)^(1/2+κ)

/-- A whole-family intervention contradicting the RH block law in either case. -/
private def blockRejected : Realization signature := by
  classical
  exact realize signature (fun _ _ n => if RiemannHypothesis then (n : ℝ)^4 + 1 else -1)
    (fun e => nomatch e)

private theorem block_rejected_law : ¬ blockArena.Law blockRejected := by
  classical
  intro h
  by_cases rh : RiemannHypothesis
  · obtain ⟨k, hk, hblock⟩ := h.mp rh (1/2) (by norm_num) 2
    have hk1 : 1 ≤ k := by omega
    have hb := hblock (k^3) le_rfl (pow_le_pow_right₀ hk1 (by decide : 3 ≤ 4))
    change (if RiemannHypothesis then _ + 1 else -1) ≤ _ at hb
    simp only [rh, ↓reduceIte, show (1 : ℝ)/2+1/2 = 1 by norm_num, Real.rpow_one] at hb
    linarith
  · apply rh
    apply h.mpr
    intro κ _ A
    refine ⟨max A 2, le_rfl, ?_⟩
    intro n _ _
    change (if RiemannHypothesis then _ + 1 else -1) ≤ _
    simp only [rh, ↓reduceIte]
    exact (by norm_num : (-1 : ℝ) ≤ 0).trans (Real.rpow_nonneg (by positivity) _)

namespace TailBlocks

def evidence : Registration blockArena (type_of% @rh_iff_tailLCM_quartic_integer_blocks) where
  actual := tailActual
  bridge := Iff.rfl
  variation := ⟨rh_iff_tailLCM_quartic_integer_blocks, blockRejected, block_rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    blockArena.Law tailActual blockRejected block_rejected_law
  dependence := tail_dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@rh_iff_tailLCM_quartic_integer_blocks) (Realization signature) Unit Unit where
  unitName :=
    .str `D5.S3.Weil.Mertens.IntegratedExplicit.CompactQuarticBridge.rh_iff_tailLCM_quartic_integer_blocks
      "__information_unit"
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.CompactQuarticBridge.TailBlocks.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨blockArena⟩
  objectArena := .source ⟨blockArena⟩
  catalog := .anonymous
  localNames := false
  realization := .source blockArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => D (n^4) (n^2)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.CompactQuarticBridge
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "body", "body", "body", "arg", "body", "arg",
        "body", "body", "body", "fn", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end TailBlocks

namespace CompactBlocks

def evidence : Registration blockArena
    (type_of% @rh_iff_compact_factorial_gcd_quartic_integer_blocks) where
  actual := compactActual
  bridge := Iff.rfl
  variation := ⟨rh_iff_compact_factorial_gcd_quartic_integer_blocks,
    blockRejected, block_rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    blockArena.Law compactActual blockRejected block_rejected_law
  dependence := compact_dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@rh_iff_compact_factorial_gcd_quartic_integer_blocks) (Realization signature) Unit Unit where
  unitName :=
    .str
      `D5.S3.Weil.Mertens.IntegratedExplicit.CompactQuarticBridge.rh_iff_compact_factorial_gcd_quartic_integer_blocks
      "__information_unit"
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.CompactQuarticBridge.CompactBlocks.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨blockArena⟩
  objectArena := .source ⟨blockArena⟩
  catalog := .anonymous
  localNames := false
  realization := .source blockArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => compactD n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.CompactQuarticBridge
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "body", "body", "body", "arg", "body", "arg",
        "body", "body", "body", "fn", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end CompactBlocks

end Reg.D5.S3.Weil.Mertens.IntegratedExplicit.CompactQuarticBridge
