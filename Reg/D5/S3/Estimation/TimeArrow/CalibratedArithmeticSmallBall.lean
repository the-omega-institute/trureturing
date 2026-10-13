import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Estimation.TimeArrow.CalibratedArithmeticSmallBall
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Estimation.SequentialDecisionRisk.FiniteSupportSelectionBayes
open _root_.D5.S3.Estimation.TimeArrow.NativeRowMomentTransfer
open _root_.D5.S3.Estimation.TimeArrow.NativeRectangleReferenceRatios
open LeanInformationAudit

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Reg.D5.S3.Estimation.TimeArrow.CalibratedArithmeticSmallBall

@[reducible] def signature : Signature where
  Params := Σ M : ℕ, Σ q : ℕ, Σ _L : ℕ, Σ _S : Support M q, Σ _r : ℝ, Fin M
  State _ := ℕ × ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p counts =>
    rowReference p.2.2.2.1 p.2.2.2.2.1 p.2.2.1 p.2.2.2.2.2 counts)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ {M q L : ℕ} (S : Support M q) (r κ : ℝ)
    (_hκ : 0 < κ) (_hr : 0 < r) (_hrκ : r ≤ 1 - κ)
    (_hcκ : compensation M q r ≤ 1 - κ) (_hL : 1 ≤ L)
    (i : Fin M) (_hi : i ∈ S.val) (k l : ℕ)
    (_hkp : 15 / 16 ≤ ((L : ℝ) * (1 + r) / 2 / (k + 1)))
    (_hkp' : ((L : ℝ) * (1 + r) / 2 / (k + 1)) ≤ 1)
    (_hlp : 15 / 16 ≤ ((L : ℝ) * (1 - r) / 2 / (l + 1)))
    (_hlp' : ((L : ℝ) * (1 - r) / 2 / (l + 1)) ≤ 1),
    ∀ j : Fin 4,
      7 / 8 * rowReference S r L i (k, l) ≤
        rowReference S r L i (![(k,l), (k+1,l), (k,l+1), (k+1,l+1)] j) ∧
      rowReference S r L i (![(k,l), (k+1,l), (k,l+1), (k+1,l+1)] j) ≤
        9 / 8 * R.readout () ⟨M, q, L, S, r, i⟩ (k,l)

private theorem actual_law : arena.Law actual := signal_four_reference_ratios

private def fullSupport : Support 1 1 := ⟨Finset.univ, by simp⟩

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hc := (h (L := 32) fullSupport (1 / 16) (1 / 2)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [compensation]) (by norm_num) 0
    (by simp [fullSupport]) 17 15
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 0).2
  have hp := reference_pos fullSupport (1 / 16) (1 / 2)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [compensation]) (L := 32) (by norm_num) 0 (17,15)
  change rowReference fullSupport (1 / 16) 32 0 (17,15) ≤ 9 / 8 * (-1 : ℝ) at hc
  linarith

def audit : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := by
    intro role
    refine ⟨⟨1, 1, 0, fullSupport, 0, 0⟩, (0,0), (1,0), ?_⟩
    change rowReference fullSupport 0 0 0 (0,0) ≠ rowReference fullSupport 0 0 0 (1,0)
    norm_num [rowReference]

noncomputable def signal_ratios_registration :
    Contract.Registration.{0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@_root_.D5.S3.Estimation.TimeArrow.NativeRectangleReferenceRatios.signal_four_reference_ratios)
    (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Estimation.TimeArrow.CalibratedArithmeticSmallBall.signalRatiosUnit,
  realizationName := `Reg.D5.S3.Estimation.TimeArrow.CalibratedArithmeticSmallBall.audit,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨audit⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ p counts =>
    rowReference p.2.2.2.1 p.2.2.2.2.1 p.2.2.1 p.2.2.2.2.2 counts)
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Estimation.TimeArrow.CalibratedArithmeticSmallBall,
    definition := none,
    coordinates := #[0, 1, 2, 3, 4, 11],
    readouts := #[{
      path := #[
        "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "arg",
        "arg", "arg"],
      stateBinder := 0,
      functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `autoImplicit, value := .bool false },
    { name := `relaxedAutoImplicit, value := .bool false }] }

end Reg.D5.S3.Estimation.TimeArrow.CalibratedArithmeticSmallBall
