import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Estimation.TimeArrow.NativeSharedRootFeedback
import Reg.Support.SingleDependentReadout

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Estimation.TimeArrow.RectangleCalibrationBounds
open _root_.D5.S3.Estimation.TimeArrow.SharedRectangleCalibration
open LeanInformationAudit
open scoped BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Reg.D5.S3.Estimation.TimeArrow.NativeSharedRootFeedback

private theorem zero_offsets (j : Fin 4) : offsets 0 0 j = 0 := by
  fin_cases j <;> norm_num [offsets]

namespace RootBox

@[reducible] def signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℝ (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ x0 x => |x - x0|) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ (F : ℝ → ℝ) (q x0 x d a b : ℝ)
    (_hd : 0 < d) (_ha : 0 < a) (_hmono : StrictMono F)
    (_hcont : ContinuousOn F (Set.Icc (x0 - d) (x0 + d)))
    (_hdiff : DifferentiableOn ℝ F (interior (Set.Icc (x0 - d) (x0 + d))))
    (_hlower : ∀ u ∈ interior (Set.Icc (x0 - d) (x0 + d)), a ≤ deriv F u)
    (_hroot : F x = q) (_hres : |F x0 - q| ≤ b) (_hsmall : b ≤ a * d),
    R.readout () x0 x ≤ d ∧ a * |x - x0| ≤ b

private theorem actual_law : arena.Law actual := root_box_of_residual

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hc := (h (fun x => x) 0 0 0 1 1 0 (by norm_num) (by norm_num)
    strictMono_id continuous_id.continuousOn differentiable_id.differentiableOn
    (by intro u hu; simp) rfl (by norm_num) (by norm_num)).1
  norm_num [rejected, realize] at hc

def audit : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro role
    refine ⟨0, 0, 1, ?_⟩
    norm_num [actual, realize]

end RootBox

namespace CentralBootstrap
universe u

@[reducible] def signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℝ (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ x0 x => |x - x0|) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => Real.log 2 + 1) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ {ι : Type u} [Fintype ι] (outside : ι → ℝ)
    (r ε N Rm U q t t0 x0 x w : ℝ) (_hN : 0 < N)
    (_hc : ∀ j, 0 ≤ cellCounts N Rm U t j) (_ht : |t - t0| ≤ w)
    (_hbase : calibratedMean outside r ε N Rm U t0 x0 = q)
    (_hroot : calibratedMean outside r ε N Rm U t x = q)
    (_hvar : w < calibratedVariance outside r ε N Rm U t0 x0)
    (_hsmall : 2 * w ≤ (calibratedVariance outside r ε N Rm U t0 x0 - w) / 2 * Real.log 2),
    R.readout () x0 x ≤ Real.log 2 ∧
      |x - x0| ≤ 4 * w / (calibratedVariance outside r ε N Rm U t0 x0 - w) ∧
      (calibratedVariance outside r ε N Rm U t0 x0 - w) / 2 ≤
        calibratedVariance outside r ε N Rm U t x ∧
      calibratedVariance outside r ε N Rm U t x ≤
        2 * (calibratedVariance outside r ε N Rm U t0 x0 + w)

private theorem actual_law : arena.{u}.Law actual := shared_root_central_bootstrap

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  classical
  intro h
  let outside : ULift.{u} (Fin 0) → ℝ := fun _ => 0
  have hcells (j : Fin 4) : cellCounts 4 2 2 1 j = 1 := by
    fin_cases j <;> norm_num [cellCounts]
  have hmean : calibratedMean outside 0 0 4 2 2 1 0 = 2 := by
    norm_num [outside, calibratedMean, hcells, zero_offsets, Fin.sum_univ_four]
  have hvariance : calibratedVariance outside 0 0 4 2 2 1 0 = 1 := by
    norm_num [outside, calibratedVariance, hcells, zero_offsets, Fin.sum_univ_four]
  have hc := (h outside 0 0 4 2 2 2 1 1 0 0 0 (by norm_num)
    (by intro j; fin_cases j <;> norm_num [cellCounts]) (by norm_num)
    hmean hmean (by rw [hvariance]; norm_num)
    (by rw [hvariance]; have hp := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
        nlinarith)).1
  change Real.log 2 + 1 ≤ Real.log 2 at hc
  linarith

def audit : Registration arena.{u} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro role
    refine ⟨0, 0, 1, ?_⟩
    norm_num [actual, realize]

end CentralBootstrap

namespace FeedbackBounds

@[reducible] def signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => Real.sigmoid x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ (r ε x B D d a b X : ℝ)
    (_ha : 0 < a) (_haD : a ≤ D) (_hDb : D ≤ b)
    (_hB : 0 ≤ B) (_hd : 0 ≤ d) (_hneg : checkerboard r ε x ≤ -d)
    (_hx : |x| ≤ X) (_hbox : |x| ≤ Real.log 2),
    B * d / (8 * b) - X / 4 ≤
      R.readout () () x - 1 / 2 -
        B * Real.sigmoid x * (1 - Real.sigmoid x) * checkerboard r ε x / D ∧
      Real.sigmoid x - 1 / 2 -
        B * Real.sigmoid x * (1 - Real.sigmoid x) * checkerboard r ε x / D ≤
          X / 4 + B / (2 * a)

private theorem actual_law : arena.Law actual := compensated_feedback_bounds

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hc := (h 0 0 0 0 1 0 1 1 0 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [checkerboard, zero_offsets]) (by norm_num)
    (by simpa using (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le)).1
  norm_num [rejected, realize] at hc

def audit : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro role
    refine ⟨(), 0, 1, ?_⟩
    change Real.sigmoid 0 ≠ Real.sigmoid 1
    exact fun h => (by norm_num : (0 : ℝ) ≠ 1) (Real.sigmoid_injective h)

end FeedbackBounds

namespace FeedbackBox

@[reducible] def signature : Signature :=
  Reg.Support.SingleDependentReadout.signature (Σ _r : ℝ, ℝ) (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ p x => checkerboard p.1 p.2 x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ {r : ℝ} (_hr : 0 < r) (_hr1 : r < 1),
    ∃ d δ : ℝ, 0 < d ∧ 0 < δ ∧ δ ≤ Real.log 2 ∧
      ∀ ε x : ℝ, |ε| < δ → |x| < δ → R.readout () ⟨r, ε⟩ x ≤ -d

private theorem actual_law : arena.Law actual := compensated_feedback_box

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨d, δ, hd, hδ, _, hh⟩ := h (r := 1 / 2) (by norm_num) (by norm_num)
  have hc := hh 0 0 (by simpa using hδ) (by simpa using hδ)
  change (0 : ℝ) ≤ -d at hc
  linarith

def audit : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro role
    refine ⟨⟨1 / 2, 0⟩, 0, Real.log 2, ?_⟩
    change checkerboard (1 / 2) 0 0 ≠ checkerboard (1 / 2) 0 (Real.log 2)
    have ho1 : offsets (1 / 2) 0 1 = Real.log (3 / 2) := by
      change Real.log ((1 + 1 / 2) / (1 - 0)) = Real.log (3 / 2)
      norm_num
    have ho2 : offsets (1 / 2) 0 2 = Real.log (1 / 2) := by
      change Real.log ((1 - 1 / 2) / (1 + 0)) = Real.log (1 / 2)
      norm_num
    have ho3 : offsets (1 / 2) 0 3 = Real.log (3 / 2) + Real.log (1 / 2) := by
      change Real.log ((1 + 1 / 2) / (1 - 0)) +
        Real.log ((1 - 1 / 2) / (1 + 0)) = Real.log (3 / 2) + Real.log (1 / 2)
      norm_num
    simp only [checkerboard, ho1, ho2, ho3]
    norm_num [Real.sigmoid_def, Real.exp_neg, Real.exp_add,
      Real.exp_log (by norm_num : (0 : ℝ) < 2),
      Real.exp_log (by norm_num : (0 : ℝ) < 3 / 2),
      Real.exp_log (by norm_num : (0 : ℝ) < 1 / 2)]

end FeedbackBox

noncomputable def rootbox_registration : Contract.Registration.{0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@_root_.D5.S3.Estimation.TimeArrow.RectangleCalibrationBounds.root_box_of_residual)
    (Realization RootBox.signature) Unit Unit := {
  unitName := `Reg.D5.S3.Estimation.TimeArrow.NativeSharedRootFeedback.RootBox.unit,
  realizationName := `Reg.D5.S3.Estimation.TimeArrow.NativeSharedRootFeedback.RootBox.audit,
  realizationSource := none,
  generated := false,
  arena := .source ⟨RootBox.arena⟩,
  objectArena := .source ⟨RootBox.arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source RootBox.arena ⟨RootBox.audit⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize RootBox.signature
    (fun _ x0 x => |x - x0|) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Estimation.TimeArrow.NativeSharedRootFeedback,
    definition := none,
    coordinates := #[2],
    readouts := #[{
      path := #[
        "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "fn", "arg", "fn", "arg"],
      stateBinder := 3,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `autoImplicit, value := .bool false },
    { name := `relaxedAutoImplicit, value := .bool false }] }

noncomputable def centralbootstrap_registration.{u} :
    Contract.Registration.{0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@_root_.D5.S3.Estimation.TimeArrow.RectangleCalibrationBounds.shared_root_central_bootstrap.{u})
    (Realization CentralBootstrap.signature) Unit Unit := {
  unitName := `Reg.D5.S3.Estimation.TimeArrow.NativeSharedRootFeedback.CentralBootstrap.unit,
  realizationName := `Reg.D5.S3.Estimation.TimeArrow.NativeSharedRootFeedback.CentralBootstrap.audit,
  realizationSource := none,
  generated := false,
  arena := .source ⟨CentralBootstrap.arena.{u}⟩,
  objectArena := .source ⟨CentralBootstrap.arena.{u}⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source CentralBootstrap.arena.{u} ⟨CentralBootstrap.audit.{u}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize CentralBootstrap.signature
    (fun _ x0 x => |x - x0|) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Estimation.TimeArrow.NativeSharedRootFeedback,
    definition := none,
    coordinates := #[11],
    readouts := #[{
      path := #[
        "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "fn", "arg"],
      stateBinder := 12,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `autoImplicit, value := .bool false },
    { name := `relaxedAutoImplicit, value := .bool false }] }

noncomputable def feedbackbounds_registration :
    Contract.Registration.{0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@_root_.D5.S3.Estimation.TimeArrow.RectangleCalibrationBounds.compensated_feedback_bounds)
    (Realization FeedbackBounds.signature) Unit Unit := {
  unitName := `Reg.D5.S3.Estimation.TimeArrow.NativeSharedRootFeedback.FeedbackBounds.unit,
  realizationName := `Reg.D5.S3.Estimation.TimeArrow.NativeSharedRootFeedback.FeedbackBounds.audit,
  realizationSource := none,
  generated := false,
  arena := .source ⟨FeedbackBounds.arena⟩,
  objectArena := .source ⟨FeedbackBounds.arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source FeedbackBounds.arena ⟨FeedbackBounds.audit⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize FeedbackBounds.signature
    (fun _ _ x => Real.sigmoid x) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Estimation.TimeArrow.NativeSharedRootFeedback,
    definition := none,
    coordinates := #[],
    readouts := #[{
      path := #[
        "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "fn", "arg", "arg", "fn",
        "arg", "fn", "arg"],
      stateBinder := 2,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `autoImplicit, value := .bool false },
    { name := `relaxedAutoImplicit, value := .bool false }] }

noncomputable def feedbackbox_registration :
    Contract.Registration.{0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@_root_.D5.S3.Estimation.TimeArrow.RectangleCalibrationBounds.compensated_feedback_box)
    (Realization FeedbackBox.signature) Unit Unit := {
  unitName := `Reg.D5.S3.Estimation.TimeArrow.NativeSharedRootFeedback.FeedbackBox.unit,
  realizationName := `Reg.D5.S3.Estimation.TimeArrow.NativeSharedRootFeedback.FeedbackBox.audit,
  realizationSource := none,
  generated := false,
  arena := .source ⟨FeedbackBox.arena⟩,
  objectArena := .source ⟨FeedbackBox.arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source FeedbackBox.arena ⟨FeedbackBox.audit⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize FeedbackBox.signature
    (fun _ p x => checkerboard p.1 p.2 x) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Estimation.TimeArrow.NativeSharedRootFeedback,
    definition := none,
    coordinates := #[0, 5],
    readouts := #[{
      path := #[
        "body", "body", "body", "arg", "body", "arg", "body",
        "arg", "arg", "arg", "body", "body", "body", "body",
        "fn", "arg"],
      stateBinder := 6,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `autoImplicit, value := .bool false },
    { name := `relaxedAutoImplicit, value := .bool false }] }

end Reg.D5.S3.Estimation.TimeArrow.NativeSharedRootFeedback
