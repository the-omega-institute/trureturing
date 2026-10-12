import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Estimation.TimeArrow.NativeSignalConditionalFiber
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Reg.D5.S3.Estimation.TimeArrow.NativeSignalConditionalFiber
open _root_.D5.S3.Estimation.TimeArrow.SharedRectangleCalibration

@[reducible] def signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x => Real.sigmoid x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ a x : ℝ,
    HasDerivAt (fun u : ℝ => Real.sigmoid (u + a))
      (R.readout () () (x + a) * (1 - Real.sigmoid (x + a))) x

private theorem actual_law : arena.Law actual := by
  exact sigmoid_shift_deriv

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have incompatible := (h 0 0).unique (sigmoid_shift_deriv 0 0)
  norm_num [rejected, realize, Real.sigmoid_zero] at incompatible

def audit : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change Real.sigmoid 0 ≠ Real.sigmoid 1
    exact fun h => (by norm_num : (0 : ℝ) ≠ 1) (Real.sigmoid_injective h)

noncomputable def registration_1 :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Estimation.TimeArrow.SharedRectangleCalibration.sigmoid_shift_deriv) (Realization signature) Unit Unit := {
  unitName := (Lean.Name.str (Lean.Name.str `D5.S3.Estimation.TimeArrow.SharedRectangleCalibration.sigmoid_shift_deriv "Reg.D5.S3.Estimation.TimeArrow.NativeSignalConditionalFiber/Reg.D5.S3.Estimation.TimeArrow.NativeSignalConditionalFiber.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Estimation.TimeArrow.NativeSignalConditionalFiber.audit,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨audit⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ x => Real.sigmoid x) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Estimation.TimeArrow.NativeSignalConditionalFiber,
    definition := none,
    coordinates := #[],
    readouts := #[{ path := #["body", "body", "fn", "arg", "fn", "arg"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `autoImplicit, value := .bool false },
    { name := `relaxedAutoImplicit, value := .bool false }] }


open _root_.D5.S3.Estimation.TimeArrow.NativeGrowthRounding
open _root_.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance

namespace CentralRounding

@[reducible] def signature : Signature where
  Params := ℝ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ r L => centralPositive r L) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ (r : ℝ) (L : ℕ) (_hr : 0 ≤ r) (_hr1 : r ≤ 1),
    R.readout () r L ≤ L ∧
      0 ≤ ((1 + r) / 2) * (L : ℝ) - centralPositive r L ∧
      ((1 + r) / 2) * (L : ℝ) - centralPositive r L < 1 ∧
      (centralNegative r L : ℝ) = (L : ℝ) - centralPositive r L

private theorem actual_law : arena.Law actual := by
  exact central_rounding

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have incompatible := (h 0 0 (by norm_num) (by norm_num)).1
  norm_num [rejected, realize] at incompatible

def audit : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨0, 0, 2, ?_⟩
    change centralPositive 0 0 ≠ centralPositive 0 2
    norm_num [centralPositive]

end CentralRounding

namespace PopulationBounds

@[reducible] def signature : Signature where
  Params := ℝ × ℝ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p L => population p.1 p.2 L) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ (r β : ℝ) (L : ℕ) (_hφ : 0 ≤ phi r) (_hβ : 0 < β),
    Real.exp (phi r / β * (L : ℝ)) / 2 ≤ (R.readout () (r, β) L : ℝ) ∧
      (population r β L : ℝ) ≤ Real.exp (phi r / β * (L : ℝ))

private theorem actual_law : arena.Law actual := by
  exact population_exponential_bounds

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have incompatible := (h 0 1 0 (by norm_num [phi]) (by norm_num)).1
  norm_num [rejected, realize] at incompatible

def audit : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨(1, 1), 0, 1, ?_⟩
    change population 1 1 0 ≠ population 1 1 1
    have log_nonzero : Real.log (2 : ℝ) ≠ 0 :=
      ne_of_gt (Real.log_pos (by norm_num))
    norm_num [population, phi, log_nonzero]

end PopulationBounds

namespace InformationRate

@[reducible] def signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ r => phi r) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ (r : ℝ) (_hr : 0 < r) (_hr1 : r < 1),
    0 < R.readout () () r ∧ phi r < Real.log 2

private theorem actual_law : arena.Law actual := by
  exact information_rate_bounds

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have incompatible := (h (1 / 2) (by norm_num) (by norm_num)).1
  norm_num [rejected, realize] at incompatible

def audit : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨(), 0, 1 / 2, ?_⟩
    change phi 0 ≠ phi (1 / 2)
    have positive := (information_rate_bounds (1 / 2) (by norm_num) (by norm_num)).1
    rw [show phi 0 = 0 by norm_num [phi]]
    exact ne_of_lt positive

end InformationRate


namespace CenterRounding

@[reducible] def signature : Signature where
  Params := ℝ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ r L => center r L) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ (r : ℝ) (L : ℕ) (_hr : 0 ≤ r) (_hr1 : r < 1),
    phi r * (L : ℝ) - Real.log ((1 + r) / (1 - r)) ≤ R.readout () r L ∧
      center r L ≤ phi r * (L : ℝ)

private theorem actual_law : arena.Law actual := by
  exact center_rounding

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have incompatible := (h 0 0 (by norm_num) (by norm_num)).1
  norm_num [rejected, realize] at incompatible

def audit : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨1, 0, 1, ?_⟩
    change center 1 0 ≠ center 1 1
    norm_num [center, centralPositive, centralNegative]
    exact ne_of_lt (Real.log_pos (by norm_num : (1 : ℝ) < 2))

end CenterRounding

namespace OriginalCountRounding

@[reducible] def signature : Signature where
  Params := ℝ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ r L => ⌊((1 + r) / 2) * (L : ℝ)⌋₊) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ (r : ℝ) (L : ℕ) (_hr : 0 < r) (_hr1 : r < 1)
    (_hL : 1 ≤ L) (_hplus : 15 ≤ ((1 + r) / 2) * (L : ℝ))
    (_hminus : 30 ≤ ((1 - r) / 2) * (L : ℝ)),
    let k := R.readout () r L
    let l := L - k
    k ≤ L ∧ 0 < k ∧ 0 < l ∧
      15 / 16 ≤ ((L : ℝ) * (1 + r) / 2 / (k + 1)) ∧
      ((L : ℝ) * (1 + r) / 2 / (k + 1)) ≤ 1 ∧
      15 / 16 ≤ ((L : ℝ) * (1 - r) / 2 / (l + 1)) ∧
      ((L : ℝ) * (1 - r) / 2 / (l + 1)) ≤ 1

private theorem actual_law : arena.Law actual := by
  exact _root_.D5.S3.Estimation.TimeArrow.NativeRectangleReferenceRatios.original_count_rounding

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have incompatible := (h (1 / 2) 160 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)).2.1
  norm_num [rejected, realize] at incompatible

def audit : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨1 / 2, 0, 2, ?_⟩
    norm_num [actual, realize]

end OriginalCountRounding

noncomputable def registration_2 :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Estimation.TimeArrow.NativeGrowthRounding.central_rounding)
      (Realization CentralRounding.signature) Unit Unit := {
  unitName := Lean.Name.str
    (Lean.Name.str `D5.S3.Estimation.TimeArrow.NativeGrowthRounding.central_rounding
      "Reg.D5.S3.Estimation.TimeArrow.NativeSignalConditionalFiber/Reg.D5.S3.Estimation.TimeArrow.NativeSignalConditionalFiber.CentralRounding.arena/[anonymous]")
    "__information_unit",
  realizationName := `Reg.D5.S3.Estimation.TimeArrow.NativeSignalConditionalFiber.CentralRounding.audit,
  realizationSource := none,
  generated := false,
  arena := .source ⟨CentralRounding.arena⟩,
  objectArena := .source ⟨CentralRounding.arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source CentralRounding.arena ⟨CentralRounding.audit⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize CentralRounding.signature (fun _ r L => centralPositive r L) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Estimation.TimeArrow.NativeSignalConditionalFiber,
    definition := none,
    coordinates := #[0],
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "fn", "arg"],
      stateBinder := 1,
      functionOperand := false,
      stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `autoImplicit, value := .bool false },
    { name := `relaxedAutoImplicit, value := .bool false }] }

noncomputable def registration_3 :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Estimation.TimeArrow.NativeGrowthRounding.population_exponential_bounds)
      (Realization PopulationBounds.signature) Unit Unit := {
  unitName := Lean.Name.str
    (Lean.Name.str `D5.S3.Estimation.TimeArrow.NativeGrowthRounding.population_exponential_bounds
      "Reg.D5.S3.Estimation.TimeArrow.NativeSignalConditionalFiber/Reg.D5.S3.Estimation.TimeArrow.NativeSignalConditionalFiber.PopulationBounds.arena/[anonymous]")
    "__information_unit",
  realizationName := `Reg.D5.S3.Estimation.TimeArrow.NativeSignalConditionalFiber.PopulationBounds.audit,
  realizationSource := none,
  generated := false,
  arena := .source ⟨PopulationBounds.arena⟩,
  objectArena := .source ⟨PopulationBounds.arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source PopulationBounds.arena ⟨PopulationBounds.audit⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize PopulationBounds.signature (fun _ p L => population p.1 p.2 L) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Estimation.TimeArrow.NativeSignalConditionalFiber,
    definition := none,
    coordinates := #[0, 1],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "arg", "arg"],
      stateBinder := 2,
      functionOperand := false,
      stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `autoImplicit, value := .bool false },
    { name := `relaxedAutoImplicit, value := .bool false }] }

noncomputable def registration_4 :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Estimation.TimeArrow.NativeGrowthRounding.information_rate_bounds)
      (Realization InformationRate.signature) Unit Unit := {
  unitName := Lean.Name.str
    (Lean.Name.str `D5.S3.Estimation.TimeArrow.NativeGrowthRounding.information_rate_bounds
      "Reg.D5.S3.Estimation.TimeArrow.NativeSignalConditionalFiber/Reg.D5.S3.Estimation.TimeArrow.NativeSignalConditionalFiber.InformationRate.arena/[anonymous]")
    "__information_unit",
  realizationName := `Reg.D5.S3.Estimation.TimeArrow.NativeSignalConditionalFiber.InformationRate.audit,
  realizationSource := none,
  generated := false,
  arena := .source ⟨InformationRate.arena⟩,
  objectArena := .source ⟨InformationRate.arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source InformationRate.arena ⟨InformationRate.audit⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize InformationRate.signature (fun _ _ r => phi r) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Estimation.TimeArrow.NativeSignalConditionalFiber,
    definition := none,
    coordinates := #[],
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "arg"],
      stateBinder := 0,
      functionOperand := false,
      stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `autoImplicit, value := .bool false },
    { name := `relaxedAutoImplicit, value := .bool false }] }

noncomputable def registration_5 :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Estimation.TimeArrow.NativeGrowthRounding.center_rounding)
      (Realization CenterRounding.signature) Unit Unit := {
  unitName := Lean.Name.str
    (Lean.Name.str `D5.S3.Estimation.TimeArrow.NativeGrowthRounding.center_rounding
      "Reg.D5.S3.Estimation.TimeArrow.NativeSignalConditionalFiber/Reg.D5.S3.Estimation.TimeArrow.NativeSignalConditionalFiber.CenterRounding.arena/[anonymous]")
    "__information_unit",
  realizationName := `Reg.D5.S3.Estimation.TimeArrow.NativeSignalConditionalFiber.CenterRounding.audit,
  realizationSource := none,
  generated := false,
  arena := .source ⟨CenterRounding.arena⟩,
  objectArena := .source ⟨CenterRounding.arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source CenterRounding.arena ⟨CenterRounding.audit⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize CenterRounding.signature (fun _ r L => center r L) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Estimation.TimeArrow.NativeSignalConditionalFiber,
    definition := none,
    coordinates := #[0],
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "arg"],
      stateBinder := 1,
      functionOperand := false,
      stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `autoImplicit, value := .bool false },
    { name := `relaxedAutoImplicit, value := .bool false }] }

noncomputable def registration_6 :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Estimation.TimeArrow.NativeRectangleReferenceRatios.original_count_rounding)
      (Realization OriginalCountRounding.signature) Unit Unit := {
  unitName := Lean.Name.str
    (Lean.Name.str `D5.S3.Estimation.TimeArrow.NativeRectangleReferenceRatios.original_count_rounding
      "Reg.D5.S3.Estimation.TimeArrow.NativeSignalConditionalFiber/Reg.D5.S3.Estimation.TimeArrow.NativeSignalConditionalFiber.OriginalCountRounding.arena/[anonymous]")
    "__information_unit",
  realizationName := `Reg.D5.S3.Estimation.TimeArrow.NativeSignalConditionalFiber.OriginalCountRounding.audit,
  realizationSource := none,
  generated := false,
  arena := .source ⟨OriginalCountRounding.arena⟩,
  objectArena := .source ⟨OriginalCountRounding.arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source OriginalCountRounding.arena ⟨OriginalCountRounding.audit⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize OriginalCountRounding.signature (fun _ r L => ⌊((1 + r) / 2) * (L : ℝ)⌋₊) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Estimation.TimeArrow.NativeSignalConditionalFiber,
    definition := none,
    coordinates := #[0],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "value"],
      stateBinder := 1,
      functionOperand := false,
      stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `autoImplicit, value := .bool false },
    { name := `relaxedAutoImplicit, value := .bool false }] }

end Reg.D5.S3.Estimation.TimeArrow.NativeSignalConditionalFiber
