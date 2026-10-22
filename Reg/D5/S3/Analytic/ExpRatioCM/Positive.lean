import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.ExpRatioCM.Positive
import Reg.D5.S3.Analytic.ExpRatioCM.Extraction
import Mathlib.Analysis.Calculus.Deriv.Abs

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Analytic.ExpRatioCM.Defs
open _root_.D5.S3.Analytic.ExpRatioCM.Positive
open _root_.D5.S3.Analytic.ExpRatioCM.Series
open _root_.Reg.D5.S3.Analytic.ExpRatioCM.Series
open scoped Topology
open LeanInformationAudit
open Set

noncomputable section
namespace Reg.D5.S3.Analytic.ExpRatioCM.Positive

def nonsmoothMoment : Realization momentSignature :=
  realize momentSignature (fun _ _ t => |t - 1|) (fun e => nomatch e)

private theorem nonsmoothRejected : ¬ ∀ i : ℕ,
    ContDiffOn ℝ ⊤ (nonsmoothMoment.readout () i) (Ioi 0) := by
  intro h
  have hd : DifferentiableAt ℝ (fun t : ℝ => |t - 1|) 1 :=
    ((h 0).differentiableOn (by simp) 1 (by norm_num)).differentiableAt
      (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))
  apply not_differentiableAt_abs_zero
  simpa only [Function.comp_def, id_eq, add_sub_cancel_right] using
    (show DifferentiableAt ℝ (fun t : ℝ => |t - 1|) ((fun x : ℝ => x + 1) 0) by simpa using hd).comp (0 : ℝ) ((differentiableAt_id : DifferentiableAt ℝ (fun x : ℝ => x) 0).add_const 1)

namespace MomentSmooth
def arena : Arena where
  signature := momentSignature
  Law R := ∀ i : ℕ, ContDiffOn ℝ ⊤ (R.readout () i) (Ioi 0)
private theorem rejected : ¬ arena.Law nonsmoothMoment := by
  exact nonsmoothRejected
def family : Registration arena (type_of% (@contDiffOn_F)) where
  actual := momentActual
  bridge := Iff.rfl
  variation := ⟨@contDiffOn_F, nonsmoothMoment, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law momentActual nonsmoothMoment rejected
  dependence := Composition.family.dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@contDiffOn_F) (Realization momentSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.ExpRatioCM.Positive.MomentSmooth.unit
  realizationName := `Reg.D5.S3.Analytic.ExpRatioCM.Positive.MomentSmooth.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize momentSignature (fun _ i t => F i t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.ExpRatioCM.Positive
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms audit
end MomentSmooth

namespace SecondZero
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ _ t => G 0 t) (fun e => nomatch e)
def bad : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, Real.log 2, ?_⟩
  change G 0 0 ≠ G 0 (Real.log 2)
  norm_num [G, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
def arena : Arena where
  signature := signature
  Law R := ∀ {t : ℝ}, 0 < t → R.readout () () t = 1 + F 0 t
private theorem rejected : ¬ arena.Law bad := by
  intro h
  have hh := h (t := 1) (by norm_num)
  have hp := F_pos 0 (t := 1) (by norm_num)
  change 0 = 1 + F 0 1 at hh
  linarith
def family : Registration arena (type_of% (@G_zero_eq)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@G_zero_eq, bad, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual bad rejected
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@G_zero_eq) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.ExpRatioCM.Positive.SecondZero.unit
  realizationName := `Reg.D5.S3.Analytic.ExpRatioCM.Positive.SecondZero.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ t => G 0 t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.ExpRatioCM.Positive
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms audit
end SecondZero

namespace FirstRatioSmooth
def arena : Arena where
  signature := momentSignature
  Law R := ∀ i : ℕ, ContDiffOn ℝ ⊤ (R.readout () i) (Ioi 0)
private theorem rejected : ¬ arena.Law nonsmoothMoment := by
  exact nonsmoothRejected
def family : Registration arena (type_of% (@contDiffOn_ratioF)) where
  actual := ratioActual
  bridge := Iff.rfl
  variation := ⟨@contDiffOn_ratioF, nonsmoothMoment, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law ratioActual nonsmoothMoment rejected
  dependence := RatioExpansion.family.dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@contDiffOn_ratioF) (Realization momentSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.ExpRatioCM.Positive.FirstRatioSmooth.unit
  realizationName := `Reg.D5.S3.Analytic.ExpRatioCM.Positive.FirstRatioSmooth.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize momentSignature (fun _ i t => ratioF i t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.ExpRatioCM.Positive
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms audit
end FirstRatioSmooth

namespace SecondRatioSmooth
def arena : Arena where
  signature := momentSignature
  Law R := ∀ i : ℕ, ContDiffOn ℝ ⊤ (R.readout () i) (Ioi 0)
private theorem rejected : ¬ arena.Law nonsmoothMoment := by
  exact nonsmoothRejected
def family : Registration arena (type_of% (@contDiffOn_ratioG)) where
  actual := secondRatioActual
  bridge := Iff.rfl
  variation := ⟨@contDiffOn_ratioG, nonsmoothMoment, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law secondRatioActual nonsmoothMoment rejected
  dependence := RatioAgreement.family.dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@contDiffOn_ratioG) (Realization momentSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.ExpRatioCM.Positive.SecondRatioSmooth.unit
  realizationName := `Reg.D5.S3.Analytic.ExpRatioCM.Positive.SecondRatioSmooth.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize momentSignature (fun _ i t => ratioG i t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.ExpRatioCM.Positive
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms audit
end SecondRatioSmooth

abbrev functionSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (ℝ → ℝ) (fun _ => ℝ) (fun _ => ℝ)
def functionActual : Realization functionSignature :=
  realize functionSignature (fun _ h t => h t) (fun e => nomatch e)
private theorem functionDependence : ObservationalDependence functionSignature functionActual := by
  intro i
  refine ⟨id, 0, 1, ?_⟩
  norm_num [functionActual, realize]

def negativeFunction : Realization functionSignature :=
  realize functionSignature (fun _ _ _ => (-1 : ℝ)) (fun e => nomatch e)

private theorem negative_not_cm : ¬ CompletelyMonotoneOn (fun _ : ℝ => (-1 : ℝ)) := by
  intro h
  have hz := h.2 0 1 (by norm_num)
  norm_num at hz

namespace Criterion

def arena : Arena where
  signature := functionSignature
  Law R := ∀ {h : ℝ → ℝ} {c r : ℕ → ℝ},
    ContDiffOn ℝ ⊤ h (Ioi 0) →
    (∀ k : ℕ, ∀ t : ℝ, 0 < t →
      iteratedDeriv k h t = (-1 : ℝ) ^ k *
        (∑' n : ℕ, c n * r n ^ k * Real.exp (-r n * t))) →
    (∀ n : ℕ, 0 ≤ c n) → (∀ n : ℕ, 0 ≤ r n) →
    CompletelyMonotoneOn (R.readout () h)

private theorem rejected : ¬ arena.Law negativeFunction := by
  intro h
  have hz := @h (fun _ => 0) (fun _ => 0) (fun _ => 0) contDiffOn_const
    (fun k t ht => by simp) (fun n => le_refl _) (fun n => le_refl _)
  exact negative_not_cm hz

def family : Registration arena (type_of% @cm_of_nonnegative_exponential_expansion) where
  actual := functionActual
  bridge := Iff.rfl
  variation := ⟨@cm_of_nonnegative_exponential_expansion, negativeFunction, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law functionActual negativeFunction rejected
  dependence := functionDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@cm_of_nonnegative_exponential_expansion) (Realization functionSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.ExpRatioCM.Positive.Criterion.unit
  realizationName := `Reg.D5.S3.Analytic.ExpRatioCM.Positive.Criterion.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize functionSignature (fun _ h t => h t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.ExpRatioCM.Positive
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit
end Criterion

abbrev signature := _root_.Reg.D5.S3.Analytic.ExpRatioCM.Series.momentSignature
abbrev actual := _root_.Reg.D5.S3.Analytic.ExpRatioCM.Series.ratioActual

def negativeRatio : Realization signature :=
  realize signature (fun _ _ _ => (-1 : ℝ)) (fun e => nomatch e)

namespace LowIndices

def arena : Arena where
  signature := signature
  Law R := ∀ (i : ℕ), i ≤ 2 →
    CompletelyMonotoneOn (R.readout () i) ∧ CompletelyMonotoneOn (ratioG i)

private theorem rejected : ¬ arena.Law negativeRatio := by
  intro h
  exact negative_not_cm (h 0 (by norm_num)).1

def family : Registration arena (type_of% @cm_of_le_two) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@cm_of_le_two, negativeRatio, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual negativeRatio rejected
  dependence := FirstRatioSmooth.family.dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@cm_of_le_two) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.ExpRatioCM.Positive.LowIndices.unit
  realizationName := `Reg.D5.S3.Analytic.ExpRatioCM.Positive.LowIndices.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ i t => ratioF i t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.ExpRatioCM.Positive
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit
end LowIndices

end Reg.D5.S3.Analytic.ExpRatioCM.Positive
end
