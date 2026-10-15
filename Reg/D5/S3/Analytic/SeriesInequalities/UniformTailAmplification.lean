import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.SeriesInequalities.UniformTailAmplification
import Reg.Support.SingleDependentReadout

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Analytic.SeriesInequalities.UniformTailAmplification
open LeanInformationAudit Filter
open scoped BigOperators ENNReal NNReal Topology

set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u

noncomputable section
namespace Reg.D5.S3.Analytic.SeriesInequalities.UniformTailAmplification

/-- The observed object is the entire common multiplier, with no restriction
on its infinite domain or on the family X in the original source telescope. -/
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => ℕ → ℕ) (fun _ => ℕ → ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ w => w) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => 0) (fun e => nomatch e)

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨(), (fun _ => 0), (fun _ => 1), ?_⟩
  change (fun _ : ℕ => (0 : ℕ)) ≠ (fun _ : ℕ => (1 : ℕ))
  intro h
  have h0 := congrFun h 0
  norm_num at h0

def arena : Arena where
  signature := signature
  Law F := ∀ {X : Type u} (a : X → ℕ → ℝ≥0∞) (δ : ℝ≥0) (_hδ : 0 < δ)
      (_hUT : ∀ ε : ℝ≥0, 0 < ε →
        ∃ N : ℕ, ∀ x, (∑' k, a x (N + k)) ≤ (ε : ℝ≥0∞)),
    ∃ w : ℕ → ℕ,
      (∀ n, 1 ≤ (F.readout () () w) n) ∧ Monotone w ∧
      Tendsto w atTop atTop ∧
      (∀ x, (∑' n, (w n : ℝ≥0∞) * a x n) ≤
        (∑' n, a x n) + (δ : ℝ≥0∞)) ∧
      (∀ ε : ℝ≥0, 0 < ε → ∃ M : ℕ, ∀ x,
        (∑' k, (w (M + k) : ℝ≥0∞) * a x (M + k)) ≤ (ε : ℝ≥0∞))

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  obtain ⟨w, hw, _⟩ := @h PUnit.{u + 1} (fun _ _ => 0) 1 (by norm_num)
    (fun ε _ => ⟨0, fun _ => by simp⟩)
  have hbad := hw 0
  change (1 : ℕ) ≤ 0 at hbad
  omega

def family : Registration arena.{u}
    (type_of% (@exists_uniform_tail_amplification.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_uniform_tail_amplification, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

noncomputable def audit :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@exists_uniform_tail_amplification.{u}) (Realization signature) Unit Unit := {
  unitName :=
    `Reg.D5.S3.Analytic.SeriesInequalities.UniformTailAmplification.uniform_tail_unit
  realizationName := `Reg.D5.S3.Analytic.SeriesInequalities.UniformTailAmplification.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ w => w) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.SeriesInequalities.UniformTailAmplification
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "body",
        "fn", "arg", "body", "arg", "fn"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms exists_uniform_tail_amplification
#print axioms family
#print axioms audit

end Reg.D5.S3.Analytic.SeriesInequalities.UniformTailAmplification
