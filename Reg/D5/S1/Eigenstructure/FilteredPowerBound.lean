import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Eigenstructure.FilteredPowerBound
import Reg.Support.DependentFamily
import Mathlib.Algebra.Field.ULift

open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators

noncomputable section
universe u v

namespace Reg.D5.S1.Eigenstructure.FilteredPowerBound

private instance liftedRealField : NontriviallyNormedField (ULift.{u} ℝ) where
  __ := (inferInstance : Field (ULift.{u} ℝ))
  __ := (inferInstance : Norm (ULift.{u} ℝ))
  __ := (inferInstance : MetricSpace (ULift.{u} ℝ))
  dist_eq x y := dist_eq_norm_neg_add x y
  norm_mul x y := norm_mul x.down y.down
  non_trivial := ⟨⟨2⟩, by norm_num [ULift.norm_def]⟩

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

/-- The selected readout is the real comparison in the conclusion; every source premise
and every scalar and space universe is retained in the family law. -/
def arena : Arena where
  signature := signature
  Law R := ∀ {𝕜 : Type u} {E : Type v} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (A B : E →L[𝕜] E) (F : ℕ → Submodule 𝕜 E) (h : ℕ),
    F 0 = ⊥ → F h = ⊤ →
    (∀ j < h, ∀ x ∈ F (j + 1), A x ∈ F (j + 1)) →
    (∀ j < h, ∀ x ∈ F (j + 1), B x ∈ F j) →
    ‖A‖ ≤ 1 → ∀ k : ℕ,
    R.readout () () ‖(A + B) ^ k‖
      (∑ l ∈ Finset.range h, (k.choose l : ℝ) * ‖B‖ ^ l)

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro hh
  exact @hh (ULift.{u} ℝ) PUnit.{v+1} inferInstance inferInstance inferInstance
    0 0 (fun _ => ⊥) 0 rfl
    (by apply Submodule.ext; intro x; simp [Subsingleton.elim x 0])
    (by intro j hj; omega) (by intro j hj; omega) (by simp) 0

def registration : Registration arena.{u,v}
    (∀ {𝕜 : Type u} {E : Type v} [NontriviallyNormedField 𝕜]
      [NormedAddCommGroup E] [NormedSpace 𝕜 E]
      (A B : E →L[𝕜] E) (F : ℕ → Submodule 𝕜 E) (h : ℕ),
      F 0 = ⊥ → F h = ⊤ →
      (∀ j < h, ∀ x ∈ F (j + 1), A x ∈ F (j + 1)) →
      (∀ j < h, ∀ x ∈ F (j + 1), B x ∈ F j) →
      ‖A‖ ≤ 1 → ∀ k : ℕ,
      ‖(A + B) ^ k‖ ≤ ∑ l ∈ Finset.range h, (k.choose l : ℝ) * ‖B‖ ^ l) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S1.Eigenstructure.FilteredPowerBound.norm_add_pow_le_sum_choose,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      cases i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      cases j
      exact (hj rfl).elim
    · intro e
      cases e
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
    intro he
    have bad : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he 0) le_rfl
    norm_num at bad

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Eigenstructure.FilteredPowerBound.norm_add_pow_le_sum_choose.{u,v})
    (type_of% (realize.{0,0,0,0,0} signature (fun _ _ x y => x ≤ y)
      (fun e => nomatch e))) Unit Unit := {
  unitName :=
    `D5.S1.Eigenstructure.FilteredPowerBound.norm_add_pow_le_sum_choose.__information_unit,
  realizationName := `Reg.D5.S1.Eigenstructure.FilteredPowerBound.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Eigenstructure.FilteredPowerBound, definition := none, coordinates := #[],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "fn", "fn"], stateBinder := 0,
      functionOperand := true, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[] }

end Reg.D5.S1.Eigenstructure.FilteredPowerBound
