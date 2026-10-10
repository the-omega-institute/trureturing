import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.AbsoluteSeparability.GurvitsBarnumMoments
import Reg.Support.DependentFamily

open LeanInformationAudit Matrix
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Entanglement.AbsoluteSeparability.GurvitsBarnumMoments
open scoped BigOperators

noncomputable section
namespace Reg.D5.S3.Quantum.Entanglement.AbsoluteSeparability.GurvitsBarnumMoments
universe u

abbrev signature : Signature where
  Params := ℕ
  State d := (Fin d → ℂ) → ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ f => designSum f) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨0, (fun _ => 0), (fun _ => 1), ?_⟩
  simp [actual, realize, designSum]

namespace Additivity

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {d : ℕ} {ι : Type u} [Fintype ι]
    (f : ι → (Fin d → ℂ) → ℂ),
      R.readout () d (fun z => ∑ a, f a z) = ∑ a, designSum (f a)

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have he := h (d := 0) (ι := ULift.{u} Empty) (fun a => nomatch a.down)
  simpa [rejected, realize] using he

def family : Registration arena.{u} (type_of% @designSum_sum.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@designSum_sum.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@designSum_sum.{u}) (Realization signature) (type_of% @designSum) Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.AbsoluteSeparability.GurvitsBarnumMoments.Additivity.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.AbsoluteSeparability.GurvitsBarnumMoments.Additivity.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := true
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨True.intro⟩ True.intro
  readout := some (realize signature actual.readout actual.anchor)
  variation := .evidence ⟨True.intro⟩ True.intro
  sensitivity := .evidence ⟨True.intro⟩ True.intro
  partialSensitivity := none
  escapeFrom := some (@designSum)
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.AbsoluteSeparability.GurvitsBarnumMoments
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := some ⟨arena.{u}, ⟨family.{u}⟩⟩
  options := #[] }

#print axioms family
#print axioms registration

end Additivity

namespace Monotonicity

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {d : ℕ} (f g : (Fin d → ℂ) → ℂ),
    (∀ z, (f z).re ≤ (g z).re) →
      (R.readout () d f).re ≤ (designSum g).re

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h (d := 0) (fun _ => 0) (fun _ => 0) (by intro z; rfl)
  norm_num [rejected, realize, designSum] at he

def family : Registration arena (type_of% @re_designSum_mono) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@re_designSum_mono, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@re_designSum_mono) (Realization signature) (type_of% @designSum) Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.AbsoluteSeparability.GurvitsBarnumMoments.Monotonicity.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.AbsoluteSeparability.GurvitsBarnumMoments.Monotonicity.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := true
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨True.intro⟩ True.intro
  readout := some (realize signature actual.readout actual.anchor)
  variation := .evidence ⟨True.intro⟩ True.intro
  sensitivity := .evidence ⟨True.intro⟩ True.intro
  partialSensitivity := none
  escapeFrom := some (@designSum)
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.AbsoluteSeparability.GurvitsBarnumMoments
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := some ⟨arena, ⟨family⟩⟩
  options := #[] }

#print axioms family
#print axioms registration

end Monotonicity

namespace QuadraticProduct

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {d : ℕ} (T U : Matrix (Fin d) (Fin d) ℂ),
    R.readout () d (fun z => quadratic T z * quadratic U z) =
      (4 : ℂ) ^ d * (trace T * trace U + ∑ i, ∑ j, T i j * U j i)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h (d := 0) 0 0
  norm_num [rejected, realize] at he

def family : Registration arena (type_of% @quadratic_product_sum) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@quadratic_product_sum, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@quadratic_product_sum) (Realization signature) (type_of% @designSum) Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.AbsoluteSeparability.GurvitsBarnumMoments.QuadraticProduct.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.AbsoluteSeparability.GurvitsBarnumMoments.QuadraticProduct.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := true
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨True.intro⟩ True.intro
  readout := some (realize signature actual.readout actual.anchor)
  variation := .evidence ⟨True.intro⟩ True.intro
  sensitivity := .evidence ⟨True.intro⟩ True.intro
  partialSensitivity := none
  escapeFrom := some (@designSum)
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.AbsoluteSeparability.GurvitsBarnumMoments
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := some ⟨arena, ⟨family⟩⟩
  options := #[] }

#print axioms family
#print axioms registration

end QuadraticProduct

end Reg.D5.S3.Quantum.Entanglement.AbsoluteSeparability.GurvitsBarnumMoments
