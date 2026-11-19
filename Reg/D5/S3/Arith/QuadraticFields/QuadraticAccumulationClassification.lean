import D5.S3.Arith.QuadraticFields.QuadraticAccumulationClassification
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

/-! Source-bound audit of the actual quadratic accumulation classification. -/

noncomputable section
set_option autoImplicit false

namespace Reg.D5.S3.Arith.QuadraticFields.QuadraticAccumulationClassification
open _root_.D5.S3.Arith.QuadraticFields.QuadraticAccumulation
open _root_.D5.S3.Arith.QuadraticFields.QuadraticAccumulationClassification
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Set Filter
open scoped Topology

abbrev signature := Reg.Support.SingleDependentReadout.signature Unit
  (fun _ => ℝ) (fun _ => Set ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ a => approximationValues a) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => Set.univ) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (D : ℤ), 2 ≤ D → Squarefree D → ∀ (A B : ℚ), B ≠ 0 →
    derivedSet (R.readout () () ((A : ℝ) + (B : ℝ) * Real.sqrt (D : ℝ))) =
      {x | ∃ s : RealField D A B, s ∈ realTraceDual D A B ∧ s ≠ 0 ∧
        (x = 2 * (B : ℝ) * Real.sqrt (D : ℝ) * (Algebra.norm ℚ s : ℝ) ∨
         x = -(2 * (B : ℝ) * Real.sqrt (D : ℝ) * (Algebra.norm ℚ s : ℝ)))}

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hz : (0 : ℝ) ∈ derivedSet (Set.univ : Set ℝ) := by
    change NeBot ((𝓝[≠] (0 : ℝ)) ⊓ 𝓟 (Set.univ : Set ℝ))
    simpa using (inferInstance : NeBot (𝓝[≠] (0 : ℝ)))
  have he := h 2 (by norm_num) (by norm_num) 0 1 (by norm_num)
  change derivedSet (Set.univ : Set ℝ) = _ at he
  rw [he] at hz
  obtain ⟨s, _, hs0, hv⟩ := hz
  let : Fact (¬ IsSquare (2 : ℚ)) := ⟨by norm_num⟩
  let E := coordinateEquiv 2 (by norm_num) 0 1 (by norm_num)
  have ht0 : E.symm s ≠ 0 := by
    intro ht
    apply hs0
    simpa using congrArg E ht
  have hn : Algebra.norm ℚ (E.symm s) ≠ 0 := Algebra.norm_ne_zero_iff.mpr ht0
  have hn' : Algebra.norm ℚ s ≠ 0 := by
    have hnE : Algebra.norm ℚ s = Algebra.norm ℚ (E.symm s) := by
      simpa only [AlgEquiv.apply_symm_apply] using Algebra.norm_eq_of_algEquiv E (E.symm s)
    rw [hnE]
    exact hn
  rcases hv with hv | hv <;> norm_num at hv <;> exact hn' hv

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1/2, ?_⟩
  change approximationValues 0 ≠ approximationValues (1/2)
  intro h
  have hm : (1/2 : ℝ) ∈ approximationValues (1/2) :=
    ⟨1, 0, by norm_num, by norm_num⟩
  rw [← h] at hm
  obtain ⟨q, p, _, hp⟩ := hm
  have hi : (1 : ℝ) = 2 * ((-|q| * p : ℤ) : ℝ) := by
    push_cast
    norm_num at hp
    nlinarith [hp]
  have hi' : (1 : ℤ) = 2 * (-|q| * p) := by exact_mod_cast hi
  omega

def family : Registration arena (type_of% (@derivedSet_eq_signed_norm_values)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@derivedSet_eq_signed_norm_values, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@derivedSet_eq_signed_norm_values) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Arith.QuadraticFields.QuadraticAccumulationClassification.derivedSet_eq_signed_norm_values.audit
  realizationName := `Reg.D5.S3.Arith.QuadraticFields.QuadraticAccumulationClassification.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ a => approximationValues a) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.QuadraticFields.QuadraticAccumulationClassification
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.QuadraticFields.QuadraticAccumulationClassification
