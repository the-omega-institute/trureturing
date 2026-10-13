import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Lieb.MonotoneBlockConcavity
import Reg.Support.DependentFamily
import Mathlib.Analysis.InnerProductSpace.PiL2

open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S3.Quantum.Lieb.MonotoneBlockConcavity
open LownerHeinzTheorem JensenOperatorInequality LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.Quantum.Lieb.MonotoneBlockConcavity
universe u

abbrev signature : Signature where
  Params := ℝ → ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ f x => f x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ x => x ^ (2 : ℕ)) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H], ∀ (f : ℝ → ℝ),
    ContinuousOn f (Set.Ioi 0) →
    LownerHeinzCore.OperatorMonotoneOn (𝓐 := L (HSum H)) (Set.Ioi 0) f →
    ∀ {A B : L H}, IsStrictlyPositive A → IsStrictlyPositive B →
    ∀ {t : ℝ}, 0 ≤ t → t ≤ 1 →
      (1 - t) • cfcR f A + t • cfcR f B ≤
        cfcR (r.readout () f) ((1 - t) • A + t • B)

private theorem actual_law : arena.{u}.Law actual := by
  intro H _ _ _ _ f hf hmono A B hA hB t ht0 ht1
  exact monotone_double_space_concavity f hf hmono hA hB ht0 ht1

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro hall
  let H := EuclideanSpace ℂ (ULift.{u} (Fin 1))
  have hmono : LownerHeinzCore.OperatorMonotoneOn
      (𝓐 := L (HSum H)) (Set.Ioi 0) (fun x : ℝ => x) := by
    intro A B hA hB hBA _ _
    change cfc (id : ℝ → ℝ) B ≤ cfc (id : ℝ → ℝ) A
    rw [cfc_id ℝ B (IsSelfAdjoint.of_nonneg hB),
      cfc_id ℝ A (IsSelfAdjoint.of_nonneg hA)]
    exact hBA
  have hc := hall (H := H) (fun x : ℝ => x) continuous_id.continuousOn hmono
    (A := (1/4 : ℝ) • (1 : L H)) (B := (3/4 : ℝ) • (1 : L H))
    (isStrictlyPositive_one.smul (by norm_num : (0 : ℝ) < 1/4))
    (isStrictlyPositive_one.smul (by norm_num : (0 : ℝ) < 3/4))
    (t := (1/2 : ℝ)) (by norm_num) (by norm_num)
  change (1 - (1/2 : ℝ)) • cfc (id : ℝ → ℝ) ((1/4 : ℝ) • (1 : L H)) +
    (1/2 : ℝ) • cfc (id : ℝ → ℝ) ((3/4 : ℝ) • (1 : L H)) ≤
    cfc (fun x : ℝ => x ^ (2 : ℕ))
      ((1 - (1/2 : ℝ)) • ((1/4 : ℝ) • (1 : L H)) +
        (1/2 : ℝ) • ((3/4 : ℝ) • 1)) at hc
  have heq : (1 - (1/2 : ℝ)) • ((1/4 : ℝ) • (1 : L H)) +
      (1/2 : ℝ) • ((3/4 : ℝ) • 1) = algebraMap ℝ (L H) (1/2) := by
    simp [Algebra.algebraMap_eq_smul_one, smul_smul, ← add_smul]
    norm_num
  rw [heq, ← Algebra.algebraMap_eq_smul_one (R := ℝ) (A := L H) (1/4 : ℝ),
    ← Algebra.algebraMap_eq_smul_one (R := ℝ) (A := L H) (3/4 : ℝ),
    cfc_algebraMap, cfc_algebraMap, cfc_algebraMap] at hc
  norm_num [Algebra.algebraMap_eq_smul_one, smul_smul, ← add_smul] at hc

def familyRegistration : Registration arena.{u}
    (type_of% (@monotone_double_space_concavity.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      cases i; cases j
      exact (hj rfl).elim
    · intro e
      exact nomatch e
  dependence := by
    change ObservationalDependence signature actual
    intro i
    refine ⟨(fun x : ℝ => x), (0 : ℝ), (1 : ℝ), ?_⟩
    norm_num [actual, realize]

/- The selected source observation is only the function operand of the RHS CFC.
The two LHS operands and every hypothesis remain fixed in the intervention law. -/
noncomputable def registration_1 : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@monotone_double_space_concavity.{u}) (type_of% actual) Type Unit := {
  unitName := `Reg.D5.S3.Quantum.Lieb.MonotoneBlockConcavity.monotone_double_space_concavity.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Lieb.MonotoneBlockConcavity.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨familyRegistration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ f x => f x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℝ
  sourceSelection := some {
    owner := `D5.S3.Quantum.Lieb.MonotoneBlockConcavity
    definition := none
    coordinates := #[5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms familyRegistration
#print axioms registration_1
end Reg.D5.S3.Quantum.Lieb.MonotoneBlockConcavity
