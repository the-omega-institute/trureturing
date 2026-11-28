import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Analytic.GoldenTomography.FinitePronySecondMomentRange

/-! Observe the squared mean in the sufficient lower bound for a second moment. -/

set_option autoImplicit false

namespace Reg.D5.S3.Analytic.GoldenTomography.FinitePronySecondMomentRange

open _root_.D5.S3.Analytic.GoldenTomography.FinitePronySecondMomentRange
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

universe u

private abbrev signature : Signature.{u+1,u,0,u,0} where
  Params := Σ K : Type u, Field K
  State p := p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.1
  Anchor := Empty
  finiteAnchor := inferInstance

private def actual : Realization signature.{u} :=
  realize signature (fun _ p x => letI := p.2; x ^ 2) (fun e => nomatch e)

private def rejected : Realization signature.{u} :=
  realize signature (fun _ p _ => letI := p.2; (-1 : p.1)) (fun e => nomatch e)

private abbrev arena : Arena.{u+1,u,0,u,0} where
  signature := signature
  Law R := ∀ {K : Type u} [field : Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {a b M x s : K} (_hM : 0 < M),
    (∀ n, HasMoments n a b M x s →
      a < x ∧ x < b ∧ M * x ^ 2 ≤ s ∧ s < M * ((a + b) * x - a * b) ∧
        (s = M * x ^ 2 ↔ n = 1)) ∧
    (a < x ∧ x < b ∧ M * R.readout () ⟨K, field⟩ x ≤ s ∧ s < M * ((a + b) * x - a * b) →
      HasMoments (if s = M * x ^ 2 then 1 else 2) a b M x s)

private instance liftedOrder : IsStrictOrderedRing (ULift.{u} ℚ) :=
  Function.Injective.isStrictOrderedRing ULift.down rfl rfl (fun _ _ => rfl)
    (fun _ _ => rfl) Iff.rfl Iff.rfl

private theorem rejected_law : ¬ arena.{u}.Law rejected.{u} := by
  intro h
  let K := ULift.{u} ℚ
  have hh := h (K := K) (a := -1) (b := 1) (M := 1) (x := 0) (s := -1)
    (by decide)
  have hlower : (1 : K) * rejected.readout () ⟨K, inferInstance⟩ 0 ≤ -1 := by
    change (1 : K) * (-1) ≤ -1
    simp
  have hupper : (-1 : K) < 1 * ((-1 + 1) * 0 - (-1) * 1) := by
    rw [mul_zero, zero_sub, mul_one, one_mul, neg_neg]
    decide
  have hrealization := hh.2 ⟨by decide, by decide, hlower, hupper⟩
  have impossible := (hh.1 _ hrealization).2.2.1
  rw [zero_pow (by decide : 2 ≠ 0), mul_zero] at impossible
  exact (by decide : ¬ (0 : K) ≤ -1) impossible

private theorem sensitivity : Sensitivity arena.{u} actual.{u} := by
  constructor
  · intro role
    refine ⟨rejected, ?_, ?_, rejected_law⟩
    · intro other different
      exact (different (Subsingleton.elim _ _)).elim
    · funext e
      exact nomatch e
  · intro e
    exact nomatch e

private theorem dependence : ObservationalDependence signature.{u} actual.{u} := by
  intro _
  let K := ULift.{u} ℚ
  exact ⟨⟨K, inferInstance⟩, 0, 1, (by decide : (0 : K) ^ 2 ≠ 1 ^ 2)⟩

def family : Registration arena.{u} (type_of% @finite_prony_second_moment_range.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@finite_prony_second_moment_range.{u}, rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

def audit : Contract.Registration.{u+1,0,1,0,0,0,u+1,u,0,u,0,0}
    (@finite_prony_second_moment_range.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.GoldenTomography.FinitePronySecondMomentRange.unit
  realizationName := `Reg.D5.S3.Analytic.GoldenTomography.FinitePronySecondMomentRange.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p x => letI := p.2; x ^ 2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.GoldenTomography.FinitePronySecondMomentRange
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "arg", "domain", "arg", "arg", "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Analytic.GoldenTomography.FinitePronySecondMomentRange
