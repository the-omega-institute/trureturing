import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Analysis.RefinedBMVLargeDegree
import Reg.Support.DependentFamily

/-! The two bounds both read the trace of a matrix on the left-hand side. -/

namespace Reg.D5.S3.Quantum.Analysis.RefinedBMVLargeDegree

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.RefinedBMV
open _root_.RefinedBMV.LargeDegree
open LeanInformationAudit Matrix NormedSpace
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

noncomputable section

universe u

local instance (n : Type u) : DecidableEq n := Classical.decEq n

abbrev signature : Signature where
  Params := Σ n : Type u, Fintype n
  State p := Matrix p.1 p.1 ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p X => letI := p.2; Matrix.trace X) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev productArena : Arena where
  signature := signature.{u}
  Law R := ∀ {n : Type u} [inst : Fintype n] {p : ℕ}, 3 ≤ p →
    ∀ A B : Matrix n n ℂ, A.PosSemidef → B.PosSemidef →
      R.readout () ⟨n, inst⟩ (((A ^ ((p : ℝ) / 3)) * B) ^ 3) ≤ DimThree.wordMean p A B

abbrev exponentialArena : Arena where
  signature := signature.{u}
  Law R := ∀ {n : Type u} [inst : Fintype n] {p : ℕ}, 3 ≤ p →
    ∀ H K : Matrix n n ℂ, H.IsHermitian → K.IsHermitian →
      R.readout () ⟨n, inst⟩ (exp ((p : ℝ) • H + (3 : ℝ) • K)) ≤
        DimThree.wordMean p (exp H) (exp K)

private theorem product_rejected : ¬ productArena.{u}.Law rejected := by
  intro h
  have impossible := h (n := ULift.{u} Empty) (p := 3) (by decide) 0 0
    Matrix.PosSemidef.zero Matrix.PosSemidef.zero
  norm_num [rejected, realize, DimThree.wordMean, balancedWords,
    trace_eq_zero_of_isEmpty, Complex.le_def] at impossible

private theorem exponential_rejected : ¬ exponentialArena.{u}.Law rejected := by
  intro h
  have impossible := h (n := ULift.{u} Empty) (p := 3) (by decide) 0 0
    Matrix.isHermitian_zero Matrix.isHermitian_zero
  norm_num [rejected, realize, DimThree.wordMean, balancedWords,
    trace_eq_zero_of_isEmpty, Complex.le_def] at impossible

private theorem depends : ObservationalDependence signature.{u} actual := by
  intro role
  refine ⟨⟨ULift.{u} (Fin 1), inferInstance⟩, 0, 1, ?_⟩
  change Matrix.trace (0 : Matrix (ULift.{u} (Fin 1)) (ULift.{u} (Fin 1)) ℂ) ≠
    Matrix.trace (1 : Matrix (ULift.{u} (Fin 1)) (ULift.{u} (Fin 1)) ℂ)
  norm_num [Matrix.trace_one]

private theorem sensitivity
    (law : Realization signature.{u} → Prop) (hbad : ¬ law rejected) :
    Sensitivity ⟨signature, law⟩ actual := by
  constructor
  · intro i
    exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, hbad⟩
  · intro e
    exact nomatch e

def productFamily : Registration productArena.{u} (type_of% @product_bound_all.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@product_bound_all.{u}, rejected, product_rejected⟩
  sensitivity := sensitivity productArena.Law product_rejected
  dependence := depends

def exponentialFamily :
    Registration exponentialArena.{u} (type_of% @exponential_bound_all.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exponential_bound_all.{u}, rejected, exponential_rejected⟩
  sensitivity := sensitivity exponentialArena.Law exponential_rejected
  dependence := depends

def productRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@product_bound_all.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `RefinedBMV.LargeDegree.product_bound_all.__information_unit
  realizationName := ``productFamily
  realizationSource := none
  generated := false
  arena := .source ⟨productArena.{u}⟩
  objectArena := .source ⟨productArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source productArena.{u} ⟨productFamily.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p X => letI := p.2; Matrix.trace X) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.RefinedBMVLargeDegree
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def exponentialRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@exponential_bound_all.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `RefinedBMV.LargeDegree.exponential_bound_all.__information_unit
  realizationName := ``exponentialFamily
  realizationSource := none
  generated := false
  arena := .source ⟨exponentialArena.{u}⟩
  objectArena := .source ⟨exponentialArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source exponentialArena.{u} ⟨exponentialFamily.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p X => letI := p.2; Matrix.trace X) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.RefinedBMVLargeDegree
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms productRegistration
#print axioms exponentialRegistration

end
end Reg.D5.S3.Quantum.Analysis.RefinedBMVLargeDegree
