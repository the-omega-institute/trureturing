import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Analysis.RefinedBMV.NineFour
import Reg.Support.DependentFamily

/-! Trace readout for the refined BMV comparisons at bidegree (9,4). -/

namespace Reg.D5.S3.Quantum.Analysis.RefinedBMV.NineFour

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.RefinedBMV
open LeanInformationAudit Matrix NormedSpace
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

noncomputable section

abbrev signature : Signature where
  Params := ℕ
  State n := Matrix (Fin n) (Fin n) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ X => Matrix.trace X) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev productArena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ),
    A.PosSemidef → B.IsHermitian →
    715 * (R.readout () n (((A ^ (9 / 4 : ℝ)) * B) ^ 4)).re ≤
      ((balancedWords 9 4).map fun w ↦ (trace (evalWord A B w)).re).sum

abbrev exponentialArena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (H K : Matrix (Fin n) (Fin n) ℂ),
    H.IsHermitian → K.IsHermitian →
    715 * (R.readout () n (exp ((9 : ℝ) • H + (4 : ℝ) • K))).re ≤
      ((balancedWords 9 4).map fun w ↦ (trace (evalWord (exp H) (exp K) w)).re).sum

private theorem product_rejected : ¬ productArena.Law rejected := by
  intro h
  have impossible := h (n := 0) 0 0 Matrix.PosSemidef.zero Matrix.isHermitian_zero
  norm_num [rejected, realize, trace_eq_zero_of_isEmpty] at impossible

private theorem exponential_rejected : ¬ exponentialArena.Law rejected := by
  intro h
  have impossible := h (n := 0) 0 0 Matrix.isHermitian_zero Matrix.isHermitian_zero
  norm_num [rejected, realize, trace_eq_zero_of_isEmpty] at impossible

private theorem depends : ObservationalDependence signature actual := by
  intro role
  refine ⟨1, 0, 1, ?_⟩
  change Matrix.trace (0 : Matrix (Fin 1) (Fin 1) ℂ) ≠
    Matrix.trace (1 : Matrix (Fin 1) (Fin 1) ℂ)
  norm_num [Matrix.trace_one]

private theorem sensitivity (law : Realization signature → Prop) (hbad : ¬ law rejected) :
    Sensitivity ⟨signature, law⟩ actual := by
  constructor
  · intro i
    exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, hbad⟩
  · intro e
    exact nomatch e

def productFamily : Registration productArena (type_of% @product_bound94) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@product_bound94, rejected, product_rejected⟩
  sensitivity := sensitivity productArena.Law product_rejected
  dependence := depends

def exponentialFamily : Registration exponentialArena (type_of% @exponential_bound94) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exponential_bound94, rejected, exponential_rejected⟩
  sensitivity := sensitivity exponentialArena.Law exponential_rejected
  dependence := depends

def productRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@product_bound94) (Realization signature) Unit Unit where
  unitName := `RefinedBMV.product_bound94.__information_unit
  realizationName := ``productFamily
  realizationSource := none
  generated := false
  arena := .source ⟨productArena⟩
  objectArena := .source ⟨productArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source productArena ⟨productFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ X => Matrix.trace X) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.RefinedBMV.NineFour
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def exponentialRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@exponential_bound94) (Realization signature) Unit Unit where
  unitName := `RefinedBMV.exponential_bound94.__information_unit
  realizationName := ``exponentialFamily
  realizationSource := none
  generated := false
  arena := .source ⟨exponentialArena⟩
  objectArena := .source ⟨exponentialArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source exponentialArena ⟨exponentialFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ X => Matrix.trace X) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.RefinedBMV.NineFour
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Quantum.Analysis.RefinedBMV.NineFour
