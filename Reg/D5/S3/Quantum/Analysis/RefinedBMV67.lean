import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Analysis.RefinedBMV67
import Reg.Support.DependentFamily

/-! Trace readout for Hägele's four comparisons at degrees six and seven. -/

namespace Reg.D5.S3.Quantum.Analysis.RefinedBMV67

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

abbrev productArena6 : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ),
    A.PosSemidef → B.PosSemidef →
    210 * (R.readout () n (((A ^ (6 / 4 : ℝ)) * B) ^ 4)).re ≤
      ((balancedWords 6 4).map fun w ↦ (trace (evalWord A B w)).re).sum

abbrev exponentialArena6 : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (H K : Matrix (Fin n) (Fin n) ℂ),
    H.IsHermitian → K.IsHermitian →
    210 * (R.readout () n (exp ((6 : ℝ) • H + (4 : ℝ) • K))).re ≤
      ((balancedWords 6 4).map fun w ↦ (trace (evalWord (exp H) (exp K) w)).re).sum

private theorem product_rejected6 : ¬ productArena6.Law rejected := by
  intro h
  have impossible := h (n := 0) 0 0 Matrix.PosSemidef.zero Matrix.PosSemidef.zero
  norm_num [rejected, realize, trace_eq_zero_of_isEmpty] at impossible

private theorem exponential_rejected6 : ¬ exponentialArena6.Law rejected := by
  intro h
  have impossible := h (n := 0) 0 0 Matrix.isHermitian_zero Matrix.isHermitian_zero
  norm_num [rejected, realize, trace_eq_zero_of_isEmpty] at impossible

abbrev productArena7 : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ),
    A.PosSemidef → B.IsHermitian →
    330 * (R.readout () n (((A ^ (7 / 4 : ℝ)) * B) ^ 4)).re ≤
      ((balancedWords 7 4).map fun w ↦ (trace (evalWord A B w)).re).sum

abbrev exponentialArena7 : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (H K : Matrix (Fin n) (Fin n) ℂ),
    H.IsHermitian → K.IsHermitian →
    330 * (R.readout () n (exp ((7 : ℝ) • H + (4 : ℝ) • K))).re ≤
      ((balancedWords 7 4).map fun w ↦ (trace (evalWord (exp H) (exp K) w)).re).sum

private theorem product_rejected7 : ¬ productArena7.Law rejected := by
  intro h
  have impossible := h (n := 0) 0 0 Matrix.PosSemidef.zero Matrix.isHermitian_zero
  norm_num [rejected, realize, trace_eq_zero_of_isEmpty] at impossible

private theorem exponential_rejected7 : ¬ exponentialArena7.Law rejected := by
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

def productFamily6 : Registration productArena6 (type_of% @product_bound64) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@product_bound64, rejected, product_rejected6⟩
  sensitivity := sensitivity productArena6.Law product_rejected6
  dependence := depends

def exponentialFamily6 : Registration exponentialArena6 (type_of% @exponential_bound64) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exponential_bound64, rejected, exponential_rejected6⟩
  sensitivity := sensitivity exponentialArena6.Law exponential_rejected6
  dependence := depends

def productRegistration6 : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@product_bound64) (Realization signature) Unit Unit where
  unitName := `RefinedBMV.product_bound64.__information_unit
  realizationName := ``productFamily6
  realizationSource := none
  generated := false
  arena := .source ⟨productArena6⟩
  objectArena := .source ⟨productArena6⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source productArena6 ⟨productFamily6⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ X => Matrix.trace X) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.RefinedBMV67
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

def exponentialRegistration6 : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@exponential_bound64) (Realization signature) Unit Unit where
  unitName := `RefinedBMV.exponential_bound64.__information_unit
  realizationName := ``exponentialFamily6
  realizationSource := none
  generated := false
  arena := .source ⟨exponentialArena6⟩
  objectArena := .source ⟨exponentialArena6⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source exponentialArena6 ⟨exponentialFamily6⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ X => Matrix.trace X) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.RefinedBMV67
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


def productFamily7 : Registration productArena7 (type_of% @product_bound74) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@product_bound74, rejected, product_rejected7⟩
  sensitivity := sensitivity productArena7.Law product_rejected7
  dependence := depends

def exponentialFamily7 : Registration exponentialArena7 (type_of% @exponential_bound74) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exponential_bound74, rejected, exponential_rejected7⟩
  sensitivity := sensitivity exponentialArena7.Law exponential_rejected7
  dependence := depends

def productRegistration7 : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@product_bound74) (Realization signature) Unit Unit where
  unitName := `RefinedBMV.product_bound74.__information_unit
  realizationName := ``productFamily7
  realizationSource := none
  generated := false
  arena := .source ⟨productArena7⟩
  objectArena := .source ⟨productArena7⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source productArena7 ⟨productFamily7⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ X => Matrix.trace X) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.RefinedBMV67
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

def exponentialRegistration7 : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@exponential_bound74) (Realization signature) Unit Unit where
  unitName := `RefinedBMV.exponential_bound74.__information_unit
  realizationName := ``exponentialFamily7
  realizationSource := none
  generated := false
  arena := .source ⟨exponentialArena7⟩
  objectArena := .source ⟨exponentialArena7⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source exponentialArena7 ⟨exponentialFamily7⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ X => Matrix.trace X) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.RefinedBMV67
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
end Reg.D5.S3.Quantum.Analysis.RefinedBMV67
