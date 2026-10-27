import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.Partitions.OverpartitionThreshold

/-! Source-bound audit of the uniform native overpartition identity. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Reg.D5.S3.Combinatorics.Partitions.OverpartitionThreshold
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Partitions.OverpartitionThreshold

abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ k n => T n - 2 * ∑ j ∈ Finset.Icc k n, (-1 : ℤ) ^ (j - k) * N j n)
  (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ k n => (T n - 2 * ∑ j ∈ Finset.Icc k n, (-1 : ℤ) ^ (j - k) * N j n) + 1)
  (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law readout := ∀ k n : ℕ, 0 < k → U k n = readout.readout () k n

private theorem source_bridge : (type_of% (@result)) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have good := result 1 0 (by decide)
  have bad := h 1 0 (by decide)
  change U 1 0 = (T 0 - 2 * ∑ j ∈ Finset.Icc 1 0,
    (-1 : ℤ) ^ (j - 1) * N j 0) + 1 at bad
  omega

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨2, 0, 1, ?_⟩
  change (T 0 - 2 * ∑ j ∈ Finset.Icc 2 0, (-1 : ℤ) ^ (j - 2) * N j 0) ≠
    (T 1 - 2 * ∑ j ∈ Finset.Icc 2 1, (-1 : ℤ) ^ (j - 2) * N j 1)
  norm_num [T, Fintype.sum_sigma]

def familyRegistration : Registration arena (type_of% (@result)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@result) (type_of% (realize signature actual.readout actual.anchor))
    Unit Unit where
  unitName := `D5.S3.Combinatorics.Partitions.OverpartitionThreshold.result.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Partitions.OverpartitionThreshold.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Partitions.OverpartitionThreshold
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

end Reg.D5.S3.Combinatorics.Partitions.OverpartitionThreshold
