import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Quantum.Measurements.VisibleStateSpaceDimension

/-! Original-source audit of the public density-matrix compactness and convexity supplier. -/
noncomputable section
open Set
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Measurements.VisibleStateSpaceDimension
namespace Reg.D5.S3.Quantum.Measurements.VisibleStateSpaceDimension

abbrev signature : Signature where
  Params := {d : ℕ // d ≠ 0}
  State p := Matrix (Fin p.1) (Fin p.1) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ M => M.PosSemidef ∧ Matrix.trace M = 1) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => True) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ d : ℕ, ∀ [NeZero d],
    IsCompact {M | R.readout () ⟨d, NeZero.ne d⟩ M} ∧
      Convex ℝ {M | R.readout () ⟨d, NeZero.ne d⟩ M}
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hc := (h 1).1
  change IsCompact (univ : Set (Matrix (Fin 1) (Fin 1) ℂ)) at hc
  exact noncompact_univ _ hc

def family : Registration arena (type_of% density_matrix_set_compact_convex) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨density_matrix_set_compact_convex, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := by
    intro i
    let p : signature.Params := ⟨1, by decide⟩
    refine ⟨p, 1, 0, ?_⟩
    intro h
    have ht : actual.readout i p 1 := ⟨Matrix.PosSemidef.one, by norm_num [p]⟩
    have hz : actual.readout i p 0 := (Iff.of_eq h).mp ht
    have he := hz.2
    norm_num [p] at he

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    density_matrix_set_compact_convex (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Measurements.VisibleStateSpaceDimension.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Measurements.VisibleStateSpaceDimension.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ M => M.PosSemidef ∧ Matrix.trace M = 1) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurements.VisibleStateSpaceDimension
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration
end Reg.D5.S3.Quantum.Measurements.VisibleStateSpaceDimension
