import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Eigenstructure.OrthogonalAbsoluteProductMinimum
import Reg.Support.SingleDependentReadout

open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S1.Eigenstructure.OrthogonalAbsoluteProductMinimum
open LeanInformationAudit
open scoped Matrix

noncomputable section
namespace Reg.D5.S1.Eigenstructure.OrthogonalAbsoluteProductMinimum

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

/-- The complete positive-dimension, nonsingular-matrix telescope and the attained
clause are retained. The observation is the lower-bound comparison relation. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (K : ℕ), 0 < K → ∀ (P : Matrix (Fin K) (Fin K) ℝ), P.det ≠ 0 →
    (∀ Q : Matrix (Fin K) (Fin K) ℝ, Orthogonal Q →
      R.readout () () 1 (objective P Q)) ∧
    ∃ Q : Matrix (Fin K) (Fin K) ℝ, Orthogonal Q ∧ objective P Q = 1

private theorem actual_law : arena.Law actual := result

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := (h 1 (by decide) 1 (by simp)).1 1 (by simp [Orthogonal])
  exact hh

def family : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    intro he
    have hbad : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he 0) le_rfl
    norm_num at hbad

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Eigenstructure.OrthogonalAbsoluteProductMinimum.result)
    (Realization signature) Type Unit where
  unitName := `Reg.D5.S1.Eigenstructure.OrthogonalAbsoluteProductMinimum.unit
  realizationName := `Reg.D5.S1.Eigenstructure.OrthogonalAbsoluteProductMinimum.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Eigenstructure.OrthogonalAbsoluteProductMinimum
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end Reg.D5.S1.Eigenstructure.OrthogonalAbsoluteProductMinimum
end
