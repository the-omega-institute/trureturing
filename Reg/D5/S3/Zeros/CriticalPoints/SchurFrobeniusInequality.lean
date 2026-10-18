import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Zeros.CriticalPoints.SchurFrobeniusInequality
import Reg.Support.SingleDependentReadout

/-! Source-bound registration of the exact inequality and equality statement. -/

namespace Reg.D5.S3.Zeros.CriticalPoints.SchurFrobeniusInequality
open _root_.D5.S3.Zeros.CriticalPoints.SchurFrobeniusInequality
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix Complex

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- The bound as an observation of the original dimension-dependent data. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℕ (fun n => Matrix (Fin n) (Fin n) ℂ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ A => ∑ i, ∑ j, ‖A i j‖ ^ 2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

/-- The full source statement with the first upper-bound occurrence exposed. -/
def arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ),
    ((A.charpoly.roots.map (fun μ => ‖μ‖ ^ 2)).sum ≤ R.readout () n A) ∧
    (((A.charpoly.roots.map (fun μ => ‖μ‖ ^ 2)).sum = ∑ i, ∑ j, ‖A i j‖ ^ 2) ↔
      A * Aᴴ = Aᴴ * A)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := (h 0 0).1
  change ((Matrix.charpoly (0 : Matrix (Fin 0) (Fin 0) ℂ)).roots.map
    (fun μ => ‖μ‖ ^ 2)).sum ≤ (-1 : ℝ) at hh
  have hn : 0 ≤ ((Matrix.charpoly (0 : Matrix (Fin 0) (Fin 0) ℂ)).roots.map
    (fun μ => ‖μ‖ ^ 2)).sum := Multiset.sum_nonneg (by
      intro x hx
      obtain ⟨μ, _, rfl⟩ := Multiset.mem_map.mp hx
      positivity)
  linarith

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, (0 : Matrix (Fin 1) (Fin 1) ℂ), (fun _ _ => 1), ?_⟩
  norm_num [actual, realize, Fin.sum_univ_one]

def source_registration : Registration arena (type_of% @schur_frobenius) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨schur_frobenius, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Zeros.CriticalPoints.SchurFrobeniusInequality.schur_frobenius)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Zeros.CriticalPoints.SchurFrobeniusInequality.unit
  realizationName := `Reg.D5.S3.Zeros.CriticalPoints.SchurFrobeniusInequality.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ A => ∑ i, ∑ j, ‖A i j‖ ^ 2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Zeros.CriticalPoints.SchurFrobeniusInequality
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Zeros.CriticalPoints.SchurFrobeniusInequality
