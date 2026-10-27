import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity
import Reg.Support.DependentFamily

/-! Source-bound audit of determinant positivity under strict row diagonal dominance. -/

namespace Reg.D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity

open _root_.D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

/-- Evaluate the source determinant map at its matrix, retaining every index type. -/
abbrev signature : Signature where
  Params := Σ ι : Type u, Matrix ι ι ℝ
  State p := Matrix p.1 p.1 ℝ → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p det => det p.2) (fun e => Empty.elim e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 0) (fun e => Empty.elim e)

/-- Preserve the full source telescope and both diagonal-dominance hypotheses. -/
abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {ι : Type u} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (_hd : ∀ i, 0 < M i i)
    (_h : ∀ i, ∑ j ∈ Finset.univ.erase i, ‖M i j‖ < M i i),
    0 < R.readout () ⟨ι, M⟩ Matrix.det

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hbad := @h (ULift.{u} (Fin 1)) inferInstance inferInstance 1
    (by intro i; simp)
    (by
      intro i
      have hs : ∑ j ∈ Finset.univ.erase i,
          ‖(1 : Matrix (ULift.{u} (Fin 1)) (ULift.{u} (Fin 1)) ℝ) i j‖ = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        exact False.elim ((Finset.mem_erase.mp hj).1 (Subsingleton.elim _ _))
      rw [hs]
      simp)
  change (0 : ℝ) < 0 at hbad
  exact (lt_irrefl 0) hbad

theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨⟨ULift.{u} (Fin 1), 1⟩, (fun _ => 0), (fun _ => 1), ?_⟩
  exact zero_ne_one

def source_registration : Registration arena.{u} (type_of% @det_pos_of_dominant.{u}) where
  actual := realize signature.{u} (fun _ p det => det p.2) (fun e => Empty.elim e)
  bridge := Iff.rfl
  variation := ⟨@det_pos_of_dominant.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@det_pos_of_dominant.{u})
      (Realization signature.{u}) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨source_registration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ p det => det p.2) (fun e => Empty.elim e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity
    definition := none
    coordinates := #[0, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity
