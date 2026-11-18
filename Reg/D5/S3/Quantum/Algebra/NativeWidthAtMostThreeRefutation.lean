import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Algebra.NativeWidthAtMostThreeRefutation
import Reg.Support.DependentFamily

/-! Source-bound audit of the unrestricted positive-scalar obstruction. -/

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Algebra.NativeWidthAtMostThreeRefutation
open Matrix
open scoped BigOperators ComplexOrder

noncomputable section
namespace Reg.D5.S3.Quantum.Algebra.NativeWidthAtMostThreeRefutation

abbrev signature : Signature where
  Params := MatN 3
  State _ := MatM 3
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Matrix (Fin 5 × Fin 3) (Fin 5 × Fin 3) ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ N M => (∑ r, Matrix.kronecker (M r) (N r))ᴴ *
    (∑ r, Matrix.kronecker (M r) (N r))) (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (M : MatM 3) (N : MatN 3) (lambda : ℝ), 0 < lambda →
    ¬ (R.readout () N M = (lambda : ℂ) •
      (1 : Matrix (Fin 5 × Fin 3) (Fin 5 × Fin 3) ℂ))

private def spikeM : MatM 3 := fun r i j => if r = 0 ∧ i = 0 ∧ j = 0 then 1 else 0
private def spikeN : MatN 3 := fun r i j => if r = 0 ∧ i = 0 ∧ j = 0 then 1 else 0

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 0 0 1 (by norm_num)
  apply hh
  simp [rejected, realize]

def family : Registration arena (type_of% (@positive_scalar_obstruction)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨positive_scalar_obstruction, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨spikeN, (fun _ _ _ => 0), spikeM, ?_⟩
    intro he
    have hh := congrArg (fun A : Matrix (Fin 5 × Fin 3) (Fin 5 × Fin 3) ℂ =>
      A (0,0) (0,0)) he
    norm_num [actual, realize, spikeM, spikeN, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.sum_apply, Matrix.kronecker,
      Matrix.kroneckerMap_apply, Fintype.sum_prod_type, Fin.sum_univ_succ, Pi.zero_apply, Matrix.kroneckerMap] at hh

noncomputable def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@positive_scalar_obstruction) (Realization signature) Unit Unit := {
  unitName :=
    `D5.S3.Quantum.Algebra.NativeWidthAtMostThreeRefutation.scalar_information_unit
  realizationName := `Reg.D5.S3.Quantum.Algebra.NativeWidthAtMostThreeRefutation.family
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
    (fun _ N M => (∑ r, Matrix.kronecker (M r) (N r))ᴴ *
      (∑ r, Matrix.kronecker (M r) (N r))) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Algebra.NativeWidthAtMostThreeRefutation
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.Quantum.Algebra.NativeWidthAtMostThreeRefutation
