import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Eigenstructure.CommonEigenvalueFieldDegree
import Reg.Support.SingleDependentReadout
import Mathlib.Algebra.Field.ULift

open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S1.Eigenstructure.CommonEigenvalueFieldDegree
open LeanInformationAudit
open scoped Matrix

noncomputable section
universe u v w z

namespace Reg.D5.S1.Eigenstructure.CommonEigenvalueFieldDegree

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ n m => n ≤ m) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

/-- The original four universes, fields, arbitrary index family and both eigenvector
hypotheses remain in the law. Only the concluding natural comparison is observed. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {F : Type u} {L : Type v} [Field F] [Field L] [Algebra F L]
    {I : Type w} {J : Type z} [Fintype J]
    (M : I → Matrix J J F) (eigenvalues : I → L) (x : J → L),
    x ≠ 0 → (∀ i, (M i).map (algebraMap F L) *ᵥ x = eigenvalues i • x) →
    FiniteDimensional F (IntermediateField.adjoin F (Set.range eigenvalues)) ∧
      R.readout () ()
        (Module.finrank F (IntermediateField.adjoin F (Set.range eigenvalues))) (Fintype.card J)

private theorem actual_law : arena.{u,v,w,z}.Law actual :=
  @_root_.D5.S1.Eigenstructure.CommonEigenvalueFieldDegree.common_eigenvalue_field_degree

private theorem rejected_law : ¬ arena.{u,v,w,z}.Law rejected := by
  let F := ULift.{u} ℚ
  let L := ULift.{v} ℚ
  let φ : F →+* L := ULift.ringEquiv.symm.toRingHom.comp ULift.ringEquiv.toRingHom
  let : Algebra F L := φ.toAlgebra
  let J := PUnit.{z+1}
  let I := PUnit.{w+1}
  let M : I → Matrix J J F := fun _ => 1
  let eigenvalues : I → L := fun _ => 1
  let x : J → L := fun _ => 1
  have hx : x ≠ 0 := by
    intro h
    have hbad := congrFun h PUnit.unit
    exact one_ne_zero hbad
  have heig (i : I) : (M i).map (algebraMap F L) *ᵥ x = eigenvalues i • x := by
    simp [M, eigenvalues, Matrix.map_one]
  intro h
  exact (h M eigenvalues x hx heig).2

def family : Registration arena.{u,v,w,z} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    intro h
    have hbad : (1 : ℕ) ≤ 0 := Eq.mp (congrFun h 0) le_rfl
    omega

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@common_eigenvalue_field_degree.{u,v,w,z})
    (Realization signature) Type Unit where
  unitName := `Reg.D5.S1.Eigenstructure.CommonEigenvalueFieldDegree.unit
  realizationName := `Reg.D5.S1.Eigenstructure.CommonEigenvalueFieldDegree.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n m => n ≤ m) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Eigenstructure.CommonEigenvalueFieldDegree
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end Reg.D5.S1.Eigenstructure.CommonEigenvalueFieldDegree
end
