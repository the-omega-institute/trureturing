import LeanInformationAuditInterface.Contract.Registration
import D5.S3.HomologicalAlgebra.AbelianExtensionH1
import Reg.Support.DependentFamily
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.ULift

/-! Original-telescope dependent-family evidence for extension cohomology. -/

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.HomologicalAlgebra.AbelianExtensionH1
open groupCohomology

namespace Reg.D5.S3.HomologicalAlgebra.AbelianExtensionH1
noncomputable section

structure SourceData where
  N : Type
  Q : Type
  S : Type
  groupN : CommGroup N
  groupQ : Group Q
  groupS : Group S
  extension : by
    letI := groupN
    letI := groupQ
    letI := groupS
    exact GroupExtension N Q S
  automorphism : by
    letI := groupN
    letI := groupQ
    letI := groupS
    exact ↥(automorphisms extension)

abbrev signature : Signature where
  Params := SourceData
  State p := p.Q
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.Q
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p y => p.automorphism.val y) (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ p _ => by letI := p.groupQ; exact 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {N : Type} {Q : Type} {S : Type}
    [hN : CommGroup N] [hQ : Group Q] [hS : Group S] (E : GroupExtension N Q S),
    (∀ (a : automorphisms E) (y : Q),
      E.inl (@Additive.toMul N ((defectEquiv E (Additive.ofMul a)) (E.rightHom y))) =
        R.readout () ⟨N,Q,S,hN,hQ,hS,E,a⟩ y * y⁻¹) ∧
    (∀ (d : cocycles₁ (coefficients E)) (y : Q),
      ((defectEquiv E).symm d).toMul.val y = E.inl (@Additive.toMul N (d (E.rightHom y))) * y) ∧
    (∀ a : Additive (automorphisms E), a ∈ innerKernel E ↔
      ∃ b : N, ∀ y : Q,
        a.toMul.val y = E.inl b * y * (E.inl b)⁻¹) ∧
    Nonempty ((Additive (automorphisms E) ⧸ innerKernel E) ≃+ H1 (coefficients E))

abbrev statement : Prop := type_of% @classification

theorem bridge : statement ↔ arena.Law actual := Iff.rfl

private abbrev C := Multiplicative (ZMod 2)

private def testExtension : GroupExtension (ULift C) (ULift C) Unit where
  inl := {
    toFun := fun n => ⟨n.down⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  rightHom := 1
  inl_injective := fun _ _ h => h
  range_inl_eq_ker_rightHom := by
    ext y
    constructor
    · intro _; simp
    · intro _; exact ⟨⟨y.down⟩, rfl⟩
  rightHom_surjective := fun s => ⟨1, Subsingleton.elim _ _⟩

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let E := testExtension
  let a : automorphisms E := 1
  let y : ULift C := ⟨Multiplicative.ofAdd 1⟩
  have hb := (h E).1 a y
  have ha := (classification E).1 a y
  have he : (1 : ULift C) = y⁻¹ := by
    calc
      _ = E.inl (@Additive.toMul (ULift C) ((defectEquiv E (Additive.ofMul a)) (E.rightHom y))) := by
        simpa only [a, OneMemClass.coe_one, MulAut.one_apply, mul_inv_cancel] using ha.symm
      _ = _ := by simpa only [rejected, realize, one_mul] using hb
  have hy : y = 1 := by simpa only [inv_eq_one] using he.symm
  have hz := congrArg (fun z : ULift C => z.down.toAdd) hy
  exact one_ne_zero hz

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  let E := testExtension
  let p : SourceData := ⟨_,_,_,inferInstance,inferInstance,inferInstance,E,1⟩
  refine ⟨p, 1, ⟨Multiplicative.ofAdd 1⟩, ?_⟩
  intro h
  have hz := congrArg (fun z : ULift C => z.down.toAdd) h
  exact zero_ne_one hz

def family : Registration arena statement where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp @classification, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

/-- The family evidence retains the original theorem telescope. Source occurrence
selection addresses the first defect formula in its original lexical scope. -/
def entry : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@classification)
    (type_of% (realize signature (fun _ p y => p.automorphism.val y) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `Reg.D5.S3.HomologicalAlgebra.AbelianExtensionH1.informationUnit
  realizationName := `Reg.D5.S3.HomologicalAlgebra.AbelianExtensionH1.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p y => p.automorphism.val y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.HomologicalAlgebra.AbelianExtensionH1
    definition := none
    coordinates := #[0,1,2,6,7]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","fn","arg","body","body","arg","fn","arg"]
      stateBinder := 8
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.HomologicalAlgebra.AbelianExtensionH1
