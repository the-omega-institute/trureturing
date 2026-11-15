import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Quantum.Analysis.PositiveMomentRigidity
import Mathlib.Analysis.InnerProductSpace.StarOrder

/-! Full source telescopes and dependent carrier families for positive moments.
Whole-family interventions retain the zero output and all other degenerate fibers. -/

open LeanInformationAudit
open scoped ComplexOrder unitInterval
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Analysis.PositiveMomentRigidity

noncomputable section
universe u

namespace Reg.D5.S3.Quantum.Analysis.PositiveMomentRigidity

abbrev orderSignature : Signature where
  Params := Σ A : Type u, PartialOrder A
  State p := p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.1 → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def orderActual : Realization orderSignature.{u} :=
  realize orderSignature (fun _ p x y => @LE.le p.1 p.2.toLE x y) (fun e => nomatch e)

def orderRejected : Realization orderSignature.{u} :=
  realize orderSignature (fun _ _ _ _ => False) (fun e => nomatch e)

namespace Kadison

def arena : Arena where
  signature := orderSignature.{u}
  Law R := ∀ {A : Type u} [CStarAlgebra A] [horder : PartialOrder A] [StarOrderedRing A]
    (Z : C(I, ℂ) →ₚ[ℂ] A) (_hunit : Z 1 = 1) (g : C(I, ℝ)),
    R.readout () ⟨A, horder⟩ (Z (complexify g) * Z (complexify g))
      (Z (complexify (g * g)))

private theorem actual_law : arena.{u}.Law orderActual := @kadison_real.{u}

private theorem rejected_law : ¬ arena.{u}.Law orderRejected := by
  intro h
  let A := PUnit.{u+1} →L[ℂ] PUnit.{u+1}
  exact h (A := A) 0 (Subsingleton.elim _ _) 0

def family : Registration arena.{u} (type_of% (@kadison_real.{u})) where
  actual := orderActual
  bridge := Iff.rfl
  variation := ⟨actual_law, orderRejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨orderRejected, ?_, rfl, rejected_law⟩
      exact fun j hji => (hji (show j = i from @Subsingleton.elim Unit _ j i)).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨ULift.{u} ℝ, inferInstance⟩, ⟨0⟩, ⟨1⟩, ?_⟩
    intro h
    have hh := congrFun h (ULift.up 0)
    change ((0 : ℝ) ≤ 0) = ((1 : ℝ) ≤ 0) at hh
    have := Eq.mp hh le_rfl
    norm_num at this

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@kadison_real.{u}) (Realization orderSignature.{u}) Unit Unit where
  unitName := `D5.S3.Quantum.Analysis.PositiveMomentRigidity.kadisonUnit
  realizationName := `Reg.D5.S3.Quantum.Analysis.PositiveMomentRigidity.Kadison.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize orderSignature
    (fun _ p x y => @LE.le p.1 p.2.toLE x y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.PositiveMomentRigidity
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Kadison

abbrev equalitySignature : Signature where
  Params := Type u
  State A := A
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ A := A → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def equalityActual : Realization equalitySignature.{u} :=
  realize equalitySignature (fun _ _ x y => x = y) (fun e => nomatch e)

def equalityRejected : Realization equalitySignature.{u} :=
  realize equalitySignature (fun _ _ _ _ => False) (fun e => nomatch e)

namespace Rigidity

def arena : Arena where
  signature := equalitySignature.{u}
  Law R := ∀ {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (Z : C(I, ℂ) →ₚ[ℂ] A) (_hunit : Z 1 = 1)
    (_hsquare : Z (coordinate * coordinate) = Z coordinate * Z coordinate),
    ∃ Φ : C(I, ℂ) →⋆ₐ[ℂ] A, (∀ f, Φ f = Z f) ∧
      R.readout () A (Φ coordinate) (Z coordinate)

private theorem actual_law : arena.{u}.Law equalityActual := @exists_starAlgHom_of_square.{u}

private theorem rejected_law : ¬ arena.{u}.Law equalityRejected := by
  intro h
  let A := PUnit.{u+1} →L[ℂ] PUnit.{u+1}
  obtain ⟨_, _, hf⟩ := h (A := A) 0 (Subsingleton.elim _ _) (Subsingleton.elim _ _)
  exact hf

def family : Registration arena.{u} (type_of% (@exists_starAlgHom_of_square.{u})) where
  actual := equalityActual
  bridge := Iff.rfl
  variation := ⟨actual_law, equalityRejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨equalityRejected, ?_, rfl, rejected_law⟩
      exact fun j hji => (hji (show j = i from @Subsingleton.elim Unit _ j i)).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    refine ⟨ULift.{u} Bool, ⟨false⟩, ⟨true⟩, ?_⟩
    intro h
    have hh := congrFun h (ULift.up false)
    simp [equalityActual, realize] at hh

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@exists_starAlgHom_of_square.{u}) (Realization equalitySignature.{u}) Unit Unit where
  unitName := `D5.S3.Quantum.Analysis.PositiveMomentRigidity.rigidityUnit
  realizationName := `Reg.D5.S3.Quantum.Analysis.PositiveMomentRigidity.Rigidity.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize equalitySignature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.PositiveMomentRigidity
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Rigidity

namespace ScalarHinges

def arena : Arena where
  signature := equalitySignature.{u}
  Law R := ∀ {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (Z : C(I, ℂ) →ₚ[ℂ] A) (_hunit : Z 1 = 1)
    (φ : A →ₚ[ℂ] ℂ) (_hfaithful : ∀ b : A, 0 ≤ b → φ b = 0 → b = 0)
    (_hhinge : ∀ s : ℝ, 0 < s → s < 1 →
      (φ (Z (hinge s))).re ≤ (φ ((Z coordinate - algebraMap ℝ A s)⁺)).re),
    R.readout () A (Z (coordinate * coordinate)) (Z coordinate * Z coordinate) ∧
      ∃ Φ : C(I, ℂ) →⋆ₐ[ℂ] A, (∀ f, Φ f = Z f) ∧ Φ coordinate = Z coordinate

private theorem actual_law : arena.{u}.Law equalityActual :=
  @exists_starAlgHom_of_scalar_hinges.{u}

private theorem rejected_law : ¬ arena.{u}.Law equalityRejected := by
  intro h
  let A := PUnit.{u+1} →L[ℂ] PUnit.{u+1}
  obtain ⟨hf, _⟩ := h (A := A) 0 (Subsingleton.elim _ _) 0
    (by intro b _ _; exact Subsingleton.elim _ _)
    (by intro s _ _; simp)
  exact hf

def family : Registration arena.{u} (type_of% (@exists_starAlgHom_of_scalar_hinges.{u})) where
  actual := equalityActual
  bridge := Iff.rfl
  variation := ⟨actual_law, equalityRejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨equalityRejected, ?_, rfl, rejected_law⟩
      exact fun j hji => (hji (show j = i from @Subsingleton.elim Unit _ j i)).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    refine ⟨ULift.{u} Bool, ⟨false⟩, ⟨true⟩, ?_⟩
    intro h
    have hh := congrFun h (ULift.up false)
    simp [equalityActual, realize] at hh

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@exists_starAlgHom_of_scalar_hinges.{u}) (Realization equalitySignature.{u}) Unit Unit where
  unitName := `D5.S3.Quantum.Analysis.PositiveMomentRigidity.scalarHingesUnit
  realizationName := `Reg.D5.S3.Quantum.Analysis.PositiveMomentRigidity.ScalarHinges.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize equalitySignature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.PositiveMomentRigidity
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ScalarHinges
end Reg.D5.S3.Quantum.Analysis.PositiveMomentRigidity
