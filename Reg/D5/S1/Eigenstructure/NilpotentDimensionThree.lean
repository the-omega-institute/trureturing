import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Eigenstructure.NilpotentDimensionThree
import Mathlib.Algebra.Field.ULift
import Reg.Support.DependentFamily

/-! The witnessed initial zero in a nilpotent normal basis. -/

set_option autoImplicit false

namespace Reg.D5.S1.Eigenstructure.NilpotentDimensionThree

open _root_.D5.S1.Eigenstructure.NilpotentDimensionThree
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Module

universe u v

abbrev signature : Signature where
  Params := Σ K : Type u, Σ V : Type v, Σ k : Field K, Σ g : AddCommGroup V,
    letI := k
    letI := g
    Module K V
  State p := p.2.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.2.1 → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u,v} :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature.{u,v} :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u,v}
  Law R :=
    ∀ {K : Type u} {V : Type v} [k : Field K] [g : AddCommGroup V] [m : Module K V]
      [FiniteDimensional K V] (f : Module.End K V), finrank K V = 3 → f ≠ 0 → f ^ 3 = 0 →
      ∃ b : Basis (Fin 3) K V, R.readout () ⟨K, V, k, g, m⟩ (f (b 0)) 0 ∧ f (b 1) = b 0 ∧
        ((f ^ 2 = 0 ∧ f (b 2) = 0) ∨ (f ^ 2 ≠ 0 ∧ f (b 2) = b 1))

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  let K := ULift.{u} ℚ
  let W := Fin 3 → ℚ
  let e : ULift.{v} W ≃ₗ[K] W := ULift.moduleEquiv
  let q : W ≃ₗ[K] (Fin 3 → K) :=
    { toFun := fun x i => ULift.up (x i)
      invFun := fun x i => (x i).down
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let f : Module.End K (Fin 3 → K) :=
    (LinearMap.proj 1 : (Fin 3 → K) →ₗ[K] K).smulRight (Pi.single 0 1)
  have hf0 : f ≠ 0 := by
    intro h
    have hz := congrArg (fun g : Module.End K (Fin 3 → K) => g (Pi.single 1 1) 0) h
    simp [f, Pi.smul_apply] at hz
  have hf2 : f ^ 2 = 0 := by
    apply LinearMap.ext
    intro x
    funext i
    simp [pow_two, f, Module.End.mul_apply, Pi.smul_apply]
  have hf3 : f ^ 3 = 0 := by
    rw [pow_succ, hf2, zero_mul]
  let iso := e.trans q
  let g := iso.symm.conjRingEquiv f
  have hg0 : g ≠ 0 := by
    intro h
    apply hf0
    exact iso.symm.conjRingEquiv.injective (h.trans (map_zero _).symm)
  have hg3 : g ^ 3 = 0 := by
    change (iso.symm.conjRingEquiv f) ^ 3 = 0
    rw [← map_pow, hf3, map_zero]
  intro h
  let : FiniteDimensional K (ULift.{v} W) := iso.symm.finiteDimensional
  obtain ⟨_, bad, _⟩ := h g (by rw [LinearEquiv.finrank_eq iso]; simp) hg0 hg3
  exact bad

def family : Registration arena.{u,v} (type_of% (@exists_basis.{u,v})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_basis.{u,v}, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨⟨ULift.{u} ℚ, ULift.{v} ℚ, inferInstance, inferInstance, inferInstance⟩, ULift.up 0, ULift.up 1, ?_⟩
    intro h
    have hbad : (0 : ULift.{v} ℚ) = 1 :=
      Eq.mp (congrFun h 1).symm rfl
    exact zero_ne_one hbad

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@exists_basis.{u,v}) (Realization signature.{u,v}) Type Unit where
  unitName := `Reg.D5.S1.Eigenstructure.NilpotentDimensionThree.unit
  realizationName := `Reg.D5.S1.Eigenstructure.NilpotentDimensionThree.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Eigenstructure.NilpotentDimensionThree
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S1.Eigenstructure.NilpotentDimensionThree
