import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Eigenstructure.BinaryCubicRepeatedRoot
import Mathlib.Algebra.Module.ULift
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.Ring
import Reg.Support.DependentFamily

/-! The fixed first basis vector in a binary cubic with a repeated root. -/

set_option autoImplicit false

namespace Reg.D5.S1.Eigenstructure.BinaryCubicRepeatedRoot

open _root_.D5.S1.Eigenstructure.BinaryCubicRepeatedRoot
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Module Polynomial

universe v

abbrev signature : Signature where
  Params := Σ V : Type v, Σ g : AddCommGroup V,
    letI := g
    Module (ZMod 2) V
  State p := p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.1 → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{v} :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature.{v} :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{v}
  Law R :=
    ∀ {V : Type v} [g : AddCommGroup V] [m : Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
      (f : Module.End (ZMod 2) V), finrank (ZMod 2) V = 3 → f.charpoly = X ^ 3 + X →
      ∃ b : Basis (Fin 3) (ZMod 2) V, R.readout () ⟨V, g, m⟩ (f (b 0)) (b 0) ∧ f (b 2) = 0 ∧
        ((f ^ 2 = f ∧ f (b 1) = b 1) ∨ (f ^ 2 ≠ f ∧ f (b 1) = b 0 + b 1))

private theorem rejected_law : ¬ arena.{v}.Law rejected := by
  let W := Fin 3 → ZMod 2
  let e : ULift.{v} W ≃ₗ[ZMod 2] W := ULift.moduleEquiv
  let : FiniteDimensional (ZMod 2) (ULift.{v} W) := e.symm.finiteDimensional
  let A : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1, 0, 0; 0, 1, 0; 0, 0, 0]
  have hA : A.charpoly = X ^ 3 + X := by
    rw [Matrix.charpoly, Matrix.det_fin_three]
    simp [A, ZModModule.neg_eq_self]
    ring_nf
    have htwo : (2 : (ZMod 2)[X]) = 0 := CharP.cast_eq_zero _ 2
    simp [htwo, add_comm]
  intro h
  obtain ⟨_, bad, _⟩ := h (e.symm.conj A.toLin') (by rw [e.finrank_eq]; simp [W])
    (by rwa [e.symm.charpoly_conj, Matrix.charpoly_toLin'])
  exact bad

def family : Registration arena.{v} (type_of% (@exists_basis.{v})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_basis.{v}, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨⟨ULift.{v} (ZMod 2), inferInstance, inferInstance⟩, ULift.up 0, ULift.up 1, ?_⟩
    intro h
    have hbad : (0 : ULift.{v} (ZMod 2)) = 1 :=
      Eq.mp (congrFun h 1).symm rfl
    exact zero_ne_one hbad

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@exists_basis.{v}) (Realization signature.{v}) Type Unit where
  unitName := `Reg.D5.S1.Eigenstructure.BinaryCubicRepeatedRoot.unit
  realizationName := `Reg.D5.S1.Eigenstructure.BinaryCubicRepeatedRoot.family
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
    owner := `D5.S1.Eigenstructure.BinaryCubicRepeatedRoot
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S1.Eigenstructure.BinaryCubicRepeatedRoot
