import D5.S3.Quantum.Algebra.Approximate.Compression
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

/-! The full Banach-algebra telescope and its actual Taylor readout. -/

set_option autoImplicit false
noncomputable section
universe u

namespace Reg.D5.S3.Quantum.Algebra.Approximate.Compression

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Algebra.Approximate.Compression

structure Scope where
  A : Type u
  [ring : NormedRing A]
  [algebra : NormedAlgebra ℝ A]
  [complete : CompleteSpace A]
  [normOne : NormOneClass A]

attribute [instance] Scope.ring Scope.algebra Scope.complete Scope.normOne

abbrev signature : Signature where
  Params := Scope.{u}
  State p := p.A
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.A
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ t => correction t) (fun e => nomatch e)

abbrev sourceScope : Prop := type_of% (@correction_idempotent.{u})

abbrev arena : Arena where
  signature := signature.{u}
  Law r := ∀ (p : Scope.{u}) (t : p.A), ‖t ^ 2 - 1‖ < 1 →
    r.readout () p t * r.readout () p t = r.readout () p t

theorem source_bridge : sourceScope.{u} ↔ arena.{u}.Law actual.{u} := by
  constructor
  · intro h p t ht
    exact h t ht
  · intro h A ring algebra complete normOne t ht
    exact h ⟨A⟩ t ht

theorem actual_law : arena.{u}.Law actual.{u} :=
  source_bridge.mp (@correction_idempotent.{u})

private theorem inverseSqrt_zero {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] :
    inverseSqrt (0 : A) = 1 := by
  unfold inverseSqrt
  rw [tsum_eq_single 0]
  · simp
  · intro n hn
    simp [zero_pow hn]

private theorem correction_one {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] :
    correction (1 : A) = 1 := by
  unfold correction
  simp only [one_pow, sub_self, inverseSqrt_zero, one_mul]
  module

private theorem correction_neg_one {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] :
    correction (-1 : A) = 0 := by
  simp [correction, inverseSqrt_zero]

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hc := h ⟨ULift.{u} ℝ⟩ 1 (by norm_num)
  have hd := congrArg ULift.down hc
  norm_num [rejected, realize] at hd

private theorem actual_dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨⟨ULift.{u} ℝ⟩, 1, -1, ?_⟩
  change correction (1 : ULift.{u} ℝ) ≠ correction (-1 : ULift.{u} ℝ)
  rw [correction_one, correction_neg_one]
  exact one_ne_zero

def family : Registration arena.{u} sourceScope.{u} where
  actual := actual
  bridge := source_bridge
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := actual_dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@correction_idempotent.{u}) (Realization signature.{u})
      (type_of% (@correction.{u})) Unit where
  unitName := `D5.S3.Quantum.Algebra.Approximate.Compression.correction_idempotent.information_unit
  realizationName := `Reg.D5.S3.Quantum.Algebra.Approximate.Compression.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ t => correction t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (@correction.{u})
  sourceSelection := some {
    owner := `D5.S3.Quantum.Algebra.Approximate.Compression
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 5
      functionOperand := true
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Quantum.Algebra.Approximate.Compression
