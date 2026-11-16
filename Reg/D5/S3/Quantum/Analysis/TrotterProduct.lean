import D5.S3.Quantum.Analysis.TrotterProduct
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Full-telescope source audit with a dependent readout family. -/

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Filter NormedSpace
open scoped Topology
noncomputable section
universe u
namespace Reg.D5.S3.Quantum.Analysis.TrotterProduct

structure AlgebraScope where
  A : Type u
  [ring : NormedRing A]
  [algebra : NormedAlgebra ℝ A]
  [complete : CompleteSpace A]
  [one : NormOneClass A]
attribute [instance] AlgebraScope.ring AlgebraScope.algebra AlgebraScope.complete AlgebraScope.one

abbrev signature : Signature where
  Params := AlgebraScope.{u}
  State p := p.A
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Filter p.A
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ x => nhds x) (fun e => nomatch e)
def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => ⊥) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {A : Type u} [NormedRing A] [NormedAlgebra ℝ A]
    [CompleteSpace A] [NormOneClass A] (X Y : A),
    Tendsto (fun n : ℕ => (exp ((n : ℝ)⁻¹ • X) * exp ((n : ℝ)⁻¹ • Y)) ^ n)
      atTop (R.readout () ⟨A⟩ (exp (X + Y)))

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hb := h (A := ULift.{u} ℝ) 0 0
  have : (atTop : Filter ℕ) = ⊥ := tendsto_bot_right_iff.mp hb
  exact (Filter.NeBot.ne (inferInstance : NeBot (atTop : Filter ℕ))) this

def family : Registration arena.{u} (type_of% (@NormedSpace.trotter_product.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@NormedSpace.trotter_product.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(⟨ULift.{u} ℝ⟩ : AlgebraScope.{u}), 0, 1, ?_⟩
    intro h
    have he : (𝓝 (0 : ULift.{u} ℝ)) = 𝓝 1 := h
    exact zero_ne_one (nhds_injective he)

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@NormedSpace.trotter_product.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Analysis.TrotterProduct.unit
  realizationName := `Reg.D5.S3.Quantum.Analysis.TrotterProduct.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ _ x => nhds x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.TrotterProduct
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit
end Reg.D5.S3.Quantum.Analysis.TrotterProduct

namespace Reg.D5.S3.Quantum.Analysis.TrotterProduct.PowerDifference

structure RingScope where
  A : Type u
  [ring : NormedRing A]
  [one : NormOneClass A]
  power : ℕ
attribute [instance] RingScope.ring RingScope.one

abbrev signature : Signature where
  Params := RingScope.{u}
  State p := p.A × p.A
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p x => ‖x.1 ^ p.power - x.2 ^ p.power‖) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {A : Type u} [NormedRing A] [NormOneClass A] {S T : A} {C : ℝ},
    1 ≤ C → ‖S‖ ≤ C → ‖T‖ ≤ C → ∀ n : ℕ,
      R.readout () ⟨A, n⟩ (S, T) ≤ n * C ^ n * ‖S - T‖

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hb := h (A := ULift.{u} ℝ) (S := 0) (T := 0) (C := 1)
    le_rfl (by simp) (by simp) 0
  norm_num [rejected, realize] at hb

def family : Registration arena.{u}
    (type_of% (@NormedSpace.norm_pow_sub_pow_le_of_norm_le.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@NormedSpace.norm_pow_sub_pow_le_of_norm_le.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(⟨ULift.{u} ℝ, 1⟩ : RingScope.{u}), (0, 0), (1, 0), ?_⟩
    norm_num [actual, realize]

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@NormedSpace.norm_pow_sub_pow_le_of_norm_le.{u})
    (Realization signature.{u}) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Analysis.TrotterProduct.PowerDifference.unit
  realizationName := `Reg.D5.S3.Quantum.Analysis.TrotterProduct.PowerDifference.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p x => ‖x.1 ^ p.power - x.2 ^ p.power‖) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.TrotterProduct
    definition := none
    coordinates := #[0, 9]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit
end Reg.D5.S3.Quantum.Analysis.TrotterProduct.PowerDifference
