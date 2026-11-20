import LeanInformationAuditInterface.Contract.Registration
import D5.S3.HomologicalAlgebra.TotalUnimodularL1Repair
import Reg.Support.SingleDependentReadout

/-! Source-bound observations of signed doubling, integral cost, and modular support. -/

namespace Reg.D5.S3.HomologicalAlgebra.TotalUnimodularL1Repair

open _root_.D5.S3.HomologicalAlgebra.TotalUnimodularL1Repair
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Matrix

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
universe u v

private theorem single_role_sensitivity
    (arena : Arena) [Subsingleton arena.signature.Role] [IsEmpty arena.signature.Anchor]
    (actual rejected : Realization arena.signature) (hbad : ¬ arena.Law rejected) :
    Sensitivity arena actual := by
  constructor
  · intro role
    refine ⟨rejected, ?_, ?_, hbad⟩
    · intro other h
      exact (h (Subsingleton.elim _ _)).elim
    · funext anchor
      exact isEmptyElim anchor
  · intro anchor
    exact isEmptyElim anchor

private theorem zero_tu (M : Type u) (N : Type v) :
    (0 : Matrix M N ℤ).IsTotallyUnimodular := by
  rw [Matrix.isTotallyUnimodular_iff]
  intro k rows cols
  cases k with
  | zero => exact ⟨1, by simp⟩
  | succ k => exact ⟨0, by simp⟩

private abbrev realSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

private def realOrder : Realization realSignature :=
  realize realSignature (fun _ _ a b => a ≤ b) (fun e => nomatch e)

private def falseOrder : Realization realSignature :=
  realize realSignature (fun _ _ _ _ => False) (fun e => nomatch e)

private theorem real_order_dependence : ObservationalDependence realSignature realOrder := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hzero := congrFun h 0
  norm_num [realOrder, realize] at hzero

namespace SupportMembership

private abbrev signature : Signature where
  Params := Type v
  State K := K
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ K := K → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

private def actual : Realization signature.{v} :=
  realize signature (fun _ _ a b => a ≠ b) (fun e => nomatch e)

private def rejected : Realization signature.{v} :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

private abbrev arena.{rowLevel,columnLevel} : Arena where
  signature := signature.{columnLevel}
  Law R := ∀ {N : Type rowLevel} {K : Type columnLevel} [Zero K] [Fintype N] {w : N → K} {j : N},
    j ∈ nonzeroSupport w ↔ R.readout () K (w j) 0

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  let w : ULift.{u} Unit → ULift.{v} ℕ := fun _ => ⟨1⟩
  exact (@h _ _ _ _ w ⟨()⟩).mp (mem_nonzeroSupport.mpr (by decide))

private theorem dependence : ObservationalDependence signature.{v} actual := by
  intro role
  refine ⟨ULift.{v} ℕ, ⟨0⟩, ⟨1⟩, ?_⟩
  intro h
  have he := congrFun h (⟨0⟩ : ULift.{v} ℕ)
  change ((⟨0⟩ : ULift.{v} ℕ) ≠ ⟨0⟩) = ((⟨1⟩ : ULift.{v} ℕ) ≠ ⟨0⟩) at he
  exact (Eq.mpr he (by decide)) rfl

def family.{rowLevel,columnLevel} : Registration arena.{rowLevel,columnLevel} (type_of% (@mem_nonzeroSupport.{rowLevel,columnLevel})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@mem_nonzeroSupport.{rowLevel,columnLevel}, rejected, rejected_law⟩
  sensitivity := single_role_sensitivity arena actual rejected rejected_law
  dependence := dependence

def registration.{rowLevel,columnLevel} : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@mem_nonzeroSupport.{rowLevel,columnLevel}) (Realization signature.{columnLevel}) Unit Unit where
  unitName :=
    `D5.S3.HomologicalAlgebra.TotalUnimodularL1Repair.mem_nonzeroSupport.__information_unit
  realizationName :=
    `Reg.D5.S3.HomologicalAlgebra.TotalUnimodularL1Repair.SupportMembership.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{rowLevel,columnLevel}⟩
  objectArena := .source ⟨arena.{rowLevel,columnLevel}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{rowLevel,columnLevel} ⟨family.{rowLevel,columnLevel}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{columnLevel} (fun _ _ a b => a ≠ b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.HomologicalAlgebra.TotalUnimodularL1Repair
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end SupportMembership

namespace SignedColumns

private abbrev signature : Signature where
  Params := Σ (_ : Type u), Type v
  State p := Matrix p.1 p.2 ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Matrix p.1 (p.2 ⊕ p.2) ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

private def actual : Realization signature.{u,v} :=
  realize signature (fun _ _ A => Matrix.fromCols A (-A)) (fun e => nomatch e)

private def rejected : Realization signature.{u,v} :=
  realize signature (fun _ _ _ => fun _ _ => 2) (fun e => nomatch e)

private abbrev arena.{rowLevel,columnLevel} : Arena where
  signature := signature.{rowLevel,columnLevel}
  Law R := ∀ {M : Type rowLevel} {N : Type columnLevel} (A : Matrix M N ℤ) (_ : A.IsTotallyUnimodular),
    (R.readout () ⟨M, N⟩ A).IsTotallyUnimodular

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  have hbad := h 0 (zero_tu (ULift.{u} Unit) (ULift.{v} Unit))
  obtain ⟨s, hs⟩ := hbad.apply ⟨()⟩ (.inl ⟨()⟩)
  change (s : ℤ) = 2 at hs
  cases s <;> norm_num at hs

private theorem dependence : ObservationalDependence signature.{u,v} actual := by
  intro role
  refine ⟨⟨ULift.{u} Unit, ULift.{v} Unit⟩, 0, (fun _ _ => 1), ?_⟩
  intro h
  have he := congrFun (congrFun h ⟨()⟩) (.inl ⟨()⟩)
  exact zero_ne_one he

def family.{rowLevel,columnLevel} : Registration arena.{rowLevel,columnLevel} (type_of% (@fromCols_neg_isTotallyUnimodular.{rowLevel,columnLevel})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@fromCols_neg_isTotallyUnimodular.{rowLevel,columnLevel}, rejected, rejected_law⟩
  sensitivity := single_role_sensitivity arena actual rejected rejected_law
  dependence := dependence

def registration.{rowLevel,columnLevel} : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@fromCols_neg_isTotallyUnimodular.{rowLevel,columnLevel}) (Realization signature.{rowLevel,columnLevel}) Unit Unit where
  unitName :=
    `D5.S3.HomologicalAlgebra.TotalUnimodularL1Repair.fromCols_neg_isTotallyUnimodular.__information_unit
  realizationName :=
    `Reg.D5.S3.HomologicalAlgebra.TotalUnimodularL1Repair.SignedColumns.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{rowLevel,columnLevel}⟩
  objectArena := .source ⟨arena.{rowLevel,columnLevel}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{rowLevel,columnLevel} ⟨family.{rowLevel,columnLevel}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{rowLevel,columnLevel} (fun _ _ A => Matrix.fromCols A (-A)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.HomologicalAlgebra.TotalUnimodularL1Repair
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end SignedColumns

namespace IntegralCost

private abbrev signature := realSignature
private abbrev actual := realOrder
private abbrev rejected := falseOrder

private abbrev arena.{rowLevel,columnLevel} : Arena where
  signature := signature
  Law R := ∀ {M : Type rowLevel} {N : Type columnLevel} [Fintype M] [Fintype N]
    (A : Matrix M N ℤ) (_ : A.IsTotallyUnimodular) (b : M → ℤ) (x : N → ℝ),
    (A.map (Int.castRingHom ℝ) *ᵥ x = fun i => (b i : ℝ)) →
    ∃ z : N → ℤ, A *ᵥ z = b ∧ R.readout () () (∑ j, |(z j : ℝ)|) (∑ j, |x j|)

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  obtain ⟨_, _, hbad⟩ := h 0 (zero_tu (ULift.{u} Unit) (ULift.{v} Unit)) 0 0 (by ext; simp)
  exact hbad

def family.{rowLevel,columnLevel} : Registration arena.{rowLevel,columnLevel} (type_of% (@exists_integer_l1_repair.{rowLevel,columnLevel})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_integer_l1_repair.{rowLevel,columnLevel}, rejected, rejected_law⟩
  sensitivity := single_role_sensitivity arena actual rejected rejected_law
  dependence := real_order_dependence

def registration.{rowLevel,columnLevel} : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@exists_integer_l1_repair.{rowLevel,columnLevel}) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.HomologicalAlgebra.TotalUnimodularL1Repair.exists_integer_l1_repair.__information_unit
  realizationName :=
    `Reg.D5.S3.HomologicalAlgebra.TotalUnimodularL1Repair.IntegralCost.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{rowLevel,columnLevel}⟩
  objectArena := .source ⟨arena.{rowLevel,columnLevel}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{rowLevel,columnLevel} ⟨family.{rowLevel,columnLevel}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ a b => a ≤ b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.HomologicalAlgebra.TotalUnimodularL1Repair
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end IntegralCost

namespace SupportCost

private abbrev signature := realSignature
private abbrev actual := realOrder
private abbrev rejected := falseOrder

private abbrev arena.{columnLevel} : Arena where
  signature := signature
  Law R := ∀ {N : Type columnLevel} [Fintype N] (z : N → ℤ),
    R.readout () () ((nonzeroSupport z).card : ℝ) (∑ j, |(z j : ℝ)|)

private theorem rejected_law : ¬ arena.{v}.Law rejected := by
  intro h
  exact h (0 : ULift.{v} Unit → ℤ)

def family.{columnLevel} : Registration arena.{columnLevel} (type_of% (@support_card_le_sum_abs.{columnLevel})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@support_card_le_sum_abs.{columnLevel}, rejected, rejected_law⟩
  sensitivity := single_role_sensitivity arena actual rejected rejected_law
  dependence := real_order_dependence

def registration.{columnLevel} : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@support_card_le_sum_abs.{columnLevel}) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.HomologicalAlgebra.TotalUnimodularL1Repair.support_card_le_sum_abs.__information_unit
  realizationName :=
    `Reg.D5.S3.HomologicalAlgebra.TotalUnimodularL1Repair.SupportCost.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{columnLevel}⟩
  objectArena := .source ⟨arena.{columnLevel}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{columnLevel} ⟨family.{columnLevel}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ a b => a ≤ b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.HomologicalAlgebra.TotalUnimodularL1Repair
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end SupportCost

namespace ReducedSupport

private abbrev signature : Signature where
  Params := Type v
  State N := Finset N
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ N := Finset N → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

private def actual : Realization signature.{v} :=
  realize signature (fun _ _ a b => a ⊆ b) (fun e => nomatch e)

private def rejected : Realization signature.{v} :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

private abbrev arena.{rowLevel,columnLevel} : Arena where
  signature := signature.{columnLevel}
  Law R := ∀ {M : Type rowLevel} {N : Type columnLevel} [Fintype N] (A : Matrix M N ℤ) (b : M → ℤ)
    (z : N → ℤ), A *ᵥ z = b → ∀ n : ℕ,
    (A.map (Int.castRingHom (ZMod n)) *ᵥ (fun j => (z j : ZMod n)) = fun i => (b i : ZMod n)) ∧
      R.readout () N (nonzeroSupport (fun j => (z j : ZMod n))) (nonzeroSupport z)

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  exact (h (0 : Matrix (ULift.{u} Unit) (ULift.{v} Unit) ℤ) 0 0 (by ext; simp) 2).2

private theorem dependence : ObservationalDependence signature.{v} actual := by
  intro role
  refine ⟨ULift.{v} Unit, ∅, {⟨()⟩}, ?_⟩
  intro h
  have he := congrFun h (∅ : Finset (ULift.{v} Unit))
  change ((∅ : Finset (ULift.{v} Unit)) ⊆ ∅) = (({⟨()⟩} : Finset (ULift.{v} Unit)) ⊆ ∅) at he
  have hb := Eq.mp he (Finset.Subset.refl _)
  simpa using hb (Finset.mem_singleton_self (⟨()⟩ : ULift.{v} Unit))

def family.{rowLevel,columnLevel} : Registration arena.{rowLevel,columnLevel} (type_of% (@reduce_integer_solution.{rowLevel,columnLevel})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@reduce_integer_solution.{rowLevel,columnLevel}, rejected, rejected_law⟩
  sensitivity := single_role_sensitivity arena actual rejected rejected_law
  dependence := dependence

def registration.{rowLevel,columnLevel} : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@reduce_integer_solution.{rowLevel,columnLevel}) (Realization signature.{columnLevel}) Unit Unit where
  unitName :=
    `D5.S3.HomologicalAlgebra.TotalUnimodularL1Repair.reduce_integer_solution.__information_unit
  realizationName :=
    `Reg.D5.S3.HomologicalAlgebra.TotalUnimodularL1Repair.ReducedSupport.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{rowLevel,columnLevel}⟩
  objectArena := .source ⟨arena.{rowLevel,columnLevel}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{rowLevel,columnLevel} ⟨family.{rowLevel,columnLevel}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{columnLevel} (fun _ _ a b => a ⊆ b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.HomologicalAlgebra.TotalUnimodularL1Repair
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg",
        "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ReducedSupport

namespace ModularCost

private abbrev signature := realSignature
private abbrev actual := realOrder
private abbrev rejected := falseOrder

private abbrev arena.{rowLevel,columnLevel} : Arena where
  signature := signature
  Law R := ∀ {M : Type rowLevel} {N : Type columnLevel} [Fintype M] [Fintype N]
    (A : Matrix M N ℤ) (_ : A.IsTotallyUnimodular) (b : M → ℤ) (x : N → ℝ),
    (A.map (Int.castRingHom ℝ) *ᵥ x = fun i => (b i : ℝ)) → ∀ n : ℕ,
    ∃ y : N → ZMod n, (A.map (Int.castRingHom (ZMod n)) *ᵥ y = fun i => (b i : ZMod n)) ∧
      R.readout () () ((nonzeroSupport y).card : ℝ) (∑ j, |x j|)

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  obtain ⟨_, _, hbad⟩ := h 0 (zero_tu (ULift.{u} Unit) (ULift.{v} Unit)) 0 0 (by ext; simp) 2
  exact hbad

def family.{rowLevel,columnLevel} : Registration arena.{rowLevel,columnLevel} (type_of% (@exists_zmod_repair_with_support_bound.{rowLevel,columnLevel})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_zmod_repair_with_support_bound.{rowLevel,columnLevel}, rejected, rejected_law⟩
  sensitivity := single_role_sensitivity arena actual rejected rejected_law
  dependence := real_order_dependence

def registration.{rowLevel,columnLevel} : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@exists_zmod_repair_with_support_bound.{rowLevel,columnLevel}) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.HomologicalAlgebra.TotalUnimodularL1Repair.exists_zmod_repair_with_support_bound.__information_unit
  realizationName :=
    `Reg.D5.S3.HomologicalAlgebra.TotalUnimodularL1Repair.ModularCost.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{rowLevel,columnLevel}⟩
  objectArena := .source ⟨arena.{rowLevel,columnLevel}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{rowLevel,columnLevel} ⟨family.{rowLevel,columnLevel}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ a b => a ≤ b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.HomologicalAlgebra.TotalUnimodularL1Repair
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "arg", "body", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ModularCost

end

end Reg.D5.S3.HomologicalAlgebra.TotalUnimodularL1Repair
