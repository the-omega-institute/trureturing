import LeanInformationAuditInterface.Contract.Registration
import D5.S0.Certificates.Algebra.BergmanNoncommutativeSemigroup
import Reg.Support.DependentFamily
import Mathlib.Algebra.Field.ULift

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S0.Certificates.Algebra
open BergmanQuestion15Refutation (Contracted delta product positivePower)
open BergmanQuestion23Refutation (mixedPower)
open BergmanCyclicGrading (positiveProduct)
open BergmanNoncommutativeSemigroup

namespace Reg.D5.S0.Certificates.Algebra.BergmanNoncommutativeSemigroup
noncomputable section
universe u
namespace RightZeroFamily
abbrev signature : Signature where
  Params := Unit
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℕ
  Anchor := Empty
  finiteAnchor := inferInstance
abbrev actual : Realization signature :=
  realize signature (fun _ _ n => Fintype.card (RightZero n)) (fun e => nomatch e)
abbrev rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law r := ∀ (F : Type u) [field : Field F] (n : ℕ) (hn : 2 ≤ n),
    r.readout () () n = 2 * n + 1 ∧
    (∃ a b : RightZero n, a * b ≠ b * a) ∧
    positivePower (generator n (by omega) false) (n - 1) ≠ 0 ∧
    positivePower (generator n (by omega) true) (n - 1) ≠ 0 ∧
    positivePower (generator n (by omega) false) (n - 1) ≠
      positivePower (generator n (by omega) true) (n - 1) ∧
    difference F n (by omega) ≠ 0 ∧
    difference F n (by omega) ∈ Submodule.span F
      (Set.range (fun b => delta F (RightZero n) (generator n (by omega) b))) ∧
    difference F n (by omega) * difference F n (by omega) = 0 ∧
    positivePower (difference F n (by omega)) (n - 1) = 0 ∧
    (∀ a : Fin (n + 1) → RightZero n, positiveProduct n a = 0) ∧
    mixedPower (product F (RightZero n)) ⊤ n = ⊥ ∧
    (∀ a : Fin (n + 1) → Contracted F (RightZero n), positiveProduct n a = 0) ∧
    positivePower (delta F (RightZero n) (generator n (by omega) false)) (n - 1) ≠ 0
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hh := (h (ULift.{u} ℚ) 2 (by decide)).1
  norm_num [rejected, realize] at hh
abbrev audit : Registration arena.{u}
    (type_of% @_root_.D5.S0.Certificates.Algebra.BergmanNoncommutativeSemigroup.right_zero_family) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S0.Certificates.Algebra.BergmanNoncommutativeSemigroup.right_zero_family,
    rejected, rejected_law⟩
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
    refine ⟨(), 2, 3, ?_⟩
    change Fintype.card (RightZero 2) ≠ Fintype.card (RightZero 3)
    rw [(right_zero_family ℚ 2 (by decide)).1, (right_zero_family ℚ 3 (by decide)).1]
    decide
noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S0.Certificates.Algebra.BergmanNoncommutativeSemigroup.right_zero_family)
    (type_of% actual) Unit Unit := {
  unitName := `D5.S0.Certificates.Algebra.BergmanNoncommutativeSemigroup.right_zero_family.__information_unit
  realizationName := `Reg.D5.S0.Certificates.Algebra.BergmanNoncommutativeSemigroup.RightZeroFamily.audit
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨audit⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S0.Certificates.Algebra.BergmanNoncommutativeSemigroup
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","body","fn","arg","fn","arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end RightZeroFamily
namespace ProductFamily
abbrev signature : Signature where
  Params := Unit
  State := fun _ => Fin 3
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ProductModel
  Anchor := Empty
  finiteAnchor := inferInstance
abbrev actual : Realization signature :=
  realize signature (fun _ _ i => positivePower
    (includeZero (BergmanCyclicSemigroup.generator 6 true i)) 5) (fun e => nomatch e)
abbrev rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law r := ∀ (F : Type u) [field : Field F],
    Fintype.card N = 4 ∧ Fintype.card ProductModel = 196 ∧
    (∃ a b : ProductModel, a * b ≠ b * a) ∧
    Function.Injective (embedding F) ∧
    (∀ s, embedding F (delta F _ s) = delta F ProductModel (s, 0)) ∧
    (∀ a : Fin 7 → ProductModel, positiveProduct 6 a = 0) ∧
    mixedPower (product F ProductModel) ⊤ 6 = ⊥ ∧
    (∀ a : Fin 7 → Contracted F ProductModel, positiveProduct 6 a = 0) ∧
    Function.Injective (r.readout () ()) ∧
    (∀ i : Fin 3, positivePower
      (includeZero (BergmanCyclicSemigroup.generator 6 true i)) 5 ≠ 0) ∧
    positivePower (delta F ProductModel
      (includeZero (BergmanCyclicSemigroup.generator 6 true 0))) 5 ≠ 0 ∧
    (∀ (ω : F), IsPrimitiveRoot ω 3 →
      ∃ u ∈ Submodule.span F (Set.range (fun i =>
          delta F (BergmanCyclicSemigroup.Model 6 true)
            (BergmanCyclicSemigroup.generator 6 true i))),
        u ≠ 0 ∧ positivePower u 5 = 0 ∧
        embedding F u ∈ Submodule.span F (Set.range (fun i =>
          delta F ProductModel (includeZero (BergmanCyclicSemigroup.generator 6 true i)))) ∧
        embedding F u ≠ 0 ∧ positivePower (embedding F u) 5 = 0)
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hi := (h (ULift.{u} ℚ)).2.2.2.2.2.2.2.2.1
  have hh := hi (a₁ := (0 : Fin 3)) (a₂ := 1) rfl
  norm_num at hh
abbrev audit : Registration arena.{u}
    (type_of% @_root_.D5.S0.Certificates.Algebra.BergmanNoncommutativeSemigroup.product_family) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S0.Certificates.Algebra.BergmanNoncommutativeSemigroup.product_family,
    rejected, rejected_law⟩
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
    refine ⟨(), 0, 1, ?_⟩
    have hi := (product_family ℚ).2.2.2.2.2.2.2.2.1
    exact fun h => (by decide : (0 : Fin 3) ≠ 1) (hi h)
noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S0.Certificates.Algebra.BergmanNoncommutativeSemigroup.product_family)
    (type_of% actual) Unit Unit := {
  unitName := `D5.S0.Certificates.Algebra.BergmanNoncommutativeSemigroup.product_family.__information_unit
  realizationName := `Reg.D5.S0.Certificates.Algebra.BergmanNoncommutativeSemigroup.ProductFamily.audit
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨audit⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S0.Certificates.Algebra.BergmanNoncommutativeSemigroup
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","arg","arg","arg","arg","arg","arg","arg","arg","fn","arg","arg","body"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end ProductFamily
end
end Reg.D5.S0.Certificates.Algebra.BergmanNoncommutativeSemigroup
