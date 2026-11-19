import LeanInformationAuditInterface.Contract.Registration
import D5.S0.Certificates.Algebra.BergmanCyclicGrading
import Reg.Support.DependentFamily
import Mathlib.Algebra.Field.ULift

/-! # Actual grading observations and interventions -/

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S0.Certificates.Algebra
open BergmanCyclicSemigroup BergmanCyclicGrading BergmanQuestion15Refutation
open BergmanQuestion23Refutation

namespace Reg.D5.S0.Certificates.Algebra.BergmanCyclicGrading
universe u
noncomputable section

namespace Nilpotency
abbrev Parameters := Σ _n : ℕ, Bool
abbrev signature : Signature where
  Params := Parameters
  State := fun p => Model p.1 p.2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ p => Model p.1 p.2
  Anchor := Empty
  finiteAnchor := inferInstance
abbrev actual : Realization signature :=
  realize signature (fun _ p s => positivePower s (p.1 - 1)) (fun e => nomatch e)
abbrev rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law r := ∀ (F : Type u) [_field : Field F] (n : ℕ) (_hn : 0 < n) (q : Bool),
    (∀ a : Fin (n + 1) → Model n q, positiveProduct n a = 0) ∧
    r.readout () ⟨n, q⟩ (generator n q 0) ≠ 0 ∧
    mixedPower (product F (Model n q)) ⊤ n = ⊥ ∧
    (∀ a : Fin (n + 1) → Contracted F (Model n q), positiveProduct n a = 0) ∧
    positivePower (delta F (Model n q) (generator n q 0)) (n - 1) ≠ 0
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  exact (h (ULift.{u} ℚ) 1 (by decide) false).2.1 rfl

abbrev audit : Registration arena.{u}
    (type_of% @_root_.D5.S0.Certificates.Algebra.BergmanCyclicGrading.nilpotency) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S0.Certificates.Algebra.BergmanCyclicGrading.nilpotency,
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
    refine ⟨⟨1, false⟩, Model.terminal 0, 0, ?_⟩
    intro h
    change (Model.terminal (0 : Fin 3) : Model 1 false) = 0 at h
    cases h

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S0.Certificates.Algebra.BergmanCyclicGrading.nilpotency)
    (type_of% actual) Unit Unit := {
  unitName := `D5.S0.Certificates.Algebra.BergmanCyclicGrading.nilpotency.__information_unit
  realizationName := `Reg.D5.S0.Certificates.Algebra.BergmanCyclicGrading.Nilpotency.audit
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
    owner := `D5.S0.Certificates.Algebra.BergmanCyclicGrading
    definition := none
    coordinates := #[2, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end Nilpotency

namespace Cardinalities
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
  realize signature (fun _ _ n => Fintype.card (Model n false)) (fun e => nomatch e)
abbrev rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law r := ∀ (n : ℕ) (_hn : 2 ≤ n),
    r.readout () () n = (n + 2).choose 3 + 3 ∧
    Fintype.card (Model n true) = 3 * n * (n - 1) / 2 + 4 ∧
    ∀ (F : Type u) [_field : Field F],
      Module.finrank F (Contracted F (Model n false)) = (n + 2).choose 3 + 2 ∧
      Module.finrank F (Contracted F (Model n true)) = 3 * n * (n - 1) / 2 + 3
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hh := (h 2 (by decide)).1
  norm_num [rejected, realize, Nat.choose] at hh

abbrev audit : Registration arena.{u}
    (type_of% @_root_.D5.S0.Certificates.Algebra.BergmanCyclicGrading.cardinalities) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S0.Certificates.Algebra.BergmanCyclicGrading.cardinalities,
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
    change Fintype.card (Model 2 false) ≠ Fintype.card (Model 3 false)
    rw [(cardinalities.{u} 2 (by decide)).1, (cardinalities.{u} 3 (by decide)).1]
    norm_num [Nat.choose]

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S0.Certificates.Algebra.BergmanCyclicGrading.cardinalities)
    (type_of% actual) Unit Unit := {
  unitName := `D5.S0.Certificates.Algebra.BergmanCyclicGrading.cardinalities.__information_unit
  realizationName := `Reg.D5.S0.Certificates.Algebra.BergmanCyclicGrading.Cardinalities.audit
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
    owner := `D5.S0.Certificates.Algebra.BergmanCyclicGrading
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end Cardinalities

namespace LowerCounts
abbrev signature : Signature where
  Params := ℕ
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℕ
  Anchor := Empty
  finiteAnchor := inferInstance
abbrev actual : Realization signature :=
  realize signature (fun _ n d =>
    Nat.card {s : Model n false // s ∈ generatorProducts n false (d - 1) ∧ s ≠ 0})
    (fun e => nomatch e)
abbrev rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law r := ∀ (n d : ℕ) (_hd : 0 < d) (_hdn : d < n),
    r.readout () n d = (d + 2).choose 2 ∧
    Nat.card {s : Model n true // s ∈ generatorProducts n true (d - 1) ∧ s ≠ 0} = 3 * d
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := (h 2 1 (by decide) (by decide)).1
  norm_num [rejected, realize, Nat.choose] at hh

abbrev audit : Registration arena
    (type_of% @_root_.D5.S0.Certificates.Algebra.BergmanCyclicGrading.lower_product_counts) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S0.Certificates.Algebra.BergmanCyclicGrading.lower_product_counts,
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
    refine ⟨4, 1, 2, ?_⟩
    change Nat.card {s : Model 4 false // s ∈ generatorProducts 4 false 0 ∧ s ≠ 0} ≠
      Nat.card {s : Model 4 false // s ∈ generatorProducts 4 false 1 ∧ s ≠ 0}
    rw [(lower_product_counts 4 1 (by decide) (by decide)).1,
      (lower_product_counts 4 2 (by decide) (by decide)).1]
    norm_num [Nat.choose]

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S0.Certificates.Algebra.BergmanCyclicGrading.lower_product_counts)
    (type_of% actual) Unit Unit := {
  unitName :=
    `D5.S0.Certificates.Algebra.BergmanCyclicGrading.lower_product_counts.__information_unit
  realizationName := `Reg.D5.S0.Certificates.Algebra.BergmanCyclicGrading.LowerCounts.audit
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
    owner := `D5.S0.Certificates.Algebra.BergmanCyclicGrading
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end LowerCounts

namespace ProductSets
abbrev Parameters := Σ _n : ℕ, Σ _q : Bool, ℕ
abbrev signature : Signature where
  Params := Parameters
  State := fun p => Sym (Fin 3) (p.2.2 + 1)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ p => Model p.1 p.2.1
  Anchor := Empty
  finiteAnchor := inferInstance
abbrev actual : Realization signature :=
  realize signature (fun _ p a => normal p.1 p.2.1 a.val) (fun e => nomatch e)
abbrev rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law r := ∀ (n : ℕ) (q : Bool) (k : ℕ),
    generatorProducts n q k = Set.range (r.readout () ⟨n, q, k⟩)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hm : generator 2 false 0 ∈ generatorProducts 2 false 0 := ⟨fun _ => 0, rfl⟩
  rw [h 2 false 0] at hm
  obtain ⟨a, ha⟩ := hm
  have hn : generator 2 false 0 ≠ 0 := by simp [generator, normal, survives]
  exact hn ha.symm

abbrev audit : Registration arena
    (type_of% @_root_.D5.S0.Certificates.Algebra.BergmanCyclicGrading.product_sets) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S0.Certificates.Algebra.BergmanCyclicGrading.product_sets,
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
    let a : Sym (Fin 3) 1 := ⟨{0}, by simp⟩
    let b : Sym (Fin 3) 1 := ⟨{1}, by simp⟩
    refine ⟨⟨2, false, 0⟩, a, b, ?_⟩
    intro h
    change normal 2 false a.val = normal 2 false b.val at h
    simp only [normal, a, b, Multiset.card_singleton, survives,
      true_or, and_self, Nat.ofNat_pos, Nat.one_lt_ofNat] at h
    have he := congrArg (fun x : Model 2 false => match x with
      | .lower a => a.val.val
      | _ => 0) h
    norm_num at he

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S0.Certificates.Algebra.BergmanCyclicGrading.product_sets)
    (type_of% actual) Unit Unit := {
  unitName := `D5.S0.Certificates.Algebra.BergmanCyclicGrading.product_sets.__information_unit
  realizationName := `Reg.D5.S0.Certificates.Algebra.BergmanCyclicGrading.ProductSets.audit
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
    owner := `D5.S0.Certificates.Algebra.BergmanCyclicGrading
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "arg", "arg", "body"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end ProductSets

namespace TerminalProducts
abbrev Parameters := Σ _n : ℕ, Bool
abbrev signature : Signature where
  Params := Parameters
  State := fun p => Model p.1 p.2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => Bool
  Anchor := Empty
  finiteAnchor := inferInstance
abbrev actual : Realization signature := by
  classical
  exact realize signature (fun _ _ s => decide (s ≠ 0)) (fun e => nomatch e)
abbrev rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law r := ∀ (n : ℕ) (_hn : 3 ≤ n) (q : Bool),
    {s : Model n q | s ∈ generatorProducts n q (n - 1) ∧ r.readout () ⟨n, q⟩ s = true} =
      Set.range (Model.terminal : Fin 3 → Model n q) ∧
    Nat.card {s : Model n q // s ∈ generatorProducts n q (n - 1) ∧ s ≠ 0} = 3 ∧
    (0 : Model n q) ∈ generatorProducts n q (n - 1)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := (h 3 (by decide) false).1
  have hm : (Model.terminal 0 : Model 3 false) ∈
      Set.range (Model.terminal : Fin 3 → Model 3 false) := ⟨0, rfl⟩
  rw [← he] at hm
  exact Bool.false_ne_true hm.2

abbrev audit : Registration arena
    (type_of% @_root_.D5.S0.Certificates.Algebra.BergmanCyclicGrading.terminal_products) where
  actual := actual
  bridge := by
    classical
    simp only [actual, realize, decide_eq_true_eq]
  variation := ⟨by
    intro n hn q
    simpa only [actual, realize, decide_eq_true_eq] using terminal_products n hn q,
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
    refine ⟨⟨3, false⟩, Model.terminal 0, 0, ?_⟩
    classical
    change decide ((Model.terminal 0 : Model 3 false) ≠ 0) ≠
      decide ((0 : Model 3 false) ≠ 0)
    simp [show (Model.terminal (0 : Fin 3) : Model 3 false) ≠ 0 by intro h; cases h]

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S0.Certificates.Algebra.BergmanCyclicGrading.terminal_products)
    (type_of% actual) Unit Unit := {
  unitName := `D5.S0.Certificates.Algebra.BergmanCyclicGrading.terminal_products.__information_unit
  realizationName := `Reg.D5.S0.Certificates.Algebra.BergmanCyclicGrading.TerminalProducts.audit
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
    owner := `D5.S0.Certificates.Algebra.BergmanCyclicGrading
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "fn", "arg", "arg", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end TerminalProducts

end
end Reg.D5.S0.Certificates.Algebra.BergmanCyclicGrading
