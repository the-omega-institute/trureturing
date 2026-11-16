import LeanInformationAuditInterface.Contract.Registration
import D5.S0.Certificates.Algebra.BergmanCyclicSemigroup
import Reg.Support.DependentFamily

/-! # The generated presentation and its normal forms -/

open LeanInformationAudit
open _root_.D5.S0.Certificates.Algebra
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S0.Certificates.Algebra.BergmanCyclicSemigroup

namespace Reg.D5.S0.Certificates.Algebra.BergmanCyclicSemigroup

noncomputable section

abbrev Parameters := Σ _n : ℕ, Σ _q : Bool, Word

abbrev signature : Signature where
  Params := Parameters
  State := fun _ => Word
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ p => Model p.1 p.2.1
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev actual : Realization signature :=
  realize signature (fun _ p t => reduce p.1 p.2.1 t) (fun e => nomatch e)

abbrev rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ (n : ℕ) (hn : 0 < n) (q : Bool) (s t : Word),
    presentation n hn q s t ↔ reduce n q s = r.readout () ⟨n, q, s⟩ t

private abbrev witness : Word := .monomial ⟨{0}, by simp⟩

private theorem witness_nonzero : reduce 2 false witness ≠ 0 := by
  simp [reduce, witness, normal, survives]

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have H := (h 2 (by decide) false witness witness).mp (ConGen.Rel.refl _)
  exact witness_nonzero H

abbrev completenessAudit : Registration arena
    (type_of% @_root_.D5.S0.Certificates.Algebra.BergmanCyclicSemigroup.normal_form_complete) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S0.Certificates.Algebra.BergmanCyclicSemigroup.normal_form_complete,
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
    refine ⟨⟨2, false, witness⟩, witness, 0, ?_⟩
    exact witness_nonzero

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S0.Certificates.Algebra.BergmanCyclicSemigroup.normal_form_complete)
    (type_of% actual) Unit Unit := {
  unitName := `D5.S0.Certificates.Algebra.BergmanCyclicSemigroup.normal_form_complete.__information_unit
  realizationName := `Reg.D5.S0.Certificates.Algebra.BergmanCyclicSemigroup.completenessAudit
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨completenessAudit⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S0.Certificates.Algebra.BergmanCyclicSemigroup
    definition := none
    coordinates := #[0, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }


namespace NormalMul
abbrev signature : Signature where
  Params := Σ _n : ℕ, Σ _q : Bool, Exponent
  State := fun _ => Exponent
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ p => Model p.1 p.2.1
  Anchor := Empty
  finiteAnchor := inferInstance
abbrev actual : Realization signature :=
  realize signature (fun _ p b => normal p.1 p.2.1 (p.2.2 + b)) (fun e => nomatch e)
abbrev rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law r := ∀ {n : ℕ} {q : Bool} (a b : Exponent) (_ha : 0 < a.card) (_hb : 0 < b.card), normal n q a * normal n q b = r.readout () ⟨n, q, a⟩ b
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have H := h ({0} : Exponent) {0} (by simp) (by simp) (n := 2) (q := false)
  change normal 2 false {0} * normal 2 false {0} = 0 at H
  rw [normal_mul _ _ (by simp) (by simp)] at H
  have hn : normal 2 false ({0} + {0} : Exponent) ≠ 0 := by decide
  exact hn H
abbrev audit : Registration arena (type_of% @_root_.D5.S0.Certificates.Algebra.BergmanCyclicSemigroup.normal_mul) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S0.Certificates.Algebra.BergmanCyclicSemigroup.normal_mul, rejected, rejected_law⟩
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
    refine ⟨⟨2, false, {0}⟩, {0}, {0, 0}, ?_⟩
    change normal 2 false ({0} + {0} : Exponent) ≠ normal 2 false ({0} + {0, 0} : Exponent)
    decide
noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S0.Certificates.Algebra.BergmanCyclicSemigroup.normal_mul)
    (type_of% actual) Unit Unit := {
  unitName := `D5.S0.Certificates.Algebra.BergmanCyclicSemigroup.normal_mul.__information_unit
  realizationName := `Reg.D5.S0.Certificates.Algebra.BergmanCyclicSemigroup.NormalMul.audit
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
    owner := `D5.S0.Certificates.Algebra.BergmanCyclicSemigroup
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end NormalMul

namespace GeneratorPower
abbrev signature : Signature where
  Params := Σ _n : ℕ, Σ _q : Bool, Fin 3
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ p => Model p.1 p.2.1
  Anchor := Empty
  finiteAnchor := inferInstance
abbrev actual : Realization signature :=
  realize signature (fun _ p k => normal p.1 p.2.1 (Multiset.replicate (k + 1) p.2.2)) (fun e => nomatch e)
abbrev rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law r := ∀ (n : ℕ) (q : Bool) (i : Fin 3) (k : ℕ), BergmanQuestion15Refutation.positivePower (generator n q i) k = r.readout () ⟨n, q, i⟩ k
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have H := h 1 false 0 0
  change BergmanQuestion15Refutation.positivePower (generator 1 false 0) 0 = 0 at H
  have hn : BergmanQuestion15Refutation.positivePower (generator 1 false 0) 0 ≠ 0 := by decide
  exact hn H
abbrev audit : Registration arena (type_of% @_root_.D5.S0.Certificates.Algebra.BergmanCyclicSemigroup.generator_power) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S0.Certificates.Algebra.BergmanCyclicSemigroup.generator_power, rejected, rejected_law⟩
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
    refine ⟨⟨1, false, 0⟩, 0, 1, ?_⟩
    change normal 1 false (Multiset.replicate (0 + 1) (0 : Fin 3)) ≠
      normal 1 false (Multiset.replicate (1 + 1) (0 : Fin 3))
    decide
noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S0.Certificates.Algebra.BergmanCyclicSemigroup.generator_power)
    (type_of% actual) Unit Unit := {
  unitName := `D5.S0.Certificates.Algebra.BergmanCyclicSemigroup.generator_power.__information_unit
  realizationName := `Reg.D5.S0.Certificates.Algebra.BergmanCyclicSemigroup.GeneratorPower.audit
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
    owner := `D5.S0.Certificates.Algebra.BergmanCyclicSemigroup
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end GeneratorPower

namespace TerminalPowers
abbrev signature : Signature where
  Params := Σ _n : ℕ, Bool
  State := fun _ => Fin 3
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ p => Model p.1 p.2
  Anchor := Empty
  finiteAnchor := inferInstance
abbrev actual : Realization signature :=
  realize signature (fun _ p i => BergmanQuestion15Refutation.positivePower (generator p.1 p.2 i) (p.1 - 1)) (fun e => nomatch e)
abbrev rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law r := ∀ (n : ℕ) (_hn : 0 < n) (q : Bool) (i : Fin 3), r.readout () ⟨n, q⟩ i = .terminal i
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have H := h 1 (by decide) false 0
  change (0 : Model 1 false) = .terminal 0 at H
  cases H
abbrev audit : Registration arena (type_of% @_root_.D5.S0.Certificates.Algebra.BergmanCyclicSemigroup.terminal_powers) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S0.Certificates.Algebra.BergmanCyclicSemigroup.terminal_powers, rejected, rejected_law⟩
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
    refine ⟨⟨1, false⟩, 0, 1, ?_⟩
    change BergmanQuestion15Refutation.positivePower (generator 1 false 0) 0 ≠
      BergmanQuestion15Refutation.positivePower (generator 1 false 1) 0
    decide
noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S0.Certificates.Algebra.BergmanCyclicSemigroup.terminal_powers)
    (type_of% actual) Unit Unit := {
  unitName := `D5.S0.Certificates.Algebra.BergmanCyclicSemigroup.terminal_powers.__information_unit
  realizationName := `Reg.D5.S0.Certificates.Algebra.BergmanCyclicSemigroup.TerminalPowers.audit
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
    owner := `D5.S0.Certificates.Algebra.BergmanCyclicSemigroup
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end TerminalPowers

namespace NormalSurjective
abbrev signature : Signature where
  Params := Σ _n : ℕ, Bool
  State := fun _ => Exponent
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ p => Model p.1 p.2
  Anchor := Empty
  finiteAnchor := inferInstance
abbrev actual : Realization signature :=
  realize signature (fun _ p a => normal p.1 p.2 a) (fun e => nomatch e)
abbrev rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law r := ∀ (n : ℕ) (_hn : 0 < n) (q : Bool) (s : Model n q), ∃ a : Exponent, 0 < a.card ∧ r.readout () ⟨n, q⟩ a = s
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨a, _, H⟩ := h 1 (by decide) false (.terminal 0)
  change (0 : Model 1 false) = .terminal 0 at H
  cases H
abbrev audit : Registration arena (type_of% @_root_.D5.S0.Certificates.Algebra.BergmanCyclicSemigroup.normal_surjective) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S0.Certificates.Algebra.BergmanCyclicSemigroup.normal_surjective, rejected, rejected_law⟩
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
    refine ⟨⟨1, false⟩, {0}, 0, ?_⟩
    change normal 1 false ({0} : Exponent) ≠ normal 1 false (0 : Exponent)
    decide
noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S0.Certificates.Algebra.BergmanCyclicSemigroup.normal_surjective)
    (type_of% actual) Unit Unit := {
  unitName := `D5.S0.Certificates.Algebra.BergmanCyclicSemigroup.normal_surjective.__information_unit
  realizationName := `Reg.D5.S0.Certificates.Algebra.BergmanCyclicSemigroup.NormalSurjective.audit
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
    owner := `D5.S0.Certificates.Algebra.BergmanCyclicSemigroup
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "body", "arg", "fn", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end NormalSurjective

namespace Generated
abbrev signature : Signature where
  Params := Σ _n : ℕ, Bool
  State := fun p => Set (Model p.1 p.2)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ p => Subsemigroup (Model p.1 p.2)
  Anchor := Empty
  finiteAnchor := inferInstance
abbrev actual : Realization signature :=
  realize signature (fun _ _ s => Subsemigroup.closure s) (fun e => nomatch e)
abbrev rejected : Realization signature :=
  realize signature (fun _ _ _ => ⊥) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law r := ∀ (n : ℕ) (_hn : 0 < n) (q : Bool), r.readout () ⟨n, q⟩ (Set.range (generator n q)) = ⊤
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have H := h 1 (by decide) false
  have hm : (Model.terminal (0 : Fin 3) : Model 1 false) ∈ (⊥ : Subsemigroup (Model 1 false)) := by
    rw [show (⊥ : Subsemigroup (Model 1 false)) = ⊤ from H]
    trivial
  exact hm
abbrev audit : Registration arena (type_of% @_root_.D5.S0.Certificates.Algebra.BergmanCyclicSemigroup.generated) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S0.Certificates.Algebra.BergmanCyclicSemigroup.generated, rejected, rejected_law⟩
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
    refine ⟨⟨1, false⟩, ∅, Set.univ, ?_⟩
    change Subsemigroup.closure (∅ : Set (Model 1 false)) ≠ Subsemigroup.closure Set.univ
    simp only [Subsemigroup.closure_empty, Subsemigroup.closure_univ]
    intro h
    have hm : (Model.terminal (0 : Fin 3) : Model 1 false) ∈ (⊥ : Subsemigroup (Model 1 false)) := by
      rw [h]
      trivial
    exact hm
noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S0.Certificates.Algebra.BergmanCyclicSemigroup.generated)
    (type_of% actual) Unit Unit := {
  unitName := `D5.S0.Certificates.Algebra.BergmanCyclicSemigroup.generated.__information_unit
  realizationName := `Reg.D5.S0.Certificates.Algebra.BergmanCyclicSemigroup.Generated.audit
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
    owner := `D5.S0.Certificates.Algebra.BergmanCyclicSemigroup
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Generated

namespace QuotientMul
abbrev signature : Signature where
  Params := Σ n : ℕ, Model n false
  State := fun p => Model p.1 false
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ p => Model p.1 true
  Anchor := Empty
  finiteAnchor := inferInstance
abbrev actual : Realization signature :=
  realize signature (fun _ p t => quotient (p.2 * t)) (fun e => nomatch e)
abbrev rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law r := ∀ {n : ℕ} (s t : Model n false), r.readout () ⟨n, s⟩ t = quotient s * quotient t
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have H := h (n := 2) (generator 2 false 0) (generator 2 false 0)
  change (0 : Model 2 true) = quotient (generator 2 false 0) * quotient (generator 2 false 0) at H
  have hn : quotient (generator 2 false 0) * quotient (generator 2 false 0) ≠ 0 := by decide
  exact hn H.symm
abbrev audit : Registration arena (type_of% @_root_.D5.S0.Certificates.Algebra.BergmanCyclicSemigroup.quotient_mul) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S0.Certificates.Algebra.BergmanCyclicSemigroup.quotient_mul, rejected, rejected_law⟩
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
    refine ⟨⟨2, generator 2 false 0⟩, generator 2 false 0, 0, ?_⟩
    change quotient (generator 2 false 0 * generator 2 false 0) ≠ quotient (generator 2 false 0 * 0)
    decide
noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S0.Certificates.Algebra.BergmanCyclicSemigroup.quotient_mul)
    (type_of% actual) Unit Unit := {
  unitName := `D5.S0.Certificates.Algebra.BergmanCyclicSemigroup.quotient_mul.__information_unit
  realizationName := `Reg.D5.S0.Certificates.Algebra.BergmanCyclicSemigroup.QuotientMul.audit
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
    owner := `D5.S0.Certificates.Algebra.BergmanCyclicSemigroup
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end QuotientMul

namespace QuotientFibers
abbrev signature : Signature where
  Params := ℕ
  State := fun n => Model n false
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ n => Model n true
  Anchor := Empty
  finiteAnchor := inferInstance
abbrev actual : Realization signature :=
  realize signature (fun _ _ t => quotient t) (fun e => nomatch e)
abbrev rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law r := ∀ {n : ℕ} (s t : Model n false), quotient s = r.readout () n t ↔ s = t ∨ (s = 0 ∨ ∃ a, s = .lower a ∧ mixed a.val.val) ∧ (t = 0 ∨ ∃ a, t = .lower a ∧ mixed a.val.val)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have H := (h (n := 1) (.terminal 0) (.terminal 0)).mpr (Or.inl rfl)
  change (Model.terminal (0 : Fin 3) : Model 1 true) = 0 at H
  cases H
abbrev audit : Registration arena (type_of% @_root_.D5.S0.Certificates.Algebra.BergmanCyclicSemigroup.quotient_fibers) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S0.Certificates.Algebra.BergmanCyclicSemigroup.quotient_fibers, rejected, rejected_law⟩
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
    refine ⟨1, Model.terminal 0, Model.terminal 1, ?_⟩
    change (Model.terminal (0 : Fin 3) : Model 1 true) ≠ .terminal 1
    decide
noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S0.Certificates.Algebra.BergmanCyclicSemigroup.quotient_fibers)
    (type_of% actual) Unit Unit := {
  unitName := `D5.S0.Certificates.Algebra.BergmanCyclicSemigroup.quotient_fibers.__information_unit
  realizationName := `Reg.D5.S0.Certificates.Algebra.BergmanCyclicSemigroup.QuotientFibers.audit
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
    owner := `D5.S0.Certificates.Algebra.BergmanCyclicSemigroup
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end QuotientFibers

namespace QuotientSurjective
abbrev signature : Signature where
  Params := ℕ
  State := fun n => Model n false
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ n => Model n true
  Anchor := Empty
  finiteAnchor := inferInstance
abbrev actual : Realization signature :=
  realize signature (fun _ _ s => quotient s) (fun e => nomatch e)
abbrev rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law r := ∀ (n : ℕ), Function.Surjective (r.readout () n)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨s, H⟩ := h 1 (.terminal 0)
  change (0 : Model 1 true) = .terminal 0 at H
  cases H
abbrev audit : Registration arena (type_of% @_root_.D5.S0.Certificates.Algebra.BergmanCyclicSemigroup.quotient_surjective) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S0.Certificates.Algebra.BergmanCyclicSemigroup.quotient_surjective, rejected, rejected_law⟩
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
    refine ⟨1, Model.terminal 0, Model.terminal 1, ?_⟩
    change (Model.terminal (0 : Fin 3) : Model 1 true) ≠ .terminal 1
    decide
noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S0.Certificates.Algebra.BergmanCyclicSemigroup.quotient_surjective)
    (type_of% actual) Unit Unit := {
  unitName := `D5.S0.Certificates.Algebra.BergmanCyclicSemigroup.quotient_surjective.__information_unit
  realizationName := `Reg.D5.S0.Certificates.Algebra.BergmanCyclicSemigroup.QuotientSurjective.audit
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
    owner := `D5.S0.Certificates.Algebra.BergmanCyclicSemigroup
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end QuotientSurjective

end

end Reg.D5.S0.Certificates.Algebra.BergmanCyclicSemigroup
