import D5.S1.Words.MBonacciParikhStarConverse
import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Words.MBonacciReversedPrefixFRS
import Reg.Support.DependentFamily

open _root_.D5.S1.Words.MBonacciSentinelDesubstitution
open _root_.D5.S1.Words.MBonacciReversedPrefixFRS
open _root_.D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs (factor)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S1.Words.MBonacciReversedPrefixFRS

abbrev Order := {m : ℕ // 2 ≤ m}
private def two : Order := ⟨2, by omega⟩

namespace reversed_prefix_fully_right_special

abbrev signature : Signature where
  Params := Σ p : Order, ℕ
  State p := ℕ → Fin p.1.val
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

private def observed (p : signature.Params) (x : signature.State p) : Prop :=
  let r := (factor x 0 p.2).reverse
  r.length = p.2 ∧ (∃ q : ℕ, factor x q r.length = r) ∧
    ∀ a : Fin p.1.val, ∃ q : ℕ, factor x q (r ++ [a]).length = r ++ [a]

def actual : Realization signature :=
  realize signature (fun _ p x => observed p x) (fun e _ => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e _ => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {m : ℕ} (hm : 2 ≤ m) (ell : ℕ),
      R.readout () ⟨⟨m, hm⟩, ell⟩ (word hm)

private theorem actual_law : arena.Law actual := by
  intro m hm ell
  simpa [actual, realize, observed, Occ, FRS] using
    (@_root_.D5.S1.Words.MBonacciReversedPrefixFRS.reversed_prefix_fully_right_special
      m hm ell)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro hh
  exact hh (hm := (by omega : 2 ≤ 2)) 0

private theorem constant_zero_rejected :
    ¬ observed ⟨two, 0⟩ (fun _ => zero two.property) := by
  intro hh
  obtain ⟨q, hq⟩ := hh.2.2 (⟨1, by decide⟩ : Fin 2)
  change factor (fun _ : ℕ => (0 : Fin 2)) q 1 = [1] at hq
  have hv := congrArg (fun s : List (Fin 2) => (s[0]?).map Fin.val) hq
  norm_num [factor] at hv

def family : Registration arena
    (type_of%
      (@_root_.D5.S1.Words.MBonacciReversedPrefixFRS.reversed_prefix_fully_right_special)) where
  actual := actual
  bridge := by
    rfl
  variation := ⟨actual_law, ⟨rejected, rejected_law⟩⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim (α := Unit) j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨two, 0⟩, word two.property, (fun _ => zero two.property), ?_⟩
    change observed ⟨two, 0⟩ (word two.property) ≠
      observed ⟨two, 0⟩ (fun _ => zero two.property)
    intro heq
    exact constant_zero_rejected (Eq.mp heq (actual_law (hm := two.property) 0))

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Words.MBonacciReversedPrefixFRS.reversed_prefix_fully_right_special)
    (type_of% actual) Unit Unit := {
  unitName := `D5.S1.Words.MBonacciReversedPrefixFRS.reversed_prefix_fully_right_special.__information_unit,
  realizationName := `Reg.D5.S1.Words.MBonacciReversedPrefixFRS.reversed_prefix_fully_right_special.family,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨family⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature actual.readout actual.anchor),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

end reversed_prefix_fully_right_special

end Reg.D5.S1.Words.MBonacciReversedPrefixFRS

open _root_.D5.S1.Words.MBonacciSentinelDesubstitution
open _root_.D5.S1.Words.MBonacciReversedPrefixFRS
open _root_.D5.S1.Words.MBonacciMinimumParikhDescent
open _root_.D5.S1.Words.MBonacciMinimumGreedy
open _root_.D5.S1.Words.MBonacciParikhStarConverse
open _root_.D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs (factor letterCount)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S1.Words.MBonacciReversedPrefixFRS

abbrev ConverseOrder := {m : ℕ // 2 ≤ m}
abbrev ConverseFive := {m : ℕ // 2 ≤ m ∧ 5 ≤ m}

namespace sentinel_frs

abbrev signature : Signature where
  Params := ConverseOrder × ℕ
  State p := ℕ → Fin p.1.val
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

private def observed (p : signature.Params) (x : signature.State p) : Prop :=
  ∀ a : Fin p.1.val, ∃ q : ℕ,
    factor x q (sentinelIter p.1.property p.2 ++ [a]).length =
      sentinelIter p.1.property p.2 ++ [a]

def actual : Realization signature :=
  realize signature (fun _ p x => observed p x) (fun e _ => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e _ => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {m : ℕ} (hm : 2 ≤ m) (t : ℕ),
      R.readout () ⟨⟨m, hm⟩, t⟩ (word hm)

private theorem actual_law : arena.Law actual := by
  intro m hm t
  exact _root_.D5.S1.Words.MBonacciReversedPrefixFRS.sentinel_frs hm t

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (by omega : 2 ≤ 2) 0

private theorem bad_observation : ¬ observed ⟨⟨2, by omega⟩, 0⟩ (fun _ => 1) := by
  intro h
  obtain ⟨q, hq⟩ := h 0
  simpa [sentinelIter, factor] using hq

def family : Registration arena (type_of% (@_root_.D5.S1.Words.MBonacciReversedPrefixFRS.sentinel_frs)) where
  actual := actual
  bridge := by rfl
  variation := ⟨actual_law, ⟨rejected, rejected_law⟩⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim (α := Unit) j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨⟨2, by omega⟩, 0⟩, (word (by omega : 2 ≤ 2)), (fun _ => 1), ?_⟩
    intro he
    exact bad_observation (Eq.mp he (by
      exact actual_law (by omega : 2 ≤ 2) 0))

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Words.MBonacciReversedPrefixFRS.sentinel_frs) (type_of% actual)
    (type_of% (@word)) Unit := {
  unitName := `D5.S1.Words.MBonacciReversedPrefixFRS.sentinel_frs.__information_unit,
  realizationName := `Reg.D5.S1.Words.MBonacciReversedPrefixFRS.sentinel_frs.family,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨family⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature actual.readout actual.anchor),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := some (@word),
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

end sentinel_frs

end Reg.D5.S1.Words.MBonacciReversedPrefixFRS

#print axioms Reg.D5.S1.Words.MBonacciReversedPrefixFRS.sentinel_frs.family
#print axioms Reg.D5.S1.Words.MBonacciReversedPrefixFRS.sentinel_frs.audit
