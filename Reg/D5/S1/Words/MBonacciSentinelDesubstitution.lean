import D5.S1.Words.MBonacciParikhStarConverse
import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Words.MBonacciSentinelDesubstitution
import Reg.Support.DependentFamily
import Reg.Support.MBonacciSentinelWordOperations

open _root_.D5.S1.Words.MBonacciSentinelDesubstitution
open _root_.D5.S1.Words.RankOneMorphismIterationBound (subst image)
open _root_.D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs (factor)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S1.Words.MBonacciSentinelDesubstitution

abbrev Order := {m : ℕ // 2 ≤ m}
private def two : Order := ⟨2, by first | (unfold Occ; decide) | decide⟩

namespace zero_iff_unique_boundary

abbrev signature : Signature where
  Params := Order
  State p := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Fin p.val
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p q => word p.property q) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ p _ => zero p.property) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {m : ℕ} (hm : 2 ≤ m) (q : ℕ),
      R.readout () ⟨m, hm⟩ q = zero hm ↔ ∃! i, q = boundary hm i

private theorem rejected_law : ¬ arena.Law rejected := by
  intro hh
  have h := (hh (by first | (unfold Occ; decide) | decide : 2 ≤ 2) 1).mp rfl
  have hz := (zero_iff_unique_boundary (by first | (unfold Occ; decide) | decide : 2 ≤ 2) 1).mpr h
  exact (by first | (unfold Occ; decide) | decide : word (by first | (unfold Occ; decide) | decide : 2 ≤ 2) 1 ≠ zero (by first | (unfold Occ; decide) | decide : 2 ≤ 2)) hz

def family : Registration arena (type_of% (@_root_.D5.S1.Words.MBonacciSentinelDesubstitution.zero_iff_unique_boundary)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S1.Words.MBonacciSentinelDesubstitution.zero_iff_unique_boundary, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim (α := Unit) j i)).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    refine ⟨two, 0, 1, ?_⟩
    change word (by first | (unfold Occ; decide) | decide : 2 ≤ 2) 0 ≠ word (by first | (unfold Occ; decide) | decide : 2 ≤ 2) 1
    decide

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Words.MBonacciSentinelDesubstitution.zero_iff_unique_boundary)
    (type_of% actual) Unit Unit := {
  unitName := `D5.S1.Words.MBonacciSentinelDesubstitution.zero_iff_unique_boundary.__information_unit,
  realizationName := `Reg.D5.S1.Words.MBonacciSentinelDesubstitution.zero_iff_unique_boundary.family,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨family⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature actual.readout actual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Words.MBonacciSentinelDesubstitution, definition := none,
    coordinates := #[0, 1],
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "fn", "arg"], stateBinder := 2,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

end zero_iff_unique_boundary

namespace sentinel_occurrence_iff

abbrev signature : Signature where
  Params := Σ p : Order, List (Fin p.val)
  State p := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p q => Occ p.1.property (T p.1.property p.2) q) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ p _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {m : ℕ} (hm : 2 ≤ m) (s : List (Fin m)) (q : ℕ),
      R.readout () ⟨⟨m, hm⟩, s⟩ q ↔ ∃ i, q = boundary hm i ∧ Occ hm s i

private theorem rejected_law : ¬ arena.Law rejected := by
  intro hh
  have h := hh (by first | (unfold Occ; decide) | decide : 2 ≤ 2) [] 0
  exact h.mpr ⟨0, by first | (unfold Occ; decide) | decide, by first | (unfold Occ; decide) | decide⟩

def family : Registration arena (type_of% (@_root_.D5.S1.Words.MBonacciSentinelDesubstitution.sentinel_occurrence_iff)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S1.Words.MBonacciSentinelDesubstitution.sentinel_occurrence_iff, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim (α := Unit) j i)).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨two, []⟩, 0, 1, ?_⟩
    change Occ (by first | (unfold Occ; decide) | decide : 2 ≤ 2) [zero (by first | (unfold Occ; decide) | decide : 2 ≤ 2)] 0 ≠
    Occ (by first | (unfold Occ; decide) | decide : 2 ≤ 2) [zero (by first | (unfold Occ; decide) | decide : 2 ≤ 2)] 1
    intro he
    exact (by first | (unfold Occ; decide) | decide : ¬ Occ (by first | (unfold Occ; decide) | decide : 2 ≤ 2) [zero (by first | (unfold Occ; decide) | decide : 2 ≤ 2)] 1)
      (Eq.mp he (by first | (unfold Occ; decide) | decide))

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Words.MBonacciSentinelDesubstitution.sentinel_occurrence_iff)
    (type_of% actual) Unit Unit := {
  unitName := `D5.S1.Words.MBonacciSentinelDesubstitution.sentinel_occurrence_iff.__information_unit,
  realizationName := `Reg.D5.S1.Words.MBonacciSentinelDesubstitution.sentinel_occurrence_iff.family,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨family⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature actual.readout actual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Words.MBonacciSentinelDesubstitution, definition := none,
    coordinates := #[0, 1, 2],
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"], stateBinder := 3,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

end sentinel_occurrence_iff

namespace right_extension_occurrence_iff

abbrev signature : Signature where
  Params := Σ p : Order, List (Fin p.val) × Fin p.val
  State p := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p q => Occ p.1.property (T p.1.property p.2.1 ++ [rot p.1.property p.2.2]) q) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ p _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {m : ℕ} (hm : 2 ≤ m) (s : List (Fin m)) (b : Fin m) (q : ℕ),
      R.readout () ⟨⟨m, hm⟩, s, b⟩ q ↔
        ∃ i, q = boundary hm i ∧ Occ hm (s ++ [b]) i

private theorem rejected_law : ¬ arena.Law rejected := by
  intro hh
  have h := hh (by first | (unfold Occ; decide) | decide : 2 ≤ 2) [] ⟨0, by first | (unfold Occ; decide) | decide⟩ 0
  exact h.mpr ⟨0, by first | (unfold Occ; decide) | decide, by first | (unfold Occ; decide) | decide⟩

def family : Registration arena (type_of% (@_root_.D5.S1.Words.MBonacciSentinelDesubstitution.right_extension_occurrence_iff)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S1.Words.MBonacciSentinelDesubstitution.right_extension_occurrence_iff, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim (α := Unit) j i)).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨two, [], ⟨0, by first | (unfold Occ; decide) | decide⟩⟩, 0, 1, ?_⟩
    change Occ (by first | (unfold Occ; decide) | decide : 2 ≤ 2) [⟨0, by first | (unfold Occ; decide) | decide⟩, ⟨1, by first | (unfold Occ; decide) | decide⟩] 0 ≠
    Occ (by first | (unfold Occ; decide) | decide : 2 ≤ 2) [⟨0, by first | (unfold Occ; decide) | decide⟩, ⟨1, by first | (unfold Occ; decide) | decide⟩] 1
    intro he
    exact (by first | (unfold Occ; decide) | decide : ¬ Occ (by first | (unfold Occ; decide) | decide : 2 ≤ 2) [⟨0, by first | (unfold Occ; decide) | decide⟩, ⟨1, by first | (unfold Occ; decide) | decide⟩] 1)
      (Eq.mp he (by first | (unfold Occ; decide) | decide))

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Words.MBonacciSentinelDesubstitution.right_extension_occurrence_iff)
    (type_of% actual) Unit Unit := {
  unitName := `D5.S1.Words.MBonacciSentinelDesubstitution.right_extension_occurrence_iff.__information_unit,
  realizationName := `Reg.D5.S1.Words.MBonacciSentinelDesubstitution.right_extension_occurrence_iff.family,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨family⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature actual.readout actual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Words.MBonacciSentinelDesubstitution, definition := none,
    coordinates := #[0, 1, 2, 3],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"], stateBinder := 4,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

end right_extension_occurrence_iff

namespace common_unique_preimage

abbrev signature : Signature where
  Params := Order
  State p := List (Fin p.val)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := List (Fin p.val)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p q => T p.property q) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ p _ => []) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {m : ℕ} (hm : 2 ≤ m) (r : List (Fin m)), r ≠ [] →
      (∃ q, Occ hm r q) → r.head? = some (zero hm) → r.getLast? = some (zero hm) →
      ∃! s, r = R.readout () ⟨m, hm⟩ s ∧ s.length < r.length

private theorem rejected_law : ¬ arena.Law rejected := by
  intro hh
  obtain ⟨s, hs, _⟩ := hh (by first | (unfold Occ; decide) | decide : 2 ≤ 2) [zero (by first | (unfold Occ; decide) | decide : 2 ≤ 2)]
    (by simp) ⟨0, by first | (unfold Occ; decide) | decide⟩ rfl rfl
  simpa [rejected, realize] using hs.1

def family : Registration arena (type_of% (@_root_.D5.S1.Words.MBonacciSentinelDesubstitution.common_unique_preimage)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S1.Words.MBonacciSentinelDesubstitution.common_unique_preimage, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim (α := Unit) j i)).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    refine ⟨two, [], [zero two.property], ?_⟩
    change T (by first | (unfold Occ; decide) | decide : 2 ≤ 2) [] ≠ T (by first | (unfold Occ; decide) | decide : 2 ≤ 2) [zero (by first | (unfold Occ; decide) | decide : 2 ≤ 2)]
    decide

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Words.MBonacciSentinelDesubstitution.common_unique_preimage)
    (type_of% actual) Unit Unit := {
  unitName := `D5.S1.Words.MBonacciSentinelDesubstitution.common_unique_preimage.__information_unit,
  realizationName := `Reg.D5.S1.Words.MBonacciSentinelDesubstitution.common_unique_preimage.family,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨family⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature actual.readout actual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Words.MBonacciSentinelDesubstitution, definition := none,
    coordinates := #[0, 1],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg", "body", "fn", "arg", "arg"], stateBinder := 7,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

end common_unique_preimage

namespace fully_right_special_descent

abbrev signature : Signature where
  Params := Order
  State p := List (Fin p.val)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := List (Fin p.val)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p q => T p.property q) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ p _ => []) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {m : ℕ} (hm : 2 ≤ m) (r : List (Fin m)), r ≠ [] →
      r.head? = some (zero hm) → FRS hm r →
      ∃! s, r = R.readout () ⟨m, hm⟩ s ∧ s.length < r.length ∧ FRS hm s ∧
        (∀ q, Occ hm r q ↔ ∃ i, q = boundary hm i ∧ Occ hm s i) ∧
        (∀ b q, Occ hm (r ++ [rot hm b]) q ↔
          ∃ i, q = boundary hm i ∧ Occ hm (s ++ [b]) i)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro hh
  have hf : FRS (by first | (unfold Occ; decide) | decide : 2 ≤ 2) [zero (by first | (unfold Occ; decide) | decide : 2 ≤ 2)] := by
    intro a
    fin_cases a
    · exact ⟨2, by first | (unfold Occ; decide) | decide⟩
    · exact ⟨0, by first | (unfold Occ; decide) | decide⟩
  obtain ⟨s, hs, _⟩ := hh (by first | (unfold Occ; decide) | decide : 2 ≤ 2) [zero (by first | (unfold Occ; decide) | decide : 2 ≤ 2)]
    (by simp) rfl hf
  simpa [rejected, realize] using hs.1

def family : Registration arena (type_of% (@_root_.D5.S1.Words.MBonacciSentinelDesubstitution.fully_right_special_descent)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S1.Words.MBonacciSentinelDesubstitution.fully_right_special_descent, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim (α := Unit) j i)).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    refine ⟨two, [], [zero two.property], ?_⟩
    change T (by first | (unfold Occ; decide) | decide : 2 ≤ 2) [] ≠ T (by first | (unfold Occ; decide) | decide : 2 ≤ 2) [zero (by first | (unfold Occ; decide) | decide : 2 ≤ 2)]
    decide

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Words.MBonacciSentinelDesubstitution.fully_right_special_descent)
    (type_of% actual) Unit Unit := {
  unitName := `D5.S1.Words.MBonacciSentinelDesubstitution.fully_right_special_descent.__information_unit,
  realizationName := `Reg.D5.S1.Words.MBonacciSentinelDesubstitution.fully_right_special_descent.family,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨family⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature actual.readout actual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Words.MBonacciSentinelDesubstitution, definition := none,
    coordinates := #[0, 1],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "body", "fn", "arg", "arg"], stateBinder := 6,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

end fully_right_special_descent

namespace actual_word_laws

abbrev signature : Signature where
  Params := Order
  State p := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := List (Fin p.val)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p q => factor (word p.property) 0 (image (phi p.property) q (zero p.property)).length) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ p _ => []) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {m : ℕ} (hm : 2 ≤ m),
      (∀ k, R.readout () ⟨m, hm⟩ k = image (phi hm) k (zero hm)) ∧
      StrictMono (boundary hm) ∧ boundary hm 0 = 0 ∧
      (∀ i, boundary hm i = ∑ h ∈ Finset.range i, (phi hm (word hm h)).length) ∧
      (∀ i, factor (word hm) (boundary hm i) (phi hm (word hm i)).length = phi hm (word hm i)) ∧
      (∀ q, word hm q ≠ zero hm → word hm (q + 1) = zero hm) ∧
      (∀ a, (rot hm a).val = (a.val + 1) % m)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro hh
  have h := (hh (by first | (unfold Occ; decide) | decide : 2 ≤ 2)).1 0
  simpa [rejected, realize, image] using h

def family : Registration arena (type_of% (@_root_.D5.S1.Words.MBonacciSentinelDesubstitution.actual_word_laws)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S1.Words.MBonacciSentinelDesubstitution.actual_word_laws, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim (α := Unit) j i)).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    refine ⟨two, 0, 1, ?_⟩
    change factor (word (by first | (unfold Occ; decide) | decide : 2 ≤ 2)) 0 1 ≠ factor (word (by first | (unfold Occ; decide) | decide : 2 ≤ 2)) 0 2
    decide

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Words.MBonacciSentinelDesubstitution.actual_word_laws)
    (type_of% actual) Unit Unit := {
  unitName := `D5.S1.Words.MBonacciSentinelDesubstitution.actual_word_laws.__information_unit,
  realizationName := `Reg.D5.S1.Words.MBonacciSentinelDesubstitution.actual_word_laws.family,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨family⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature actual.readout actual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Words.MBonacciSentinelDesubstitution, definition := none,
    coordinates := #[0, 1],
    readouts := #[{
      path := #["body", "body", "fn", "arg", "body", "fn", "arg"], stateBinder := 2,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

end actual_word_laws

namespace occurrence_transport

abbrev signature : Signature where
  Params := Order
  State p := List (Fin p.val)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := List (Fin p.val)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p q => subst (phi p.property) q) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ p _ => [⟨1, by have := p.property; omega⟩]) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {m : ℕ} (hm : 2 ≤ m) (s : List (Fin m)) (i : ℕ), Occ hm s i →
      Occ hm (R.readout () ⟨m, hm⟩ s) (boundary hm i) ∧
      Occ hm (T hm s) (boundary hm i) ∧
      (s ≠ [] → Occ hm (subst (phi hm) s).tail (boundary hm i + 1))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro hh
  have h := (hh (by first | (unfold Occ; decide) | decide : 2 ≤ 2) [zero (by first | (unfold Occ; decide) | decide : 2 ≤ 2)] 0 (by first | (unfold Occ; decide) | decide)).1
  exact (by first | (unfold Occ; decide) | decide : ¬ Occ (by first | (unfold Occ; decide) | decide : 2 ≤ 2) [⟨1, by first | (unfold Occ; decide) | decide⟩] 0) h

def family : Registration arena (type_of% (@_root_.D5.S1.Words.MBonacciSentinelDesubstitution.occurrence_transport)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S1.Words.MBonacciSentinelDesubstitution.occurrence_transport, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim (α := Unit) j i)).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    refine ⟨two, [], [zero two.property], ?_⟩
    change subst (phi (by first | (unfold Occ; decide) | decide : 2 ≤ 2)) [] ≠ subst (phi (by first | (unfold Occ; decide) | decide : 2 ≤ 2)) [zero (by first | (unfold Occ; decide) | decide : 2 ≤ 2)]
    decide

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Words.MBonacciSentinelDesubstitution.occurrence_transport)
    (type_of% actual) Unit Unit := {
  unitName := `D5.S1.Words.MBonacciSentinelDesubstitution.occurrence_transport.__information_unit,
  realizationName := `Reg.D5.S1.Words.MBonacciSentinelDesubstitution.occurrence_transport.family,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨family⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature actual.readout actual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Words.MBonacciSentinelDesubstitution, definition := none,
    coordinates := #[0, 1],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "fn", "arg"], stateBinder := 2,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

end occurrence_transport

namespace iterate_prefix

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Output _ _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ k => k) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ k => k + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {m : ℕ} (hm : 2 ≤ m) {k t : ℕ} (_h : k ≤ t),
    image (phi hm) (R.readout () () k) (zero hm) <+: image (phi hm) t (zero hm)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (by decide : 2 ≤ 2) (k := 0) (t := 0) (by decide)
  exact (by decide : ¬ image (phi (by decide : 2 ≤ 2)) 1 (zero (by decide : 2 ≤ 2)) <+:
    image (phi (by decide : 2 ≤ 2)) 0 (zero (by decide : 2 ≤ 2))) hh

def family : Registration arena (type_of% (@_root_.D5.S1.Words.MBonacciSentinelDesubstitution.iterate_prefix)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S1.Words.MBonacciSentinelDesubstitution.iterate_prefix, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim (α := Unit) j i)).elim
    · intro e; exact nomatch e
  dependence := by
    intro _
    refine ⟨(), 0, 1, ?_⟩
    change (0 : ℕ) ≠ 1
    decide

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Words.MBonacciSentinelDesubstitution.iterate_prefix) (type_of% actual) Unit Unit := {
  unitName := `D5.S1.Words.MBonacciSentinelDesubstitution.iterate_prefix.__information_unit,
  realizationName := `Reg.D5.S1.Words.MBonacciSentinelDesubstitution.iterate_prefix.family,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨family⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature actual.readout actual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Words.MBonacciSentinelDesubstitution, definition := none,
    coordinates := #[],
    readouts := #[{
      path := #[
        "body",
        "body",
        "body",
        "body",
        "body",
        "fn",
        "arg",
        "fn",
        "arg"],
      stateBinder := 2,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

end iterate_prefix

namespace iterate_growth

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Output _ _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ k => k) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {m : ℕ} (hm : 2 ≤ m) (k : ℕ),
    k + 1 ≤ (image (phi hm) (R.readout () () k) (zero hm)).length

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (by decide : 2 ≤ 2) 1
  exact (by decide : ¬ (1 + 1 ≤ (image (phi (by decide : 2 ≤ 2)) 0
    (zero (by decide : 2 ≤ 2))).length)) hh

def family : Registration arena (type_of% (@_root_.D5.S1.Words.MBonacciSentinelDesubstitution.iterate_growth)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S1.Words.MBonacciSentinelDesubstitution.iterate_growth, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim (α := Unit) j i)).elim
    · intro e; exact nomatch e
  dependence := by
    intro _
    refine ⟨(), 0, 1, ?_⟩
    change (0 : ℕ) ≠ 1
    decide

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Words.MBonacciSentinelDesubstitution.iterate_growth) (type_of% actual) Unit Unit := {
  unitName := `D5.S1.Words.MBonacciSentinelDesubstitution.iterate_growth.__information_unit,
  realizationName := `Reg.D5.S1.Words.MBonacciSentinelDesubstitution.iterate_growth.family,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨family⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature actual.readout actual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Words.MBonacciSentinelDesubstitution, definition := none,
    coordinates := #[],
    readouts := #[{
      path := #[
        "body",
        "body",
        "body",
        "arg",
        "arg",
        "fn",
        "arg"],
      stateBinder := 2,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

end iterate_growth

namespace word_eq_iterate

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Output _ _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ n => n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {m : ℕ} (hm : 2 ≤ m) (k n : ℕ)
    (hn : n < (image (phi hm) k (zero hm)).length),
    word hm (R.readout () () n) = (image (phi hm) k (zero hm))[n]

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (by decide : 2 ≤ 2) 1 1 (by decide)
  exact (by decide : ¬ word (by decide : 2 ≤ 2) 0 =
    (image (phi (by decide : 2 ≤ 2)) 1 (zero (by decide : 2 ≤ 2)))[1]) hh

def family : Registration arena (type_of% (@_root_.D5.S1.Words.MBonacciSentinelDesubstitution.word_eq_iterate)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S1.Words.MBonacciSentinelDesubstitution.word_eq_iterate, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim (α := Unit) j i)).elim
    · intro e; exact nomatch e
  dependence := by
    intro _
    refine ⟨(), 0, 1, ?_⟩
    change (0 : ℕ) ≠ 1
    decide

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Words.MBonacciSentinelDesubstitution.word_eq_iterate) (type_of% actual) Unit Unit := {
  unitName := `D5.S1.Words.MBonacciSentinelDesubstitution.word_eq_iterate.__information_unit,
  realizationName := `Reg.D5.S1.Words.MBonacciSentinelDesubstitution.word_eq_iterate.family,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨family⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature actual.readout actual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Words.MBonacciSentinelDesubstitution, definition := none,
    coordinates := #[],
    readouts := #[{
      path := #[
        "body",
        "body",
        "body",
        "body",
        "body",
        "fn",
        "arg",
        "arg"],
      stateBinder := 3,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

end word_eq_iterate

namespace factor_get

abbrev signature : Signature where
  Params := Σ m : ℕ, Σ _x : ℕ → Fin m, ℕ
  State _ := ℕ
  Output _ p := Fin p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p j => p.2.1 (p.2.2 + j)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ p _ => p.2.1 p.2.2) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {m : ℕ} (x : ℕ → Fin m) (i n j : ℕ) (hj : j < n),
    (factor x i n)[j]'(by simpa [factor] using hj) = R.readout () ⟨m, x, i⟩ j

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let x : ℕ → Fin 2 := fun q => ⟨q % 2, Nat.mod_lt _ (by decide)⟩
  have hh := h x 0 2 1 (by decide)
  have he : (1 : Fin 2) = 0 := hh
  exact (by decide : (1 : Fin 2) ≠ 0) he

def family : Registration arena (type_of% (@_root_.D5.S1.Words.MBonacciSentinelDesubstitution.factor_get)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S1.Words.MBonacciSentinelDesubstitution.factor_get, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim (α := Unit) j i)).elim
    · intro e; exact nomatch e
  dependence := by
    intro _
    let x : ℕ → Fin 2 := fun q => ⟨q % 2, Nat.mod_lt _ (by decide)⟩
    refine ⟨⟨2, x, 0⟩, 0, 1, ?_⟩
    change x 0 ≠ x 1
    decide

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Words.MBonacciSentinelDesubstitution.factor_get) (type_of% actual) Unit Unit := {
  unitName := `D5.S1.Words.MBonacciSentinelDesubstitution.factor_get.__information_unit,
  realizationName := `Reg.D5.S1.Words.MBonacciSentinelDesubstitution.factor_get.family,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨family⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature actual.readout actual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Words.MBonacciSentinelDesubstitution, definition := none,
    coordinates := #[0, 1, 2],
    readouts := #[{
      path := #[
        "body",
        "body",
        "body",
        "body",
        "body",
        "body",
        "arg"],
      stateBinder := 4,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

end factor_get

end Reg.D5.S1.Words.MBonacciSentinelDesubstitution
