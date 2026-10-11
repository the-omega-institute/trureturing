import D5.S1.Words.MBonacciParikhStarConverse
import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Words.MBonacciSentinelDesubstitution
import Reg.Support.DependentFamily

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

end Reg.D5.S1.Words.MBonacciSentinelDesubstitution

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

namespace Reg.D5.S1.Words.MBonacciSentinelDesubstitution

abbrev ConverseOrder := {m : ℕ // 2 ≤ m}
abbrev ConverseFive := {m : ℕ // 2 ≤ m ∧ 5 ≤ m}

namespace boundary_window

abbrev signature : Signature where
  Params := ConverseOrder × ℕ
  State p := ℕ → ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

private def observed (p : signature.Params) (x : signature.State p) : Prop :=
  ∃ i : ℕ, x i ≤ p.2 ∧ p.2 < x (i + 1)

def actual : Realization signature :=
  realize signature (fun _ p x => observed p x) (fun e _ => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e _ => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {m : ℕ} (hm : 2 ≤ m) (q : ℕ),
      R.readout () ⟨⟨m, hm⟩, q⟩ (boundary hm)

private theorem actual_law : arena.Law actual := by
  intro m hm q
  exact _root_.D5.S1.Words.MBonacciSentinelDesubstitution.boundary_window hm q

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (by omega : 2 ≤ 2) 0

private theorem bad_observation : ¬ observed ⟨⟨2, by omega⟩, 0⟩ (fun _ => 0) := by
  simp [observed]

def family : Registration arena (type_of% (@_root_.D5.S1.Words.MBonacciSentinelDesubstitution.boundary_window)) where
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
    refine ⟨⟨⟨2, by omega⟩, 0⟩, (boundary (by omega : 2 ≤ 2)), (fun _ => 0), ?_⟩
    intro he
    exact bad_observation (Eq.mp he (by
      exact actual_law (by omega : 2 ≤ 2) 0))

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Words.MBonacciSentinelDesubstitution.boundary_window) (type_of% actual)
    (type_of% (@boundary)) Unit := {
  unitName := `D5.S1.Words.MBonacciSentinelDesubstitution.boundary_window.__information_unit,
  realizationName := `Reg.D5.S1.Words.MBonacciSentinelDesubstitution.boundary_window.family,
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
  escapeFrom := some (@boundary),
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

end boundary_window

namespace t_head

abbrev signature : Signature where
  Params := Σ p : ConverseOrder, List (Fin p.val)
  State p := List (Fin p.1.val)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

private def observed (p : signature.Params) (x : signature.State p) : Prop :=
  ∃ v : List (Fin p.1.val), x = zero p.1.property :: v

def actual : Realization signature :=
  realize signature (fun _ p x => observed p x) (fun e _ => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e _ => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {m : ℕ} (hm : 2 ≤ m) (s : List (Fin m)),
      R.readout () ⟨⟨m, hm⟩, s⟩ (T hm s)

private theorem actual_law : arena.Law actual := by
  intro m hm s
  exact _root_.D5.S1.Words.MBonacciSentinelDesubstitution.t_head hm s

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (by omega : 2 ≤ 2) []

private theorem bad_observation : ¬ observed ⟨⟨2, by omega⟩, []⟩ ([]) := by
  simp [observed]

def family : Registration arena (type_of% (@_root_.D5.S1.Words.MBonacciSentinelDesubstitution.t_head)) where
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
    refine ⟨⟨⟨2, by omega⟩, []⟩, (T (by omega : 2 ≤ 2) []), ([]), ?_⟩
    intro he
    exact bad_observation (Eq.mp he (by
      exact actual_law (by omega : 2 ≤ 2) []))

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Words.MBonacciSentinelDesubstitution.t_head) (type_of% actual)
    (type_of% (@T)) Unit := {
  unitName := `D5.S1.Words.MBonacciSentinelDesubstitution.t_head.__information_unit,
  realizationName := `Reg.D5.S1.Words.MBonacciSentinelDesubstitution.t_head.family,
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
  escapeFrom := some (@T),
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

end t_head

namespace occ_cons

abbrev signature : Signature where
  Params := Σ p : ConverseOrder, Fin p.val × (List (Fin p.val) × ℕ)
  State p := (List (Fin p.1.val) → ℕ → Prop) × (ℕ → Fin p.1.val)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

private def observed (p : signature.Params) (x : signature.State p) : Prop :=
  x.1 (p.2.1 :: p.2.2.1) p.2.2.2 ↔
    x.2 p.2.2.2 = p.2.1 ∧ x.1 p.2.2.1 (p.2.2.2 + 1)

def actual : Realization signature :=
  realize signature (fun _ p x => observed p x) (fun e _ => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e _ => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {m : ℕ} (hm : 2 ≤ m) (a : Fin m) (s : List (Fin m)) (q : ℕ),
      R.readout () ⟨⟨m, hm⟩, a, s, q⟩ (Occ hm, word hm)

private theorem actual_law : arena.Law actual := by
  intro m hm a s q
  exact _root_.D5.S1.Words.MBonacciSentinelDesubstitution.occ_cons hm a s q

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (by omega : 2 ≤ 2) 0 [] 0

private theorem bad_observation : ¬ observed ⟨⟨2, by omega⟩, 0, [], 0⟩ ((fun _ _ => True, fun _ => 1)) := by
  simp [observed]

def family : Registration arena (type_of% (@_root_.D5.S1.Words.MBonacciSentinelDesubstitution.occ_cons)) where
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
    refine ⟨⟨⟨2, by omega⟩, 0, [], 0⟩, ((Occ (by omega : 2 ≤ 2), word (by omega : 2 ≤ 2))), ((fun _ _ => True, fun _ => 1)), ?_⟩
    intro he
    exact bad_observation (Eq.mp he (by
      exact actual_law (by omega : 2 ≤ 2) 0 [] 0))

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Words.MBonacciSentinelDesubstitution.occ_cons) (type_of% actual)
    (type_of% (@Occ)) Unit := {
  unitName := `D5.S1.Words.MBonacciSentinelDesubstitution.occ_cons.__information_unit,
  realizationName := `Reg.D5.S1.Words.MBonacciSentinelDesubstitution.occ_cons.family,
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
  escapeFrom := some (@Occ),
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

end occ_cons

namespace factor_add

abbrev signature : Signature where
  Params := Σ m : ℕ, (ℕ → Fin m) × (ℕ × (ℕ × ℕ))
  State p := ℕ → ℕ → List (Fin p.1)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

private def observed (p : signature.Params) (x : signature.State p) : Prop :=
  x p.2.2.1 (p.2.2.2.1 + p.2.2.2.2) =
    x p.2.2.1 p.2.2.2.1 ++ x (p.2.2.1 + p.2.2.2.1) p.2.2.2.2

def actual : Realization signature :=
  realize signature (fun _ p x => observed p x) (fun e _ => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e _ => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {m : ℕ} (x : ℕ → Fin m) (i n t : ℕ),
      R.readout () ⟨m, x, i, n, t⟩ (factor x)

private theorem actual_law : arena.Law actual := by
  intro m x i n t
  exact _root_.D5.S1.Words.MBonacciSentinelDesubstitution.factor_add x i n t

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (m := 2) (fun _ => 0) 0 0 0

private theorem bad_observation : ¬ observed ⟨2, (fun _ => 0), 0, 0, 0⟩ (fun _ _ => [0]) := by
  simp [observed]

def family : Registration arena (type_of% (@_root_.D5.S1.Words.MBonacciSentinelDesubstitution.factor_add)) where
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
    refine ⟨⟨2, (fun _ => 0), 0, 0, 0⟩, (factor (fun _ => (0 : Fin 2))), (fun _ _ => [0]), ?_⟩
    intro he
    exact bad_observation (Eq.mp he (by
      exact actual_law (m := 2) (fun _ => 0) 0 0 0))

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Words.MBonacciSentinelDesubstitution.factor_add) (type_of% actual)
    (type_of% (@factor)) Unit := {
  unitName := `D5.S1.Words.MBonacciSentinelDesubstitution.factor_add.__information_unit,
  realizationName := `Reg.D5.S1.Words.MBonacciSentinelDesubstitution.factor_add.family,
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
  escapeFrom := some (@factor),
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

end factor_add

end Reg.D5.S1.Words.MBonacciSentinelDesubstitution

#print axioms Reg.D5.S1.Words.MBonacciSentinelDesubstitution.boundary_window.family
#print axioms Reg.D5.S1.Words.MBonacciSentinelDesubstitution.boundary_window.audit
#print axioms Reg.D5.S1.Words.MBonacciSentinelDesubstitution.t_head.family
#print axioms Reg.D5.S1.Words.MBonacciSentinelDesubstitution.t_head.audit
#print axioms Reg.D5.S1.Words.MBonacciSentinelDesubstitution.occ_cons.family
#print axioms Reg.D5.S1.Words.MBonacciSentinelDesubstitution.occ_cons.audit
#print axioms Reg.D5.S1.Words.MBonacciSentinelDesubstitution.factor_add.family
#print axioms Reg.D5.S1.Words.MBonacciSentinelDesubstitution.factor_add.audit
