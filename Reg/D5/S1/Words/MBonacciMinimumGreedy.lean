import D5.S1.Words.MBonacciParikhStarConverse
import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Words.MBonacciMinimumGreedy
import Reg.Support.DependentFamily

open _root_.D5.S1.Words.MBonacciMinimumGreedy
open _root_.D5.S1.Words.MBonacciSentinelDesubstitution
open _root_.D5.S1.Words.RankOneMorphismIterationBound (subst image)
open _root_.D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs (factor letterCount)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S1.Words.MBonacciMinimumGreedy

abbrev Order := {m : ℕ // 2 ≤ m ∧ 5 ≤ m}
private abbrev five : Order := ⟨5, by omega⟩

namespace minimal_abelian_complexity_greedy

abbrev signature : Signature where
  Params := Order × ℕ
  State p := ℕ → Fin p.1.val
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

private def observed (p : signature.Params) (x : signature.State p) : Prop :=
  1 ≤ p.2 →
    (Set.range (fun q : ℕ => fun a => letterCount (factor x q p.2) a)).ncard = p.1.val →
    ∃ k : ℕ, p.2 = S p.1.property.1 k ∧ topIndex p.1.property.1 p.2 = k ∧
      fullGreedy p.1.property.1 p.2 = periodicDigits (m := p.1.val) k ∧
      (fullGreedy p.1.property.1 p.2).length = k + 1 ∧
      (fullGreedy p.1.property.1 p.2).head? = some 1

def actual : Realization signature :=
  realize signature (fun _ p x => observed p x) (fun e _ => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e _ => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {m : ℕ} (hm : 2 ≤ m) (h5 : 5 ≤ m) (n : ℕ),
    R.readout () ⟨⟨m, hm, h5⟩, n⟩ (word hm)

private theorem actual_law : arena.Law actual := by
  intro m hm h5 n
  exact @_root_.D5.S1.Words.MBonacciMinimumGreedy.minimal_abelian_complexity_greedy
    m hm h5 n

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h five.property.1 five.property.2 0

private def cutWord (q : ℕ) : Fin 5 :=
  if q = 0 then 1 else if q = 1 then 2 else if q = 2 then 3
  else if q = 3 then 4 else 0

private def cutVector (j : Fin 5) : Fin 5 → ℕ :=
  fun a => letterCount (factor cutWord j.val 3) a

private theorem cutVector_injective : Function.Injective cutVector := by
  decide

private theorem cut_image :
    Set.range (fun q : ℕ => fun a => letterCount (factor cutWord q 3) a) =
      Set.range cutVector := by
  ext v
  constructor
  · rintro ⟨q, rfl⟩
    by_cases h0 : q = 0
    · exact ⟨0, by subst q; rfl⟩
    by_cases h1 : q = 1
    · exact ⟨1, by subst q; rfl⟩
    by_cases h2 : q = 2
    · exact ⟨2, by subst q; rfl⟩
    by_cases h3 : q = 3
    · exact ⟨3, by subst q; rfl⟩
    refine ⟨4, ?_⟩
    have h4 : 4 ≤ q := by omega
    have hh1 : q + 1 ≠ 0 ∧ q + 1 ≠ 1 ∧ q + 1 ≠ 2 ∧ q + 1 ≠ 3 := by omega
    have hh2 : q + 2 ≠ 0 ∧ q + 2 ≠ 1 ∧ q + 2 ≠ 2 ∧ q + 2 ≠ 3 := by omega
    funext a
    simp [cutVector, factor, List.range_succ, cutWord, h0, h1, h2, h3, hh1, hh2]
  · rintro ⟨i, rfl⟩
    exact ⟨i.val, rfl⟩

private theorem sentinel_sum_not_three (k : ℕ) : S five.property.1 k ≠ 3 := by
  cases k with
  | zero => simp [S]
  | succ k =>
      cases k with
      | zero => simp [S, U, image]
      | succ k =>
          have he : k + 1 + 1 = 2 + k := by omega
          rw [S, he, Finset.sum_range_add]
          norm_num [U, image, subst, phi, zero, five, Finset.sum_range_succ]
          omega

private theorem cut_rejected : ¬ observed ⟨five, 3⟩ cutWord := by
  intro hh
  have hc : (Set.range (fun q : ℕ => fun a : Fin 5 =>
      letterCount (factor cutWord q 3) a)).ncard = 5 := by
    rw [cut_image, Set.ncard_range_of_injective cutVector_injective]
    simp
  obtain ⟨k, hk, _⟩ := hh (by omega) hc
  exact sentinel_sum_not_three k hk.symm

def family : Registration arena
    (type_of% (@_root_.D5.S1.Words.MBonacciMinimumGreedy.minimal_abelian_complexity_greedy)) where
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
    refine ⟨⟨five, 3⟩, word five.property.1, cutWord, ?_⟩
    change observed ⟨five, 3⟩ (word five.property.1) ≠ observed ⟨five, 3⟩ cutWord
    intro he
    exact cut_rejected (Eq.mp he (actual_law five.property.1 five.property.2 3))

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Words.MBonacciMinimumGreedy.minimal_abelian_complexity_greedy)
    (type_of% actual) (type_of% (@word)) Unit := {
  unitName := `D5.S1.Words.MBonacciMinimumGreedy.minimal_abelian_complexity_greedy.__information_unit,
  realizationName := `Reg.D5.S1.Words.MBonacciMinimumGreedy.minimal_abelian_complexity_greedy.family,
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

end minimal_abelian_complexity_greedy
end Reg.D5.S1.Words.MBonacciMinimumGreedy

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

namespace Reg.D5.S1.Words.MBonacciMinimumGreedy

abbrev ConverseOrder := {m : ℕ // 2 ≤ m}
abbrev ConverseFive := {m : ℕ // 2 ≤ m ∧ 5 ≤ m}

namespace sentinel_sum

abbrev signature : Signature where
  Params := ConverseOrder × ℕ
  State p := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

private def observed (p : signature.Params) (x : signature.State p) : Prop :=
  x = S p.1.property p.2

def actual : Realization signature :=
  realize signature (fun _ p x => observed p x) (fun e _ => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e _ => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {m : ℕ} (hm : 2 ≤ m) (k : ℕ), R.readout () ⟨⟨m, hm⟩, k⟩
      ((((T hm)^[k]) ([] : List (Fin m))).length + 1)

private theorem actual_law : arena.Law actual := by
  intro m hm k
  exact _root_.D5.S1.Words.MBonacciMinimumGreedy.sentinel_sum hm k

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (by omega : 2 ≤ 2) 0

private theorem bad_observation : ¬ observed ⟨⟨2, by omega⟩, 0⟩ (2) := by
  norm_num [observed, S]

def family : Registration arena (type_of% (@_root_.D5.S1.Words.MBonacciMinimumGreedy.sentinel_sum)) where
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
    refine ⟨⟨⟨2, by omega⟩, 0⟩, (1), (2), ?_⟩
    intro he
    exact bad_observation (Eq.mp he (by
      exact actual_law (by omega : 2 ≤ 2) 0))

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Words.MBonacciMinimumGreedy.sentinel_sum) (type_of% actual)
    (type_of% (@T)) Unit := {
  unitName := `D5.S1.Words.MBonacciMinimumGreedy.sentinel_sum.__information_unit,
  realizationName := `Reg.D5.S1.Words.MBonacciMinimumGreedy.sentinel_sum.family,
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

end sentinel_sum

namespace scan_length

abbrev signature : Signature where
  Params := ConverseOrder × (ℕ × ℕ)
  State p := List ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

private def observed (p : signature.Params) (x : signature.State p) : Prop :=
  x.length = p.2.1

def actual : Realization signature :=
  realize signature (fun _ p x => observed p x) (fun e _ => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e _ => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {m : ℕ} (hm : 2 ≤ m) (count r : ℕ),
      R.readout () ⟨⟨m, hm⟩, count, r⟩ (greedyScan hm count r)

private theorem actual_law : arena.Law actual := by
  intro m hm count r
  exact _root_.D5.S1.Words.MBonacciMinimumGreedy.scan_length hm count r

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (by omega : 2 ≤ 2) 1 0

private theorem bad_observation : ¬ observed ⟨⟨2, by omega⟩, 1, 0⟩ ([]) := by
  simp [observed]

def family : Registration arena (type_of% (@_root_.D5.S1.Words.MBonacciMinimumGreedy.scan_length)) where
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
    refine ⟨⟨⟨2, by omega⟩, 1, 0⟩, (greedyScan (by omega : 2 ≤ 2) 1 0), ([]), ?_⟩
    intro he
    exact bad_observation (Eq.mp he (by
      exact actual_law (by omega : 2 ≤ 2) 1 0))

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Words.MBonacciMinimumGreedy.scan_length) (type_of% actual)
    (type_of% (@greedyScan)) Unit := {
  unitName := `D5.S1.Words.MBonacciMinimumGreedy.scan_length.__information_unit,
  realizationName := `Reg.D5.S1.Words.MBonacciMinimumGreedy.scan_length.family,
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
  escapeFrom := some (@greedyScan),
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

end scan_length

namespace sentinel_top

abbrev signature : Signature where
  Params := ConverseOrder × ℕ
  State p := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

private def observed (p : signature.Params) (x : signature.State p) : Prop :=
  x = p.2

def actual : Realization signature :=
  realize signature (fun _ p x => observed p x) (fun e _ => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e _ => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {m : ℕ} (hm : 2 ≤ m) (k : ℕ),
      R.readout () ⟨⟨m, hm⟩, k⟩ (topIndex hm (S hm k))

private theorem actual_law : arena.Law actual := by
  intro m hm k
  exact _root_.D5.S1.Words.MBonacciMinimumGreedy.sentinel_top hm k

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (by omega : 2 ≤ 2) 0

private theorem bad_observation : ¬ observed ⟨⟨2, by omega⟩, 0⟩ (1) := by
  simp [observed]

def family : Registration arena (type_of% (@_root_.D5.S1.Words.MBonacciMinimumGreedy.sentinel_top)) where
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
    refine ⟨⟨⟨2, by omega⟩, 0⟩, (topIndex (by omega : 2 ≤ 2) (S (by omega : 2 ≤ 2) 0)), (1), ?_⟩
    intro he
    exact bad_observation (Eq.mp he (by
      exact actual_law (by omega : 2 ≤ 2) 0))

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Words.MBonacciMinimumGreedy.sentinel_top) (type_of% actual)
    (type_of% (@topIndex)) Unit := {
  unitName := `D5.S1.Words.MBonacciMinimumGreedy.sentinel_top.__information_unit,
  realizationName := `Reg.D5.S1.Words.MBonacciMinimumGreedy.sentinel_top.family,
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
  escapeFrom := some (@topIndex),
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

end sentinel_top

namespace scan_sentinel

abbrev signature : Signature where
  Params := ConverseOrder × ℕ
  State p := List ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

private def observed (p : signature.Params) (x : signature.State p) : Prop :=
  x = periodicDigits (m := p.1.val) p.2

def actual : Realization signature :=
  realize signature (fun _ p x => observed p x) (fun e _ => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e _ => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {m : ℕ} (hm : 2 ≤ m) (k : ℕ),
      R.readout () ⟨⟨m, hm⟩, k⟩ (greedyScan hm (k + 1) (S hm k))

private theorem actual_law : arena.Law actual := by
  intro m hm k
  exact _root_.D5.S1.Words.MBonacciMinimumGreedy.scan_sentinel hm k

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (by omega : 2 ≤ 2) 0

private theorem bad_observation : ¬ observed ⟨⟨2, by omega⟩, 0⟩ ([]) := by
  simp [observed, periodicDigits]

def family : Registration arena (type_of% (@_root_.D5.S1.Words.MBonacciMinimumGreedy.scan_sentinel)) where
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
    refine ⟨⟨⟨2, by omega⟩, 0⟩, (greedyScan (by omega : 2 ≤ 2) 1 (S (by omega : 2 ≤ 2) 0)), ([]), ?_⟩
    intro he
    exact bad_observation (Eq.mp he (by
      exact actual_law (by omega : 2 ≤ 2) 0))

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Words.MBonacciMinimumGreedy.scan_sentinel) (type_of% actual)
    (type_of% (@greedyScan)) Unit := {
  unitName := `D5.S1.Words.MBonacciMinimumGreedy.scan_sentinel.__information_unit,
  realizationName := `Reg.D5.S1.Words.MBonacciMinimumGreedy.scan_sentinel.family,
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
  escapeFrom := some (@greedyScan),
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

end scan_sentinel

end Reg.D5.S1.Words.MBonacciMinimumGreedy

#print axioms Reg.D5.S1.Words.MBonacciMinimumGreedy.sentinel_sum.family
#print axioms Reg.D5.S1.Words.MBonacciMinimumGreedy.sentinel_sum.audit
#print axioms Reg.D5.S1.Words.MBonacciMinimumGreedy.scan_length.family
#print axioms Reg.D5.S1.Words.MBonacciMinimumGreedy.scan_length.audit
#print axioms Reg.D5.S1.Words.MBonacciMinimumGreedy.sentinel_top.family
#print axioms Reg.D5.S1.Words.MBonacciMinimumGreedy.sentinel_top.audit
#print axioms Reg.D5.S1.Words.MBonacciMinimumGreedy.scan_sentinel.family
#print axioms Reg.D5.S1.Words.MBonacciMinimumGreedy.scan_sentinel.audit
