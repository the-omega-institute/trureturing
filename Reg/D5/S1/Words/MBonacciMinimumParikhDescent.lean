import D5.S1.Words.MBonacciParikhStarConverse
import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Words.MBonacciMinimumParikhDescent
import Reg.Support.DependentFamily

open _root_.D5.S1.Words.MBonacciMinimumParikhDescent
open _root_.D5.S1.Words.MBonacciSentinelDesubstitution
open _root_.D5.S1.Words.RankOneMorphismIterationBound (subst)
open _root_.D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs (factor letterCount)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S1.Words.MBonacciMinimumParikhDescent

abbrev Order := {m : ℕ // 2 ≤ m ∧ 3 ≤ m}
private abbrev three : Order := ⟨3, by omega⟩

namespace minimal_abelian_complexity_length

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
    ∃ k : ℕ, p.2 = (((T p.1.property.1)^[k]) ([] : List (Fin p.1.val))).length + 1

def actual : Realization signature :=
  realize signature (fun _ p x => observed p x) (fun e _ => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e _ => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {m : ℕ} (hm : 2 ≤ m) (h3 : 3 ≤ m) (n : ℕ),
    R.readout () ⟨⟨m, hm, h3⟩, n⟩ (word hm)

private theorem actual_law : arena.Law actual := by
  intro m hm h3 n
  exact @_root_.D5.S1.Words.MBonacciMinimumParikhDescent.minimal_abelian_complexity_length
    m hm h3 n

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h three.property.1 three.property.2 0

private def cutWord (q : ℕ) : Fin 3 := if q = 0 then 1 else if q = 1 then 2 else 0
private def cutVector (j : Fin 3) : Fin 3 → ℕ :=
  fun a => letterCount (factor cutWord j.val 3) a

private theorem cutVector_injective : Function.Injective cutVector := by
  intro i j h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  fin_cases i <;> fin_cases j <;>
    norm_num [cutVector, cutWord, factor, List.range_succ, letterCount, List.count_cons] at *
  all_goals omega

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
    refine ⟨2, ?_⟩
    have h2 : 2 ≤ q := by omega
    have hq1 : q + 1 ≠ 0 ∧ q + 1 ≠ 1 := by omega
    have hq2 : q + 2 ≠ 0 ∧ q + 2 ≠ 1 := by omega
    funext a
    simp [cutVector, factor, List.range_succ, cutWord, h0, h1, hq2]
  · rintro ⟨i, rfl⟩
    exact ⟨i.val, rfl⟩

private theorem sentinel_not_two (k : ℕ) :
    (((T three.property.1)^[k]) ([] : List (Fin 3))).length ≠ 2 := by
  have h : ∀ s : List (Fin 3), 3 ≤ (T three.property.1 (T three.property.1 s)).length := by
    intro s
    simp only [T, subst, List.flatMap_append, List.flatMap_singleton,
      List.length_append]
    norm_num [phi, zero, three]
  cases k with
  | zero => simp
  | succ k =>
    cases k with
    | zero => norm_num [Function.iterate_succ_apply', T, subst]
    | succ k =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      have hh := h (((T three.property.1)^[k]) [])
      omega

private theorem cut_rejected : ¬ observed ⟨three, 3⟩ cutWord := by
  intro hh
  have hc : (Set.range (fun q : ℕ => fun a => letterCount (factor cutWord q 3) a)).ncard = 3 := by
    rw [cut_image, Set.ncard_range_of_injective cutVector_injective]
    simp
  obtain ⟨k, hk⟩ := hh (by omega) hc
  have he : (((T three.property.1)^[k]) ([] : List (Fin 3))).length = 2 := by
    change 3 = (((T three.property.1)^[k]) ([] : List (Fin 3))).length + 1 at hk
    omega
  exact sentinel_not_two k he

def family : Registration arena
    (type_of% (@_root_.D5.S1.Words.MBonacciMinimumParikhDescent.minimal_abelian_complexity_length)) where
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
    refine ⟨⟨three, 3⟩, word three.property.1, cutWord, ?_⟩
    change observed ⟨three, 3⟩ (word three.property.1) ≠ observed ⟨three, 3⟩ cutWord
    intro he
    exact cut_rejected (Eq.mp he (actual_law three.property.1 three.property.2 3))

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Words.MBonacciMinimumParikhDescent.minimal_abelian_complexity_length)
    (type_of% actual) (type_of% (@word)) Unit := {
  unitName := `D5.S1.Words.MBonacciMinimumParikhDescent.minimal_abelian_complexity_length.__information_unit,
  realizationName := `Reg.D5.S1.Words.MBonacciMinimumParikhDescent.minimal_abelian_complexity_length.family,
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

end minimal_abelian_complexity_length
end Reg.D5.S1.Words.MBonacciMinimumParikhDescent

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

namespace Reg.D5.S1.Words.MBonacciMinimumParikhDescent

abbrev ConverseOrder := {m : ℕ // 2 ≤ m}
abbrev ConverseFive := {m : ℕ // 2 ≤ m ∧ 5 ≤ m}

namespace star_injective

abbrev signature : Signature where
  Params := Σ m : ℕ, List (Fin m)
  State p := Fin p.1 → Fin p.1 → ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

private def observed (p : signature.Params) (x : signature.State p) : Prop :=
  Function.Injective x

def actual : Realization signature :=
  realize signature (fun _ p x => observed p x) (fun e _ => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e _ => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {m : ℕ} (r : List (Fin m)), R.readout () ⟨m, r⟩ (star r)

private theorem actual_law : arena.Law actual := by
  intro m r
  exact _root_.D5.S1.Words.MBonacciMinimumParikhDescent.star_injective r

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (m := 2) []

private theorem bad_observation : ¬ observed ⟨2, []⟩ (fun _ _ => 0) := by
  intro h
  have hh := h (a₁ := (0 : Fin 2)) (a₂ := 1) rfl
  exact (by decide : (0 : Fin 2) ≠ 1) hh

def family : Registration arena (type_of% (@_root_.D5.S1.Words.MBonacciMinimumParikhDescent.star_injective)) where
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
    refine ⟨⟨2, []⟩, (star ([] : List (Fin 2))), (fun _ _ => 0), ?_⟩
    intro he
    exact bad_observation (Eq.mp he (by
      exact actual_law (m := 2) []))

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Words.MBonacciMinimumParikhDescent.star_injective) (type_of% actual)
    (type_of% (@_root_.D5.S1.Words.MBonacciMinimumParikhDescent.star)) Unit := {
  unitName := `D5.S1.Words.MBonacciMinimumParikhDescent.star_injective.__information_unit,
  realizationName := `Reg.D5.S1.Words.MBonacciMinimumParikhDescent.star_injective.family,
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
  escapeFrom := some (@_root_.D5.S1.Words.MBonacciMinimumParikhDescent.star),
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

end star_injective

namespace star_subset

abbrev signature : Signature where
  Params := Σ p : ConverseOrder, List (Fin p.val)
  State p := Fin p.1.val → Fin p.1.val → ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

private def observed (p : signature.Params) (x : signature.State p) : Prop :=
  FRS p.1.property p.2 → Set.range x ⊆ parikhImage p.1.property (p.2.length + 1)

def actual : Realization signature :=
  realize signature (fun _ p x => observed p x) (fun e _ => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e _ => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {m : ℕ} (hm : 2 ≤ m) (r : List (Fin m)),
      R.readout () ⟨⟨m, hm⟩, r⟩ (star r)

private theorem actual_law : arena.Law actual := by
  intro m hm r
  exact _root_.D5.S1.Words.MBonacciMinimumParikhDescent.star_subset hm r

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (by omega : 2 ≤ 2) []

private theorem bad_observation : ¬ observed ⟨⟨2, by omega⟩, []⟩ (fun _ _ => 0) := by
  intro h
  have hf : FRS (by omega : 2 ≤ 2) [] := by
    simpa [sentinelIter] using sentinel_frs (by omega : 2 ≤ 2) 0
  have hz := h hf (show (fun _ : Fin 2 => 0) ∈ Set.range (fun _ : Fin 2 => fun _ : Fin 2 => 0) from ⟨0, rfl⟩)
  obtain ⟨q, hq⟩ := hz
  have hh := congrFun hq (word (by omega : 2 ≤ 2) q)
  simpa [factor, letterCount] using hh

def family : Registration arena (type_of% (@_root_.D5.S1.Words.MBonacciMinimumParikhDescent.star_subset)) where
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
    refine ⟨⟨⟨2, by omega⟩, []⟩, (star ([] : List (Fin 2))), (fun _ _ => 0), ?_⟩
    intro he
    exact bad_observation (Eq.mp he (by
      exact actual_law (by omega : 2 ≤ 2) []))

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Words.MBonacciMinimumParikhDescent.star_subset) (type_of% actual)
    (type_of% (@_root_.D5.S1.Words.MBonacciMinimumParikhDescent.star)) Unit := {
  unitName := `D5.S1.Words.MBonacciMinimumParikhDescent.star_subset.__information_unit,
  realizationName := `Reg.D5.S1.Words.MBonacciMinimumParikhDescent.star_subset.family,
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
  escapeFrom := some (@_root_.D5.S1.Words.MBonacciMinimumParikhDescent.star),
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

end star_subset

end Reg.D5.S1.Words.MBonacciMinimumParikhDescent

#print axioms Reg.D5.S1.Words.MBonacciMinimumParikhDescent.star_injective.family
#print axioms Reg.D5.S1.Words.MBonacciMinimumParikhDescent.star_injective.audit
#print axioms Reg.D5.S1.Words.MBonacciMinimumParikhDescent.star_subset.family
#print axioms Reg.D5.S1.Words.MBonacciMinimumParikhDescent.star_subset.audit
