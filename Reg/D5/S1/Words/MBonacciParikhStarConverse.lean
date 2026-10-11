import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Words.MBonacciParikhStarConverse
import Reg.Support.DependentFamily

open _root_.D5.S1.Words.MBonacciSentinelDesubstitution
open _root_.D5.S1.Words.MBonacciReversedPrefixFRS
open _root_.D5.S1.Words.MBonacciMinimumParikhDescent
open _root_.D5.S1.Words.MBonacciMinimumGreedy
open _root_.D5.S1.Words.MBonacciParikhStarConverse
open _root_.D5.S1.Words.RankOneMorphismIterationBound (subst)
open _root_.D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs (factor letterCount)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S1.Words.MBonacciParikhStarConverse

/-- Select the original compiled private source constant without exporting it. -/
elab "conversePrivate% " n:ident : term => do
  let scopePrefix := Lean.Name.num `_private.D5.S1.Words.MBonacciParikhStarConverse 0
  let sourceName := scopePrefix ++ (`D5.S1.Words.MBonacciParikhStarConverse ++ n.getId)
  Lean.Meta.mkConstWithFreshMVarLevels sourceName

universe u

abbrev ConverseOrder := {m : ℕ // 2 ≤ m}
abbrev ConverseFive := {m : ℕ // 2 ≤ m ∧ 5 ≤ m}

namespace greedyScan_injective

abbrev signature : Signature where
  Params := ConverseOrder × ℕ
  State p := ℕ → List ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

private def observed (p : signature.Params) (x : signature.State p) : Prop :=
  0 < p.2 → Function.Injective x

def actual : Realization signature :=
  realize signature (fun _ p x => observed p x) (fun e _ => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e _ => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {m : ℕ} (hm : 2 ≤ m) (count : ℕ),
      R.readout () ⟨⟨m, hm⟩, count⟩ (greedyScan hm count)

private theorem actual_law : arena.Law actual := by
  intro m hm count
  exact _root_.D5.S1.Words.MBonacciParikhStarConverse.greedyScan_injective hm count

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (by omega : 2 ≤ 2) 1

private theorem bad_observation : ¬ observed ⟨⟨2, by omega⟩, 1⟩ (fun _ => []) := by
  intro h
  have hh := h (by omega) (a₁ := 0) (a₂ := 1) rfl
  omega

def family : Registration arena (type_of% (@_root_.D5.S1.Words.MBonacciParikhStarConverse.greedyScan_injective)) where
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
    refine ⟨⟨⟨2, by omega⟩, 1⟩, (greedyScan (by omega : 2 ≤ 2) 1), (fun _ => []), ?_⟩
    intro he
    exact bad_observation (Eq.mp he (by
      exact actual_law (by omega : 2 ≤ 2) 1))

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Words.MBonacciParikhStarConverse.greedyScan_injective) (type_of% actual)
    (type_of% (@greedyScan)) Unit := {
  unitName := `D5.S1.Words.MBonacciParikhStarConverse.greedyScan_injective.__information_unit,
  realizationName := `Reg.D5.S1.Words.MBonacciParikhStarConverse.greedyScan_injective.family,
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

end greedyScan_injective

namespace sentinel_parikh_image

abbrev signature : Signature where
  Params := ConverseOrder × ℕ
  State p := Set (Fin p.1.val → ℕ)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

private def observed (p : signature.Params) (x : signature.State p) : Prop :=
  x = Set.range (star (sentinelIter p.1.property p.2))

def actual : Realization signature :=
  realize signature (fun _ p x => observed p x) (fun e _ => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e _ => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {m : ℕ} (hm : 2 ≤ m) (k : ℕ),
      R.readout () ⟨⟨m, hm⟩, k⟩ (parikhImage hm (S hm k))

private theorem actual_law : arena.Law actual := by
  intro m hm k
  exact _root_.D5.S1.Words.MBonacciParikhStarConverse.sentinel_parikh_image hm k

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (by omega : 2 ≤ 2) 0

private theorem bad_observation : ¬ observed ⟨⟨2, by omega⟩, 0⟩ (∅) := by
  intro h
  have hz : star (sentinelIter (by omega : 2 ≤ 2) 0) 0 ∈
      Set.range (star (sentinelIter (by omega : 2 ≤ 2) 0)) := ⟨0, rfl⟩
  rw [← h] at hz
  exact hz

def family : Registration arena (type_of% (@_root_.D5.S1.Words.MBonacciParikhStarConverse.sentinel_parikh_image)) where
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
    refine ⟨⟨⟨2, by omega⟩, 0⟩, (parikhImage (by omega : 2 ≤ 2) (S (by omega : 2 ≤ 2) 0)), (∅), ?_⟩
    intro he
    exact bad_observation (Eq.mp he (by
      exact actual_law (by omega : 2 ≤ 2) 0))

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Words.MBonacciParikhStarConverse.sentinel_parikh_image) (type_of% actual)
    (type_of% (@parikhImage)) Unit := {
  unitName := `D5.S1.Words.MBonacciParikhStarConverse.sentinel_parikh_image.__information_unit,
  realizationName := `Reg.D5.S1.Words.MBonacciParikhStarConverse.sentinel_parikh_image.family,
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
  escapeFrom := some (@parikhImage),
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

end sentinel_parikh_image

namespace uniform_minimum_characterization

abbrev signature : Signature where
  Params := ConverseFive × ℕ
  State p := Set (Fin p.1.val → ℕ)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

private def observed (p : signature.Params) (x : signature.State p) : Prop :=
  1 ≤ p.2 →
    (x.ncard = p.1.val ↔ ∃ k : ℕ, p.2 = S p.1.property.1 k) ∧
    (x.ncard = p.1.val ↔ ∃ k : ℕ,
      fullGreedy p.1.property.1 p.2 = periodicDigits (m := p.1.val) k)

def actual : Realization signature :=
  realize signature (fun _ p x => observed p x) (fun e _ => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e _ => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {m : ℕ} (hm : 2 ≤ m) (h5 : 5 ≤ m) (n : ℕ),
      R.readout () ⟨⟨m, hm, h5⟩, n⟩ (parikhImage hm n)

private theorem actual_law : arena.Law actual := by
  intro m hm h5 n
  exact _root_.D5.S1.Words.MBonacciParikhStarConverse.uniform_minimum_characterization hm h5 n

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (by omega : 2 ≤ 5) (by omega : 5 ≤ 5) 1

private theorem bad_observation : ¬ observed ⟨⟨5, by omega⟩, 1⟩ (∅) := by
  intro h
  have hh := (h (by omega)).1.mpr (show ∃ k : ℕ, 1 = S (by omega : 2 ≤ 5) k from ⟨0, by simp [S]⟩)
  simpa using hh

def family : Registration arena (type_of% (@_root_.D5.S1.Words.MBonacciParikhStarConverse.uniform_minimum_characterization)) where
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
    refine ⟨⟨⟨5, by omega⟩, 1⟩, (parikhImage (by omega : 2 ≤ 5) 1), (∅), ?_⟩
    intro he
    exact bad_observation (Eq.mp he (by
      exact actual_law (by omega : 2 ≤ 5) (by omega : 5 ≤ 5) 1))

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Words.MBonacciParikhStarConverse.uniform_minimum_characterization) (type_of% actual)
    (type_of% (@parikhImage)) Unit := {
  unitName := `D5.S1.Words.MBonacciParikhStarConverse.uniform_minimum_characterization.__information_unit,
  realizationName := `Reg.D5.S1.Words.MBonacciParikhStarConverse.uniform_minimum_characterization.family,
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
  escapeFrom := some (@parikhImage),
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

end uniform_minimum_characterization


namespace periodic_greedy_sentinel

abbrev signature : Signature where
  Params := ConverseOrder × ℕ × ℕ
  State _ := (ℕ → List ℕ) × ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

private def observed (p : signature.Params) (x : signature.State p) : Prop :=
  1 ≤ p.2.1 → x.1 p.2.1 = periodicDigits (m := p.1.val) p.2.2 → p.2.1 = x.2

def actual : Realization signature :=
  realize signature (fun _ p x => observed p x) (fun e _ => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e _ => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {m : ℕ} (hm : 2 ≤ m) (n k : ℕ),
      R.readout () ⟨⟨m, hm⟩, n, k⟩ (fullGreedy hm, S hm k)

private theorem actual_law : arena.Law actual := by
  intro m hm n k
  exact (conversePrivate% periodic_greedy_sentinel) hm n k

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (by omega : 2 ≤ 2) 1 0

private theorem bad_observation : ¬ observed ⟨⟨2, by omega⟩, 1, 0⟩ ((fun _ => periodicDigits (m := 2) 0), 0) := by
  intro h
  unfold observed at h
  have hh := h (Nat.le_refl 1) rfl
  change 1 = 0 at hh
  omega

def family : Registration arena (type_of% (conversePrivate% periodic_greedy_sentinel)) where
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
    refine ⟨⟨⟨2, by omega⟩, 1, 0⟩, (fullGreedy (by omega : 2 ≤ 2), S (by omega : 2 ≤ 2) 0), ((fun _ => periodicDigits (m := 2) 0), 0), ?_⟩
    intro he
    exact bad_observation (Eq.mp he (by
      exact actual_law (by omega : 2 ≤ 2) 1 0))

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (conversePrivate% periodic_greedy_sentinel) (type_of% actual) (type_of% (@fullGreedy)) Unit := {
  unitName := `D5.S1.Words.MBonacciParikhStarConverse.periodic_greedy_sentinel.__information_unit,
  realizationName := `Reg.D5.S1.Words.MBonacciParikhStarConverse.periodic_greedy_sentinel.family,
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
  escapeFrom := some (@fullGreedy),
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

end periodic_greedy_sentinel


namespace clip_permutation

abbrev signature : Signature where
  Params := Σ α : Type u, α × List α × List α
  State p := List p.1 × List p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

private def observed (p : signature.Params) (x : signature.State p) : Prop :=
  x.1.Perm x.2 → p.2.2.1.Perm p.2.2.2

def actual : Realization signature :=
  realize signature (fun _ p x => observed p x) (fun e _ => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e _ => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {α : Type u} (a : α) (t y : List α),
      R.readout () ⟨α, a, t, y⟩ (a :: t, y ++ [a])

private theorem actual_law : arena.{u}.Law actual := by
  intro α a t y
  exact (conversePrivate% clip_permutation) a t y

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  exact h (ULift.up 0 : ULift.{u} ℕ) [] []

private theorem bad_observation : ¬ observed ⟨ULift.{u} ℕ, ULift.up 0, [], [ULift.up 1]⟩ ([], []) := by
  intro h
  unfold observed at h
  have hh := (h (List.Perm.refl [])).length_eq
  simp at hh

def family : Registration arena.{u} (type_of% (conversePrivate% clip_permutation)) where
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
    refine ⟨⟨ULift.{u} ℕ, ULift.up 0, [], [ULift.up 1]⟩, ([ULift.up 0], [ULift.up 1, ULift.up 0]), ([], []), ?_⟩
    intro he
    exact bad_observation (Eq.mp he (by
      exact actual_law (ULift.up 0 : ULift.{u} ℕ) [] [ULift.up 1]))

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (conversePrivate% clip_permutation) (type_of% actual.{u}) (type_of% (@List.Perm.{u})) Unit := {
  unitName := `D5.S1.Words.MBonacciParikhStarConverse.clip_permutation.__information_unit,
  realizationName := `Reg.D5.S1.Words.MBonacciParikhStarConverse.clip_permutation.family,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena.{u} ⟨family⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature actual.readout actual.anchor),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := some (@List.Perm),
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

end clip_permutation


namespace star_transport

abbrev signature : Signature where
  Params := Σ o : ConverseOrder, List (Fin o.val)
  State p := ℕ → Fin p.1.val
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

private def observed (p : signature.Params) (x : signature.State p) : Prop :=
  (conversePrivate% Star) p.1.property p.2 →
    ∀ q : ℕ, ∃ b : Fin p.1.val,
      (factor x q ((T p.1.property p.2).length + 1)).Perm (T p.1.property p.2 ++ [b])

def actual : Realization signature :=
  realize signature (fun _ p x => observed p x) (fun e _ => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e _ => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {m : ℕ} (hm : 2 ≤ m) (r : List (Fin m)),
      R.readout () ⟨⟨m, hm⟩, r⟩ (word hm)

private theorem actual_law : arena.Law actual := by
  intro m hm r
  exact (conversePrivate% star_transport) hm r

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (by omega : 2 ≤ 2) []

private theorem bad_observation : ¬ observed ⟨⟨2, by omega⟩, []⟩ (fun _ => 1) := by
  intro h
  unfold observed at h
  obtain ⟨b, hb⟩ := h ((conversePrivate% sentinel_star) (by omega : 2 ≤ 2) 0) 0
  have hc := hb.count_eq (0 : Fin 2)
  have cases_b : b = 0 ∨ b = 1 := by fin_cases b <;> simp
  rcases cases_b with rfl | rfl <;> norm_num [factor, T, subst, zero, sentinelIter, List.count_replicate] at hc

def family : Registration arena (type_of% (conversePrivate% star_transport)) where
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
    refine ⟨⟨⟨2, by omega⟩, []⟩, (word (by omega : 2 ≤ 2)), (fun _ => 1), ?_⟩
    intro he
    exact bad_observation (Eq.mp he (by
      exact actual_law (by omega : 2 ≤ 2) []))

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (conversePrivate% star_transport) (type_of% actual) (type_of% (@word)) Unit := {
  unitName := `D5.S1.Words.MBonacciParikhStarConverse.star_transport.__information_unit,
  realizationName := `Reg.D5.S1.Words.MBonacciParikhStarConverse.star_transport.family,
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

end star_transport


namespace sentinel_star

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
  ∀ q : ℕ, ∃ b : Fin p.1.val,
    (factor x q ((sentinelIter p.1.property p.2).length + 1)).Perm
      (sentinelIter p.1.property p.2 ++ [b])

def actual : Realization signature :=
  realize signature (fun _ p x => observed p x) (fun e _ => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e _ => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {m : ℕ} (hm : 2 ≤ m) (k : ℕ),
      R.readout () ⟨⟨m, hm⟩, k⟩ (word hm)

private theorem actual_law : arena.Law actual := by
  intro m hm k
  exact (conversePrivate% sentinel_star) hm k

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (by omega : 2 ≤ 2) 1

private theorem bad_observation : ¬ observed ⟨⟨2, by omega⟩, 1⟩ (fun _ => 1) := by
  intro h
  unfold observed at h
  obtain ⟨b, hb⟩ := h 0
  have hc := hb.count_eq (0 : Fin 2)
  have cases_b : b = 0 ∨ b = 1 := by fin_cases b <;> simp
  rcases cases_b with rfl | rfl <;> norm_num [factor, T, subst, zero, sentinelIter, List.count_replicate] at hc

def family : Registration arena (type_of% (conversePrivate% sentinel_star)) where
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
    refine ⟨⟨⟨2, by omega⟩, 1⟩, (word (by omega : 2 ≤ 2)), (fun _ => 1), ?_⟩
    intro he
    exact bad_observation (Eq.mp he (by
      exact actual_law (by omega : 2 ≤ 2) 1))

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (conversePrivate% sentinel_star) (type_of% actual) (type_of% (@word)) Unit := {
  unitName := `D5.S1.Words.MBonacciParikhStarConverse.sentinel_star.__information_unit,
  realizationName := `Reg.D5.S1.Words.MBonacciParikhStarConverse.sentinel_star.family,
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

end sentinel_star


namespace sentinel_iterate

abbrev signature : Signature where
  Params := ConverseOrder × ℕ
  State p := List (Fin p.1.val)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

private def observed (p : signature.Params) (x : signature.State p) : Prop :=
  x = ((T p.1.property)^[p.2]) []

def actual : Realization signature :=
  realize signature (fun _ p x => observed p x) (fun e _ => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e _ => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {m : ℕ} (hm : 2 ≤ m) (k : ℕ),
      R.readout () ⟨⟨m, hm⟩, k⟩ (sentinelIter hm k)

private theorem actual_law : arena.Law actual := by
  intro m hm k
  exact (conversePrivate% sentinel_iterate) hm k

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (by omega : 2 ≤ 2) 0

private theorem bad_observation : ¬ observed ⟨⟨2, by omega⟩, 0⟩ [0] := by
  intro h
  unfold observed at h
  simp [Function.iterate_zero] at h

def family : Registration arena (type_of% (conversePrivate% sentinel_iterate)) where
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
    refine ⟨⟨⟨2, by omega⟩, 0⟩, (sentinelIter (by omega : 2 ≤ 2) 0), [0], ?_⟩
    intro he
    exact bad_observation (Eq.mp he (by
      exact actual_law (by omega : 2 ≤ 2) 0))

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (conversePrivate% sentinel_iterate) (type_of% actual) (type_of% (@sentinelIter)) Unit := {
  unitName := `D5.S1.Words.MBonacciParikhStarConverse.sentinel_iterate.__information_unit,
  realizationName := `Reg.D5.S1.Words.MBonacciParikhStarConverse.sentinel_iterate.family,
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
  escapeFrom := some (@sentinelIter),
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

end sentinel_iterate


namespace sentinel_cardinality

abbrev signature : Signature where
  Params := ConverseOrder × ℕ
  State p := Set (Fin p.1.val → ℕ)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

private def observed (p : signature.Params) (x : signature.State p) : Prop :=
  x.ncard = p.1.val

def actual : Realization signature :=
  realize signature (fun _ p x => observed p x) (fun e _ => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e _ => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {m : ℕ} (hm : 2 ≤ m) (k : ℕ),
      R.readout () ⟨⟨m, hm⟩, k⟩ (parikhImage hm (S hm k))

private theorem actual_law : arena.Law actual := by
  intro m hm k
  exact (conversePrivate% sentinel_cardinality) hm k

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (by omega : 2 ≤ 2) 0

private theorem bad_observation : ¬ observed ⟨⟨2, by omega⟩, 0⟩ ∅ := by
  intro h
  unfold observed at h
  simpa using h

def family : Registration arena (type_of% (conversePrivate% sentinel_cardinality)) where
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
    refine ⟨⟨⟨2, by omega⟩, 0⟩, (parikhImage (by omega : 2 ≤ 2) (S (by omega : 2 ≤ 2) 0)), ∅, ?_⟩
    intro he
    exact bad_observation (Eq.mp he (by
      exact actual_law (by omega : 2 ≤ 2) 0))

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (conversePrivate% sentinel_cardinality) (type_of% actual) (type_of% (@parikhImage)) Unit := {
  unitName := `D5.S1.Words.MBonacciParikhStarConverse.sentinel_cardinality.__information_unit,
  realizationName := `Reg.D5.S1.Words.MBonacciParikhStarConverse.sentinel_cardinality.family,
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
  escapeFrom := some (@parikhImage),
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

end sentinel_cardinality

end Reg.D5.S1.Words.MBonacciParikhStarConverse

#print axioms Reg.D5.S1.Words.MBonacciParikhStarConverse.greedyScan_injective.family
#print axioms Reg.D5.S1.Words.MBonacciParikhStarConverse.greedyScan_injective.audit
#print axioms Reg.D5.S1.Words.MBonacciParikhStarConverse.sentinel_parikh_image.family
#print axioms Reg.D5.S1.Words.MBonacciParikhStarConverse.sentinel_parikh_image.audit
#print axioms Reg.D5.S1.Words.MBonacciParikhStarConverse.uniform_minimum_characterization.family
#print axioms Reg.D5.S1.Words.MBonacciParikhStarConverse.uniform_minimum_characterization.audit

#print axioms Reg.D5.S1.Words.MBonacciParikhStarConverse.periodic_greedy_sentinel.family
#print axioms Reg.D5.S1.Words.MBonacciParikhStarConverse.periodic_greedy_sentinel.audit

#print axioms Reg.D5.S1.Words.MBonacciParikhStarConverse.clip_permutation.family
#print axioms Reg.D5.S1.Words.MBonacciParikhStarConverse.clip_permutation.audit

#print axioms Reg.D5.S1.Words.MBonacciParikhStarConverse.star_transport.family
#print axioms Reg.D5.S1.Words.MBonacciParikhStarConverse.star_transport.audit

#print axioms Reg.D5.S1.Words.MBonacciParikhStarConverse.sentinel_star.family
#print axioms Reg.D5.S1.Words.MBonacciParikhStarConverse.sentinel_star.audit

#print axioms Reg.D5.S1.Words.MBonacciParikhStarConverse.sentinel_iterate.family
#print axioms Reg.D5.S1.Words.MBonacciParikhStarConverse.sentinel_iterate.audit

#print axioms Reg.D5.S1.Words.MBonacciParikhStarConverse.sentinel_cardinality.family
#print axioms Reg.D5.S1.Words.MBonacciParikhStarConverse.sentinel_cardinality.audit
