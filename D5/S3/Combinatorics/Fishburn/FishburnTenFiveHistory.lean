/- GID: D5/S3/Combinatorics/Fishburn/FishburnTenFiveHistory
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Fishburn/FishburnTenFiveHistory
   mirror-E: none(waiver:maximum-insertion-history-inverse)
   anchors: []
   utility: none
   digest: Active maximum-insertion histories biject with all nonempty class members. -/

import D5.S3.Combinatorics.Fishburn.FishburnBasicParents

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Fishburn.FishburnTenFiveHistory

open D5.S3.Combinatorics Nonnesting FishburnDefs FishburnBasicParents

def replay : List ℕ → List ℕ
  | [] => [1]
  | gap :: earlier => (replay earlier).insertIdx gap (earlier.length + 2)

def LegalHistory (patterns : List (List ℕ)) : List ℕ → Prop
  | [] => [1] ∈ avoiders 1 patterns
  | gap :: earlier => LegalHistory patterns earlier ∧ gap ≤ (replay earlier).length ∧
      (replay earlier).insertIdx gap (earlier.length + 2) ∈
        avoiders (earlier.length + 2) patterns

set_option maxHeartbeats 1800000 in
theorem maximum_history_equivalence (patterns : List (List ℕ)) (depth : ℕ) :
    ∃ correspondence : {gaps : List ℕ // gaps.length = depth ∧ LegalHistory patterns gaps} ≃
        avoiders (depth + 1) patterns,
      ∀ history, (correspondence history).val = replay history.val := by
  have hvalid : ∀ gaps : List ℕ, LegalHistory patterns gaps →
      replay gaps ∈ avoiders (gaps.length + 1) patterns := by
    intro gaps
    cases gaps with
    | nil => exact id
    | cons gap earlier =>
      intro hlegal
      simpa only [replay, List.length_cons, Nat.add_assoc] using hlegal.2.2
  have hinjective : ∀ count : ℕ, ∀ first second : List ℕ,
      first.length = count → second.length = count →
      LegalHistory patterns first → LegalHistory patterns second →
      replay first = replay second → first = second := by
    intro count
    induction count with
    | zero =>
      intro first second hfirst hsecond _ _ _
      have hf := List.length_eq_zero_iff.mp hfirst
      have hs := List.length_eq_zero_iff.mp hsecond
      exact hf.trans hs.symm
    | succ count ih =>
      intro first second hfirst hsecond hlegalfirst hlegalsecond heq
      cases first with
      | nil => simp at hfirst
      | cons gap earlier =>
        cases second with
        | nil => simp at hsecond
        | cons othergap otherearlier =>
          have hear : earlier.length = count := by simpa using hfirst
          have hother : otherearlier.length = count := by simpa using hsecond
          have hpfirst : replay earlier ∈ avoiders (count + 1) patterns := by
            simpa only [hear] using hvalid earlier hlegalfirst.1
          have hpsecond : replay otherearlier ∈ avoiders (count + 1) patterns := by
            simpa only [hother] using hvalid otherearlier hlegalsecond.1
          have hcfirst : (replay earlier).insertIdx gap (count + 1 + 1) ∈
              avoiders (count + 1 + 1) patterns := by
            simpa only [hear, Nat.add_assoc] using hlegalfirst.2.2
          have hcsecond : (replay otherearlier).insertIdx othergap (count + 1 + 1) ∈
              avoiders (count + 1 + 1) patterns := by
            simpa only [hother, Nat.add_assoc] using hlegalsecond.2.2
          let source := {entry : List ℕ × ℕ //
            entry.1 ∈ avoiders (count + 1) patterns ∧ entry.2 ≤ entry.1.length ∧
              entry.1.insertIdx entry.2 (count + 1 + 1) ∈
                avoiders (count + 1 + 1) patterns}
          let firstEntry : source :=
            ⟨(replay earlier, gap), hpfirst, hlegalfirst.2.1, hcfirst⟩
          let secondEntry : source :=
            ⟨(replay otherearlier, othergap), hpsecond, hlegalsecond.2.1, hcsecond⟩
          have hentries : firstEntry = secondEntry := by
            apply (maximum_insertion_bijection (count + 1) patterns).1
            apply Subtype.ext
            simpa only [firstEntry, secondEntry, replay, hear, hother, Nat.add_assoc]
              using heq
          have hpairs := congrArg Subtype.val hentries
          have hparents : replay earlier = replay otherearlier := congrArg Prod.fst hpairs
          have hgaps : gap = othergap := congrArg Prod.snd hpairs
          have htails := ih earlier otherearlier hear hother hlegalfirst.1 hlegalsecond.1
            hparents
          exact congrArg₂ List.cons hgaps htails
  have hsurjective : ∀ count : ℕ, ∀ child : avoiders (count + 1) patterns,
      ∃ gaps : List ℕ, gaps.length = count ∧ LegalHistory patterns gaps ∧
        replay gaps = child.val := by
    intro count
    induction count with
    | zero =>
      intro child
      have hperm : child.val.Perm [1] := child.property.1
      have heq := List.perm_singleton.mp hperm
      refine ⟨[], rfl, ?_, heq.symm⟩
      simpa only [LegalHistory, heq] using child.property
    | succ count ih =>
      intro child
      obtain ⟨entry, hentry⟩ :=
        (maximum_insertion_bijection (count + 1) patterns).2 child
      obtain ⟨earlier, hear, hlegal, hparent⟩ := ih ⟨entry.val.1, entry.property.1⟩
      have hchild : entry.val.1.insertIdx entry.val.2 (count + 1 + 1) = child.val :=
        congrArg Subtype.val hentry
      refine ⟨entry.val.2 :: earlier, by simp [hear], ?_, ?_⟩
      · change LegalHistory patterns earlier ∧ entry.val.2 ≤ (replay earlier).length ∧ _
        refine ⟨hlegal, ?_, ?_⟩
        · simpa only [hparent] using entry.property.2.1
        · simpa only [hparent, hear, Nat.add_assoc] using entry.property.2.2
      · simpa only [replay, hparent, hear, Nat.add_assoc] using hchild
  let decode : {gaps : List ℕ // gaps.length = depth ∧ LegalHistory patterns gaps} →
      avoiders (depth + 1) patterns := fun history =>
    ⟨replay history.val, by
      simpa only [history.property.1] using hvalid history.val history.property.2⟩
  have hbijective : Function.Bijective decode := by
    constructor
    · intro first second heq
      apply Subtype.ext
      exact hinjective depth first.val second.val first.property.1 second.property.1
        first.property.2 second.property.2 (congrArg Subtype.val heq)
    · intro child
      obtain ⟨gaps, hlength, hlegal, heq⟩ := hsurjective depth child
      refine ⟨⟨gaps, hlength, hlegal⟩, ?_⟩
      exact Subtype.ext heq
  exact ⟨Equiv.ofBijective decode hbijective, fun _ => rfl⟩

end D5.S3.Combinatorics.Fishburn.FishburnTenFiveHistory
