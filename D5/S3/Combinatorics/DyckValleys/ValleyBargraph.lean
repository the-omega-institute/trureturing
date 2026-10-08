/- GID: D5/S3/Combinatorics/DyckValleys/ValleyBargraph
   generality: G
   mirror-B: D5/B/S3/Combinatorics/DyckValleys/ValleyBargraph
   mirror-E: none(waiver:mu-welker-conjecture-three-nine)
   anchors: []
   utility: none
   digest: The common recursive code proves the valley and bargraph cardinalities equal. -/

import D5.S3.Combinatorics.DyckValleys.ValleyBargraphBijection

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.DyckValleys.ValleyBargraph

open ValleyBargraphDefs

/-- Mu--Welker Conjecture 3.9, via a size- and statistic-preserving bijection. -/
theorem result : ValleyBargraphDefs.claim := by
  classical
  intro n i hn _hi _hin
  let S : Set DyckWord :=
    {p | p.semilength = n ∧ AvoidsUUDD p ∧ valleys p = i}
  let T : Set (List ℕ) :=
    {H | IsBargraph H ∧ H.length = i ∧ semiperimeter H = n}
  let C := {c : Code // c.word.semilength = n ∧ valleys c.word = i}
  let fw : C → S := fun c =>
    ⟨c.val.word, c.property.1, Code.words_sound c.val, c.property.2⟩
  have hw : Function.Bijective fw := by
    constructor
    · intro c d h
      apply Subtype.ext
      exact Code.words_injective (congrArg Subtype.val h)
    · intro p
      obtain ⟨c, hc⟩ := Code.words_surjective p.val (p.property.1 ▸ hn) p.property.2.1
      have hs : c.word.semilength = n := by
        rw [hc]
        exact p.property.1
      have hv : valleys c.word = i := by
        rw [hc]
        exact p.property.2.2
      exact ⟨⟨c, hs, hv⟩, Subtype.ext hc⟩
  let fg : C → T := fun c =>
    ⟨c.val.height, (heights_sound c.val).1,
      (heights_sound c.val).2.2.trans c.property.2,
      (heights_sound c.val).2.1.trans c.property.1⟩
  have hg : Function.Bijective fg := by
    constructor
    · intro c d h
      apply Subtype.ext
      exact heights_injective (congrArg Subtype.val h)
    · intro H
      obtain ⟨c, hc⟩ := heights_surjective H.val H.property.1
      have hs : c.word.semilength = n := by
        rw [← (heights_sound c).2.1, hc]
        exact H.property.2.2
      have hv : valleys c.word = i := by
        rw [← (heights_sound c).2.2, hc]
        exact H.property.2.1
      exact ⟨⟨c, hs, hv⟩, Subtype.ext hc⟩
  let e : S ≃ T := (Equiv.ofBijective fw hw).symm.trans (Equiv.ofBijective fg hg)
  have hfinite : S.Finite := by
    have hall : ({p : DyckWord | p.semilength = n} : Set DyckWord).Finite := by
      apply Set.finite_def.mpr
      exact ⟨inferInstanceAs (Fintype {p : DyckWord // p.semilength = n})⟩
    exact hall.subset (fun _ h => h.1)
  let : Fintype S := hfinite.fintype
  let : Fintype T := Fintype.ofEquiv S e
  change S.ncard = T.ncard
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact Fintype.card_congr e

end D5.S3.Combinatorics.DyckValleys.ValleyBargraph
