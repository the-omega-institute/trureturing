/- GID: D5/S3/Combinatorics/Fishburn/FishburnBasicDecreasingPrefixes
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Fishburn/FishburnBasicDecreasingPrefixes
   mirror-E: none(waiver:first-ascent-induction)
   anchors: []
   utility: none
   digest: Every Fishburn prefix ending at one is decreasing. -/

import D5.S3.Combinatorics.Fishburn.FishburnBasicAscents

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Fishburn.FishburnBasicPrefixes

open D5.S3.Combinatorics.Fishburn.FishburnDefs
open D5.S3.Combinatorics.Fishburn.FishburnBasicAscents

theorem prefix_through_one_decreasing (n : ℕ) (p : List ℕ)
    (hperm : p.Perm (List.range' 1 n)) (hfish : IsFishburn p)
    (one : ℕ) (honebound : one < p.length) (hone : p.getD one 0 = 1) :
    ∀ earlier later, earlier < later → later ≤ one →
      p.getD later 0 < p.getD earlier 0 := by
  have hnodup : p.Nodup := hperm.nodup_iff.mpr (List.nodup_range' 1)
  have hascents := (isFishburn_iff_ascent_predecessor n p hperm).mp hfish
  have hdec : ∀ later, later ≤ one → ∀ earlier, earlier < later →
      p.getD later 0 < p.getD earlier 0 := by
    intro later
    induction later using Nat.strong_induction_on with
    | h later ih =>
      intro hlater earlier hearlier
      cases later with
      | zero => omega
      | succ previous =>
        have hstep : p.getD (previous + 1) 0 < p.getD previous 0 := by
          rcases lt_trichotomy (p.getD (previous + 1) 0) (p.getD previous 0) with
            hlt | heq | hascent
          · exact hlt
          · have hindex := (List.getD_inj (by omega) (by omega) hnodup).mp heq
            omega
          · rcases hascents previous (by omega) hascent with hbottom | hpred
            · have hindex : previous = one :=
                (List.getD_inj (by omega) honebound hnodup).mp (hbottom.trans hone.symm)
              omega
            · obtain ⟨pred, hpred, hvalue⟩ := hpred
              have hdecrease := ih previous (by omega) (by omega) pred hpred
              omega
        by_cases heq : earlier = previous
        · subst earlier
          exact hstep
        · exact lt_trans hstep (ih previous (by omega) (by omega) earlier (by omega))
  intro earlier later hearlier hlater
  exact hdec later hlater earlier hearlier

end D5.S3.Combinatorics.Fishburn.FishburnBasicPrefixes
