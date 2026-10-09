/- GID: D5/S3/Combinatorics/Games/DivisorNimBoundSmallSupport
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Games/DivisorNimBoundSmallSupport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Two equal dyadic removals restore an even minimum-depth count. -/

import D5.S3.Combinatorics.Games.DivisorNimBoundOutcome

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Games.DivisorNimGrundy

theorem paired_pivot_structure {P : Position} (hp : Positive P) {h k : ℕ}
    (hk : HasDepth P (k + 1)) (hc : countAt P (k + 1) = 1)
    (hh : h ∈ P) (hval : k + 1 < valuation h) :
    let Q := successor P h (2 ^ k)
    let z := h - 2 ^ k
    Q.erase z = P.erase h ∧
      (∀ x ∈ Q.erase z, k + 1 ≤ valuation x) ∧
      countAt (Q.erase z) (k + 1) = 1 ∧
      0 < z - 2 ^ k ∧ valuation (z - 2 ^ k) = k + 1 := by
  dsimp only
  have hd := power_legal hp hk hh
  have hv : valuation (2 ^ (k + 1)) = k + 1 := padicValNat.prime_pow _
  have hsub := valuation_sub_of_lt hd.1 hd.2.1 (by rw [hv]; exact hval)
  have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [pow_succ]; omega
  have hs : h - 2 ^ k - 2 ^ k = h - 2 ^ (k + 1) := by omega
  have hz : h - 2 ^ k ≠ 0 := by omega
  have he : (successor P h (2 ^ k)).erase (h - 2 ^ k) = P.erase h := by
    rw [successor, if_neg hz, Multiset.add_comm]
    change ((h - 2 ^ k) ::ₘ P.erase h).erase (h - 2 ^ k) = P.erase h
    exact Multiset.erase_cons_head _ _
  refine ⟨he, ?_, ?_, ?_, ?_⟩
  · rw [he]
    exact fun x hx => hk.1 x (Multiset.mem_of_mem_erase hx)
  · rw [he]
    have ht := countAt_erase (k := k + 1) hh
    rw [if_neg (by omega)] at ht
    omega
  · rw [hs]; exact hsub.1
  · rw [hs]; exact hsub.2.trans hv


end D5.S3.Combinatorics.Games.DivisorNimGrundy
