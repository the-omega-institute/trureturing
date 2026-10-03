/- GID: D5/S3/Combinatorics/ArcherCyclicPadovanTriples
   generality: G
   mirror-B: D5/B/S3/Combinatorics/ArcherCyclicPadovanTriples
   mirror-E: none(waiver:separated-block-triple-exclusion-for-padovan-proof)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: A 213 triple crossing a separated increasing low suffix lies in the high block. -/

import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.ArcherCyclicPadovanTriples

theorem triple_213_in_high (high low : List ℕ)
    (hsep : ∀ x ∈ high, ∀ y ∈ low, y < x)
    (hlow : low.Pairwise (· < ·))
    (c b d : ℕ) (hbc : b < c) (hcd : c < d)
    (hsub : [c, b, d].Sublist (high ++ low)) :
    [c, b, d].Sublist high := by
  obtain ⟨u, v, huv, hu, hv⟩ := List.sublist_append_iff.mp hsub
  rcases u with _ | ⟨x, us⟩
  · have hvEq : [c, b, d] = v := by simpa using huv
    have hcb : [c, b].Sublist low := by
      have hpair : [c, b].Sublist [c, b, d] :=
        List.Sublist.cons_cons c (List.Sublist.cons_cons b (List.nil_sublist _))
      exact hpair.trans (by simpa [← hvEq] using hv)
    have hlt := (List.pairwise_iff_forall_sublist.mp hlow) hcb
    omega
  · have hx : x = c := by simpa using (congrArg List.head? huv).symm
    subst x
    rcases us with _ | ⟨y, us'⟩
    · have hvEq : [b, d] = v := by simpa using congrArg List.tail huv
      have hcmid : c ∈ high := hu.subset (by simp)
      have hdlo : d ∈ low := hv.subset (by simp [← hvEq])
      have hlt := hsep c hcmid d hdlo
      omega
    · have hy : y = b := by
        have htail := congrArg List.tail huv
        simpa using (congrArg List.head? htail).symm
      subst y
      rcases us' with _ | ⟨z, us''⟩
      · have hvEq : [d] = v := by
          have htail := congrArg List.tail (congrArg List.tail huv)
          simpa using htail
        have hcHigh : c ∈ high := hu.subset (by simp)
        have hdLow : d ∈ low := hv.subset (by simp [← hvEq])
        have hlt := hsep c hcHigh d hdLow
        omega
      · have hz : z = d := by
          have htail := congrArg List.tail (congrArg List.tail huv)
          simpa using (congrArg List.head? htail).symm
        subst z
        have hlen : us'' = [] ∧ v = [] := by
          have hlenEq := congrArg List.length huv
          simp only [List.length_cons, List.length_append, List.length_nil,
            Nat.zero_add] at hlenEq
          have hus : us''.length = 0 := by omega
          have hvlen : v.length = 0 := by omega
          exact ⟨List.length_eq_zero_iff.mp hus, List.length_eq_zero_iff.mp hvlen⟩
        rcases hlen with ⟨rfl, rfl⟩
        simpa using hu

theorem triple_213_after_low (low high : List ℕ)
    (hlow : low.Pairwise (· < ·))
    (hsep : ∀ x ∈ low, ∀ y ∈ high, x < y)
    (c b d : ℕ) (hbc : b < c)
    (hsub : [c, b, d].Sublist (low ++ high)) :
    [c, b, d].Sublist high := by
  obtain ⟨u, v, huv, hu, hv⟩ := List.sublist_append_iff.mp hsub
  rcases u with _ | ⟨x, us⟩
  · simpa using huv ▸ hv
  · have hx : x = c := by simpa using (congrArg List.head? huv).symm
    subst x
    rcases us with _ | ⟨y, us'⟩
    · have hvEq : [b, d] = v := by simpa using congrArg List.tail huv
      have hcLow : c ∈ low := hu.subset (by simp)
      have hbHigh : b ∈ high := hv.subset (by simp [← hvEq])
      have hlt := hsep c hcLow b hbHigh
      omega
    · have hy : y = b := by
        have htail := congrArg List.tail huv
        simpa using (congrArg List.head? htail).symm
      subst y
      have hpair : [c, b].Sublist low := by
        have hsubpair : [c, b].Sublist (c :: b :: us') :=
          List.Sublist.cons_cons c (List.Sublist.cons_cons b (List.nil_sublist _))
        exact hsubpair.trans hu
      have hlt := (List.pairwise_iff_forall_sublist.mp hlow) hpair
      omega

end D5.S3.Combinatorics.ArcherCyclicPadovanTriples
