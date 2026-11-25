/- GID: D5/S3/Arith/Divisors/MakowskiSchinzel/SupportSieve
   generality: I
   mirror-B: none(waiver:source-only-implementation)
   mirror-E: none(waiver:unbounded-combinatorial-proof)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/Divisors/MakowskiSchinzel/Main.makowski_schinzel_eta_le_42; instance=D5/S3/Arith/Divisors/MakowskiSchinzel/Data/Prefix00.prefix00_checked
   digest: Simultaneous prefix and joint count certificates remove every small odd support. -/

import D5.S3.Arith.Divisors.MakowskiSchinzel.SupportModel
import D5.S3.Arith.Divisors.MakowskiSchinzel.Data.All

/-! Complete small-support exclusion for finite prime sets. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.MakowskiSchinzel.Certificate

open Data

/-- Source deletion inequalities for a finite set of primes. -/
def Necessary (Q : Finset ℕ) : Prop :=
  ∀ r : ℕ, r.Prime → Odd r → (sources Q r).Nonempty →
    geom r (sourceList Q r).length * lowerProduct (sourceList Q r) < 1

private theorem empty_of_certificate {Q : Finset ℕ} {c : PrefixCertificate}
    (hp : ∀ q ∈ Q, q.Prime)
    (hbudget : (interesting Q).card ≤ 42) (hn : Necessary Q)
    (hc : c.check = true) (hr : c.r.Prime) (hro : Odd c.r)
    (hlen : c.table.length = 42)
    (hf : ∀ s ∈ c.forbidden, sources Q s = ∅) : sources Q c.r = ∅ := by
  by_contra hh
  have hnonempty := Finset.nonempty_iff_ne_empty.mpr hh
  exact c.excludes_sources hc hro hp
    (by rw [hlen]; exact sources_card_le hr.one_lt hro hbudget) hf
    (hn c.r hr hro hnonempty)

private theorem earlier_empty {Q : Finset ℕ}
    (hp : ∀ q ∈ Q, q.Prime)
    (hbudget : (interesting Q).card ≤ 42) (hn : Necessary Q) :
    ∀ c ∈ roundOne ++ roundTwo, sources Q c.r = ∅ := by
  have hfirst : ∀ c ∈ roundOne, sources Q c.r = ∅ := by
    intro c hc
    have hs := stage_shapes c (List.mem_append_left _ hc)
    apply empty_of_certificate hp hbudget hn (checked_member roundOne_checked hc)
      hs.1 hs.2.1 hs.2.2
    simp only [roundOne_forbidden c hc, List.not_mem_nil, false_implies, implies_true]
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact hfirst c hc
  · have hs := stage_shapes c (List.mem_append_right _ hc)
    apply empty_of_certificate hp hbudget hn (checked_member roundTwo_checked hc)
      hs.1 hs.2.1 hs.2.2
    intro s hs
    obtain ⟨d, hd, hds⟩ := roundTwo_forbidden c hc s hs
    simpa [hds] using hfirst d hd

private theorem joint_impossible {Q : Finset ℕ}
    (hp : ∀ q ∈ Q, q.Prime)
    (hbudget : (interesting Q).card ≤ 42) (hn : Necessary Q)
    (hearlier : ∀ c ∈ roundOne ++ roundTwo, sources Q c.r = ∅)
    (hfive : (sources Q 5).Nonempty) (heleven : (sources Q 11).Nonempty) : False := by
  classical
  let A := sources Q 5
  let B := sources Q 11
  let U := A \ B
  let V := B \ A
  let W := A ∩ B
  have hA : A ⊆ interesting Q := sources_subset_interesting (by decide) (by decide)
  have hB : B ⊆ interesting Q := sources_subset_interesting (by decide) (by decide)
  have hUB : (A ∪ B).card ≤ 42 :=
    (Finset.card_le_card (Finset.union_subset hA hB)).trans hbudget
  have hU : U.card + W.card = A.card := Finset.card_sdiff_add_card_inter A B
  have hV : V.card + W.card = B.card := by
    simpa [W, Finset.inter_comm] using Finset.card_sdiff_add_card_inter B A
  have hUnion : (A ∪ B).card + W.card = A.card + B.card :=
    Finset.card_union_add_card_inter A B
  have hbudget' : U.card + V.card + W.card ≤ 42 := by omega
  have hp' {S : Finset ℕ} (hS : S ⊆ Q) : ∀ q ∈ S, q.Prime :=
    fun q hq => hp q (hS hq)
  have hUQ : U ⊆ Q := fun q hq => (Finset.mem_filter.mp
    (Finset.mem_sdiff.mp hq).1).1
  have hVQ : V ⊆ Q := fun q hq => (Finset.mem_filter.mp
    (Finset.mem_sdiff.mp hq).1).1
  have hWQ : W ⊆ Q := fun q hq => (Finset.mem_filter.mp
    (Finset.mem_inter.mp hq).1).1
  have hearlier' {q s : ℕ} (hq : q ∈ Q)
      (hs : ∃ c ∈ roundOne ++ roundTwo, c.r = s) : ¬s ∣ q - 1 := by
    obtain ⟨c, hc, hcs⟩ := hs
    intro hd
    have hm : q ∈ sources Q c.r := Finset.mem_filter.mpr ⟨hq, by simpa [hcs] using hd⟩
    simpa [hearlier c hc] using hm
  have hc5 : prefix50.check = true := checked_member prefix12_checked (by simp)
  have hc11 : prefix51.check = true := checked_member prefix12_checked (by simp)
  have hrU : List.Forall₂ (· ≤ ·) (prefix50.table.take U.sort.length) U.sort := by
    apply prefix50.ranks_on hc5 (by decide) (hp' hUQ)
    · change U.card ≤ 42
      omega
    · intro q hq
      exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp hq).1).2
    · intro q hq s hs
      rcases conditional_forbidden.1 s hs with rfl | hs
      · intro hd
        exact (Finset.mem_sdiff.mp hq).2 (Finset.mem_filter.mpr ⟨hUQ hq, hd⟩)
      · exact hearlier' (hUQ hq) hs
  have hrV : List.Forall₂ (· ≤ ·) (prefix51.table.take V.sort.length) V.sort := by
    apply prefix51.ranks_on hc11 (by decide) (hp' hVQ)
    · change V.card ≤ 42
      omega
    · intro q hq
      exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp hq).1).2
    · intro q hq s hs
      rcases conditional_forbidden.2 s hs with rfl | hs
      · intro hd
        exact (Finset.mem_sdiff.mp hq).2 (Finset.mem_filter.mpr ⟨hVQ hq, hd⟩)
      · exact hearlier' (hVQ hq) hs
  have hrW : List.Forall₂ (· ≤ ·) (bothCertificate.table.take W.sort.length) W.sort := by
    apply bothCertificate.ranks_on both_checked (by decide) (hp' hWQ)
    · change W.card ≤ 42
      omega
    · intro q hq
      have hm := Finset.mem_inter.mp hq
      exact (show Nat.Coprime 5 11 by decide).mul_dvd_of_dvd_of_dvd
        (Finset.mem_filter.mp hm.1).2 (Finset.mem_filter.mp hm.2).2
    · intro q hq s hs
      exact hearlier' (hWQ hq) (both_forbidden s hs)
  have h5 := hn 5 (by decide) (by decide) hfive
  have h11 := hn 11 (by decide) (by decide) heleven
  have hprod5 : lowerProduct (U.sort ++ W.sort) = lowerProduct A.sort := by
    simp only [lowerProduct, List.map_append, List.prod_append]
    exact lowerProduct_split A B
  have hprod11 : lowerProduct (V.sort ++ W.sort) = lowerProduct B.sort := by
    have hh := lowerProduct_split B A
    simpa [W, Finset.inter_comm, lowerProduct, List.map_append, List.prod_append] using hh
  apply checkJoint_excludes_ranked joint_checked
    (by decide) (by decide) (by decide)
    (a := U.sort) (b := V.sort) (c := W.sort)
    (by simpa only [Finset.length_sort] using hbudget') hrU hrV hrW
  constructor
  · simpa only [Finset.length_sort, hU, hprod5, sourceList] using h5
  · simpa only [Finset.length_sort, hV, hprod11, sourceList] using h11

/-- The complete finite certificates remove every odd prime support below 131. -/
theorem small_support_empty {Q : Finset ℕ}
    (hp : ∀ q ∈ Q, q.Prime)
    (hbudget : (interesting Q).card ≤ 42) (hn : Necessary Q)
    {r : ℕ} (hr : r.Prime) (hro : Odd r) (hrsmall : r < 131) :
    sources Q r = ∅ := by
  classical
  have hearlier := earlier_empty hp hbudget hn
  have h5if : sources Q 11 = ∅ → sources Q 5 = ∅ := by
    intro h11
    apply empty_of_certificate (c := prefix50) hp hbudget hn
      (checked_member prefix12_checked (by simp)) (by decide) (by decide) (by decide)
    intro s hs
    rcases conditional_forbidden.1 s hs with rfl | ⟨c, hc, hcs⟩
    · exact h11
    · simpa [hcs] using hearlier c hc
  have h5 : sources Q 5 = ∅ := by
    by_contra hh5
    have hh11 : sources Q 11 ≠ ∅ := by intro hh; exact hh5 (h5if hh)
    exact joint_impossible hp hbudget hn hearlier
      (Finset.nonempty_iff_ne_empty.mpr hh5) (Finset.nonempty_iff_ne_empty.mpr hh11)
  have h11 : sources Q 11 = ∅ := by
    apply empty_of_certificate (c := prefix51) hp hbudget hn
      (checked_member prefix12_checked (by simp)) (by decide) (by decide) (by decide)
    intro s hs
    rcases conditional_forbidden.2 s hs with rfl | ⟨c, hc, hcs⟩
    · exact h5
    · simpa [hcs] using hearlier c hc
  have h3 : sources Q 3 = ∅ := by
    apply empty_of_certificate (c := prefix52) hp hbudget hn
      (checked_member prefix13_checked (by simp)) (by decide) (by decide) (by decide)
    intro s hs
    rcases three_forbidden s hs with rfl | rfl | ⟨c, hc, hcs⟩
    · exact h5
    · exact h11
    · simpa [hcs] using hearlier c hc
  rcases small_prime_covered r (Finset.mem_range.mpr hrsmall) hr hro with
    rfl | rfl | rfl | ⟨c, hc, hcr⟩
  · exact h3
  · exact h5
  · exact h11
  · simpa [hcr] using hearlier c hc

#print axioms small_support_empty

end D5.S3.Arith.MakowskiSchinzel.Certificate
