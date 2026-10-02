/- GID: D5/S3/Combinatorics/FundamentalBijection/ThetaBasicSum
   generality: G
   mirror-B: D5/B/S3/Combinatorics/FundamentalBijection/ThetaBasicSum
   mirror-E: none(waiver:permutation-sum-cuts)
   anchors: [mathlib/module/Mathlib.Data.List.Intervals]
   utility: none
   digest: Strict prefix-suffix separation forces a permutation value cut. -/

import D5.S3.Combinatorics.FundamentalBijection.ThetaBasicInverseGeneral
import Mathlib.Data.List.Intervals

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.FundamentalBijection.ThetaBasicSum

/-- A strict value separation between the first `k` entries and the
remaining entries forces a value cut in a permutation. -/
theorem separated_prefix_cut (w : List ℕ)
    (hw : w.Perm (List.range' 1 w.length)) (k : ℕ) (hk : k ≤ w.length)
    (hsep : ∀ x ∈ w.take k, ∀ y ∈ w.drop k, x < y) :
    ∀ x ∈ w.take k, x ≤ k := by
  let u := w.take k
  let v := w.drop k
  have hnodup : u.Nodup := (hw.nodup_iff.mpr List.nodup_range').take
  have hlen : u.length = k := by simp [u, hk]
  intro x hx
  by_contra hnot
  have hxgt : k < x := by omega
  have hlow : (List.range' 1 k).toFinset ⊆ u.toFinset := by
    intro y hy
    have hyr : y ∈ List.range' 1 k := List.mem_toFinset.mp hy
    obtain ⟨a, ha, hval⟩ := List.mem_range'.mp hyr
    have hyw : y ∈ w := hw.mem_iff.mpr
      (List.mem_range'.mpr ⟨a, by omega, hval⟩)
    have hyuv : y ∈ u ++ v := by
      simpa only [u, v, List.take_append_drop] using hyw
    rcases List.mem_append.mp hyuv with hyu | hyv
    · exact List.mem_toFinset.mpr hyu
    · have hxy : x < y := hsep x hx y hyv
      omega
  have hcard : (List.range' 1 k).toFinset.card = u.toFinset.card := by
    simp [List.card_toFinset, List.dedup_eq_self.mpr hnodup,
      List.dedup_eq_self.mpr List.nodup_range', hlen]
  have hset : (List.range' 1 k).toFinset = u.toFinset :=
    Finset.eq_of_subset_of_card_le hlow (by omega)
  have hxr : x ∈ List.range' 1 k := by
    apply List.mem_toFinset.mp
    rw [hset]
    exact List.mem_toFinset.mpr hx
  obtain ⟨a, ha, hval⟩ := List.mem_range'.mp hxr
  omega

end D5.S3.Combinatorics.FundamentalBijection.ThetaBasicSum
