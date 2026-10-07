/- GID: D5/S3/Arith/Covering/PrivateEncloserDescent
   generality: G
   mirror-B: D5/B/S3/Arith/Covering/PrivateEncloserDescent
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Private enclosers below actual descendants occur in sum-minimal odd covers. -/

import D5.S3.Arith.Covering.ConcentratedPrimeSingleton

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos7.OddDistinctCoveringSystem

open scoped BigOperators

/-- An odd nonunit modulus containing an original class's entire private region
must occur if it is smaller than an actual descendant modulus. Only modulus-sum
minimality at the fixed class count is required. -/
theorem private_encloser_below_descendant_is_present
    {L : ℕ} (F : OddDistinctCoveringSystem L)
    (hsumMin : ∀ H : OddDistinctCoveringSystem L,
      (∑ i, F.modulus i) ≤ ∑ i, H.modulus i)
    (g M : Fin L) (hdiv : F.modulus g ∣ F.modulus M)
    (e w : ℕ) (he : 1 < e) (heodd : Odd e)
    (hprice : e < F.modulus M)
    (henclose : ∀ x, Private F g x → x ≡ w [MOD e]) :
    ∃ k, F.modulus k = e := by
  classical
  by_contra habsent
  have hfresh : ∀ k, F.modulus k ≠ e := fun k hk => habsent ⟨k, hk⟩
  let newMod : Fin L → ℕ := fun k => if k = M then e else F.modulus k
  let newRes : Fin L → ℕ := fun k =>
    if k = M then w else if k = g then F.residue M else F.residue k
  have hcovered (x : ℕ) : ∃ k, x ≡ newRes k [MOD newMod k] := by
    by_cases hp : Private F g x
    · exact ⟨M, by simpa [newRes, newMod] using henclose x hp⟩
    obtain ⟨k, hkg, hxk⟩ : ∃ k, k ≠ g ∧ x ≡ F.residue k [MOD F.modulus k] := by
      by_cases hxg : x ≡ F.residue g [MOD F.modulus g]
      · by_contra hn
        exact hp ⟨hxg, fun k hkg hxk => hn ⟨k, hkg, hxk⟩⟩
      · obtain ⟨k, hxk⟩ := F.covers x
        exact ⟨k, fun h => hxg (h ▸ hxk), hxk⟩
    by_cases hkM : k = M
    · subst k
      exact ⟨g, by simpa [newRes, newMod, hkg.symm] using hxk.of_dvd hdiv⟩
    · exact ⟨k, by simpa [newRes, newMod, hkM, hkg] using hxk⟩
  have hnewInj : Function.Injective newMod := by
    intro i j hij
    by_cases hi : i = M
    · subst i
      by_cases hj : j = M
      · exact hj.symm
      · exact False.elim (hfresh j
          (by simpa only [newMod, if_pos rfl, if_neg hj] using hij.symm))
    · by_cases hj : j = M
      · subst j
        exact False.elim (hfresh i
          (by simpa only [newMod, if_pos rfl, if_neg hi] using hij))
      · exact F.modulus_injective (by simpa only [newMod, if_neg hi, if_neg hj] using hij)
  let H : OddDistinctCoveringSystem L :=
    { residue := newRes
      modulus := newMod
      covers := hcovered
      modulus_one_lt := by
        intro k
        by_cases hk : k = M
        · simpa only [newMod, if_pos hk] using he
        · simpa only [newMod, if_neg hk] using F.modulus_one_lt k
      modulus_odd := by
        intro k
        by_cases hk : k = M
        · simpa only [newMod, if_pos hk] using heodd
        · simpa only [newMod, if_neg hk] using F.modulus_odd k
      modulus_injective := hnewInj }
  have hcost : (∑ k, newMod k) < ∑ k, F.modulus k := by
    apply Finset.sum_lt_sum
    · intro k _
      by_cases hk : k = M
      · subst k
        simpa only [newMod, if_pos rfl] using hprice.le
      · simp only [newMod, if_neg hk, le_refl]
    · exact ⟨M, Finset.mem_univ M, by simpa only [newMod, if_pos rfl] using hprice⟩
  exact (Nat.not_lt_of_ge (hsumMin H)) hcost

end Erdos7.OddDistinctCoveringSystem
