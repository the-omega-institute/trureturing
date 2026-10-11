/- GID: D5/S3/Arith/Covering/PrivateRegionRephasing
   generality: G
   mirror-B: D5/B/S3/Arith/Covering/PrivateRegionRephasing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Crowded descendants force odd nonunit private-region enclosers to occur. -/

import D5.S3.Arith.Covering.ConcentratedPrimeSingleton

set_option autoImplicit false
set_option relaxedAutoImplicit false

open private Erdos7.OddDistinctCoveringSystem.deleting_owner_contradicts_count_minimality from
  D5.S3.Arith.Covering.ConcentratedPrimeSingleton

namespace Erdos7.OddDistinctCoveringSystem

/-- If two descendants of an original class have the same residue modulo its
modulus, every odd nonunit modulus enclosing all of that class's private points occurs
in a cover with the fewest possible distinct odd moduli. -/
theorem crowded_descendants_force_private_encloser
    {L : ℕ} (F : OddDistinctCoveringSystem L)
    (countMin : ∀ {N : ℕ}, OddDistinctCoveringSystem N → L ≤ N)
    (g i j : Fin L) (hig : i ≠ g) (hjg : j ≠ g) (hij : i ≠ j)
    (hdi : F.modulus g ∣ F.modulus i) (hdj : F.modulus g ∣ F.modulus j)
    (hphase : F.residue i ≡ F.residue j [MOD F.modulus g])
    (e w : ℕ) (he : 1 < e) (heodd : Odd e)
    (hprivate : ∀ x, Private F g x → x ≡ w [MOD e]) :
    ∃ k, F.modulus k = e := by
  classical
  by_contra habsent
  have hfresh : ∀ k, F.modulus k ≠ e := fun k hk => habsent ⟨k, hk⟩
  let newMod : Fin L → ℕ := fun k => if k = i then e else F.modulus k
  let newRes : Fin L → ℕ := fun k =>
    if k = i then w else if k = g then F.residue i else F.residue k
  have hold (x : ℕ) (k : Fin L) (hki : k ≠ i) (hkg : k ≠ g)
      (hx : x ≡ F.residue k [MOD F.modulus k]) :
      x ≡ newRes k [MOD newMod k] := by simpa [newRes, newMod, hki, hkg] using hx
  have hparent (x : ℕ) (hx : x ≡ F.residue i [MOD F.modulus g]) :
      x ≡ newRes g [MOD newMod g] := by
    simpa [newRes, newMod, hig.symm] using hx
  have hcovered (x : ℕ) : ∃ k, k ≠ j ∧ x ≡ newRes k [MOD newMod k] := by
    by_cases hp : Private F g x
    · exact ⟨i, hij, by simpa [newRes, newMod] using hprivate x hp⟩
    obtain ⟨k, hkg, hxk⟩ : ∃ k, k ≠ g ∧ x ≡ F.residue k [MOD F.modulus k] := by
      by_cases hxg : x ≡ F.residue g [MOD F.modulus g]
      · by_contra hn
        exact hp ⟨hxg, fun k hkg hxk => hn ⟨k, hkg, hxk⟩⟩
      · obtain ⟨k, hxk⟩ := F.covers x
        exact ⟨k, fun h => hxg (h ▸ hxk), hxk⟩
    by_cases hki : k = i
    · subst k
      exact ⟨g, hjg.symm, hparent x (hxk.of_dvd hdi)⟩
    by_cases hkj : k = j
    · subst k
      exact ⟨g, hjg.symm, hparent x ((hxk.of_dvd hdj).trans hphase.symm)⟩
    exact ⟨k, hkj, hold x k hki hkg hxk⟩
  have hnewinj : Function.Injective newMod := by
    intro a b hab
    by_cases hai : a = i
    · subst a
      by_cases hbi : b = i
      · exact hbi.symm
      · have hh : e = F.modulus b := by simpa [newMod, hbi] using hab
        exact False.elim (hfresh b hh.symm)
    · by_cases hbi : b = i
      · subst b
        have hh : F.modulus a = e := by simpa [newMod, hai] using hab
        exact False.elim (hfresh a hh)
      · exact F.modulus_injective (by simpa [newMod, hai, hbi] using hab)
  let H : OddDistinctCoveringSystem L := {
    modulus := newMod
    residue := newRes
    covers := fun x => let ⟨k, _, hk⟩ := hcovered x; ⟨k, hk⟩
    modulus_injective := hnewinj
    modulus_one_lt := by
      intro k
      by_cases hki : k = i
      · simpa [newMod, hki] using he
      · simpa [newMod, hki] using F.modulus_one_lt k
    modulus_odd := by
      intro k
      by_cases hki : k = i
      · simpa [newMod, hki] using heodd
      · simpa [newMod, hki] using F.modulus_odd k }
  exact Erdos7.OddDistinctCoveringSystem.deleting_owner_contradicts_count_minimality
    H countMin j hcovered

end Erdos7.OddDistinctCoveringSystem
