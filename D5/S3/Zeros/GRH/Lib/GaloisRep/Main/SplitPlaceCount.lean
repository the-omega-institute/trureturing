/- GID: D5/S3/Zeros/GRH/Lib/GaloisRep/Main/SplitPlaceCount
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/GaloisRep/Main/SplitPlaceCount
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.GaloisRep.Main.SplitPlaceCount. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/GaloisRep/Main/SplitPlaceCount.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Shimura.HeckeTower.WildType
import D5.S3.Zeros.GRH.Lib.GaloisRep.Main.AttachedDefs
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Galois representations attached to forms on definite unitary groups (known result; see
Lib.GaloisRep.Main.AvatarCompatibility).

This file: Enough places above a split quadratic place, using roots of unity. -/


open NumberField Filter Ideal IsCyclotomicExtension.Rat Set Finset
variable {E} [Field E] [NumberField E] [IsCMField E] {d} [HasQuadSubfield d E] {w : FinPlace E}

lemma IsSplitPrimeToDisc.star_ne (h : IsSplitPrimeToDisc (w.below (QuadField d))) :
  w.IsSplit := by grind [below_star, star_ne_and_prime_norm]

lemma eventually_notMem_star_notMem (ℓ : ℕ) [NeZero ℓ] (S : Finset (FinPlace E)) : ∀ᶠ w in cofinite,
  w ∉ S ∧ star w ∉ S ∧
  ↑ℓ ∉ w.1 := by simpa [↓eventually_and, finite_natCast_mem] using! S.finite_toSet.star

/-- For E stably unramified containing K = ℚ(√−d), u a split place of K prime to d
(`IsSplitPrimeToDisc`) and any places a, b of E, some place of E above u differs from a and b. -/
lemma IsSplitPrimeToDisc.exists_place_above_ne [U : StablyUnram E] {u} (h :
  IsSplitPrimeToDisc u) (a b : FinPlace E) : ∃ v, .below (QuadField d) v = u ∧
  v ≠ a ∧ star v ≠ a ∧ v ≠ b ∧ star v ≠ b := by_contra fun c ↦ by
  obtain ⟨⟨ζ, z⟩, p, o⟩ := U.1, h.star_ne_and_prime_norm.2.imp_left Fact.mk
  have H m e (k : ℕ+) [NeZero m] (t : _ = e * m ∧ ¬m.totient ≤ 4 * k.1 ∧ ∀ x : ZMod m, IsUnit x →
    x ^ k.1 = 1 := by open Calc in decide +kernel) : u.q ∣ m := by_contra fun n ↦ t.2.1 ((fun
    (K : IntermediateField ..) (_ : IsCyclotomicExtension _ ℚ K) ↦ by
    simp [← finrank m K, ← RingOfIntegers.rank, ← sum_ramification_inertia_eq_finrank
      (span {(u.q : ℤ)}), ramificationIdx_eq_of_not_dvd _ K _ n, inertiaDeg_eq_of_not_dvd _ K _ n]
    grw [orderOf_le_of_pow_eq_one k.2 (t.2.2 _ (ZMod.isUnit_prime_of_not_dvd p.1 n)),
      ncard_le_ncard (t := Finset.image (·.below K |>.1) {a, b, star a, star b}) fun P l ↦ by
      obtain ⟨v, ⟨⟩⟩ := FinPlace.comap_surjective (algebraMap K E) ⟨P, l.1, by cases l.2; aesop⟩
      exact mem_image_of_mem _ (by grind [=_ below_star, star_star, (o (v.below _)).2
        (by simpa using l.2.1.le)]), ncard_coe_finset, card_image_le, card_le_four]) _
    ((z.pow (by lia) t.1).intermediateField_adjoin_isCyclotomicExtension _))
  exact p.1.not_dvd_one (dvd_gcd (H 80 63 4) (H 63 80 6))
