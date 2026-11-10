/- GID: D5/S3/Arith/Descartes/SplitPrimeSphereRadii
   generality: I
   mirror-B: D5/B/S3/Arith/Descartes/SplitPrimeSphereRadii
   mirror-E: none(waiver:symbolic-unbounded-classification)
   anchors: []
   utility: none
   digest: Split prime powers in one primitive spherical radius occur in one or two others. -/

import D5.S3.Arith.Descartes.PrimitiveSphereRadii

/-! Shared divisibility at every positive prime-power threshold. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Descartes.SplitPrimeSphereRadii

open Finset PrimitiveSphereRadii

private lemma other_curvature_unit (b : Fin 4 → ℕ) (hprim : gcd4 b = 1)
    (heq : (∑ i, b i) ^ 2 = 3 * ∑ i, b i ^ 2)
    (p : ℕ) (hp : p.Prime) (hodd : p ≠ 2) (i : Fin 4) :
    ∃ j, j ≠ i ∧ ¬p ∣ b j := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra! hall
  have hunit : ¬p ∣ b i := by
    intro hi
    have hd : p ∣ gcd4 b := Finset.dvd_gcd fun j _ => by
      by_cases hji : j = i
      · simpa [hji] using hi
      · exact hall j hji
    rw [hprim] at hd
    exact hp.not_dvd_one hd
  have hz (j : Fin 4) (hji : j ≠ i) : (b j : ZMod p) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr (hall j hji)
  have hs : (∑ j, (b j : ZMod p)) = b i := by
    apply sum_eq_single i
    · intro j _ hji
      exact hz j hji
    · simp
  have hss : (∑ j, (b j : ZMod p) ^ 2) = (b i : ZMod p) ^ 2 := by
    apply sum_eq_single i
    · intro j _ hji
      rw [hz j hji, zero_pow (by decide)]
    · simp
  have he : (∑ j, (b j : ZMod p)) ^ 2 = 3 * ∑ j, (b j : ZMod p) ^ 2 := by
    have h := congrArg (fun n : ℕ => (n : ZMod p)) heq
    push_cast at h
    exact h
  rw [hs, hss] at he
  have hzero : (2 : ZMod p) * (b i : ZMod p) ^ 2 = 0 := by
    linear_combination -he
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro h
    have hd := (ZMod.natCast_eq_zero_iff 2 p).mp h
    exact hodd ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp hd)
  have hbzero : (b i : ZMod p) = 0 := by
    exact sq_eq_zero_iff.mp (Or.resolve_left (mul_eq_zero.mp hzero) htwo)
  exact hunit ((ZMod.natCast_eq_zero_iff _ _).mp hbzero)

/-- Every positive split-prime power in one radius occurs in one or two other
coordinates, counting equal radii separately. -/
theorem result (r : Fin 4 → ℕ) (hpos : ∀ i, 0 < r i)
    (hprim : gcd4 r = 1) (hdesc : sphereDescartes r)
    (p : ℕ) (hp : p.Prime) (hsplit : p % 3 = 1)
    (k : ℕ) (hk : 0 < k) (i : Fin 4) (hi : p ^ k ∣ r i) :
    (univ.filter fun j => j ≠ i ∧ p ^ k ∣ r j).card = 1 ∨
    (univ.filter fun j => j ≠ i ∧ p ^ k ∣ r j).card = 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hodd : p ≠ 2 := by intro h; subst p; norm_num at hsplit
  obtain ⟨j, hji, hj⟩ := other_curvature_unit (curvature r)
    (curvature_primitive r hpos) (curvature_equation r hpos hdesc) p hp hodd i
  have hval (a : Fin 4) :
      padicValNat p (curvature r a) + padicValNat p (r a) =
        padicValNat p (commonMultiple r) := by
    rw [← padicValNat.mul (curvature_pos r hpos a).ne' (hpos a).ne',
      curvature_mul_radius]
  have hjval := padicValNat.eq_zero_of_not_dvd hj
  have hle : padicValNat p (r i) ≤ padicValNat p (r j) := by
    have := hval i
    have := hval j
    omega
  have hjk : p ^ k ∣ r j := (padicValNat_dvd_iff_le (hpos j).ne').mpr
    (((padicValNat_dvd_iff_le (hpos i).ne').mp hi).trans hle)
  let t := univ.filter fun a => p ^ k ∣ r a
  have hit : i ∈ t := mem_filter.mpr ⟨mem_univ i, hi⟩
  have hjt : j ∈ t := mem_filter.mpr ⟨mem_univ j, hjk⟩
  have hlow : 2 ≤ t.card := by
    have hsub : {i, j} ⊆ t := by simp only [insert_subset_iff, singleton_subset_iff]; exact ⟨hit, hjt⟩
    have := card_le_card hsub
    simpa [hji, Ne.symm hji] using this
  have hnotall : ∃ a, ¬p ^ k ∣ r a := by
    by_contra! hall
    have hd : p ∣ gcd4 r := Finset.dvd_gcd fun a _ =>
      (dvd_pow_self p (by omega : k ≠ 0)).trans (hall a)
    rw [hprim] at hd
    exact hp.not_dvd_one hd
  obtain ⟨a, ha⟩ := hnotall
  have hupp : t.card < 4 := by
    have hstrict : t ⊂ univ := Finset.ssubset_iff_subset_ne.mpr ⟨filter_subset _ _, by
      intro he
      have : a ∈ t := he.symm ▸ mem_univ a
      exact ha (mem_filter.mp this).2⟩
    simpa using card_lt_card hstrict
  have hcount : (univ.filter fun j => j ≠ i ∧ p ^ k ∣ r j).card = t.card - 1 := by
    have he : (univ.filter fun j => j ≠ i ∧ p ^ k ∣ r j) = t.erase i := by
      ext j
      simp only [mem_filter, mem_univ, true_and, mem_erase, t]
    rw [he, card_erase_of_mem hit]
  omega

#print axioms result

end D5.S3.Arith.Descartes.SplitPrimeSphereRadii
