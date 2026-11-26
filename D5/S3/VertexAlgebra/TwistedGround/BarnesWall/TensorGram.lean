/- GID: D5/S3/VertexAlgebra/TwistedGround/BarnesWall/TensorGram
   generality: I
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The normalized tensor rows realize the Barnes–Wall Gram and its mod-two half form. -/

import D5.S3.VertexAlgebra.TwistedGround.BarnesWall.TensorSubsetRows
import Mathlib.Data.Finset.Powerset

/-! The Gram matrix of the KRR tensor basis (arXiv:2411.13646v2,
Appendix A.1), in the word coordinates used for the Pauli action. -/

open scoped BigOperators
set_option autoImplicit false

namespace D5.S3.VertexAlgebra.TwistedGround.BarnesWall.TensorGram

open LatticeTwistedGroundRealization.SignQuotient (F₂)
open TailPauliPairing (Word complement pairing parity)
open TensorSubsetRows (included subsetRow falseCount rowScale scaledRow)

noncomputable section

variable {ι : Type} [Fintype ι] [LinearOrder ι]

def meet (u v : Word ι) : Word ι := fun r => u r && v r

def support (u : Word ι) : Finset ι := Finset.univ.filter fun r => u r = true

def sublabels (u : Word ι) : Finset (Word ι) := by
  classical
  exact Finset.univ.filter fun k => included u k

private theorem mem_sublabels (u k : Word ι) : k ∈ sublabels u ↔ included u k := by
  simp [sublabels]

private theorem included_meet (u v k : Word ι) :
    included (meet u v) k ↔ included u k ∧ included v k := by
  simp only [included, meet, Bool.and_eq_true]
  constructor
  · intro h
    exact ⟨fun r hr => (h r hr).1, fun r hr => (h r hr).2⟩
  · rintro ⟨hu, hv⟩ r hr
    exact ⟨hu r hr, hv r hr⟩

private theorem included_iff_support_subset (u k : Word ι) :
    included u k ↔ support k ⊆ support u := by
  simp only [included, Finset.subset_iff, support, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The column labels on a subset row are the subsets of its true slots. -/
theorem card_sublabels (u : Word ι) : (sublabels u).card = 2 ^ (support u).card := by
  classical
  rw [← Finset.card_powerset]
  refine Finset.card_bij (fun k _ => support k) ?_ ?_ ?_
  · intro k hk
    exact Finset.mem_powerset.mpr ((included_iff_support_subset u k).mp ((mem_sublabels u k).mp hk))
  · intro k _ l _ hkl
    funext r
    have hr : k r = true ↔ l r = true := by
      have hmem : r ∈ support k ↔ r ∈ support l := by rw [hkl]
      simpa only [support, Finset.mem_filter, Finset.mem_univ, true_and] using hmem
    cases hk : k r <;> cases hl : l r <;> simp_all
  · intro s hs
    let k : Word ι := fun r => decide (r ∈ s)
    have hk : support k = s := by
      ext r
      simp [support, k]
    have hku : included u k := (included_iff_support_subset u k).mpr (by
      rw [hk]
      exact Finset.mem_powerset.mp hs)
    exact ⟨k, (mem_sublabels u k).mpr hku, hk⟩

/-- In (A.1.1) the tensor factors supply `falseCount u` powers of `√2`,
and the zero-slot parity rounds that exponent up to the next even integer.
This is the exponent of two already used by `TensorSubsetRows.rowScale`. -/
def fullRowExponent (u : Word ι) : ℕ := (falseCount u + 1) / 2

def rawGramExponent (u v : Word ι) : ℕ :=
  fullRowExponent u + fullRowExponent v + (support (meet u v)).card

/-- Both subset indicators are one exactly at the sublabels of the meet. -/
theorem dotProduct_scaledRow (u v : Word ι) :
    (∑ k : Word ι, scaledRow u k * scaledRow v k) = (2 : ℚ) ^ rawGramExponent u v := by
  classical
  calc
    _ = ∑ k : Word ι, if included (meet u v) k then rowScale u * rowScale v else 0 := by
      apply Finset.sum_congr rfl
      intro k _
      by_cases hu : included u k <;> by_cases hv : included v k <;>
        simp [scaledRow, subsetRow, included_meet, hu, hv]
    _ = ((sublabels (meet u v)).card : ℚ) * (rowScale u * rowScale v) := by
      unfold sublabels
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    _ = _ := by
      rw [card_sublabels]
      simp only [Nat.cast_pow, Nat.cast_ofNat, rawGramExponent, fullRowExponent, rowScale, pow_add]
      ring

def hammingDistance (u v : Word ι) : ℕ := (Finset.univ.filter fun r => u r ≠ v r).card

private theorem card_filter_eq_sum (p : ι → Prop) [DecidablePred p] :
    (Finset.univ.filter p).card = ∑ r, if p r then 1 else 0 := by
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]

private theorem slot_count (u v : Word ι) :
    falseCount u + falseCount v + 2 * (support (meet u v)).card + hammingDistance u v =
      2 * Fintype.card ι := by
  simp only [falseCount, support, hammingDistance, card_filter_eq_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  calc
    _ = ∑ _ : ι, (2 : ℕ) := by
      apply Finset.sum_congr rfl
      intro r _
      cases hu : u r <;> cases hv : v r <;> simp [meet, hu, hv]
    _ = _ := by simp [nsmul_eq_mul, mul_comm]

private theorem distance_le_card (u v : Word ι) :
    hammingDistance u v ≤ Fintype.card ι := Finset.card_le_univ _

private theorem distance_eq_card_iff (u v : Word ι) :
    hammingDistance u v = Fintype.card ι ↔ v = complement u := by
  rw [hammingDistance, Finset.card_eq_iff_eq_univ]
  constructor
  · intro h
    funext r
    have hr : r ∈ Finset.univ.filter (fun r => u r ≠ v r) := by
      rw [h]
      exact Finset.mem_univ r
    have hne := (Finset.mem_filter.mp hr).2
    cases hu : u r <;> cases hv : v r <;> simp_all [complement]
  · rintro rfl
    ext r
    cases hu : u r <;> simp [complement, hu]

private theorem falseCount_complement_add (u : Word ι) :
    falseCount u + falseCount (complement u) = Fintype.card ι := by
  simp only [falseCount, card_filter_eq_sum, ← Finset.sum_add_distrib]
  calc
    _ = ∑ _ : ι, (1 : ℕ) := by
      apply Finset.sum_congr rfl
      intro r _
      cases hu : u r <;> simp [complement, hu]
    _ = _ := by simp

private theorem card_mod_two (hodd : (Fintype.card ι : F₂) = 1) : Fintype.card ι % 2 = 1 := by
  have h := hodd
  rw [← ZMod.natCast_mod (Fintype.card ι) 2] at h
  by_contra hn
  have hz : Fintype.card ι % 2 = 0 := by omega
  simp [hz] at h

private theorem falseCount_mod_two_eq_one_iff (hodd : (Fintype.card ι : F₂) = 1) (u : Word ι) :
    falseCount u % 2 = 1 ↔ parity u = 0 := by
  have hsum : (falseCount u : F₂) + parity u = (Fintype.card ι : F₂) := by
    simp only [falseCount, card_filter_eq_sum, Nat.cast_sum, parity, ← Finset.sum_add_distrib]
    calc
      _ = ∑ _ : ι, (1 : F₂) := by
        apply Finset.sum_congr rfl
        intro r _
        cases hu : u r <;> simp [hu]
      _ = _ := by simp
  rw [hodd, ← ZMod.natCast_mod (falseCount u) 2] at hsum
  rcases (show falseCount u % 2 = 0 ∨ falseCount u % 2 = 1 by omega) with hz | ho
  · have hp : parity u = 1 := by simpa [hz] using hsum
    simp [hz, hp]
  · have h : (1 : F₂) + parity u = 1 := by simpa [ho] using hsum
    have hp : parity u = 0 := add_left_cancel (h.trans (add_zero (1 : F₂)).symm)
    simp [ho, hp]

/-- The KRR overall row factor is `2 ^ (-(m+1)/4)` for odd `m`.
Its square divides every unnormalized inner product by `2 ^ ((m+1)/2)`.
At `m = 7` this is the denominator `16` in `Rank128Lattice`. The scale
is applied to the inner product so it stays rational. -/
def normalizationExponent : ℕ := (Fintype.card ι + 1) / 2

def gramExponent (u v : Word ι) : ℕ := rawGramExponent u v - normalizationExponent (ι := ι)

private theorem twice_fullRowExponent (u : Word ι) :
    2 * fullRowExponent u = falseCount u + falseCount u % 2 := by
  unfold fullRowExponent
  omega

private theorem twice_normalizationExponent (hodd : (Fintype.card ι : F₂) = 1) :
    2 * normalizationExponent (ι := ι) = Fintype.card ι + 1 := by
  have hm := card_mod_two hodd
  unfold normalizationExponent
  omega

theorem gramExponent_add_normalization (hodd : (Fintype.card ι : F₂) = 1) (u v : Word ι) :
    gramExponent u v + normalizationExponent (ι := ι) = rawGramExponent u v := by
  have hcount := slot_count u v
  have hdist := distance_le_card u v
  have hnorm := twice_normalizationExponent hodd
  have hu := twice_fullRowExponent u
  have hv := twice_fullRowExponent v
  unfold gramExponent rawGramExponent
  omega

/-- Twice the Gram exponent plus the Hamming distance is
`m - 1 + δu + δv`, with `δu` the parity of the zero slots.
The displayed form avoids a truncated subtraction at complementary words. -/
theorem gramExponent_distance (hodd : (Fintype.card ι : F₂) = 1) (u v : Word ι) :
    2 * gramExponent u v + hammingDistance u v + 1 =
      Fintype.card ι + falseCount u % 2 + falseCount v % 2 := by
  have hcount := slot_count u v
  have hexp := gramExponent_add_normalization hodd u v
  have hnorm := twice_normalizationExponent hodd
  have hu := twice_fullRowExponent u
  have hv := twice_fullRowExponent v
  unfold rawGramExponent at hexp
  omega

/-- The integral entries of the normalized KRR Gram at odd slot count. -/
def gram (u v : Word ι) : ℤ := 2 ^ gramExponent u v

theorem gram_eq_normalized_dotProduct (hodd : (Fintype.card ι : F₂) = 1) (u v : Word ι) :
    (gram u v : ℚ) = (∑ k : Word ι, scaledRow u k * scaledRow v k) /
      (2 : ℚ) ^ normalizationExponent (ι := ι) := by
  have hden : (2 : ℚ) ^ normalizationExponent (ι := ι) ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [dotProduct_scaledRow, ← gramExponent_add_normalization hodd u v, pow_add,
    mul_div_cancel_right₀ _ hden]
  simp [gram]

theorem gram_comm (u v : Word ι) : gram u v = gram v u := by
  have hmeet : meet v u = meet u v := by
    funext r
    exact Bool.and_comm _ _
  unfold gram gramExponent rawGramExponent
  rw [hmeet, add_comm (fullRowExponent u) (fullRowExponent v)]

/-- In addition to the complement entries, two odd-weight words at distance
`m - 1` have odd Gram entry. The second case is the `G²` term of KRR Lemma A.1. -/
theorem gramExponent_eq_zero_iff (hodd : (Fintype.card ι : F₂) = 1) (u v : Word ι) :
    gramExponent u v = 0 ↔ v = complement u ∨
      (hammingDistance u v + 1 = Fintype.card ι ∧ falseCount u % 2 = 0 ∧ falseCount v % 2 = 0) := by
  have hcount := gramExponent_distance hodd u v
  have hdle := distance_le_card u v
  have hdcomp := distance_eq_card_iff u v
  constructor
  · intro hz
    by_cases hfull : hammingDistance u v = Fintype.card ι
    · exact Or.inl (hdcomp.mp hfull)
    · exact Or.inr ⟨by omega, by omega, by omega⟩
  · rintro (hc | ⟨hd, hu, hv⟩)
    · have hd := hdcomp.mpr hc
      have hf := falseCount_complement_add u
      rw [← hc] at hf
      have hmod := congrArg (fun n : ℕ => n % 2) hf
      change (falseCount u + falseCount v) % 2 = Fintype.card ι % 2 at hmod
      rw [Nat.add_mod, card_mod_two hodd] at hmod
      omega
    · omega

private theorem cast_two_pow (n : ℕ) : (((2 : ℤ) ^ n : ℤ) : F₂) = if n = 0 then 1 else 0 := by
  rw [Int.cast_pow, show (((2 : ℤ) : F₂)) = 0 by decide]
  cases n <;> simp

theorem gram_mod_two (u v : Word ι) : (gram u v : F₂) = if gramExponent u v = 0 then 1 else 0 :=
  cast_two_pow _

/-- The mod-two Gram against any even-weight label is the complement pairing. -/
theorem gram_mod_two_of_even_right (hodd : (Fintype.card ι : F₂) = 1) (u v : Word ι)
    (hv : parity v = 0) : (gram u v : F₂) = pairing u v := by
  classical
  have hv' := (falseCount_mod_two_eq_one_iff hodd v).mpr hv
  simp [gram_mod_two, pairing, gramExponent_eq_zero_iff hodd u v, hv']

theorem gram_mod_two_of_even_even (hodd : (Fintype.card ι : F₂) = 1) (u v : Word ι)
    (hu : parity u = 0) (hv : parity v = 0) : (gram u v : F₂) = 0 := by
  have hcount := gramExponent_distance hodd u v
  have hdle := distance_le_card u v
  have hu' := (falseCount_mod_two_eq_one_iff hodd u).mpr hu
  have hv' := (falseCount_mod_two_eq_one_iff hodd v).mpr hv
  rw [gram_mod_two, if_neg (show gramExponent u v ≠ 0 by omega)]

theorem gramExponent_self (hodd : (Fintype.card ι : F₂) = 1) (u : Word ι) :
    gramExponent u u = (Fintype.card ι - 1) / 2 + falseCount u % 2 := by
  have h := gramExponent_distance hodd u u
  have hm := card_mod_two hodd
  have hd : hammingDistance u u = 0 := by simp [hammingDistance]
  omega

private theorem gram_diagonal_factor (hodd : (Fintype.card ι : F₂) = 1)
    (hm : 3 ≤ Fintype.card ι) (u : Word ι) : gram u u = 2 ^ (gramExponent u u - 1) * 2 := by
  have h := gramExponent_self hodd u
  have he : gramExponent u u - 1 + 1 = gramExponent u u := by omega
  change (2 : ℤ) ^ gramExponent u u = _
  rw [← pow_succ, he]

theorem gram_diagonal_even (hodd : (Fintype.card ι : F₂) = 1)
    (hm : 3 ≤ Fintype.card ι) (u : Word ι) : (2 : ℤ) ∣ gram u u :=
  ⟨2 ^ (gramExponent u u - 1), (gram_diagonal_factor hodd hm u).trans (mul_comm _ _)⟩

private theorem distance_le_two (r s : ι) (u v : Word ι)
    (h : ∀ t, t ≠ r → t ≠ s → u t = v t) : hammingDistance u v ≤ 2 := by
  have hsub : (Finset.univ.filter fun t => u t ≠ v t) ⊆ ({r, s} : Finset ι) := by
    intro t ht
    have hne := (Finset.mem_filter.mp ht).2
    by_cases hr : t = r
    · simp [hr]
    · by_cases hs : t = s
      · simp [hs]
      · exact (hne (h t hr hs)).elim
  exact (Finset.card_le_card hsub).trans Finset.card_le_two

variable [order : LinearOrder (Word ι)]

local notation:50 x " ≺ " y => @LT.lt (Word ι) order.toLT x y

/-- KRR's lower-triangular half Gram, with the integral diagonal divided
before reduction, as in `Rank128Lattice.lowerMatrix_mod_two`. -/
def halfGram : Matrix (Word ι) (Word ι) F₂ := fun u v =>
  (((@ite ℤ (v ≺ u) (order.toDecidableLT v u) (gram u v) 0) + (if v = u then gram u u / 2 else 0) : ℤ) : F₂)

theorem halfGram_symmetrize (hodd : (Fintype.card ι : F₂) = 1)
    (hm : 3 ≤ Fintype.card ι) (u v : Word ι) :
    halfGram u v + halfGram v u = (gram u v : F₂) := by
  rcases lt_trichotomy u v with h | rfl | h
  · have hn : ¬ (v ≺ u) := @not_lt_of_gt _ order.toPreorder _ _ h
    have hne : u ≠ v := @ne_of_lt _ order.toPreorder _ _ h
    simp [halfGram, h, hn, hne, hne.symm, gram_comm v u]
  · have hd := gramExponent_self hodd u
    rw [CharTwo.add_self_eq_zero, gram_mod_two, if_neg (show gramExponent u u ≠ 0 by omega)]
  · have hn : ¬ (u ≺ v) := @not_lt_of_gt _ order.toPreorder _ _ h
    have hne : v ≠ u := @ne_of_lt _ order.toPreorder _ _ h
    simp [halfGram, h, hn, hne, hne.symm]

/-- Holding every slot except `r` and `s` fixed makes the half Gram zero,
including the halved integral diagonal. -/
theorem halfGram_eq_zero_of_agree_outside (hodd : (Fintype.card ι : F₂) = 1)
    (hm : 5 ≤ Fintype.card ι) (r s : ι) (u v : Word ι)
    (h : ∀ t, t ≠ r → t ≠ s → u t = v t) : halfGram u v = 0 := by
  by_cases huv : v = u
  · subst v
    have hd := gramExponent_self hodd u
    have hn : gramExponent u u - 1 ≠ 0 := by omega
    have hirr : ¬ (u ≺ u) := @lt_irrefl _ order.toPreorder u
    simp only [halfGram, hirr, ite_false, ite_true, zero_add]
    rw [gram_diagonal_factor hodd (by omega) u, Int.mul_ediv_cancel _ (by decide : (2 : ℤ) ≠ 0),
      cast_two_pow, if_neg hn]
  · have hd := distance_le_two r s u v h
    have hcount := gramExponent_distance hodd u v
    have hn : gramExponent u v ≠ 0 := by omega
    by_cases hlt : v ≺ u <;> simp [halfGram, huv, hlt, gram_mod_two, hn]

/-- The corresponding bilinear form vanishes on vectors supported in any
one block with all slots outside `r` and `s` fixed. -/
theorem halfGram_bilin_eq_zero_on_block (hodd : (Fintype.card ι : F₂) = 1)
    (hm : 5 ≤ Fintype.card ι) (r s : ι) (w : Word ι) (a b : Word ι → F₂)
    (ha : ∀ u, a u ≠ 0 → ∀ t, t ≠ r → t ≠ s → u t = w t)
    (hb : ∀ v, b v ≠ 0 → ∀ t, t ≠ r → t ≠ s → v t = w t) :
    halfGram.toBilin' a b = 0 := by
  rw [Matrix.toBilin'_apply]
  apply Finset.sum_eq_zero
  intro u _
  apply Finset.sum_eq_zero
  intro v _
  by_cases hu : a u = 0
  · simp [hu]
  · by_cases hv : b v = 0
    · simp [hv]
    · have h : ∀ t, t ≠ r → t ≠ s → u t = v t :=
        fun t hr hs => (ha u hu t hr hs).trans (hb v hv t hr hs).symm
      simp [halfGram_eq_zero_of_agree_outside hodd hm r s u v h]

end
end D5.S3.VertexAlgebra.TwistedGround.BarnesWall.TensorGram
