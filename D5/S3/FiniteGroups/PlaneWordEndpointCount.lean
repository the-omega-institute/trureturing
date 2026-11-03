/- GID: D5/S3/FiniteGroups/PlaneWordEndpointCount
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/PlaneWordEndpointCount
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Data.Fintype.Powerset]
   utility: none
   digest: Signed coordinate words counted by two independent subset fibers. -/

import D5.S3.FiniteGroups.BajnokBeattyFirstReturnDefect
import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
The four coordinate steps become the four independent sign pairs after
the coordinate change (x,y) ↦ (x+y,x-y).  A word is consequently equivalent
to two subsets of its positions.  The existing Mathlib fixed-cardinality
subset count supplies the binomial coefficients.

The endpoint fiber equivalence is the content used by the short-return-band
consumer.  No novelty claim is made for this classical square-lattice count.
Other declarations are consumed implementation helpers; the rotated endpoint identity is also reused by the first-reversal proof.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace D5.S3.FiniteGroups.PlaneWordEndpointCount

open D5.S3.FiniteGroups.NearSquareLatticeRigidity (Plane)
open D5.S3.FiniteGroups.BajnokBeattyFirstReturnDefect (step endpoint)

private def negativeU {L : ℕ} (w : Fin L → Fin 4) : Finset (Fin L) :=
  Finset.univ.filter fun i => w i = 1 ∨ w i = 3

private def negativeV {L : ℕ} (w : Fin L → Fin 4) : Finset (Fin L) :=
  Finset.univ.filter fun i => w i = 1 ∨ w i = 2

private def decodeWord {L : ℕ} (s t : Finset (Fin L)) : Fin L → Fin 4 :=
  fun i => if i ∈ s then (if i ∈ t then 1 else 3)
    else (if i ∈ t then 2 else 0)

private def wordSubsetEquiv (L : ℕ) :
    (Fin L → Fin 4) ≃ Finset (Fin L) × Finset (Fin L) where
  toFun w := (negativeU w, negativeV w)
  invFun st := decodeWord st.1 st.2
  left_inv := by
    intro w
    funext i
    change decodeWord (negativeU w) (negativeV w) i = w i
    simp only [decodeWord, negativeU, negativeV, Finset.mem_filter,
      Finset.mem_univ, true_and]
    generalize w i = a
    fin_cases a <;> norm_num
  right_inv := by
    rintro ⟨s, t⟩
    change (negativeU (decodeWord s t), negativeV (decodeWord s t)) = (s, t)
    apply Prod.ext
    · apply Finset.ext
      intro i
      simp only [negativeU, Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases hs : i ∈ s <;> by_cases ht : i ∈ t <;>
        simp [decodeWord, hs, ht]
    · apply Finset.ext
      intro i
      simp only [negativeV, Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases hs : i ∈ s <;> by_cases ht : i ∈ t <;>
        simp [decodeWord, hs, ht]

private lemma sum_signs {L : ℕ} (s : Finset (Fin L)) :
    (∑ i : Fin L, (1 - 2 * (if i ∈ s then 1 else 0) : ℤ)) =
      (L : ℤ) - 2 * (s.card : ℤ) := by
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp

private lemma decoded_rotated_endpoint {L : ℕ} (s t : Finset (Fin L)) :
    endpoint (decodeWord s t) 0 + endpoint (decodeWord s t) 1 =
      (L : ℤ) - 2 * (s.card : ℤ) ∧
    endpoint (decodeWord s t) 0 - endpoint (decodeWord s t) 1 =
      (L : ℤ) - 2 * (t.card : ℤ) := by
  constructor
  · calc
      endpoint (decodeWord s t) 0 + endpoint (decodeWord s t) 1 =
          ∑ i : Fin L, (step (decodeWord s t i) 0 +
            step (decodeWord s t i) 1) := by
              simp only [endpoint, Finset.sum_apply, Finset.sum_add_distrib]
      _ = ∑ i : Fin L, (1 - 2 * (if i ∈ s then 1 else 0) : ℤ) := by
        apply Finset.sum_congr rfl
        intro i hi
        by_cases hs : i ∈ s <;> by_cases ht : i ∈ t <;>
          simp [decodeWord, step, hs, ht]
      _ = (L : ℤ) - 2 * (s.card : ℤ) := sum_signs s
  · calc
      endpoint (decodeWord s t) 0 - endpoint (decodeWord s t) 1 =
          ∑ i : Fin L, (step (decodeWord s t i) 0 -
            step (decodeWord s t i) 1) := by
              simp only [endpoint, Finset.sum_apply, Finset.sum_sub_distrib]
      _ = ∑ i : Fin L, (1 - 2 * (if i ∈ t then 1 else 0) : ℤ) := by
        apply Finset.sum_congr rfl
        intro i hi
        by_cases hs : i ∈ s <;> by_cases ht : i ∈ t <;>
          simp [decodeWord, step, hs, ht]
      _ = (L : ℤ) - 2 * (t.card : ℤ) := sum_signs t

lemma rotated_endpoint {L : ℕ} (w : Fin L → Fin 4) :
    endpoint w 0 + endpoint w 1 =
      (L : ℤ) - 2 * ((negativeU w).card : ℤ) ∧
    endpoint w 0 - endpoint w 1 =
      (L : ℤ) - 2 * ((negativeV w).card : ℤ) := by
  have hinv : decodeWord (negativeU w) (negativeV w) = w :=
    (wordSubsetEquiv L).left_inv w
  have h := decoded_rotated_endpoint (negativeU w) (negativeV w)
  rwa [hinv] at h

private def endpointFiberEquiv (L a b : ℕ) (x y : ℤ)
    (hx : (L : ℤ) - 2 * (a : ℤ) = x + y)
    (hy : (L : ℤ) - 2 * (b : ℤ) = x - y) :
    {w : Fin L → Fin 4 // endpoint w = ![x, y]} ≃
      {s : Finset (Fin L) // s.card = a} ×
      {t : Finset (Fin L) // t.card = b} := by
  have hpred (w : Fin L → Fin 4) :
      endpoint w = ![x, y] ↔
        (negativeU w).card = a ∧ (negativeV w).card = b := by
    obtain ⟨hu, hv⟩ := rotated_endpoint w
    constructor
    · intro hw
      have h0 := congrFun hw 0
      have h1 := congrFun hw 1
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
      constructor <;> omega
    · rintro ⟨ha, hb⟩
      ext i
      fin_cases i
      · change endpoint w 0 = x
        omega
      · change endpoint w 1 = y
        omega
  exact ((wordSubsetEquiv L).subtypeEquiv hpred).trans
    Equiv.subtypeProdEquivProd

/-- The exact endpoint count for four signed coordinate steps.  No parity
or reachability premise is hidden: the two displayed integer equations are
the complete conversion from endpoint coordinates to the two subset sizes.
The formula remains valid when a size exceeds the word length, since the
corresponding fixed-size subset type and binomial coefficient are both empty.
-/
theorem endpoint_card (L a b : ℕ) (x y : ℤ)
    (hx : (L : ℤ) - 2 * (a : ℤ) = x + y)
    (hy : (L : ℤ) - 2 * (b : ℤ) = x - y) :
    Nat.card {w : Fin L → Fin 4 // endpoint w = ![x, y]} =
      Nat.choose L a * Nat.choose L b := by
  calc
    Nat.card {w : Fin L → Fin 4 // endpoint w = ![x, y]} =
        Nat.card ({s : Finset (Fin L) // s.card = a} ×
          {t : Finset (Fin L) // t.card = b}) :=
      Nat.card_congr (endpointFiberEquiv L a b x y hx hy)
    _ = Nat.choose L a * Nat.choose L b := by
      rw [Nat.card_prod]
      simp only [Nat.card_eq_fintype_card, Fintype.card_finset_len, Fintype.card_fin]

end D5.S3.FiniteGroups.PlaneWordEndpointCount
