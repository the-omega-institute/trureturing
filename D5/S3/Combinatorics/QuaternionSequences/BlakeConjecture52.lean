/- GID: D5/S3/Combinatorics/QuaternionSequences/BlakeConjecture52
   generality: G
   mirror-B: D5/B/S3/Combinatorics/QuaternionSequences/BlakeConjecture52
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Q₈ sequences of length ≥ 2 have nonzero off-period correlation for each Q₈ noncentral twist. -/

import OmegaBuild.Commands
import Mathlib.Algebra.QuaternionBasis
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Polynomial.Basic

compile_only_with_mathlib

/-! # Blake's noncentral twist conjecture -/

open scoped Quaternion BigOperators Polynomial
open Finset Polynomial

namespace D5.S3.Combinatorics.QuaternionSequences.BlakeConjecture52

private abbrev qi : ℍ[ℤ] := ⟨0, 1, 0, 0⟩
private abbrev qj : ℍ[ℤ] := ⟨0, 0, 1, 0⟩
private abbrev qk : ℍ[ℤ] := ⟨0, 0, 0, 1⟩

/-- The six noncentral elements of the Hamilton quaternion alphabet. -/
def Noncentral (u : ℍ[ℤ]) : Prop :=
  u = qi ∨ u = -qi ∨ u = qj ∨ u = -qj ∨ u = qk ∨ u = -qk

/-- The eight letters of Blake's alphabet, in integral Hamilton coordinates. -/
def IsQ8 (u : ℍ[ℤ]) : Prop := u = 1 ∨ u = -1 ∨ Noncentral u

private def twistUnit (u : ℍ[ℤ]) (hu : Noncentral u) : ℍ[ℤ]ˣ where
  val := u
  inv := star u
  val_inv := by
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals ext <;> decide
  inv_val := by
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals ext <;> decide

/-- For the Euclidean decomposition `n = qM + r`, return `s r * u ^ q`. -/
def extension {M : ℕ} (hM : 0 < M) (s : Fin M → ℍ[ℤ])
    (u : ℍ[ℤ]) (hu : Noncentral u) (n : ℤ) : ℍ[ℤ] :=
  s ⟨(n % (M : ℤ)).toNat, by
    have hpos : (0 : ℤ) < M := by exact_mod_cast hM
    have h₁ := Int.emod_nonneg n hpos.ne'
    have h₂ := Int.emod_lt_of_pos n hpos
    omega⟩ * ↑(twistUnit u hu ^ (n / (M : ℤ)))

/-- The literal twisted autocorrelation with Blake's order of the quaternion factors. -/
def correlation {M : ℕ} (hM : 0 < M) (s : Fin M → ℍ[ℤ])
    (u : ℍ[ℤ]) (hu : Noncentral u) (τ : ℤ) : ℍ[ℤ] :=
  ∑ r : Fin M, s r * star (extension hM s u hu ((r.val : ℤ) + τ))

private theorem extension_at {M : ℕ} (hM : 0 < M) (s : Fin M → ℍ[ℤ])
    (u : ℍ[ℤ]) (hu : Noncentral u) (q : ℤ) (r : Fin M) :
    extension hM s u hu (q * (M : ℤ) + r.val) = s r * ↑(twistUnit u hu ^ q) := by
  have hpos : (0 : ℤ) < M := by exact_mod_cast hM
  obtain ⟨hq, hr⟩ := (Int.ediv_emod_unique (r := (r.val : ℤ)) (q := q)
    (a := q * (M : ℤ) + (r.val : ℤ)) hpos).2
    ⟨by ring, by omega, by exact_mod_cast r.isLt⟩
  simp only [extension, hq, hr, Int.toNat_natCast]

private theorem extension_add {M : ℕ} [NeZero M] (hM : 0 < M)
    (s : Fin M → ℍ[ℤ]) (u : ℍ[ℤ]) (hu : Noncentral u) (r τ : Fin M) :
    extension hM s u hu ((r.val : ℤ) + τ.val) =
      s (r + τ) * (if M ≤ r.val + τ.val then u else 1) := by
  split_ifs with h
  · have hwrap : (r.val : ℤ) + τ.val = (1 : ℤ) * M + (r + τ).val := by
      rw [Fin.val_add_eq_ite, ite_eq_left h]
      omega
    rw [hwrap, extension_at]
    simp [twistUnit]
  · have hplain : (r.val : ℤ) + τ.val = (0 : ℤ) * M + (r + τ).val := by
      rw [Fin.val_add_eq_ite, ite_eq_right h]
      omega
    rw [hplain, extension_at]
    simp

section Character

variable {R : Type*} [CommRing R]

private theorem neg_eq_of_two_zero (h₂ : (2 : R) = 0) (x : R) : -x = x := by
  rw [neg_eq_iff_add_eq_zero, ← two_mul, h₂, zero_mul]

private def characterBasis (h₂ : (2 : R) = 0) (V : R) (hV : V * V = 1)
    (second : Bool) : QuaternionAlgebra.Basis R (-1 : ℤ) 0 (-1) where
  i := if second then 1 else V
  j := if second then V else 1
  k := V
  i_mul_i := by cases second <;> simp [hV, neg_eq_of_two_zero h₂]
  j_mul_j := by cases second <;> simp [hV, neg_eq_of_two_zero h₂]
  i_mul_j := by cases second <;> simp
  j_mul_i := by cases second <;> simp [neg_eq_of_two_zero h₂]

private abbrev character (h₂ : (2 : R) = 0) (V : R) (hV : V * V = 1)
    (second : Bool) : ℍ[ℤ] →+* R :=
  (characterBasis h₂ V hV second).liftHom.toRingHom

private theorem character_star (h₂ : (2 : R) = 0) (V : R) (hV : V * V = 1)
    (second : Bool) (x : ℍ[ℤ]) :
    character h₂ V hV second (star x) = character h₂ V hV second x := by
  change (characterBasis h₂ V hV second).lift (star x) =
    (characterBasis h₂ V hV second).lift x
  simp [QuaternionAlgebra.Basis.lift, neg_eq_of_two_zero h₂]

private theorem character_letter (h₂ : (2 : R) = 0) (V : R) (hV : V * V = 1)
    (second : Bool) {x : ℍ[ℤ]} (hx : IsQ8 x) :
    character h₂ V hV second x = 1 ∨ character h₂ V hV second x = V := by
  have hi : character h₂ V hV second qi = if second then 1 else V := by
    change (characterBasis h₂ V hV second).lift qi = _
    simp [QuaternionAlgebra.Basis.lift, characterBasis]
  have hj : character h₂ V hV second qj = if second then V else 1 := by
    change (characterBasis h₂ V hV second).lift qj = _
    simp [QuaternionAlgebra.Basis.lift, characterBasis]
  have hk : character h₂ V hV second qk = V := by
    change (characterBasis h₂ V hV second).lift qk = _
    simp [QuaternionAlgebra.Basis.lift, characterBasis]
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    cases second <;>
      simp only [map_one, map_neg, hi, hj, hk, neg_eq_of_two_zero h₂,
        Bool.false_eq_true, ite_false, ite_true, true_or, or_true]

private theorem character_twist (h₂ : (2 : R) = 0) (V : R) (hV : V * V = 1)
    {u : ℍ[ℤ]} (hu : Noncentral u) :
    ∃ second, character h₂ V hV second u = V := by
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨false, ?_⟩
    change (characterBasis h₂ V hV false).lift qi = V
    simp [QuaternionAlgebra.Basis.lift, characterBasis]
  · refine ⟨false, ?_⟩
    rw [map_neg, neg_eq_of_two_zero h₂]
    change (characterBasis h₂ V hV false).lift qi = V
    simp [QuaternionAlgebra.Basis.lift, characterBasis]
  · refine ⟨true, ?_⟩
    change (characterBasis h₂ V hV true).lift qj = V
    simp [QuaternionAlgebra.Basis.lift, characterBasis]
  · refine ⟨true, ?_⟩
    rw [map_neg, neg_eq_of_two_zero h₂]
    change (characterBasis h₂ V hV true).lift qj = V
    simp [QuaternionAlgebra.Basis.lift, characterBasis]
  · refine ⟨false, ?_⟩
    change (characterBasis h₂ V hV false).lift qk = V
    simp [QuaternionAlgebra.Basis.lift, characterBasis]
  · refine ⟨false, ?_⟩
    rw [map_neg, neg_eq_of_two_zero h₂]
    change (characterBasis h₂ V hV false).lift qk = V
    simp [QuaternionAlgebra.Basis.lift, characterBasis]

private theorem map_correlation {M : ℕ} [NeZero M] (hM : 0 < M)
    (s : Fin M → ℍ[ℤ]) (u : ℍ[ℤ]) (hu : Noncentral u)
    (φ : ℍ[ℤ] →+* R) (hstar : ∀ x, φ (star x) = φ x)
    (τ : Fin M) :
    φ (correlation hM s u hu τ.val) =
      ∑ r : Fin M, φ (s r) * φ (s (r + τ)) *
        (if M ≤ r.val + τ.val then φ u else 1) := by
  rw [correlation, map_sum]
  apply sum_congr rfl
  intro r _
  rw [extension_add, star_mul, map_mul, map_mul, hstar, hstar]
  split_ifs <;> simp [mul_comm, mul_left_comm]

end Character

/-- Group the product by the cyclic difference of the two indices. -/
private theorem cyclic_product {R : Type*} [CommRing R] {M : ℕ} [NeZero M]
    (a : Fin M → R) {W V : R} (hW : W ^ M = V) :
    (∑ r : Fin M, a r * W ^ r.val) *
        (∑ j : Fin M, a j * W ^ (M - 1 - j.val)) =
      ∑ τ : Fin M, (∑ r : Fin M, a r * a (r + τ) *
        (if M ≤ r.val + τ.val then V else 1)) * W ^ (M - 1 - τ.val) := by
  rw [sum_mul]
  simp_rw [mul_sum]
  calc
    _ = ∑ r : Fin M, ∑ τ : Fin M,
        (a r * W ^ r.val) * (a (r + τ) * W ^ (M - 1 - (r + τ).val)) := by
      apply sum_congr rfl
      intro r _
      exact Fintype.sum_equiv (Equiv.addLeft r).symm _ _ (by intro j; simp)
    _ = _ := by
      simp_rw [sum_mul]
      rw [sum_comm]
      apply sum_congr rfl
      intro τ _
      apply sum_congr rfl
      intro r _
      have hr := r.isLt
      have ht := τ.isLt
      calc
        _ = (a r * a (r + τ)) * W ^ (r.val + (M - 1 - (r + τ).val)) := by
          rw [pow_add]
          ring
        _ = _ := by
          rw [Fin.val_add_eq_ite]
          split_ifs with h
          · have he : r.val + (M - 1 - (r.val + τ.val - M)) = M + (M - 1 - τ.val) := by
              omega
            rw [he, pow_add, hW]
            simp only [mul_assoc]
          · have he : r.val + (M - 1 - (r.val + τ.val)) = M - 1 - τ.val := by omega
            rw [he, mul_one]

private abbrev Truncated (d : ℕ) :=
  (ZMod 2)[X] ⧸ Ideal.span ({(X : (ZMod 2)[X]) ^ (2 * d)} : Set (ZMod 2)[X])

private noncomputable abbrev truncate (d : ℕ) : (ZMod 2)[X] →+* Truncated d := Ideal.Quotient.mk _

private theorem truncate_pow {d k m M : ℕ} (hd : d = 2 ^ k) (hM : M = d * m)
    (hm : Odd m) :
    let W : Truncated d := truncate d (X + 1)
    let V : Truncated d := truncate d (X ^ d + 1)
    V * V = 1 ∧ W ^ M = V := by
  dsimp
  have hV : truncate d (X ^ d + 1) * truncate d (X ^ d + 1) = 1 := by
    rw [← map_mul]
    have he : (X ^ d + 1 : (ZMod 2)[X]) * (X ^ d + 1) = X ^ (2 * d) + 1 := by
      rw [← pow_two, add_sq, ← pow_mul, Nat.mul_comm d 2]
      rw [show (2 : (ZMod 2)[X]) = 0 from CharTwo.two_eq_zero]
      simp
    rw [he, map_add, Ideal.Quotient.mk_singleton_self, map_one, zero_add]
  refine ⟨hV, ?_⟩
  have hWd : truncate d (X + 1) ^ d = truncate d (X ^ d + 1) := by
    rw [← map_pow]
    congr 1
    rw [hd, add_pow_char_pow _ _ 2, one_pow]
  rw [hM, pow_mul, hWd]
  obtain ⟨b, hb⟩ := hm
  simp only [hb, pow_add, pow_mul, pow_two, hV, one_pow, one_mul, pow_one]

private theorem coeff_eq_of_truncate_eq {d : ℕ} {p q : (ZMod 2)[X]}
    (h : truncate d p = truncate d q) {j : ℕ} (hj : j < 2 * d) :
    p.coeff j = q.coeff j := by
  have hz : truncate d (p - q) = 0 := by rw [map_sub, h, sub_self]
  obtain ⟨b, hb⟩ := (Ideal.Quotient.eq_zero_iff_dvd _ _).1 hz
  have hc := congrArg (fun f : (ZMod 2)[X] => f.coeff j) hb
  rw [coeff_sub, coeff_X_pow_mul', ite_eq_right (by omega : ¬ 2 * d ≤ j)] at hc
  exact sub_eq_zero.mp hc

private theorem geom_coeff {M d : ℕ} (hd : 0 < d)
    (hW : truncate d (X + 1) ^ M = truncate d (X ^ d + 1))
    (j : ℕ) (hj : j < d) :
    (∑ r : Fin M, (X + 1 : (ZMod 2)[X]) ^ r.val).coeff j = if j = d - 1 then 1 else 0 := by
  let S : (ZMod 2)[X] := ∑ r : Fin M, (X + 1 : (ZMod 2)[X]) ^ r.val
  have hS : S * X + 1 = (X + 1) ^ M := by
    dsimp [S]
    rw [sum_fin_eq_sum_range]
    convert geom_sum_mul_add (X : (ZMod 2)[X]) M using 3
    exact sum_congr rfl (fun r hr => dite_eq_left (Finset.mem_range.mp hr))
  have ht : truncate d (S * X) = truncate d (X ^ d) := by
    apply add_right_cancel (b := 1)
    calc
      _ = truncate d (S * X + 1) := by rw [map_add, map_one]
      _ = truncate d (X ^ d + 1) := by rw [hS, map_pow, hW]
      _ = _ := by rw [map_add, map_one]
  have hc := coeff_eq_of_truncate_eq ht (j := j + 1) (by omega)
  rw [coeff_mul_X, coeff_X_pow] at hc
  have hj' : j + 1 = d ↔ j = d - 1 := by omega
  simpa only [hj'] using hc

private theorem lifted_coeff {M d : ℕ} (b : Fin M → (ZMod 2)[X]) (e : Equiv.Perm (Fin M))
    (j : ℕ) (hj : j < d) :
    (∑ r : Fin M, (1 + X ^ d * b r) * (X + 1) ^ (e r).val).coeff j =
      (∑ r : Fin M, (X + 1 : (ZMod 2)[X]) ^ r.val).coeff j := by
  rw [finsetSum_coeff, finsetSum_coeff]
  calc
    _ = ∑ r : Fin M, ((X + 1 : (ZMod 2)[X]) ^ (e r).val).coeff j := by
      apply sum_congr rfl
      intro r _
      rw [add_mul, one_mul, coeff_add, mul_assoc, coeff_X_pow_mul', ite_eq_right (by omega), add_zero]
    _ = _ := Equiv.sum_comp e (fun r : Fin M => ((X + 1 : (ZMod 2)[X]) ^ r.val).coeff j)

private theorem leading_product {p q : (ZMod 2)[X]} {d : ℕ} (hd : 0 < d)
    (hp : ∀ j < d, p.coeff j = if j = d - 1 then 1 else 0)
    (hq : ∀ j < d, q.coeff j = if j = d - 1 then 1 else 0) :
    (p * q).coeff (2 * d - 2) = 1 := by
  have hpne : p ≠ 0 := by
    intro hp0
    have hpc := hp (d - 1) (by omega)
    rw [hp0] at hpc
    simp at hpc
  have hqne : q ≠ 0 := by
    intro hq0
    have hqc := hq (d - 1) (by omega)
    rw [hq0] at hqc
    simp at hqc
  have hpdeg : p.natTrailingDegree = d - 1 := by
    apply le_antisymm
    · apply natTrailingDegree_le_of_ne_zero
      rw [hp (d - 1) (by omega)]
      simp
    · apply le_natTrailingDegree hpne
      intro j hj
      rw [hp j (by omega), ite_eq_right (by omega)]
  have hqdeg : q.natTrailingDegree = d - 1 := by
    apply le_antisymm
    · apply natTrailingDegree_le_of_ne_zero
      rw [hq (d - 1) (by omega)]
      simp
    · apply le_natTrailingDegree hqne
      intro j hj
      rw [hq j (by omega), ite_eq_right (by omega)]
  rw [show 2 * d - 2 = p.natTrailingDegree + q.natTrailingDegree by omega,
    coeff_mul_natTrailingDegree_add_natTrailingDegree]
  change p.coeff p.natTrailingDegree * q.coeff q.natTrailingDegree = 1
  rw [hpdeg, hqdeg, hp (d - 1) (by omega), hq (d - 1) (by omega)]
  simp

private theorem even_of_correlation_one_zero {M : ℕ} [NeZero M] (hM : 2 ≤ M)
    (s : Fin M → ℍ[ℤ]) (hs : ∀ r, IsQ8 (s r))
    (u : ℍ[ℤ]) (hu : Noncentral u)
    (hz : correlation (by omega) s u hu 1 = 0) : Even M := by
  let φ := character (R := ZMod 2) (by decide) 1 (one_mul 1) false
  have hφ {x : ℍ[ℤ]} (hx : IsQ8 x) : φ x = 1 :=
    (character_letter (by decide) 1 (one_mul 1) false hx).elim id id
  let τ : Fin M := ⟨1, by omega⟩
  have hsum := map_correlation (by omega) s u hu φ
    (character_star (by decide) 1 (one_mul 1) false) τ
  change φ (correlation (by omega) s u hu 1) = _ at hsum
  simp [hz, hφ (Or.inr (Or.inr hu)), fun r => hφ (hs r)] at hsum
  exact even_iff_two_dvd.mpr ((ZMod.natCast_eq_zero_iff M 2).mp hsum.symm)

/-- Every length at least two and every noncentral twist have a nonzero twisted
autocorrelation at an integer shift strictly between zero and the length. -/
theorem blake_conjecture_5_2 {M : ℕ} (hM : 2 ≤ M)
    (s : Fin M → ℍ[ℤ]) (hs : ∀ r, IsQ8 (s r))
    (u : ℍ[ℤ]) (hu : Noncentral u) :
    ∃ τ : ℤ, 0 < τ ∧ τ < (M : ℤ) ∧ ¬ ((M : ℤ) ∣ τ) ∧
      correlation (by omega) s u hu τ ≠ 0 := by
  classical
  let : NeZero M := ⟨by omega⟩
  have hpos : 0 < M := by omega
  by_contra! h
  have hz (τ : Fin M) (hτ : τ ≠ 0) : correlation hpos s u hu τ.val = 0 := by
    have hp : 0 < (τ.val : ℤ) := by
      by_contra! hp
      exact hτ (Fin.ext (by change τ.val = 0; omega))
    have hb : (τ.val : ℤ) < M := by exact_mod_cast τ.isLt
    apply h _ hp hb
    intro hdvd
    have he := Int.emod_eq_zero_of_dvd hdvd
    rw [Int.emod_eq_of_lt hp.le hb] at he
    omega
  have heven : Even M :=
    even_of_correlation_one_zero hM s hs u hu
      (hz ⟨1, by omega⟩ (by intro he; have := congrArg Fin.val he; contradiction))
  let d := 2 ^ M.factorization 2
  let m := M / d
  have hd : 0 < d := by dsimp [d]; positivity
  have hMdm : M = d * m := (Nat.ordProj_mul_ordCompl_eq_self M 2).symm
  have hm : Odd m := Nat.not_even_iff_odd.mp fun he =>
    Nat.not_dvd_ordCompl Nat.prime_two (NeZero.ne M) (even_iff_two_dvd.mp he)
  let W := truncate d (X + 1)
  let V := truncate d (X ^ d + 1)
  obtain ⟨hV, hW⟩ : V * V = 1 ∧ W ^ M = V := truncate_pow rfl hMdm hm
  have h₂ : (2 : Truncated d) = 0 := by
    rw [← map_ofNat (truncate d) 2, show (2 : (ZMod 2)[X]) = 0 from CharTwo.two_eq_zero, map_zero]
  have hMzero : (M : Truncated d) = 0 := by
    obtain ⟨b, hb⟩ := heven
    rw [hb, Nat.cast_add, ← two_mul, h₂, zero_mul]
  obtain ⟨second, hφu⟩ := character_twist h₂ V hV hu
  let φ := character h₂ V hV second
  let a : Fin M → Truncated d := fun r => φ (s r)
  have halphabet (r : Fin M) : a r = 1 ∨ a r = V := character_letter h₂ V hV second (hs r)
  have hasq (r : Fin M) : a r * a r = 1 := by
    rcases halphabet r with hr | hr
    · rw [hr, one_mul]
    · rw [hr, hV]
  have hprod :
      (∑ r : Fin M, a r * W ^ r.val) *
        (∑ r : Fin M, a r * W ^ (M - 1 - r.val)) = 0 := by
    rw [cyclic_product a hW, Fintype.sum_eq_single (0 : Fin M)]
    · simp [hasq, hMzero, show ∀ r : Fin M, ¬ M ≤ r.val from fun r => r.isLt.not_ge]
    · intro τ hτ
      have hmap := map_correlation hpos s u hu φ (character_star h₂ V hV second) τ
      rw [hz τ hτ, map_zero, hφu] at hmap
      change (∑ r : Fin M, a r * a (r + τ) * (if M ≤ r.val + τ.val then V else 1)) *
        W ^ (M - 1 - τ.val) = 0
      rw [← hmap, zero_mul]
  let b : Fin M → (ZMod 2)[X] := fun r => if a r = 1 then 0 else 1
  have hlift (r : Fin M) : truncate d (1 + X ^ d * b r) = a r := by
    by_cases hr : a r = 1
    · simp [b, hr]
    · have hv := (halphabet r).resolve_left hr
      simp only [b, ite_eq_right hr, mul_one, hv, V]
      rw [add_comm]
  let p : (ZMod 2)[X] := ∑ r : Fin M, (1 + X ^ d * b r) * (X + 1) ^ r.val
  let q : (ZMod 2)[X] := ∑ r : Fin M, (1 + X ^ d * b r) * (X + 1) ^ (M - 1 - r.val)
  have hqrev : q = ∑ r : Fin M, (1 + X ^ d * b r) * (X + 1) ^ (Fin.revPerm r).val := by
    apply sum_congr rfl
    intro r _
    have hr : (Fin.revPerm r).val = M - 1 - r.val := by rw [Fin.revPerm_apply, Fin.val_rev]; omega
    rw [hr]
  have hzero : truncate d (p * q) = 0 := by
    simpa only [p, q, map_mul, map_sum, map_pow, hlift, ← show W = truncate d (X + 1) from rfl]
      using hprod
  have hc (j : ℕ) (hj : j < d) :
      p.coeff j = if j = d - 1 then 1 else 0 := by
    rw [show p = ∑ r : Fin M, (1 + X ^ d * b r) * (X + 1) ^ (Equiv.refl (Fin M) r).val from rfl,
      lifted_coeff b (Equiv.refl (Fin M)) j hj, geom_coeff hd hW j hj]
  have hc' (j : ℕ) (hj : j < d) :
      q.coeff j = if j = d - 1 then 1 else 0 := by
    rw [hqrev, lifted_coeff b Fin.revPerm j hj, geom_coeff hd hW j hj]
  have hpq := leading_product hd hc hc'
  rw [coeff_eq_of_truncate_eq (hzero.trans (map_zero (truncate d)).symm)
    (by omega : 2 * d - 2 < 2 * d), coeff_zero] at hpq
  exact zero_ne_one hpq

#print axioms blake_conjecture_5_2


private theorem transverse_sum {R T : Type*} [CommRing R] [Fintype T] [AddCommGroup T]
    {M : ℕ} [NeZero M] (a : Fin M → T → R) (r τ : Fin M) :
    (∑ s : T, ∑ t : T, a r t * a (r + τ) (t + s)) =
      (∑ t : T, a r t) * (∑ t : T, a (r + τ) t) := by
  rw [sum_comm, sum_mul]
  exact sum_congr rfl fun t _ =>
    (Equiv.sum_comp (Equiv.addLeft t) (fun v : T => a r t * a (r + τ) v)).trans
      (mul_sum _ _ _).symm

section Transverse

variable {T : Type*} [Fintype T] [AddCommGroup T]
variable {M : ℕ}

/-- Blake's right-twisted base-box autocorrelation at the represented shift `(τ, s)`. -/
def baseCorrelation (hM : 0 < M) (A : Fin M → T → ℍ[ℤ])
    (u : ℍ[ℤ]) (hu : Noncentral u) (τ : Fin M) (s : T) : ℍ[ℤ] :=
  ∑ r : Fin M, ∑ t : T, A r t *
    star (extension hM (fun j => A j (t + s)) u hu ((r.val : ℤ) + τ.val))

/-- The full extension autocorrelation over `4M × T`, enumerated by `qM + r`. -/
def fullPeriodCorrelation (hM : 0 < M) (A : Fin M → T → ℍ[ℤ])
    (u : ℍ[ℤ]) (hu : Noncentral u) (τ : Fin M) (s : T) : ℍ[ℤ] :=
  ∑ q : Fin 4, ∑ r : Fin M, ∑ t : T,
    extension hM (fun j => A j t) u hu ((q.val : ℤ) * M + r.val) *
      star (extension hM (fun j => A j (t + s)) u hu
        (((q.val : ℤ) * M + r.val) + τ.val))

variable [NeZero M]

private theorem mapped_array_corr {R : Type*} [CommRing R] (hM : 0 < M)
    (A : Fin M → T → ℍ[ℤ]) (u : ℍ[ℤ]) (hu : Noncentral u)
    (φ : ℍ[ℤ] →+* R) (hstar : ∀ x, φ (star x) = φ x) (τ : Fin M) :
    (∑ s : T, φ (baseCorrelation hM A u hu τ s)) =
    ∑ r : Fin M, (∑ t : T, φ (A r t)) * (∑ t : T, φ (A (r + τ) t)) *
      (if M ≤ r.val + τ.val then φ u else 1) := by
  simp only [baseCorrelation, map_sum, extension_add, star_mul, map_mul, hstar]
  rw [sum_comm]
  apply sum_congr rfl
  intro r _
  have reindex := transverse_sum (fun j t => φ (A j t)) r τ
  calc
    _ = ∑ s : T, ∑ t : T, (φ (A r t) * φ (A (r + τ) (t + s))) *
        φ (if M ≤ r.val + τ.val then u else 1) := by
      apply sum_congr rfl
      intro s _
      apply sum_congr rfl
      intro t _
      ring
    _ = (∑ s : T, ∑ t : T, φ (A r t) * φ (A (r + τ) (t + s))) *
        φ (if M ≤ r.val + τ.val then u else 1) := by simp only [sum_mul]
    _ = _ := by rw [reindex]; split_ifs <;> simp

private theorem q8_star_product {x : ℍ[ℤ]} (hx : IsQ8 x) : x * star x = 1 := by
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals ext <;> decide

private theorem array_diag (hM : 0 < M) (A : Fin M → T → ℍ[ℤ])
    (hA : ∀ r t, IsQ8 (A r t)) (u : ℍ[ℤ]) (hu : Noncentral u) :
    baseCorrelation hM A u hu 0 0 = (M * Fintype.card T : ℕ) := by
  unfold baseCorrelation
  simp_rw [extension_add]
  calc
    _ = ∑ _r : Fin M, ∑ _t : T, (1 : ℍ[ℤ]) := by
      apply sum_congr rfl
      intro r _
      apply sum_congr rfl
      intro t _
      simp [r.isLt.not_ge, q8_star_product (hA r t)]
    _ = _ := by simp [nsmul_eq_mul, Nat.cast_mul]

omit [AddCommGroup T] in
private theorem odd_cast {R : Type*} [CommRing R] (hT : Odd (Fintype.card T))
    (h₂ : (2 : R) = 0) : (Fintype.card T : R) = 1 := by
  obtain ⟨b, hb⟩ := hT
  rw [hb, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, h₂, zero_mul, zero_add, Nat.cast_one]

private theorem base_correlation_exists (hM : 2 ≤ M) (hT : Odd (Fintype.card T))
    (A : Fin M → T → ℍ[ℤ]) (hA : ∀ r t, IsQ8 (A r t))
    (u : ℍ[ℤ]) (hu : Noncentral u) :
    ∃ τ : Fin M, ∃ s : T, (τ, s) ≠ (0, 0) ∧ baseCorrelation (by omega) A u hu τ s ≠ 0 := by
  classical
  have hpos : 0 < M := by omega
  by_contra! hz
  have hzero (τ : Fin M) (hτ : τ ≠ 0) (s : T) : baseCorrelation hpos A u hu τ s = 0 :=
    hz τ s (fun e => hτ (congrArg Prod.fst e))
  have hz0 (s : T) (hs : s ≠ 0) : baseCorrelation hpos A u hu 0 s = 0 :=
    hz 0 s (fun e => hs (congrArg Prod.snd e))
  have heven : Even M := by
    let φ := character (R := ZMod 2) (by decide) 1 (one_mul 1) false
    have hφ {x : ℍ[ℤ]} (hx : IsQ8 x) : φ x = 1 :=
      (character_letter (by decide) 1 (one_mul 1) false hx).elim id id
    let τ : Fin M := ⟨1, by omega⟩
    have hn : τ ≠ 0 := by intro he; have := congrArg Fin.val he; contradiction
    have hφu : φ u = 1 := hφ (Or.inr (Or.inr hu))
    have hwrap (r : Fin M) : φ (if M ≤ r.val + τ.val then u else 1) = 1 := by
      split_ifs <;> simp [hφu]
    have hmap : φ (baseCorrelation hpos A u hu τ 0) = (M : ZMod 2) * Fintype.card T := by
      simp [baseCorrelation, extension_add, map_sum, star_mul, map_mul,
        character_star (by decide) 1 (one_mul 1) false, hwrap, fun r t => hφ (hA r t),
        nsmul_eq_mul]
    rw [hzero τ hn, map_zero, odd_cast hT (by decide), mul_one] at hmap
    exact even_iff_two_dvd.mpr ((ZMod.natCast_eq_zero_iff M 2).mp hmap.symm)
  let d := 2 ^ M.factorization 2
  let m := M / d
  have hd : 0 < d := by dsimp [d]; positivity
  have hMdm : M = d * m := (Nat.ordProj_mul_ordCompl_eq_self M 2).symm
  have hm : Odd m := Nat.not_even_iff_odd.mp fun he =>
    Nat.not_dvd_ordCompl Nat.prime_two (NeZero.ne M) (even_iff_two_dvd.mp he)
  let W := truncate d (X + 1)
  let V := truncate d (X ^ d + 1)
  obtain ⟨hV, hW⟩ : V * V = 1 ∧ W ^ M = V := truncate_pow rfl hMdm hm
  have h₂ : (2 : Truncated d) = 0 := by
    rw [← map_ofNat (truncate d) 2, show (2 : (ZMod 2)[X]) = 0 from CharTwo.two_eq_zero, map_zero]
  have hMzero : (M : Truncated d) = 0 := by
    obtain ⟨b, hb⟩ := heven
    rw [hb, Nat.cast_add, ← two_mul, h₂, zero_mul]
  obtain ⟨second, hφu⟩ := character_twist h₂ V hV hu
  let φ := character h₂ V hV second
  let a : Fin M → Truncated d := fun r => ∑ t, φ (A r t)
  have hcorr (τ : Fin M) : (∑ s : T, φ (baseCorrelation hpos A u hu τ s)) = 0 := by
    by_cases hτ : τ = 0
    · subst τ
      rw [Fintype.sum_eq_single (0 : T)]
      · simp [array_diag hpos A hA u hu, Nat.cast_mul, hMzero]
      · intro s hs
        rw [hz0 s hs, map_zero]
    · simp [hzero τ hτ]
  have hprod :
      (∑ r : Fin M, a r * W ^ r.val) *
        (∑ r : Fin M, a r * W ^ (M - 1 - r.val)) = 0 := by
    rw [cyclic_product a hW]
    apply Finset.sum_eq_zero
    intro τ _
    have hmap := mapped_array_corr hpos A u hu φ (character_star h₂ V hV second) τ
    rw [hφu, hcorr τ] at hmap
    change (∑ r : Fin M, a r * a (r + τ) *
      (if M ≤ r.val + τ.val then V else 1)) * W ^ (M - 1 - τ.val) = 0
    rw [← hmap, zero_mul]
  let letter : Fin M → T → (ZMod 2)[X] := fun r t => if φ (A r t) = 1 then 0 else 1
  have hletter (r : Fin M) (t : T) : truncate d (1 + X ^ d * letter r t) = φ (A r t) := by
    by_cases hr : φ (A r t) = 1
    · simp [letter, hr]
    · have hv := (character_letter h₂ V hV second (hA r t)).resolve_left hr
      change φ (A r t) = V at hv
      simp only [letter, ite_eq_right hr, mul_one, hv]
      exact congrArg (truncate d) (add_comm _ _)
  let b : Fin M → (ZMod 2)[X] := fun r => ∑ t : T, letter r t
  have hlift (r : Fin M) : truncate d (1 + X ^ d * b r) = a r := by
    have hsum : (∑ t : T, (1 + X ^ d * letter r t : (ZMod 2)[X])) = 1 + X ^ d * b r := by
      rw [sum_add_distrib, ← mul_sum, sum_const, card_univ, nsmul_eq_mul, mul_one,
        odd_cast (R := (ZMod 2)[X]) hT CharTwo.two_eq_zero]
    rw [← hsum, map_sum]
    exact sum_congr rfl (fun t _ => hletter r t)
  let p : (ZMod 2)[X] := ∑ r : Fin M, (1 + X ^ d * b r) * (X + 1) ^ r.val
  let q : (ZMod 2)[X] := ∑ r : Fin M, (1 + X ^ d * b r) * (X + 1) ^ (M - 1 - r.val)
  have hqrev : q = ∑ r : Fin M, (1 + X ^ d * b r) * (X + 1) ^ (Fin.revPerm r).val := by
    apply sum_congr rfl
    intro r _
    have hr : (Fin.revPerm r).val = M - 1 - r.val := by rw [Fin.revPerm_apply, Fin.val_rev]; omega
    rw [hr]
  have hpqzero : truncate d (p * q) = 0 := by
    simpa only [p, q, map_mul, map_sum, map_pow, hlift, ← show W = truncate d (X + 1) from rfl]
      using hprod
  have hc (j : ℕ) (hj : j < d) :
      p.coeff j = if j = d - 1 then 1 else 0 := by
    rw [show p = ∑ r : Fin M, (1 + X ^ d * b r) * (X + 1) ^ (Equiv.refl (Fin M) r).val from rfl,
      lifted_coeff b (Equiv.refl (Fin M)) j hj, geom_coeff hd hW j hj]
  have hc' (j : ℕ) (hj : j < d) :
      q.coeff j = if j = d - 1 then 1 else 0 := by
    rw [hqrev, lifted_coeff b Fin.revPerm j hj, geom_coeff hd hW j hj]
  have hpq := leading_product hd hc hc'
  rw [coeff_eq_of_truncate_eq (hpqzero.trans (map_zero (truncate d)).symm)
    (by omega : 2 * d - 2 < 2 * d), coeff_zero] at hpq
  exact zero_ne_one hpq

omit [NeZero M] in
private theorem extension_translate (hM : 0 < M) (a : Fin M → ℍ[ℤ])
    (u : ℍ[ℤ]) (hu : Noncentral u) (q n : ℤ) :
    extension hM a u hu (q * (M : ℤ) + n) =
      extension hM a u hu n * (↑(twistUnit u hu ^ q) : ℍ[ℤ]) := by
  have hpos : (0 : ℤ) < M := by exact_mod_cast hM
  have hr0 := Int.emod_nonneg n hpos.ne'
  have hrM := Int.emod_lt_of_pos n hpos
  let r : Fin M := ⟨(n % (M : ℤ)).toNat, by omega⟩
  have hr : (r.val : ℤ) = n % (M : ℤ) := Int.toNat_of_nonneg hr0
  have hn : n / (M : ℤ) * (M : ℤ) + r.val = n := by
    rw [hr, Int.ediv_mul_add_emod]
  have hqn : q * (M : ℤ) + n = (n / (M : ℤ) + q) * (M : ℤ) + r.val := by
    rw [add_mul]
    omega
  calc
    _ = a r * (↑(twistUnit u hu ^ (n / (M : ℤ) + q)) : ℍ[ℤ]) := by
      rw [hqn, extension_at]
    _ = a r * (↑(twistUnit u hu ^ (n / (M : ℤ))) : ℍ[ℤ]) *
        (↑(twistUnit u hu ^ q) : ℍ[ℤ]) := by
      rw [zpow_add, Units.val_mul, mul_assoc]
    _ = _ := by
      have hbase := (congrArg (extension hM a u hu) hn.symm).trans
        (extension_at hM a u hu (n / (M : ℤ)) r)
      rw [← hbase]

omit [Fintype T] [NeZero M] in
private theorem period_block_term (hM : 0 < M) (A : Fin M → T → ℍ[ℤ])
    (u : ℍ[ℤ]) (hu : Noncentral u) (q : ℤ) (r τ : Fin M) (t s : T) :
    extension hM (fun j => A j t) u hu (q * (M : ℤ) + r.val) *
        star (extension hM (fun j => A j (t + s)) u hu
          ((q * (M : ℤ) + r.val) + τ.val)) =
      A r t * star (extension hM (fun j => A j (t + s)) u hu ((r.val : ℤ) + τ.val)) := by
  have hstar : star (twistUnit u hu) = (twistUnit u hu)⁻¹ := Units.ext rfl
  have hq : (↑(twistUnit u hu ^ q) : ℍ[ℤ]) * star (↑(twistUnit u hu ^ q) : ℍ[ℤ]) = 1 := by
    rw [← Units.coe_star, star_zpow, hstar, inv_zpow]
    exact Units.val_inv _
  rw [add_assoc, extension_at, extension_translate, star_mul, ← mul_assoc, mul_assoc (A r t),
    hq, mul_one]

omit [NeZero M] in
private theorem full_period_factor_four (hM : 0 < M) (A : Fin M → T → ℍ[ℤ])
    (u : ℍ[ℤ]) (hu : Noncentral u) (τ : Fin M) (s : T) :
    fullPeriodCorrelation hM A u hu τ s = 4 • baseCorrelation hM A u hu τ s := by
  simp [fullPeriodCorrelation, period_block_term, baseCorrelation]

private theorem four_nsmul_eq_zero (x : ℍ[ℤ]) : (4 • x : ℍ[ℤ]) = 0 ↔ x = 0 := by
  constructor
  · intro hx
    rw [show (4 : ℕ) = (3 : ℕ) + 1 from rfl, add_nsmul, one_nsmul,
      show (3 : ℕ) = (2 : ℕ) + 1 from rfl, add_nsmul, one_nsmul, two_nsmul] at hx
    ext
    · have h := congrArg QuaternionAlgebra.re hx
      simp only [Quaternion.re_add, Quaternion.re_zero] at h ⊢
      omega
    · have h := congrArg QuaternionAlgebra.imI hx
      simp only [Quaternion.imI_add, Quaternion.imI_zero] at h ⊢
      omega
    · have h := congrArg QuaternionAlgebra.imJ hx
      simp only [Quaternion.imJ_add, Quaternion.imJ_zero] at h ⊢
      omega
    · have h := congrArg QuaternionAlgebra.imK hx
      simp only [Quaternion.imK_add, Quaternion.imK_zero] at h ⊢
      omega
  · rintro rfl
    exact nsmul_zero _

omit [NeZero M] in
/-- An array of odd transverse cardinality and first-axis length at least two has one
    off-period shift with nonzero base and full extension autocorrelations. -/
theorem odd_transverse_nonvanishing (hM : 2 ≤ M) (hT : Odd (Fintype.card T))
    (A : Fin M → T → ℍ[ℤ]) (hA : ∀ r t, IsQ8 (A r t))
    (u : ℍ[ℤ]) (hu : Noncentral u) :
    ∃ τ : Fin M, ∃ s : T, (τ, s) ≠ (0, 0) ∧
      baseCorrelation (by omega) A u hu τ s ≠ 0 ∧
      fullPeriodCorrelation (by omega) A u hu τ s ≠ 0 := by
  letI : NeZero M := ⟨by omega⟩
  obtain ⟨τ, s, hshift, hbase⟩ := base_correlation_exists hM hT A hA u hu
  refine ⟨τ, s, hshift, hbase, ?_⟩
  rw [full_period_factor_four]
  exact fun hfull => hbase ((four_nsmul_eq_zero _).mp hfull)

end Transverse

end D5.S3.Combinatorics.QuaternionSequences.BlakeConjecture52
