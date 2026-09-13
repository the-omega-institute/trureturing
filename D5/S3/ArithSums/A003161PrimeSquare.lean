/- GID: D5/S3/ArithSums/A003161PrimeSquare
   generality: G
   mirror-B: D5/B/S3/ArithSums/A003161PrimeSquare
   mirror-E: none(waiver:universal-congruence-no-numeric-artifact)
   anchors: [mathlib/module/Mathlib.Data.Nat.Choose.Lucas]
   utility: none
   digest: A003161 at odd indices satisfies a congruence modulo each odd prime square. -/

import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Tactic

open Finset

namespace D5.S3.ArithSums.A003161PrimeSquare

/-- A shifted binomial coefficient retains its value modulo the square of an odd prime.

This statement is classical, not new here: it belongs to the
Babbage-Wolstenholme-Ljunggren-Jacobsthal circle, and follows from Jacobsthal's
refinement of the congruence for `C(m*p, a*p)` together with the identity
`C(m*p - 1, a*p) = (m - a) * C(m*p, a*p) / m`. It is written out here only because
the pinned Mathlib carries no Wolstenholme-type result at all; its provenance is
attested to the literature. -/
theorem choose_mul_sub_one_mod_prime_sq (m a p : ℕ) (hm : 0 < m)
    (hp : p.Prime) (hp2 : p ≠ 2) :
    (Nat.choose (m * p - 1) (a * p) : ℤ) ≡ Nat.choose (m - 1) a [ZMOD (p : ℤ) ^ 2] := by
  let : Fact p.Prime := ⟨hp⟩
  have hp0 := hp.pos
  have hp1 := hp.one_lt
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hpred (r : ℕ) (hr : r < p) :
      (Nat.choose (p - 1) r : ℤ) ≡ (-1) ^ r [ZMOD (p : ℤ)] := by
    induction r with
    | zero => simp [Int.ModEq.refl]
    | succ r ih =>
      have hpas := Nat.choose_succ_succ' (p - 1) r
      rw [Nat.sub_add_cancel hp1.le] at hpas
      have hd : (p : ℤ) ∣ (Nat.choose p (r + 1) : ℤ) := by
        exact_mod_cast hp.dvd_choose_self (by omega) hr
      have he : (Nat.choose (p - 1) (r + 1) : ℤ) =
          Nat.choose p (r + 1) - Nat.choose (p - 1) r := by
        have hz : (Nat.choose p (r + 1) : ℤ) =
            Nat.choose (p - 1) r + Nat.choose (p - 1) (r + 1) := by exact_mod_cast hpas
        omega
      rw [he, pow_succ]
      simpa using hd.modEq_zero_int.sub (ih (by omega))
  have hlucas (t a r : ℕ) (hr : r < p) :
      (Nat.choose ((t + 1) * p - 1) (a * p + r) : ℤ) ≡
        (-1) ^ r * Nat.choose t a [ZMOD (p : ℤ)] := by
    have he : (t + 1) * p - 1 = t * p + (p - 1) := by
      rw [Nat.add_mul, one_mul]; omega
    have h := Choose.choose_modEq_choose_mod_mul_choose_div
      (n := (t + 1) * p - 1) (k := a * p + r) (p := p)
    have hdt : (t * p + (p - 1)) / p = t := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hp0,
        Nat.div_eq_of_lt (by omega : p - 1 < p), zero_add]
    have hda : (a * p + r) / p = a := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hp0, Nat.div_eq_of_lt hr, zero_add]
    simp only [he, Nat.mul_add_mod_self_right,
      Nat.mod_eq_of_lt (by omega : p - 1 < p), Nat.mod_eq_of_lt hr,
      hdt, hda] at h
    simpa only [he] using h.trans ((hpred r hr).mul_right _)
  have hscale {x y z : ℤ} (hz : (p : ℤ) ∣ z)
      (hxy : x ≡ y [ZMOD (p : ℤ)]) :
      z * x ≡ z * y [ZMOD (p : ℤ) ^ 2] := by
    apply Int.ModEq.of_dvd _ hxy.mul_left'
    simpa [pow_two] using mul_dvd_mul hz (dvd_refl (p : ℤ))
  have hsplit (f : ℕ → ℤ) :
      ∑ i ∈ range (p + 1), f i = f 0 + (∑ i ∈ range (p - 1), f (i + 1)) + f p := by
    rw [sum_range_succ]
    conv_lhs => lhs; rw [← Nat.sub_add_cancel hp1.le, sum_range_succ']
    ring
  have halt : ∑ i ∈ range (p - 1), (-1 : ℤ) ^ (i + 1) * Nat.choose p (i + 1) = 0 := by
    have h := Int.alternating_sum_range_choose_of_ne hp.ne_zero
    rw [hsplit] at h
    simpa [hodd.neg_one_pow, add_comm, add_left_comm, add_assoc] using h
  have hsign (r : ℕ) (hr : r ≤ p) : (-1 : ℤ) ^ (p - r) = -(-1) ^ r := by
    have he : (-1 : ℤ) ^ (p - r) * (-1) ^ r = -1 := by
      rw [← pow_add, Nat.sub_add_cancel hr, hodd.neg_one_pow]
    rcases neg_one_pow_eq_or ℤ r with h | h <;> rw [h] at he ⊢ <;> linarith
  have hend : ∀ t a : ℕ,
      (Nat.choose ((t + 1) * p - 1) (a * p) : ℤ) ≡ Nat.choose t a [ZMOD (p : ℤ) ^ 2] := by
    intro t
    induction t with
    | zero =>
      intro a
      cases a with
      | zero => simp [Int.ModEq.refl]
      | succ a =>
        have hlt : p - 1 < (a + 1) * p := by rw [Nat.add_mul, one_mul]; omega
        simp [Nat.choose_eq_zero_of_lt hlt, Int.ModEq.refl]
    | succ t ih =>
      intro a
      cases a with
      | zero => simp [Int.ModEq.refl]
      | succ a =>
        let f : ℕ → ℤ := fun i =>
          Nat.choose p i * Nat.choose ((t + 1) * p - 1) ((a + 1) * p - i)
        have hv : (Nat.choose ((t + 1 + 1) * p - 1) ((a + 1) * p) : ℤ) =
            ∑ i ∈ range (p + 1), f i := by
          have he : (t + 1 + 1) * p - 1 = p + ((t + 1) * p - 1) := by
            have ht0 : 0 < (t + 1) * p := Nat.mul_pos (by omega) hp0
            rw [Nat.add_mul, one_mul]; omega
          rw [he, Nat.add_choose_eq, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
            Nat.cast_sum]
          simp only [Nat.cast_mul]
          symm
          apply sum_subset (range_mono (by nlinarith : p + 1 ≤ (a + 1) * p + 1))
          intro i hi hnot
          have hpi : p < i := by simpa using hnot
          simp [f, Nat.choose_eq_zero_of_lt hpi]
        have hinter : (∑ i ∈ range (p - 1), f (i + 1)) ≡ 0 [ZMOD (p : ℤ) ^ 2] := by
          have hs : (∑ i ∈ range (p - 1), f (i + 1)) ≡
              ∑ i ∈ range (p - 1),
                -(Nat.choose t a : ℤ) * ((-1) ^ (i + 1) * Nat.choose p (i + 1))
                [ZMOD (p : ℤ) ^ 2] := by
            apply Int.ModEq.sum
            intro i hi
            have hi' := mem_range.mp hi
            have he : (a + 1) * p - (i + 1) = a * p + (p - (i + 1)) := by
              rw [Nat.add_mul, one_mul]; omega
            have hd : (p : ℤ) ∣ (Nat.choose p (i + 1) : ℤ) := by
              exact_mod_cast hp.dvd_choose_self (by omega) (by omega)
            have h := hscale hd (hlucas t a (p - (i + 1)) (by omega))
            dsimp [f]
            rw [hsign (i + 1) (by omega)] at h
            rw [he]
            convert h using 1
            ring
          simpa [← mul_sum, halt] using hs
        rw [hv, hsplit]
        have h0 : f 0 ≡ Nat.choose t (a + 1) [ZMOD (p : ℤ) ^ 2] := by
          simpa [f] using ih (a + 1)
        have hp' : f p ≡ Nat.choose t a [ZMOD (p : ℤ) ^ 2] := by
          simpa [f, Nat.add_mul] using ih a
        have h := (h0.add hinter).add hp'
        simpa [Nat.choose_succ_succ, Nat.cast_add, add_comm] using h
  simpa [Nat.sub_add_cancel hm] using hend (m - 1) a

/-- The ballot-cube sequence, with the lower binomial index minus one interpreted as zero. -/
def a (n : ℕ) : ℕ :=
  ∑ j ∈ range (n / 2 + 1),
    (Nat.choose n j - if j = 0 then 0 else Nat.choose n (j - 1)) ^ 3

/-- The odd-indexed subsequence of A003161. -/
def b (n : ℕ) : ℕ := a (2 * n - 1)

/-- Multiplying the index by an odd prime preserves the ballot-cube sum modulo its square. -/
theorem a003161_prime_square (n p : ℕ) (hn : 0 < n) (hp : p.Prime) (hp2 : p ≠ 2) :
    (b (n * p) : ℤ) ≡ b n [ZMOD (p : ℤ) ^ 2] := by
  let : Fact p.Prime := ⟨hp⟩
  have hp0 := hp.pos
  have hp1 := hp.one_lt
  have hnp : 0 < n * p := Nat.mul_pos hn hp0
  let c : ℕ → ℕ → ℤ := fun t j => Nat.choose (2 * t - 1) j
  let d : ℕ → ℕ → ℤ := fun t j => c t j - if j = 0 then 0 else c t (j - 1)
  have hcast (t : ℕ) (ht : 0 < t) : (b t : ℤ) = ∑ j ∈ range t, d t j ^ 3 := by
    have hh : (2 * t - 1) / 2 + 1 = t := by omega
    simp only [b, a, hh, Nat.cast_sum]
    apply sum_congr rfl
    intro j hj
    have hj' := mem_range.mp hj
    cases j with
    | zero => simp [d, c]
    | succ j =>
      have hle : Nat.choose (2 * t - 1) j ≤ Nat.choose (2 * t - 1) (j + 1) :=
        Nat.choose_le_succ_of_lt_half_left (by omega)
      simp [d, c, Nat.cast_sub hle]
  have hleft (q : ℕ) : c (n * p) (q * p) ≡ c n q [ZMOD (p : ℤ) ^ 2] := by
    have h := choose_mul_sub_one_mod_prime_sq (2 * n) q p (by omega) hp hp2
    simpa [c, mul_assoc] using h
  have hright (q : ℕ) (hq : q < n) :
      c (n * p) ((q + 1) * p - 1) ≡ c n q [ZMOD (p : ℤ) ^ 2] := by
    have hq' : q ≤ 2 * n - 1 := by omega
    have hs : (2 * n - 1 - q) + (q + 1) = 2 * n := by omega
    have he := congrArg (fun t => t * p) hs
    rw [Nat.add_mul] at he
    have hpos : 0 < (q + 1) * p := Nat.mul_pos (by omega) hp0
    have hsum : 2 * (n * p) - 1 = (2 * n - 1 - q) * p + ((q + 1) * p - 1) := by
      rw [← mul_assoc]
      omega
    have hsym := Nat.choose_symm_of_eq_add hsum
    dsimp [c]
    rw [← hsym]
    simpa [c, Nat.choose_symm hq'] using hleft (2 * n - 1 - q)
  have hboundary (q : ℕ) (hq : q < n) :
      d (n * p) (q * p) ≡ d n q [ZMOD (p : ℤ) ^ 2] := by
    cases q with
    | zero => simpa [d] using hleft 0
    | succ q =>
      have hq0 : (q + 1) * p ≠ 0 := Nat.mul_ne_zero (by omega) hp.ne_zero
      simpa [d, hq0] using (hleft (q + 1)).sub (hright q (by omega))
  have hinter (q r : ℕ) (hr : r < p - 1) :
      d (n * p) (q * p + (r + 1)) ^ 3 ≡
        4 * (c (n * p) (q * p + (r + 1)) ^ 3 - c (n * p) (q * p + r) ^ 3)
        [ZMOD (p : ℤ) ^ 2] := by
    have hres : (q * p + (r + 1)) % p = r + 1 := by
      simp [Nat.add_mod, Nat.mod_eq_of_lt (by omega : r + 1 < p)]
    have htop : (2 * (n * p)) % p = 0 := by simp [Nat.mul_mod]
    have hzero := Choose.choose_modEq_choose_mod_mul_choose_div
      (n := 2 * (n * p)) (k := q * p + (r + 1)) (p := p)
    rw [htop, hres, Nat.choose_zero_succ] at hzero
    have hdiv : (p : ℤ) ∣ (Nat.choose (2 * (n * p)) (q * p + (r + 1)) : ℤ) := by
      apply Int.modEq_zero_iff_dvd.mp
      simpa using hzero
    have hpas := Nat.choose_succ_succ' (2 * (n * p) - 1) (q * p + r)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ 2 * (n * p))] at hpas
    have hsum : (p : ℤ) ∣ c (n * p) (q * p + (r + 1)) + c (n * p) (q * p + r) := by
      rw [Nat.add_assoc] at hpas
      rw [hpas, Nat.cast_add] at hdiv
      simpa only [c, add_comm] using hdiv
    obtain ⟨z, hz⟩ := hsum
    rw [Int.modEq_iff_dvd]
    have hj0 : q * p + (r + 1) ≠ 0 := by omega
    have hjpred : q * p + (r + 1) - 1 = q * p + r := by omega
    simp only [d, hj0, if_false, hjpred]
    refine ⟨3 * (c (n * p) (q * p + (r + 1)) - c (n * p) (q * p + r)) * z ^ 2, ?_⟩
    calc
      _ = 3 * (c (n * p) (q * p + (r + 1)) - c (n * p) (q * p + r)) *
          (c (n * p) (q * p + (r + 1)) + c (n * p) (q * p + r)) ^ 2 := by ring
      _ = _ := by rw [hz]; ring
  have hblock (q : ℕ) (hq : q < n) :
      (∑ r ∈ range p, d (n * p) (q * p + r) ^ 3) ≡ d n q ^ 3
        [ZMOD (p : ℤ) ^ 2] := by
    have hs := Int.ModEq.sum (s := range (p - 1)) (fun r hr => hinter q r (mem_range.mp hr))
    have ht : (∑ r ∈ range (p - 1),
        4 * (c (n * p) (q * p + (r + 1)) ^ 3 - c (n * p) (q * p + r) ^ 3)) =
        4 * (c (n * p) ((q + 1) * p - 1) ^ 3 - c (n * p) (q * p) ^ 3) := by
      rw [← mul_sum, sum_range_sub (fun r => c (n * p) (q * p + r) ^ 3)]
      have he : q * p + (p - 1) = (q + 1) * p - 1 := by
        rw [Nat.add_mul, one_mul]; omega
      simp [he]
    rw [ht] at hs
    have hz := ((hright q hq).pow 3).sub ((hleft q).pow 3)
    have hz' : 4 * (c (n * p) ((q + 1) * p - 1) ^ 3 - c (n * p) (q * p) ^ 3) ≡
        0 [ZMOD (p : ℤ) ^ 2] := by simpa using hz.mul_left 4
    have h := (hs.trans hz').add ((hboundary q hq).pow 3)
    have he : (∑ r ∈ range p, d (n * p) (q * p + r) ^ 3) =
        (∑ r ∈ range (p - 1), d (n * p) (q * p + (r + 1)) ^ 3) +
          d (n * p) (q * p + 0) ^ 3 := by
      simpa only [Nat.sub_add_cancel hp1.le] using
        sum_range_succ' (fun r => d (n * p) (q * p + r) ^ 3) (p - 1)
    rw [he]
    simpa [add_comm] using h
  have hblocks (t : ℕ) (f : ℕ → ℤ) :
      (∑ j ∈ range (t * p), f j) = ∑ q ∈ range t, ∑ r ∈ range p, f (q * p + r) := by
    induction t with
    | zero => simp
    | succ t ih => rw [Nat.succ_mul, sum_range_add, ih, sum_range_succ]
  rw [hcast (n * p) hnp, hcast n hn, hblocks]
  exact Int.ModEq.sum (fun q hq => hblock q (mem_range.mp hq))

#print axioms choose_mul_sub_one_mod_prime_sq
#print axioms a
#print axioms b
#print axioms a003161_prime_square

end D5.S3.ArithSums.A003161PrimeSquare
