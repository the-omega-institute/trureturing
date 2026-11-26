/- GID: D5/S3/Arith/Lattices/HilbertSmith/DivisorFormula
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/HilbertSmith/DivisorFormula
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: []
   utility: none
   digest: Attained prime-layer minimum and its successive interval LCM factors. -/

import D5.S3.Arith.Lattices.HilbertSmith.NestedResidueMatching
import Mathlib.Algebra.GCDMonoid.FinsetLemmas
import Mathlib.Data.Nat.Log

/-! # The Hilbert determinantal divisor exponents -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Lattices.HilbertSmith.DivisorFormula

open Finset NestedResidueMatching
open scoped BigOperators

/-- One pair of index sets attains the sum of the layerwise lower bounds. -/
theorem residueLoss_sum_minimum {p n k : ℕ} (hp : 0 < p) (hk : k ≤ n) (e : ℕ) :
    (∀ {I J : Finset ℕ}, I ⊆ range n → J ⊆ range n → I.card = k → J.card = k →
      2 * (∑ a ∈ Icc 1 e, (k - commonCapacity n (p ^ a))) ≤
        ∑ a ∈ Icc 1 e, residueLoss (p ^ a) I J) ∧
    (∃ I ⊆ range n, ∃ J ⊆ range n, I.card = k ∧ J.card = k ∧
      (∑ a ∈ Icc 1 e, residueLoss (p ^ a) I J) =
        2 * (∑ a ∈ Icc 1 e, (k - commonCapacity n (p ^ a)))) := by
  constructor
  · intro I J hI hJ hIk hJk
    rw [mul_sum]
    exact sum_le_sum fun a _ => residue_loss_lower (pow_pos hp a) hI hJ hIk hJk
  · obtain ⟨I, hI, J, hJ, hIk, hJk, hopt⟩ := exists_residue_minimizer hp hk e
    refine ⟨I, hI, J, hJ, hIk, hJk, ?_⟩
    rw [mul_sum]
    exact sum_congr rfl fun a ha => hopt a (mem_Icc.mp ha).2

/-- The exponent of a prime in the determinantal divisor of the specified order. -/
def divisorExponent (p n L k : ℕ) : ℕ :=
  k * (L.factorization p - Nat.log p (2 * n - 1)) +
    ∑ a ∈ Icc 1 (Nat.log p (2 * n - 1)), (k - commonCapacity n (p ^ a))

private def smithExponent (p n L k : ℕ) : ℕ :=
  L.factorization p - Nat.log p (2 * n - 1) +
    ((Icc 1 (Nat.log p (2 * n - 1))).filter (fun a => commonCapacity n (p ^ a) < k)).card

private theorem divisorExponent_succ (p n L k : ℕ) :
    divisorExponent p n L (k + 1) = divisorExponent p n L k + smithExponent p n L (k + 1) := by
  have h (a : ℕ) :
      k + 1 - commonCapacity n (p ^ a) =
        (k - commonCapacity n (p ^ a)) + if commonCapacity n (p ^ a) < k + 1 then 1 else 0 := by
    split_ifs <;> omega
  unfold divisorExponent smithExponent
  simp_rw [h]
  rw [sum_add_distrib, Finset.sum_boole, Nat.cast_id, Nat.add_mul, Nat.one_mul]
  omega

/-- The least common multiple of the integers in the closed interval
from k to 2n − k. The interval starting at one clears all Hilbert denominators. -/
def intervalLCM (n k : ℕ) : ℕ := (Icc k (2 * n - k)).lcm id

theorem intervalLCM_ne_zero {n k : ℕ} (hk : 0 < k) : intervalLCM n k ≠ 0 := by
  unfold intervalLCM
  exact Finset.lcm_ne_zero_iff.mpr fun t ht => (hk.trans_le (mem_Icc.mp ht).1).ne'

theorem intervalLCM_dvd_of_le {n k l : ℕ} (hkl : k ≤ l) :
    intervalLCM n l ∣ intervalLCM n k := by
  unfold intervalLCM
  apply Finset.lcm_dvd
  intro t ht
  obtain ⟨hlo, hhi⟩ := mem_Icc.mp ht
  exact Finset.dvd_lcm (f := id) (mem_Icc.mpr ⟨hkl.trans hlo, by omega⟩)

/-- Any positive denominator-clearing scale contains all prime powers up
to the logarithmic cutoff. -/
theorem height_le_factorization {p n L : ℕ} (hp : p.Prime) (hL : L ≠ 0)
    (hd : intervalLCM n 1 ∣ L) : Nat.log p (2 * n - 1) ≤ L.factorization p := by
  by_cases hN : 2 * n - 1 = 0
  · simp only [hN, Nat.log_zero_right, Nat.zero_le]
  · have hmem : p ^ Nat.log p (2 * n - 1) ∈ Icc 1 (2 * n - 1) :=
      mem_Icc.mpr ⟨pow_pos hp.pos _, Nat.pow_log_le_self p hN⟩
    exact (hp.pow_dvd_iff_le_factorization hL).mp
      ((Finset.dvd_lcm (f := id) hmem).trans hd)

/-- The reflected capacity is at least k exactly when the symmetric
interval contains a multiple of the modulus. -/
theorem le_capacity_iff_exists_dvd {n k q : ℕ} (hk : k ≤ n) (hq : 0 < q) :
    k ≤ commonCapacity n q ↔ ∃ t ∈ Icc k (2 * n - k), q ∣ t := by
  let r := n % q
  let d := n / q
  have hrem : r + q * d = n := Nat.mod_add_div n q
  have hr : r < q := Nat.mod_lt n hq
  have hup : q * (d + 1) = n + (q - r) := by
    rw [Nat.mul_succ]
    omega
  change k ≤ n - min r (q - r) ↔ _
  constructor
  · intro hc
    rcases le_total r (q - r) with h | h
    · rw [min_eq_left h] at hc
      exact ⟨q * d, mem_Icc.mpr ⟨by omega, by omega⟩, ⟨d, rfl⟩⟩
    · rw [min_eq_right h] at hc
      exact ⟨q * (d + 1), mem_Icc.mpr ⟨by omega, by omega⟩, ⟨d + 1, rfl⟩⟩
  · rintro ⟨t, ht, m, rfl⟩
    obtain ⟨hlo, hhi⟩ := mem_Icc.mp ht
    by_cases hm : m ≤ d
    · have hprod := Nat.mul_le_mul_left q hm
      have hmin := min_le_left r (q - r)
      omega
    · have hprod := Nat.mul_le_mul_left q (show d + 1 ≤ m by omega)
      have hmin := min_le_right r (q - r)
      omega

private theorem prime_pow_dvd_intervalLCM_iff {p n k a : ℕ} (hp : p.Prime)
    (hk : 0 < k) (hkn : k ≤ n) :
    p ^ a ∣ intervalLCM n k ↔ ∃ t ∈ Icc k (2 * n - k), p ^ a ∣ t := by
  have h0 : ∀ t ∈ Icc k (2 * n - k), id t ≠ 0 :=
    fun t ht => (hk.trans_le (mem_Icc.mp ht).1).ne'
  constructor
  · intro hd
    have hval := (hp.pow_dvd_iff_le_factorization (intervalLCM_ne_zero hk)).mp hd
    have hn : (Icc k (2 * n - k)).Nonempty := ⟨n, mem_Icc.mpr ⟨hkn, by omega⟩⟩
    obtain ⟨t, ht, hsup⟩ :=
      (Icc k (2 * n - k)).exists_mem_eq_sup hn (fun x => (id x).factorization p)
    unfold intervalLCM at hval
    rw [Finset.factorization_lcm h0 p, hsup] at hval
    exact ⟨t, ht, (hp.pow_dvd_iff_le_factorization (h0 t ht)).mpr hval⟩
  · rintro ⟨t, ht, htdiv⟩
    exact htdiv.trans (Finset.dvd_lcm (f := id) ht)

/-- The positive prime-power layers at which the reflected capacity is at least k. -/
def capacityLayers (p n k : ℕ) : Finset ℕ :=
  (Icc 1 (Nat.log p (2 * n - 1))).filter (fun a => k ≤ commonCapacity n (p ^ a))

/-- The exponent in the interval LCM counts the prime-power layers
whose reflected capacity is at least k. -/
theorem intervalLCM_factorization {p n k : ℕ} (hp : p.Prime)
    (hk : 0 < k) (hkn : k ≤ n) :
    (intervalLCM n k).factorization p =
      (capacityLayers p n k).card := by
  unfold capacityLayers
  have hcap (a : ℕ) : k ≤ commonCapacity n (p ^ a) ↔ a ≤ (intervalLCM n k).factorization p :=
    (le_capacity_iff_exists_dvd hkn (pow_pos hp.pos a)).trans
      ((prime_pow_dvd_intervalLCM_iff hp hk hkn).symm.trans
        (hp.pow_dvd_iff_le_factorization (intervalLCM_ne_zero hk)))
  have hb : (intervalLCM n k).factorization p ≤ Nat.log p (2 * n - 1) := by
    obtain ⟨t, ht, hd⟩ := (prime_pow_dvd_intervalLCM_iff hp hk hkn).mp
      (Nat.ordProj_dvd (intervalLCM n k) p)
    have htpos : 0 < t := hk.trans_le (mem_Icc.mp ht).1
    exact Nat.le_log_of_pow_le hp.one_lt
      ((Nat.le_of_dvd htpos hd).trans ((mem_Icc.mp ht).2.trans (by omega)))
  have hfilter :
      (Icc 1 (Nat.log p (2 * n - 1))).filter (fun a => k ≤ commonCapacity n (p ^ a)) =
        Icc 1 ((intervalLCM n k).factorization p) := by
    ext a
    simp only [mem_filter, mem_Icc, hcap]
    omega
  rw [hfilter, Nat.card_Icc, Nat.add_sub_cancel]

private theorem smithExponent_eq_intervalLCM {p n k L : ℕ} (hp : p.Prime)
    (hk : 0 < k) (hkn : k ≤ n) (hL : L ≠ 0) (hd : intervalLCM n 1 ∣ L) :
    smithExponent p n L k = (L / intervalLCM n k).factorization p := by
  have hLe := height_le_factorization hp hL hd
  have hcount := card_filter_add_card_filter_not (s := Icc 1 (Nat.log p (2 * n - 1)))
    (fun a => k ≤ commonCapacity n (p ^ a))
  change (capacityLayers p n k).card + _ = _ at hcount
  rw [← intervalLCM_factorization hp hk hkn, Nat.card_Icc, Nat.add_sub_cancel] at hcount
  have hcomplement : (Icc 1 (Nat.log p (2 * n - 1))).filter
        (fun a => ¬ k ≤ commonCapacity n (p ^ a)) =
      (Icc 1 (Nat.log p (2 * n - 1))).filter (fun a => commonCapacity n (p ^ a) < k) := by
    ext a
    simp only [mem_filter, not_le]
  rw [hcomplement] at hcount
  rw [smithExponent, Nat.factorization_div ((intervalLCM_dvd_of_le hk).trans hd)]
  simp only [Finsupp.coe_tsub, Pi.sub_apply]
  omega

/-- The primewise increment is the exponent of the exact interval-LCM quotient. -/
theorem divisorExponent_succ_eq_intervalLCM {p n k L : ℕ} (hp : p.Prime)
    (hL : L ≠ 0) (hd : intervalLCM n 1 ∣ L) (hk : k + 1 ≤ n) :
    divisorExponent p n L (k + 1) =
      divisorExponent p n L k + (L / intervalLCM n (k + 1)).factorization p := by
  rw [divisorExponent_succ, smithExponent_eq_intervalLCM hp (Nat.succ_pos k) hk hL hd]

end D5.S3.Arith.Lattices.HilbertSmith.DivisorFormula
