/- GID: D5/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/TailConstants
   generality: G
   mirror-B: none(waiver:source-only-implementation)
   mirror-E: none(waiver:unbounded-combinatorial-proof)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/Main.makowski_schinzel_of_smooth_predecessors; instance=D5/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/Main.makowski_schinzel_of_smooth_predecessors
   digest: Fixed-point smooth sums underestimate the finite reciprocal Euler mass. -/

import D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.Enumeration
import D5.S3.PrimeGaps.EulerProducts

/-! Interpret the tail constants as finite reciprocal sums and finite Euler products. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4000

namespace D5.S3.Arith.MakowskiSchinzel.SmoothPredecessor

open Finset

private theorem partial_branches_le (w : ℕ → ℕ) {s : Finset ℕ} {p X c : ℕ}
    (hp : p.Prime) (hps : p ∉ s) (hc : 0 < c) :
    (∑ e ∈ range 64, ∑ m ∈ factoredMultiples s X (c * p ^ e), w m) ≤
      ∑ m ∈ factoredMultiples (insert p s) X c, w m := by
  let E := Nat.equivProdNatFactoredNumbers hp hps
  have hquot (e m : ℕ) (hd : c * p ^ e ∣ m) :
      m / c = p ^ e * (m / (c * p ^ e)) := by
    obtain ⟨k, rfl⟩ := hd
    rw [Nat.mul_div_cancel_left _ (mul_pos hc (pow_pos hp.pos _)), mul_assoc,
      Nat.mul_div_cancel_left _ hc]
  rw [sum_sigma']
  apply sum_le_sum_of_injOn (fun x => x.2)
  · intro a ha b hb hab
    change a.2 = b.2 at hab
    have ha' := (mem_filter.mp (mem_sigma.mp ha).2).2
    have hb' := (mem_filter.mp (mem_sigma.mp hb).2).2
    have heq : E (a.1, ⟨a.2 / (c * p ^ a.1), ha'.2⟩) =
        E (b.1, ⟨b.2 / (c * p ^ b.1), hb'.2⟩) := by
      apply Subtype.ext
      change p ^ a.1 * (a.2 / (c * p ^ a.1)) =
        p ^ b.1 * (b.2 / (c * p ^ b.1))
      rw [← hquot _ _ ha'.1, ← hquot _ _ hb'.1, hab]
    have he : a.1 = b.1 := congrArg Prod.fst (E.injective heq)
    exact Sigma.ext he (heq_of_eq hab)
  · intro m hm
    obtain ⟨⟨e, m⟩, hx, rfl⟩ := mem_image.mp hm
    obtain ⟨_, hm⟩ := mem_sigma.mp hx
    obtain ⟨hmI, hdiv, hfact⟩ := mem_filter.mp hm
    refine mem_filter.mpr ⟨hmI, dvd_trans (dvd_mul_right c (p ^ e)) hdiv, ?_⟩
    rw [hquot e m hdiv]
    exact Nat.pow_mul_mem_factoredNumbers hp e hfact
  · intro i hi
    exact le_rfl
  · intro m hm hnot
    exact Nat.zero_le _

private theorem smoothSum_le_sum (w : ℕ → ℕ) (ps : List ℕ)
    (hprime : ∀ p ∈ ps, p.Prime) (hnodup : ps.Nodup) {X c : ℕ}
    (hc : 0 < c) (hcx : c ≤ X) :
    smoothSum w ps X c ≤ ∑ m ∈ factoredMultiples ps.toFinset X c, w m := by
  induction ps generalizing c with
  | nil =>
    have heq : factoredMultiples ∅ X c = {c} := by
      ext m
      constructor
      · intro hm
        obtain ⟨_, hd, hfact⟩ := mem_filter.mp hm
        have hquot : m / c = 1 := by
          simpa only [Nat.factoredNumbers_empty, Set.mem_singleton_iff] using hfact
        have hmc : c = m := by
          simpa only [hquot, mul_one] using Nat.mul_div_cancel' hd
        simpa only [mem_singleton] using hmc.symm
      · intro hm
        have hmc : m = c := mem_singleton.mp hm
        subst m
        refine mem_filter.mpr ⟨mem_Icc.mpr ⟨hc, hcx⟩, dvd_refl c, ?_⟩
        simp [Nat.factoredNumbers_empty, Nat.div_self hc]
    simp only [smoothSum, List.toFinset_nil, heq, sum_singleton, le_refl]
  | cons p ps ih =>
    obtain ⟨hnot, hnodup⟩ := List.nodup_cons.mp hnodup
    have hp := hprime p List.mem_cons_self
    have htail : ∀ r ∈ ps, r.Prime := fun r hr => hprime r (List.mem_cons_of_mem p hr)
    change powSum 64 (fun c' => smoothSum w ps X c') p X c ≤ _
    rw [(powSum_eq_sum_range _ _).mpr (Or.inr (Or.inl hp.one_lt.le)), List.toFinset_cons]
    apply le_trans (b := ∑ e ∈ range 64,
      ∑ m ∈ factoredMultiples ps.toFinset X (c * p ^ e), w m) ?_
      (partial_branches_le w hp (by simpa using hnot) hc)
    apply sum_le_sum
    intro e _
    by_cases he : c * p ^ e ≤ X
    · rw [if_pos he]
      exact ih htail hnodup (mul_pos hc (pow_pos hp.pos e)) he
    · rw [if_neg he]
      have hempty : factoredMultiples ps.toFinset X (c * p ^ e) = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro m hm
        obtain ⟨hmI, hd, _⟩ := mem_filter.mp hm
        have hmpos : 0 < m := (mem_Icc.mp hmI).1
        have hmX := (mem_Icc.mp hmI).2
        have hle := Nat.le_of_dvd hmpos hd
        omega
      simp only [hempty, sum_empty, le_refl]


/-- Flooring each scaled reciprocal gives a lower bound for their exact weighted sum. -/
theorem smooth_floor_sum_le (ps : List ℕ) (hprime : ∀ p ∈ ps, p.Prime)
    (hnodup : ps.Nodup) {X d : ℕ} (hX : ps = [] → 1 ≤ X ∨ scale / d = 0) :
    (smoothSum (fun m => scale / (d * m)) ps X 1 : ℝ) / scale ≤
      ∑ m ∈ factoredMultiples ps.toFinset X 1, 1 / ((d : ℝ) * m) := by
  by_cases hz : X = 0
  · subst X
    cases ps with
    | nil =>
      have hw : scale / d = 0 := (hX rfl).resolve_left (by omega)
      simp [smoothSum, hw, factoredMultiples]
    | cons p ps => simp [smoothSum, powSum, factoredMultiples]
  have hpos : 1 ≤ X := by omega
  have hle := smoothSum_le_sum (fun m => scale / (d * m)) ps hprime hnodup
    (by decide) hpos
  apply le_trans (div_le_div_of_nonneg_right (Nat.cast_le.mpr hle) (by positivity))
  rw [Nat.cast_sum, sum_div]
  apply sum_le_sum
  intro m _
  have hs : (0 : ℝ) < scale := by norm_num [scale]
  have hdiv := div_le_div_of_nonneg_right
    (Nat.cast_div_le (m := scale) (n := d * m) :
      ((scale / (d * m) : ℕ) : ℝ) ≤ (scale : ℝ) / (d * m : ℕ)) hs.le
  rw [div_right_comm, div_self hs.ne', Nat.cast_mul] at hdiv
  exact hdiv

/-- The primes retained below an odd label are exactly all primes at most that label. -/
private theorem label_primes_eq {p : ℕ} (hp : p ≤ 100) :
    (allPrimes.filter (· ≤ p)).toFinset = p.primesLE := by
  have hall : allPrimes.toFinset = Nat.primesLE 97 := by decide +kernel
  have hgap : ∀ q ∈ Nat.primesLE 100, q ≤ 97 := by decide +kernel
  ext q
  simp only [List.toFinset_filter, hall, mem_filter, Nat.mem_primesLE, decide_eq_true_eq]
  constructor
  · intro h
    exact ⟨h.2, h.1.2⟩
  · intro h
    exact ⟨⟨hgap q (Nat.mem_primesLE.mpr ⟨h.1.trans hp, h.2⟩), h.2⟩, h.1⟩

/-- The stored floor sum is below the finite smooth reciprocal mass that it approximates. -/
theorem tail_floor_sum_le (p : ℕ) :
    ((tailData p).2.2 : ℝ) / scale ≤
      ∑ m ∈ factoredMultiples (allPrimes.filter (· ≤ p)).toFinset
          (bound / (2 * p)) 1, 1 / (2 * (p : ℝ) * m) := by
  let rs := allPrimes.filter (· ≤ p)
  have hpr : ∀ q ∈ rs, q.Prime := by
    intro q hq
    have hmem : q ∈ allPrimes := List.mem_of_mem_filter hq
    have hall : allPrimes.all (fun r => decide r.Prime) = true := by decide +kernel
    exact of_decide_eq_true ((List.all_eq_true.mp hall) q hmem)
  have hn : rs.Nodup := (show allPrimes.Nodup by decide +kernel).filter _
  by_cases hb : 1 ≤ (bound / (2 * p) : ℕ)
  · have hh := smooth_floor_sum_le rs hpr hn (fun _ => Or.inl hb) (d := 2 * p)
    simpa only [tailData, rs, Nat.cast_mul, Nat.cast_ofNat, mul_assoc] using hh
  · have hb0 : bound / (2 * p) = 0 := Nat.lt_one_iff.mp (Nat.lt_of_not_ge hb)
    have hz : (tailData p).2.2 = 0 := by
      change smoothSum (fun c => scale / (2 * p * c)) rs (bound / (2 * p)) 1 = 0
      rw [hb0]
      cases hrs : rs with
      | nil =>
        have hp2 : p < 2 := by
          by_contra hn
          have : 2 ∈ rs := List.mem_filter.mpr
            ⟨by simp [allPrimes], by simpa using (show 2 ≤ p by omega)⟩
          simp [hrs] at this
        interval_cases p
        · simp [smoothSum]
        · norm_num [bound] at hb0
      | cons q qs => rfl
    rw [hz]
    simp only [Nat.cast_zero, zero_div]
    positivity

/-- The stored ratio equals the finite Euler product exactly through label 100. -/
theorem tail_euler_ratio {p : ℕ} :
    LongGapsBetweenPrimes.eulerProduct p 1 =
      ((tailData p).1 : ℝ) / (tailData p).2.1 ↔ p ≤ 100 := by
  have hratio {p : ℕ} (hp : p ≤ 100) :
      LongGapsBetweenPrimes.eulerProduct p 1 =
        ((tailData p).1 : ℝ) / (tailData p).2.1 := by
    let rs := allPrimes.filter (· ≤ p)
    have hn : rs.Nodup := (show allPrimes.Nodup by decide +kernel).filter _
    have heq : rs.toFinset = p.primesLE := label_primes_eq hp
    have hnum : (tailData p).1 = ∏ q ∈ rs.toFinset, q := by
      change rs.foldl (· * ·) 1 = _
      rw [List.prod_toFinset _ hn]
      simpa only [List.map_id, List.map_id'] using (List.prod_eq_foldl (xs := rs)).symm
    have hden : (tailData p).2.1 = ∏ q ∈ rs.toFinset, (q - 1) := by
      change rs.foldl (fun a r => a * (r - 1)) 1 = _
      rw [List.prod_toFinset _ hn, List.prod_eq_foldl, List.foldl_map]
    rw [LongGapsBetweenPrimes.eulerProduct, ← heq, hnum, hden,
      Nat.cast_prod, Nat.cast_prod, ← prod_div_distrib]
    apply prod_congr rfl
    intro q hq
    have hq2 := (Nat.prime_of_mem_primesLE (heq ▸ hq)).two_le
    have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
    have hq1 : (q : ℝ) - 1 ≠ 0 := by
      have : (2 : ℝ) ≤ q := by exact_mod_cast hq2
      linarith
    rw [Real.rpow_neg_one, Nat.cast_sub (by omega : 1 ≤ q), Nat.cast_one]
    field_simp [hq0, hq1]

  refine ⟨?_, hratio⟩
  intro heq
  by_contra hp
  have hp101 : 101 ≤ p := by omega
  have hfilter (n : ℕ) (hn : 100 ≤ n) : allPrimes.filter (· ≤ n) = allPrimes := by
    apply List.filter_eq_self.mpr
    intro q hq
    have hall : ∀ q ∈ allPrimes, q ≤ 100 := by decide +kernel
    simpa using (hall q hq).trans hn
  have hstored : ((tailData p).1 : ℝ) / (tailData p).2.1 =
      ((tailData 100).1 : ℝ) / (tailData 100).2.1 := by
    simp only [tailData, hfilter p (by omega), hfilter 100 le_rfl]
  have hfactor {q : ℕ} (hq : q.Prime) : 1 ≤ (1 - (q : ℝ) ^ (-(1 : ℝ)))⁻¹ := by
    have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq.two_le
    rw [Real.rpow_neg_one]
    have hq0 : (0 : ℝ) < q := by linarith
    have hinv : (q : ℝ)⁻¹ < 1 := (inv_lt_one₀ hq0).mpr (by linarith)
    have hden : 0 < 1 - (q : ℝ)⁻¹ := by linarith
    have hupper : 1 - (q : ℝ)⁻¹ ≤ 1 := sub_le_self _ (inv_nonneg.mpr hq0.le)
    simpa only [one_div, inv_one] using one_div_le_one_div_of_le hden hupper
  have hmono : LongGapsBetweenPrimes.eulerProduct 101 1 ≤
      LongGapsBetweenPrimes.eulerProduct p 1 := by
    apply Finset.prod_le_prod_of_subset_of_one_le₀ (Nat.primesLE_mono hp101)
    · intro q hq
      exact zero_le_one.trans (hfactor (Nat.prime_of_mem_primesLE hq))
    · intro q hq _
      exact hfactor (Nat.prime_of_mem_primesLE hq)
  have hset : Nat.primesLE 101 = insert 101 (Nat.primesLE 100) := by decide +kernel
  have hnot : 101 ∉ Nat.primesLE 100 := by decide +kernel
  have hstep : LongGapsBetweenPrimes.eulerProduct 101 1 =
      (101 / 100 : ℝ) * LongGapsBetweenPrimes.eulerProduct 100 1 := by
    simp only [LongGapsBetweenPrimes.eulerProduct, hset, prod_insert hnot]
    norm_num [Real.rpow_neg_one]
  have hpos := LongGapsBetweenPrimes.eulerProduct_pos 100 (by norm_num : (0 : ℝ) < 1)
  rw [hstep, heq, hstored, ← hratio (p := 100) le_rfl] at hmono
  nlinarith

/-- A finite actual tail uses only the Euler mass left after the small smooth numbers. -/
theorem reciprocal_tail_bound {p b fs : ℕ} (hp : 0 < p) (T : Finset ℕ)
    (hT : ∀ q ∈ T, ∃ m : ℕ, b < m ∧ q = 2 * p * m + 1 ∧
      m ∈ Nat.smoothNumbers (p + 1))
    (hfs : (fs : ℝ) / scale ≤
      ∑ m ∈ (Icc 1 b).filter (fun m => m ∈ Nat.smoothNumbers (p + 1)),
        1 / (2 * (p : ℝ) * m)) :
    (∑ q ∈ T, 1 / (q : ℝ)) ≤
      LongGapsBetweenPrimes.eulerProduct p 1 / (2 * (p : ℝ)) - (fs : ℝ) / scale ∧
    (T.Nonempty → (∑ q ∈ T, 1 / (q : ℝ)) <
      LongGapsBetweenPrimes.eulerProduct p 1 / (2 * (p : ℝ)) - (fs : ℝ) / scale) := by
  classical
  let u : ℕ → ℕ := fun q => (q - 1) / (2 * p)
  let S := (Icc 1 b).filter (fun m => m ∈ Nat.smoothNumbers (p + 1))
  let M := T.image u
  have hD : (0 : ℝ) < 2 * (p : ℝ) := by positivity
  have hu (q : ℕ) (hq : q ∈ T) :
      b < u q ∧ q = 2 * p * u q + 1 ∧ u q ∈ Nat.smoothNumbers (p + 1) := by
    obtain ⟨m, hbm, hqm, hm⟩ := hT q hq
    have hum : u q = m := by simp [u, hqm, Nat.mul_div_cancel_left _ (by omega : 0 < 2 * p)]
    simpa only [hum] using And.intro hbm (And.intro hqm hm)
  have hinj : Set.InjOn u T := by
    intro q hq r hr hqr
    rw [(hu q hq).2.1, (hu r hr).2.1, hqr]
  have hdis : Disjoint S M := by
    apply disjoint_left.mpr
    intro m hm hm'
    obtain ⟨q, hq, rfl⟩ := mem_image.mp hm'
    have hb := (mem_Icc.mp (mem_filter.mp hm).1).2
    exact (not_lt_of_ge hb) (hu q hq).1
  have hsum := LongGapsBetweenPrimes.sum_smooth_le_eulerProduct
    (N := p) (σ := 1) (by norm_num) (S ∪ M) (by
      intro m hm
      rcases mem_union.mp hm with hm | hm
      · exact (mem_filter.mp hm).2
      · obtain ⟨q, hq, rfl⟩ := mem_image.mp hm
        exact (hu q hq).2.2)
  simp only [Real.rpow_neg_one] at hsum
  rw [sum_union hdis] at hsum
  have hsmall : (∑ m ∈ S, 1 / (2 * (p : ℝ) * m)) =
      (∑ m ∈ S, (m : ℝ)⁻¹) / (2 * (p : ℝ)) := by
    rw [sum_div]
    apply sum_congr rfl
    intro m hm
    simp only [one_div, mul_inv_rev]
    ring
  have hlarge : (∑ q ∈ T, 1 / (2 * (p : ℝ) * u q)) =
      (∑ m ∈ M, (m : ℝ)⁻¹) / (2 * (p : ℝ)) := by
    rw [show M = T.image u from rfl, sum_image hinj, sum_div]
    apply sum_congr rfl
    intro q hq
    simp only [one_div, mul_inv_rev]
    ring
  have hqle : (∑ q ∈ T, 1 / (q : ℝ)) ≤
      ∑ q ∈ T, 1 / (2 * (p : ℝ) * u q) := by
    apply sum_le_sum
    intro q hq
    have hu0 : 0 < u q := by have := (hu q hq).1; omega
    have hqu : (q : ℝ) = 2 * (p : ℝ) * u q + 1 := by
      exact_mod_cast (hu q hq).2.1
    apply one_div_le_one_div_of_le (by positivity)
    linarith
  have hboth : (∑ m ∈ S, 1 / (2 * (p : ℝ) * m)) +
      (∑ q ∈ T, 1 / (2 * (p : ℝ) * u q)) ≤
      LongGapsBetweenPrimes.eulerProduct p 1 / (2 * (p : ℝ)) := by
    rw [hsmall, hlarge, ← add_div]
    exact div_le_div_of_nonneg_right hsum hD.le
  change (fs : ℝ) / scale ≤ ∑ m ∈ S, 1 / (2 * (p : ℝ) * m) at hfs
  constructor
  · linarith
  · intro hnonempty
    have hstrict : (∑ q ∈ T, 1 / (q : ℝ)) <
        ∑ q ∈ T, 1 / (2 * (p : ℝ) * u q) := by
      apply sum_lt_sum
      · intro q hq
        have hu0 : 0 < u q := by have := (hu q hq).1; omega
        have hqu : (q : ℝ) = 2 * (p : ℝ) * u q + 1 := by
          exact_mod_cast (hu q hq).2.1
        exact (one_div_lt_one_div_of_lt (by positivity) (by linarith)).le
      · obtain ⟨q, hq⟩ := hnonempty
        refine ⟨q, hq, ?_⟩
        have hu0 : 0 < u q := by have := (hu q hq).1; omega
        have hqu : (q : ℝ) = 2 * (p : ℝ) * u q + 1 := by
          exact_mod_cast (hu q hq).2.1
        exact one_div_lt_one_div_of_lt (by positivity) (by linarith)
    linarith

end D5.S3.Arith.MakowskiSchinzel.SmoothPredecessor
