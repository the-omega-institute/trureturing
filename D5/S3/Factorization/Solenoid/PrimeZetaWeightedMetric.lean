/- GID: D5/S3/Factorization/Solenoid/PrimeZetaWeightedMetric
   generality: G
   mirror-B: D5/B/S3/Factorization/Solenoid/PrimeZetaWeightedMetric
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Prime-zeta weighted p-adic distance metrizes the hidden-address product topology. -/

import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Topology.MetricSpace.PiNat

/- Library-search audit trail (2026-08-28):
   * Exact pinned-Mathlib hit `Nat.Primes.summable_rpow` proves summability of
     the source weights when `1 < s`; `PadicInt.norm_le_one` bounds every
     coordinate distance by one.
   * `PiCountable.metricSpace` is a close construction using encoded geometric
     weights, but it does not expose the source's prime-zeta weights. Its finite
     coordinate and summable-tail proof pattern is reused here.
   * Repository body-shape searches found prime-indexed power sums and the raw
     all-prime p-adic product, but no definition of this normalized distance or
     a metric inducing the product topology from these weights. -/

namespace D5.S3.Factorization.Solenoid.PrimeZetaWeightedMetric

open Filter Set Topology
open scoped Topology

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

private instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

/-- The prime-zeta normalizing sum used by the weighted hidden-address metric. -/
def primeZetaWeightSum (s : ℝ) : ℝ :=
  ∑' p : Nat.Primes, (p : ℝ) ^ (-s)

/-- The normalized prime-zeta weighted sum of the standard p-adic coordinate
distances on the all-prime hidden-address product. -/
def primeWeightedDistance (s : ℝ)
    (u v : ∀ p : Nat.Primes, ℤ_[p.1]) : ℝ :=
  (∑' p : Nat.Primes, (p : ℝ) ^ (-s) * dist (u p) (v p)) /
    primeZetaWeightSum s

private theorem prime_weight_summable (s : ℝ) (hs : 1 < s) :
    Summable (fun p : Nat.Primes => (p : ℝ) ^ (-s)) := by
  exact Nat.Primes.summable_rpow.mpr (by linarith)

private theorem prime_weight_pos (s : ℝ) (p : Nat.Primes) :
    0 < (p : ℝ) ^ (-s) :=
  Real.rpow_pos_of_pos (by exact_mod_cast p.2.pos) _

private theorem prime_zeta_pos (s : ℝ) (hs : 1 < s) :
    0 < primeZetaWeightSum s := by
  let p : Nat.Primes := ⟨2, Nat.prime_two⟩
  exact (prime_weight_summable s hs).tsum_pos
    (fun q => (prime_weight_pos s q).le) p (prime_weight_pos s p)

private theorem padic_distance_le_one (p : Nat.Primes)
    (x y : ℤ_[p.1]) : dist x y ≤ 1 := by
  rw [dist_eq_norm]
  exact PadicInt.norm_le_one (x - y)

private theorem weighted_terms_summable (s : ℝ) (hs : 1 < s)
    (u v : ∀ p : Nat.Primes, ℤ_[p.1]) :
    Summable (fun p : Nat.Primes =>
      (p : ℝ) ^ (-s) * dist (u p) (v p)) := by
  refine Summable.of_nonneg_of_le
    (fun p => mul_nonneg (prime_weight_pos s p).le dist_nonneg)
    (fun p => ?_) (prime_weight_summable s hs)
  simpa using mul_le_mul_of_nonneg_left
    (padic_distance_le_one p (u p) (v p)) (prime_weight_pos s p).le

private theorem prime_weighted_distance_self (s : ℝ)
    (u : ∀ p : Nat.Primes, ℤ_[p.1]) :
    primeWeightedDistance s u u = 0 := by
  simp [primeWeightedDistance]

private theorem prime_weighted_distance_comm (s : ℝ)
    (u v : ∀ p : Nat.Primes, ℤ_[p.1]) :
    primeWeightedDistance s u v = primeWeightedDistance s v u := by
  unfold primeWeightedDistance
  congr 1
  apply tsum_congr
  intro p
  rw [dist_comm]

private theorem prime_weighted_distance_triangle (s : ℝ) (hs : 1 < s)
    (u v w : ∀ p : Nat.Primes, ℤ_[p.1]) :
    primeWeightedDistance s u w ≤
      primeWeightedDistance s u v + primeWeightedDistance s v w := by
  have hzeta := prime_zeta_pos s hs
  have huv := weighted_terms_summable s hs u v
  have hvw := weighted_terms_summable s hs v w
  rw [primeWeightedDistance, primeWeightedDistance, primeWeightedDistance, ← add_div]
  apply (div_le_div_iff_of_pos_right hzeta).2
  rw [← huv.tsum_add hvw]
  exact (weighted_terms_summable s hs u w).tsum_le_tsum
    (fun p => by
      simpa [mul_add] using mul_le_mul_of_nonneg_left
        (dist_triangle (u p) (v p) (w p)) (prime_weight_pos s p).le)
    (huv.add hvw)

private theorem prime_weighted_distance_eq_zero (s : ℝ) (hs : 1 < s)
    (u v : ∀ p : Nat.Primes, ℤ_[p.1])
    (hzero : primeWeightedDistance s u v = 0) : u = v := by
  have hzeta := prime_zeta_pos s hs
  have hsum := weighted_terms_summable s hs u v
  have htotal :
      (∑' p : Nat.Primes, (p : ℝ) ^ (-s) * dist (u p) (v p)) = 0 := by
    exact (div_eq_zero_iff.mp (by simpa [primeWeightedDistance] using hzero)).resolve_right
      hzeta.ne'
  funext p
  have hterm_nonneg : 0 ≤ (p : ℝ) ^ (-s) * dist (u p) (v p) :=
    mul_nonneg (prime_weight_pos s p).le dist_nonneg
  have hterm_le :
      (p : ℝ) ^ (-s) * dist (u p) (v p) ≤
        ∑' q : Nat.Primes, (q : ℝ) ^ (-s) * dist (u q) (v q) :=
    hsum.le_tsum p (fun q _ =>
      mul_nonneg (prime_weight_pos s q).le dist_nonneg)
  have hterm_zero : (p : ℝ) ^ (-s) * dist (u p) (v p) = 0 := by
    apply le_antisymm
    · simpa [htotal] using hterm_le
    · exact hterm_nonneg
  exact eq_of_dist_eq_zero
    ((mul_eq_zero.mp hterm_zero).resolve_left (prime_weight_pos s p).ne')

private theorem prime_weighted_isOpen_iff (s : ℝ) (hs : 1 < s)
    (s' : Set (∀ p : Nat.Primes, ℤ_[p.1])) :
    IsOpen s' ↔
      ∀ x ∈ s', ∃ ε > 0, ∀ y, primeWeightedDistance s x y < ε → y ∈ s' := by
  have hzeta := prime_zeta_pos s hs
  constructor
  · intro hopen x hx
    rcases isOpen_pi_iff.mp hopen x hx with ⟨places, U, hU, hUs⟩
    classical
    have hradius : ∀ p : Nat.Primes, ∃ r > 0,
        Metric.ball (x p) r ⊆ if p ∈ places then U p else Set.univ := by
      intro p
      by_cases hp : p ∈ places
      · rcases Metric.isOpen_iff.mp (hU p hp).1 (x p) (hU p hp).2 with
          ⟨r, hrpos, hr⟩
        exact ⟨r, hrpos, by simpa [hp] using hr⟩
      · exact ⟨1, zero_lt_one, by simp [hp]⟩
    choose radius hradius_pos hradius_sub using hradius
    let factor : Nat.Primes -> ℝ := fun p =>
      min 1 ((p : ℝ) ^ (-s) * radius p / primeZetaWeightSum s)
    let ε : ℝ := ∏ p ∈ places, factor p
    have hfactor_pos : ∀ p, 0 < factor p := by
      intro p
      exact lt_min zero_lt_one
        (div_pos (mul_pos (prime_weight_pos s p) (hradius_pos p)) hzeta)
    have hfactor_le_one : ∀ p, factor p ≤ 1 := fun p => min_le_left _ _
    have hεpos : 0 < ε := by
      exact Finset.prod_pos fun p hp => hfactor_pos p
    refine ⟨ε, hεpos, fun y hy => hUs ?_⟩
    intro p hp
    have hp' : p ∈ places := hp
    have hpball : y p ∈ Metric.ball (x p) (radius p) := by
      rw [Metric.mem_ball]
      have hterms := weighted_terms_summable s hs x y
      have hterm_le :
          (p : ℝ) ^ (-s) * dist (x p) (y p) ≤
            ∑' q : Nat.Primes, (q : ℝ) ^ (-s) * dist (x q) (y q) :=
        hterms.le_tsum p (fun q _ =>
          mul_nonneg (prime_weight_pos s q).le dist_nonneg)
      have hε_le_factor : ε ≤ factor p := by
        dsimp [ε]
        rw [← Finset.mul_prod_erase places factor hp']
        exact mul_le_of_le_one_right (hfactor_pos p).le
          (Finset.prod_le_one
            (fun q hq => (hfactor_pos q).le)
            (fun q hq => hfactor_le_one q))
      have hdistance_lt :
          (p : ℝ) ^ (-s) * dist (x p) (y p) / primeZetaWeightSum s <
            (p : ℝ) ^ (-s) * radius p / primeZetaWeightSum s := by
        apply (div_le_div_of_nonneg_right hterm_le hzeta.le).trans_lt
        exact hy.trans_le (hε_le_factor.trans (min_le_right _ _))
      have hmul_lt := (div_lt_div_iff_of_pos_right hzeta).mp hdistance_lt
      simpa [dist_comm] using
        lt_of_mul_lt_mul_left hmul_lt (prime_weight_pos s p).le
    have hmem := hradius_sub p hpball
    simpa [hp'] using hmem
  · intro hmetric
    apply isOpen_iff_forall_mem_open.mpr
    intro x hx
    rcases hmetric x hx with ⟨ε, hεpos, hε⟩
    obtain ⟨places, htail⟩ : ∃ places : Finset Nat.Primes,
        (∑' p : {q : Nat.Primes // q ∉ places}, ((p : Nat.Primes) : ℝ) ^ (-s)) <
          ε * primeZetaWeightSum s / 2 := by
      exact ((tendsto_order.1 (tendsto_tsum_compl_atTop_zero
        (fun p : Nat.Primes => (p : ℝ) ^ (-s)))).2 _
          (div_pos (mul_pos hεpos hzeta) zero_lt_two)).exists
    let radius : Nat.Primes -> ℝ := fun p =>
      ε * primeZetaWeightSum s /
        (2 * (places.card + 1) * (p : ℝ) ^ (-s))
    let neighborhood : Set (∀ p : Nat.Primes, ℤ_[p.1]) :=
      (places : Set Nat.Primes).pi fun p => Metric.ball (x p) (radius p)
    have hradius_pos : ∀ p, 0 < radius p := by
      intro p
      exact div_pos (mul_pos hεpos hzeta)
        (mul_pos (mul_pos zero_lt_two (by positivity)) (prime_weight_pos s p))
    have hopen_neighborhood : IsOpen neighborhood := by
      exact isOpen_set_pi places.finite_toSet fun p hp => Metric.isOpen_ball
    have hx_neighborhood : x ∈ neighborhood := by
      intro p hp
      simpa [Metric.mem_ball] using hradius_pos p
    refine ⟨neighborhood, ?_, hopen_neighborhood, hx_neighborhood⟩
    intro y hy
    apply hε y
    have hterms := weighted_terms_summable s hs x y
    have hfinite :
        (∑ p ∈ places, (p : ℝ) ^ (-s) * dist (x p) (y p)) <
          ε * primeZetaWeightSum s / 2 := by
      calc
        (∑ p ∈ places, (p : ℝ) ^ (-s) * dist (x p) (y p))
            ≤ ∑ p ∈ places,
                ε * primeZetaWeightSum s / (2 * (places.card + 1)) := by
              apply Finset.sum_le_sum
              intro p hp
              have hpball := hy p hp
              rw [Metric.mem_ball] at hpball
              rw [dist_comm] at hpball
              have hmul := mul_le_mul_of_nonneg_left hpball.le
                (prime_weight_pos s p).le
              have hdenpos : 0 < (p : ℝ) ^ (-s) := prime_weight_pos s p
              dsimp [radius] at hmul
              calc
                (p : ℝ) ^ (-s) * dist (x p) (y p)
                    ≤ (p : ℝ) ^ (-s) *
                        (ε * primeZetaWeightSum s /
                          (2 * (places.card + 1) * (p : ℝ) ^ (-s))) := hmul
                _ = ε * primeZetaWeightSum s / (2 * (places.card + 1)) := by
                  field_simp [hdenpos.ne']
        _ = places.card *
              (ε * primeZetaWeightSum s / (2 * (places.card + 1))) := by simp
        _ < ε * primeZetaWeightSum s / 2 := by
          have hcard : (places.card : ℝ) < places.card + 1 := by norm_num
          rw [← mul_div_assoc]
          apply (div_lt_div_iff₀ (by positivity :
            (0 : ℝ) < 2 * (places.card + 1)) zero_lt_two).2
          nlinarith [mul_pos hεpos hzeta]
    have htail_terms :
        (∑' p : {q : Nat.Primes // q ∉ places},
          (((p : Nat.Primes) : ℝ) ^ (-s) * dist (x p) (y p))) <
            ε * primeZetaWeightSum s / 2 := by
      apply lt_of_le_of_lt ?_ htail
      exact (hterms.subtype _).tsum_le_tsum
        (fun p => by
          simpa using mul_le_mul_of_nonneg_left
            (padic_distance_le_one (p : Nat.Primes) (x p) (y p))
            (prime_weight_pos s (p : Nat.Primes)).le)
        ((prime_weight_summable s hs).subtype _)
    rw [primeWeightedDistance]
    apply (div_lt_iff₀ hzeta).2
    rw [← hterms.sum_add_tsum_compl (s := places)]
    calc
      (∑ p ∈ places, (p : ℝ) ^ (-s) * dist (x p) (y p)) +
          ∑' p : ↑(↑places : Set Nat.Primes)ᶜ,
            ((p : Nat.Primes) : ℝ) ^ (-s) * dist (x p) (y p) <
          ε * primeZetaWeightSum s / 2 +
            ε * primeZetaWeightSum s / 2 :=
        add_lt_add hfinite htail_terms
      _ = ε * primeZetaWeightSum s := by ring

/-- The exact prime-zeta weighted distance satisfies the four metric laws, and
its open-ball characterization agrees with the product topology. -/
theorem prime_weighted_distance_is_metric_and_induces_product_topology
    (s : ℝ) (hs : 1 < s) :
    (∀ u : ∀ p : Nat.Primes, ℤ_[p.1],
      primeWeightedDistance s u u = 0) ∧
    (∀ u v : ∀ p : Nat.Primes, ℤ_[p.1],
      primeWeightedDistance s u v = primeWeightedDistance s v u) ∧
    (∀ u v w : ∀ p : Nat.Primes, ℤ_[p.1],
      primeWeightedDistance s u w ≤
        primeWeightedDistance s u v + primeWeightedDistance s v w) ∧
    (∀ u v : ∀ p : Nat.Primes, ℤ_[p.1],
      primeWeightedDistance s u v = 0 → u = v) ∧
    (∀ t : Set (∀ p : Nat.Primes, ℤ_[p.1]),
      IsOpen t ↔ ∀ u ∈ t, ∃ ε > 0, ∀ v,
        primeWeightedDistance s u v < ε → v ∈ t) := by
  exact ⟨prime_weighted_distance_self s,
    prime_weighted_distance_comm s,
    prime_weighted_distance_triangle s hs,
    prime_weighted_distance_eq_zero s hs,
    prime_weighted_isOpen_iff s hs⟩

#print axioms primeZetaWeightSum
#print axioms primeWeightedDistance
#print axioms prime_weighted_distance_is_metric_and_induces_product_topology

end

end D5.S3.Factorization.Solenoid.PrimeZetaWeightedMetric
