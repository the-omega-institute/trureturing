/- GID: D5/S3/Arith/Abundancy/ZelinskyPrimitiveAbundantLowerBound
   generality: G
   mirror-B: D5/B/S3/Arith/Abundancy/ZelinskyPrimitiveAbundantLowerBound
   mirror-E: none(waiver:symbolic-asymptotic-lower-bound)
   anchors: []
   utility: none
   digest: Odd squarefree primitive non-deficient integers avoiding finite prime sets. -/

import D5.S3.Arith.Abundancy.ZelinskyZhangDoublePrimitive
import D5.S3.Arith.Robin.Analytic.OmegaTail.Lower
import D5.S3.Arith.Abundancy.ZelinskyDeficientCore
import D5.S3.Arith.Robin.PriceRecord.QuantitativePrimeAbel
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.GCD.BigOperators

/-! Quantitative prime selection produces many primitive non-deficient integers. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Finset Real Filter
open scoped BigOperators Topology

namespace D5.S3.Arith.Abundancy.ZelinskyPrimitiveAbundantLowerBound

open D5.S3.Arith.Robin.PriceRecord.QuantitativePrimeAbel
open ZelinskyZhangDoublePrimitive (PrimitiveNonDeficient)
open ZelinskyZhangKLPrimitive (Deficient sig sig_prime_mul)

private def eulerH (s : Finset ℕ) : ℝ := ∏ p ∈ s, (1 + 1 / (p : ℝ))

private lemma eulerH_pos (s : Finset ℕ) : 0 < eulerH s :=
  prod_pos (fun p _ => by positivity)

private lemma ratio_product (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    sig (∏ p ∈ s, p) / (∏ p ∈ s, p) = eulerH s := by
  simp only [sig, eulerH]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_prod_of_prime _ hs]
  push_cast
  rw [← Finset.prod_div_distrib]
  apply prod_congr rfl
  intro p hp
  rw [D5.S3.Factorization.ReciprocalSigmaThreshold.sigma_prime (hs p hp)]
  push_cast
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (hs p hp).ne_zero
  field_simp [hp0]


private lemma product_squarefree (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    Squarefree (∏ p ∈ s, p) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    exact Nat.coprime_iff_isRelPrime.mp
      ((Nat.coprime_primes (hs p hp) (hs q hq)).mpr hpq)
  · exact fun p hp => (hs p hp).squarefree

private lemma prime_mem_of_dvd_product (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime) {p : ℕ} (hp : p.Prime)
    (hd : p ∣ ∏ q ∈ s, q) : p ∈ s := by
  obtain ⟨q, hq, hpq⟩ := (hp.prime.dvd_finsetProd_iff id).mp hd
  have he : p = q := (Nat.prime_dvd_prime_iff_eq hp (hs q hq)).mp hpq
  exact he ▸ hq

private lemma primitive_of_erase (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    (hab : 2 ≤ eulerH s) (herase : ∀ p ∈ s, eulerH (s.erase p) < 2) :
    PrimitiveNonDeficient (∏ p ∈ s, p) := by
  classical
  have hn : 0 < ∏ p ∈ s, p := Finset.prod_pos (fun p hp => (hs p hp).pos)
  have hnR : (0 : ℝ) < ∏ p ∈ s, p := by exact_mod_cast hn
  constructor
  · change ¬ sig (∏ p ∈ s, p) < 2 * (∏ p ∈ s, p)
    rw [← ratio_product s hs] at hab
    exact not_lt.mpr ((le_div_iff₀ hnR).mp hab)
  · intro d hd hlt
    have hdn := Nat.dvd_of_mem_divisors hd
    have hdpos := Nat.pos_of_mem_divisors hd
    have hepos : 0 < (∏ p ∈ s, p) / d := Nat.div_pos (Nat.le_of_dvd hn hdn) hdpos
    have hene : (∏ p ∈ s, p) / d ≠ 1 := by
      intro he
      have hh := Nat.div_mul_cancel hdn
      rw [he, one_mul] at hh
      omega
    obtain ⟨p, hp, hpe⟩ := Nat.exists_prime_and_dvd hene
    have hpn : p ∣ ∏ q ∈ s, q :=
      hpe.trans (Nat.div_dvd_of_dvd hdn)
    have hps := prime_mem_of_dvd_product s hs hp hpn
    have hprod : p * (∏ q ∈ s.erase p, q) = ∏ q ∈ s, q :=
      mul_prod_erase s id hps
    have hdp : d ∣ ∏ q ∈ s.erase p, q := by
      have hmul : p * d ∣ ∏ q ∈ s, q := by
        obtain ⟨a, ha⟩ := hpe
        refine ⟨a, ?_⟩
        calc
          _ = ((∏ q ∈ s, q) / d) * d := (Nat.div_mul_cancel hdn).symm
          _ = (p * a) * d := by rw [ha]
          _ = (p * d) * a := by ring
      rw [← hprod] at hmul
      exact (Nat.mul_dvd_mul_iff_left hp.pos).mp hmul
    have hsmall : 0 < ∏ q ∈ s.erase p, q :=
      Finset.prod_pos (fun q hq => (hs q (mem_of_mem_erase hq)).pos)
    have hm := D5.S3.Arith.Robin.GA2ForcedPrimeSource.abundancy_mono
      hdpos hsmall hdp
    change sig d < 2 * d
    apply (div_lt_iff₀ (show (0 : ℝ) < d by exact_mod_cast hdpos)).mp
    apply hm.trans_lt
    change sig _ / _ < 2
    rw [ratio_product _ (fun q hq => hs q (mem_of_mem_erase hq))]
    exact herase p hps

private lemma strict_bernoulli (a : ℝ) (ha : 0 < a) (k : ℕ) (hk : 2 ≤ k) :
    1 + 1 / a < (1 + 1 / ((k : ℝ) * a)) ^ k := by
  have hkR : (1 : ℝ) < k := by exact_mod_cast (show 1 < k by omega)
  have hpos : 0 < 1 / ((k : ℝ) * a) := by positivity
  have h := one_add_mul_self_lt_rpow_one_add
    (s := 1 / ((k : ℝ) * a)) (by linarith) hpos.ne' hkR
  rw [rpow_natCast] at h
  convert h using 1
  congr 1
  field_simp

private lemma block_product_lower (s : Finset ℕ) (a : ℝ) (ha : 0 < a)
    (hk : 2 ≤ s.card) (hs : ∀ q ∈ s, (0 : ℝ) < q ∧ (q : ℝ) ≤ s.card * a) :
    1 + 1 / a < eulerH s := by
  apply (strict_bernoulli a ha s.card hk).trans_le
  change _ ≤ ∏ q ∈ s, (1 + 1 / (q : ℝ))
  rw [← Finset.prod_const (s := s)]
  exact Finset.prod_le_prod₀ (fun _ _ => by positivity) (fun q hq =>
    add_le_add le_rfl (one_div_le_one_div_of_le (hs q hq).1 (hs q hq).2))

private lemma block_product_upper (s : Finset ℕ) (a : ℝ) (ha : 0 < a)
    (hs : s.Nonempty) (hlo : ∀ q ∈ s, (s.card : ℝ) * (a + 1) < q) :
    eulerH s < 1 + 1 / a := by
  have hk : (0 : ℝ) < s.card := by exact_mod_cast card_pos.mpr hs
  have hy : 0 < (s.card : ℝ) * (a + 1) := by positivity
  have hsum : (∑ q ∈ s, 1 / (q : ℝ)) < 1 / (a + 1) := by
    calc
      _ < ∑ _q ∈ s, 1 / ((s.card : ℝ) * (a + 1)) := by
        apply sum_lt_sum_of_nonempty hs
        intro q hq
        exact one_div_lt_one_div_of_lt hy (hlo q hq)
      _ = 1 / (a + 1) := by simp; field_simp
  have hlog : 1 / (a + 1) ≤ log (1 + 1 / a) := by
    convert one_sub_inv_le_log_of_pos (show 0 < 1 + 1 / a by positivity) using 1
    field_simp
    <;> ring
  calc
    eulerH s ≤ exp (∑ q ∈ s, 1 / (q : ℝ)) :=
      prod_one_add_le_exp_sum s (fun q => by positivity)
    _ < exp (1 / (a + 1)) := exp_lt_exp.mpr hsum
    _ ≤ exp (log (1 + 1 / a)) := exp_le_exp.mpr hlog
    _ = 1 + 1 / a := exp_log (by positivity)

private lemma eulerH_erase {s : Finset ℕ} {q : ℕ} (hq : q ∈ s) :
    (1 + 1 / (q : ℝ)) * eulerH (s.erase q) = eulerH s := by
  classical
  exact mul_prod_erase s (fun p => 1 + 1 / (p : ℝ)) hq

private lemma primitive_prime_block (S T : Finset ℕ) (a : ℝ) (ha : 0 < a)
    (hS : ∀ p ∈ S, p.Prime ∧ (p : ℝ) < 2 * a)
    (hT : ∀ q ∈ T, q.Prime ∧
      ((T.card : ℝ) - 1) * (a + 1) < q ∧ (q : ℝ) ≤ T.card * a)
    (hk : 3 ≤ T.card) (hthreshold : eulerH S * (1 + 1 / a) = 2) :
    PrimitiveNonDeficient (∏ p ∈ S ∪ T, p) := by
  classical
  have hkR : (3 : ℝ) ≤ T.card := by exact_mod_cast hk
  have hlarge (q : ℕ) (hq : q ∈ T) : 2 * a < q := by
    have hh := (hT q hq).2.1
    nlinarith
  have hdis : Disjoint S T := by
    apply disjoint_left.mpr
    intro p hp hpt
    exact ((hS p hp).2.trans (hlarge p hpt)).false
  have hprod : eulerH (S ∪ T) = eulerH S * eulerH T := by
    exact prod_union hdis
  have hpr : ∀ p ∈ S ∪ T, p.Prime := by
    intro p hp
    exact (mem_union.mp hp).elim (fun h => (hS p h).1) (fun h => (hT p h).1)
  have hdelete (q : ℕ) (hq : q ∈ T) : eulerH ((S ∪ T).erase q) < 2 := by
    have hne : (T.erase q).Nonempty := by
      apply card_pos.mp
      rw [card_erase_of_mem hq]
      omega
    have hu : eulerH (T.erase q) < 1 + 1 / a := by
      apply block_product_upper _ a ha hne
      intro r hr
      rw [card_erase_of_mem hq, Nat.cast_sub (by omega : 1 ≤ T.card), Nat.cast_one]
      exact (hT r (mem_of_mem_erase hr)).2.1
    have heq : eulerH ((S ∪ T).erase q) = eulerH S * eulerH (T.erase q) := by
      apply mul_left_cancel₀ (show (1 + 1 / (q : ℝ)) ≠ 0 by positivity)
      rw [eulerH_erase (mem_union_right S hq), hprod, ← eulerH_erase hq]
      ring
    rw [heq, ← hthreshold]
    exact mul_lt_mul_of_pos_left hu (eulerH_pos S)
  apply primitive_of_erase (S ∪ T) hpr
  · rw [hprod, ← hthreshold]
    apply le_of_lt
    apply mul_lt_mul_of_pos_left _ (eulerH_pos S)
    exact block_product_lower T a ha (by omega)
      (fun q hq => ⟨by exact_mod_cast (hT q hq).1.pos, (hT q hq).2.2⟩)
  · intro p hp
    rcases mem_union.mp hp with hpS | hpT
    · obtain ⟨q, hq⟩ := card_pos.mp (show 0 < T.card by omega)
      have hpq : (p : ℝ) < q := (hS p hpS).2.trans (hlarge q hq)
      have hfac : 1 + 1 / (q : ℝ) < 1 + 1 / (p : ℝ) := by
        linarith [one_div_lt_one_div_of_lt
          (by exact_mod_cast (hS p hpS).1.pos : (0 : ℝ) < p) hpq]
      have hpe := eulerH_erase (mem_union_left T hpS)
      have hqe := eulerH_erase (mem_union_right S hq)
      have hpos := eulerH_pos ((S ∪ T).erase p)
      have hposq : 0 < 1 + 1 / (q : ℝ) := by positivity
      have hle : eulerH ((S ∪ T).erase p) < eulerH ((S ∪ T).erase q) := by
        nlinarith [mul_lt_mul_of_pos_right hfac hpos]
      exact hle.trans (hdelete q hq)
    · exact hdelete p hpT

attribute [local instance] Classical.propDecidable

private lemma selected_family_count (M S W : Finset ℕ) (k X : ℕ) (a : ℝ)
    (hM : ∀ p ∈ M, p.Prime) (ha : 0 < a) (ha1 : 1 < a) (hk : 3 ≤ k)
    (hS : ∀ p ∈ S, p.Prime ∧ max 2 (M.sup id) < p ∧ (p : ℝ) < 2 * a)
    (hW : ∀ q ∈ W, q.Prime ∧
      ((k : ℝ) - 1) * (a + 1) < q ∧ (q : ℝ) ≤ k * a)
    (hthreshold : eulerH S * (1 + 1 / a) = 2)
    (hcost : (∑ p ∈ S, log (p : ℝ)) + k * log ((k : ℝ) * a) ≤ log (X : ℝ))
    (hX : 0 < X) :
    W.card.choose k ≤ ((Icc 1 X).filter fun n =>
      Odd n ∧ Squarefree n ∧ PrimitiveNonDeficient n ∧ ∀ p ∈ M, ¬ p ∣ n).card := by
  classical
  let C := W.powersetCard k
  let f (T : Finset ℕ) := (∏ p ∈ S, p) * (∏ q ∈ T, q)
  have hsP : ∀ p ∈ S, p.Prime := fun p hp => (hS p hp).1
  have hSne : S.Nonempty := by
    by_contra he
    have heq := hthreshold
    rw [not_nonempty_iff_eq_empty.mp he] at heq
    simp only [eulerH, prod_empty, one_mul] at heq
    field_simp at heq
    nlinarith
  have hdata {T : Finset ℕ} (hT : T ∈ C) :
      T.card = k ∧ (∀ p ∈ T, p.Prime) ∧ Disjoint S T := by
    obtain ⟨hsub, hcard⟩ := mem_powersetCard.mp hT
    refine ⟨hcard, fun p hp => (hW p (hsub hp)).1, ?_⟩
    apply disjoint_left.mpr
    intro p hpS hpT
    have hh := (hW p (hsub hpT)).2.1
    have hkR : (3 : ℝ) ≤ k := by exact_mod_cast hk
    have hsmall := (hS p hpS).2.2
    nlinarith
  have hinj : Set.InjOn f (C : Set (Finset ℕ)) := by
    intro T hT U hU he
    have hm : 0 < ∏ p ∈ S, p := Finset.prod_pos (fun p hp => (hsP p hp).pos)
    exact D5.S3.Arith.Robin.Analytic.OmegaTail.Lower.prime_product_injective
      (hdata hT).2.1 (hdata hU).2.1 ((Nat.mul_left_cancel_iff hm).mp he)
  have hsub : C.image f ⊆ (Icc 1 X).filter (fun n =>
      Odd n ∧ Squarefree n ∧ PrimitiveNonDeficient n ∧ ∀ p ∈ M, ¬ p ∣ n) := by
    intro n hn
    obtain ⟨T, hT, rfl⟩ := mem_image.mp hn
    obtain ⟨hcard, htP, hdis⟩ := hdata hT
    have hTW := (mem_powersetCard.mp hT).1
    have hU : ∀ p ∈ S ∪ T, p.Prime := by
      intro p hp
      exact (mem_union.mp hp).elim (fun h => hsP p h) (fun h => htP p h)
    have hf : f T = ∏ p ∈ S ∪ T, p := (prod_union hdis).symm
    have hnpos : 0 < f T := by
      rw [hf]
      exact Finset.prod_pos (fun p hp => (hU p hp).pos)
    have hnR : (0 : ℝ) < f T := by exact_mod_cast hnpos
    have hlog : log (f T : ℝ) = (∑ p ∈ S, log (p : ℝ)) +
        ∑ q ∈ T, log (q : ℝ) := by
      rw [hf, Nat.cast_prod, log_prod (fun p hp => by exact_mod_cast (hU p hp).ne_zero)]
      exact sum_union hdis
    have hbound : f T ≤ X := by
      suffices (f T : ℝ) ≤ X by exact_mod_cast this
      apply (log_le_log_iff hnR (by exact_mod_cast hX)).mp
      rw [hlog]
      apply le_trans _ hcost
      gcongr
      calc
        _ ≤ ∑ _q ∈ T, log ((k : ℝ) * a) := by
          apply sum_le_sum
          intro q hq
          exact log_le_log (by exact_mod_cast (htP q hq).pos)
            (hW q (hTW hq)).2.2
        _ = k * log ((k : ℝ) * a) := by simp [hcard]
    have hrough : ∀ p ∈ S ∪ T, max 2 (M.sup id) < p := by
      intro p hp
      rcases mem_union.mp hp with hp | hp
      · exact (hS p hp).2.1
      · have hh := (hW p (hTW hp)).2.1
        have hkR : (3 : ℝ) ≤ k := by exact_mod_cast hk
        obtain ⟨q, hq⟩ := hSne
        have hqB : ((max 2 (M.sup id) : ℕ) : ℝ) < q := by
          exact_mod_cast (hS q hq).2.1
        have hqA := (hS q hq).2.2
        exact_mod_cast (show ((max 2 (M.sup id) : ℕ) : ℝ) < p by nlinarith)
    refine mem_filter.mpr ⟨mem_Icc.mpr ⟨hnpos, hbound⟩, ?_⟩
    rw [hf]
    refine ⟨Nat.not_even_iff_odd.mp ?_, product_squarefree _ hU,
      primitive_prime_block S T a ha (fun p hp => ⟨hsP p hp, (hS p hp).2.2⟩)
        (fun q hq => by simpa only [hcard] using hW q (hTW hq))
        (by omega) hthreshold, ?_⟩
    · intro heven
      have htwo := prime_mem_of_dvd_product _ hU Nat.prime_two heven.two_dvd
      have hh := hrough 2 htwo
      omega
    · intro p hp hpn
      have hpu := prime_mem_of_dvd_product _ hU (hM p hp) hpn
      have hpb := hrough p hpu
      have hsup : p ≤ M.sup id := le_sup (f := id) hp
      omega
  simpa only [C, card_image_of_injOn hinj, card_powersetCard] using card_le_card hsub

private lemma theta_interval_sum {y z : ℝ} (hyz : y ≤ z) :
    Chebyshev.theta z - Chebyshev.theta y =
      ∑ p ∈ primeInterval y z, Real.log (p : ℝ) := by
  classical
  have he : primeInterval y z = Nat.primesLE ⌊z⌋₊ \ Nat.primesLE ⌊y⌋₊ := by
    ext p
    simp only [primeInterval, Finset.mem_filter, Finset.mem_Ioc,
      Finset.mem_sdiff, Nat.mem_primesLE]
    constructor
    · rintro ⟨⟨hlo, hhi⟩, hp⟩
      exact ⟨⟨hhi, hp⟩, fun h => (Nat.not_le_of_lt hlo) h.1⟩
    · rintro ⟨⟨hhi, hp⟩, hlo⟩
      exact ⟨⟨lt_of_not_ge (fun h => hlo ⟨h, hp⟩), hhi⟩, hp⟩
  have hsub : Nat.primesLE ⌊y⌋₊ ⊆ Nat.primesLE ⌊z⌋₊ := by
    intro p hp
    exact Nat.mem_primesLE.mpr
      ⟨(Nat.mem_primesLE.mp hp).1.trans (Nat.floor_mono hyz),
        (Nat.mem_primesLE.mp hp).2⟩
  rw [he, Chebyshev.theta_eq_sum_primesLE, Chebyshev.theta_eq_sum_primesLE]
  have h := Finset.sum_sdiff hsub (f := fun p : ℕ => Real.log (p : ℝ))
  linarith

private lemma theta_interval_le_card {y z : ℝ} (hyz : y ≤ z) (hz : 0 ≤ z) :
    Chebyshev.theta z - Chebyshev.theta y ≤
      (primeInterval y z).card * Real.log z := by
  rw [theta_interval_sum hyz]
  calc
    _ ≤ ∑ _p ∈ primeInterval y z, Real.log z := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨hpI, hpP⟩ := Finset.mem_filter.mp hp
      have hpz : (p : ℝ) ≤ z :=
        (Nat.le_floor_iff hz).mp (Finset.mem_Ioc.mp hpI).2
      exact Real.log_le_log (by exact_mod_cast hpP.pos) hpz
    _ = _ := by simp

private lemma theta_cubic_threshold : ∃ U : ℝ, 2 ≤ U ∧
    ∀ x : ℝ, U ≤ x → |Chebyshev.theta x - x| ≤ x / Real.log x ^ 3 := by
  have he : ∀ᶠ x : ℝ in atTop,
      |Chebyshev.theta x - x| ≤ x / Real.log x ^ 3 := by
    filter_upwards [(theta_error_log_power 3).def (by norm_num : (0 : ℝ) < 1),
      eventually_gt_atTop (1 : ℝ)] with x hx hx1
    have hx0 : 0 < x := by linarith
    have hlog : 0 < Real.log x := Real.log_pos hx1
    simpa only [Real.norm_eq_abs, one_mul,
      abs_of_pos (div_pos hx0 (pow_pos hlog 3))] using hx
  obtain ⟨U, hU⟩ := eventually_atTop.mp he
  exact ⟨max 2 U, le_max_left _ _, fun x hx => hU x ((le_max_right _ _).trans hx)⟩

-- The proof requires only error bounds at TWO endpoints. It does not need
-- MovingBoxCapacity or uniform local Abel summation.
private lemma prime_block_capacity {U α : ℝ} {k : ℕ}
    (hU : 2 ≤ U)
    (herr : ∀ x : ℝ, U ≤ x → |Chebyshev.theta x - x| ≤ x / Real.log x ^ 3)
    (hα : U ≤ α) (hk : 3 ≤ k) (hgap : 2 * ((k : ℝ) - 1) ≤ α)
    (hcube : 8 * (k : ℝ) ≤ Real.log α ^ 3) :
    α / (4 * Real.log ((k : ℝ) * α)) ≤
      ((primeInterval (((k : ℝ) - 1) * (α + 1)) ((k : ℝ) * α)).card : ℝ) := by
  let y := ((k : ℝ) - 1) * (α + 1)
  let z := (k : ℝ) * α
  have hα2 : 2 ≤ α := hU.trans hα
  have hα0 : 0 < α := by linarith
  have hk3 : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hyα : α ≤ y := by dsimp [y]; nlinarith
  have hwidth : α / 2 ≤ z - y := by dsimp [y, z]; nlinarith
  have hyz : y ≤ z := by linarith
  have hz0 : 0 < z := by dsimp [z]; positivity
  have hlα : 0 < Real.log α := Real.log_pos (by linarith)
  have hpoint (x : ℝ) (hxα : α ≤ x) (hxz : x ≤ z) :
      |Chebyshev.theta x - x| ≤ α / 8 := by
    have hx0 : 0 < x := hα0.trans_le hxα
    have hlx : 0 < Real.log x := Real.log_pos (by linarith)
    have hlog : Real.log α ^ 3 ≤ Real.log x ^ 3 := by
      gcongr
    calc
      _ ≤ x / Real.log x ^ 3 := herr x (hα.trans hxα)
      _ ≤ z / Real.log α ^ 3 :=
        div_le_div₀ hz0.le hxz (by positivity) hlog
      _ ≤ α / 8 := by
        apply (div_le_iff₀ (pow_pos hlα 3)).mpr
        dsimp [z]
        nlinarith [mul_le_mul_of_nonneg_right hcube hα0.le]
  have hey := hpoint y hyα hyz
  have hez := hpoint z (hyα.trans hyz) le_rfl
  have htheta : α / 4 ≤ Chebyshev.theta z - Chebyshev.theta y := by
    obtain ⟨heyL, heyU⟩ := abs_le.mp hey
    obtain ⟨hezL, hezU⟩ := abs_le.mp hez
    linarith
  have hcount := theta_interval_le_card hyz hz0.le
  have hlogz : 0 < Real.log z := Real.log_pos (by nlinarith)
  change α / (4 * Real.log z) ≤ _
  apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 4) hlogz)).mpr
  nlinarith

-- A weaker factor 2 in the binomial bound costs only k log 2 = o(log X).
-- Reuse Mathlib's pow_le_choose; do not reprove a binomial-coefficient estimate.
private lemma choose_half_lower {N k : ℕ} (hk : 0 < k) (hNk : 2 * k ≤ N) :
    ((N : ℝ) / (2 * k)) ^ k ≤ (N.choose k : ℝ) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hb : (N : ℝ) / 2 ≤ ((N + 1 - k : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : k ≤ N + 1)]
    push_cast
    have hNkR : 2 * (k : ℝ) ≤ N := by exact_mod_cast hNk
    linarith
  have hf : (k.factorial : ℝ) ≤ (k : ℝ) ^ k := by
    exact_mod_cast Nat.factorial_le_pow k
  calc
    _ = ((N : ℝ) / 2) ^ k / (k : ℝ) ^ k := by
      rw [← div_pow]
      congr 1
      field_simp
    _ ≤ (((N + 1 - k : ℕ) : ℝ) ^ k) / (k.factorial : ℝ) := by
      apply div_le_div₀ (by positivity) (by gcongr) (by positivity) hf
    _ ≤ (N.choose k : ℝ) := Nat.pow_le_choose k N


private lemma parameter_slack {C D a : ℝ} (ha : 0 < a)
    (hbudget : C + a < D) (hgain : (39 / 40 : ℝ) * D < a) :
    ∀ᶠ t : ℝ in atTop,
      1 ≤ t ∧ 5 ≤ ⌊a * t⌋₊ ∧ (⌊a * t⌋₊ : ℝ) ≤ a * t ∧
      t + log (3 * a) + log t ≤ 2 * t ∧
      C * t ^ 2 + (⌊a * t⌋₊ : ℝ) * (t + log (3 * a) + log t) ≤ D * t ^ 2 ∧
      (39 / 40 : ℝ) * D * t ^ 2 ≤
        (⌊a * t⌋₊ : ℝ) * (t - log (16 * a) - 2 * log t) ∧
      8 * (⌊a * t⌋₊ : ℝ) ≤ t ^ 3 ∧ 16 * a * t ^ 2 ≤ exp t := by
  let b (t : ℝ) := t + log (3 * a) + log t
  let c (t : ℝ) := t - log (16 * a) - 2 * log t
  have ht : Tendsto (fun t : ℝ => t) atTop atTop := tendsto_id
  have hlog : Tendsto (fun t : ℝ => log t / t) atTop (𝓝 0) := by
    simpa only [rpow_one] using
      (isLittleO_log_rpow_rpow_atTop 1 (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero
  have hb : Tendsto (fun t : ℝ => b t / t) atTop (𝓝 1) := by
    have h := ((tendsto_const_nhds (x := (1 : ℝ)) (f := atTop)).add
      (ht.const_div_atTop (log (3 * a)))).add hlog
    norm_num only [add_zero] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht0
    dsimp only [b]
    field_simp
  have hc : Tendsto (fun t : ℝ => c t / t) atTop (𝓝 1) := by
    have h := ((tendsto_const_nhds (x := (1 : ℝ)) (f := atTop)).sub
      (ht.const_div_atTop (log (16 * a)))).sub (hlog.const_mul 2)
    norm_num only [mul_zero, sub_zero] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht0
    dsimp only [c]
    field_simp
  have hk := tendsto_nat_floor_mul_div_atTop ha.le
  have hcost := (hk.mul hb).const_add C
  have hproduce := hk.mul hc
  simp only [mul_one] at hcost hproduce
  have hklarge : Tendsto (fun t : ℝ => ⌊a * t⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp (ht.const_mul_atTop ha)
  have ht2 : Tendsto (fun t : ℝ => t ^ 2) atTop atTop :=
    tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0)
  filter_upwards [eventually_ge_atTop (1 : ℝ), hklarge.eventually_ge_atTop 5,
    hb.eventually_lt_const (by norm_num : (1 : ℝ) < 2),
    hcost.eventually_lt_const hbudget, hproduce.eventually_const_lt hgain,
    ht2.eventually_ge_atTop (8 * a),
    (tendsto_exp_div_pow_atTop 2).eventually_ge_atTop (16 * a)]
    with t ht1 hk5 hb2 hcostD hproduceD ht2a hexp
  have ht0 : 0 < t := by linarith
  have hfloor : (⌊a * t⌋₊ : ℝ) ≤ a * t := Nat.floor_le (by positivity)
  have hcostD' : C * t ^ 2 + (⌊a * t⌋₊ : ℝ) * b t < D * t ^ 2 := by
    have he : C + (⌊a * t⌋₊ : ℝ) / t * (b t / t) =
        (C * t ^ 2 + (⌊a * t⌋₊ : ℝ) * b t) / t ^ 2 := by
      field_simp
      <;> ring
    rw [he] at hcostD
    exact (div_lt_iff₀ (pow_pos ht0 2)).mp hcostD
  have hproduceD' : (39 / 40 : ℝ) * D * t ^ 2 <
      (⌊a * t⌋₊ : ℝ) * c t := by
    have he : (⌊a * t⌋₊ : ℝ) / t * (c t / t) =
        ((⌊a * t⌋₊ : ℝ) * c t) / t ^ 2 := by
      field_simp
      <;> ring
    rw [he] at hproduceD
    exact (lt_div_iff₀ (pow_pos ht0 2)).mp hproduceD
  refine ⟨ht1, hk5, hfloor, (div_lt_iff₀ ht0).mp hb2 |>.le,
    hcostD'.le, hproduceD'.le, ?_, ?_⟩
  · nlinarith [mul_le_mul_of_nonneg_right ht2a ht0.le]
  · exact (le_div_iff₀ (pow_pos ht0 2)).mp hexp

private lemma binomial_log_gain {N k : ℕ} {a t D α z : ℝ}
    (hk : 0 < k) (hNk : 2 * k ≤ N) (ha : 0 < a) (ht : 0 < t)
    (hz : 1 < z) (hN : α / (4 * log z) ≤ N) (hα : exp t ≤ α)
    (hden : 8 * (k : ℝ) * log z ≤ 16 * a * t ^ 2)
    (hgain : (39 / 40 : ℝ) * D * t ^ 2 ≤
      (k : ℝ) * (t - log (16 * a) - 2 * log t)) :
    (39 / 40 : ℝ) * D * t ^ 2 ≤ log (N.choose k : ℝ) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlz : 0 < log z := log_pos hz
  have hN' : α ≤ (N : ℝ) * (4 * log z) :=
    (div_le_iff₀ (by positivity : 0 < 4 * log z)).mp hN
  have hfrac : exp t / (16 * a * t ^ 2) ≤ (N : ℝ) / (2 * k) := by
    apply (div_le_div_iff₀ (by positivity : 0 < 16 * a * t ^ 2)
      (by positivity : (0 : ℝ) < 2 * k)).mpr
    have h1 := mul_le_mul_of_nonneg_right (hα.trans hN')
      (by positivity : (0 : ℝ) ≤ 2 * k)
    have h2 := mul_le_mul_of_nonneg_left hden hN0.le
    nlinarith
  have heq : log (exp t / (16 * a * t ^ 2)) =
      t - log (16 * a) - 2 * log t := by
    rw [log_div (exp_ne_zero _) (by positivity), log_exp,
      log_mul (by positivity) (by positivity), log_pow]
    ring
  have hlog := log_le_log (by positivity : 0 < exp t / (16 * a * t ^ 2)) hfrac
  rw [heq] at hlog
  have hchoose := log_le_log
    (pow_pos (div_pos hN0 (by positivity : (0 : ℝ) < 2 * k)) k)
    (choose_half_lower hk hNk)
  rw [log_pow] at hchoose
  exact hgain.trans ((mul_le_mul_of_nonneg_left hlog hk0.le).trans hchoose)

private lemma lower_bound_parameters (C : ℝ) :
    let D := 1000 * (|C| + 1)
    let a := (99 / 100 : ℝ) * D
    ∀ᶠ t : ℝ in atTop,
      ∀ α : ℝ, exp t ≤ α → α ≤ 3 * exp t →
      let k := ⌊a * t⌋₊
      let z := (k : ℝ) * α
      5 ≤ k ∧ 2 * ((k : ℝ) - 1) ≤ α ∧ 8 * (k : ℝ) ≤ log α ^ 3 ∧
      C * t ^ 2 + (k : ℝ) * log z ≤ D * t ^ 2 ∧
      ∀ N : ℕ, α / (4 * log z) ≤ N →
        2 * k ≤ N ∧ (39 / 40 : ℝ) * D * t ^ 2 ≤ log (N.choose k : ℝ) := by
  dsimp only
  let D := 1000 * (|C| + 1)
  let a := (99 / 100 : ℝ) * D
  have hD : 0 < D := by dsimp [D]; positivity
  have ha : 0 < a := by dsimp [a]; positivity
  have hCa : C + a < D := by
    dsimp [a, D]
    nlinarith [le_abs_self C, abs_nonneg C]
  have hDa : (39 / 40 : ℝ) * D < a := by dsimp [a]; nlinarith
  filter_upwards [parameter_slack ha hCa hDa] with t hslack
  obtain ⟨ht1, hk5, hka, hb, hbudget, hgain, hcube, hexp⟩ := hslack
  have ht0 : 0 < t := by linarith
  intro α hαL hαU
  let k := ⌊a * t⌋₊
  let z := (k : ℝ) * α
  have hkR : (5 : ℝ) ≤ k := by exact_mod_cast hk5
  have hα0 : 0 < α := (exp_pos t).trans_le hαL
  have hα1 : 1 < α := (one_lt_exp_iff.mpr ht0).trans_le hαL
  have hz1 : 1 < z := by dsimp [z]; nlinarith
  have hαt : t ≤ log α := by simpa only [log_exp] using log_le_log (exp_pos t) hαL
  have hzU : z ≤ 3 * a * t * exp t := by
    dsimp [z]
    calc
      _ ≤ (a * t) * (3 * exp t) := mul_le_mul hka hαU hα0.le (by positivity)
      _ = _ := by ring
  have hlogz : log z ≤ t + log (3 * a) + log t := by
    have h := log_le_log (by linarith : 0 < z) hzU
    rw [log_mul (by positivity) (exp_ne_zero _), log_exp,
      log_mul (by positivity) ht0.ne'] at h
    linarith
  have hden : 8 * (k : ℝ) * log z ≤ 16 * a * t ^ 2 := by
    have hlogz2 := hlogz.trans hb
    have h1 := mul_le_mul_of_nonneg_left hlogz2 (by positivity : (0 : ℝ) ≤ 8 * k)
    have h2 := mul_le_mul_of_nonneg_right hka (by positivity : (0 : ℝ) ≤ 16 * t)
    nlinarith
  have hgap : 2 * ((k : ℝ) - 1) ≤ α := by
    have h1 : 2 * (k : ℝ) ≤ 16 * a * t ^ 2 := by
      nlinarith [mul_nonneg ha.le (sq_nonneg (t - 1))]
    linarith
  refine ⟨hk5, hgap, ?_, ?_, ?_⟩
  · exact hcube.trans (by gcongr)
  · have h := mul_le_mul_of_nonneg_left hlogz (by positivity : (0 : ℝ) ≤ k)
    linarith
  · intro N hN
    have hlogz0 : 0 < log z := log_pos hz1
    have hN' := (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 4) hlogz0)).mp hN
    have hNk : 2 * k ≤ N := by
      have h1 : 8 * (k : ℝ) * log z ≤ α := hden.trans (hexp.trans hαL)
      have h2 : 2 * (k : ℝ) ≤ N := by nlinarith [log_pos hz1]
      exact_mod_cast h2
    have hk0 : 0 < k := by dsimp only [k]; omega
    exact ⟨hNk, binomial_log_gain hk0 hNk ha ht0 hz1 hN hαL hden hgain⟩

private lemma cutoff_parameter_atTop {D : ℝ} (hD : 0 < D) :
    Tendsto (fun X : ℝ => sqrt (log X / D)) atTop atTop ∧
      ∀ᶠ X : ℝ in atTop, D * sqrt (log X / D) ^ 2 = log X := by
  refine ⟨tendsto_sqrt_atTop.comp (tendsto_log_atTop.atTop_div_const hD), ?_⟩
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
  rw [sq_sqrt (div_nonneg (log_pos hX).le hD.le)]
  field_simp


/-- Almost linearly many odd squarefree primitive non-deficient integers avoid any
finite set of prime divisors. The counting interval includes both endpoints. -/
theorem result (M : Finset ℕ) (hM : ∀ p ∈ M, p.Prime) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      (X : ℝ) ^ (39 / 40 : ℝ) ≤
        (((Icc 1 X).filter fun n => Odd n ∧ Squarefree n ∧
          PrimitiveNonDeficient n ∧ ∀ p ∈ M, ¬ p ∣ n).card : ℝ) := by
  classical
  obtain ⟨C, hC, T₀, hcore⟩ := ZelinskyDeficientCore.result (max 2 (M.sup id))
  obtain ⟨U, hU, herr⟩ := theta_cubic_threshold
  let D : ℝ := 1000 * (|C| + 1)
  let b : ℝ := (99 / 100 : ℝ) * D
  have hD : 0 < D := by dsimp [D]; positivity
  obtain ⟨V, hV⟩ := eventually_atTop.mp (lower_bound_parameters C)
  let t (X : ℕ) : ℝ := sqrt (log (X : ℝ) / D)
  have hcut := cutoff_parameter_atTop hD
  have ht : Tendsto t atTop atTop := hcut.1.comp tendsto_natCast_atTop_atTop
  have he := tendsto_exp_atTop.comp ht
  have hsq : ∀ᶠ X : ℕ in atTop, D * t X ^ 2 = log (X : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually hcut.2
  have hev : ∀ᶠ X : ℕ in atTop,
      (X : ℝ) ^ (39 / 40 : ℝ) ≤
        (((Icc 1 X).filter fun n => Odd n ∧ Squarefree n ∧
          PrimitiveNonDeficient n ∧ ∀ p ∈ M, ¬ p ∣ n).card : ℝ) := by
    filter_upwards [ht.eventually_ge_atTop T₀, ht.eventually_ge_atTop V,
      ht.eventually_gt_atTop 0, he.eventually_ge_atTop U, hsq,
      eventually_gt_atTop (0 : ℕ)] with X hT hVt ht0 heU hsqX hX
    obtain ⟨S, hS, hdef, hαL, hαU, hP, hlog⟩ := hcore (t X) hT
    let α := eulerH S / (2 - eulerH S)
    change exp (t X) ≤ α at hαL
    change α ≤ 3 * exp (t X) at hαU
    change ∀ p ∈ S, (p : ℝ) < 2 * α at hP
    have hα0 : 0 < α := (exp_pos _).trans_le hαL
    have hα1 : 1 < α := (one_lt_exp_iff.mpr ht0).trans_le hαL
    have hαU' : U ≤ α := heU.trans hαL
    let k := ⌊b * t X⌋₊
    let z := (k : ℝ) * α
    obtain ⟨hk5, hgap, hcube, hbudget, hgain⟩ := hV (t X) hVt α hαL hαU
    change 5 ≤ k at hk5
    change 2 * ((k : ℝ) - 1) ≤ α at hgap
    change 8 * (k : ℝ) ≤ log α ^ 3 at hcube
    change C * t X ^ 2 + k * log z ≤ D * t X ^ 2 at hbudget
    change ∀ N : ℕ, α / (4 * log z) ≤ N →
      2 * k ≤ N ∧ (39 / 40 : ℝ) * D * t X ^ 2 ≤ log (N.choose k : ℝ) at hgain
    let W := primeInterval (((k : ℝ) - 1) * (α + 1)) z
    have hcap : α / (4 * log z) ≤ (W.card : ℝ) :=
      prime_block_capacity hU herr hαU' (by omega) hgap hcube
    obtain ⟨hNk, hchoose⟩ := hgain W.card hcap
    have hW : ∀ q ∈ W, q.Prime ∧
        ((k : ℝ) - 1) * (α + 1) < q ∧ (q : ℝ) ≤ k * α := by
      intro q hq
      obtain ⟨hqI, hqP⟩ := mem_filter.mp hq
      have hkR : (5 : ℝ) ≤ k := by exact_mod_cast hk5
      have hy0 : 0 ≤ ((k : ℝ) - 1) * (α + 1) :=
        mul_nonneg (by linarith) (by linarith)
      exact ⟨hqP, (Nat.floor_lt hy0).mp (mem_Ioc.mp hqI).1,
        (Nat.le_floor_iff (by positivity)).mp (mem_Ioc.mp hqI).2⟩
    have hthreshold : eulerH S * (1 + 1 / α) = 2 := by
      have hspos := eulerH_pos S
      change eulerH S < 2 at hdef
      have hde : 2 - eulerH S ≠ 0 := by linarith
      dsimp [α]
      field_simp [hde, hspos.ne']
      <;> ring
    have hcost : (∑ p ∈ S, log (p : ℝ)) + k * log ((k : ℝ) * α) ≤
        log (X : ℝ) := by
      rw [← hsqX]
      change _ + k * log z ≤ _
      linarith
    have hcount := selected_family_count M S W k X α hM hα0 hα1 (by omega)
      (fun p hp => ⟨(hS p hp).1, (hS p hp).2, hP p hp⟩)
      hW hthreshold hcost hX
    have hchoosepos : (0 : ℝ) < W.card.choose k := by
      exact_mod_cast Nat.choose_pos (by omega : k ≤ W.card)
    apply le_trans _ (show (W.card.choose k : ℝ) ≤ _ by exact_mod_cast hcount)
    rw [rpow_def_of_pos (show (0 : ℝ) < X by exact_mod_cast hX)]
    apply (le_log_iff_exp_le hchoosepos).mp
    rw [← hsqX]
    nlinarith [hchoose]
  exact eventually_atTop.mp hev

end D5.S3.Arith.Abundancy.ZelinskyPrimitiveAbundantLowerBound
