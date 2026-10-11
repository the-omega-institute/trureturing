/- GID: D5/S3/Arith/Robin/FewDistinctPrimes
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/FewDistinctPrimes
   mirror-E: none(waiver:universal-inequality)
   anchors: []
   utility: none
   digest: Above 5040, every integer with at most eight distinct primes satisfies Robin's bound. -/

import D5.S3.Arith.Robin.ElevenSmooth
import D5.S3.Arith.ExponentExchange.PrefixNormalForm
import D5.S3.Arith.GoldenResourceOptimalInteger

/-! An integer `n` and the exponent normal form `m ≤ n` with as many distinct primes satisfy
`σ(n)/n ≤ σ(m)/m`, so Robin's inequality at `m > 5040` passes to `n`. With at most eight
distinct primes, a normal form is a product of powers of `2, 3, …, 19` with non-increasing
exponents. Below `10^12` a kernel-checked enumeration of these products bounds `σ(m)/m` on
twelve intervals; above it the saturation bound `∏ p/(p-1) = 323323/55296` suffices. A normal
form at most 5040 has `σ(m)/m ≤ 403/105` by the frozen 5040 optimum, which `e^γ log log n`
exceeds for `n ≥ 6000`. On `(5040, 6000)` an integer is 11-smooth or has a prime factor
`p ≥ 13` whose cofactor is below 462. -/

namespace D5.S3.Arith.Robin.FewDistinctPrimes

open D5.S3.Arith.GoldenResource.RobinRationalBasis
open D5.S3.Arith.Robin.ElevenSmooth
open D5.S3.Arith.ExponentExchange.IntegerSwap
open D5.S3.Arith.ExponentExchange.PrefixNormalForm
open D5.S3.Arith.GoldenResourceOptimalInteger

/-- `1 + p + ⋯ + p^k` in closed form. -/
def geom (p k : ℕ) : ℕ := (p ^ (k + 1) - 1) / (p - 1)

/-- The product `∏ pᵢ ^ eᵢ` along two aligned lists. -/
def powProd : List ℕ → List ℕ → ℕ
  | p :: ps, e :: es => p ^ e * powProd ps es
  | _, _ => 1

/-- The product of the geometric sums `1 + pᵢ + ⋯ + pᵢ ^ eᵢ` along two aligned lists. -/
def geomProd : List ℕ → List ℕ → ℕ
  | p :: ps, e :: es => geom p e * geomProd ps es
  | _, _ => 1

private theorem geom_spec {p : ℕ} (hp : 2 ≤ p) (k : ℕ) : geom p k * (p - 1) + 1 = p ^ (k + 1) := by
  have hdvd : p - 1 ∣ p ^ (k + 1) - 1 := by
    simpa only [one_pow] using Nat.sub_dvd_pow_sub_pow p 1 (k + 1)
  have h1 : 1 ≤ p ^ (k + 1) := Nat.one_le_pow _ _ (by omega)
  unfold geom
  rw [Nat.div_mul_cancel hdvd]
  omega

private theorem sigma_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    ArithmeticFunction.sigma 1 (p ^ k) = geom p k := by
  rw [ArithmeticFunction.sigma_one_apply_prime_pow hp, Nat.geomSum_eq hp.two_le]
  rfl

private theorem powProd_map (f : ℕ → ℕ) :
    ∀ ps : List ℕ, powProd ps (ps.map f) = (ps.map fun p => p ^ f p).prod
  | [] => rfl
  | p :: ps => by simp only [List.map_cons, powProd, List.prod_cons, powProd_map f ps]

private theorem geomProd_map (f : ℕ → ℕ) :
    ∀ ps : List ℕ, geomProd ps (ps.map f) = (ps.map fun p => geom p (f p)).prod
  | [] => rfl
  | p :: ps => by simp only [List.map_cons, geomProd, List.prod_cons, geomProd_map f ps]

private theorem powProd_pos : ∀ (ps es : List ℕ), (∀ p ∈ ps, 0 < p) → 0 < powProd ps es
  | [], _, _ => by simp [powProd]
  | _ :: _, [], _ => by simp [powProd]
  | p :: ps, e :: es, h => by
    simp only [powProd]
    exact Nat.mul_pos (pow_pos (h p (by simp)) _)
      (powProd_pos ps es fun q hq => h q (List.mem_cons_of_mem _ hq))

/-- An integer whose primes lie in the list `ps` is the product of its prime powers along `ps`,
and its divisor sum is the product of the matching geometric sums. -/
theorem factor_repr {ps : List ℕ} (hps : ∀ p ∈ ps, p.Prime) (hnd : ps.Nodup)
    {n : ℕ} (hn : n ≠ 0) (hsub : n.primeFactors ⊆ ps.toFinset) :
    powProd ps (ps.map n.factorization) = n ∧
      geomProd ps (ps.map n.factorization) = ArithmeticFunction.sigma 1 n := by
  have hzero : ∀ x ∈ ps.toFinset, x ∉ n.primeFactors → n.factorization x = 0 := by
    intro x _ hx
    simpa [← Nat.support_factorization] using hx
  constructor
  · rw [powProd_map, ← List.prod_toFinset _ hnd]
    conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hn,
      Nat.prod_factorization_eq_prod_primeFactors]
    refine (Finset.prod_subset hsub fun x hx hxn => ?_).symm
    rw [hzero x hx hxn, pow_zero]
  · rw [geomProd_map, ← List.prod_toFinset _ hnd,
      ArithmeticFunction.IsMultiplicative.multiplicative_factorization _
        ArithmeticFunction.isMultiplicative_sigma hn,
      Nat.prod_factorization_eq_prod_primeFactors]
    rw [Finset.prod_congr rfl fun p hp =>
      (sigma_prime_pow (hps p (List.mem_toFinset.mp hp)) (n.factorization p)).symm]
    refine (Finset.prod_subset hsub fun x hx hxn => ?_).symm
    rw [hzero x hx hxn, pow_zero]
    exact ArithmeticFunction.isMultiplicative_sigma.map_one

/-- The saturation bound `σ(m)/m ≤ ∏ p/(p-1)` in integer form. -/
theorem geomProd_le : ∀ (ps es : List ℕ), (∀ p ∈ ps, 2 ≤ p) → es.length = ps.length →
    geomProd ps es * (ps.map (· - 1)).prod ≤ powProd ps es * ps.prod
  | [], [], _, _ => by simp [geomProd, powProd]
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | p :: ps, e :: es, hps, hlen => by
    have hp := hps p (by simp)
    have ih := geomProd_le ps es (fun q hq => hps q (List.mem_cons_of_mem _ hq))
      (by simpa using hlen)
    have hloc : geom p e * (p - 1) ≤ p ^ e * p := by
      have := geom_spec hp e
      rw [pow_succ] at this
      omega
    simp only [geomProd, powProd, List.map_cons, List.prod_cons]
    calc geom p e * geomProd ps es * ((p - 1) * (ps.map (· - 1)).prod)
        = (geom p e * (p - 1)) * (geomProd ps es * (ps.map (· - 1)).prod) := by ring
      _ ≤ (p ^ e * p) * (powProd ps es * ps.prod) := Nat.mul_le_mul hloc ih
      _ = p ^ e * powProd ps es * (p * ps.prod) := by ring

/-- The ratio bound `K/100` used on each interval of the table, indexed by its left end. -/
private def segK (m : ℕ) : ℕ :=
  if m < 10080 then 381 else if m < 25200 then 395 else if m < 55440 then 411
  else if m < 110880 then 425 else if m < 332640 then 436 else if m < 1441440 then 452
  else if m < 7207200 then 471 else if m < 61261200 then 490 else if m < 367567200 then 513
  else if m < 3491888400 then 530 else if m < 41902660800 then 549 else 568

private def leafOK (m s : ℕ) : Bool := decide (m ≤ 5040) || decide (100 * s ≤ segK m * m)

/-- Enumerates every product `m · ∏ pᵢ^kᵢ < 10^12` along `ps` with `e ≥ k₁ ≥ k₂ ≥ ⋯`,
carrying the divisor sum, and checks each leaf. -/
private def check : List ℕ → ℕ → ℕ → ℕ → Bool
  | [], _, m, s => leafOK m s
  | p :: ps, e, m, s => (List.range (e + 1)).all fun k =>
      decide (1000000000000 ≤ m * p ^ k) || check ps k (m * p ^ k) (s * geom p k)

private theorem check_sound : ∀ (ps : List ℕ) (e m s : ℕ), (∀ p ∈ ps, 0 < p) →
    check ps e m s = true → ∀ es : List ℕ, es.length = ps.length →
      es.Pairwise (fun a b => b ≤ a) → (∀ k ∈ es.head?, k ≤ e) →
        m * powProd ps es < 1000000000000 →
          leafOK (m * powProd ps es) (s * geomProd ps es) = true
  | [], _, m, s, _, h, [], _, _, _, _ => by simpa [check, powProd, geomProd] using h
  | [], _, _, _, _, _, _ :: _, hlen, _, _, _ => by simp at hlen
  | _ :: _, _, _, _, _, _, [], hlen, _, _, _ => by simp at hlen
  | p :: ps, e, m, s, hpos, h, k :: es, hlen, hpw, hhead, hlt => by
    have hk : k ≤ e := hhead k rfl
    have hpp : 0 < powProd ps es :=
      powProd_pos ps es fun q hq => hpos q (List.mem_cons_of_mem _ hq)
    have hlt' : m * p ^ k * powProd ps es < 1000000000000 := by
      simpa only [powProd, mul_assoc] using hlt
    simp only [check, List.all_eq_true, List.mem_range, Bool.or_eq_true,
      decide_eq_true_eq] at h
    rcases h k (by omega) with h1 | h1
    · have : m * p ^ k ≤ m * p ^ k * powProd ps es := Nat.le_mul_of_pos_right _ hpp
      omega
    · have hpw' := List.pairwise_cons.mp hpw
      have := check_sound ps k (m * p ^ k) (s * geom p k)
        (fun q hq => hpos q (List.mem_cons_of_mem _ hq)) h1 es (by simpa using hlen) hpw'.2
        (fun j hj => hpw'.1 j (List.mem_of_mem_head? hj)) hlt'
      simpa only [powProd, geomProd, mul_assoc] using this

private def eightPrimes : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19]

private theorem prime_of_mem_eight {p : ℕ} (hp : p ∈ eightPrimes) : p.Prime := by
  simp only [eightPrimes, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

set_option maxRecDepth 100000 in
private theorem check_eight : check eightPrimes 40 1 1 = true := by decide +kernel

/-- A normal form with at most eight distinct primes uses only the primes up to 19. -/
private theorem subset_eight {m : ℕ} (hm : m ≠ 0)
    (hanti : ∀ p q : ℕ, p.Prime → q.Prime → p < q → m.factorization q ≤ m.factorization p)
    (hcard : m.primeFactors.card ≤ 8) : m.primeFactors ⊆ eightPrimes.toFinset := by
  intro q hq
  by_contra hqn
  have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
  have hq19 : 19 < q := by
    by_contra hle
    rw [not_lt] at hle
    interval_cases q <;> first | exact hqn (by decide) | norm_num at hqp
  have hvq : 1 ≤ m.factorization q :=
    (hqp.dvd_iff_one_le_factorization hm).mp (Nat.dvd_of_mem_primeFactors hq)
  have hsub : insert q eightPrimes.toFinset ⊆ m.primeFactors := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact hq
    · have hp' : p ∈ eightPrimes := List.mem_toFinset.mp hp
      have hpp := prime_of_mem_eight hp'
      have hpq : p < q := by
        simp only [eightPrimes, List.mem_cons, List.not_mem_nil, or_false] at hp'
        omega
      have := hanti p q hpp hqp hpq
      exact Nat.mem_primeFactors.mpr
        ⟨hpp, (hpp.dvd_iff_one_le_factorization hm).mpr (by omega), hm⟩
  have hle := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hqn] at hle
  have h8 : eightPrimes.toFinset.card = 8 := by decide
  omega

private theorem loglog_6000 : (54 / 25 : Real) <
    Real.log (Real.log 6000) :=
  loglog_of 6000 (4349 / 500) _ (375 / 256)
    (4349 / 4000) 12 3 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num [atanhPartial, Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [atanhPartial, Finset.sum_range_succ]) (by norm_num)

private theorem loglog_10080 : (111 / 50 : Real) <
    Real.log (Real.log 10080) :=
  loglog_of 10080 (9217 / 1000) _ (315 / 256)
    (9217 / 8000) 13 3 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num [atanhPartial, Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [atanhPartial, Finset.sum_range_succ]) (by norm_num)

private theorem loglog_25200 : (1157 / 500 : Real) <
    Real.log (Real.log 25200) :=
  loglog_of 25200 (10133 / 1000) _ (1575 / 1024)
    (10133 / 8000) 14 3 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num [atanhPartial, Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [atanhPartial, Finset.sum_range_succ]) (by norm_num)

private theorem loglog_55440 : (2389 / 1000 : Real) <
    Real.log (Real.log 55440) :=
  loglog_of 55440 (5461 / 500) _ (3465 / 2048)
    (5461 / 4000) 15 3 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num [atanhPartial, Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [atanhPartial, Finset.sum_range_succ]) (by norm_num)

private theorem loglog_110880 : (2451 / 1000 : Real) <
    Real.log (Real.log 110880) :=
  loglog_of 110880 (2323 / 200) _ (3465 / 2048)
    (2323 / 1600) 16 3 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num [atanhPartial, Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [atanhPartial, Finset.sum_range_succ]) (by norm_num)

private theorem loglog_332640 : (2541 / 1000 : Real) <
    Real.log (Real.log 332640) :=
  loglog_of 332640 (12713 / 1000) _ (10395 / 8192)
    (12713 / 8000) 18 3 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num [atanhPartial, Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [atanhPartial, Finset.sum_range_succ]) (by norm_num)

private theorem loglog_1441440 : (53 / 20 : Real) <
    Real.log (Real.log 1441440) :=
  loglog_of 1441440 (709 / 50) _ (45045 / 32768)
    (709 / 400) 20 3 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num [atanhPartial, Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [atanhPartial, Finset.sum_range_succ]) (by norm_num)

private theorem loglog_7207200 : (1379 / 500 : Real) <
    Real.log (Real.log 7207200) :=
  loglog_of 7207200 (15789 / 1000) _ (225225 / 131072)
    (15789 / 8000) 22 3 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num [atanhPartial, Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [atanhPartial, Finset.sum_range_succ]) (by norm_num)

private theorem loglog_61261200 : (577 / 200 : Real) <
    Real.log (Real.log 61261200) :=
  loglog_of 61261200 (17929 / 1000) _ (3828825 / 2097152)
    (17929 / 16000) 25 4 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num [atanhPartial, Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [atanhPartial, Finset.sum_range_succ]) (by norm_num)

private theorem loglog_367567200 : (149 / 50 : Real) <
    Real.log (Real.log 367567200) :=
  loglog_of 367567200 (19721 / 1000) _ (11486475 / 8388608)
    (19721 / 16000) 28 4 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num [atanhPartial, Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [atanhPartial, Finset.sum_range_succ]) (by norm_num)

private theorem loglog_3491888400 : (386 / 125 : Real) <
    Real.log (Real.log 3491888400) :=
  loglog_of 3491888400 (5493 / 250) _ (218243025 / 134217728)
    (5493 / 4000) 31 4 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num [atanhPartial, Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [atanhPartial, Finset.sum_range_succ]) (by norm_num)

private theorem loglog_41902660800 : (639 / 200 : Real) <
    Real.log (Real.log 41902660800) :=
  loglog_of 41902660800 (24457 / 1000) _ (654729075 / 536870912)
    (24457 / 16000) 35 4 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num [atanhPartial, Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [atanhPartial, Finset.sum_range_succ]) (by norm_num)

private theorem loglog_1000000000000 : (3317 / 1000 : Real) <
    Real.log (Real.log 1000000000000) :=
  loglog_of 1000000000000 (2763 / 100) _ (244140625 / 134217728)
    (2763 / 1600) 39 4 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num [atanhPartial, Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [atanhPartial, Finset.sum_range_succ]) (by norm_num)

/-- Robin's inequality for every normal form above 5040 with at most eight distinct primes. -/
private theorem robin_normal_form {m : ℕ} (hm : 5040 < m)
    (hanti : ∀ p q : ℕ, p.Prime → q.Prime → p < q → m.factorization q ≤ m.factorization p)
    (hcard : m.primeFactors.card ≤ 8) :
    (ArithmeticFunction.sigma 1 m : ℝ) / m <
      Real.exp Real.eulerMascheroniConstant * Real.log (Real.log (m : ℝ)) := by
  have hm0 : m ≠ 0 := by omega
  obtain ⟨hpow, hgeom⟩ := factor_repr (fun p hp => prime_of_mem_eight hp) (by decide) hm0
    (subset_eight hm0 hanti hcard)
  by_cases hX : m < 1000000000000
  · have hpw : (eightPrimes.map m.factorization).Pairwise (fun a b => b ≤ a) := by
      rw [List.pairwise_map]
      refine List.Pairwise.imp_of_mem (R := (· < ·)) ?_ (by decide)
      intro a b ha hb hab
      exact hanti a b (prime_of_mem_eight ha) (prime_of_mem_eight hb) hab
    have hhead : ∀ k ∈ (eightPrimes.map m.factorization).head?, k ≤ 40 := by
      intro k hk
      simp only [eightPrimes, List.map_cons, List.head?_cons, Option.mem_def,
        Option.some.injEq] at hk
      subst hk
      by_contra h40
      have h2 : 2 ^ m.factorization 2 ≤ m := Nat.le_of_dvd (by omega) (Nat.ordProj_dvd m 2)
      have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (show 40 ≤ m.factorization 2 by omega)
      omega
    have hleaf := check_sound eightPrimes 40 1 1 (fun p hp => (prime_of_mem_eight hp).pos)
      check_eight _ (by simp) hpw hhead (by rw [one_mul, hpow]; exact hX)
    rw [one_mul, one_mul, hpow, hgeom] at hleaf
    simp only [leafOK, Bool.or_eq_true, decide_eq_true_eq] at hleaf
    rcases hleaf with h | hv
    · omega
    rw [segK] at hv
    by_cases h0 : m < 10080
    · rw [if_pos h0] at hv
      exact finish (t := 5040) (l := 1071 / 500) (by norm_num) hm.le (by norm_num)
          (by exact_mod_cast loglog_5040) (by norm_num) hv
    rw [if_neg h0] at hv
    by_cases h1 : m < 25200
    · rw [if_pos h1] at hv
      exact finish (t := 10080) (l := 111 / 50) (by norm_num) (by omega) (by norm_num)
          (by exact_mod_cast loglog_10080) (by norm_num) hv
    rw [if_neg h1] at hv
    by_cases h2 : m < 55440
    · rw [if_pos h2] at hv
      exact finish (t := 25200) (l := 1157 / 500) (by norm_num) (by omega) (by norm_num)
          (by exact_mod_cast loglog_25200) (by norm_num) hv
    rw [if_neg h2] at hv
    by_cases h3 : m < 110880
    · rw [if_pos h3] at hv
      exact finish (t := 55440) (l := 2389 / 1000) (by norm_num) (by omega) (by norm_num)
          (by exact_mod_cast loglog_55440) (by norm_num) hv
    rw [if_neg h3] at hv
    by_cases h4 : m < 332640
    · rw [if_pos h4] at hv
      exact finish (t := 110880) (l := 2451 / 1000) (by norm_num) (by omega) (by norm_num)
          (by exact_mod_cast loglog_110880) (by norm_num) hv
    rw [if_neg h4] at hv
    by_cases h5 : m < 1441440
    · rw [if_pos h5] at hv
      exact finish (t := 332640) (l := 2541 / 1000) (by norm_num) (by omega) (by norm_num)
          (by exact_mod_cast loglog_332640) (by norm_num) hv
    rw [if_neg h5] at hv
    by_cases h6 : m < 7207200
    · rw [if_pos h6] at hv
      exact finish (t := 1441440) (l := 53 / 20) (by norm_num) (by omega) (by norm_num)
          (by exact_mod_cast loglog_1441440) (by norm_num) hv
    rw [if_neg h6] at hv
    by_cases h7 : m < 61261200
    · rw [if_pos h7] at hv
      exact finish (t := 7207200) (l := 1379 / 500) (by norm_num) (by omega) (by norm_num)
          (by exact_mod_cast loglog_7207200) (by norm_num) hv
    rw [if_neg h7] at hv
    by_cases h8 : m < 367567200
    · rw [if_pos h8] at hv
      exact finish (t := 61261200) (l := 577 / 200) (by norm_num) (by omega) (by norm_num)
          (by exact_mod_cast loglog_61261200) (by norm_num) hv
    rw [if_neg h8] at hv
    by_cases h9 : m < 3491888400
    · rw [if_pos h9] at hv
      exact finish (t := 367567200) (l := 149 / 50) (by norm_num) (by omega) (by norm_num)
          (by exact_mod_cast loglog_367567200) (by norm_num) hv
    rw [if_neg h9] at hv
    by_cases h10 : m < 41902660800
    · rw [if_pos h10] at hv
      exact finish (t := 3491888400) (l := 386 / 125) (by norm_num) (by omega) (by norm_num)
          (by exact_mod_cast loglog_3491888400) (by norm_num) hv
    rw [if_neg h10] at hv
    exact finish (t := 41902660800) (l := 639 / 200) (by norm_num) (by omega) (by norm_num)
        (by exact_mod_cast loglog_41902660800) (by norm_num) hv
  · have hb := geomProd_le eightPrimes (eightPrimes.map m.factorization)
      (fun p hp => (prime_of_mem_eight hp).two_le) (by simp)
    rw [hpow, hgeom] at hb
    have hc1 : (eightPrimes.map (· - 1)).prod = 1658880 := by decide
    have hc2 : eightPrimes.prod = 9699690 := by decide
    rw [hc1, hc2] at hb
    have hv : 100 * ArithmeticFunction.sigma 1 m ≤ 585 * m := by omega
    exact finish (t := 1000000000000) (l := 3317 / 1000) (by norm_num) (by omega) (by norm_num)
      (by exact_mod_cast loglog_1000000000000) (by norm_num) hv

/-- `σ(m)/m ≤ σ(5040)/5040 = 403/105` for `m ≤ 5040`, from the frozen optimum at price `1/25`. -/
private theorem ratio_le_5040 {m : ℕ} (hm : 1 ≤ m) (hm' : m ≤ 5040) :
    (ArithmeticFunction.sigma 1 m : ℝ) / m ≤ 403 / 105 := by
  have hopt := (golden_resource_unique_optimum hm).1
  unfold goldenResourceObjective at hopt
  rw [reciprocal_divisor_sum hm, reciprocal_divisor_sum (by norm_num : 1 ≤ (5040 : ℕ))] at hopt
  have h5040 : ArithmeticFunction.sigma 1 5040 = 19344 := by decide +kernel
  rw [h5040] at hopt
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hpos : 0 < (ArithmeticFunction.sigma 1 m : ℝ) / m :=
    div_pos (by exact_mod_cast ArithmeticFunction.sigma_pos 1 m (by omega)) hmR
  have hlogm : Real.log m ≤ Real.log 5040 := Real.log_le_log hmR (by exact_mod_cast hm')
  have hval : ((19344 : ℕ) : ℝ) / ((5040 : ℕ) : ℝ) = 403 / 105 := by norm_num
  rw [hval] at hopt
  push_cast at hopt
  have hle : Real.log ((ArithmeticFunction.sigma 1 m : ℝ) / m) ≤ Real.log (403 / 105) := by
    linarith
  exact (Real.log_le_log_iff hpos (by norm_num)).mp hle

private theorem loglog_mono {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    Real.log (Real.log a) ≤ Real.log (Real.log b) :=
  Real.log_le_log (Real.log_pos ha) (Real.log_le_log (by linarith) hab)

private theorem small_table : ∀ r < 462, 4 * ArithmeticFunction.sigma 1 r ≤ 13 * r := by
  decide +kernel

/-- On `(5040, 6000)`: 11-smooth integers are frozen, and otherwise a prime `p ≥ 13` splits off
with `σ(pᵃ)/pᵃ ≤ 13/12` and a cofactor below 462 with ratio at most `13/4`. -/
private theorem robin_small {n : ℕ} (hn : 5040 < n) (h6000 : n < 6000) :
    (ArithmeticFunction.sigma 1 n : ℝ) / n <
      Real.exp Real.eulerMascheroniConstant * Real.log (Real.log (n : ℝ)) := by
  have hn0 : n ≠ 0 := by omega
  by_cases hsub : n.primeFactors ⊆ ([2, 3, 5, 7, 11] : List ℕ).toFinset
  · obtain ⟨hpow, -⟩ := factor_repr (ps := [2, 3, 5, 7, 11])
      (fun p hp => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl <;> norm_num) (by decide) hn0 hsub
    have heq : 2 ^ n.factorization 2 * 3 ^ n.factorization 3 * 5 ^ n.factorization 5 *
        7 ^ n.factorization 7 * 11 ^ n.factorization 11 = n := by
      simpa only [powProd, List.map_cons, List.map_nil, mul_one, mul_assoc] using hpow
    have h := robin_eleven_smooth (n.factorization 2) (n.factorization 3) (n.factorization 5)
      (n.factorization 7) (n.factorization 11) (by rw [heq]; exact hn)
    rwa [heq] at h
  obtain ⟨p, hp, hpn⟩ := Finset.not_subset.mp hsub
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hp13 : 13 ≤ p := by
    by_contra hlt
    rw [not_le] at hlt
    interval_cases p <;> first | exact hpn (by decide) | norm_num at hpp
  have ha : 1 ≤ n.factorization p :=
    (hpp.dvd_iff_one_le_factorization hn0).mp (Nat.dvd_of_mem_primeFactors hp)
  have hdecomp : p ^ n.factorization p * (n / p ^ n.factorization p) = n :=
    Nat.ordProj_mul_ordCompl_eq_self n p
  have hcop : (p ^ n.factorization p).Coprime (n / p ^ n.factorization p) :=
    (Nat.coprime_ordCompl hpp hn0).pow_left _
  have hpa : 13 ≤ p ^ n.factorization p := le_trans hp13 (Nat.le_self_pow (by omega) p)
  set a := n.factorization p
  set r := n / p ^ a
  have hr0 : r ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hdecomp
    omega
  have hr462 : r < 462 := by
    have := Nat.mul_le_mul_right r hpa
    omega
  have hZ := normalized_sigma_mul hcop
  rw [hdecomp] at hZ
  have hZp : (ArithmeticFunction.sigma 1 (p ^ a) : ℝ) / (p ^ a : ℕ) ≤ 13 / 12 := by
    rw [sigma_prime_pow hpp a]
    have hs := geom_spec hpp.two_le a
    have hpR : (13 : ℝ) ≤ p := by exact_mod_cast hp13
    have hsR : (geom p a : ℝ) * ((p : ℝ) - 1) + 1 = (p : ℝ) ^ a * p := by
      have h1 : ((geom p a * (p - 1) + 1 : ℕ) : ℝ) = ((p ^ (a + 1) : ℕ) : ℝ) := by rw [hs]
      push_cast [Nat.cast_sub (show 1 ≤ p by omega), pow_succ] at h1
      linarith
    have hQ : (0 : ℝ) < (p : ℝ) ^ a := by positivity
    have hg : (0 : ℝ) ≤ geom p a := Nat.cast_nonneg _
    rw [div_le_iff₀ (by push_cast; exact hQ)]
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left hpR hQ.le]
  have hZr : (ArithmeticFunction.sigma 1 r : ℝ) / r ≤ 13 / 4 := by
    have h := small_table r hr462
    have hrR : (0 : ℝ) < r := by exact_mod_cast Nat.pos_of_ne_zero hr0
    rw [div_le_iff₀ hrR]
    have : (4 : ℝ) * ArithmeticFunction.sigma 1 r ≤ 13 * r := by exact_mod_cast h
    linarith
  have hnonneg : 0 ≤ (ArithmeticFunction.sigma 1 r : ℝ) / r := by positivity
  have hZn : (ArithmeticFunction.sigma 1 n : ℝ) / n ≤ 169 / 48 := by
    rw [hZ]
    calc _ ≤ 13 / 12 * (13 / 4) := mul_le_mul hZp hZr hnonneg (by norm_num)
      _ = 169 / 48 := by norm_num
  have hll := loglog_mono (a := 5040) (b := n) (by norm_num) (by exact_mod_cast hn.le)
  have hr := mul_lt_mul exp_gamma_lower (loglog_5040.le.trans hll) (by norm_num)
    (Real.exp_pos _).le
  linarith

/-- Robin's inequality `σ(n)/n < e^γ log log n` for every `n > 5040` with at most eight distinct
prime factors. -/
theorem robin_of_card_primeFactors_le_eight {n : ℕ} (hn : 5040 < n)
    (hcard : n.primeFactors.card ≤ 8) :
    (ArithmeticFunction.sigma 1 n : ℝ) / n <
      Real.exp Real.eulerMascheroniConstant * Real.log (Real.log (n : ℝ)) := by
  by_cases h6000 : n < 6000
  · exact robin_small hn h6000
  obtain ⟨m, hm1, hmn, hmcard, hmanti, hZ⟩ := exists_antitone_exponent_form (n := n) (by omega)
  have hnR : (6000 : ℝ) ≤ n := by exact_mod_cast not_lt.mp h6000
  by_cases hm5040 : m ≤ 5040
  · have h1 := ratio_le_5040 hm1 hm5040
    have hll := loglog_mono (a := 6000) (b := n) (by norm_num) hnR
    have hr := mul_lt_mul exp_gamma_lower (loglog_6000.le.trans hll) (by norm_num)
      (Real.exp_pos _).le
    linarith
  have hm : 5040 < m := by omega
  have hR := robin_normal_form hm hmanti (hmcard.le.trans hcard)
  have hll := loglog_mono (a := m) (b := n) (by exact_mod_cast (show 1 < m by omega))
    (by exact_mod_cast hmn)
  have := mul_le_mul_of_nonneg_left hll (Real.exp_pos Real.eulerMascheroniConstant).le
  linarith

private def ninePrimes : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23]

private theorem take_succ_prod :
    ∀ k < 9, (ninePrimes.take (k + 1)).prod = (ninePrimes.take k).prod * ninePrimes.getD k 0 := by
  decide

private theorem small_primes {k p : ℕ} (hk : k < 9) (hp : p.Prime)
    (hlt : p < ninePrimes.getD k 0) : p ∈ ninePrimes.take k := by
  have h23 : p < 23 := by
    interval_cases k <;> simp [ninePrimes] at hlt <;> omega
  interval_cases k <;> interval_cases p <;>
    first | (simp [ninePrimes] at hlt ⊢; done) | (norm_num at hp)

/-- `k ≤ 9` distinct primes have product at least the product of the first `k` primes. -/
private theorem prod_primes_ge : ∀ k ≤ 9, ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) → S.card = k →
    (ninePrimes.take k).prod ≤ ∏ p ∈ S, p := by
  intro k
  induction k with
  | zero =>
    intro _ S _ hS
    simp [Finset.card_eq_zero.mp hS, ninePrimes]
  | succ k ih =>
    intro hk S hS hcard
    have hne : S.Nonempty := Finset.card_pos.mp (by omega)
    have hqS : S.max' hne ∈ S := S.max'_mem hne
    have hcard' : (S.erase (S.max' hne)).card = k := by
      rw [Finset.card_erase_of_mem hqS, hcard]
      rfl
    have hIH := ih (by omega) (S.erase (S.max' hne))
      (fun p hp => hS p (Finset.mem_of_mem_erase hp)) hcard'
    have hq : ninePrimes.getD k 0 ≤ S.max' hne := by
      by_contra hlt
      rw [not_le] at hlt
      have hk23 : ninePrimes.getD k 0 ≤ 23 := by
        have : ∀ j < 9, ninePrimes.getD j 0 ≤ 23 := by decide
        exact this k (by omega)
      have hsub : S ⊆ (ninePrimes.take k).toFinset := by
        intro p hp
        have hpq : p ≤ S.max' hne := S.le_max' p hp
        exact List.mem_toFinset.mpr (small_primes (by omega) (hS p hp) (by omega))
      have h1 := Finset.card_le_card hsub
      have h2 : (ninePrimes.take k).toFinset.card ≤ k :=
        (List.toFinset_card_le _).trans (by simp)
      omega
    rw [take_succ_prod k (by omega), ← Finset.mul_prod_erase S _ hqS, mul_comm (S.max' hne)]
    exact Nat.mul_le_mul hIH hq

/-- Robin's inequality for every `n` with `5040 < n < 223092870 = 2·3·5·7·11·13·17·19·23`. -/
theorem robin_lt_223092870 {n : ℕ} (hn : 5040 < n) (hn' : n < 223092870) :
    (ArithmeticFunction.sigma 1 n : ℝ) / n <
      Real.exp Real.eulerMascheroniConstant * Real.log (Real.log (n : ℝ)) := by
  refine robin_of_card_primeFactors_le_eight hn ?_
  by_contra h9
  rw [not_le] at h9
  obtain ⟨S, hSsub, hScard⟩ :=
    Finset.exists_subset_card_eq (show 9 ≤ n.primeFactors.card by omega)
  have h1 := prod_primes_ge 9 le_rfl S
    (fun p hp => Nat.prime_of_mem_primeFactors (hSsub hp)) hScard
  have h2 : ∏ p ∈ S, p ≤ n := Nat.le_of_dvd (by omega)
    ((Finset.prod_dvd_prod_of_subset _ _ _ hSsub).trans (Nat.prod_primeFactors_dvd n))
  have h3 : (ninePrimes.take 9).prod = 223092870 := by decide
  omega

end D5.S3.Arith.Robin.FewDistinctPrimes
