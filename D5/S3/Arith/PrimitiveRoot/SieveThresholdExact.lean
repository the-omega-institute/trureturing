/- GID: D5/S3/Arith/PrimitiveRoot/SieveThresholdExact
   generality: G
   mirror-B: D5/B/S3/Arith/PrimitiveRoot/SieveThresholdExact
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Arith/PrimitiveRoot/SieveThresholdExact.exists_prime_primitiveRoot; premises=D5/S3/Arith/PrimitiveRoot/SieveSevenFactors.seven_candidates,D5/S3/Arith/PrimitiveRoot/SieveThreshold.feasible_of_ge_4100000
   digest: The exact arithmetic threshold for the coarse signed sieve estimates. -/
import D5.S3.Arith.PrimitiveRoot.SieveSevenFactors
import D5.S3.Arith.PrimitiveRoot.SieveThreshold

/-! Exact threshold and infeasible parameters for the coarse smoothed estimates. -/

namespace D5.S3.Arith.PrimitiveRoot.SieveThresholdExact
open scoped BigOperators
open SievePrimeFactors SieveThreshold SieveSevenFactors CharacterExpansion CharacterSieve

private lemma margin_3483482 {x A : ℝ} (hx : 3483482 ≤ x)
    (hAb : A ≤ 165 / 4) :
    2 + 3 * A * Real.log x < Real.sqrt x := by
  classical
  have hexp : Real.exp 2 ≤ (3483482 : ℝ) := exp_two_le (by norm_num)
  apply margin_mono hexp hx
  have hlog : Real.log 3483482 < 1883 / 125 := by
    let v : ℝ := 99710273 / 100000000
    have hv : 0 < v := by norm_num [v]
    have hc : (3483482 : ℝ) < 2 ^ 22 * v ^ 64 := by norm_num [v]
    have hl := Real.log_lt_log (by norm_num : (0 : ℝ) < 3483482) hc
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow] at hl
    norm_num only [Nat.cast_ofNat] at hl
    have hb := Real.log_le_sub_one_of_pos hv
    dsimp [v] at hb
    nlinarith [Real.log_two_lt_d9]
  have hs : (9332 / 5 : ℝ) < Real.sqrt 3483482 :=
    (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  have hl : 0 ≤ Real.log (3483482 : ℝ) := Real.log_nonneg (by norm_num)
  have hmul := mul_le_mul_of_nonneg_right hAb hl
  nlinarith [hlog]

private lemma covered_sieve_eq (x e : ℕ) (T : Finset ℕ) (hx : x - 1 ≠ 0)
    (hcover : ∀ p : ℕ, p.Prime → p ∣ x - 1 → p ∣ e ∨ p ∈ T) :
    sievePrimes x e T = (x - 1).primeFactors \ (Nat.gcd e (x - 1)).primeFactors := by
  classical
  have hf : Nat.gcd e (x - 1) ≠ 0 :=
    Nat.ne_of_gt (Nat.gcd_pos_of_pos_right _ (Nat.pos_of_ne_zero hx))
  ext p
  simp only [sievePrimes, Finset.mem_filter, Finset.mem_sdiff]
  constructor
  · rintro ⟨hT, hp, hd, hne⟩
    refine ⟨hp.mem_primeFactors hd hx, ?_⟩
    intro h
    exact hne ((Nat.dvd_of_mem_primeFactors h).trans (Nat.gcd_dvd_left _ _))
  · rintro ⟨hS, hE⟩
    obtain ⟨hp, hd, _⟩ := Nat.mem_primeFactors.mp hS
    have hn : ¬p ∣ e := fun h => hE (hp.mem_primeFactors (Nat.dvd_gcd h hd) hf)
    exact ⟨(hcover p hp hd).resolve_left hn, hp, hd, hn⟩

private def dQ (U : Finset ℕ) : ℚ := 1 - ∑ p ∈ U, (p : ℚ)⁻¹

private def kQ (E U : Finset ℕ) : ℚ :=
  dQ U * (2 ^ E.card - 1) + ((U.card : ℚ) - 1 + dQ U) * 2 ^ E.card

private lemma cast_dQ (U : Finset ℕ) : (dQ U : ℝ) = delta U := by
  classical
  simp [dQ, delta]

private lemma cast_kQ (f : ℕ) (U : Finset ℕ) :
    (kQ f.primeFactors U : ℝ) = errorCoefficient f U := by
  classical
  simp [kQ, errorCoefficient, cast_dQ]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
-- Exact rational reduction checks both seven-prime support powersets.
private lemma coefficient_obstruction (x e v : ℕ) (T : Finset ℕ)
    (hx : x - 1 ≠ 0) (hv : v = 17 ∨ v = 29)
    (hS : (x - 1).primeFactors = {2, 3, 5, 7, 11, 13, v})
    (hcover : ∀ p : ℕ, p.Prime → p ∣ x - 1 → p ∣ e ∨ p ∈ T)
    (hδ : 0 < delta (sievePrimes x e T)) :
    42 * delta (sievePrimes x e T) <
      errorCoefficient (Nat.gcd e (x - 1)) (sievePrimes x e T) := by
  classical
  let f := Nat.gcd e (x - 1)
  have hU := covered_sieve_eq x e T hx hcover
  have hsub : f.primeFactors ⊆ ({2, 3, 5, 7, 11, 13, v} : Finset ℕ) :=
    hS ▸ Nat.primeFactors_mono (Nat.gcd_dvd_right e (x - 1)) hx
  have hδQ : 0 < dQ ({2, 3, 5, 7, 11, 13, v} \ f.primeFactors) := by
    have hreal : 0 < (dQ ({2, 3, 5, 7, 11, 13, v} \ f.primeFactors) : ℝ) := by
      simpa only [cast_dQ, hU, hS, f] using hδ
    exact_mod_cast hreal
  have certificate : ∀ E ∈ ({2, 3, 5, 7, 11, 13, v} : Finset ℕ).powerset,
      0 < dQ ({2, 3, 5, 7, 11, 13, v} \ E) →
      42 * dQ ({2, 3, 5, 7, 11, 13, v} \ E) <
        kQ E ({2, 3, 5, 7, 11, 13, v} \ E) := by
    rcases hv with rfl | rfl <;> unfold kQ dQ <;> decide +kernel
  have hc := certificate f.primeFactors
    (Finset.mem_powerset.mpr hsub) hδQ
  have hreal : (42 : ℝ) * (dQ ({2, 3, 5, 7, 11, 13, v} \ f.primeFactors) : ℝ) <
      (kQ f.primeFactors ({2, 3, 5, 7, 11, 13, v} \ f.primeFactors) : ℝ) := by
    exact_mod_cast hc
  simpa only [cast_dQ, cast_kQ, hU, hS, f] using hreal

private lemma log_lower_3483481 {x : ℝ} (hx : 3483481 ≤ x) : 15 < Real.log x := by
  classical
  have hp : (0 : ℝ) < 83 / 100 := by norm_num
  have hl := Real.one_sub_inv_le_log_of_pos hp
  have hb : Real.log ((83 / 100 : ℝ) * 2 ^ 22) < Real.log x :=
    Real.log_lt_log (by positivity) (by linarith)
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at hb
  norm_num only [Nat.cast_ofNat] at hb
  norm_num at hl
  nlinarith [Real.log_two_gt_d9]

private lemma rational_margin (x : ℕ) (C b : ℝ) (hx : 0 < x) (hC : 0 ≤ C)
    (hb : 0 ≤ b) (hsq : b ^ 2 < x)
    (hnum : 2 + 3 * C * (22 * (6931471808 / 10000000000 : ℝ) +
      x / 2 ^ 22 - 1) < b) :
    2 + 3 * C * Real.log x < Real.sqrt x := by
  classical
  have hl := Real.log_le_sub_one_of_pos
    (show (0 : ℝ) < x / 2 ^ 22 by positivity)
  rw [Real.log_div (by positivity) (by positivity), Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  have hlb : Real.log x < 22 * (6931471808 / 10000000000 : ℝ) +
      x / 2 ^ 22 - 1 := by nlinarith [Real.log_two_lt_d9]
  have hmul := mul_le_mul_of_nonneg_left hlb.le (show 0 ≤ 3 * C by positivity)
  have hs := (Real.lt_sqrt hb).mpr hsq
  nlinarith

private lemma feasible_by_support (x : ℕ) (S : Finset ℕ)
    (hS : (x - 1).primeFactors = S) (hx : 1 < x) (h6 : 6 ∣ x - 1) (C : ℝ)
    (hδ : 0 < delta (S \ {2, 3}))
    (hK : errorCoefficient 6 (S \ {2, 3}) ≤ delta (S \ {2, 3}) * C)
    (hmargin : 2 + 3 * C * Real.log x < Real.sqrt x) : Feasible x := by
  classical
  let T := S \ {2, 3}
  have hcover : ∀ p : ℕ, p.Prime → p ∣ x - 1 → p ∣ 6 ∨ p ∈ T := by
    intro p hp hd
    by_cases h : p ∣ 6
    · exact Or.inl h
    · right
      refine Finset.mem_sdiff.mpr ⟨hS ▸ hp.mem_primeFactors hd (by omega), ?_⟩
      intro hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with rfl | rfl <;> norm_num at h
  have hU : sievePrimes x 6 T = T := by
    rw [covered_sieve_eq x 6 T (by omega) hcover, Nat.gcd_eq_left h6, hS]
    have hpf : Nat.primeFactors 6 = {2, 3} := by decide +kernel
    rw [hpf]
  refine ⟨6, T, by decide, hcover, ?_, ?_⟩
  · rwa [hU]
  · rw [hU, Nat.gcd_eq_left h6]
    exact signed_margin (by exact_mod_cast hx.le) hδ hK hmargin

private lemma feasible_below_tail (x : ℕ) (hlo : 3483482 ≤ x) (hhi : x < 4100000)
    (hne : x ≠ 3573571) : Feasible x := by
  classical
  have hx1 : 1 < x := by omega
  have hxR : (3483482 : ℝ) ≤ x := by exact_mod_cast hlo
  have hxR1 : (1 : ℝ) ≤ x := by exact_mod_cast hx1.le
  let k := (x - 1).primeFactors.card
  have hk7 : k ≤ 7 := by
    by_contra h
    have hc : (x - 1).primeFactors.card = 8 + (k - 8) := by dsimp [k] at *; omega
    have hr := (radical_lower (x - 1) (k - 8) hc.ge).trans
      (Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd (x - 1)))
    have hp : 1 ≤ 19 ^ (k - 8) := Nat.one_le_pow _ _ (by omega)
    have hn : 9699690 ≤ x - 1 := (by nlinarith : 9699690 ≤ 9699690 * 19 ^ (k - 8))
      |>.trans hr
    omega
  by_cases hk2 : k ≤ 2
  · obtain ⟨e, T, he, hed, hcover, hr, hs, _, _, hU, hδ⟩ :=
      split_support x k 0 hx1 (by simp [k])
    have hr : (Nat.gcd e (x - 1)).primeFactors.card = k := by
      simpa only [Nat.gcd_eq_left hed] using hr
    have hT : T = ∅ := Finset.card_eq_zero.mp hs
    refine ⟨e, T, he, hcover, ?_, ?_⟩
    · rw [hU, hT]
      norm_num [delta]
    · rw [hU, hT]
      apply signed_margin hxR1 (by norm_num [delta]) (A := 165 / 4)
      · have hp : (2 : ℝ) ^ k ≤ 2 ^ 2 := pow_le_pow_right₀ (by norm_num) hk2
        norm_num [errorCoefficient, delta, hr] at *
        linarith
      · exact margin_3483482 hxR le_rfl
  by_cases hk6 : k ≤ 6
  · let s := k - 2
    have hs4 : s ≤ 4 := by dsimp [s]; omega
    have hc : (x - 1).primeFactors.card = 2 + s := by dsimp [s, k] at *; omega
    obtain ⟨e, T, he, hed, hcover, hr, hs, _, _, hU, hδ⟩ :=
      split_support x 2 s hx1 hc
    have hr : (Nat.gcd e (x - 1)).primeFactors.card = 2 := by
      simpa only [Nat.gcd_eq_left hed] using hr
    let q := (x - 1).primeFactors.orderEmbOfFin hc
    have hbound := reciprocal_tail_margin_five q (by omega : 2 ≤ 2) (by omega : s ≤ 5)
      (q.strictMono.strictMonoOn _)
      (fun i _ => Nat.prime_of_mem_primeFactors (Finset.orderEmbOfFin_mem _ hc i))
      (by intro i; apply q.monotone; change i.val + 2 ≤ 2 + i.val; omega)
    have hδb : (3 / 8 : ℝ) < delta T := by rw [hδ]; linarith
    have hδp : 0 < delta T := lt_trans (by norm_num) hδb
    refine ⟨e, T, he, hcover, ?_, ?_⟩
    · rwa [hU]
    · rw [hU]
      apply signed_margin hxR1 hδp (A := 165 / 4)
      · unfold errorCoefficient
        rw [hr, hs]
        have hsR : (s : ℝ) ≤ 4 := by exact_mod_cast hs4
        norm_num only [show (2 : ℝ) ^ 2 = 4 by norm_num]
        nlinarith
      · exact margin_3483482 hxR le_rfl
  · have hc7 : (x - 1).primeFactors.card = 7 := by dsimp [k] at *; omega
    have hc : (x - 1).primeFactors.card = 2 + 5 := hc7
    let q := (x - 1).primeFactors.orderEmbOfFin hc
    by_cases hgood : (∑ i : Fin 5, (q (Fin.natAdd 2 i) : ℝ)⁻¹) ≤ 73 / 137
    · obtain ⟨e, T, he, hed, hcover, hr, hs, _, _, hU, hδ⟩ :=
        split_support x 2 5 hx1 hc
      have hr : (Nat.gcd e (x - 1)).primeFactors.card = 2 := by
        simpa only [Nat.gcd_eq_left hed] using hr
      have hδb : (64 / 137 : ℝ) ≤ delta T := by rw [hδ]; linarith
      have hδp : 0 < delta T := lt_of_lt_of_le (by norm_num) hδb
      refine ⟨e, T, he, hcover, ?_, ?_⟩
      · rwa [hU]
      · rw [hU]
        apply signed_margin hxR1 hδp (A := 165 / 4)
        · unfold errorCoefficient
          rw [hr, hs]
          norm_num only [Nat.cast_ofNat, show (2 : ℝ) ^ 2 = 4 by norm_num]
          nlinarith
        · exact margin_3483482 hxR le_rfl
    · have hmem := (seven_candidates x).mp ⟨hlo, by omega, hc7, lt_of_not_ge hgood⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with hbad | hmem
      · exact (hne hbad).elim
      rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · apply feasible_by_support 4084081 {2, 3, 5, 7, 11, 13, 17}
          (by decide +kernel) (by decide) (by decide) (4417 / 100)
        all_goals try rw [show ({2, 3, 5, 7, 11, 13, 17} : Finset ℕ) \ {2, 3} =
          {5, 7, 11, 13, 17} from by decide +kernel]
        · norm_num [delta]
        · norm_num [errorCoefficient, delta, show Nat.primeFactors 6 = {2, 3} by decide +kernel]
        · exact rational_margin _ _ (4041 / 2) (by decide) (by norm_num) (by norm_num)
            (by norm_num) (by norm_num)
      · apply feasible_by_support 3993991 {2, 3, 5, 7, 11, 13, 19}
          (by decide +kernel) (by decide) (by decide) (437 / 10)
        all_goals try rw [show ({2, 3, 5, 7, 11, 13, 19} : Finset ℕ) \ {2, 3} =
          {5, 7, 11, 13, 19} from by decide +kernel]
        · norm_num [delta]
        · norm_num [errorCoefficient, delta, show Nat.primeFactors 6 = {2, 3} by decide +kernel]
        · exact rational_margin _ _ 1998 (by decide) (by norm_num) (by norm_num)
            (by norm_num) (by norm_num)
      · apply feasible_by_support 3723721 {2, 3, 5, 7, 11, 13, 31}
          (by decide +kernel) (by decide) (by decide) (211 / 5)
        all_goals try rw [show ({2, 3, 5, 7, 11, 13, 31} : Finset ℕ) \ {2, 3} =
          {5, 7, 11, 13, 31} from by decide +kernel]
        · norm_num [delta]
        · norm_num [errorCoefficient, delta, show Nat.primeFactors 6 = {2, 3} by decide +kernel]
        · exact rational_margin _ _ 1929 (by decide) (by norm_num) (by norm_num)
            (by norm_num) (by norm_num)
      · apply feasible_by_support 3693691 {2, 3, 5, 7, 11, 13, 41}
          (by decide +kernel) (by decide) (by decide) (83 / 2)
        all_goals try rw [show ({2, 3, 5, 7, 11, 13, 41} : Finset ℕ) \ {2, 3} =
          {5, 7, 11, 13, 41} from by decide +kernel]
        · norm_num [delta]
        · norm_num [errorCoefficient, delta, show Nat.primeFactors 6 = {2, 3} by decide +kernel]
        · exact rational_margin _ _ 1900 (by decide) (by norm_num) (by norm_num)
            (by norm_num) (by norm_num)
      · apply feasible_by_support 3873871 {2, 3, 5, 7, 11, 13, 43}
          (by decide +kernel) (by decide) (by decide) (83 / 2)
        all_goals try rw [show ({2, 3, 5, 7, 11, 13, 43} : Finset ℕ) \ {2, 3} =
          {5, 7, 11, 13, 43} from by decide +kernel]
        · norm_num [delta]
        · norm_num [errorCoefficient, delta, show Nat.primeFactors 6 = {2, 3} by decide +kernel]
        · exact rational_margin _ _ 1900 (by decide) (by norm_num) (by norm_num)
            (by norm_num) (by norm_num)
      · apply feasible_by_support 3730651 {2, 3, 5, 7, 11, 17, 19}
          (by decide +kernel) (by decide) (by decide) (211 / 5)
        all_goals try rw [show ({2, 3, 5, 7, 11, 17, 19} : Finset ℕ) \ {2, 3} =
          {5, 7, 11, 17, 19} from by decide +kernel]
        · norm_num [delta]
        · norm_num [errorCoefficient, delta, show Nat.primeFactors 6 = {2, 3} by decide +kernel]
        · exact rational_margin _ _ 1929 (by decide) (by norm_num) (by norm_num)
            (by norm_num) (by norm_num)
      · apply feasible_by_support 3612841 {2, 3, 5, 7, 11, 17, 23}
          (by decide +kernel) (by decide) (by decide) (83 / 2)
        all_goals try rw [show ({2, 3, 5, 7, 11, 17, 23} : Finset ℕ) \ {2, 3} =
          {5, 7, 11, 17, 23} from by decide +kernel]
        · norm_num [delta]
        · norm_num [errorCoefficient, delta, show Nat.primeFactors 6 = {2, 3} by decide +kernel]
        · exact rational_margin _ _ 1900 (by decide) (by norm_num) (by norm_num)
            (by norm_num) (by norm_num)

/-- Feasibility unconditionally excludes both arithmetic obstructions. -/
theorem feasible_ne_exceptions (x : ℕ) :
    Feasible x → x ≠ 3483481 ∧ x ≠ 3573571 := by
  classical
  have obstruction (x : ℕ) (hx : x = 3483481 ∨ x = 3573571) : ¬Feasible x := by
    intro ⟨e, T, he, hcover, hδ, hpos⟩
    have hx0 : x - 1 ≠ 0 := by rcases hx with rfl | rfl <;> decide
    have hcoef : 42 * delta (sievePrimes x e T) <
        errorCoefficient (Nat.gcd e (x - 1)) (sievePrimes x e T) := by
      rcases hx with rfl | rfl
      · exact coefficient_obstruction _ _ 29 _ hx0 (Or.inr rfl)
          (by decide +kernel) hcover hδ
      · exact coefficient_obstruction _ _ 17 _ hx0 (Or.inl rfl)
          (by decide +kernel) hcover hδ
    have hlo : (3483481 : ℝ) ≤ x := by rcases hx with rfl | rfl <;> norm_num
    have hhi : (x : ℝ) < 1891 ^ 2 := by rcases hx with rfl | rfl <;> norm_num
    have hs0 : 0 < Real.sqrt (x : ℝ) := Real.sqrt_pos.mpr (by linarith)
    have hlog := log_lower_3483481 hlo
    have hs := (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1891)).mpr hhi
    have hM : 0 < (3 / 2 : ℝ) * Real.sqrt x * Real.log x := by positivity
    have hK := mul_lt_mul_of_pos_right hcoef hM
    have hlogmul := mul_lt_mul_of_pos_left hlog (mul_pos hδ hs0)
    have hsmul := mul_lt_mul_of_pos_left hs (mul_pos hδ hs0)
    have hsq := congrArg (fun t => delta (sievePrimes x e T) * t)
      (Real.sq_sqrt (show (0 : ℝ) ≤ x by positivity))
    nlinarith

  intro h
  exact ⟨fun heq => obstruction x (Or.inl heq) h,
    fun heq => obstruction x (Or.inr heq) h⟩

/-- Exact feasibility for every integer in the threshold range, without a primality assumption. -/
theorem feasible_iff (x : ℕ) (hx : 3483481 ≤ x) :
    Feasible x ↔ x ≠ 3483481 ∧ x ≠ 3573571 := by
  classical
  constructor
  · exact feasible_ne_exceptions x
  · rintro ⟨hfirst, hsecond⟩
    by_cases htail : 4100000 ≤ x
    · exact feasible_of_ge_4100000 x htail
    · exact feasible_below_tail x (by omega) (by omega) hsecond

/-- Covering parameters transfer squarefree-order character bounds to a prime primitive root. -/
theorem exists_prime_primitiveRoot_of_covering (p : ℕ) [Fact p.Prime]
    (M : ℝ)
    (hM : ∀ χ : DirichletCharacter ℂ p, χ ≠ 1 →
      orderOf χ ∣ ∏ q ∈ (p - 1).primeFactors, q →
      |(smoothedCharacterSum p χ).re| ≤ M)
    (hparams : ∃ (e : ℕ) (T : Finset ℕ), e ≠ 0 ∧
      (∀ q : ℕ, q.Prime → q ∣ p - 1 → q ∣ e ∨ q ∈ T) ∧
      errorCoefficient (Nat.gcd e (p - 1)) (sievePrimes p e T) * M <
        delta (sievePrimes p e T) * (smoothedCharacterSum p 1).re) :
    ∃ q : ℕ, q.Prime ∧ q < p ∧ orderOf (q : ZMod p) = p - 1 := by
  classical
  obtain ⟨e, T, he, hcover, hmargin⟩ := hparams
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  let f := Nat.gcd e (p - 1)
  have hf : f ≠ 0 := Nat.ne_of_gt (Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero he))
  have hcoverf : ∀ q : ℕ, q.Prime → q ∣ p - 1 → q ∣ f ∨ q ∈ T := by
    intro q hq hd
    exact (hcover q hq hd).imp (fun h => Nat.dvd_gcd h hd) id
  have hU : sievePrimes p f T = sievePrimes p e T := by
    ext t
    simp only [sievePrimes, Finset.mem_filter]
    constructor
    · rintro ⟨ht, hprime, hd, hn⟩
      exact ⟨ht, hprime, hd, fun h => hn (Nat.dvd_gcd h hd)⟩
    · rintro ⟨ht, hprime, hd, hn⟩
      exact ⟨ht, hprime, hd, fun h => hn (h.trans (Nat.gcd_dvd_left _ _))⟩
  apply (exists_prime_primitiveRoot_of_smoothed_signed p f T
    M hf hcoverf ?_ ?_).2
  · intro χ hχ hord
    apply hM χ hχ
    have hsub : f.primeFactors ⊆ (p - 1).primeFactors :=
      Nat.primeFactors_mono (Nat.gcd_dvd_right _ _) (by omega)
    rcases hord with hd | ⟨t, ht, hd⟩
    · exact hd.trans (Finset.prod_dvd_prod_of_subset _ _ _ hsub)
    · have hnot : t ∉ f.primeFactors := by
        intro hmem
        exact (Finset.mem_filter.mp ht).2.2.2 (Nat.dvd_of_mem_primeFactors hmem)
      have htmem : t ∈ (p - 1).primeFactors :=
        (Finset.mem_filter.mp ht).2.1.mem_primeFactors
          (Finset.mem_filter.mp ht).2.2.1 (by omega)
      have hdprod : t * (∏ q ∈ f.primeFactors, q) ∣
          ∏ q ∈ (p - 1).primeFactors, q := by
        have hins : (∏ q ∈ insert t f.primeFactors, q) =
            t * (∏ q ∈ f.primeFactors, q) := Finset.prod_insert hnot
        rw [← hins]
        exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.insert_subset htmem hsub)
      exact hd.trans hdprod
  · rw [Nat.gcd_eq_left (Nat.gcd_dvd_right e (p - 1)), hU]
    exact hmargin

/-- Coarse estimates for squarefree character orders give a prime primitive root. -/
theorem exists_prime_primitiveRoot (p : ℕ) [Fact p.Prime] (hp : 3483482 ≤ p)
    (hM : ∀ χ : DirichletCharacter ℂ p, χ ≠ 1 →
      orderOf χ ∣ ∏ q ∈ (p - 1).primeFactors, q →
      |(smoothedCharacterSum p χ).re| ≤ (3 / 2 : ℝ) * Real.sqrt p * Real.log p)
    (hmain : (p : ℝ) / 2 - Real.sqrt p ≤ (smoothedCharacterSum p 1).re) :
    ∃ q : ℕ, q.Prime ∧ q < p ∧ orderOf (q : ZMod p) = p - 1 := by
  classical
  have hne : p ≠ 3573571 := by
    intro heq
    have hprime : Nat.Prime 3573571 := heq ▸ (Fact.out : p.Prime)
    norm_num at hprime
  obtain ⟨e, T, he, hcover, hδ, hmargin⟩ :=
    (feasible_iff p (by omega)).mpr ⟨by omega, hne⟩
  apply exists_prime_primitiveRoot_of_covering p _ hM
  refine ⟨e, T, he, hcover, ?_⟩
  exact hmargin.trans_le (mul_le_mul_of_nonneg_left hmain hδ.le)

end D5.S3.Arith.PrimitiveRoot.SieveThresholdExact

-- The utility header grammar requires its metadata on one physical line.
set_option linter.style.longLine.maxLineLength 258
