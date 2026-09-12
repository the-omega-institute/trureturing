/- GID: D5/S3/Arith/GoldenResource/A279609DoublingRefutation
   generality: I
   mirror-B: D5/B/S3/Arith/GoldenResource/A279609DoublingRefutation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=atom:f1e442dc23de02562417cb024f7fc6712689168f5b16fee22b387bf678d18ca5; result=D5/S3/Arith/GoldenResource/A279609DoublingRefutation.result; claim=D5/S3/Arith/GoldenResource/A279609DoublingRefutation.claim
   digest: A certified adjacent pair of colossally abundant integers refutes the proposed doubling inequality. -/

import D5.S3.Arith.GoldenResource.FirstLayerMarginalAntitone

/- Library-search audit trail (2026-09-13):
   1. D5 searches for the four witness numerals, the exact price-window shape,
      adjacency, and the harmonic-exponential floor expression found no theorem
      proving this instance. Existing price-interval and threshold declarations are
      reused. A PCRE word-boundary search for goldenUpperPrice found two files.
   2. Pinned Mathlib searches found no A279609 or colossal-abundance result and no
      witness numeral. Real logarithm comparison, factorization reconstruction,
      exponential bounds, and sigma multiplicativity declarations are reused.
   3. GitHub Lean-code searches for A279609, both witness integers, colossally
      abundant, goldenUpperPrice, and the combined floor shape returned no hit.
      The positive-control query Real.exp_bound returned thirty-six hits. -/

namespace D5.S3.Arith.GoldenResource.A279609DoublingRefutation

open D5.S3.Arith.GoldenResourceOptimalInteger

noncomputable section

private theorem marginal_lt_reference
    (x p : ℝ) (d e : ℕ)
    (hx : 1 < x) (hp : 1 < p) (hd : 0 < d) (_he : 0 < e)
    (hxpow : x ^ d < (255 / 254 : ℝ) ^ e)
    (hppow : (2 : ℝ) ^ e < p ^ d) :
    Real.log x / Real.log p < Real.log (255 / 254) / Real.log 2 := by
  have hlogp : 0 < Real.log p := Real.log_pos hp
  have hlogtwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlogref : 0 < Real.log (255 / 254 : ℝ) := Real.log_pos (by norm_num)
  have hxy : (d : ℝ) * Real.log x < (e : ℝ) * Real.log (255 / 254 : ℝ) := by
    have h := Real.log_lt_log (pow_pos (by positivity) _) hxpow
    simpa only [Real.log_pow] using h
  have hp2 : (e : ℝ) * Real.log 2 < (d : ℝ) * Real.log p := by
    have h := Real.log_lt_log (pow_pos (by positivity) _) hppow
    simpa only [Real.log_pow] using h
  have hdreal : (0 : ℝ) < d := by exact_mod_cast hd
  have hscaled :
      (d : ℝ) * (Real.log x * Real.log 2) <
        (d : ℝ) * (Real.log (255 / 254 : ℝ) * Real.log p) := by
    calc
      (d : ℝ) * (Real.log x * Real.log 2) =
          ((d : ℝ) * Real.log x) * Real.log 2 := by ring
      _ < ((e : ℝ) * Real.log (255 / 254 : ℝ)) * Real.log 2 :=
        mul_lt_mul_of_pos_right hxy hlogtwo
      _ = Real.log (255 / 254 : ℝ) * ((e : ℝ) * Real.log 2) := by ring
      _ < Real.log (255 / 254 : ℝ) * ((d : ℝ) * Real.log p) :=
        mul_lt_mul_of_pos_left hp2 hlogref
      _ = (d : ℝ) * (Real.log (255 / 254 : ℝ) * Real.log p) := by ring
  have hcross := lt_of_mul_lt_mul_left hscaled hdreal.le
  exact (div_lt_div_iff₀ hlogp hlogtwo).mpr hcross

private theorem reference_lt_marginal
    (x p : ℝ) (d e : ℕ)
    (hx : 1 < x) (hp : 1 < p) (hd : 0 < d) (_he : 0 < e)
    (hppow : p ^ d < (2 : ℝ) ^ e)
    (hxpow : (255 / 254 : ℝ) ^ e < x ^ d) :
    Real.log (255 / 254) / Real.log 2 < Real.log x / Real.log p := by
  have hlogx : 0 < Real.log x := Real.log_pos hx
  have hlogp : 0 < Real.log p := Real.log_pos hp
  have hlogtwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hp2 : (d : ℝ) * Real.log p < (e : ℝ) * Real.log 2 := by
    have h := Real.log_lt_log (pow_pos (by positivity) _) hppow
    simpa only [Real.log_pow] using h
  have hxy : (e : ℝ) * Real.log (255 / 254 : ℝ) < (d : ℝ) * Real.log x := by
    have h := Real.log_lt_log (pow_pos (by positivity) _) hxpow
    simpa only [Real.log_pow] using h
  have hdreal : (0 : ℝ) < d := by exact_mod_cast hd
  have hscaled :
      (d : ℝ) * (Real.log (255 / 254 : ℝ) * Real.log p) <
        (d : ℝ) * (Real.log x * Real.log 2) := by
    calc
      (d : ℝ) * (Real.log (255 / 254 : ℝ) * Real.log p) =
          Real.log (255 / 254 : ℝ) * ((d : ℝ) * Real.log p) := by ring
      _ < Real.log (255 / 254 : ℝ) * ((e : ℝ) * Real.log 2) :=
        mul_lt_mul_of_pos_left hp2 (Real.log_pos (by norm_num))
      _ = ((e : ℝ) * Real.log (255 / 254 : ℝ)) * Real.log 2 := by ring
      _ < ((d : ℝ) * Real.log x) * Real.log 2 :=
        mul_lt_mul_of_pos_right hxy hlogtwo
      _ = (d : ℝ) * (Real.log x * Real.log 2) := by ring
  have hcross := lt_of_mul_lt_mul_left hscaled hdreal.le
  exact (div_lt_div_iff₀ hlogtwo hlogp).mpr hcross

private theorem golden_marginal_lt_reference
    (p a : ℕ) (x : ℝ) (d e : ℕ)
    (hshape : goldenLayerMarginal p a = Real.log x / Real.log p)
    (hx : 1 < x) (hp : 1 < (p : ℝ)) (hd : 0 < d) (he : 0 < e)
    (hxpow : x ^ d < (255 / 254 : ℝ) ^ e)
    (hppow : (2 : ℝ) ^ e < (p : ℝ) ^ d) :
    goldenLayerMarginal p a < goldenLayerMarginal 2 7 := by
  rw [hshape]
  have h := marginal_lt_reference x p d e hx hp hd he hxpow hppow
  norm_num [goldenLayerMarginal] at h ⊢
  exact h

private theorem reference_lt_golden_marginal
    (p a : ℕ) (x : ℝ) (d e : ℕ)
    (hshape : goldenLayerMarginal p a = Real.log x / Real.log p)
    (hx : 1 < x) (hp : 1 < (p : ℝ)) (hd : 0 < d) (he : 0 < e)
    (hppow : (p : ℝ) ^ d < (2 : ℝ) ^ e)
    (hxpow : (255 / 254 : ℝ) ^ e < x ^ d) :
    goldenLayerMarginal 2 7 < goldenLayerMarginal p a := by
  rw [hshape]
  have h := reference_lt_marginal x p d e hx hp hd he hppow hxpow
  norm_num [goldenLayerMarginal] at h ⊢
  exact h

private theorem m_price_window_rational_separation :
    (goldenLayerMarginal 3 5 < goldenLayerMarginal 2 7 ∧
      goldenLayerMarginal 5 3 < goldenLayerMarginal 2 7 ∧
      goldenLayerMarginal 7 3 < goldenLayerMarginal 2 7 ∧
      goldenLayerMarginal 11 2 < goldenLayerMarginal 2 7 ∧
      goldenLayerMarginal 13 2 < goldenLayerMarginal 2 7 ∧
      goldenLayerMarginal 17 2 < goldenLayerMarginal 2 7 ∧
      goldenLayerMarginal 19 2 < goldenLayerMarginal 2 7 ∧
      goldenLayerMarginal 23 2 < goldenLayerMarginal 2 7 ∧
      goldenLayerMarginal 29 2 < goldenLayerMarginal 2 7 ∧
      goldenLayerMarginal 31 2 < goldenLayerMarginal 2 7 ∧
      goldenLayerMarginal 37 2 < goldenLayerMarginal 2 7 ∧
      goldenLayerMarginal 41 2 < goldenLayerMarginal 2 7 ∧
      goldenLayerMarginal 43 2 < goldenLayerMarginal 2 7 ∧
      goldenLayerMarginal 47 1 < goldenLayerMarginal 2 7) ∧
    (goldenLayerMarginal 2 7 < goldenLayerMarginal 2 6 ∧
      goldenLayerMarginal 2 7 < goldenLayerMarginal 3 4 ∧
      goldenLayerMarginal 2 7 < goldenLayerMarginal 5 2 ∧
      goldenLayerMarginal 2 7 < goldenLayerMarginal 7 2 ∧
      goldenLayerMarginal 2 7 < goldenLayerMarginal 11 1 ∧
      goldenLayerMarginal 2 7 < goldenLayerMarginal 13 1 ∧
      goldenLayerMarginal 2 7 < goldenLayerMarginal 17 1 ∧
      goldenLayerMarginal 2 7 < goldenLayerMarginal 19 1 ∧
      goldenLayerMarginal 2 7 < goldenLayerMarginal 23 1 ∧
      goldenLayerMarginal 2 7 < goldenLayerMarginal 29 1 ∧
      goldenLayerMarginal 2 7 < goldenLayerMarginal 31 1 ∧
      goldenLayerMarginal 2 7 < goldenLayerMarginal 37 1 ∧
      goldenLayerMarginal 2 7 < goldenLayerMarginal 41 1 ∧
      goldenLayerMarginal 2 7 < goldenLayerMarginal 43 1) := by
  have h3u : goldenLayerMarginal 3 5 < goldenLayerMarginal 2 7 := by
    apply golden_marginal_lt_reference 3 5 (364 / 363) 1 1 <;>
      norm_num [goldenLayerMarginal]
  have h5u : goldenLayerMarginal 5 3 < goldenLayerMarginal 2 7 := by
    apply golden_marginal_lt_reference 5 3 (156 / 155) 1 2 <;>
      norm_num [goldenLayerMarginal]
  have h7u : goldenLayerMarginal 7 3 < goldenLayerMarginal 2 7 := by
    apply golden_marginal_lt_reference 7 3 (400 / 399) 1 1 <;>
      norm_num [goldenLayerMarginal]
  have h11u : goldenLayerMarginal 11 2 < goldenLayerMarginal 2 7 := by
    apply golden_marginal_lt_reference 11 2 (133 / 132) 1 2 <;>
      norm_num [goldenLayerMarginal]
  have h13u : goldenLayerMarginal 13 2 < goldenLayerMarginal 2 7 := by
    apply golden_marginal_lt_reference 13 2 (183 / 182) 1 2 <;>
      norm_num [goldenLayerMarginal]
  have h17u : goldenLayerMarginal 17 2 < goldenLayerMarginal 2 7 := by
    apply golden_marginal_lt_reference 17 2 (307 / 306) 1 1 <;>
      norm_num [goldenLayerMarginal]
  have h19u : goldenLayerMarginal 19 2 < goldenLayerMarginal 2 7 := by
    apply golden_marginal_lt_reference 19 2 (381 / 380) 1 1 <;>
      norm_num [goldenLayerMarginal]
  have h23u : goldenLayerMarginal 23 2 < goldenLayerMarginal 2 7 := by
    apply golden_marginal_lt_reference 23 2 (553 / 552) 1 1 <;>
      norm_num [goldenLayerMarginal]
  have h29u : goldenLayerMarginal 29 2 < goldenLayerMarginal 2 7 := by
    apply golden_marginal_lt_reference 29 2 (871 / 870) 1 1 <;>
      norm_num [goldenLayerMarginal]
  have h31u : goldenLayerMarginal 31 2 < goldenLayerMarginal 2 7 := by
    apply golden_marginal_lt_reference 31 2 (993 / 992) 1 1 <;>
      norm_num [goldenLayerMarginal]
  have h37u : goldenLayerMarginal 37 2 < goldenLayerMarginal 2 7 := by
    apply golden_marginal_lt_reference 37 2 (1407 / 1406) 1 1 <;>
      norm_num [goldenLayerMarginal]
  have h41u : goldenLayerMarginal 41 2 < goldenLayerMarginal 2 7 := by
    apply golden_marginal_lt_reference 41 2 (1723 / 1722) 1 1 <;>
      norm_num [goldenLayerMarginal]
  have h43u : goldenLayerMarginal 43 2 < goldenLayerMarginal 2 7 := by
    apply golden_marginal_lt_reference 43 2 (1893 / 1892) 1 1 <;>
      norm_num [goldenLayerMarginal]
  have h47u : goldenLayerMarginal 47 1 < goldenLayerMarginal 2 7 := by
    apply golden_marginal_lt_reference 47 1 (48 / 47) 2 11 <;>
      norm_num [goldenLayerMarginal]
  have h2l : goldenLayerMarginal 2 7 < goldenLayerMarginal 2 6 :=
    golden_layer_strict_decrease Nat.prime_two (by norm_num) (by norm_num)
  have h3l : goldenLayerMarginal 2 7 < goldenLayerMarginal 3 4 := by
    apply reference_lt_golden_marginal 3 4 (121 / 120) 1 2 <;>
      norm_num [goldenLayerMarginal]
  have h5l : goldenLayerMarginal 2 7 < goldenLayerMarginal 5 2 := by
    apply reference_lt_golden_marginal 5 2 (31 / 30) 1 3 <;>
      norm_num [goldenLayerMarginal]
  have h7l : goldenLayerMarginal 2 7 < goldenLayerMarginal 7 2 := by
    apply reference_lt_golden_marginal 7 2 (57 / 56) 1 3 <;>
      norm_num [goldenLayerMarginal]
  have h11l : goldenLayerMarginal 2 7 < goldenLayerMarginal 11 1 := by
    apply reference_lt_golden_marginal 11 1 (12 / 11) 1 4 <;>
      norm_num [goldenLayerMarginal]
  have h13l : goldenLayerMarginal 2 7 < goldenLayerMarginal 13 1 := by
    apply reference_lt_golden_marginal 13 1 (14 / 13) 1 4 <;>
      norm_num [goldenLayerMarginal]
  have h17l : goldenLayerMarginal 2 7 < goldenLayerMarginal 17 1 := by
    apply reference_lt_golden_marginal 17 1 (18 / 17) 1 5 <;>
      norm_num [goldenLayerMarginal]
  have h19l : goldenLayerMarginal 2 7 < goldenLayerMarginal 19 1 := by
    apply reference_lt_golden_marginal 19 1 (20 / 19) 1 5 <;>
      norm_num [goldenLayerMarginal]
  have h23l : goldenLayerMarginal 2 7 < goldenLayerMarginal 23 1 := by
    apply reference_lt_golden_marginal 23 1 (24 / 23) 1 5 <;>
      norm_num [goldenLayerMarginal]
  have h29l : goldenLayerMarginal 2 7 < goldenLayerMarginal 29 1 := by
    apply reference_lt_golden_marginal 29 1 (30 / 29) 1 5 <;>
      norm_num [goldenLayerMarginal]
  have h31l : goldenLayerMarginal 2 7 < goldenLayerMarginal 31 1 := by
    apply reference_lt_golden_marginal 31 1 (32 / 31) 1 5 <;>
      norm_num [goldenLayerMarginal]
  have h37l : goldenLayerMarginal 2 7 < goldenLayerMarginal 37 1 := by
    apply reference_lt_golden_marginal 37 1 (38 / 37) 1 6 <;>
      norm_num [goldenLayerMarginal]
  have h41l : goldenLayerMarginal 2 7 < goldenLayerMarginal 41 1 := by
    apply reference_lt_golden_marginal 41 1 (42 / 41) 1 6 <;>
      norm_num [goldenLayerMarginal]
  have h43l : goldenLayerMarginal 2 7 < goldenLayerMarginal 43 1 := by
    apply reference_lt_golden_marginal 43 1 (44 / 43) 2 11 <;>
      norm_num [goldenLayerMarginal]
  exact ⟨⟨h3u, h5u, h7u, h11u, h13u, h17u, h19u, h23u, h29u, h31u, h37u,
    h41u, h43u, h47u⟩, ⟨h2l, h3l, h5l, h7l, h11l, h13l, h17l, h19l, h23l,
    h29l, h31l, h37l, h41l, h43l⟩⟩

private def mFactors : ℕ →₀ ℕ :=
  Finsupp.single 2 6 + Finsupp.single 3 4 + Finsupp.single 5 2 +
  Finsupp.single 7 2 + Finsupp.single 11 1 + Finsupp.single 13 1 +
  Finsupp.single 17 1 + Finsupp.single 19 1 + Finsupp.single 23 1 +
  Finsupp.single 29 1 + Finsupp.single 31 1 + Finsupp.single 37 1 +
  Finsupp.single 41 1 + Finsupp.single 43 1

private theorem m_factorization :
    mFactors = (395622702669701707200 : ℕ).factorization := by
  have hprime : ∀ p ∈ mFactors.support, p.Prime := by
    intro p hp
    rw [Finsupp.mem_support_iff] at hp
    by_cases h2 : p = 2; · subst p; norm_num
    by_cases h3 : p = 3; · subst p; norm_num
    by_cases h5 : p = 5; · subst p; norm_num
    by_cases h7 : p = 7; · subst p; norm_num
    by_cases h11 : p = 11; · subst p; norm_num
    by_cases h13 : p = 13; · subst p; norm_num
    by_cases h17 : p = 17; · subst p; norm_num
    by_cases h19 : p = 19; · subst p; norm_num
    by_cases h23 : p = 23; · subst p; norm_num
    by_cases h29 : p = 29; · subst p; norm_num
    by_cases h31 : p = 31; · subst p; norm_num
    by_cases h37 : p = 37; · subst p; norm_num
    by_cases h41 : p = 41; · subst p; norm_num
    by_cases h43 : p = 43; · subst p; norm_num
    simp [mFactors, h2, h3, h5, h7, h11, h13, h17, h19, h23, h29, h31,
      h37, h41, h43] at hp
  apply (Nat.eq_factorization_iff (by norm_num) hprime).mpr
  simp only [mFactors]
  repeat' rw [Finsupp.prod_add_index' (by simp) (by simp [pow_add])]
  simp

private theorem prime_dvd_m_cases {p : ℕ} (hp : p.Prime)
    (hpm : p ∣ 395622702669701707200) :
    p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 13 ∨
    p = 17 ∨ p = 19 ∨ p = 23 ∨ p = 29 ∨ p = 31 ∨
    p = 37 ∨ p = 41 ∨ p = 43 := by
  have hpos : 0 < mFactors p := by
    rw [m_factorization]
    exact hp.factorization_pos_of_dvd (by norm_num) hpm
  by_cases h2 : p = 2; · subst p; simp
  by_cases h3 : p = 3; · subst p; simp
  by_cases h5 : p = 5; · subst p; simp
  by_cases h7 : p = 7; · subst p; simp
  by_cases h11 : p = 11; · subst p; simp
  by_cases h13 : p = 13; · subst p; simp
  by_cases h17 : p = 17; · subst p; simp
  by_cases h19 : p = 19; · subst p; simp
  by_cases h23 : p = 23; · subst p; simp
  by_cases h29 : p = 29; · subst p; simp
  by_cases h31 : p = 31; · subst p; simp
  by_cases h37 : p = 37; · subst p; simp
  by_cases h41 : p = 41; · subst p; simp
  by_cases h43 : p = 43; · subst p; simp
  simp [mFactors, h2, h3, h5, h7, h11, h13, h17, h19, h23, h29, h31,
    h37, h41, h43] at hpos

open D5.S3.Arith.GoldenResource.GoldenResourcePriceInterval
open D5.S3.Arith.GoldenResource.GoldenResourceThresholdCriterion
open D5.S3.Arith.GoldenResource.GoldenSmallestMissingPrime

/-- The first witness integer has a nonempty golden-resource price window. -/
theorem m_price_window :
    goldenUpperPrice 395622702669701707200 ≤
      goldenLowerPrice 395622702669701707200 := by
  rcases m_price_window_rational_separation with
    ⟨⟨h3u, h5u, h7u, h11u, h13u, h17u, h19u, h23u, h29u, h31u, h37u,
      h41u, h43u, h47u⟩,
     ⟨h2l, h3l, h5l, h7l, h11l, h13l, h17l, h19l, h23l, h29l, h31l,
      h37l, h41l, h43l⟩⟩
  have hfac2 : (395622702669701707200 : ℕ).factorization 2 = 6 := by
    rw [← m_factorization]
    norm_num [mFactors]
  have hfac3 : (395622702669701707200 : ℕ).factorization 3 = 4 := by
    rw [← m_factorization]
    norm_num [mFactors]
  have hfac5 : (395622702669701707200 : ℕ).factorization 5 = 2 := by
    rw [← m_factorization]
    norm_num [mFactors]
  have hfac7 : (395622702669701707200 : ℕ).factorization 7 = 2 := by
    rw [← m_factorization]
    norm_num [mFactors]
  have hfac11 : (395622702669701707200 : ℕ).factorization 11 = 1 := by
    rw [← m_factorization]
    norm_num [mFactors]
  have hfac13 : (395622702669701707200 : ℕ).factorization 13 = 1 := by
    rw [← m_factorization]
    norm_num [mFactors]
  have hfac17 : (395622702669701707200 : ℕ).factorization 17 = 1 := by
    rw [← m_factorization]
    norm_num [mFactors]
  have hfac19 : (395622702669701707200 : ℕ).factorization 19 = 1 := by
    rw [← m_factorization]
    norm_num [mFactors]
  have hfac23 : (395622702669701707200 : ℕ).factorization 23 = 1 := by
    rw [← m_factorization]
    norm_num [mFactors]
  have hfac29 : (395622702669701707200 : ℕ).factorization 29 = 1 := by
    rw [← m_factorization]
    norm_num [mFactors]
  have hfac31 : (395622702669701707200 : ℕ).factorization 31 = 1 := by
    rw [← m_factorization]
    norm_num [mFactors]
  have hfac37 : (395622702669701707200 : ℕ).factorization 37 = 1 := by
    rw [← m_factorization]
    norm_num [mFactors]
  have hfac41 : (395622702669701707200 : ℕ).factorization 41 = 1 := by
    rw [← m_factorization]
    norm_num [mFactors]
  have hfac43 : (395622702669701707200 : ℕ).factorization 43 = 1 := by
    rw [← m_factorization]
    norm_num [mFactors]
  apply (colossally_abundant_iff_price_interval_nonempty (by norm_num)).mp
  refine ⟨goldenLayerMarginal 2 7, ?_,
    (golden_resource_optimal_iff_layer_thresholds ?_ (by norm_num)).mpr ⟨?_, ?_⟩⟩
  · norm_num [goldenLayerMarginal]
    positivity
  · norm_num [goldenLayerMarginal]
    positivity
  · intro p hp
    by_cases hpm : p ∣ 395622702669701707200
    · rcases prime_dvd_m_cases hp hpm with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · simpa [hfac2]
      · simpa [hfac3] using h3u.le
      · simpa [hfac5] using h5u.le
      · simpa [hfac7] using h7u.le
      · simpa [hfac11] using h11u.le
      · simpa [hfac13] using h13u.le
      · simpa [hfac17] using h17u.le
      · simpa [hfac19] using h19u.le
      · simpa [hfac23] using h23u.le
      · simpa [hfac29] using h29u.le
      · simpa [hfac31] using h31u.le
      · simpa [hfac37] using h37u.le
      · simpa [hfac41] using h41u.le
      · simpa [hfac43] using h43u.le
    · rw [Nat.factorization_eq_zero_of_not_dvd hpm]
      have hp47 : 47 ≤ p := by
        by_contra hnot
        have hlt : p < 47 := by omega
        interval_cases p <;> norm_num at hp
        all_goals norm_num at hpm
      simpa using golden_layer_marginal_one_threshold_of_le hp (by norm_num) hp47 h47u.le
  · intro p hp hpm
    rcases prime_dvd_m_cases hp hpm with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [hfac2] using h2l.le
    · simpa [hfac3] using h3l.le
    · simpa [hfac5] using h5l.le
    · simpa [hfac7] using h7l.le
    · simpa [hfac11] using h11l.le
    · simpa [hfac13] using h13l.le
    · simpa [hfac17] using h17l.le
    · simpa [hfac19] using h19l.le
    · simpa [hfac23] using h23l.le
    · simpa [hfac29] using h29l.le
    · simpa [hfac31] using h31l.le
    · simpa [hfac37] using h37l.le
    · simpa [hfac41] using h41l.le
    · simpa [hfac43] using h43l.le

private def nFactors : ℕ →₀ ℕ := mFactors + Finsupp.single 2 1

private theorem n_factorization :
    nFactors = (791245405339403414400 : ℕ).factorization := by
  have hprime : ∀ p ∈ nFactors.support, p.Prime := by
    intro p hp
    rw [Finsupp.mem_support_iff] at hp
    by_cases h2 : p = 2; · subst p; norm_num
    by_cases h3 : p = 3; · subst p; norm_num
    by_cases h5 : p = 5; · subst p; norm_num
    by_cases h7 : p = 7; · subst p; norm_num
    by_cases h11 : p = 11; · subst p; norm_num
    by_cases h13 : p = 13; · subst p; norm_num
    by_cases h17 : p = 17; · subst p; norm_num
    by_cases h19 : p = 19; · subst p; norm_num
    by_cases h23 : p = 23; · subst p; norm_num
    by_cases h29 : p = 29; · subst p; norm_num
    by_cases h31 : p = 31; · subst p; norm_num
    by_cases h37 : p = 37; · subst p; norm_num
    by_cases h41 : p = 41; · subst p; norm_num
    by_cases h43 : p = 43; · subst p; norm_num
    simp [nFactors, mFactors, h2, h3, h5, h7, h11, h13, h17, h19, h23,
      h29, h31, h37, h41, h43] at hp
  apply (Nat.eq_factorization_iff (by norm_num) hprime).mpr
  simp only [nFactors, mFactors]
  repeat' rw [Finsupp.prod_add_index' (by simp) (by simp [pow_add])]
  simp

private theorem prime_dvd_n_cases {p : ℕ} (hp : p.Prime)
    (hpn : p ∣ 791245405339403414400) :
    p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 13 ∨
    p = 17 ∨ p = 19 ∨ p = 23 ∨ p = 29 ∨ p = 31 ∨
    p = 37 ∨ p = 41 ∨ p = 43 := by
  have hpos : 0 < nFactors p := by
    rw [n_factorization]
    exact hp.factorization_pos_of_dvd (by norm_num) hpn
  by_cases h2 : p = 2; · subst p; simp
  by_cases h3 : p = 3; · subst p; simp
  by_cases h5 : p = 5; · subst p; simp
  by_cases h7 : p = 7; · subst p; simp
  by_cases h11 : p = 11; · subst p; simp
  by_cases h13 : p = 13; · subst p; simp
  by_cases h17 : p = 17; · subst p; simp
  by_cases h19 : p = 19; · subst p; simp
  by_cases h23 : p = 23; · subst p; simp
  by_cases h29 : p = 29; · subst p; simp
  by_cases h31 : p = 31; · subst p; simp
  by_cases h37 : p = 37; · subst p; simp
  by_cases h41 : p = 41; · subst p; simp
  by_cases h43 : p = 43; · subst p; simp
  simp [nFactors, mFactors, h2, h3, h5, h7, h11, h13, h17, h19, h23,
    h29, h31, h37, h41, h43] at hpos

private theorem n_shared_endpoint_rational_separation :
    (goldenLayerMarginal 2 8 < goldenLayerMarginal 2 7 ∧
      goldenLayerMarginal 3 5 < goldenLayerMarginal 2 7 ∧
      goldenLayerMarginal 5 3 < goldenLayerMarginal 2 7 ∧
      goldenLayerMarginal 7 3 < goldenLayerMarginal 2 7 ∧
      goldenLayerMarginal 11 2 < goldenLayerMarginal 2 7 ∧
      goldenLayerMarginal 13 2 < goldenLayerMarginal 2 7 ∧
      goldenLayerMarginal 17 2 < goldenLayerMarginal 2 7 ∧
      goldenLayerMarginal 19 2 < goldenLayerMarginal 2 7 ∧
      goldenLayerMarginal 23 2 < goldenLayerMarginal 2 7 ∧
      goldenLayerMarginal 29 2 < goldenLayerMarginal 2 7 ∧
      goldenLayerMarginal 31 2 < goldenLayerMarginal 2 7 ∧
      goldenLayerMarginal 37 2 < goldenLayerMarginal 2 7 ∧
      goldenLayerMarginal 41 2 < goldenLayerMarginal 2 7 ∧
      goldenLayerMarginal 43 2 < goldenLayerMarginal 2 7 ∧
      goldenLayerMarginal 47 1 < goldenLayerMarginal 2 7) ∧
    (goldenLayerMarginal 2 7 ≤ goldenLayerMarginal 2 7 ∧
      goldenLayerMarginal 2 7 < goldenLayerMarginal 3 4 ∧
      goldenLayerMarginal 2 7 < goldenLayerMarginal 5 2 ∧
      goldenLayerMarginal 2 7 < goldenLayerMarginal 7 2 ∧
      goldenLayerMarginal 2 7 < goldenLayerMarginal 11 1 ∧
      goldenLayerMarginal 2 7 < goldenLayerMarginal 13 1 ∧
      goldenLayerMarginal 2 7 < goldenLayerMarginal 17 1 ∧
      goldenLayerMarginal 2 7 < goldenLayerMarginal 19 1 ∧
      goldenLayerMarginal 2 7 < goldenLayerMarginal 23 1 ∧
      goldenLayerMarginal 2 7 < goldenLayerMarginal 29 1 ∧
      goldenLayerMarginal 2 7 < goldenLayerMarginal 31 1 ∧
      goldenLayerMarginal 2 7 < goldenLayerMarginal 37 1 ∧
      goldenLayerMarginal 2 7 < goldenLayerMarginal 41 1 ∧
      goldenLayerMarginal 2 7 < goldenLayerMarginal 43 1) := by
  rcases m_price_window_rational_separation with
    ⟨⟨h3u, h5u, h7u, h11u, h13u, h17u, h19u, h23u, h29u, h31u, h37u,
      h41u, h43u, h47u⟩,
     ⟨_, h3l, h5l, h7l, h11l, h13l, h17l, h19l, h23l, h29l, h31l,
      h37l, h41l, h43l⟩⟩
  have h2u : goldenLayerMarginal 2 8 < goldenLayerMarginal 2 7 :=
    golden_layer_strict_decrease Nat.prime_two (by norm_num) (by norm_num)
  exact ⟨⟨h2u, h3u, h5u, h7u, h11u, h13u, h17u, h19u, h23u, h29u, h31u,
    h37u, h41u, h43u, h47u⟩, ⟨le_rfl, h3l, h5l, h7l, h11l, h13l, h17l,
    h19l, h23l, h29l, h31l, h37l, h41l, h43l⟩⟩

private theorem n_thresholds_and_m_upper :
    (∀ p : ℕ, p.Prime →
      goldenLayerMarginal p ((395622702669701707200 : ℕ).factorization p + 1) ≤
        goldenLayerMarginal 2 7) ∧
    (∀ p : ℕ, p.Prime →
      goldenLayerMarginal p ((791245405339403414400 : ℕ).factorization p + 1) ≤
        goldenLayerMarginal 2 7) ∧
    (∀ p : ℕ, p.Prime → p ∣ 791245405339403414400 →
      goldenLayerMarginal 2 7 ≤
        goldenLayerMarginal p ((791245405339403414400 : ℕ).factorization p)) := by
  rcases m_price_window_rational_separation with
    ⟨⟨h3u, h5u, h7u, h11u, h13u, h17u, h19u, h23u, h29u, h31u, h37u,
      h41u, h43u, h47u⟩, _⟩
  rcases n_shared_endpoint_rational_separation with
    ⟨⟨h2nu, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩,
     ⟨h2nl, h3l, h5l, h7l, h11l, h13l, h17l, h19l, h23l, h29l, h31l,
      h37l, h41l, h43l⟩⟩
  have hmUpper : ∀ p : ℕ, p.Prime →
      goldenLayerMarginal p ((395622702669701707200 : ℕ).factorization p + 1) ≤
        goldenLayerMarginal 2 7 := by
    intro p hp
    by_cases hpm : p ∣ 395622702669701707200
    · rcases prime_dvd_m_cases hp hpm with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · simp [← m_factorization, mFactors]
      · simpa [← m_factorization, mFactors] using h3u.le
      · simpa [← m_factorization, mFactors] using h5u.le
      · simpa [← m_factorization, mFactors] using h7u.le
      · simpa [← m_factorization, mFactors] using h11u.le
      · simpa [← m_factorization, mFactors] using h13u.le
      · simpa [← m_factorization, mFactors] using h17u.le
      · simpa [← m_factorization, mFactors] using h19u.le
      · simpa [← m_factorization, mFactors] using h23u.le
      · simpa [← m_factorization, mFactors] using h29u.le
      · simpa [← m_factorization, mFactors] using h31u.le
      · simpa [← m_factorization, mFactors] using h37u.le
      · simpa [← m_factorization, mFactors] using h41u.le
      · simpa [← m_factorization, mFactors] using h43u.le
    · rw [Nat.factorization_eq_zero_of_not_dvd hpm]
      have hp47 : 47 ≤ p := by
        by_contra hnot
        have hlt : p < 47 := by omega
        interval_cases p <;> norm_num at hp
        all_goals norm_num at hpm
      simpa using golden_layer_marginal_one_threshold_of_le hp (by norm_num) hp47 h47u.le
  have hnUpper : ∀ p : ℕ, p.Prime →
      goldenLayerMarginal p ((791245405339403414400 : ℕ).factorization p + 1) ≤
        goldenLayerMarginal 2 7 := by
    intro p hp
    by_cases hpn : p ∣ 791245405339403414400
    · rcases prime_dvd_n_cases hp hpn with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · simpa [← n_factorization, nFactors, mFactors] using h2nu.le
      · simpa [← n_factorization, nFactors, mFactors] using h3u.le
      · simpa [← n_factorization, nFactors, mFactors] using h5u.le
      · simpa [← n_factorization, nFactors, mFactors] using h7u.le
      · simpa [← n_factorization, nFactors, mFactors] using h11u.le
      · simpa [← n_factorization, nFactors, mFactors] using h13u.le
      · simpa [← n_factorization, nFactors, mFactors] using h17u.le
      · simpa [← n_factorization, nFactors, mFactors] using h19u.le
      · simpa [← n_factorization, nFactors, mFactors] using h23u.le
      · simpa [← n_factorization, nFactors, mFactors] using h29u.le
      · simpa [← n_factorization, nFactors, mFactors] using h31u.le
      · simpa [← n_factorization, nFactors, mFactors] using h37u.le
      · simpa [← n_factorization, nFactors, mFactors] using h41u.le
      · simpa [← n_factorization, nFactors, mFactors] using h43u.le
    · rw [Nat.factorization_eq_zero_of_not_dvd hpn]
      have hp47 : 47 ≤ p := by
        by_contra hnot
        have hlt : p < 47 := by omega
        interval_cases p <;> norm_num at hp
        all_goals norm_num at hpn
      simpa using golden_layer_marginal_one_threshold_of_le hp (by norm_num) hp47 h47u.le
  have hnLower : ∀ p : ℕ, p.Prime → p ∣ 791245405339403414400 →
      goldenLayerMarginal 2 7 ≤
        goldenLayerMarginal p ((791245405339403414400 : ℕ).factorization p) := by
    intro p hp hpn
    rcases prime_dvd_n_cases hp hpn with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [← n_factorization, nFactors, mFactors] using h2nl
    · simpa [← n_factorization, nFactors, mFactors] using h3l.le
    · simpa [← n_factorization, nFactors, mFactors] using h5l.le
    · simpa [← n_factorization, nFactors, mFactors] using h7l.le
    · simpa [← n_factorization, nFactors, mFactors] using h11l.le
    · simpa [← n_factorization, nFactors, mFactors] using h13l.le
    · simpa [← n_factorization, nFactors, mFactors] using h17l.le
    · simpa [← n_factorization, nFactors, mFactors] using h19l.le
    · simpa [← n_factorization, nFactors, mFactors] using h23l.le
    · simpa [← n_factorization, nFactors, mFactors] using h29l.le
    · simpa [← n_factorization, nFactors, mFactors] using h31l.le
    · simpa [← n_factorization, nFactors, mFactors] using h37l.le
    · simpa [← n_factorization, nFactors, mFactors] using h41l.le
    · simpa [← n_factorization, nFactors, mFactors] using h43l.le
  exact ⟨hmUpper, hnUpper, hnLower⟩

/-- The doubled witness has a nonempty price window whose lower endpoint is the
upper endpoint of the first witness. -/
theorem n_price_window_and_shared_endpoint :
    goldenUpperPrice 791245405339403414400 ≤
        goldenLowerPrice 791245405339403414400 ∧
      goldenLowerPrice 791245405339403414400 =
        goldenUpperPrice 395622702669701707200 := by
  rcases n_thresholds_and_m_upper with ⟨hmUpper, hnUpper, hnLower⟩
  have hrefPos : 0 < goldenLayerMarginal 2 7 := by
    norm_num [goldenLayerMarginal]
    positivity
  have hnCA : IsColossallyAbundant 791245405339403414400 :=
    ⟨goldenLayerMarginal 2 7, hrefPos,
      (golden_resource_optimal_iff_layer_thresholds hrefPos (by norm_num)).mpr
        ⟨hnUpper, hnLower⟩⟩
  refine ⟨(colossally_abundant_iff_price_interval_nonempty (by norm_num)).mp hnCA, ?_⟩
  have hnLowerEq : goldenLowerPrice 791245405339403414400 =
      goldenLayerMarginal 2 7 := by
    have hs : (791245405339403414400 : ℕ).primeFactors.Nonempty := by simp
    rw [goldenLowerPrice, dif_pos hs]
    apply le_antisymm
    · have hmem : 2 ∈ (791245405339403414400 : ℕ).primeFactors :=
        Nat.prime_two.mem_primeFactors (by norm_num) (by norm_num)
      have hle := Finset.inf'_le
        (fun p => goldenLayerMarginal p ((791245405339403414400 : ℕ).factorization p)) hmem
      have hfac2 : (791245405339403414400 : ℕ).factorization 2 = 7 := by
        rw [← n_factorization]
        norm_num [nFactors, mFactors]
      rw [hfac2] at hle
      exact hle
    · apply Finset.le_inf' hs
      intro p hp
      exact hnLower p (Nat.prime_of_mem_primeFactors hp)
        (Nat.dvd_of_mem_primeFactors hp)
  have hmUpperEq : goldenUpperPrice 395622702669701707200 =
      goldenLayerMarginal 2 7 := by
    obtain ⟨p, hp, heq, hall⟩ := golden_upper_price_spec
      (n := 395622702669701707200) (by norm_num)
    apply le_antisymm
    · rw [heq]
      exact hmUpper p hp
    · have h := hall 2 Nat.prime_two
      simpa [← m_factorization, mFactors] using h
  exact hnLowerEq.trans hmUpperEq.symm

private theorem strict_m_lower_and_n_upper :
    (∀ p : ℕ, p.Prime → p ∣ 395622702669701707200 →
      goldenLayerMarginal 2 7 <
        goldenLayerMarginal p ((395622702669701707200 : ℕ).factorization p)) ∧
    (∀ p : ℕ, p.Prime →
      goldenLayerMarginal p ((791245405339403414400 : ℕ).factorization p + 1) <
        goldenLayerMarginal 2 7) := by
  rcases m_price_window_rational_separation with
    ⟨_, ⟨h2l, h3l, h5l, h7l, h11l, h13l, h17l, h19l, h23l, h29l, h31l,
      h37l, h41l, h43l⟩⟩
  rcases n_shared_endpoint_rational_separation with
    ⟨⟨h2u, h3u, h5u, h7u, h11u, h13u, h17u, h19u, h23u, h29u, h31u,
      h37u, h41u, h43u, h47u⟩, _⟩
  constructor
  · intro p hp hpm
    rcases prime_dvd_m_cases hp hpm with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [← m_factorization, mFactors] using h2l
    · simpa [← m_factorization, mFactors] using h3l
    · simpa [← m_factorization, mFactors] using h5l
    · simpa [← m_factorization, mFactors] using h7l
    · simpa [← m_factorization, mFactors] using h11l
    · simpa [← m_factorization, mFactors] using h13l
    · simpa [← m_factorization, mFactors] using h17l
    · simpa [← m_factorization, mFactors] using h19l
    · simpa [← m_factorization, mFactors] using h23l
    · simpa [← m_factorization, mFactors] using h29l
    · simpa [← m_factorization, mFactors] using h31l
    · simpa [← m_factorization, mFactors] using h37l
    · simpa [← m_factorization, mFactors] using h41l
    · simpa [← m_factorization, mFactors] using h43l
  · intro p hp
    by_cases hpn : p ∣ 791245405339403414400
    · rcases prime_dvd_n_cases hp hpn with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · simpa [← n_factorization, nFactors, mFactors] using h2u
      · simpa [← n_factorization, nFactors, mFactors] using h3u
      · simpa [← n_factorization, nFactors, mFactors] using h5u
      · simpa [← n_factorization, nFactors, mFactors] using h7u
      · simpa [← n_factorization, nFactors, mFactors] using h11u
      · simpa [← n_factorization, nFactors, mFactors] using h13u
      · simpa [← n_factorization, nFactors, mFactors] using h17u
      · simpa [← n_factorization, nFactors, mFactors] using h19u
      · simpa [← n_factorization, nFactors, mFactors] using h23u
      · simpa [← n_factorization, nFactors, mFactors] using h29u
      · simpa [← n_factorization, nFactors, mFactors] using h31u
      · simpa [← n_factorization, nFactors, mFactors] using h37u
      · simpa [← n_factorization, nFactors, mFactors] using h41u
      · simpa [← n_factorization, nFactors, mFactors] using h43u
    · rw [Nat.factorization_eq_zero_of_not_dvd hpn]
      have hp47 : 47 ≤ p := by
        by_contra hnot
        have hlt : p < 47 := by omega
        interval_cases p <;> norm_num at hp
        all_goals norm_num at hpn
      rcases hp47.eq_or_lt with rfl | hlt
      · simpa using h47u
      · exact (golden_layer_marginal_one_strictAnti (by norm_num) hp hlt).trans h47u

private theorem critical_price_optimizer_trichotomy
    {k : ℕ} (hk : 1 ≤ k) {mu : ℝ} (hmu : 0 < mu)
    (hopt : IsGoldenResourceOptimal mu k) :
    (goldenLayerMarginal 2 7 < mu → k ∣ 395622702669701707200) ∧
    (mu < goldenLayerMarginal 2 7 → 791245405339403414400 ∣ k) ∧
    (mu = goldenLayerMarginal 2 7 →
      395622702669701707200 ∣ k ∧ k ∣ 791245405339403414400) := by
  rcases n_thresholds_and_m_upper with ⟨hmUpper, _, hnLower⟩
  rcases strict_m_lower_and_n_upper with ⟨hmLowerStrict, hnUpperStrict⟩
  rcases (golden_resource_optimal_iff_layer_thresholds hmu hk).mp hopt with
    ⟨hkUpper, hkLower⟩
  have hk0 : k ≠ 0 := by omega
  constructor
  · intro hrefMu
    apply (Nat.factorization_le_iff_dvd hk0 (by norm_num)).mp
    intro p
    by_cases hp : p.Prime
    · by_contra hnot
      have hlt : (395622702669701707200 : ℕ).factorization p < k.factorization p := by
        omega
      have hpdvd : p ∣ k := Nat.dvd_of_factorization_pos (by omega)
      have hmono : goldenLayerMarginal p (k.factorization p) ≤
          goldenLayerMarginal p ((395622702669701707200 : ℕ).factorization p + 1) := by
        have hle : (395622702669701707200 : ℕ).factorization p + 1 ≤
            k.factorization p := by omega
        rcases hle.eq_or_lt with heq | hstrict
        · rw [heq]
        · exact (golden_layer_strict_decrease hp (by omega) hstrict).le
      have hleMu : mu ≤ goldenLayerMarginal 2 7 :=
        (hkLower p hp hpdvd).trans (hmono.trans (hmUpper p hp))
      exact (not_lt_of_ge hleMu) hrefMu
    · simp [Nat.factorization_eq_zero_of_not_prime k hp]
  constructor
  · intro hMuRef
    apply (Nat.factorization_le_iff_dvd (by norm_num) hk0).mp
    intro p
    by_cases hp : p.Prime
    · by_contra hnot
      have hlt : k.factorization p <
          (791245405339403414400 : ℕ).factorization p := by omega
      have hpdvd : p ∣ 791245405339403414400 :=
        Nat.dvd_of_factorization_pos (by omega)
      have hmono :
          goldenLayerMarginal p ((791245405339403414400 : ℕ).factorization p) ≤
            goldenLayerMarginal p (k.factorization p + 1) := by
        have hle : k.factorization p + 1 ≤
            (791245405339403414400 : ℕ).factorization p := by omega
        rcases hle.eq_or_lt with heq | hstrict
        · rw [heq]
        · exact (golden_layer_strict_decrease hp (by omega) hstrict).le
      have hRefMu : goldenLayerMarginal 2 7 ≤ mu :=
        (hnLower p hp hpdvd).trans (hmono.trans (hkUpper p hp))
      exact (not_lt_of_ge hRefMu) hMuRef
    · simp [Nat.factorization_eq_zero_of_not_prime 791245405339403414400 hp]
  · intro hMuEq
    constructor
    · apply (Nat.factorization_le_iff_dvd (by norm_num) hk0).mp
      intro p
      by_cases hp : p.Prime
      · by_contra hnot
        have hlt : k.factorization p <
            (395622702669701707200 : ℕ).factorization p := by omega
        have hpdvd : p ∣ 395622702669701707200 :=
          Nat.dvd_of_factorization_pos (by omega)
        have hmono :
            goldenLayerMarginal p ((395622702669701707200 : ℕ).factorization p) ≤
              goldenLayerMarginal p (k.factorization p + 1) := by
          have hle : k.factorization p + 1 ≤
              (395622702669701707200 : ℕ).factorization p := by omega
          rcases hle.eq_or_lt with heq | hstrict
          · rw [heq]
          · exact (golden_layer_strict_decrease hp (by omega) hstrict).le
        have hRef : goldenLayerMarginal p
            ((395622702669701707200 : ℕ).factorization p) ≤
              goldenLayerMarginal 2 7 := by
          calc
            _ ≤ goldenLayerMarginal p (k.factorization p + 1) := hmono
            _ ≤ mu := hkUpper p hp
            _ = goldenLayerMarginal 2 7 := hMuEq
        exact (not_lt_of_ge hRef) (hmLowerStrict p hp hpdvd)
      · simp [Nat.factorization_eq_zero_of_not_prime 395622702669701707200 hp]
    · apply (Nat.factorization_le_iff_dvd hk0 (by norm_num)).mp
      intro p
      by_cases hp : p.Prime
      · by_contra hnot
        have hlt : (791245405339403414400 : ℕ).factorization p <
            k.factorization p := by omega
        have hpdvd : p ∣ k := Nat.dvd_of_factorization_pos (by omega)
        have hmono : goldenLayerMarginal p (k.factorization p) ≤
            goldenLayerMarginal p
              ((791245405339403414400 : ℕ).factorization p + 1) := by
          have hle : (791245405339403414400 : ℕ).factorization p + 1 ≤
              k.factorization p := by omega
          rcases hle.eq_or_lt with heq | hstrict
          · rw [heq]
          · exact (golden_layer_strict_decrease hp (by omega) hstrict).le
        have hRef : goldenLayerMarginal 2 7 ≤
            goldenLayerMarginal p
              ((791245405339403414400 : ℕ).factorization p + 1) := by
          calc
            _ = mu := hMuEq.symm
            _ ≤ goldenLayerMarginal p (k.factorization p) := hkLower p hp hpdvd
            _ ≤ _ := hmono
        exact (not_le_of_gt (hnUpperStrict p hp)) hRef
      · simp [Nat.factorization_eq_zero_of_not_prime k hp]

/-- No colossally abundant integer lies strictly between the two witnesses. -/
theorem no_colossally_abundant_between :
    ∀ k : ℕ, 395622702669701707200 < k →
      k < 791245405339403414400 → ¬ IsColossallyAbundant k := by
  intro k hmk hkn hkCA
  obtain ⟨mu, hmu, hopt⟩ := hkCA
  rcases critical_price_optimizer_trichotomy (by omega) hmu hopt with
    ⟨habove, hbelow, hequal⟩
  rcases lt_trichotomy (goldenLayerMarginal 2 7) mu with hrefMu | hrefEq | hMuRef
  · have hkdm := habove hrefMu
    have hle := Nat.le_of_dvd (by norm_num) hkdm
    omega
  · rcases hequal hrefEq.symm with ⟨hmdk, hkdn⟩
    obtain ⟨a, rfl⟩ := hmdk
    have ha : a ∣ 2 := by
      apply (Nat.mul_dvd_mul_iff_left (by norm_num :
        0 < (395622702669701707200 : ℕ))).mp
      convert hkdn using 1 <;> norm_num
    rcases (Nat.dvd_prime Nat.prime_two).mp ha with rfl | rfl
    · norm_num at hmk
    · norm_num at hkn
  · have hndk := hbelow hMuRef
    have hle := Nat.le_of_dvd (by omega) hndk
    omega

end

end D5.S3.Arith.GoldenResource.A279609DoublingRefutation
