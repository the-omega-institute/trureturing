/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SingularSeriesTail
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SingularSeriesTail
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform quadratic Euler tails control finite singular series and interval correlation sums. -/

import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.FiniteSieve.FiniteSieveDefs
import D5.S3.Analytic.PrimeProducts.FiniteOffsetSingularSeries
import D5.S3.Factorization.JordanCototientRecordLimitInfinity
import D5.S3.PrimeGaps.EulerProducts
import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.FormalIntervalMomentBounds

/-! Quantitative truncation of offset Euler products and centered interval correlations. -/

open scoped BigOperators Topology
open Set Filter

namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer

noncomputable section
set_option autoImplicit false

open D5.S3.Analytic.PrimeProducts.FiniteLocalResidueBlockingCriterion
open D5.S3.Analytic.PrimeProducts.FiniteOffsetSingularSeries

private lemma finite_factor_nonneg (H : Finset Int) (p : Nat.Primes) :
    0 ≤ (1 - (localResidueCount H p.val : ℝ) / p.val) /
      (1 - 1 / (p.val : ℝ)) ^ H.card := by
  have hp : (0 : ℝ) < p.val := by exact_mod_cast p.property.pos
  have hle : (localResidueCount H p.val : ℝ) ≤ p.val := by
    let : NeZero p.val := ⟨p.property.ne_zero⟩
    exact_mod_cast (show localResidueCount H p.val ≤ p.val by
      simpa only [localResidueCount, ZMod.card] using (localResidueSet H p.val).card_le_univ)
  have hden : 0 < (1 - 1 / (p.val : ℝ)) ^ H.card := by
    have hp1 : (1 : ℝ) < p.val := by exact_mod_cast p.property.one_lt
    exact pow_pos (sub_pos.mpr ((div_lt_one hp).mpr hp1)) _
  exact div_nonneg (sub_nonneg.mpr (by exact (div_le_one hp).2 hle)) hden.le

private lemma finite_factor_le_inv (H : Finset Int) (p : Nat.Primes) :
    (1 - (localResidueCount H p.val : ℝ) / p.val) /
      (1 - 1 / (p.val : ℝ)) ^ H.card ≤
      (1 / (1 - 1 / (p.val : ℝ))) ^ H.card := by
  have hp : (0 : ℝ) < p.val := by exact_mod_cast p.property.pos
  have hp1 : (1 : ℝ) < p.val := by exact_mod_cast p.property.one_lt
  have hden : 0 < (1 - 1 / (p.val : ℝ)) ^ H.card := by
    exact pow_pos (sub_pos.mpr ((div_lt_one hp).mpr hp1)) _
  have hnum : 1 - (localResidueCount H p.val : ℝ) / p.val ≤ 1 := by
    have hnonneg : 0 ≤ (localResidueCount H p.val : ℝ) / p.val :=
      div_nonneg (Nat.cast_nonneg _) hp.le
    linarith
  calc
    _ ≤ 1 / (1 - 1 / (p.val : ℝ)) ^ H.card := div_le_div_of_nonneg_right hnum hden.le
    _ ≤ _ := by
      simp only [one_div, inv_pow]
      rfl

private theorem finite_singular_series_nonneg (y : ℕ) (D : Finset ℕ) :
    0 ≤ finiteSingularSeries y D := by
  classical
  have hcard : (D.image (fun d : ℕ => (d : ℤ))).card = D.card :=
    Finset.card_image_of_injective _ Int.ofNat_injective
  unfold finiteSingularSeries
  apply Finset.prod_nonneg
  intro p hp
  simpa only [hcard] using
    finite_factor_nonneg (D.image (fun d : ℕ => (d : ℤ))) ⟨p, Nat.prime_of_mem_primesLE hp⟩

private theorem finite_singular_series_le_denominator_product (y : ℕ) (D : Finset ℕ) :
    finiteSingularSeries y D ≤
      ∏ p ∈ y.primesLE, (1 / (1 - 1 / (p : ℝ))) ^ D.card := by
  classical
  have hcard : (D.image (fun d : ℕ => (d : ℤ))).card = D.card :=
    Finset.card_image_of_injective _ Int.ofNat_injective
  unfold finiteSingularSeries
  apply Finset.prod_le_prod₀
  · intro p hp
    simpa only [hcard] using
      finite_factor_nonneg (D.image (fun d : ℕ => (d : ℤ))) ⟨p, Nat.prime_of_mem_primesLE hp⟩
  · intro p hp
    simpa only [hcard] using
      finite_factor_le_inv (D.image (fun d : ℕ => (d : ℤ))) ⟨p, Nat.prime_of_mem_primesLE hp⟩

theorem primorial_ratio_eq_denominator_product (y : ℕ) :
    sieveDensity ⟨primorial y, primorial_pos y⟩ =
      ∏ p ∈ y.primesLE, (1 / (1 - 1 / (p : ℝ))) := by
  have ht : (Nat.totient (primorial y) : ℝ) =
      (primorial y : ℝ) * ∏ p ∈ y.primesLE, (1 - 1 / (p : ℝ)) := by
    have h := congrArg (fun q : ℚ => (q : ℝ))
      (Nat.totient_eq_mul_prod_factors (primorial y))
    push_cast at h
    simpa only [primeFactors_primorial, one_div] using h
  change (primorial y : ℝ) / (Nat.totient (primorial y) : ℝ) = _
  rw [ht, div_mul_eq_div_mul_one_div,
    div_self (by exact_mod_cast (primorial_pos y).ne'), one_mul]
  simp only [one_div, Finset.prod_inv_distrib]

private theorem finite_singular_series_le_density_pow (y : ℕ) (D : Finset ℕ) :
    finiteSingularSeries y D ≤ sieveDensity ⟨primorial y, primorial_pos y⟩ ^ D.card := by
  calc
    finiteSingularSeries y D ≤ ∏ p ∈ y.primesLE, (1 / (1 - 1 / (p : ℝ))) ^ D.card :=
      finite_singular_series_le_denominator_product y D
    _ = (∏ p ∈ y.primesLE, (1 / (1 - 1 / (p : ℝ)))) ^ D.card := by
      rw [← Finset.prod_pow]
    _ = sieveDensity ⟨primorial y, primorial_pos y⟩ ^ D.card := by
      rw [primorial_ratio_eq_denominator_product]

private theorem center_sub_center_expansion (y : ℕ) (D : Finset ℕ) :
    center concreteSS D - center (finiteSingularSeries y) D =
      ∑ J ∈ D.powerset, (-1 : ℝ) ^ (D.card - J.card) *
        (concreteSS J - finiteSingularSeries y J) := by
  classical
  simp only [center, centerFinite]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]

private lemma scalar_factor_bounds (k : ℕ) (hk : k ≤ 4) (x : ℝ)
    (hx : 0 ≤ x) (hx8 : x ≤ 1 / 8) :
    0 ≤ (1 - k * x) / (1 - x) ^ k ∧
    (1 - k * x) / (1 - x) ^ k ≤ 1 ∧
    |(1 - k * x) / (1 - x) ^ k - 1| ≤ 256 * x ^ 2 := by
  have hx1 : x ≤ 1 := by linarith
  have hbase : 0 < 1 - x := by linarith
  have hden : 0 < (1 - x) ^ k := pow_pos hbase _
  have hdenlower : (1 / 16 : ℝ) ≤ (1 - x) ^ k := by
    calc
      (1 / 16 : ℝ) = (1 / 2 : ℝ) ^ 4 := by norm_num
      _ ≤ (1 / 2 : ℝ) ^ k := pow_le_pow_of_le_one (by norm_num) (by norm_num) hk
      _ ≤ (1 - x) ^ k := pow_le_pow_left₀ (by norm_num) (by linarith) _
  have hkR : (k : ℝ) ≤ 4 := by exact_mod_cast hk
  have hnum : 0 ≤ 1 - k * x := by
    nlinarith only [mul_le_mul_of_nonneg_right hkR hx, hx8]
  have hbern := one_add_mul_le_pow (R := ℝ) (a := -x) (by linarith) k
  simp only [mul_neg, ← sub_eq_add_neg] at hbern
  have hle : (1 - k * x) / (1 - x) ^ k ≤ 1 := (div_le_one hden).2 hbern
  refine ⟨div_nonneg hnum hden.le, hle, ?_⟩
  rw [abs_of_nonpos (sub_nonpos.mpr hle), neg_sub, one_sub_div hden.ne']
  apply (div_le_iff₀ hden).2
  have hrem : (1 - x) ^ k - (1 - k * x) ≤ 16 * x ^ 2 := by
    have h := binomial_remainder_le x hx hx1 k
    have hk2 : (k : ℝ) ^ 2 ≤ 16 := by nlinarith only [hkR, (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    exact h.trans (mul_le_mul_of_nonneg_right hk2 (sq_nonneg x))
  have hmul := mul_le_mul_of_nonneg_left hdenlower (show 0 ≤ 256 * x ^ 2 by positivity)
  nlinarith only [hrem, hmul]

private lemma large_prime_residue_count (y : ℕ) (D : Finset ℕ)
    (hdiam : ∀ d ∈ D, ∀ e ∈ D, Nat.dist d e ≤ y)
    (p : Nat.Primes) (hp : y < p.val) :
    localResidueCount (D.image (fun d : ℕ => (d : ℤ))) p.val = D.card := by
  classical
  rw [local_residue_count_eq_card_of_diameter_lt _ y p.val ?_ hp]
  · exact Finset.card_image_of_injective _ Int.ofNat_injective
  · intro a ha b hb
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hb
    have hdist : ((e : ℤ) - d).natAbs = Nat.dist d e := by
      rcases le_total d e with h | h
      · rw [Int.natAbs_natCast_sub_natCast_of_ge h, Nat.dist_eq_sub_of_le h]
      · rw [Int.natAbs_natCast_sub_natCast_of_le h, Nat.dist_eq_sub_of_le_right h]
    rw [hdist]
    exact hdiam d hd e he

private lemma large_prime_factor_bounds (y : ℕ) (hy : 8 ≤ y) (D : Finset ℕ)
    (hcard : D.card ≤ 4) (hdiam : ∀ d ∈ D, ∀ e ∈ D, Nat.dist d e ≤ y)
    (p : Nat.Primes) (hp : y < p.val) :
    let f := D5.S3.Analytic.PrimeProducts.FiniteOffsetSingularSeries.offsetLocalFactor
      (D.image (fun d : ℕ => (d : ℤ))) p
    0 ≤ f ∧ f ≤ 1 ∧ |f - 1| ≤ 256 / (p.val : ℝ) ^ 2 := by
  have hp8 : (8 : ℝ) ≤ p.val := by exact_mod_cast (hy.trans hp.le)
  have h := scalar_factor_bounds D.card hcard (1 / p.val) (by positivity)
    (one_div_le_one_div_of_le (by norm_num) hp8)
  have hDcard : (D.image (fun d : ℕ => (d : ℤ))).card = D.card :=
    Finset.card_image_of_injective _ Int.ofNat_injective
  dsimp only
  rw [D5.S3.Analytic.PrimeProducts.FiniteOffsetSingularSeries.offsetLocalFactor,
    large_prime_residue_count y D hdiam p hp, hDcard]
  simpa only [div_eq_mul_inv, one_mul, mul_pow, one_div, inv_pow] using h

private lemma finite_prime_square_tail (y : ℕ) (hy : y ≠ 0)
    (s : Finset Nat.Primes) (hs : ∀ p ∈ s, y < p.val) :
    (∑ p ∈ s, 1 / (p.val : ℝ) ^ 2) ≤ 1 / (y : ℝ) := by
  classical
  let ns := s.image (fun p : Nat.Primes => p.val)
  calc
    _ = ∑ n ∈ ns, 1 / (n : ℝ) ^ 2 :=
      (Finset.sum_image Subtype.val_injective.injOn).symm
    _ ≤ ∑ n ∈ Finset.Ioc y (max y (ns.sup id)), 1 / (n : ℝ) ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro n hn
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hn
        exact Finset.mem_Ioc.mpr ⟨hs p hp,
          (Finset.le_sup (f := id) (Finset.mem_image.mpr ⟨p, hp, rfl⟩)).trans
            (le_max_right _ _)⟩
      · intro n _ _
        positivity
    _ ≤ 1 / (y : ℝ) - 1 / ((max y (ns.sup id) : ℕ) : ℝ) := by
      simpa only [one_div] using
        (sum_Ioc_inv_sq_le_sub (α := ℝ) hy (le_max_left y (ns.sup id)))
    _ ≤ _ := sub_le_self _ (by positivity)

set_option backward.isDefEq.respectTransparency false in
private lemma offset_tail_product (y : ℕ) (hy : 8 ≤ y) (D : Finset ℕ)
    (hcard : D.card ≤ 4) (hdiam : ∀ d ∈ D, ∀ e ∈ D, Nat.dist d e ≤ y) :
    ∃ T : ℝ,
      HasProd (fun p : {p : Nat.Primes // y < p.val} =>
        offsetLocalFactor (D.image (fun d : ℕ => (d : ℤ))) p.val) T ∧
      concreteSS D = finiteSingularSeries y D * T ∧ |T - 1| ≤ 256 / (y : ℝ) := by
  classical
  let f := offsetLocalFactor (D.image (fun d : ℕ => (d : ℤ)))
  let I := {p : Nat.Primes // y < p.val}
  let : LinearOrder Nat.Primes := inferInstanceAs (LinearOrder {p : ℕ // p.Prime})
  let : LinearOrder I := inferInstanceAs (LinearOrder {p : Nat.Primes // y < p.val})
  have hb (p : I) := large_prime_factor_bounds y hy D hcard hdiam p.val p.property
  have hsum (s : Finset I) : (∑ p ∈ s, |f p.val - 1|) ≤ 256 / (y : ℝ) := by
    calc
      _ ≤ ∑ p ∈ s, 256 / (p.val.val : ℝ) ^ 2 :=
        Finset.sum_le_sum (fun p _ => (hb p).2.2)
      _ = 256 * ∑ p ∈ s.image Subtype.val, 1 / (p.val : ℝ) ^ 2 := by
        rw [Finset.mul_sum, Finset.sum_image Subtype.val_injective.injOn]
        apply Finset.sum_congr rfl
        intro p _
        ring
      _ ≤ 256 * (1 / (y : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply finite_prime_square_tail y (by omega)
        intro p hp
        obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hp
        exact q.property
      _ = _ := by ring
  have hm : Multipliable (fun p : I => f p.val) :=
    D5.S3.Analytic.PrimeProducts.FormalFactorTableCounterexamples.absolute_convergence_admission_gives_multipliable
      _ (summable_of_sum_le (fun p => abs_nonneg _) hsum)
  refine ⟨∏' p : I, f p.val, hm.hasProd, ?_, ?_⟩
  · let s : Finset Nat.Primes := y.primesLE.subtype Nat.Prime
    have hs : (s : Set Nat.Primes) = {p | p.val ≤ y} := by
      ext p
      change p ∈ y.primesLE.subtype Nat.Prime ↔ p.val ≤ y
      rw [Finset.mem_subtype, Nat.mem_primesLE]
      exact and_iff_left p.property
    have hscard : (D.image (fun d : ℕ => (d : ℤ))).card = D.card :=
      Finset.card_image_of_injective _ Int.ofNat_injective
    have hfinite : (∏ p ∈ s, f p) = finiteSingularSeries y D := by
      dsimp [f, offsetLocalFactor, finiteSingularSeries, s]
      rw [hscard]
      exact Finset.prod_subtype_of_mem (s := y.primesLE)
        (fun p : ℕ => (1 - (localResidueCount (D.image (fun d : ℕ => (d : ℤ))) p : ℝ) / p) /
          (1 - 1 / (p : ℝ)) ^ D.card) (fun p hp => Nat.prime_of_mem_primesLE hp)
    have hsmall := s.hasProd f
    rw [hfinite, hs] at hsmall
    have htail : HasProd (f ∘ (↑) : ↥(({p : Nat.Primes | p.val ≤ y} : Set Nat.Primes)ᶜ) → ℝ)
        (∏' p : I, f p.val) := by
      have heq : ({p : Nat.Primes | p.val ≤ y} : Set Nat.Primes)ᶜ =
          {p : Nat.Primes | y < p.val} := by
        ext p
        change (¬ p.val ≤ y) ↔ y < p.val
        exact not_le
      rw [heq]
      exact hm.hasProd
    exact ((hsmall.mul_compl htail).unique
      (finite_offset_blocking_and_singular_series _ _ rfl).2.2).symm
  · apply le_of_tendsto' ((hm.hasProd.sub_const 1).abs)
    intro s
    have hle : ∏ p ∈ s, f p.val ≤ 1 :=
      Finset.prod_le_one₀ (fun p _ => (hb p).1) (fun p _ => (hb p).2.1)
    rw [abs_of_nonpos (sub_nonpos.mpr hle), neg_sub]
    have hg := D5.S3.Factorization.JordanCototientRecordLimitInfinity.one_sub_prod_le_sum
      s (fun p => 1 - f p.val)
      (fun p _ => sub_nonneg.mpr (hb p).2.1)
      (fun p _ => sub_le_self _ (hb p).1)
    simp only [sub_sub_cancel] at hg
    calc
      _ ≤ ∑ p ∈ s, (1 - f p.val) := hg
      _ = ∑ p ∈ s, |f p.val - 1| := by
        apply Finset.sum_congr rfl
        intro p _
        rw [abs_of_nonpos (sub_nonpos.mpr (hb p).2.1), neg_sub]
      _ ≤ _ := hsum s

/-- The full Euler product differs from its finite part by a uniform relative tail. -/
private theorem singular_series_tail_bound (y : ℕ) (hy : 8 ≤ y) (D : Finset ℕ)
    (hcard : D.card ≤ 4) (hdiam : ∀ d ∈ D, ∀ e ∈ D, Nat.dist d e ≤ y) :
    |concreteSS D - finiteSingularSeries y D| ≤ 256 * finiteSingularSeries y D / (y : ℝ) := by
  obtain ⟨T, _, hT, hb⟩ := offset_tail_product y hy D hcard hdiam
  rw [hT, show finiteSingularSeries y D * T - finiteSingularSeries y D = finiteSingularSeries y D * (T - 1) by ring,
    abs_mul, abs_of_nonneg (finite_singular_series_nonneg y D)]
  calc
    _ ≤ finiteSingularSeries y D * (256 / (y : ℝ)) :=
      mul_le_mul_of_nonneg_left hb (finite_singular_series_nonneg y D)
    _ = _ := by ring

/-- Inclusion–exclusion transfers the Euler tail to centered series of at most four shifts. -/
private theorem centered_singular_series_tail_bound (y : ℕ) (hy : 8 ≤ y) (D : Finset ℕ)
    (hcard : D.card ≤ 4) (hdiam : ∀ d ∈ D, ∀ e ∈ D, Nat.dist d e ≤ y) :
    |center concreteSS D - center (finiteSingularSeries y) D| ≤
      4096 * sieveDensity ⟨primorial y, primorial_pos y⟩ ^ 4 / (y : ℝ) := by
  classical
  have hphi : (0 : ℝ) < Nat.totient (primorial y) := by
    exact_mod_cast (Nat.totient_pos.mpr (primorial_pos y))
  have hP : 1 ≤ sieveDensity ⟨primorial y, primorial_pos y⟩ := by
    change 1 ≤ (primorial y : ℝ) / (Nat.totient (primorial y) : ℝ)
    exact (one_le_div₀ hphi).2 (by exact_mod_cast Nat.totient_le (primorial y))
  have hterm (J : Finset ℕ) (hJ : J ∈ D.powerset) :
      |concreteSS J - finiteSingularSeries y J| ≤
        256 * sieveDensity ⟨primorial y, primorial_pos y⟩ ^ 4 / (y : ℝ) := by
    have hsub := Finset.mem_powerset.mp hJ
    have hJcard := (Finset.card_le_card hsub).trans hcard
    calc
      _ ≤ 256 * finiteSingularSeries y J / (y : ℝ) := singular_series_tail_bound y hy J hJcard
        (fun d hd e he => hdiam d (hsub hd) e (hsub he))
      _ ≤ _ := by
        gcongr
        exact (finite_singular_series_le_density_pow y J).trans (pow_le_pow_right₀ hP hJcard)
  rw [center_sub_center_expansion]
  calc
    _ ≤ ∑ J ∈ D.powerset,
        |(-1 : ℝ) ^ (D.card - J.card) * (concreteSS J - finiteSingularSeries y J)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _J ∈ D.powerset,
        256 * sieveDensity ⟨primorial y, primorial_pos y⟩ ^ 4 / (y : ℝ) := by
      apply Finset.sum_le_sum
      intro J hJ
      simpa only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul] using hterm J hJ
    _ = (2 : ℝ) ^ D.card * (256 * sieveDensity ⟨primorial y, primorial_pos y⟩ ^ 4 / (y : ℝ)) := by
      simp only [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul,
        Nat.cast_pow, Nat.cast_ofNat]
    _ ≤ (2 : ℝ) ^ 4 * (256 * sieveDensity ⟨primorial y, primorial_pos y⟩ ^ 4 / (y : ℝ)) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hcard) (by positivity)
    _ = _ := by norm_num; ring

private lemma cutoff_tail_bounds (M H : ℝ) (hM : 1 ≤ M) (hH : 2 ≤ H) :
    8 ≤ sieveCutoff M H ∧ ⌊M * H⌋₊ ≤ sieveCutoff M H ∧
      1 / (sieveCutoff M H : ℝ) ≤ 2 / (((M + 5) * H) ^ 10) := by
  have hH0 : 0 ≤ H := by linarith
  have ht : 12 ≤ (M + 5) * H := by
    nlinarith only [mul_le_mul_of_nonneg_right hM hH0, hH]
  have hpow : (M + 5) * H ≤ ((M + 5) * H) ^ 10 :=
    le_self_pow₀ (by linarith) (by norm_num)
  have h8 : 8 ≤ sieveCutoff M H := Nat.le_floor (by
    norm_num
    linarith only [ht, hpow])
  have hy : (0 : ℝ) < sieveCutoff M H := by exact_mod_cast (by omega : 0 < sieveCutoff M H)
  have hf : ((M + 5) * H) ^ 10 < (sieveCutoff M H : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  refine ⟨h8, Nat.floor_mono (by linarith only [hpow, hH]), ?_⟩
  apply (div_le_div_iff₀ hy (pow_pos (by linarith only [ht]) 10)).2
  have hy1 : (1 : ℝ) ≤ sieveCutoff M H := by exact_mod_cast (by omega : 1 ≤ sieveCutoff M H)
  linarith only [hf, hy1]

lemma density_log_bound (M : ℝ) (hM : 1 ≤ M) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ H : ℝ, 2 ≤ H → sieveDensity (primorialSieveModulus M H) ≤ B * Real.log H := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hM5 : 0 < M + 5 := by linarith
  have hlogM : 0 ≤ Real.log (M + 5) := Real.log_nonneg (by linarith)
  let B := Real.exp 6 * ((1 + 10 * Real.log (M + 5)) / Real.log 2 + 10)
  refine ⟨B, by dsimp [B]; positivity, ?_⟩
  intro H hH
  have hHpos : 0 < H := by linarith
  have hL : Real.log 2 ≤ Real.log H := Real.log_le_log (by norm_num) hH
  have hy := (cutoff_tail_bounds M H hM hH).1
  have hypos : (0 : ℝ) < sieveCutoff M H := by exact_mod_cast (by omega : 0 < sieveCutoff M H)
  have heuler : sieveDensity (primorialSieveModulus M H) = LongGapsBetweenPrimes.eulerProduct (sieveCutoff M H) 1 := by
    unfold primorialSieveModulus
    rw [primorial_ratio_eq_denominator_product]
    simp only [LongGapsBetweenPrimes.eulerProduct, Real.rpow_neg_one, one_div]
  have hlog : Real.log (sieveCutoff M H) ≤ 10 * (Real.log (M + 5) + Real.log H) := by
    calc
      _ ≤ Real.log (((M + 5) * H) ^ 10) :=
        Real.log_le_log hypos (Nat.floor_le (by positivity))
      _ = _ := by rw [Real.log_pow, Real.log_mul hM5.ne' hHpos.ne']; norm_num
  have hcoef : 1 + 10 * Real.log (M + 5) ≤
      ((1 + 10 * Real.log (M + 5)) / Real.log 2) * Real.log H := by
    have ht := mul_le_mul_of_nonneg_left hL
      (div_nonneg (by positivity : 0 ≤ 1 + 10 * Real.log (M + 5)) hlog2.le)
    rwa [div_mul_cancel₀ _ hlog2.ne'] at ht
  calc
    _ ≤ Real.exp 6 * (1 + Real.log (sieveCutoff M H)) :=
      by rw [heuler]; exact LongGapsBetweenPrimes.eulerProduct_one_le (by omega)
    _ ≤ Real.exp 6 * (1 + 10 * (Real.log (M + 5) + Real.log H)) := by gcongr
    _ = Real.exp 6 * ((1 + 10 * Real.log (M + 5)) + 10 * Real.log H) := by ring
    _ ≤ Real.exp 6 *
        (((1 + 10 * Real.log (M + 5)) / Real.log 2) * Real.log H + 10 * Real.log H) :=
      mul_le_mul_of_nonneg_left (add_le_add hcoef le_rfl) (Real.exp_nonneg _)
    _ = B * Real.log H := by dsimp [B]; ring

/-- Summing the centered Euler tail over all distinct shift tuples is uniform in endpoints. -/
theorem correlation_tail_bound (M : ℝ) (hM : 1 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, 1 ≤ k → k ≤ 4 → ∀ H : ℝ, 2 ≤ H →
      ∀ a b : Fin k → ℝ, admissible M a b →
        |corr concreteSS H a b - corr (finiteSingularSeries (sieveCutoff M H)) H a b| ≤
          C * H ^ k * Real.log H ^ 4 / (((M + 5) * H) ^ 10) := by
  classical
  obtain ⟨B, hB0, hB⟩ := density_log_bound M hM
  refine ⟨8192 * M ^ 4 * B ^ 4, by positivity, ?_⟩
  intro k _hk1 hk4 H hH a b hab
  have hH0 : 0 ≤ H := by linarith
  have hM0 : 0 ≤ M := by linarith
  have hL0 : 0 ≤ Real.log H := Real.log_nonneg (by linarith)
  have hc := cutoff_tail_bounds M H hM hH
  have hP0 : 0 ≤ sieveDensity (primorialSieveModulus M H) := by unfold sieveDensity; positivity
  let S := (Fintype.piFinset (fun i => points H (a i) (b i))).filter Function.Injective
  have hcardS : (S.card : ℝ) ≤ M ^ 4 * H ^ k := by
    calc
      _ ≤ ((Fintype.piFinset (fun i => points H (a i) (b i))).card : ℝ) := by
        exact_mod_cast Finset.card_filter_le
          (Fintype.piFinset (fun i => points H (a i) (b i))) Function.Injective
      _ = ∏ i : Fin k, ((points H (a i) (b i)).card : ℝ) := by simp
      _ ≤ ∏ _i : Fin k, M * H := by
        apply Finset.prod_le_prod₀ (fun i _ => Nat.cast_nonneg _)
        intro i _
        exact geom_points_card_le M H (a i) (b i) hH0 (hab i).1 (hab i).2.1 (hab i).2.2
      _ = M ^ k * H ^ k := by simp [mul_pow]
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hM hk4) (pow_nonneg hH0 _)
  have hterm (d : Fin k → ℕ) (hd : d ∈ S) :
      |center concreteSS (Finset.univ.image d) -
        center (finiteSingularSeries (sieveCutoff M H)) (Finset.univ.image d)| ≤
          4096 * sieveDensity (primorialSieveModulus M H) ^ 4 / (sieveCutoff M H : ℝ) := by
    have hvals (i : Fin k) : d i ≤ ⌊M * H⌋₊ :=
      Finset.mem_Iic.mp (interval_points_subset hH0 (hab i).2.2
        ((Fintype.mem_piFinset.mp (Finset.mem_filter.mp hd).1) i))
    apply centered_singular_series_tail_bound _ hc.1
    · exact Finset.card_image_le.trans (by simpa using hk4)
    · intro u hu v hv
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hu
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hv
      rw [Nat.dist_eq_max_sub_min]
      exact (Nat.sub_le _ _).trans ((max_le (hvals i) (hvals j)).trans hc.2.1)
  unfold corr
  rw [← Finset.sum_sub_distrib]
  change |∑ d ∈ S, (center concreteSS (Finset.univ.image d) -
    center (finiteSingularSeries (sieveCutoff M H)) (Finset.univ.image d))| ≤ _
  calc
    _ ≤ ∑ d ∈ S, |center concreteSS (Finset.univ.image d) -
        center (finiteSingularSeries (sieveCutoff M H)) (Finset.univ.image d)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ S, 4096 * sieveDensity (primorialSieveModulus M H) ^ 4 / (sieveCutoff M H : ℝ) :=
      Finset.sum_le_sum hterm
    _ = (S.card : ℝ) * 4096 * sieveDensity (primorialSieveModulus M H) ^ 4 * (1 / (sieveCutoff M H : ℝ)) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ (M ^ 4 * H ^ k) * 4096 * (B * Real.log H) ^ 4 *
        (2 / (((M + 5) * H) ^ 10)) := by
      apply mul_le_mul _ hc.2.2 (by positivity) (by positivity)
      gcongr
      exact hB H hH
    _ = _ := by ring

set_option backward.isDefEq.respectTransparency false in
private lemma ss_shift (D : Finset ℕ) (t : ℕ) :
    concreteSS (D.image (fun n => n + t)) = concreteSS D := by
  classical
  unfold concreteSS offsetSingularSeries
  apply tprod_congr
  intro p
  unfold offsetLocalFactor
  have hc : ((D.image (fun n => n + t)).image (fun n : ℕ => (n : ℤ))).card =
      (D.image (fun n : ℕ => (n : ℤ))).card := by
    calc
      _ = (D.image (fun n => n + t)).card := Finset.card_image_of_injective _ Int.ofNat_injective
      _ = D.card := Finset.card_image_of_injective _ (add_left_injective t)
      _ = _ := (Finset.card_image_of_injective _ Int.ofNat_injective).symm
  rw [hc]
  have hr : localResidueCount ((D.image (fun n => n + t)).image (fun n : ℕ => (n : ℤ))) p.val =
      localResidueCount (D.image (fun n : ℕ => (n : ℤ))) p.val := by
    unfold localResidueCount localResidueSet
    simp only [Finset.image_image, Function.comp_def, Int.cast_natCast]
    change (D.image (fun n : ℕ => -((n + t : ℕ) : ZMod p.val))).card =
      (D.image (fun n : ℕ => -(n : ZMod p.val))).card
    have heq : D.image (fun n : ℕ => -((n + t : ℕ) : ZMod p.val)) =
        (D.image (fun n : ℕ => -(n : ZMod p.val))).image (fun r => r - (t : ZMod p.val)) := by
      rw [Finset.image_image]
      congr 1
      funext n
      simp [Nat.cast_add, sub_eq_add_neg, add_comm]
    rw [heq]
    exact Finset.card_image_of_injective _ (show Function.Injective
      (fun r : ZMod p.val => r - (t : ZMod p.val)) from fun a b h => sub_left_injective h)
  rw [hr]

private lemma centered_pair_kernel_shift (d e t : ℕ) : centeredPairKernel (d+t) (e+t) = centeredPairKernel d e := by
  classical
  unfold centeredPairKernel
  simp only [add_left_inj]
  split_ifs with h
  · rfl
  · have he : ({d + t, e + t} : Finset ℕ) = ({d,e} : Finset ℕ).image (fun n => n + t) := by simp
    rw [he]
    unfold center
    rw [← centerFinite_image concreteSS (fun n => n + t) (add_left_injective t)]
    simp only [ss_shift]

private lemma second_correlation_eq_interval_sum (H : ℝ) (a b : Fin 2 → ℝ) :
    corr concreteSS H a b = intervalSum centeredPairKernel H (a 0) (b 0) (a 1) (b 1) := by
  classical
  unfold corr intervalSum
  rw [Finset.sum_filter, ← Finset.sum_product']
  apply Finset.sum_bij (fun d _ => (d 0, d 1))
  · intro d hd
    exact Finset.mem_product.mpr ⟨(Fintype.mem_piFinset.mp hd) 0,
      (Fintype.mem_piFinset.mp hd) 1⟩
  · intro d hd e he h
    funext i
    fin_cases i
    · exact congrArg Prod.fst h
    · exact congrArg Prod.snd h
  · intro z hz
    refine ⟨![z.1,z.2], ?_, rfl⟩
    rw [Fintype.mem_piFinset]
    intro i
    fin_cases i
    · exact (Finset.mem_product.mp hz).1
    · exact (Finset.mem_product.mp hz).2
  · intro d hd
    have hi : Function.Injective d ↔ d 0 ≠ d 1 := by
      simp [Function.Injective, Fin.forall_fin_two, ne_comm]
    have himg : Finset.univ.image d = ({d 0, d 1} : Finset ℕ) := by
      simp [Finset.univ_fin2]
    simp only [hi, himg, centeredPairKernel]
    split_ifs <;> simp_all

lemma concrete_interval_covariance (hMS : MSSecond) (M : ℝ) (hM : 1 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ H : ℝ, 1 ≤ H → ∀ a b : Fin 2 → ℝ,
      admissible M a b →
      |corr concreteSS H a b + H * Real.log H * sigma (a 0) (b 0) (a 1) (b 1)| ≤ C * H := by
  obtain ⟨C₀, hC₀, hA⟩ := hMS
  obtain ⟨C, hC, hc⟩ := interval_covariance_bound M hM C₀ hC₀
  refine ⟨C, hC, ?_⟩
  intro H hH a b hab
  rw [second_correlation_eq_interval_sum]
  exact hc centeredPairKernel (by
    intro d e
    unfold centeredPairKernel
    rw [Finset.pair_comm d e]
    by_cases h : d = e <;> simp [h, eq_comm]) centered_pair_kernel_shift hA H hH
    _ _ _ _ (hab 0).1 (hab 0).2.1 (hab 0).2.2 (hab 1).1 (hab 1).2.1 (hab 1).2.2

lemma second_correlation_bound (hMS : MSSecond) (M : ℝ) (hM : 1 ≤ M) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ H : ℝ, 2 ≤ H → ∀ a b : Fin 2 → ℝ,
      admissible M a b → |corr concreteSS H a b| ≤ B * H * Real.log H := by
  obtain ⟨C, hC, hc⟩ := concrete_interval_covariance hMS M hM
  refine ⟨C / Real.log 2 + M, by positivity, ?_⟩
  intro H hH a b hab
  have hL : Real.log 2 ≤ Real.log H := Real.log_le_log (by norm_num) hH
  have hL2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hH0 : 0 ≤ H := by linarith
  have hL0 : 0 ≤ Real.log H := Real.log_nonneg (by linarith)
  have hs := sigma_bound (d := b 1) (by linarith : 0 ≤ M) (hab 0).1 (hab 0).2.2 (hab 1).1
  have he := hc H (by linarith) a b hab
  have hlead : |H * Real.log H * sigma (a 0) (b 0) (a 1) (b 1)| ≤ H * Real.log H * M := by
    rw [abs_of_nonneg (mul_nonneg (mul_nonneg hH0 hL0) hs.1)]
    exact mul_le_mul_of_nonneg_left hs.2 (by positivity)
  have hconst : C * H ≤ (C / Real.log 2) * H * Real.log H := by
    have ht := mul_le_mul_of_nonneg_left hL (div_nonneg hC hL2.le)
    rw [div_mul_cancel₀ _ hL2.ne'] at ht
    nlinarith only [mul_le_mul_of_nonneg_right ht hH0]
  have ht := abs_sub (corr concreteSS H a b + H * Real.log H * sigma (a 0) (b 0) (a 1) (b 1))
    (H * Real.log H * sigma (a 0) (b 0) (a 1) (b 1))
  rw [add_sub_cancel_right] at ht
  calc
    _ ≤ C * H + H * Real.log H * M := ht.trans (add_le_add he hlead)
    _ ≤ _ := by nlinarith only [hconst]
/-- The three products of second correlations have a uniform quantitative Euler tail. -/
theorem pairing_tail_bound (hMS : MSSecond) (M : ℝ) (hM : 1 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ H : ℝ, 2 ≤ H → ∀ a b : Fin 4 → ℝ, admissible M a b →
      |pairCorr concreteSS H a b - finitePairCorrelation M H a b| ≤ C *
        (H ^ 3 * Real.log H ^ 5 / (((M + 5) * H) ^ 10) +
         H ^ 4 * Real.log H ^ 8 / (((M + 5) * H) ^ 20)) := by
  obtain ⟨B, hB, hfull⟩ := second_correlation_bound hMS M hM
  obtain ⟨C, hC, htail⟩ := correlation_tail_bound M hM
  refine ⟨3 * (2 * B * C + C ^ 2), by positivity, ?_⟩
  intro H hH a b hab
  have hH0 : 0 ≤ H := by linarith
  have hL0 : 0 ≤ Real.log H := Real.log_nonneg (by linarith)
  let R (i j : Fin 4) := corr concreteSS H ![a i, a j] ![b i, b j]
  let F (i j : Fin 4) := corr (finiteSingularSeries (sieveCutoff M H)) H ![a i, a j] ![b i, b j]
  let U := B * H * Real.log H
  let sieveExpectation := C * H ^ 2 * Real.log H ^ 4 / (((M + 5) * H) ^ 10)
  let V := H ^ 3 * Real.log H ^ 5 / (((M + 5) * H) ^ 10)
  let W := H ^ 4 * Real.log H ^ 8 / (((M + 5) * H) ^ 20)
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hE : 0 ≤ sieveExpectation := by dsimp [sieveExpectation]; positivity
  have had (i j : Fin 4) : admissible M ![a i, a j] ![b i, b j] := by
    intro r
    fin_cases r
    · exact hab i
    · exact hab j
  have hr (i j : Fin 4) : |R i j| ≤ U := hfull H hH _ _ (had i j)
  have he (i j : Fin 4) : |R i j - F i j| ≤ sieveExpectation :=
    htail 2 (by norm_num) (by norm_num) H hH _ _ (had i j)
  have hp (i j k l : Fin 4) :
      |R i j * R k l - F i j * F k l| ≤ (2 * B * C + C ^ 2) * (V + W) := by
    have hprod : |R i j * R k l - F i j * F k l| ≤
        2 * U * sieveExpectation + sieveExpectation ^ 2 := by
      simpa only [abs_sub_comm, mul_one, one_pow] using
        geom_product_error (F i j) (F k l) (R i j) (R k l) sieveExpectation 1 1 U
          (by norm_num) (by norm_num) hE hU
          (by simpa only [abs_sub_comm, mul_one] using he i j)
          (by simpa only [abs_sub_comm, mul_one] using he k l)
          (by simpa only [mul_one] using hr i j)
          (by simpa only [mul_one] using hr k l)
    calc
      _ ≤ 2 * U * sieveExpectation + sieveExpectation ^ 2 := hprod
      _ = (2 * B * C) * V + C ^ 2 * W := by
        dsimp [sieveExpectation, U, V, W]
        rw [show ((M + 5) * H) ^ 20 = (((M + 5) * H) ^ 10) ^ 2 by rw [← pow_mul]]
        simp only [div_eq_mul_inv, ← inv_pow]
        ring
      _ ≤ (2 * B * C + C ^ 2) * (V + W) := by
        have hV : 0 ≤ V := by dsimp [V]; positivity
        have hW : 0 ≤ W := by dsimp [W]; positivity
        nlinarith only [mul_nonneg (show 0 ≤ 2 * B * C by positivity) hW,
          mul_nonneg (sq_nonneg C) hV]
  change |R 0 1 * R 2 3 + R 0 2 * R 1 3 + R 0 3 * R 1 2 -
    (F 0 1 * F 2 3 + F 0 2 * F 1 3 + F 0 3 * F 1 2)| ≤ _
  calc
    _ = |(R 0 1 * R 2 3 - F 0 1 * F 2 3) + (R 0 2 * R 1 3 - F 0 2 * F 1 3) +
        (R 0 3 * R 1 2 - F 0 3 * F 1 2)| := by congr 1; ring
    _ ≤ |R 0 1 * R 2 3 - F 0 1 * F 2 3| + |R 0 2 * R 1 3 - F 0 2 * F 1 3| +
        |R 0 3 * R 1 2 - F 0 3 * F 1 2| := by
      exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ 3 * (2 * B * C + C ^ 2) * (V + W) := by
      linarith only [hp 0 1 2 3, hp 0 2 1 3, hp 0 3 1 2]
    _ = _ := rfl

end
end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
