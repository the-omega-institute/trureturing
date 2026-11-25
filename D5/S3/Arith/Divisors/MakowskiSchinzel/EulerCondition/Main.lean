/- GID: D5/S3/Arith/Divisors/MakowskiSchinzel/EulerCondition/Main
   generality: G
   mirror-B: D5/B/S3/Arith/Divisors/MakowskiSchinzel/EulerCondition/Main
   mirror-E: none(waiver:unbounded-combinatorial-proof)
   anchors: []
   utility: none
   digest: Euler-product capacities imply the strict sigma-totient inequalities. -/

import D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.SmoothedGroups
import D5.S3.Arith.Divisors.MakowskiSchinzel.Deletion
import D5.S3.Arith.Divisors.MakowskiSchinzel.PrimeDeletion
import D5.S3.Arith.Divisors.MakowskiSchinzel.EulerCondition.Criterion
import D5.S3.PrimeGaps.EulerProducts

/-! Largest-prime grouping and the Euler capacity criterion. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.MakowskiSchinzel.EulerCondition

open Finset

/-- For prime `r`, prime factors whose predecessor has largest prime factor `r`. -/
noncomputable def topGroup (n r : ℕ) : Finset ℕ :=
  (primeSources n r).filter fun q => q - 1 ∈ Nat.smoothNumbers (r + 1)

private theorem nonFermat_predecessor_pos {n q : ℕ} (hq : q ∈ nonFermatFactors n) :
    0 < q - 1 := by
  classical
  have := (Nat.prime_of_mem_primeFactors (mem_filter.mp hq).1).two_le
  omega

private theorem nonFermat_label {n q : ℕ} (hq : q ∈ nonFermatFactors n) :
    (q - 1).maxPrimeFac.Prime ∧ Odd (q - 1).maxPrimeFac := by
  classical
  have hq0 := (nonFermat_predecessor_pos hq).ne'
  have hpow := (mem_filter.mp hq).2.2
  have hq1 : 1 < q - 1 := by
    by_contra hle
    exact hpow ⟨0, by simp; omega⟩
  have hp := Nat.prime_maxPrimeFac_of_one_lt hq1
  refine ⟨hp, hp.odd_of_ne_two ?_⟩
  intro he
  apply hpow
  refine ⟨(q - 1).primeFactorsList.length, Nat.eq_prime_pow_of_unique_prime_dvd hq0 ?_⟩
  intro r hr hrd
  have hle := Nat.le_maxPrimeFac hq0 hr hrd
  rw [he] at hle
  have := hr.two_le
  omega

private theorem topGroup_eq_fiber (n r : ℕ) (hr : r.Prime) (hro : Odd r) :
    topGroup n r = (nonFermatFactors n).filter (fun q => (q - 1).maxPrimeFac = r) := by
  classical
  ext q
  constructor
  · intro hq
    obtain ⟨hsrc, hsm⟩ := mem_filter.mp hq
    have hQ : q ∈ nonFermatFactors n :=
      Certificate.sources_subset_interesting hr.one_lt hro hsrc
    have hq0 := (nonFermat_predecessor_pos hQ).ne'
    have hl := nonFermat_label hQ
    refine mem_filter.mpr ⟨hQ, le_antisymm ?_ ?_⟩
    · have := Nat.mem_smoothNumbers'.mp hsm _ hl.1 Nat.maxPrimeFac_dvd
      omega
    · exact Nat.le_maxPrimeFac hq0 hr (mem_filter.mp hsrc).2
  · intro hq
    obtain ⟨hQ, he⟩ := mem_filter.mp hq
    have hq0 := (nonFermat_predecessor_pos hQ).ne'
    refine mem_filter.mpr ⟨mem_filter.mpr ⟨(mem_filter.mp hQ).1, ?_⟩, ?_⟩
    · rw [← he]
      exact Nat.maxPrimeFac_dvd
    · apply Nat.mem_smoothNumbers'.mpr
      intro p hp hpd
      have := Nat.le_maxPrimeFac hq0 hp hpd
      omega

/-- Labelled group products bounded by the actual odd valuations force `1 ≤ psi n`. -/
theorem one_le_psi_of_labelled_groups (n : ℕ) (label : ℕ → ℕ)
    (hlocal : ∀ q₀ ∈ nonFermatFactors n,
      ∏ q ∈ (nonFermatFactors n).filter (fun q => label q = label q₀),
        (q : ℚ) / (q - 1 : ℕ) ≤
          geom (label q₀) ((oddPredecessorPart n).factorization (label q₀))) :
    1 ≤ psi n := by
  classical
  let Q := nonFermatFactors n
  let U := oddPredecessorPart n
  let S := Q.image label
  have hU0 : U ≠ 0 := (Nat.ordCompl_pos 2
    (prod_pos fun q hq => nonFermat_predecessor_pos hq).ne').ne'
  have hS : S ⊆ U.primeFactors := by
    intro p hp
    obtain ⟨q₀, hq₀, rfl⟩ := mem_image.mp hp
    have hgt : 1 < ∏ q ∈ Q.filter (fun q => label q = label q₀),
        (q : ℚ) / (q - 1 : ℕ) := by
      calc
        1 = ∏ _q ∈ Q.filter (fun q => label q = label q₀), (1 : ℚ) := by simp
        _ < _ := prod_lt_prod_of_nonempty₀ (fun _ _ => by norm_num) (by
          intro q hq
          have hpos := nonFermat_predecessor_pos (mem_filter.mp hq).1
          have hqp := (Nat.prime_of_mem_primeFactors
            (mem_filter.mp (mem_filter.mp hq).1).1).two_le
          apply (one_lt_div (by exact_mod_cast hpos)).mpr
          exact_mod_cast (by omega : q - 1 < q))
          ⟨q₀, mem_filter.mpr ⟨hq₀, rfl⟩⟩
    have he : U.factorization (label q₀) ≠ 0 := by
      intro he
      have hh := hlocal q₀ hq₀
      simp only [show (oddPredecessorPart n).factorization (label q₀) = 0 from he,
        geom, zero_add, sum_range_one, pow_zero] at hh
      exact (not_lt_of_ge hh) hgt
    exact Finsupp.mem_support_iff.mpr he
  have hbound : (∏ q ∈ Q, (q : ℚ) / (q - 1 : ℕ)) ≤ U.abundancyIndex := by
    calc
      _ = ∏ p ∈ S, ∏ q ∈ Q.filter (fun q => label q = p),
          (q : ℚ) / (q - 1 : ℕ) :=
        (prod_fiberwise_of_maps_to (fun q hq => mem_image.mpr ⟨q, hq, rfl⟩) _).symm
      _ ≤ ∏ p ∈ S, geom p (U.factorization p) := by
        apply prod_le_prod₀
        · intro p hp
          exact prod_nonneg fun q hq => by positivity
        · intro p hp
          obtain ⟨q₀, hq₀, rfl⟩ := mem_image.mp hp
          exact hlocal q₀ hq₀
      _ = (∏ p ∈ S, p ^ U.factorization p).abundancyIndex :=
        (SmoothPredecessor.abundancy_prime_power_product S U.factorization
          (fun p hp _ => Nat.prime_of_mem_primeFactors (hS hp))).symm
      _ ≤ U.abundancyIndex := by
        apply Nat.abundancyIndex_le_of_dvd hU0
        have hd := prod_dvd_prod_of_subset S U.primeFactors
          (fun p => p ^ U.factorization p) hS
        exact hd.trans (dvd_of_eq (Nat.prod_primeFactors_pow_factorization hU0).symm)
  have hw0 : 0 ≤ ∏ q ∈ nonFermatFactors n, (1 - (q : ℚ)⁻¹) := by
    apply prod_nonneg
    intro q hq
    have hqp := Nat.prime_of_mem_primeFactors (mem_filter.mp hq).1
    exact sub_nonneg.mpr (inv_le_one_of_one_le₀ (by exact_mod_cast hqp.one_le))
  have hcancel : (∏ q ∈ nonFermatFactors n, (q : ℚ) / (q - 1 : ℕ)) *
      (∏ q ∈ nonFermatFactors n, (1 - (q : ℚ)⁻¹)) = 1 := by
    rw [← prod_mul_distrib]
    apply prod_eq_one
    intro q hq
    have hqp := Nat.prime_of_mem_primeFactors (mem_filter.mp hq).1
    have hq1 : (1 : ℚ) < q := by exact_mod_cast hqp.one_lt
    rw [Nat.cast_sub hqp.one_le, Nat.cast_one]
    field_simp [show (q : ℚ) ≠ 0 by linarith,
      show (q : ℚ) - 1 ≠ 0 by linarith]
  have hh := mul_le_mul_of_nonneg_right hbound hw0
  rw [hcancel] at hh
  exact hh

/-- A common divisor of smooth predecessors bounds their total reciprocal mass. -/
theorem mass_le_euler_of_common_dvd (Q : Finset ℕ) (r D : ℕ)
    (hdiv : ∀ q ∈ Q, D ∣ q - 1)
    (hsm : ∀ q ∈ Q, (q - 1) / D ∈ Nat.smoothNumbers (r + 1)) :
    (∑ q ∈ Q, (r : ℚ) / (q - 1 : ℕ)) ≤
      (r : ℚ) / D * ∏ p ∈ r.primesLE, (p : ℚ) / (p - 1 : ℕ) ∧
      (2 ≤ r → 0 < D →
        (∑ q ∈ Q, (r : ℚ) / (q - 1 : ℕ)) <
          (r : ℚ) / D * ∏ p ∈ r.primesLE, (p : ℚ) / (p - 1 : ℕ)) := by
  classical
  by_cases hD : D = 0
  · subst D
    have hQ : Q = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro q hq
      exact (hsm q hq).1 (by simp)
    simp [hQ]
  let u : ℕ → ℕ := fun q => (q - 1) / D
  have hmul (q : ℕ) (hq : q ∈ Q) : D * u q = q - 1 :=
    Nat.mul_div_cancel' (hdiv q hq)
  have hinj : Set.InjOn u Q := by
    intro q hq t ht heq
    have hpred : q - 1 = t - 1 := by rw [← hmul q hq, ← hmul t ht, heq]
    have hq0 : q - 1 ≠ 0 := by
      intro he
      exact (hsm q hq).1 (by simp [he])
    have ht0 : t - 1 ≠ 0 := by
      intro he
      exact (hsm t ht).1 (by simp [he])
    omega
  have hsmooth : ∀ m ∈ Q.image u, m ∈ Nat.smoothNumbers (r + 1) := by
    intro m hm
    obtain ⟨q, hq, rfl⟩ := mem_image.mp hm
    exact hsm q hq
  have hs := LongGapsBetweenPrimes.sum_smooth_le_eulerProduct
    (N := r) (σ := 1) (by norm_num) (Q.image u) hsmooth
  simp only [Real.rpow_neg_one] at hs
  have heuler : LongGapsBetweenPrimes.eulerProduct r 1 =
      ∏ p ∈ r.primesLE, (p : ℝ) / (p - 1 : ℕ) := by
    unfold LongGapsBetweenPrimes.eulerProduct
    apply prod_congr rfl
    intro p hp
    have hp1 := (Nat.prime_of_mem_primesLE hp).one_lt
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
    rw [Real.rpow_neg_one, Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one]
    field_simp
  rw [heuler] at hs
  have hsum : (∑ q ∈ Q, (r : ℝ) / (q - 1 : ℕ)) =
      (r : ℝ) / D * ∑ q ∈ Q, (u q : ℝ)⁻¹ := by
    rw [mul_sum]
    apply sum_congr rfl
    intro q hq
    rw [← hmul q hq, Nat.cast_mul]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hweak : (∑ q ∈ Q, (r : ℚ) / (q - 1 : ℕ)) ≤
      (r : ℚ) / D * ∏ p ∈ r.primesLE, (p : ℚ) / (p - 1 : ℕ) := by
    have hreal := mul_le_mul_of_nonneg_left hs
      (show 0 ≤ (r : ℝ) / D by positivity)
    rw [sum_image hinj, ← hsum] at hreal
    apply (Rat.cast_le (K := ℝ)).mp
    simpa only [Rat.cast_sum, Rat.cast_div, Rat.cast_natCast, Rat.cast_mul,
      Rat.cast_prod] using hreal
  refine ⟨hweak, ?_⟩
  intro hr hDpos
  let S := Q.image u
  let k := S.sup id + 1
  have hlarge : S.sup id < 2 ^ k := by
    have := Nat.lt_two_pow_self (n := k)
    dsimp [k] at *
    omega
  have hmissing : 2 ^ k ∉ S := by
    intro hm
    have : 2 ^ k ≤ S.sup id := Finset.le_sup (f := id) hm
    omega
  have hpow : 2 ^ k ∈ Nat.smoothNumbers (r + 1) := by
    apply Nat.mem_smoothNumbers'.mpr
    intro p hp hpd
    have he : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
      (hp.dvd_of_dvd_pow hpd)
    omega
  have hs' := LongGapsBetweenPrimes.sum_smooth_le_eulerProduct
    (N := r) (σ := 1) (by norm_num) (insert (2 ^ k) S) (by
      intro m hm
      rcases mem_insert.mp hm with he | hm
      · exact he ▸ hpow
      · exact hsmooth m hm)
  simp only [Real.rpow_neg_one] at hs'
  rw [heuler, sum_insert hmissing] at hs'
  have hlt : (∑ m ∈ S, (m : ℝ)⁻¹) <
      ∏ p ∈ r.primesLE, (p : ℝ) / (p - 1 : ℕ) := by
    have hpos : 0 < ((2 ^ k : ℕ) : ℝ)⁻¹ := by positivity
    linarith
  have hreal := mul_lt_mul_of_pos_left hlt
    (show 0 < (r : ℝ) / D by positivity)
  rw [show (∑ m ∈ S, (m : ℝ)⁻¹) = ∑ q ∈ Q, (u q : ℝ)⁻¹ from
    sum_image hinj, ← hsum] at hreal
  apply (Rat.cast_lt (K := ℝ)).mp
  simpa only [Rat.cast_sum, Rat.cast_div, Rat.cast_natCast, Rat.cast_mul,
    Rat.cast_prod] using hreal

/-- Euler-product capacities imply both sigma-totient inequalities and strictness. -/
theorem makowski_schinzel_of_euler_condition (n : ℕ)
    (h : ∀ r : ℕ, r.Prime → Odd r → (topGroup n r).Nonempty →
      (r : ℚ) * ∏ p ∈ r.primesLE, (p : ℚ) / (p - 1 : ℕ) ≤
        ((topGroup n r).gcd (· - 1) : ℕ)) :
    n ≤ 2 * ArithmeticFunction.sigma 1 n.totient ∧
      (Odd n → n ≤ ArithmeticFunction.sigma 1 n.totient) ∧
      ((nonFermatFactors n).Nonempty →
        n < 2 * ArithmeticFunction.sigma 1 n.totient ∧
          (Odd n → n < ArithmeticFunction.sigma 1 n.totient)) := by
  classical
  have hcap (r : ℕ) (hr : r.Prime) (hro : Odd r) :
      (∑ q ∈ topGroup n r, (r : ℚ) / (q - 1 : ℕ)) ≤ 1 := by
    by_cases he : (topGroup n r).Nonempty
    · let D := (topGroup n r).gcd (· - 1)
      have hD0 : D ≠ 0 := by
        apply gcd_ne_zero_iff.mpr
        obtain ⟨q, hq⟩ := he
        refine ⟨q, hq, ?_⟩
        exact (nonFermat_predecessor_pos
          (Certificate.sources_subset_interesting hr.one_lt hro (mem_filter.mp hq).1)).ne'
      have hDq : (0 : ℚ) < D := by exact_mod_cast Nat.pos_of_ne_zero hD0
      have hm := mass_le_euler_of_common_dvd (topGroup n r) r D
        (fun q hq => gcd_dvd hq) (fun q hq =>
          Nat.mem_smoothNumbers_of_dvd (mem_filter.mp hq).2
            (Nat.div_dvd_of_dvd (gcd_dvd hq)))
      apply hm.1.trans
      rw [show (r : ℚ) / D * (∏ p ∈ r.primesLE, (p : ℚ) / (p - 1 : ℕ)) =
        ((r : ℚ) * ∏ p ∈ r.primesLE, (p : ℚ) / (p - 1 : ℕ)) / D by ring]
      exact (div_le_one hDq).mpr (h r hr hro he)
    · have he' := not_nonempty_iff_eq_empty.mp he
      simp [he']
  have hpsi := one_le_psi_of_labelled_groups n (fun q => (q - 1).maxPrimeFac)
    (by
      intro q₀ hq₀
      let p := (q₀ - 1).maxPrimeFac
      have hp : p.Prime := (nonFermat_label hq₀).1
      have hpo : Odd p := (nonFermat_label hq₀).2
      rw [← topGroup_eq_fiber n p hp hpo]
      have hb : (∏ q ∈ topGroup n p, (q : ℚ) / (q - 1 : ℕ)) ≤
          geom p (topGroup n p).card := by
        apply le_of_not_gt
        intro hbad
        exact (not_lt_of_ge (hcap p hp hpo)) (necessary_mass hp.pos _ hbad)
      apply hb.trans
      have he : (oddPredecessorPart n).factorization p =
          ∑ q ∈ nonFermatFactors n, (q - 1).factorization p := by
        rw [oddPredecessorPart, Nat.factorization_ordCompl,
          Finsupp.erase_ne (by intro he; exact hpo.not_two_dvd_nat (he ▸ dvd_rfl))]
        exact Nat.factorization_prod_apply
          (fun q hq => (nonFermat_predecessor_pos hq).ne')
      have hc : (topGroup n p).card ≤
          (oddPredecessorPart n).factorization p := by
        rw [he, topGroup_eq_fiber n p hp hpo]
        calc
          _ = ∑ _q ∈ (nonFermatFactors n).filter
              (fun q => (q - 1).maxPrimeFac = p), 1 := by simp
          _ ≤ ∑ q ∈ (nonFermatFactors n).filter
              (fun q => (q - 1).maxPrimeFac = p), (q - 1).factorization p := by
            apply sum_le_sum
            intro q hq
            obtain ⟨hq, hl⟩ := mem_filter.mp hq
            apply hp.factorization_pos_of_dvd (nonFermat_predecessor_pos hq).ne'
            exact hl ▸ Nat.maxPrimeFac_dvd
          _ ≤ _ := sum_le_sum_of_subset (filter_subset _ _)
      apply (Rat.cast_le (K := ℝ)).mp
      simpa only [geom, Rat.cast_sum, Rat.cast_pow, Rat.cast_inv, Rat.cast_natCast,
        D5.S3.Arith.RobinExponentSwap.reciprocalGeomSum] using
        (D5.S3.Arith.Robin.PaddingRatio.geom_mono (p := p) hc))
  have hpn : (n : ℚ) ≤ psi n * n := by nlinarith [Nat.cast_nonneg (α := ℚ) n]
  obtain ⟨hall, hodd, hstrict⟩ := psi_mul_le_sigma_totient n
  refine ⟨?_, ?_, ?_⟩
  · exact_mod_cast hpn.trans hall
  · intro hno
    exact_mod_cast hpn.trans (hodd hno)
  · intro hQ
    refine ⟨?_, ?_⟩
    · exact_mod_cast hpn.trans_lt (hstrict hQ).1
    · intro hno
      exact_mod_cast hpn.trans_lt ((hstrict hQ).2 hno)


end D5.S3.Arith.MakowskiSchinzel.EulerCondition
