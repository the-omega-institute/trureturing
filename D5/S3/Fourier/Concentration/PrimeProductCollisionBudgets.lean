/- GID: D5/S3/Fourier/Concentration/PrimeProductCollisionBudgets
   generality: G
   mirror-B: D5/B/S3/Fourier/Concentration/PrimeProductCollisionBudgets
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A common band shift bounds the excess collision mass across products of primes. -/

import D5.S3.Fourier.Concentration.PrimeCyclicCollisionBudgets
import Mathlib.Data.Finset.Powerset

set_option autoImplicit false

open Finset

noncomputable section

namespace D5.S3.Fourier.Concentration.PrimeProductCollisionBudgets

open PrimeCyclicCollisionBudgets (band_alias_card_le)

private theorem number_of_subsets_with_shared_shift {I J : Type*}
    [DecidableEq I] [DecidableEq J] (P : Finset I) (Y : Finset J)
    (hit : I → J → Prop) [DecidableRel hit] (r B : ℕ)
    (hB : ∀ y ∈ Y, (P.filter fun q => hit q y).card ≤ B) :
    ((P.powersetCard r).filter fun A => ∃ y ∈ Y, ∀ q ∈ A, hit q y).card ≤
      min (P.card.choose r) (Y.card * (min B P.card).choose r) := by
  classical
  apply le_min
  · rw [← card_powersetCard]
    exact card_filter_le _ _
  · let sets (y : J) := (P.filter fun q => hit q y).powersetCard r
    have hsub : ((P.powersetCard r).filter fun A => ∃ y ∈ Y, ∀ q ∈ A, hit q y) ⊆
        Y.biUnion sets := by
      intro A hA
      obtain ⟨hA, y, hy, hhit⟩ := mem_filter.mp hA
      refine mem_biUnion.mpr ⟨y, hy, mem_powersetCard.mpr ⟨?_, (mem_powersetCard.mp hA).2⟩⟩
      exact fun q hq => mem_filter.mpr ⟨(mem_powersetCard.mp hA).1 hq, hhit q hq⟩
    refine (card_le_card hsub).trans (card_biUnion_le_card_mul _ _ _ ?_)
    intro y hy
    rw [show (sets y).card = (P.filter fun q => hit q y).card.choose r by
      exact card_powersetCard _ _]
    exact Nat.choose_le_choose r (le_min (hB y hy) (card_filter_le _ _))


private theorem single_shift_prime_count
    (P : Finset ℕ) {Q B H D : ℕ} (d y : ℤ)
    (hQ : 2 ≤ Q) (hP : ∀ q ∈ P, q.Prime ∧ Q ≤ q)
    (hd : H < d.natAbs) (hD : d.natAbs ≤ D)
    (hy : y ∈ Icc (-(H : ℤ)) H)
    (hpow : D + H < Q ^ (B + 1)) :
    (P.filter fun (q : ℕ) => (q : ℤ) ∣ d - y).card ≤ B := by
  have hyabs : y.natAbs ≤ H := by have := mem_Icc.mp hy; omega
  have hpos : 0 < (d-y).natAbs := by omega
  have hmax : (d-y).natAbs ≤ D + H :=
    (Int.natAbs_sub_le d y).trans (Nat.add_le_add hD hyabs)
  have hsum : ((D : ℤ) + H).natAbs = D + H := by omega
  have h := band_alias_card_le P Q B 0 (D + H) (d-y) hQ hP hpos hmax
    (by simpa [hsum] using hpow)
  refine (card_le_card ?_).trans h
  intro q hq
  obtain ⟨hPq, hdiv⟩ := mem_filter.mp hq
  exact mem_filter.mpr ⟨hPq, 0, by simp,
    (ZMod.intCast_eq_intCast_iff_dvd_sub 0 (d-y) q).mpr (by simpa using hdiv)⟩

private theorem product_band_alias_card_le
    (P : Finset ℕ) {Q B H D : ℕ} (d : ℤ) (r : ℕ)
    (hQ : 2 ≤ Q) (hP : ∀ q ∈ P, q.Prime ∧ Q ≤ q)
    (hd : H < d.natAbs) (hD : d.natAbs ≤ D)
    (hpow : D + H < Q ^ (B + 1)) :
    ((P.powersetCard r).filter fun A => ∃ y ∈ Icc (-(H : ℤ)) H,
      (y : ZMod (∏ q ∈ A, q)) = (d : ZMod (∏ q ∈ A, q))).card ≤
      min (P.card.choose r) ((2 * H + 1) * (min B P.card).choose r) := by
  let Y := Icc (-(H : ℤ)) H
  let hit (q : ℕ) (y : ℤ) : Prop := (q : ℤ) ∣ d - y
  have hyCount : Y.card = 2 * H + 1 := by
    dsimp [Y]
    rw [Int.card_Icc]
    omega
  rw [← hyCount]
  refine le_trans (card_le_card ?_) (number_of_subsets_with_shared_shift P Y hit r B
    fun y hy => single_shift_prime_count P d y hQ hP hd hD hy hpow)
  intro A hA
  obtain ⟨hA, y, hy, heq⟩ := mem_filter.mp hA
  refine mem_filter.mpr ⟨hA, y, hy, fun q hq => ?_⟩
  have hdiv := (ZMod.intCast_eq_intCast_iff_dvd_sub y d (∏ a ∈ A, a)).mp heq
  have hqdvd : q ∣ ∏ a ∈ A, a := dvd_prod_of_mem id hq
  exact dvd_trans (by exact_mod_cast hqdvd : (q : ℤ) ∣ ((∏ a ∈ A, a : ℕ) : ℤ)) hdiv


private theorem sum_product_modular_excess_le
    {I : Type*} (S : Finset I) (d : I → ℤ) (weight : I → ℝ)
    (P : Finset ℕ) (Q B H D r : ℕ)
    (hQ : 2 ≤ Q) (hP : ∀ q ∈ P, q.Prime ∧ Q ≤ q)
    (hw : ∀ i ∈ S, 0 ≤ weight i) (hD : ∀ i ∈ S, (d i).natAbs ≤ D)
    (hpow : D + H < Q ^ (B + 1)) :
    let Y := Icc (-(H : ℤ)) H
    let L := ∑ i ∈ S, if (d i).natAbs ≤ H then weight i else 0
    let C (q : ℕ) := ∑ i ∈ S,
      if ∃ y ∈ Y, (y : ZMod q) = (d i : ZMod q) then weight i else 0
    let excess := ∑ A ∈ P.powersetCard r, (C (∏ q ∈ A, q) - L)
    0 ≤ excess ∧ excess ≤
      (min (P.card.choose r) ((2 * H + 1) * (min B P.card).choose r) : ℝ) *
        ((∑ i ∈ S, weight i) - L) := by
  classical
  let R := P.powersetCard r
  let Y := Icc (-(H : ℤ)) H
  let hit (A : Finset ℕ) (i : I) := ∃ y ∈ Y,
    (y : ZMod (∏ q ∈ A, q)) = (d i : ZMod (∏ q ∈ A, q))
  let band (i : I) := (d i).natAbs ≤ H
  let w (i : I) : ℝ := if band i then 0 else weight i
  have hw' (i : I) (hi : i ∈ S) : 0 ≤ w i := by
    dsimp [w]
    split_ifs
    · exact le_rfl
    · exact hw i hi
  have hexcess (A : Finset ℕ) :
      (∑ i ∈ S, if hit A i then weight i else 0) -
        (∑ i ∈ S, if band i then weight i else 0) =
        ∑ i ∈ S, if hit A i then w i else 0 := by
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun i _ => ?_
    by_cases hi : band i
    · have hi' : d i ∈ Y := by
        dsimp [band] at hi
        exact mem_Icc.mpr (by omega)
      have hhit : hit A i := ⟨d i, hi', rfl⟩
      simp [hhit, hi, w]
    · simp [hi, w]
  have hW : (∑ i ∈ S, weight i) - (∑ i ∈ S, if band i then weight i else 0) =
      ∑ i ∈ S, w i := by
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun i _ => by by_cases hi : band i <;> simp [hi,w]
  let excess := ∑ A ∈ R, ((∑ i ∈ S, if hit A i then weight i else 0) -
    (∑ i ∈ S, if band i then weight i else 0))
  change 0 ≤ excess ∧ excess ≤
    (min (P.card.choose r) ((2 * H + 1) * (min B P.card).choose r) : ℝ) *
      ((∑ i ∈ S, weight i) - (∑ i ∈ S, if band i then weight i else 0))
  have htotal : excess = ∑ A ∈ R, ∑ i ∈ S, if hit A i then w i else 0 :=
    sum_congr rfl fun A _ => hexcess A
  rw [htotal, hW]
  constructor
  · exact sum_nonneg fun A _ => sum_nonneg fun i hi => by
      split_ifs
      · exact hw' i hi
      · exact le_rfl
  · rw [sum_comm, mul_sum]
    refine sum_le_sum fun i hi => ?_
    by_cases hb : band i
    · simp [w,hb]
    · have hd : H < (d i).natAbs := Nat.lt_of_not_ge hb
      have hc := product_band_alias_card_le P (d i) r hQ hP hd (hD i hi) hpow
      rw [← sum_filter, sum_const, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (hw' i hi)

open D5.S3.Fourier.Concentration.CyclicCollisionCertificate
open D5.S3.Fourier.Concentration.FiniteTailMomentMissingWindow (monomialWeight)
open D5.S3.Fourier.Concentration.FiniteSincCollisionMoment (monomialWeight_nonneg)

/-- Each off-band pair counted by a product modulus shares one shift across all of its
prime factors. Summing the incidence bound controls the total weighted excess. -/
theorem sum_prime_product_cyclic_excess_le
    {J : Type*} [Fintype J] [DecidableEq J]
    (a : J → ℤ) (w : J → ℝ) (p : ℕ)
    (P : Finset ℕ) (Q B H D r : ℕ)
    (hQ : 2 ≤ Q) (hP : ∀ q ∈ P, q.Prime ∧ Q ≤ q) (hw : ∀ j, 0 ≤ w j)
    (hD : ∀ m ∈ piAntidiag univ p, ∀ n ∈ piAntidiag univ p,
      (latticeFrequency a m - latticeFrequency a n).natAbs ≤ D)
    (hpow : D + H < Q ^ (B + 1)) :
    let A := piAntidiag (univ : Finset J) p
    let L := ∑ m ∈ A, ∑ n ∈ A,
      if (latticeFrequency a m - latticeFrequency a n).natAbs ≤ H
      then monomialWeight w m * monomialWeight w n else 0
    let C (q : ℕ) := cyclicCollisionMass q a w p
      ((Icc (-(H : ℤ)) H).image (fun y : ℤ => (y : ZMod q)))
    let familySize := P.card.choose r
    let excess := ∑ S ∈ P.powersetCard r, (C (∏ q ∈ S, q) - L)
    0 ≤ excess ∧ excess ≤
      (min familySize ((2 * H + 1) * (min B P.card).choose r) : ℝ) *
        ((∑ j, w j) ^ (2 * p) - L) := by
  classical
  let A := piAntidiag (univ : Finset J) p
  let gap : (J → ℕ) × (J → ℕ) → ℤ :=
    fun pair => latticeFrequency a pair.1 - latticeFrequency a pair.2
  let weight : (J → ℕ) × (J → ℕ) → ℝ :=
    fun pair => monomialWeight w pair.1 * monomialWeight w pair.2
  have h := sum_product_modular_excess_le (A ×ˢ A) gap weight P Q B H D r hQ hP
    (fun ⟨m, n⟩ _ => mul_nonneg (monomialWeight_nonneg w hw m)
      (monomialWeight_nonneg w hw n))
    (fun ⟨m, n⟩ hmn => hD m (mem_product.mp hmn).1 n (mem_product.mp hmn).2)
    hpow
  dsimp only at h ⊢
  simp only [sum_product, gap, weight] at h
  have hmass : (∑ m ∈ A, ∑ n ∈ A, monomialWeight w m * monomialWeight w n) =
      (∑ j, w j) ^ (2 * p) := by
    have hwSum : ∑ m ∈ A, monomialWeight w m = (∑ j, w j) ^ p :=
      (sum_pow_eq_sum_piAntidiag univ w p).symm
    simp_rw [← mul_sum]
    rw [← sum_mul, hwSum, ← pow_add, two_mul]
  rw [hmass] at h
  simpa only [cyclicCollisionMass, mem_image] using h

#print axioms sum_prime_product_cyclic_excess_le

end D5.S3.Fourier.Concentration.PrimeProductCollisionBudgets
