/- GID: D5/S3/Fourier/Concentration/PrimeCyclicCollisionBudgets
   generality: G
   mirror-B: D5/B/S3/Fourier/Concentration/PrimeCyclicCollisionBudgets
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Prime moduli bound the excess weighted mass caused by cyclic wraparound. -/

import D5.S3.Fourier.Concentration.CyclicCollisionCertificate
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Int.Interval
import Mathlib.Data.ZMod.Basic
import Mathlib.Basic.Real.Basic

set_option autoImplicit false

open Finset

noncomputable section

namespace D5.S3.Fourier.Concentration.PrimeCyclicCollisionBudgets

theorem band_alias_card_le
    (P : Finset ℕ) (Q B H D : ℕ) (d : ℤ)
    (hQ : 2 ≤ Q) (hP : ∀ q ∈ P, q.Prime ∧ Q ≤ q)
    (hd : H < d.natAbs) (hD : d.natAbs ≤ D)
    (hpower : (∏ y ∈ Icc (-(H : ℤ)) H, ((D : ℤ) - y).natAbs) < Q ^ (B + 1)) :
    (P.filter (fun q => ∃ y ∈ Icc (-(H : ℤ)) H, (y : ZMod q) = (d : ZMod q))).card ≤ B := by
  classical
  let band := Icc (-(H : ℤ)) (H : ℤ)
  let hit := P.filter (fun q => ∃ y ∈ band, (y : ZMod q) = (d : ZMod q))
  let z : ℤ := d.natAbs
  let value := ∏ y ∈ band, (z - y).natAbs
  have hz : (H : ℤ) < z := by dsimp [z]; exact_mod_cast hd
  have hzD : z ≤ (D : ℤ) := by dsimp [z]; exact_mod_cast hD
  have hpos : ∀ y ∈ band, 0 < z - y := by
    intro y hy
    exact sub_pos.mpr ((mem_Icc.mp hy).2.trans_lt hz)
  have hvalue : 0 < value := by
    refine Finset.prod_pos fun y hy => ?_
    have := hpos y hy
    omega
  have hsubset : hit ⊆ value.primeFactors := by
    intro q hq
    obtain ⟨hmem, y, hy, hcongr⟩ := mem_filter.mp hq
    have hdiv := (ZMod.intCast_eq_intCast_iff_dvd_sub y d q).mp hcongr
    have hshift : ∃ t ∈ band, (q : ℤ) ∣ z - t := by
      by_cases hsign : 0 ≤ d
      · exact ⟨y, hy, by simpa [z, Int.natAbs_of_nonneg hsign] using hdiv⟩
      · refine ⟨-y, ?_, ?_⟩
        · have hy' := mem_Icc.mp hy
          exact mem_Icc.mpr (by omega)
        · have heq : z - (-y) = -(d - y) := by dsimp [z]; omega
          rw [heq]
          exact Int.dvd_neg.mpr hdiv
    obtain ⟨t, ht, hdiv'⟩ := hshift
    have habs : q ∣ (z - t).natAbs := by
      simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr hdiv'
    exact Nat.mem_primeFactors.mpr ⟨(hP q hmem).1,
      habs.trans (dvd_prod_of_mem (fun y => (z - y).natAbs) ht), hvalue.ne'⟩
  have hprod_dvd : (∏ q ∈ hit, q) ∣ value :=
    (prod_dvd_prod_of_subset hit value.primeFactors id hsubset).trans (Nat.prod_primeFactors_dvd _)
  have hsize : (∏ q ∈ hit, q) ≤ value := Nat.le_of_dvd hvalue hprod_dvd
  have hcompare : value ≤ ∏ y ∈ band, ((D : ℤ) - y).natAbs := by
    apply prod_le_prod
    intro y hy
    have hypos := hpos y hy
    omega
  by_contra h
  have hcount : B + 1 ≤ hit.card := by
    change ¬ hit.card ≤ B at h
    omega
  have hbase : Q ^ hit.card ≤ ∏ q ∈ hit, q := by
    rw [← prod_const]
    exact prod_le_prod fun q hq => (hP q (mem_filter.mp hq).1).2
  exact (not_lt_of_ge (((pow_le_pow_right' (show 1 ≤ Q by omega) hcount).trans
    hbase).trans (hsize.trans hcompare))) hpower

private theorem weighted_band_alias_le
    {I : Type*} (S : Finset I) (d : I → ℤ) (v : I → ℝ)
    (P : Finset ℕ) (Q B H D : ℕ)
    (hQ : 2 ≤ Q) (hP : ∀ q ∈ P, q.Prime ∧ Q ≤ q)
    (hv : ∀ i ∈ S, 0 ≤ v i) (hD : ∀ i ∈ S, (d i).natAbs ≤ D)
    (hpower : (∏ y ∈ Icc (-(H : ℤ)) H, ((D : ℤ) - y).natAbs) < Q ^ (B + 1)) :
    let band := Icc (-(H : ℤ)) (H : ℤ)
    let excess := ∑ q ∈ P, ∑ i ∈ S,
      if H < (d i).natAbs ∧ (∃ y ∈ band, (y : ZMod q) = (d i : ZMod q)) then v i else 0
    0 ≤ excess ∧ excess ≤ ((min B P.card : ℕ) : ℝ) * (∑ i ∈ S, if H < (d i).natAbs then v i else 0) := by
  classical
  dsimp only
  constructor
  · exact sum_nonneg fun q _ => sum_nonneg fun i hi => by split_ifs <;> simp [hv i hi]
  · rw [sum_comm, mul_sum]
    refine sum_le_sum fun i hi => ?_
    by_cases ho : H < (d i).natAbs
    · simp only [ho, true_and, ite_true]
      let T := P.filter (fun q => ∃ y ∈ Icc (-(H : ℤ)) H, (y : ZMod q) = (d i : ZMod q))
      have hT : T.card ≤ min B P.card :=
        le_min (band_alias_card_le P Q B H D (d i) hQ hP ho (hD i hi) hpower)
          (card_le_card (filter_subset _ _))
      rw [← sum_filter, sum_const, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hT) (hv i hi)
    · simp [ho]

private theorem sum_modular_excess_le
    {I : Type*} (S : Finset I) (d : I → ℤ) (v : I → ℝ)
    (P : Finset ℕ) (Q B H D : ℕ)
    (hQ : 2 ≤ Q) (hP : ∀ q ∈ P, q.Prime ∧ Q ≤ q)
    (hv : ∀ i ∈ S, 0 ≤ v i) (hD : ∀ i ∈ S, (d i).natAbs ≤ D)
    (hpower : (∏ y ∈ Icc (-(H : ℤ)) H, ((D : ℤ) - y).natAbs) < Q ^ (B + 1)) :
    let band := Icc (-(H : ℤ)) (H : ℤ)
    let L := ∑ i ∈ S, if (d i).natAbs ≤ H then v i else 0
    let C := fun q => ∑ i ∈ S,
      if ∃ y ∈ band, (y : ZMod q) = (d i : ZMod q) then v i else 0
    0 ≤ ∑ q ∈ P, (C q - L) ∧
      ∑ q ∈ P, (C q - L) ≤ ((min B P.card : ℕ) : ℝ) * ((∑ i ∈ S, v i) - L) := by
  classical
  dsimp only
  have hexcess (q : ℕ) :
      (∑ i ∈ S, if ∃ y ∈ Icc (-(H : ℤ)) H, (y : ZMod q) = (d i : ZMod q) then v i else 0)
          - (∑ i ∈ S, if (d i).natAbs ≤ H then v i else 0) =
        ∑ i ∈ S, if H < (d i).natAbs ∧
          (∃ y ∈ Icc (-(H : ℤ)) H, (y : ZMod q) = (d i : ZMod q)) then v i else 0 := by
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun i _ => ?_
    by_cases h : (d i).natAbs ≤ H
    · have hy : d i ∈ Icc (-(H : ℤ)) H := mem_Icc.mpr (by omega)
      rw [ite_eq_left (show ∃ y ∈ Icc (-(H : ℤ)) H,
        (y : ZMod q) = (d i : ZMod q) from ⟨d i, hy, rfl⟩), ite_eq_left h,
        ite_eq_right (fun h' => (not_lt.mpr h) h'.1), sub_self]
    · simp [h, lt_of_not_ge h]
  have hweight :
      (∑ i ∈ S, v i) - (∑ i ∈ S, if (d i).natAbs ≤ H then v i else 0) =
        ∑ i ∈ S, if H < (d i).natAbs then v i else 0 := by
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun i _ => by
      by_cases h : (d i).natAbs ≤ H <;> simp [h, not_lt.mpr, lt_of_not_ge]
  simp only [hexcess, hweight]
  exact weighted_band_alias_le S d v P Q B H D hQ hP hv hD hpower

open D5.S3.Fourier.Concentration.CyclicCollisionCertificate
open D5.S3.Fourier.Concentration.FiniteTailMomentMissingWindow (monomialWeight)
open D5.S3.Fourier.Concentration.FiniteSincCollisionMoment (monomialWeight_nonneg)

/-- The total excess over the integer band counts each off-band pair in at most
the prescribed number of moduli. -/
theorem sum_cyclic_excess_le
    {J : Type*} [Fintype J] [DecidableEq J]
    (a : J → ℤ) (w : J → ℝ) (p : ℕ)
    (P : Finset ℕ) (Q B H D : ℕ)
    (hQ : 2 ≤ Q) (hP : ∀ q ∈ P, q.Prime ∧ Q ≤ q) (hw : ∀ j, 0 ≤ w j)
    (hD : ∀ m ∈ piAntidiag univ p, ∀ n ∈ piAntidiag univ p,
      (latticeFrequency a m - latticeFrequency a n).natAbs ≤ D)
    (hpower : (∏ y ∈ Icc (-(H : ℤ)) H, ((D : ℤ) - y).natAbs) < Q ^ (B + 1)) :
    let A := piAntidiag (univ : Finset J) p
    let L := ∑ m ∈ A, ∑ n ∈ A,
      if (latticeFrequency a m - latticeFrequency a n).natAbs ≤ H
      then monomialWeight w m * monomialWeight w n else 0
    let C := fun q => cyclicCollisionMass q a w p
      ((Icc (-(H : ℤ)) H).image (fun y : ℤ => (y : ZMod q)))
    0 ≤ ∑ q ∈ P, (C q - L) ∧
      ∑ q ∈ P, (C q - L) ≤ ((min B P.card : ℕ) : ℝ) * ((∑ j, w j) ^ (2 * p) - L) := by
  classical
  let A := piAntidiag (univ : Finset J) p
  let d : (J → ℕ) × (J → ℕ) → ℤ :=
    fun pair => latticeFrequency a pair.1 - latticeFrequency a pair.2
  let v : (J → ℕ) × (J → ℕ) → ℝ :=
    fun pair => monomialWeight w pair.1 * monomialWeight w pair.2
  have h := sum_modular_excess_le (A ×ˢ A) d v P Q B H D hQ hP
    (fun ⟨m, n⟩ _ => mul_nonneg (monomialWeight_nonneg w hw m)
      (monomialWeight_nonneg w hw n))
    (fun ⟨m, n⟩ hmn => hD m (mem_product.mp hmn).1 n (mem_product.mp hmn).2)
    hpower
  dsimp only at h ⊢
  simp only [sum_product, d, v] at h
  have hmass : (∑ m ∈ A, ∑ n ∈ A, monomialWeight w m * monomialWeight w n) =
      (∑ j, w j) ^ (2 * p) := by
    have hwSum : ∑ m ∈ A, monomialWeight w m = (∑ j, w j) ^ p :=
      (sum_pow_eq_sum_piAntidiag univ w p).symm
    simp_rw [← mul_sum]
    rw [← sum_mul, hwSum, ← pow_add, two_mul]
  rw [hmass] at h
  simpa only [cyclicCollisionMass, mem_image] using h


#print axioms sum_cyclic_excess_le

end D5.S3.Fourier.Concentration.PrimeCyclicCollisionBudgets
