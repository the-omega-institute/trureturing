/- GID: D5/S3/Fourier/Concentration/CyclicFejerBand
   generality: G
   mirror-B: D5/B/S3/Fourier/Concentration/CyclicFejerBand
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A lower bound for cyclic prefix overlaps gives a positive Fourier bound for a band. -/

import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Data.Int.Interval

/-! A cyclic frequency band is controlled by the Fourier weights of an interval overlap. -/

open Finset

noncomputable section

namespace D5.S3.Fourier.Concentration.CyclicFejerBand

variable {q : ℕ} [NeZero q]

/-- The residues having an integer representative between `-H` and `H`. -/
def band (q H : ℕ) : Finset (ZMod q) :=
  (Icc (-(H : ℤ)) (H : ℤ)).image (fun z : ℤ => (z : ZMod q))

private def prefixPairs (q N : ℕ) (r : ZMod q) : Finset (ℕ × ℕ) :=
  (range N ×ˢ range N).filter fun p => ((p.1 : ZMod q) - p.2) = r

omit [NeZero q] in
private theorem card_prefixPairs_of_mem {N H : ℕ} (r : ZMod q) (hr : r ∈ band q H) :
    N - H ≤ (prefixPairs q N r).card := by
  obtain ⟨z, hz, rfl⟩ := mem_image.mp hr
  obtain ⟨hlo, hhi⟩ := mem_Icc.mp hz
  cases z with
  | ofNat d =>
    change (d : ℤ) ≤ (H : ℤ) at hhi
    rw [← card_range (N - H)]
    apply card_le_card_of_injOn (fun j => (j + d, j))
    · intro j hj
      have hj' := mem_range.mp (mem_coe.mp hj)
      have hA : j + d < N := by omega
      have hB : j < N := by omega
      apply mem_filter.mpr
      refine ⟨mem_product.mpr ⟨mem_range.mpr hA, mem_range.mpr hB⟩, ?_⟩
      change ((j + d : ℕ) : ZMod q) - (j : ZMod q) = ((d : ℤ) : ZMod q)
      rw [Int.cast_natCast, Nat.cast_add, add_sub_cancel_left]
    · intro j _ k _ hjk
      exact congrArg Prod.snd hjk
  | negSucc d =>
    rw [← card_range (N - H)]
    apply card_le_card_of_injOn (fun j => (j, j + (d + 1)))
    · intro j hj
      have hj' := mem_range.mp (mem_coe.mp hj)
      have hA : j < N := by omega
      have hB : j + (d + 1) < N := by omega
      apply mem_filter.mpr
      refine ⟨mem_product.mpr ⟨mem_range.mpr hA, mem_range.mpr hB⟩, ?_⟩
      simp [Int.cast_negSucc, Nat.cast_add]
    · intro j _ k _ hjk
      exact congrArg Prod.fst hjk

/-- The sum of the character at the first `N` natural-number indices, with multiplicity. -/
def prefixCharacter (q N : ℕ) [NeZero q] (k : ZMod q) : ℂ :=
  ∑ j ∈ range N, ZMod.stdAddChar ((j : ZMod q) * k)

private theorem pair_char_factor (N : ℕ) (k : ZMod q) :
    (∑ i ∈ range N, ∑ j ∈ range N,
      ZMod.stdAddChar (((i : ZMod q) - (j : ZMod q)) * k)) =
        prefixCharacter q N k * prefixCharacter q N (-k) := by
  rw [prefixCharacter, prefixCharacter, sum_mul]
  apply sum_congr rfl
  intro i _
  rw [mul_sum]
  apply sum_congr rfl
  intro j _
  rw [sub_mul, sub_eq_add_neg, AddChar.map_add_eq_mul, mul_neg]

private theorem fourier_point (M : ZMod q → ℂ) (r : ZMod q) :
    (q : ℂ) * M r = ∑ k : ZMod q, ZMod.stdAddChar (k * r) * ZMod.dft M k := by
  simpa [ZMod.dft_apply, mul_neg, smul_eq_mul] using
    (congrFun (ZMod.dft_dft M) (-r)).symm

private theorem sum_prefixPairs (N : ℕ) (M : ZMod q → ℝ) :
    (∑ r : ZMod q, ((prefixPairs q N r).card : ℝ) * M r) =
      ∑ i ∈ range N, ∑ j ∈ range N, M ((i : ZMod q) - j) := by
  let rOf (p : ℕ × ℕ) : ZMod q := (p.1 : ZMod q) - p.2
  have hrewrite (r : ZMod q) :
      ((prefixPairs q N r).card : ℝ) * M r =
        ∑ p ∈ (range N ×ˢ range N).filter (fun p => rOf p = r), M (rOf p) := by
    rw [prefixPairs]
    simp only [← nsmul_eq_mul]
    rw [← sum_const]
    apply sum_congr rfl
    intro p hp
    exact congrArg M (mem_filter.mp hp).2.symm
  simp_rw [hrewrite]
  rw [sum_fiberwise_of_maps_to (fun p _ => mem_univ (rOf p)), sum_product]

omit [NeZero q] in
private theorem card_prefixPairs_zero (N : ℕ) : N ≤ (prefixPairs q N 0).card := by
  refine (card_range N).symm.le.trans ?_
  apply card_le_card_of_injOn (fun j => (j, j))
  · intro j hj
    exact mem_filter.mpr ⟨mem_product.mpr ⟨hj, hj⟩, sub_self _⟩
  · intro i _ j _ hij
    exact congrArg Prod.fst hij

omit [NeZero q] in
private theorem zero_mem_band (H : ℕ) : 0 ∈ band q H := by
  refine mem_image.mpr ⟨(0 : ℤ), mem_Icc.mpr ⟨by omega, by positivity⟩, ?_⟩
  exact Int.cast_zero

private theorem band_le_pair_sum (N H : ℕ) (hHN : H ≤ N) (M : ZMod q → ℝ)
    (hM : ∀ r, 0 ≤ M r) :
    ((N - H : ℕ) : ℝ) * (∑ r ∈ band q H, M r) + H * M 0 ≤
      ∑ i ∈ range N, ∑ j ∈ range N, M ((i : ZMod q) - j) := by
  have hbonus : H * M 0 = ∑ r ∈ band q H, if r = 0 then (H : ℝ) * M r else 0 := by
    symm
    rw [sum_eq_single_of_mem 0 (zero_mem_band H) (fun r _ hr => ite_eq_right hr)]
    simp
  rw [mul_sum, hbonus, ← sum_add_distrib, ← sum_prefixPairs]
  calc
    _ ≤ ∑ r ∈ band q H, ((prefixPairs q N r).card : ℝ) * M r := by
      apply sum_le_sum
      intro r hr
      by_cases hzero : r = 0
      · subst r
        simp only [ite_true, ← add_mul]
        rw [← Nat.cast_add, Nat.sub_add_cancel hHN]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast card_prefixPairs_zero (q := q) N) (hM 0)
      · simp only [ite_eq_right hzero, add_zero]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast card_prefixPairs_of_mem r hr) (hM r)
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ _) fun r _ _ =>
      mul_nonneg (Nat.cast_nonneg _) (hM r)

private theorem fourier_pair_sum (N : ℕ) (M : ZMod q → ℂ) :
    (q : ℂ) * (∑ i ∈ range N, ∑ j ∈ range N, M ((i : ZMod q) - j)) =
      ∑ k : ZMod q, prefixCharacter q N k * prefixCharacter q N (-k) * ZMod.dft M k := by
  calc
    _ = ∑ i ∈ range N, ∑ j ∈ range N, ∑ k : ZMod q,
        ZMod.stdAddChar (((i : ZMod q) - (j : ZMod q)) * k) * ZMod.dft M k := by
      simp only [mul_sum]
      apply sum_congr rfl
      intro i _
      apply sum_congr rfl
      intro j _
      simpa only [mul_comm ((i : ZMod q) - (j : ZMod q))] using
        fourier_point M ((i : ZMod q) - (j : ZMod q))
    _ = ∑ k : ZMod q, ∑ i ∈ range N, ∑ j ∈ range N,
        ZMod.stdAddChar (((i : ZMod q) - (j : ZMod q)) * k) * ZMod.dft M k := by
      simp_rw [sum_comm (s := range N) (t := (univ : Finset (ZMod q)))]
    _ = _ := by
      apply sum_congr rfl
      intro k _
      simp_rw [← sum_mul]
      rw [pair_char_factor]

private theorem prefixCharacter_neg (N : ℕ) (k : ZMod q) :
    prefixCharacter q N (-k) = starRingEnd ℂ (prefixCharacter q N k) := by
  simp only [prefixCharacter, map_sum, mul_neg, AddChar.map_neg_eq_inv, ZMod.stdAddChar_apply]
  apply sum_congr rfl
  intro j _
  rw [← Circle.coe_inv, Circle.coe_inv_eq_conj]

/-- Positive character weights control band mass through the overlap of a finite prefix. -/
theorem band_le_positive_fourier (H N : ℕ) (hHN : H < N) (M : ZMod q → ℝ)
    (hM : ∀ r, 0 ≤ M r) :
    let windowWeight := fun z : ℂ => ‖z‖ ^ 2
    ((N - H : ℕ) : ℝ) * (∑ r ∈ band q H, M r) + H * M 0 ≤
      (∑ k : ZMod q, windowWeight (prefixCharacter q N k) *
        (ZMod.dft (fun r => (M r : ℂ)) k).re) / (q : ℝ) := by
  dsimp only
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hweight (k : ZMod q) :
      prefixCharacter q N k * prefixCharacter q N (-k) =
        ((‖prefixCharacter q N k‖ ^ 2 : ℝ) : ℂ) := by
    rw [prefixCharacter_neg, mul_comm, ← Complex.normSq_eq_conj_mul_self,
      Complex.normSq_eq_norm_sq]
  have hre := congrArg (Complex.reLm : ℂ →ₗ[ℝ] ℝ)
    (fourier_pair_sum N (fun r => (M r : ℂ)))
  have hre_apply (z : ℂ) : Complex.reLm z = z.re := rfl
  simp only [hweight, ← Complex.ofReal_sum, ← Complex.ofReal_natCast, ← Complex.ofReal_mul] at hre
  rw [map_sum] at hre
  simp only [hre_apply, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, zero_mul,
    sub_zero] at hre
  rw [le_div_iff₀ hq]
  calc
    _ = (q : ℝ) * (((N - H : ℕ) : ℝ) * (∑ r ∈ band q H, M r) + H * M 0) :=
      mul_comm _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (band_le_pair_sum N H hHN.le M hM) hq.le
    _ = _ := hre

end D5.S3.Fourier.Concentration.CyclicFejerBand
