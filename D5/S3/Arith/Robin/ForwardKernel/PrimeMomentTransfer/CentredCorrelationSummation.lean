/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/CentredCorrelationSummation
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/CentredCorrelationSummation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Strong prime correlations transfer to centred polynomial logarithmic BV sums. -/

import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.ArithmeticTransferDefs
import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.BVCorrelationSummation

/-! Inclusion–exclusion and BV summation for centred prime correlations. -/

open scoped BigOperators Topology
open Set Filter MeasureTheory

namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
noncomputable section
set_option autoImplicit false

private lemma hl_finset {SS : Finset ℕ → ℝ} {β ε M C N₀ N : ℝ}
    (h : ∀ N : ℝ, N₀ ≤ N → ∀ r : ℕ, 1 ≤ r → r ≤ 4 →
      ∀ d : Fin r → ℕ, Function.Injective d →
      (∀ i, 1 ≤ d i ∧ (d i : ℝ) ≤ M * N ^ β) →
      ∀ y : ℝ, 0 ≤ y → y ≤ 3 * N →
        |(∑ n ∈ Finset.Ioc 0 ⌊y⌋₊, ∏ i, ArithmeticFunction.vonMangoldt (n + d i)) -
          y * SS (Finset.univ.image d)| ≤ C * N ^ (1 / 2 + ε))
    (hN : N₀ ≤ N) (D : Finset ℕ) (hD : D.Nonempty) (hcard : D.card ≤ 4)
    (hd : ∀ d ∈ D, 1 ≤ d ∧ (d : ℝ) ≤ M * N ^ β)
    (y : ℝ) (hy : 0 ≤ y) (hyN : y ≤ 3 * N) :
    |(∑ n ∈ Finset.Ioc 0 ⌊y⌋₊, ∏ d ∈ D, ArithmeticFunction.vonMangoldt (n + d)) -
      y * SS D| ≤ C * N ^ (1 / 2 + ε) := by
  let e := D.equivFin.symm
  let d : Fin D.card → ℕ := fun i => (e i).val
  have hinj : Function.Injective d := Subtype.val_injective.comp e.injective
  have him : Finset.univ.image d = D := by
    ext v
    constructor
    · rintro hv
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
      exact (e i).property
    · intro hv
      exact Finset.mem_image.mpr ⟨D.equivFin ⟨v, hv⟩, Finset.mem_univ _, by simp [d, e]⟩
  have hp (n : ℕ) : (∏ i, ArithmeticFunction.vonMangoldt (n + d i)) =
      ∏ v ∈ D, ArithmeticFunction.vonMangoldt (n + v) := by
    calc
      _ = ∏ v ∈ Finset.univ.image d, ArithmeticFunction.vonMangoldt (n + v) :=
        (Finset.prod_image hinj.injOn).symm
      _ = _ := congrArg (fun T : Finset ℕ =>
        ∏ v ∈ T, ArithmeticFunction.vonMangoldt (n + v)) him
  simpa only [hp, him] using h N hN D.card (Finset.card_pos.mpr hD) hcard d hinj
    (fun i => hd _ (e i).property) y hy hyN

private lemma centred_expansion (D : Finset ℕ) (n : ℕ) :
    (∏ d ∈ D, (ArithmeticFunction.vonMangoldt (n + d) - 1)) =
      ∑ J ∈ D.powerset, (-1 : ℝ) ^ (D.card - J.card) *
        ∏ d ∈ J, ArithmeticFunction.vonMangoldt (n + d) := by
  simp_rw [sub_eq_add_neg]
  rw [Finset.prod_add]
  apply Finset.sum_congr rfl
  intro J hJ
  rw [Finset.prod_const, Finset.card_sdiff_of_subset (Finset.mem_powerset.mp hJ)]
  ring

/-- Inclusion–exclusion preserves the strong correlation error uniformly for all shift sets of
at most four elements, including the empty set. -/
private theorem centred_correlation_partial_sums (SS : Finset ℕ → ℝ) (β : ℝ)
    (hSS : SS ∅ = 1) (hHL : HL4 SS β) (M ε : ℝ) (hM : 1 ≤ M) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℝ in atTop,
      2 ≤ N ∧ ∀ D : Finset ℕ, D.card ≤ 4 →
        (∀ d ∈ D, 1 ≤ d ∧ (d : ℝ) ≤ M * N ^ β) →
        ∀ y : ℝ, 0 ≤ y → y ≤ 3 * N →
          |(∑ n ∈ Finset.Ioc 0 ⌊y⌋₊,
              ∏ d ∈ D, (ArithmeticFunction.vonMangoldt (n + d) - 1)) -
            y * center SS D| ≤ C * N ^ (1 / 2 + ε) := by
  obtain ⟨A, hA, N₀, hHL⟩ := hHL ε hε M hM
  refine ⟨16 * (A + 1), by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (max N₀ 2)] with N hN
  have hN₀ := (le_max_left N₀ 2).trans hN
  have hN2 := (le_max_right N₀ 2).trans hN
  have hpow : 1 ≤ N ^ (1 / 2 + ε) := Real.one_le_rpow (by linarith) (by linarith)
  refine ⟨hN2, ?_⟩
  intro D hD hd y hy hyN
  have herr (J : Finset ℕ) (hJ : J ∈ D.powerset) :
      |(∑ n ∈ Finset.Ioc 0 ⌊y⌋₊, ∏ d ∈ J, ArithmeticFunction.vonMangoldt (n + d)) -
        y * SS J| ≤ (A + 1) * N ^ (1 / 2 + ε) := by
    by_cases he : J = ∅
    · subst J
      simp only [Finset.prod_empty, Finset.sum_const, Nat.card_Ioc, Nat.sub_zero,
        nsmul_eq_mul, mul_one, hSS]
      have hf := Nat.floor_le hy
      have hf' := Nat.lt_floor_add_one y
      have hab : |(⌊y⌋₊ : ℝ) - y| ≤ 1 := by rw [abs_le]; constructor <;> linarith
      exact hab.trans (by nlinarith)
    · exact (hl_finset hHL hN₀ J (Finset.nonempty_iff_ne_empty.mpr he)
        ((Finset.card_le_card (Finset.mem_powerset.mp hJ)).trans hD)
        (fun d hv => hd d (Finset.mem_powerset.mp hJ hv)) y hy hyN).trans
          (by nlinarith [Real.rpow_nonneg (show 0 ≤ N by linarith) (1 / 2 + ε)])
  have heq : (∑ n ∈ Finset.Ioc 0 ⌊y⌋₊,
      ∏ d ∈ D, (ArithmeticFunction.vonMangoldt (n + d) - 1)) - y * center SS D =
      ∑ J ∈ D.powerset, (-1 : ℝ) ^ (D.card - J.card) *
        ((∑ n ∈ Finset.Ioc 0 ⌊y⌋₊,
          ∏ d ∈ J, ArithmeticFunction.vonMangoldt (n + d)) - y * SS J) := by
    simp_rw [centred_expansion]
    rw [Finset.sum_comm]
    simp only [center, centerFinite, Finset.mul_sum, mul_sub, Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl; intro J _; ring
  rw [heq]
  calc
    _ ≤ ∑ J ∈ D.powerset, (A + 1) * N ^ (1 / 2 + ε) := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro J hJ
      simpa only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul] using herr J hJ
    _ = (2 : ℝ) ^ D.card * ((A + 1) * N ^ (1 / 2 + ε)) := by
      simp [Finset.card_powerset]
    _ ≤ _ := by
      have hp : (2 : ℝ) ^ D.card ≤ 16 := by
        exact (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hD).trans_eq (by norm_num)
      nlinarith [mul_le_mul_of_nonneg_right hp
        (show 0 ≤ (A + 1) * N ^ (1 / 2 + ε) by positivity)]

/-- Centred correlations tested against a fixed polynomial in the logarithm have a uniform
BV discrepancy bound. The constant precedes the shifts and the weight. -/
theorem centred_polynomial_log_correlation (SS : Finset ℕ → ℝ) (β : ℝ)
    (hSS : SS ∅ = 1) (hHL : HL4 SS β) (M ε : ℝ) (hM : 1 ≤ M) (hε : 0 < ε)
    (p : Polynomial ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℝ in atTop,
      2 ≤ N ∧ ∀ D : Finset ℕ, D.card ≤ 4 →
        (∀ d ∈ D, 1 ≤ d ∧ (d : ℝ) ≤ M * N ^ β) →
        ∀ B : ℝ, ∀ w : ℝ → ℝ, BVBound w B →
          |(∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊,
              w ((n : ℝ) / N) * p.eval (Real.log n) *
                ∏ d ∈ D, (ArithmeticFunction.vonMangoldt (n + d) - 1)) -
            center SS D * (∫ x in N..2 * N, w (x / N) * p.eval (Real.log x))| ≤
              C * B * N ^ (1 / 2 + ε) * (1 + Real.log N) ^ p.natDegree := by
  obtain ⟨A, hA, hpartial⟩ := centred_correlation_partial_sums SS β hSS hHL M ε hM hε
  obtain ⟨P, hP, hpoly⟩ := polynomial_log_bv_bound p
  refine ⟨2 * A * P, by positivity, ?_⟩
  filter_upwards [hpartial] with N hN
  have hN0 : 0 ≤ N := by linarith [hN.1]
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by linarith [hN.1])
  refine ⟨hN.1, ?_⟩
  intro D hD hd B w hw
  obtain ⟨U, hU, hbound, hUV⟩ := hw.2.2.2
  let V := (eVariationOn w univ).toReal
  have hV : 0 ≤ V := ENNReal.toReal_nonneg
  have hv : eVariationOn w univ ≤ ENNReal.ofReal V := by
    rw [ENNReal.ofReal_toReal hw.1]
  obtain ⟨hvary, K, hK, hKb, hKV⟩ := hpoly N U V w hN.1 hU hV hw.1 hbound hv
  let f : ℕ → ℝ := fun n => ∏ d ∈ D, (ArithmeticFunction.vonMangoldt (n + d) - 1)
  have hcuts (y : ℝ) (hy : y ∈ Icc N (2 * N)) :
      |(∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊y⌋₊, f n) - center SS D * (y - N)| ≤
        2 * A * N ^ (1 / 2 + ε) := by
    have hN0 : 0 ≤ N := by linarith [hN.1]
    have hy0 : 0 ≤ y := hN0.trans hy.1
    have hsub : Finset.Ioc 0 ⌊N⌋₊ ⊆ Finset.Ioc 0 ⌊y⌋₊ :=
      Finset.Ioc_subset_Ioc_right (Nat.floor_le_floor hy.1)
    have hs : Finset.Ioc 0 ⌊y⌋₊ \ Finset.Ioc 0 ⌊N⌋₊ = Finset.Ioc ⌊N⌋₊ ⌊y⌋₊ := by
      ext n; simp only [Finset.mem_sdiff, Finset.mem_Ioc]; omega
    have hsum : (∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊y⌋₊, f n) =
        (∑ n ∈ Finset.Ioc 0 ⌊y⌋₊, f n) - ∑ n ∈ Finset.Ioc 0 ⌊N⌋₊, f n := by
      rw [← hs, Finset.sum_sdiff_eq_sub hsub]
    rw [hsum]
    have he : (∑ n ∈ Finset.Ioc 0 ⌊y⌋₊, f n) - (∑ n ∈ Finset.Ioc 0 ⌊N⌋₊, f n) -
        center SS D * (y - N) =
        ((∑ n ∈ Finset.Ioc 0 ⌊y⌋₊, f n) - y * center SS D) -
        ((∑ n ∈ Finset.Ioc 0 ⌊N⌋₊, f n) - N * center SS D) := by ring
    rw [he]
    exact (abs_sub _ _).trans (by
      have h1 := hN.2 D hD hd y hy0 (by linarith [hy.2])
      have h2 := hN.2 D hD hd N hN0 (by linarith)
      change |(∑ n ∈ Finset.Ioc 0 ⌊y⌋₊, f n) - y * center SS D| +
        |(∑ n ∈ Finset.Ioc 0 ⌊N⌋₊, f n) - N * center SS D| ≤ _
      linarith)
  have hmain := bv_correlation_discrepancy N (center SS D)
    (2 * A * N ^ (1 / 2 + ε)) K f
    (fun x => w (x / N) * p.eval (Real.log x)) hN.1 (by positivity) hK hvary hKb hcuts
  apply hmain.trans
  calc
    _ ≤ (2 * A * N ^ (1 / 2 + ε)) * (P * (U + V) * (1 + Real.log N) ^ p.natDegree) :=
      mul_le_mul_of_nonneg_left hKV (by positivity)
    _ ≤ (2 * A * N ^ (1 / 2 + ε)) * (P * B * (1 + Real.log N) ^ p.natDegree) := by
      gcongr
    _ = _ := by ring

end
end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
