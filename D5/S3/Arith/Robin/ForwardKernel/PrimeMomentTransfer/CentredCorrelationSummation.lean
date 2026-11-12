/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/CentredCorrelationSummation
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/CentredCorrelationSummation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Mean-square prime correlations transfer at every bounded order to centred polynomial logarithmic BV sums. -/

import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.CentredProductExpansion
import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.MeanSquareCorrelation
import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.TupleSubsetMultiplicity
import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.BVCorrelationSummation

/-! Inclusion–exclusion and BV summation for centred prime correlations. -/

open scoped BigOperators Topology
open Set Filter MeasureTheory

namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
noncomputable section
set_option autoImplicit false

private def centredError (SS : Finset ℕ → ℝ) (y : ℝ) (D : Finset ℕ) : ℝ :=
  (∑ n ∈ Finset.Ioc 0 ⌊y⌋₊,
    ∏ d ∈ D, (ArithmeticFunction.vonMangoldt (n + d) - 1)) - y * center SS D

private lemma centred_error_le (SS : Finset ℕ → ℝ) (y : ℝ) (D : Finset ℕ) :
    |centredError SS y D| ≤ ∑ R ∈ D.powerset, |correlationError SS y R| := by
  have heq : centredError SS y D =
      ∑ R ∈ D.powerset, (-1 : ℝ) ^ (D.card - R.card) * correlationError SS y R := by
    simp only [centredError, correlationError, prod_sub_one_expansion]
    rw [Finset.sum_comm]
    simp only [center, centerFinite, Finset.mul_sum, mul_sub, Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro R _
    ring
  rw [heq]
  simpa only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul] using
    Finset.abs_sum_le_sum_abs (fun R =>
      (-1 : ℝ) ^ (D.card - R.card) * correlationError SS y R) D.powerset

private lemma powerset_centred_error_le (SS : Finset ℕ → ℝ) (y : ℝ)
    (D : Finset ℕ) :
    (∑ J ∈ D.powerset, |centredError SS y J|) ≤
      (2 : ℝ) ^ D.card * ∑ R ∈ D.powerset, |correlationError SS y R| := by
  calc
    _ ≤ ∑ _J ∈ D.powerset, ∑ R ∈ D.powerset, |correlationError SS y R| := by
      apply Finset.sum_le_sum
      intro J hJ
      exact (centred_error_le SS y J).trans
        (Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.powerset_mono.mpr (Finset.mem_powerset.mp hJ))
          (fun _ _ _ => abs_nonneg _))
    _ = (2 : ℝ) ^ D.card * ∑ R ∈ D.powerset, |correlationError SS y R| := by
      simp [Finset.card_powerset]

private theorem centred_tuple_partial_sums {q : ℕ} (SS : Finset ℕ → ℝ) (β : ℝ)
    (hSS : SS ∅ = 1) (hMS : MeanSquareHL q SS β) (M ε : ℝ) (hM : 1 ≤ M) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℝ in atTop,
      2 ≤ N ∧ ∀ k : ℕ, k ≤ q → ∀ K : ℕ, 1 ≤ K → (K : ℝ) ≤ M * N ^ β →
        ∀ T : Finset (Fin k → ℕ),
        T ⊆ Fintype.piFinset (fun _ => Finset.Ioc 0 K) →
        ∀ y : ℝ, y ∈ Icc N (2 * N) →
          (∑ d ∈ T, ∑ J ∈ (Finset.univ.image d).powerset, |centredError SS y J|) ≤
            C * N ^ (1 / 2 + ε) * (K : ℝ) ^ k := by
  classical
  obtain ⟨A, hA, hbound⟩ := meanSquare_correlation_l1 SS β hMS M ε hM hε
  refine ⟨2 ^ q * ((q + 1 : ℕ) : ℝ) ^ q * (q + 1) * (A + 1), by positivity, ?_⟩
  filter_upwards [hbound] with N hN
  refine ⟨hN.1, ?_⟩
  intro k hk K hK hKN T hT y hy
  have hkq : k ≤ q := hk
  have hN0 : 0 ≤ N := by linarith [hN.1]
  have hy0 : 0 ≤ y := hN0.trans hy.1
  have hpow : 1 ≤ N ^ (1 / 2 + ε) :=
    Real.one_le_rpow (by linarith [hN.1]) (by linarith)
  have herr (r : ℕ) (hr : r ∈ Finset.range (k + 1)) :
      (∑ R ∈ (Finset.Ioc 0 K).powersetCard r, |correlationError SS y R|) ≤
        (A + 1) * N ^ (1 / 2 + ε) * (K : ℝ) ^ r := by
    by_cases hr0 : r = 0
    · subst r
      simp only [Finset.powersetCard_zero, Finset.sum_singleton,
        correlationError, Finset.prod_empty, Finset.sum_const, Nat.card_Ioc,
        Nat.sub_zero, nsmul_eq_mul, mul_one, hSS, pow_zero]
      have hf := Nat.floor_le hy0
      have hf' := Nat.lt_floor_add_one y
      have hab : |(⌊y⌋₊ : ℝ) - y| ≤ 1 := by
        rw [abs_le]; constructor <;> linarith
      exact hab.trans (by nlinarith)
    · exact (hN.2 r (by omega) (by have := Finset.mem_range.mp hr; omega)
        K hK hKN y hy.1 hy.2).trans (by
          nlinarith [Real.rpow_nonneg hN0 (1 / 2 + ε),
            pow_nonneg (Nat.cast_nonneg K : (0 : ℝ) ≤ K) r])
  have hraw := sum_tuple_subsets_le k (Finset.Ioc 0 K) T hT
    (fun R => |correlationError SS y R|) (fun _ => abs_nonneg _)
  have hsum : (∑ r ∈ Finset.range (k + 1), (K : ℝ) ^ (k - r) *
      ∑ R ∈ (Finset.Ioc 0 K).powersetCard r, |correlationError SS y R|) ≤
        (q + 1) * ((A + 1) * N ^ (1 / 2 + ε) * (K : ℝ) ^ k) := by
    calc
      _ ≤ ∑ _r ∈ Finset.range (k + 1),
          (A + 1) * N ^ (1 / 2 + ε) * (K : ℝ) ^ k := by
        apply Finset.sum_le_sum
        intro r hr
        calc
          _ ≤ (K : ℝ) ^ (k - r) *
              ((A + 1) * N ^ (1 / 2 + ε) * (K : ℝ) ^ r) :=
            mul_le_mul_of_nonneg_left (herr r hr) (by positivity)
          _ = _ := by
            have hrk : r ≤ k := by have := Finset.mem_range.mp hr; omega
            rw [show (K : ℝ) ^ (k - r) *
                ((A + 1) * N ^ (1 / 2 + ε) * (K : ℝ) ^ r) =
              (A + 1) * N ^ (1 / 2 + ε) * ((K : ℝ) ^ (k-r) * (K : ℝ) ^ r) by ring,
              ← pow_add, Nat.sub_add_cancel hrk]
      _ ≤ _ := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega : k + 1 ≤ q + 1))
          (by positivity)
  calc
    _ ≤ ∑ d ∈ T, (2 : ℝ) ^ q * ∑ R ∈ (Finset.univ.image d).powerset,
        |correlationError SS y R| := by
      apply Finset.sum_le_sum
      intro d _
      exact (powerset_centred_error_le SS y _).trans
        (mul_le_mul_of_nonneg_right
          (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
            (Finset.card_image_le.trans (by simpa using hkq)))
          (Finset.sum_nonneg (fun _ _ => abs_nonneg _)))
    _ = 2 ^ q * ∑ d ∈ T, ∑ R ∈ (Finset.univ.image d).powerset,
        |correlationError SS y R| := (Finset.mul_sum ..).symm
    _ ≤ 2 ^ q * ((k : ℝ) ^ k *
        ∑ r ∈ Finset.range (k + 1), (K : ℝ) ^ (k - r) *
        ∑ R ∈ (Finset.Ioc 0 K).powersetCard r, |correlationError SS y R|) := by
      simpa only [Nat.card_Ioc, Nat.sub_zero] using mul_le_mul_of_nonneg_left hraw
        (by positivity : (0 : ℝ) ≤ 2 ^ q)
    _ ≤ 2 ^ q * (((q + 1 : ℕ) : ℝ) ^ q *
        ((q + 1) * ((A + 1) * N ^ (1 / 2 + ε) * (K : ℝ) ^ k))) := by
      have hfactor : (k : ℝ) ^ k ≤ ((q + 1 : ℕ) : ℝ) ^ q := by
        exact_mod_cast ((Nat.pow_le_pow_left (by omega : k ≤ q + 1) k).trans
          (Nat.pow_le_pow_right (by omega : 1 ≤ q + 1) hkq))
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul hfactor hsum (Finset.sum_nonneg (fun _ _ => by positivity))
          (by positivity)) (by positivity)
    _ = _ := by ring

/-- A common polynomial logarithmic BV weight can be applied after summing centred
correlations over interval-box tuples. The constant is uniform in the tuple subfamily and
in the assignment of coefficient polynomials. -/
theorem centred_polynomial_log_correlation {q : ℕ} (SS : Finset ℕ → ℝ) (β : ℝ)
    (hSS : SS ∅ = 1) (hMS : MeanSquareHL q SS β) (M ε : ℝ) (hM : 1 ≤ M) (hε : 0 < ε)
    (p : Polynomial ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℝ in atTop,
      2 ≤ N ∧ ∀ k : ℕ, k ≤ q → ∀ K : ℕ, 1 ≤ K → (K : ℝ) ≤ M * N ^ β →
        ∀ T : Finset (Fin k → ℕ),
        T ⊆ Fintype.piFinset (fun _ => Finset.Ioc 0 K) →
        ∀ q : (Fin k → ℕ) → Finset ℕ → Polynomial ℝ,
        ∀ B : ℝ, ∀ w : ℝ → ℝ, BVBound w B →
          |(∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊,
              (w ((n : ℝ) / N) * p.eval (Real.log n)) *
                ∑ d ∈ T, ∑ J ∈ (Finset.univ.image d).powerset,
                  if q d J = p then
                    ∏ e ∈ J, (ArithmeticFunction.vonMangoldt (n + e) - 1) else 0) -
            (∑ d ∈ T, ∑ J ∈ (Finset.univ.image d).powerset,
              if q d J = p then center SS J else 0) *
                (∫ x in N..2 * N, w (x / N) * p.eval (Real.log x))| ≤
              C * B * N ^ (1 / 2 + ε) * (K : ℝ) ^ k *
                (1 + Real.log N) ^ p.natDegree := by
  classical
  obtain ⟨A, hA, hpartial⟩ := centred_tuple_partial_sums SS β hSS hMS M ε hM hε
  obtain ⟨P, hP, hpoly⟩ := polynomial_log_bv_bound p
  refine ⟨2 * A * P, by positivity, ?_⟩
  filter_upwards [hpartial] with N hN
  have hN0 : 0 ≤ N := by linarith [hN.1]
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by linarith [hN.1])
  refine ⟨hN.1, ?_⟩
  intro k hk K hK hKN T hT q B w hw
  let f : ℕ → ℝ := fun n => ∑ d ∈ T, ∑ J ∈ (Finset.univ.image d).powerset,
    if q d J = p then ∏ e ∈ J, (ArithmeticFunction.vonMangoldt (n + e) - 1) else 0
  let c : ℝ := ∑ d ∈ T, ∑ J ∈ (Finset.univ.image d).powerset,
    if q d J = p then center SS J else 0
  have hpref (y : ℝ) (hy : y ∈ Icc N (2 * N)) :
      |(∑ n ∈ Finset.Ioc 0 ⌊y⌋₊, f n) - y * c| ≤
        A * N ^ (1 / 2 + ε) * (K : ℝ) ^ k := by
    have heq : (∑ n ∈ Finset.Ioc 0 ⌊y⌋₊, f n) - y * c =
        ∑ d ∈ T, ∑ J ∈ (Finset.univ.image d).powerset,
          if q d J = p then centredError SS y J else 0 := by
      dsimp [f, c]
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro d _
      rw [Finset.sum_comm]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro J _
      split_ifs <;> simp [centredError]
    rw [heq]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply (Finset.sum_le_sum (fun d _ => Finset.abs_sum_le_sum_abs _ _)).trans
    apply le_trans _ (hN.2 k hk K hK hKN T hT y hy)
    apply Finset.sum_le_sum
    intro d _
    apply Finset.sum_le_sum
    intro J _
    split_ifs <;> simp
  have hcuts (y : ℝ) (hy : y ∈ Icc N (2 * N)) :
      |(∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊y⌋₊, f n) - c * (y - N)| ≤
        2 * A * N ^ (1 / 2 + ε) * (K : ℝ) ^ k := by
    have hsub : Finset.Ioc 0 ⌊N⌋₊ ⊆ Finset.Ioc 0 ⌊y⌋₊ :=
      Finset.Ioc_subset_Ioc_right (Nat.floor_le_floor hy.1)
    have hs : Finset.Ioc 0 ⌊y⌋₊ \ Finset.Ioc 0 ⌊N⌋₊ = Finset.Ioc ⌊N⌋₊ ⌊y⌋₊ := by
      ext n; simp only [Finset.mem_sdiff, Finset.mem_Ioc]; omega
    rw [← hs, Finset.sum_sdiff_eq_sub hsub]
    have he : (∑ n ∈ Finset.Ioc 0 ⌊y⌋₊, f n) - (∑ n ∈ Finset.Ioc 0 ⌊N⌋₊, f n) -
        c * (y - N) = ((∑ n ∈ Finset.Ioc 0 ⌊y⌋₊, f n) - y * c) -
          ((∑ n ∈ Finset.Ioc 0 ⌊N⌋₊, f n) - N * c) := by ring
    rw [he]
    exact (abs_sub _ _).trans (by
      have h1 := hpref y hy
      have h2 := hpref N ⟨le_rfl, by linarith [hN.1]⟩
      linarith)
  obtain ⟨U, hU, hbound, hUV⟩ := hw.2.2.2
  let V := (eVariationOn w univ).toReal
  have hV : 0 ≤ V := ENNReal.toReal_nonneg
  have hv : eVariationOn w univ ≤ ENNReal.ofReal V := by
    rw [ENNReal.ofReal_toReal hw.1]
  obtain ⟨hvary, L, hL, hLb, hLV⟩ := hpoly N U V w hN.1 hU hV hw.1 hbound hv
  have hmain := bv_correlation_discrepancy N c
    (2 * A * N ^ (1 / 2 + ε) * (K : ℝ) ^ k) L f
    (fun x => w (x / N) * p.eval (Real.log x)) hN.1 (by positivity) hL hvary hLb hcuts
  apply hmain.trans
  calc
    _ ≤ (2 * A * N ^ (1 / 2 + ε) * (K : ℝ) ^ k) *
        (P * (U + V) * (1 + Real.log N) ^ p.natDegree) :=
      mul_le_mul_of_nonneg_left hLV (by positivity)
    _ ≤ (2 * A * N ^ (1 / 2 + ε) * (K : ℝ) ^ k) *
        (P * B * (1 + Real.log N) ^ p.natDegree) := by gcongr
    _ = _ := by ring

end
end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
