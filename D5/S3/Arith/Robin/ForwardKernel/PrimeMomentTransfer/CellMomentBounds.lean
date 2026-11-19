/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/CellMomentBounds
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/CellMomentBounds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Mean-square prime correlations: Cell sampling has measurable normalized increments and uniform second and fourth moment bounds. -/

import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.DiscreteFourthBound
import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.DiscreteSecondBound
import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.CellQuadrature
import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.ContinuousSampling
import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.NormalizationAlgebra
import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.UniformRates
import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.CutoffWeights

/-! Pointwise and fourth moment bounds for continuous and floor sampled increments. -/

open Set Filter MeasureTheory
open scoped Topology BigOperators
namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
noncomputable section
set_option autoImplicit false

/-- Lebesgue measure on the unit dyadic interval has total mass one. -/
theorem unit_dyadic_probability : IsProbabilityMeasure (volume.restrict (Icc (1 : ℝ) 2)) := by
  constructor
  norm_num

private theorem p_S_raw_bound (N H M a b : ℝ) (n : ℕ) (hN : 2 ≤ N)
    (hH : 1 ≤ H) (_hM : 1 ≤ M) (hMH : M * H ≤ N)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ M) (hn : n ≤ ⌈2 * N⌉₊) :
    |S H a b n| ≤ (M + 1) * H * (Real.log (4 * N) + 1) := by
  have hN0 : 0 < N := by linarith
  have hH0 : 0 ≤ H := by linarith
  have hb0 : 0 ≤ b := ha.trans hab
  have hlog : 0 ≤ Real.log (4 * N) := Real.log_nonneg (by linarith)
  have hcount : ((points H a b).card : ℝ) ≤ (M + 1) * H := by
    exact (geom_points_card_le M H a b hH0 ha hab hb).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hH0)
  calc
    |S H a b n| ≤ ∑ d ∈ points H a b, |ArithmeticFunction.vonMangoldt (n + d) - 1| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ points H a b, (Real.log (4 * N) + 1) := by
      apply Finset.sum_le_sum
      intro d hd
      obtain ⟨hdlo, hdhi⟩ := Finset.mem_Ioc.mp hd
      have hd1 : 1 ≤ n + d := by omega
      have hdR : (d : ℝ) ≤ M * H :=
        (Nat.cast_le.mpr hdhi).trans ((Nat.floor_le (mul_nonneg hb0 hH0)).trans
          (mul_le_mul_of_nonneg_right hb hH0))
      have hnR : (n : ℝ) < 2 * N + 1 :=
        (Nat.cast_le.mpr hn).trans_lt (Nat.ceil_lt_add_one (by positivity))
      have hnd : ((n + d : ℕ) : ℝ) ≤ 4 * N := by push_cast; linarith
      have hv : ArithmeticFunction.vonMangoldt (n + d) ≤ Real.log (4 * N) :=
        ArithmeticFunction.vonMangoldt_le_log.trans
          (Real.strictMonoOn_log.monotoneOn (show 0 < ((n + d : ℕ) : ℝ) by exact_mod_cast (show 0 < n + d by omega))
            (show 0 < 4 * N by positivity) hnd)
      exact (abs_sub _ _).trans (by
        rw [abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, abs_one]
        linarith)
    _ ≤ (M + 1) * H * (Real.log (4 * N) + 1) := by
      simpa only [Finset.sum_const, nsmul_eq_mul] using
        mul_le_mul_of_nonneg_right hcount (by positivity)

private theorem p_S_bound (N H M a b : ℝ) (n : ℕ) (hN : 2 ≤ N)
    (hL : 1 ≤ Real.log N) (hH : 1 ≤ H) (hM : 1 ≤ M) (hMH : M * H ≤ N)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ M)
    (_hnlo : ⌊N⌋₊ ≤ n) (hn : n ≤ ⌈2 * N⌉₊) :
    |S H a b n / Real.sqrt (H * Real.log N)| ≤ 4 * (M + 1) * Real.sqrt (H * Real.log N) := by
  have hQ : 0 < Real.sqrt (H * Real.log N) := Real.sqrt_pos.mpr (by positivity)
  have hlog4 : Real.log 4 ≤ 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hl : Real.log (4 * N) + 1 ≤ 4 * Real.log N := by
    rw [Real.log_mul (by norm_num) (by linarith)]
    linarith
  rw [abs_div, abs_of_pos hQ, div_le_iff₀ hQ]
  calc
    _ ≤ (M + 1) * H * (Real.log (4 * N) + 1) := p_S_raw_bound N H M a b n hN hH hM hMH ha hab hb hn
    _ ≤ (M + 1) * H * (4 * Real.log N) := mul_le_mul_of_nonneg_left hl (by positivity)
    _ = 4 * (M + 1) * Real.sqrt (H * Real.log N) * Real.sqrt (H * Real.log N) := by
      rw [mul_assoc (4 * (M + 1)), Real.mul_self_sqrt (by positivity)]
      ring

/-- Normalized discrete and continuous increments are bounded on the dyadic interval. -/
theorem normalized_crude_bounds (N H M : ℝ) (hN : 2 ≤ N) (hL : 1 ≤ Real.log N)
    (hH : 1 ≤ H) (hM : 1 ≤ M) (hMH : M * H ≤ N) :
    (∀ (a b : ℝ) (n : ℕ), 0 ≤ a → a ≤ b → b ≤ M →
      ⌊N⌋₊ ≤ n → n ≤ ⌈2 * N⌉₊ →
        |S H a b n / Real.sqrt (H * Real.log N)| ≤ 4 * (M + 1) * Real.sqrt (H * Real.log N)) ∧
    (∀ a b t : ℝ, 0 ≤ a → a ≤ b → b ≤ M → t ∈ Icc (1 : ℝ) 2 →
      |Z H a b (N * t) N| ≤ 4 * (M + 1) * Real.sqrt (H * Real.log N) +
        (2 * Real.log (4 * N) + 2) / Real.sqrt (H * Real.log N)) := by
  refine ⟨fun a b n ha hab hb hnlo hnhi =>
    p_S_bound N H M a b n hN hL hH hM hMH ha hab hb hnlo hnhi, ?_⟩
  intro a b t ha hab hb ht
  have hx : N * t ∈ Icc N (2 * N) := by constructor <;> nlinarith [ht.1, ht.2]
  have hnlo : ⌊N⌋₊ ≤ ⌊N * t⌋₊ := Nat.floor_mono hx.1
  have hnhi : ⌊N * t⌋₊ ≤ ⌈2 * N⌉₊ :=
    (Nat.floor_mono hx.2).trans (Nat.floor_le_ceil _)
  have hQ : 0 < Real.sqrt (H * Real.log N) := Real.sqrt_pos.mpr (by positivity)
  have hp := sampling_pointwise hN hH ha hab hb hMH hx
  have he : |Z H a b (N * t) N - S H a b ⌊N * t⌋₊ / Real.sqrt (H * Real.log N)| ≤
      (2 * Real.log (4 * N) + 2) / Real.sqrt (H * Real.log N) := by
    rw [Z, ← sub_div, abs_div, abs_of_pos hQ]
    exact div_le_div_of_nonneg_right hp hQ.le
  calc
    _ ≤ |Z H a b (N * t) N - S H a b ⌊N * t⌋₊ / Real.sqrt (H * Real.log N)| +
        |S H a b ⌊N * t⌋₊ / Real.sqrt (H * Real.log N)| := by
      simpa only [sub_zero] using abs_sub_le (Z H a b (N * t) N)
        (S H a b ⌊N * t⌋₊ / Real.sqrt (H * Real.log N)) 0
    _ ≤ _ := by
      linarith [p_S_bound N H M a b ⌊N * t⌋₊ hN hL hH hM hMH ha hab hb hnlo hnhi]

/-- The continuous and cell increments belong to L4 on the same unit interval. -/
theorem sampling_memLp (N H M a b : ℝ) (hN : 2 ≤ N) (hL : 1 ≤ Real.log N)
    (hH : 1 ≤ H) (hM : 1 ≤ M) (hMH : M * H ≤ N)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ M) :
    MemLp (fun t => Z H a b (N * t) N) 4 (volume.restrict (Icc (1 : ℝ) 2)) ∧
    MemLp (fun t => S H a b ⌊N * t⌋₊ / Real.sqrt (H * Real.log N)) 4
      (volume.restrict (Icc (1 : ℝ) 2)) := by
  have hbnd := normalized_crude_bounds N H M hN hL hH hM hMH
  have hmZ : Measurable (fun t => Z H a b (N * t) N) := by
    unfold Z Delta
    have hpsi := Chebyshev.psi_mono.measurable
    fun_prop
  have hmS : Measurable (fun t => S H a b ⌊N * t⌋₊ / Real.sqrt (H * Real.log N)) :=
    ((measurable_of_countable (S H a b)).comp
      (Nat.measurable_floor.comp (measurable_const.mul measurable_id))).div_const _
  constructor
  · apply MemLp.of_bound hmZ.aestronglyMeasurable
      (4 * (M + 1) * Real.sqrt (H * Real.log N) + (2 * Real.log (4 * N) + 2) / Real.sqrt (H * Real.log N))
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact (Real.norm_eq_abs _).le.trans (hbnd.2 a b t ha hab hb ht)
  · apply MemLp.of_bound hmS.aestronglyMeasurable (4 * (M + 1) * Real.sqrt (H * Real.log N))
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have hx : N * t ∈ Icc N (2 * N) := by constructor <;> nlinarith [ht.1, ht.2]
    exact (Real.norm_eq_abs _).le.trans (hbnd.1 a b _ ha hab hb
      (Nat.floor_mono hx.1) ((Nat.floor_mono hx.2).trans (Nat.floor_le_ceil _)))

private theorem p_cell_from_sum (p : ℕ) (hp : p = 2 ∨ p = 4) (N H M C : ℝ) (hN : 2 ≤ N)
    (hL : 1 ≤ Real.log N) (hH : 1 ≤ H) (hM : 1 ≤ M) (hMH : M * H ≤ N)
    (_hC : 0 ≤ C)
    (hdisc : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ M →
      (∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊, |S H a b n| ^ p) ≤ C * N * (H * Real.log N) ^ (p / 2))
    (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ M) :
    (∫ t in (1 : ℝ)..2, |S H a b ⌊N * t⌋₊ / Real.sqrt (H * Real.log N)| ^ p) ≤
      C + 9 * (4 * (M + 1)) ^ p * (H * Real.log N) ^ (p / 2) / N := by
  have hN0 : 0 < N := by linarith
  have hH0 : 0 < H := by linarith
  have hL0 : 0 < Real.log N := by linarith
  have hQ0 : 0 < Real.sqrt (H * Real.log N) := Real.sqrt_pos.mpr (by positivity)
  have hQ4 : Real.sqrt (H * Real.log N) ^ p = (H * Real.log N) ^ (p / 2) := by
    rcases hp with rfl | rfl
    · norm_num [Real.sq_sqrt (by positivity : 0 ≤ H * Real.log N)]
    · exact (normalizer_powers H (Real.log N) hH0 hL0).2.2.2
  let F : ℕ → ℝ := fun n => |S H a b n / Real.sqrt (H * Real.log N)| ^ p
  let A : ℝ := (4 * (M + 1)) ^ p * (H * Real.log N) ^ (p / 2)
  let w : ℝ → ℝ := (Icc (1 : ℝ) 2).indicator (fun _ => 1)
  have hF : ∀ n, ⌊N⌋₊ ≤ n → n ≤ ⌈2 * N⌉₊ → |F n| ≤ A := by
    intro n hnlo hnhi
    have hs := p_S_bound N H M a b n hN hL hH hM hMH ha hab hb hnlo hnhi
    have hp := pow_le_pow_left₀ (abs_nonneg _) hs p
    simpa only [F, A, abs_pow, abs_abs, mul_pow, hQ4] using hp
  have hnorm (n : ℕ) : F n = |S H a b n| ^ p / (H * Real.log N) ^ (p / 2) := by
    dsimp [F]
    rw [abs_div, div_pow, abs_of_pos hQ0, hQ4]
  have hsum : (∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊, F n) ≤ C * N := by
    simp_rw [hnorm, ← Finset.sum_div]
    exact (div_le_iff₀ (by positivity : 0 < (H * Real.log N) ^ (p / 2))).mpr (hdisc a b ha hab hb)
  have hquad := cell_quadrature N A 3 F w hN (by dsimp [A]; positivity)
    (cutoff_bv 1 2 le_rfl (by norm_num) le_rfl) hF
  have hwx (x : ℝ) (hx : x ∈ Icc N (2 * N)) : w (x / N) = 1 := by
    apply Set.indicator_of_mem
    exact ⟨(le_div_iff₀ hN0).mpr (by linarith [hx.1]),
      (div_le_iff₀ hN0).mpr hx.2⟩
  have hint : (∫ x in N..2 * N, w (x / N) * F ⌊x⌋₊) = ∫ x in N..2 * N, F ⌊x⌋₊ := by
    apply intervalIntegral.integral_congr
    intro x hx
    dsimp only
    rw [hwx x (by simpa only [uIcc_of_le (by linarith : N ≤ 2 * N)] using hx), one_mul]
  have hsumeq : (∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊, w ((n : ℝ) / N) * F n) =
      ∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊, F n := by
    apply Finset.sum_congr rfl
    intro n hn
    obtain ⟨hnlo, hnhi⟩ := Finset.mem_Ioc.mp hn
    rw [hwx n ⟨((Nat.floor_lt hN0.le).mp hnlo).le,
      (Nat.le_floor_iff (by positivity)).mp hnhi⟩, one_mul]
  rw [hint, hsumeq] at hquad
  have hi : (∫ x in N..2 * N, F ⌊x⌋₊) ≤ C * N + 9 * A := by
    linarith [(le_abs_self _).trans hquad]
  have hscale : (∫ t in (1 : ℝ)..2, F ⌊N * t⌋₊) = (∫ x in N..2 * N, F ⌊x⌋₊) / N := by
    simpa only [mul_one, mul_comm N 2, smul_eq_mul, inv_mul_eq_div] using
      intervalIntegral.integral_comp_mul_left (fun x => F ⌊x⌋₊) hN0.ne' (a := 1) (b := 2)
  change (∫ t in (1 : ℝ)..2, F ⌊N * t⌋₊) ≤ _
  rw [hscale]
  calc
    _ ≤ (C * N + 9 * A) / N := div_le_div_of_nonneg_right hi hN0.le
    _ = _ := by dsimp [A]; field_simp

/-- Cell fourth moments are uniformly bounded over the polynomial length band. -/
theorem uniform_cell_fourth (SS : Finset ℕ → ℝ) (α β M : ℝ)
    (hα : 0 < α) (hαβ : α < β) (hβ : β < 1 / 4)
    (hSS : SS ∅ = 1) (hSS1 : ∀ d, SS {d} = 1)
    (hMS : MeanSquareHL4 SS β) (hcor : IntervalCorrelations SS) (hM : 1 ≤ M) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ N : ℝ in atTop,
      ∀ H : ℕ, N ^ α ≤ (H : ℝ) → (H : ℝ) ≤ N ^ β →
      ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ M →
        (∫ t in (1 : ℝ)..2, |S H a b ⌊N * t⌋₊ / Real.sqrt ((H : ℝ) * Real.log N)| ^ 4) ≤ C := by
  obtain ⟨C, hC, hdisc⟩ := uniform_discrete_fourth_bound SS α β M
    hα hαβ hβ hSS hSS1 hMS hcor hM
  have hp : 0 ≤ (4 * (M + 1)) ^ 4 := by positivity
  refine ⟨C + 9 * (4 * (M + 1)) ^ 4 + 1, by linarith, ?_⟩
  filter_upwards [hdisc, range_geometry α β M hα (by linarith) (by linarith),
    cell_rate β 1 4 (by linarith) (by linarith) (by norm_num) zero_lt_one]
    with N hdisc hgeom hrate
  intro H hHlo hHhi a b ha hab hb
  obtain ⟨hH, _hHN, hMH⟩ := hgeom.2.2 H hHlo hHhi
  have hH1 : 1 ≤ (H : ℝ) := by linarith
  have hsmall : ((H : ℝ) * Real.log N) ^ 2 / N ≤ 1 := by
    simpa only [Nat.cast_ofNat, show (4 : ℝ) / 2 = 2 by norm_num, Real.rpow_two]
      using hrate H hH1 hHhi
  have hbnd := p_cell_from_sum 4 (Or.inr rfl) N H M C hgeom.1 hgeom.2.1 hH1 hM hMH hC
    (hdisc H hHlo hHhi) a b ha hab hb
  calc
    _ ≤ C + 9 * (4 * (M + 1)) ^ 4 * ((H : ℝ) * Real.log N) ^ 2 / N := hbnd
    _ = C + (9 * (4 * (M + 1)) ^ 4) * (((H : ℝ) * Real.log N) ^ 2 / N) := by ring
    _ ≤ C + (9 * (4 * (M + 1)) ^ 4) * 1 :=
      add_le_add (le_refl C) (mul_le_mul_of_nonneg_left hsmall (by positivity))
    _ = C + 9 * (4 * (M + 1)) ^ 4 := by ring
    _ ≤ _ := by linarith

/-- Cell second moments are uniformly bounded on the cubic length range. -/
theorem uniform_cell_second (SS : Finset ℕ → ℝ) (α β M : ℝ)
    (hα : 0 < α) (hαβ : α < β) (hβ : β < 1 / 3)
    (hSS : SS ∅ = 1) (hSS1 : ∀ d, SS {d} = 1)
    (hMS : MeanSquareHL 3 SS β) (hcor : IntervalCorrelations SS) (hM : 1 ≤ M) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ N : ℝ in atTop,
      ∀ H : ℕ, N ^ α ≤ (H : ℝ) → (H : ℝ) ≤ N ^ β →
      ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ M →
        (∫ t in (1 : ℝ)..2, |S H a b ⌊N * t⌋₊ / Real.sqrt ((H : ℝ) * Real.log N)| ^ 2) ≤ C := by
  obtain ⟨C, hC, hdisc⟩ := uniform_discrete_second_bound SS α β M
    hα hαβ hβ hSS hSS1 hMS hcor hM
  refine ⟨C + 9 * (4 * (M + 1)) ^ 2 + 1, by nlinarith [sq_nonneg (4 * (M + 1))], ?_⟩
  filter_upwards [hdisc, range_geometry α β M hα (by linarith) (by linarith),
    cell_rate β 1 2 (by linarith) (by linarith) (by norm_num) zero_lt_one]
    with N hdisc hgeom hrate
  intro H hHlo hHhi a b ha hab hb
  obtain ⟨hH, _, hMH⟩ := hgeom.2.2 H hHlo hHhi
  have hH1 : 1 ≤ (H : ℝ) := by linarith
  have hsmall : ((H : ℝ) * Real.log N) / N ≤ 1 := by
    simpa only [Nat.cast_ofNat, show (2 : ℝ) / 2 = 1 by norm_num, Real.rpow_one]
      using hrate H hH1 hHhi
  have hbnd := p_cell_from_sum 2 (Or.inl rfl) N H M C hgeom.1 hgeom.2.1 hH1 hM hMH hC
    (by simpa only [Nat.reduceDiv, pow_one] using hdisc H hHlo hHhi) a b ha hab hb
  norm_num only [Nat.reduceDiv, pow_one] at hbnd
  calc
    _ ≤ C + 9 * (4 * (M + 1)) ^ 2 * ((H : ℝ) * Real.log N) / N := hbnd
    _ = C + (9 * (4 * (M + 1)) ^ 2) * (((H : ℝ) * Real.log N) / N) := by ring
    _ ≤ C + (9 * (4 * (M + 1)) ^ 2) * 1 := by gcongr
    _ ≤ _ := by linarith

end
end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
