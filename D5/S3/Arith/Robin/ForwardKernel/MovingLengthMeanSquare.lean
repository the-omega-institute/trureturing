/- GID: D5/S3/Arith/Robin/ForwardKernel/MovingLengthMeanSquare
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/MovingLengthMeanSquare
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform operator bounds and cell freezing give the moving-length L¹ profile law. -/

import D5.S3.Arith.Robin.ForwardKernel.MovingLengthCells
import D5.S3.Arith.Robin.ForwardKernel.MovingLengthRegularity
import D5.S3.Arith.Robin.ForwardKernel.MovingIncrementVariance
import D5.S3.Arith.Robin.ForwardKernel.ProfileLengthComparison
import D5.S3.Arith.Robin.ForwardKernel.ProfileDensity
import D5.S3.Arith.Robin.ForwardKernel.ProfileQuadraticForm

/-! Cell freezing followed by L¹ approximation gives the moving profile law. -/

namespace D5.S3.Arith.Robin.ForwardKernel.MovingLengthMeanSquare

open Set MeasureTheory Filter
open scoped Topology BigOperators NNReal
open VarianceTransferDefs VarianceTransfer MovingLengthCells
open MovingLengthRegularity MovingLengthVariance ProfileLengthComparison

noncomputable section

private lemma moving_memLp {E g : ℝ → ℝ} {θ : ℝ}
    (hE : LocallyBoundedMeasurable E) (hg : ProfileIntegrable g) (hθ : 0 < θ)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    MemLp (movingAverage E θ g) 2 (volume.restrict (Ioc a b)) :=
  profileAverage_variable_memLp hE hg (measurable_id.pow_const θ) hab
    (Real.rpow_pos_of_pos ha θ) (fun _x hx =>
      ⟨Real.rpow_le_rpow ha.le hx.1 hθ.le,
        Real.rpow_le_rpow (ha.trans_le hx.1).le hx.2 hθ.le⟩)

private lemma moving_square_bound {E g : ℝ → ℝ} {θ X V : ℝ}
    (hE : LocallyBoundedMeasurable E) (hg : ProfileIntegrable g)
    (hθ : 0 < θ) (hX : 0 < X)
    (hV : ∀ s ∈ Icc (0 : ℝ) 1,
      (∫ x in X..(2 * X), increment E (s * x ^ θ) x ^ 2) ≤ V) :
    (∫ x in X..(2 * X), movingAverage E θ g x ^ 2) ≤
      profileL1 g ^ 2 * V / (X ^ θ) ^ 2 := by
  have hXX : X ≤ 2 * X := by linarith
  let μ := volume.restrict (Ioc X (2 * X))
  have hpow : Continuous (fun x : ℝ => x ^ θ) := Real.continuous_rpow_const hθ.le
  obtain ⟨B, hB, hBb⟩ := hE.2 X (2 * X + (2 * X) ^ θ)
  have hlocal (x : ℝ) (hx : x ∈ Icc X (2 * X)) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      |increment E (s * x ^ θ) x| ≤ 2 * B := by
    have hx0 := hX.trans_le hx.1
    have hp := Real.rpow_pos_of_pos hx0 θ
    have hp' := Real.rpow_le_rpow hx0.le hx.2 hθ.le
    have h₁ := hBb x ⟨hx.1, by linarith [hx.2, Real.rpow_nonneg (by linarith : 0 ≤ 2 * X) θ]⟩
    have h₂ := hBb (x + s * x ^ θ)
      ⟨by nlinarith [hx.1, hs.1], by nlinarith [hx.2, hs.2]⟩
    exact (abs_sub _ _).trans (by linarith)
  have hm : Measurable (fun p : ℝ × ℝ => increment E (p.2 * p.1 ^ θ) p.1) :=
    (hE.1.comp (measurable_fst.add
      (measurable_snd.mul (measurable_fst.pow_const θ)))).sub (hE.1.comp measurable_fst)
  have hi : Integrable (fun p : ℝ × ℝ =>
      |g p.2| * increment E (p.2 * p.1 ^ θ) p.1 ^ 2) (μ.prod unitMeasure) := by
    have hgprod : Integrable (fun p : ℝ × ℝ => |g p.2|) (μ.prod unitMeasure) := by
      simpa only [one_mul] using
        (integrable_const (1 : ℝ) : Integrable (fun _ : ℝ => (1 : ℝ)) μ).mul_prod hg.2.abs
    apply hgprod.mul_bdd (hm.pow_const 2).aestronglyMeasurable
    have hrect : ∀ᵐ p ∂(μ.prod unitMeasure),
        p.1 ∈ Ioc X (2 * X) ∧ p.2 ∈ Ioc (0 : ℝ) 1 := by
      dsimp [μ, unitMeasure]
      rw [Measure.prod_restrict]
      exact ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)
    filter_upwards [hrect] with p hp
    simp only [Real.norm_eq_abs, abs_pow, sq_abs]
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _)
      (hlocal p.1 ⟨hp.1.1.le, hp.1.2⟩ p.2 ⟨hp.2.1.le, hp.2.2⟩) 2
  have hG := hi.integral_prod_left
  have hGb : (∫ x, ∫ s, |g s| * increment E (s * x ^ θ) x ^ 2 ∂unitMeasure ∂μ) ≤
      profileL1 g * V := by
    rw [integral_integral_swap hi]
    simp_rw [integral_const_mul]
    rw [profileL1, ← integral_mul_const]
    apply integral_mono_ae
    · simpa only [integral_const_mul] using hi.integral_prod_right
    · exact hg.2.abs.mul_const V
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      exact mul_le_mul_of_nonneg_left
        (by simpa only [intervalIntegral.integral_of_le hXX] using hV s ⟨hs.1.le, hs.2⟩)
        (abs_nonneg _)
  have hf := (moving_memLp hE hg hθ hX hXX).integrable_sq
  have hL : 0 ≤ profileL1 g := integral_nonneg fun s => abs_nonneg (g s)
  have hH : 0 < X ^ θ := Real.rpow_pos_of_pos hX θ
  calc
    _ ≤ ∫ x, (profileL1 g / (X ^ θ) ^ 2) *
        (∫ s, |g s| * increment E (s * x ^ θ) x ^ 2 ∂unitMeasure) ∂μ := by
      rw [intervalIntegral.integral_of_le hXX]
      apply integral_mono_ae hf (hG.const_mul _)
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      have hx' : x ∈ Icc X (2 * X) := ⟨hx.1.le, hx.2⟩
      have hx0 := hX.trans hx.1
      have hc := profile_cauchy_schwarz hg.2
        (k := fun s => increment E (s * x ^ θ) x)
        ((hm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
        (by positivity : 0 ≤ 2 * B) (by
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
          exact hlocal x hx' s ⟨hs.1.le, hs.2⟩)
      change profileAverage E g (x ^ θ) x ^ 2 ≤ _
      rw [profileAverage_eq_unit_integral, intervalIntegral.integral_of_le zero_le_one, div_pow]
      calc
        _ ≤ (profileL1 g * ∫ s, |g s| * increment E (s * x ^ θ) x ^ 2 ∂unitMeasure) /
            (x ^ θ) ^ 2 := div_le_div_of_nonneg_right hc (sq_nonneg _)
        _ ≤ (profileL1 g * ∫ s, |g s| * increment E (s * x ^ θ) x ^ 2 ∂unitMeasure) /
            (X ^ θ) ^ 2 := by
          apply div_le_div_of_nonneg_left (mul_nonneg hL (integral_nonneg fun s => by positivity))
            (sq_pos_of_pos hH)
          exact pow_le_pow_left₀ hH.le (Real.rpow_le_rpow hX.le hx.1.le hθ.le) 2
        _ = _ := by ring
    _ = (profileL1 g / (X ^ θ) ^ 2) *
        (∫ x, ∫ s, |g s| * increment E (s * x ^ θ) x ^ 2 ∂unitMeasure ∂μ) :=
      integral_const_mul _ _
    _ ≤ (profileL1 g / (X ^ θ) ^ 2) * (profileL1 g * V) :=
      mul_le_mul_of_nonneg_left hGb (by positivity)
    _ = _ := by ring

/-- A single eventual threshold bounds the moving operator on every integrable profile. -/
theorem moving_profile_operator_bound {E : ℝ → ℝ} {α θ β : ℝ}
    (hE : LocallyBoundedMeasurable E) (hB : ValidBand α θ β)
    (hV : CumulativeVarianceBandAsymptoticFor E α β) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℝ in atTop,
      ∀ g : ℝ → ℝ, ProfileIntegrable g →
        Real.sqrt (∫ x in X..(2 * X), movingAverage E θ g x ^ 2) ≤
          C * profileL1 g * Real.sqrt (meanSquareScale θ X) := by
  obtain ⟨K, hK, hKv⟩ := MovingIncrementVariance.moving_increment_square_bound hE hB hV
  refine ⟨Real.sqrt K, Real.sqrt_pos.mpr hK, ?_⟩
  filter_upwards [hKv, eventually_gt_atTop (1 : ℝ)] with X hKv hX
  intro g hg
  have hX0 : 0 < X := by linarith
  have hH := Real.rpow_pos_of_pos hX0 θ
  have hL : 0 ≤ profileL1 g := integral_nonneg fun s => abs_nonneg (g s)
  have hS : 0 ≤ meanSquareScale θ X := by
    exact mul_nonneg (Real.rpow_nonneg hX0.le _) (Real.log_pos hX).le
  have hp : X ^ θ * X ^ (1 - θ) = X := by
    rw [← Real.rpow_add hX0, add_sub_cancel, Real.rpow_one]
  have hb := moving_square_bound hE hg (hB.1.trans hB.2.1) hX0 hKv
  have he : profileL1 g ^ 2 * (K * X * X ^ θ * Real.log X) / (X ^ θ) ^ 2 =
      (Real.sqrt K * profileL1 g * Real.sqrt (meanSquareScale θ X)) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hK.le, Real.sq_sqrt hS]
    unfold meanSquareScale
    have hd : X / X ^ θ = X ^ (1 - θ) :=
      (div_eq_iff hH.ne').mpr (by nlinarith [hp])
    calc
      _ = K * profileL1 g ^ 2 * (X / X ^ θ) * Real.log X := by field_simp
      _ = _ := by rw [hd]; ring
  rw [he] at hb
  exact (Real.sqrt_le_sqrt hb).trans_eq (Real.sqrt_sq (by positivity))

private lemma power_sub_le {θ a b : ℝ} (hθ : θ < 1) (ha : 1 ≤ a) (hab : a ≤ b) :
    b ^ θ - a ^ θ ≤ b - a := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := ha0.trans_le hab
  have hdiv : 1 ≤ b / a := (one_le_div ha0).mpr hab
  have hr := Real.rpow_le_self_of_one_le hdiv hθ.le
  have ha' := Real.rpow_le_self_of_one_le ha hθ.le
  have he : b ^ θ = a ^ θ * (b / a) ^ θ := by
    rw [Real.div_rpow hb0.le ha0.le]
    field_simp
  calc
    _ ≤ a ^ θ * (b / a - 1) := by rw [he]; nlinarith [Real.rpow_nonneg ha0.le θ]
    _ ≤ a * (b / a - 1) := mul_le_mul_of_nonneg_right ha' (by linarith)
    _ = _ := by field_simp

private lemma cell_length_bounds {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    {n j : ℕ} (hn : 0 < n) (hj : j < n)
    {X x : ℝ} (hX : 0 < X)
    (hx : x ∈ Icc (cellPoint n j * X) (cellPoint n (j + 1) * X)) :
    let h := fixedLength θ (cellPoint n j ^ θ) X
    X ^ θ ≤ h ∧ h ≤ 2 * X ^ θ ∧
      x ^ θ ∈ Icc h (h + X ^ θ / n) := by
  have ha := cellPoint_mem hn hj.le
  have hb := cellPoint_mem hn (Nat.succ_le_of_lt hj)
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hH : 0 < X ^ θ := Real.rpow_pos_of_pos hX _
  have hv : x / X ∈ Icc (cellPoint n j) (cellPoint n (j + 1)) :=
    ⟨(le_div_iff₀ hX).mpr hx.1, (div_le_iff₀ hX).mpr hx.2⟩
  have hv0 : 0 < x / X := by linarith [hv.1, ha.1]
  have he : x ^ θ = (x / X) ^ θ * X ^ θ := by
    rw [Real.div_rpow (by nlinarith [hx.1, ha.1] : 0 ≤ x) hX.le]
    exact (div_mul_cancel₀ _ hH.ne').symm
  have hu := power_sub_le hθ1 ha.1 hv.1
  have hstep := cellPoint_step hn j
  have ha0 : 0 < cellPoint n j := by linarith [ha.1]
  have hmono := Real.rpow_le_rpow ha0.le hv.1 hθ0.le
  dsimp only [fixedLength]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact le_mul_of_one_le_left hH.le (Real.one_le_rpow ha.1 hθ0.le)
  · exact mul_le_mul_of_nonneg_right
      ((Real.rpow_le_self_of_one_le ha.1 hθ1.le).trans ha.2) hH.le
  · rw [he]
    exact mul_le_mul_of_nonneg_right hmono hH.le
  · rw [he]
    have hvstep : x / X - cellPoint n j ≤ 1 / (n : ℝ) := by linarith [hv.2]
    have h := mul_le_mul_of_nonneg_right (hu.trans hvstep) hH.le
    linear_combination h

private def cellSquareError (E : ℝ → ℝ) (θ : ℝ) (g : ℝ → ℝ) (n : ℕ) (X : ℝ) : ℝ :=
  ∑ j ∈ Finset.range n, ∫ x in (cellPoint n j * X)..(cellPoint n (j + 1) * X),
    (movingAverage E θ g x -
      profileAverage E g (fixedLength θ (cellPoint n j ^ θ) X) x) ^ 2

private lemma cell_square_error_le {E g : ℝ → ℝ} {θ : ℝ}
    (hE : LocallyBoundedMeasurable E) (hg : ProfileIntegrable g)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) {M K : ℝ} {L : ℝ≥0}
    (hM : 0 ≤ M) (hK : 0 ≤ K)
    (hgM : ∀ s ∈ Icc (0 : ℝ) 1, |g s| ≤ M)
    (hgLip : LipschitzOnWith L g (Icc (0 : ℝ) 1))
    {n : ℕ} (hn : 0 < n) {X : ℝ} (hX : 1 < X)
    (hV : ∀ u ∈ Icc (0 : ℝ) (4 * X ^ θ),
      (∫ x in X..(2 * X), increment E u x ^ 2) ≤ K * X * X ^ θ * Real.log X) :
    cellSquareError E θ g n X ≤
      (2 * ((2 * M + (L : ℝ)) ^ 2 + M ^ 2) * K) / n * meanSquareScale θ X := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hX0 : 0 < X := by linarith
  have hH : 0 < X ^ θ := Real.rpow_pos_of_pos hX0 _
  have hlog : 0 < Real.log X := Real.log_pos hX
  have hp : X ^ θ * X ^ (1 - θ) = X := by
    rw [← Real.rpow_add hX0, add_sub_cancel, Real.rpow_one]
  let A : ℝ := 2 * ((2 * M + (L : ℝ)) ^ 2 + M ^ 2)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hj (j : ℕ) (hj : j ∈ Finset.range n) :
      (∫ x in (cellPoint n j * X)..(cellPoint n (j + 1) * X),
        (movingAverage E θ g x -
          profileAverage E g (fixedLength θ (cellPoint n j ^ θ) X) x) ^ 2) ≤
        A * K / (n : ℝ) ^ 2 * meanSquareScale θ X := by
    have hjn := Finset.mem_range.mp hj
    let h := fixedLength θ (cellPoint n j ^ θ) X
    let d := X ^ θ / n
    have ha := cellPoint_mem hn hjn.le
    have hb := cellPoint_mem hn (Nat.succ_le_of_lt hjn)
    have hab : cellPoint n j * X ≤ cellPoint n (j + 1) * X :=
      mul_le_mul_of_nonneg_right (cellPoint_lt hn j).le hX0.le
    have hh := cell_length_bounds hθ0 hθ1 hn hjn hX0
      (x := cellPoint n j * X) ⟨le_rfl, hab⟩
    have hh0 : 0 < h := hH.trans_le hh.1
    have hbound (x : ℝ) (hx : x ∈ Icc (cellPoint n j * X) (cellPoint n (j + 1) * X)) :=
      (cell_length_bounds hθ0 hθ1 hn hjn hX0 hx).2.2
    have hVc (u : ℝ) (hu : u ∈ Icc (0 : ℝ) (h + d)) :
        (∫ x in (cellPoint n j * X)..(cellPoint n (j + 1) * X), increment E u x ^ 2) ≤
          K * X * X ^ θ * Real.log X := by
      have hi : IntervalIntegrable (fun x => increment E u x ^ 2) volume X (2 * X) := by
        simpa only [pow_two, id_eq] using
          (increment_product_comp_integrableOn hE isCompact_uIcc
            continuous_const continuous_id continuous_const continuous_id).intervalIntegrable
      apply le_trans (intervalIntegral.integral_mono_interval
        (by nlinarith [ha.1] : X ≤ cellPoint n j * X) hab
        (by nlinarith [hb.2] : cellPoint n (j + 1) * X ≤ 2 * X)
        (Eventually.of_forall (fun _ => sq_nonneg _)) hi)
      apply hV u
      refine ⟨hu.1, ?_⟩
      have hdH : d ≤ X ^ θ := div_le_self hH.le hn1
      linarith [hu.2, hh.2.1]
    have ht := variable_profile_square_error_le hE hg (measurable_id.pow_const θ)
      hab hh0 (show 0 ≤ d by dsimp [d]; positivity) hM hgM hgLip hbound hVc
    apply ht.trans
    change A * d ^ 2 / h ^ 4 * _ ≤ _
    calc
      _ ≤ A * d ^ 2 / (X ^ θ) ^ 4 * (K * X * X ^ θ * Real.log X) := by
        gcongr
        exact hh.1
      _ = _ := by
        dsimp [d, meanSquareScale]
        have hd : X / X ^ θ = X ^ (1 - θ) :=
          (div_eq_iff hH.ne').mpr (by nlinarith [hp])
        calc
          _ = A * K / (n : ℝ) ^ 2 * (X / X ^ θ) * Real.log X := by field_simp
          _ = _ := by rw [hd]; ring
  have ht := Finset.sum_le_sum hj
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at ht
  convert ht using 1 <;> dsimp [cellSquareError, A]
  field_simp

private lemma interval_square_comparison {a b t : ℝ} (hab : a ≤ b) (ht : 0 < t)
    {f g : ℝ → ℝ} (hf : MemLp f 2 (volume.restrict (Ioc a b)))
    (hg : MemLp g 2 (volume.restrict (Ioc a b))) :
    (∫ x in a..b, f x ^ 2) ≤ (1 + t) * (∫ x in a..b, g x ^ 2) +
      (1 + 1 / t) * (∫ x in a..b, (f x - g x) ^ 2) := by
  have hF : 0 ≤ ∫ x in a..b, f x ^ 2 :=
    intervalIntegral.integral_nonneg_of_forall hab (fun _ => sq_nonneg _)
  have hG : 0 ≤ ∫ x in a..b, g x ^ 2 :=
    intervalIntegral.integral_nonneg_of_forall hab (fun _ => sq_nonneg _)
  have hD : 0 ≤ ∫ x in a..b, (f x - g x) ^ 2 :=
    intervalIntegral.integral_nonneg_of_forall hab (fun _ => sq_nonneg _)
  have hr := interval_l2_reverse_triangle hab hf hg
  have hnorm : Real.sqrt (∫ x in a..b, f x ^ 2) ≤
      Real.sqrt (∫ x in a..b, g x ^ 2) + Real.sqrt (∫ x in a..b, (f x - g x) ^ 2) := by
    linarith [(abs_le.mp hr).2]
  have hs := pow_le_pow_left₀ (Real.sqrt_nonneg _) hnorm 2
  have hy := two_mul_le_add_mul_sq
    (a := Real.sqrt (∫ x in a..b, g x ^ 2))
    (b := Real.sqrt (∫ x in a..b, (f x - g x) ^ 2)) ht
  rw [add_sq, Real.sq_sqrt hF, Real.sq_sqrt hG, Real.sq_sqrt hD] at hs
  rw [Real.sq_sqrt hG, Real.sq_sqrt hD, inv_eq_one_div] at hy
  nlinarith

private lemma cell_square_comparison {E g : ℝ → ℝ} {θ : ℝ}
    (hE : LocallyBoundedMeasurable E) (hg : ProfileIntegrable g)
    (hθ0 : 0 < θ) (hθ1 : θ < 1)
    {n : ℕ} (hn : 0 < n) {X t : ℝ} (hX : 0 < X) (ht : 0 < t) :
    (∫ x in X..(2 * X), profileAverage E g (x ^ θ) x ^ 2) ≤
        (1 + t) * cellMeanSquare E θ g n X + (1 + 1 / t) * cellSquareError E θ g n X ∧
    cellMeanSquare E θ g n X ≤
        (1 + t) * (∫ x in X..(2 * X), profileAverage E g (x ^ θ) x ^ 2) +
          (1 + 1 / t) * cellSquareError E θ g n X := by
  have hm : Measurable (fun x : ℝ => x ^ θ) := by fun_prop
  have hh (j : ℕ) (hj : j < n) := by
    have hab := mul_le_mul_of_nonneg_right (cellPoint_lt hn j).le hX.le
    have ha := cellPoint_mem hn hj.le
    have h0 : 0 < fixedLength θ (cellPoint n j ^ θ) X := by
      dsimp [fixedLength]
      exact mul_pos (Real.rpow_pos_of_pos (by linarith [ha.1]) _) (Real.rpow_pos_of_pos hX _)
    have hf := profileAverage_variable_memLp hE hg hm hab h0
      (fun x hx => (cell_length_bounds hθ0 hθ1 hn hj hX hx).2.2)
    have hg := profileAverage_variable_memLp hE hg measurable_const hab h0
      (fun _ _ => ⟨le_rfl, le_rfl⟩)
    exact And.intro (interval_square_comparison hab ht hf hg) (interval_square_comparison hab ht hg hf)
  have hs : (∑ j ∈ Finset.range n, ∫ x in (cellPoint n j * X)..(cellPoint n (j + 1) * X),
      profileAverage E g (x ^ θ) x ^ 2) =
      ∫ x in X..(2 * X), profileAverage E g (x ^ θ) x ^ 2 := by
    have hi (j : ℕ) (hj : j < n) : IntervalIntegrable
        (fun x => profileAverage E g (x ^ θ) x ^ 2)
        volume (cellPoint n j * X) (cellPoint n (j + 1) * X) := by
      have hab := mul_le_mul_of_nonneg_right (cellPoint_lt hn j).le hX.le
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
      exact (moving_memLp hE hg hθ0 (by nlinarith [(cellPoint_mem hn hj.le).1]) hab).integrable_sq
    convert intervalIntegral.sum_integral_adjacent_intervals hi using 1 <;>
      norm_num [cellPoint, hn.ne']
  have hu := Finset.sum_le_sum (fun j hj => (hh j (Finset.mem_range.mp hj)).1)
  have hl := Finset.sum_le_sum (fun j hj => (hh j (Finset.mem_range.mp hj)).2)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hu hl
  rw [hs] at hu hl
  constructor
  · exact hu
  · simpa only [cellMeanSquare, cellSquareError, sub_sq_comm] using hl


private theorem moving_lipschitz_mean_square_tendsto
    {E g : ℝ → ℝ} {α θ β : ℝ} {L : ℝ≥0}
    (hE : LocallyBoundedMeasurable E) (hB : ValidBand α θ β)
    (hV : CumulativeVarianceBandAsymptoticFor E α β) (hg : ProfileIntegrable g)
    (hgLip : LipschitzOnWith L g (Icc (0 : ℝ) 1)) :
    Tendsto (fun X => (∫ x in X..(2 * X), movingAverage E θ g x ^ 2) /
      meanSquareScale θ X) atTop (𝓝 (Q g * ((2 : ℝ) ^ (1 - θ) - 1))) := by
  let C : ℝ := Q g * ((2 : ℝ) ^ (1 - θ) - 1)
  have hθ0 : 0 < θ := hB.1.trans hB.2.1
  have hθ1 : θ < 1 := hB.2.2.1.trans hB.2.2.2
  have hQ0 : 0 ≤ Q g := by
    rw [ProfileQuadraticForm.Q_eq_tail_energy hg]
    exact intervalIntegral.integral_nonneg_of_forall zero_le_one fun _ => sq_nonneg _
  have hC : 0 ≤ C := mul_nonneg hQ0
    (sub_nonneg.mpr (Real.one_le_rpow (by norm_num) (by linarith)))
  obtain ⟨K, hK, hKv⟩ := shorter_increment_square_bound hE hB hV (c := 4) (by norm_num)
  obtain ⟨M, hMb⟩ := isCompact_Icc.exists_bound_of_continuousOn hgLip.continuousOn
  let M' := max M 0
  have hM : 0 ≤ M' := le_max_right _ _
  have hgM : ∀ s ∈ Icc (0 : ℝ) 1, |g s| ≤ M' := by
    intro s hs
    exact (hMb s hs).trans (le_max_left _ _)
  let Kerror : ℝ := 2 * ((2 * M' + (L : ℝ)) ^ 2 + M' ^ 2) * (4 * K)
  have hKerror : 0 ≤ Kerror := by dsimp [Kerror]; positivity
  have hVar : ∀ᶠ X : ℝ in atTop, ∀ u ∈ Icc (0 : ℝ) (4 * X ^ θ),
      (∫ x in X..(2 * X), increment E u x ^ 2) ≤ 4 * K * X * X ^ θ * Real.log X := by
    filter_upwards [hKv, eventually_gt_atTop (1 : ℝ)] with X hKv hX u hu
    have hX0 : 0 < X := by linarith
    have hH := Real.rpow_pos_of_pos hX0 θ
    have hl : lengthLog θ 4 X ≤ Real.log X := by
      rw [lengthLog, Real.log_div hX0.ne' (by dsimp [fixedLength]; positivity),
        fixedLength, Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hH.ne', Real.log_rpow hX0]
      have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
      nlinarith [Real.log_pos hX]
    have hv := hKv u hu
    apply hv.trans
    unfold fixedLength
    nlinarith [mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ K * X * (4 * X ^ θ))]
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ : ℝ := min (ε / 8) (1 / 2)
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  have hδe : δ ≤ ε / 8 := min_le_left _ _
  have hδ1 : δ ≤ 1 / 2 := min_le_right _ _
  let t : ℝ := ε / (8 * (C + 1))
  have ht : 0 < t := by dsimp [t]; positivity
  have htC : t * (C + 1) = ε / 8 := by dsimp [t]; field_simp
  let k : ℝ := 1 + 1 / t
  have hk : 0 < k := by dsimp [k]; positivity
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have herror : Tendsto (fun n : ℕ => k * (Kerror / n)) atTop (𝓝 0) := by
    simpa using ((tendsto_const_nhds (x := Kerror)).div_atTop hnat).const_mul k
  obtain ⟨n, hn, hCn, hne⟩ := (eventually_gt_atTop (0 : ℕ) |>.and
    ((Metric.tendsto_nhds.mp (cell_constant_tendsto hθ0 hθ1 g) δ hδ).and
      (herror.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε / 4))))).exists
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hCn' : |cellConstant θ g n - C| < δ := by simpa only [Real.dist_eq] using hCn
  have hQ := Metric.tendsto_nhds.mp (cell_mean_square_tendsto hE hB hV hg hn) δ hδ
  filter_upwards [eventually_gt_atTop (1 : ℝ), hVar, hQ]
    with X hX hVarX hQ
  have hX0 : 0 < X := by linarith
  have hS : 0 < meanSquareScale θ X :=
    mul_pos (Real.rpow_pos_of_pos hX0 _) (Real.log_pos hX)
  let A : ℝ := (∫ x in X..(2 * X), profileAverage E g (x ^ θ) x ^ 2) /
    meanSquareScale θ X
  let B : ℝ := cellMeanSquare E θ g n X / meanSquareScale θ X
  let R : ℝ := cellSquareError E θ g n X / meanSquareScale θ X
  have hB : |B - C| < 2 * δ := by
    have hB' : |B - cellConstant θ g n| < δ := by simpa only [Real.dist_eq] using hQ
    have hh := abs_add_le (B - cellConstant θ g n) (cellConstant θ g n - C)
    rw [sub_add_sub_cancel] at hh
    linarith
  have hBC : B ≤ C + 1 := by linarith [(abs_lt.mp hB).2]
  have hRC : k * R < ε / 4 := by
    have hr := div_le_div_of_nonneg_right
      (cell_square_error_le hE hg hθ0 hθ1 hM (show 0 ≤ 4 * K by positivity)
        hgM hgLip hn hX hVarX) hS.le
    have hr' : R ≤ Kerror / n := by
      dsimp [R, Kerror]
      convert hr using 1 <;> field_simp <;> ring
    exact (mul_le_mul_of_nonneg_left hr' hk.le).trans_lt hne
  obtain ⟨hU, hD⟩ := cell_square_comparison hE hg hθ0 hθ1 hn hX0 ht
  have hU' : A ≤ (1 + t) * B + k * R := by
    have hh := div_le_div_of_nonneg_right hU hS.le
    dsimp [A, B, R, k]
    convert hh using 1 <;> ring
  have hD' : B ≤ (1 + t) * A + k * R := by
    have hh := div_le_div_of_nonneg_right hD hS.le
    dsimp [A, B, R, k]
    convert hh using 1 <;> ring
  change |A - C| < ε
  rw [abs_lt]
  constructor
  · have hlow := (abs_lt.mp hB).1
    have htC' : t * C ≤ ε / 8 := by nlinarith
    nlinarith [mul_pos ht hε]
  · have hupp := (abs_lt.mp hB).2
    have htB : t * B ≤ ε / 8 := by nlinarith [mul_le_mul_of_nonneg_left hBC ht.le]
    nlinarith

private lemma moving_sub {E f g : ℝ → ℝ} {θ x : ℝ}
    (hE : LocallyBoundedMeasurable E) (hf : ProfileIntegrable f)
    (hg : ProfileIntegrable g) (_hx : 0 < x) :
    movingAverage E θ (fun s => g s - f s) x =
      movingAverage E θ g x - movingAverage E θ f x := by
  simp only [movingAverage, profileAverage_eq_unit_integral,
    intervalIntegral.integral_of_le zero_le_one, sub_mul]
  rw [integral_sub (unit_increment_integrable hE hg.2 (x ^ θ) x)
    (unit_increment_integrable hE hf.2 (x ^ θ) x), sub_div]

/-- The band asymptotic gives the moving-length mean-square law for every L¹ profile. -/
theorem moving_profile_mean_square_tendsto {E : ℝ → ℝ} {α θ β : ℝ}
    (hE : LocallyBoundedMeasurable E) (hB : ValidBand α θ β)
    (hV : CumulativeVarianceBandAsymptoticFor E α β)
    {g : ℝ → ℝ} (hg : ProfileIntegrable g) :
    Tendsto
      (fun X => (∫ x in X..(2 * X), movingAverage E θ g x ^ 2) / meanSquareScale θ X)
      atTop (𝓝 (Q g * ((2 : ℝ) ^ (1 - θ) - 1))) := by
  have hθ0 : 0 < θ := hB.1.trans hB.2.1
  have hθ1 : θ < 1 := hB.2.2.1.trans hB.2.2.2
  let D := (2 : ℝ) ^ (1 - θ) - 1
  have hD : 0 ≤ D := sub_nonneg.mpr (Real.one_le_rpow (by norm_num) (by linarith))
  have hQ (f : ℝ → ℝ) (hf : ProfileIntegrable f) : 0 ≤ Q f := by
    rw [ProfileQuadraticForm.Q_eq_tail_energy hf]
    exact intervalIntegral.integral_nonneg_of_forall zero_le_one fun _ => sq_nonneg _
  obtain ⟨C, hC, hCb⟩ := moving_profile_operator_bound hE hB hV
  have hroot : Tendsto
      (fun X => Real.sqrt ((∫ x in X..(2 * X), movingAverage E θ g x ^ 2) /
        meanSquareScale θ X)) atTop (𝓝 (Real.sqrt (Q g) * Real.sqrt D)) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    let δ := ε / (3 * (C + Real.sqrt D + 1))
    have hδ : 0 < δ := by dsimp [δ]; positivity
    obtain ⟨f, hf, ⟨L, hfLip⟩, hgf⟩ := ProfileDensity.exists_lipschitz_profile_approx hg hδ
    have hd : ProfileIntegrable (fun s => g s - f s) := ⟨hg.1.sub hf.1, hg.2.sub hf.2⟩
    have hfroot := (moving_lipschitz_mean_square_tendsto hE hB hV hf hfLip).sqrt
    rw [Real.sqrt_mul (hQ f hf)] at hfroot
    have hfε := Metric.tendsto_nhds.mp hfroot (ε / 3) (by positivity)
    filter_upwards [hCb, hfε, eventually_gt_atTop (1 : ℝ)] with X hCb hfε hX
    have hX0 : 0 < X := by linarith
    have hXX : X ≤ 2 * X := by linarith
    have hS : 0 < meanSquareScale θ X :=
      mul_pos (Real.rpow_pos_of_pos hX0 _) (Real.log_pos hX)
    have hSroot := Real.sqrt_pos.mpr hS
    have hn (q : ℝ → ℝ) : 0 ≤ ∫ x in X..(2 * X), q x ^ 2 :=
      intervalIntegral.integral_nonneg_of_forall hXX fun _ => sq_nonneg _
    have hdiff : |Real.sqrt ((∫ x in X..(2 * X), movingAverage E θ g x ^ 2) /
          meanSquareScale θ X) -
        Real.sqrt ((∫ x in X..(2 * X), movingAverage E θ f x ^ 2) /
          meanSquareScale θ X)| ≤ C * profileL1 (fun s => g s - f s) := by
      rw [Real.sqrt_div (hn _), Real.sqrt_div (hn _), ← sub_div, abs_div,
        abs_of_pos hSroot]
      apply (div_le_div_of_nonneg_right
        (interval_l2_reverse_triangle hXX (moving_memLp hE hg hθ0 hX0 hXX)
          (moving_memLp hE hf hθ0 hX0 hXX)) (Real.sqrt_nonneg _)).trans
      apply (div_le_iff₀ hSroot).mpr
      convert hCb (fun s => g s - f s) hd using 1
      congr 1
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le hXX] at hx
      dsimp only
      rw [moving_sub hE hf hg (hX0.trans_le hx.1)]
    have henergy : |Real.sqrt (Q f) * Real.sqrt D - Real.sqrt (Q g) * Real.sqrt D| ≤
        profileL1 (fun s => g s - f s) * Real.sqrt D := by
      rw [← sub_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), abs_sub_comm]
      exact mul_le_mul_of_nonneg_right (ProfileQuadraticForm.sqrt_Q_sub_le hf hg)
        (Real.sqrt_nonneg _)
    have hδeq : (C + Real.sqrt D + 1) * δ = ε / 3 := by
      dsimp [δ]
      field_simp
    have hsum := abs_sub_le
      (Real.sqrt ((∫ x in X..(2 * X), movingAverage E θ g x ^ 2) / meanSquareScale θ X))
      (Real.sqrt ((∫ x in X..(2 * X), movingAverage E θ f x ^ 2) / meanSquareScale θ X))
      (Real.sqrt (Q g) * Real.sqrt D)
    have hsum' := abs_sub_le
      (Real.sqrt ((∫ x in X..(2 * X), movingAverage E θ f x ^ 2) / meanSquareScale θ X))
      (Real.sqrt (Q f) * Real.sqrt D) (Real.sqrt (Q g) * Real.sqrt D)
    simp only [Real.dist_eq] at hfε ⊢
    have hL : 0 ≤ profileL1 (fun s => g s - f s) := integral_nonneg fun s => abs_nonneg _
    have happrox := mul_lt_mul_of_pos_left hgf
      (by positivity : 0 < C + Real.sqrt D + 1)
    nlinarith [Real.sqrt_nonneg D]
  have hs := hroot.pow 2
  rw [mul_pow, Real.sq_sqrt (hQ g hg), Real.sq_sqrt hD] at hs
  apply hs.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
  have hX0 : 0 < X := by linarith
  exact Real.sq_sqrt (div_nonneg
    (intervalIntegral.integral_nonneg_of_forall (by linarith : X ≤ 2 * X) fun _ => sq_nonneg _)
    (mul_pos (Real.rpow_pos_of_pos hX0 _) (Real.log_pos hX)).le)

end
end D5.S3.Arith.Robin.ForwardKernel.MovingLengthMeanSquare
