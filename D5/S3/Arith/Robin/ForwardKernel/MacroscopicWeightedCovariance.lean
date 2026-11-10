/- GID: D5/S3/Arith/Robin/ForwardKernel/MacroscopicWeightedCovariance
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/MacroscopicWeightedCovariance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Frozen block limits and quadratic error bounds give weighted macroscopic covariance. -/

import D5.S3.Arith.Robin.ForwardKernel.MacroscopicVarianceDefs
import D5.S3.Arith.Robin.ForwardKernel.FixedLengthCovariance
import D5.S3.Arith.Robin.ForwardKernel.MacroscopicFreezing
import D5.S3.Combinatorics.Permanental.CycleGeodesic.CycleGeodesicScaling
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.UniformSpace.HeineCantor

/-! Fixed finite block limits for macroscopic lengths frozen at block endpoints. -/

namespace D5.S3.Arith.Robin.ForwardKernel.MacroscopicWeightedCovariance

open Set MeasureTheory Filter
open scoped Topology BigOperators
open VarianceTransferDefs MovingLengthCells MomentTransferDefs MacroscopicVarianceDefs

noncomputable section

private lemma covariance_normalizer_ratio {θ M : ℝ} (hM : 0 < M) :
    Tendsto (fun X => (X * fixedLength θ M X * lengthLog θ M X) /
      varianceScale θ X) atTop (𝓝 (M * kappa θ)) := by
  have ht := (MovingLengthCells.fixed_normalizer_ratio (θ := θ) hM).const_mul (M ^ 2)
  have hlimit : M ^ 2 * ((1 - θ) / M) = M * kappa θ := by
    dsimp [kappa]
    field_simp
  rw [hlimit] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
  have hX0 : 0 < X := zero_lt_one.trans hX
  have hp : X ^ (1 - θ) = X / X ^ θ := by
    rw [Real.rpow_sub hX0, Real.rpow_one]
  dsimp [fixedLength, meanSquareScale, varianceScale]
  rw [hp]
  field_simp [(Real.log_pos hX).ne', (Real.rpow_pos_of_pos hX0 θ).ne']

/-- The weighted covariance of lengths frozen on finitely many blocks has its overlap limit. -/
theorem fixed_block_covariance_tendsto
    {E : ℝ → ℝ} {α θ β : ℝ}
    (hE : LocallyBoundedMeasurable E) (hB : ValidBand α θ β)
    (hV : CumulativeVarianceBandAsymptoticFor E α β)
    {a b w : ℝ → ℝ} {M : ℝ} {n : ℕ} (hM : 0 < M) (hn : 0 < n)
    (ha : ∀ j ∈ Finset.range n, a (cellPoint n j) ∈ Icc (0 : ℝ) M)
    (hb : ∀ j ∈ Finset.range n, b (cellPoint n j) ∈ Icc (0 : ℝ) M) :
    Tendsto (fun X =>
      (∑ j ∈ Finset.range n, w (cellPoint n j) *
        (∫ x in (cellPoint n j * X)..(cellPoint n (j + 1) * X),
          increment E (X ^ θ * a (cellPoint n j)) x *
          increment E (X ^ θ * b (cellPoint n j)) x)) / varianceScale θ X)
      atTop (𝓝 (kappa θ / (n : ℝ) *
        ∑ j ∈ Finset.range n, w (cellPoint n j) *
          min (a (cellPoint n j)) (b (cellPoint n j)))) := by
  have hj (j : ℕ) (hj : j ∈ Finset.range n) :
      Tendsto (fun X => w (cellPoint n j) *
        (∫ x in (cellPoint n j * X)..(cellPoint n (j + 1) * X),
          increment E (X ^ θ * a (cellPoint n j)) x *
          increment E (X ^ θ * b (cellPoint n j)) x) / varianceScale θ X)
        atTop (𝓝 (kappa θ / (n : ℝ) * (w (cellPoint n j) *
          min (a (cellPoint n j)) (b (cellPoint n j))))) := by
    have hjn := Finset.mem_range.mp hj
    have hu := cellPoint_mem hn hjn.le
    have hv := cellPoint_mem hn (Nat.succ_le_of_lt hjn)
    have hs : a (cellPoint n j) / M ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg (ha j hj).1 hM.le, (div_le_one hM).mpr (ha j hj).2⟩
    have ht : b (cellPoint n j) / M ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg (hb j hj).1 hM.le, (div_le_one hM).mpr (hb j hj).2⟩
    have hc := ((FixedLengthCovariance.fixed_length_covariance_tendsto
      hE hB hV hu.1 (cellPoint_lt hn j) hv.2 hM hs ht).mul
      (covariance_normalizer_ratio (θ := θ) hM)).const_mul (w (cellPoint n j))
    rw [min_div_div_right hM.le, cellPoint_step hn] at hc
    have he : w (cellPoint n j) *
        (1 / (n : ℝ) * (min (a (cellPoint n j)) (b (cellPoint n j)) / M) *
          (M * kappa θ)) = kappa θ / (n : ℝ) *
            (w (cellPoint n j) * min (a (cellPoint n j)) (b (cellPoint n j))) := by
      field_simp
    rw [he] at hc
    apply hc.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ),
      (FixedLengthCovariance.length_log_tendsto
        (hB.2.2.1.trans hB.2.2.2) hM).eventually (eventually_gt_atTop (0 : ℝ))]
      with X hX hlog
    have hden : X * fixedLength θ M X * lengthLog θ M X ≠ 0 :=
      ne_of_gt (by dsimp [fixedLength]; positivity)
    have hlen (v : ℝ) : v / M * fixedLength θ M X = X ^ θ * v := by
      dsimp [fixedLength]
      field_simp
    simp_rw [hlen]
    rw [div_mul_div_cancel₀ hden]
    ring
  have ht := tendsto_finsetSum (Finset.range n) hj
  simpa only [Finset.sum_div, Finset.mul_sum] using ht

/-- The sum of frozen squared norms converges to the mean of the frozen lengths. -/
theorem fixed_block_square_tendsto
    {E : ℝ → ℝ} {α θ β : ℝ}
    (hE : LocallyBoundedMeasurable E) (hB : ValidBand α θ β)
    (hV : CumulativeVarianceBandAsymptoticFor E α β)
    {a : ℝ → ℝ} {M : ℝ} {n : ℕ} (hM : 0 < M) (hn : 0 < n)
    (ha : ∀ j ∈ Finset.range n, a (cellPoint n j) ∈ Icc (0 : ℝ) M) :
    Tendsto (fun X =>
      (∑ j ∈ Finset.range n,
        ∫ x in (cellPoint n j * X)..(cellPoint n (j + 1) * X),
          increment E (X ^ θ * a (cellPoint n j)) x ^ 2) / varianceScale θ X)
      atTop (𝓝 (kappa θ / (n : ℝ) * ∑ j ∈ Finset.range n, a (cellPoint n j))) := by
  simpa only [one_mul, min_self, pow_two] using
    (fixed_block_covariance_tendsto hE hB hV (w := fun _ => 1) hM hn ha ha)

/-- The limiting frozen squared norm is nonnegative and at most the length bound. -/
theorem fixed_block_square_limit_mem
    {α θ β M : ℝ} (hB : ValidBand α θ β) {n : ℕ} (hn : 0 < n)
    {a : ℝ → ℝ}
    (ha : ∀ j ∈ Finset.range n, a (cellPoint n j) ∈ Icc (0 : ℝ) M) :
    kappa θ / (n : ℝ) * (∑ j ∈ Finset.range n, a (cellPoint n j)) ∈ Icc (0 : ℝ) M := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hθ0 : 0 < θ := hB.1.trans hB.2.1
  have hθ1 : θ < 1 := hB.2.2.1.trans hB.2.2.2
  have hk : 0 ≤ kappa θ := by dsimp [kappa]; linarith
  have hk1 : kappa θ ≤ 1 := by dsimp [kappa]; linarith
  have hsum0 : 0 ≤ ∑ j ∈ Finset.range n, a (cellPoint n j) :=
    Finset.sum_nonneg (fun j hj => (ha j hj).1)
  have hsum : (∑ j ∈ Finset.range n, a (cellPoint n j)) ≤ (n : ℝ) * M := by
    simpa using Finset.sum_le_sum (s := Finset.range n) (fun j hj => (ha j hj).2)
  refine ⟨mul_nonneg (div_nonneg hk hn'.le) hsum0, ?_⟩
  calc
    _ ≤ (1 / (n : ℝ)) * ∑ j ∈ Finset.range n, a (cellPoint n j) :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hk1 hn'.le) hsum0
    _ ≤ (1 / (n : ℝ)) * ((n : ℝ) * M) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = M := by field_simp


private lemma macro_product_integrable {E a b : ℝ → ℝ} {θ X : ℝ}
    (hE : LocallyBoundedMeasurable E) (hX : 0 < X)
    (ha : ContinuousOn a (Icc (1 : ℝ) 2)) (hb : ContinuousOn b (Icc (1 : ℝ) 2)) :
    IntervalIntegrable (fun x => macroIncrement E a θ X x * macroIncrement E b θ X x)
      volume X (2 * X) := by
  let ae := IccExtend (by norm_num : (1 : ℝ) ≤ 2) (fun u : Icc (1 : ℝ) 2 => a u)
  let be := IccExtend (by norm_num : (1 : ℝ) ≤ 2) (fun u : Icc (1 : ℝ) 2 => b u)
  have hae : Continuous ae := ha.domRestrict.Icc_extend'
  have hbe : Continuous be := hb.domRestrict.Icc_extend'
  apply ((VarianceTransfer.increment_product_comp_integrableOn hE isCompact_uIcc
    ((continuous_const (y := X ^ θ)).mul (hae.comp (continuous_id.div_const X))) continuous_id
    ((continuous_const (y := X ^ θ)).mul (hbe.comp (continuous_id.div_const X))) continuous_id).intervalIntegrable).congr
  intro x hx
  have hx' : x / X ∈ Icc (1 : ℝ) 2 := by
    rw [uIoc_of_le (by linarith : X ≤ 2 * X)] at hx
    exact ⟨(le_div_iff₀ hX).2 (by simpa using hx.1.le), (div_le_iff₀ hX).2 hx.2⟩
  simp [macroIncrement, ae, be, IccExtend_of_mem _ _ hx']

/-- A positive scale bounds an absolute product by two weighted squares. -/
lemma young_abs {r : ℝ} (hr : 0 < r) (x y : ℝ) :
    |x * y| ≤ x ^ 2 / r + r * y ^ 2 := by
  rw [abs_mul]
  have hh : |x| * |y| * r ≤ (x ^ 2 / r + r * y ^ 2) * r := by
    field_simp
    nlinarith [two_mul_le_add_sq |x| (r*|y|), sq_abs x, sq_abs y]
  nlinarith [hh]

private lemma block_product_error {E a b w : ℝ → ℝ} {θ X M L d K r : ℝ} {n : ℕ}
    (hE : LocallyBoundedMeasurable E) (hX : 1 < X) (hn : 0 < n)
    (ha : MacroscopicLengthBounds a M L) (hb : MacroscopicLengthBounds b M L)
    (hw : ContinuousOn w (Icc (1 : ℝ) 2)) (hd : 0 ≤ d) (hK : 0 ≤ K) (hr : 0 < r)
    (hweight : ∀ j < n, ∀ u ∈ Icc (cellPoint n j) (cellPoint n (j+1)),
      |w u - w (cellPoint n j)| ≤ d)
    (hwb : ∀ u ∈ Icc (1 : ℝ) 2, |w u| ≤ K) :
    |weightedMacroCovariance E a b w θ X -
      (∑ j ∈ Finset.range n, w (cellPoint n j) *
        (∫ x in (cellPoint n j * X)..(cellPoint n (j+1) * X),
          increment E (X ^ θ * a (cellPoint n j)) x *
          increment E (X ^ θ * b (cellPoint n j)) x)) / varianceScale θ X| ≤
      d * (normalizedSquare θ X (macroIncrement E a θ X) +
        normalizedSquare θ X (macroIncrement E b θ X)) +
      K * ((freezingError E a θ n X + freezingError E b θ n X) / r +
        r * (normalizedSquare θ X (macroIncrement E b θ X) +
          (∑ j ∈ Finset.range n, ∫ x in (cellPoint n j * X)..(cellPoint n (j+1) * X),
            increment E (X ^ θ * a (cellPoint n j)) x ^ 2) / varianceScale θ X)) := by
  have hX0 : 0 < X := zero_lt_one.trans hX
  have hS : 0 < varianceScale θ X := by
    dsimp [varianceScale]
    exact mul_pos (mul_pos hX0 (Real.rpow_pos_of_pos hX0 _)) (Real.log_pos hX)
  have hp := macro_product_integrable (θ := θ) hE hX0 ha.1.continuousOn hb.1.continuousOn
  have hsqa : IntervalIntegrable (fun x => macroIncrement E a θ X x ^ 2) volume X (2*X) := by
    simpa only [pow_two] using macro_product_integrable (θ := θ) hE hX0 ha.1.continuousOn ha.1.continuousOn
  have hsqb : IntervalIntegrable (fun x => macroIncrement E b θ X x ^ 2) volume X (2*X) := by
    simpa only [pow_two] using macro_product_integrable (θ := θ) hE hX0 hb.1.continuousOn hb.1.continuousOn
  have hc (j : ℕ) (hj : j < n) : Icc (cellPoint n j * X) (cellPoint n (j+1) * X) ⊆ Icc X (2*X) :=
    Icc_subset_Icc (by nlinarith [(cellPoint_mem hn hj.le).1])
      (by nlinarith [(cellPoint_mem hn (Nat.succ_le_of_lt hj)).2])
  have hle (j : ℕ) : cellPoint n j * X ≤ cellPoint n (j+1) * X :=
    mul_le_mul_of_nonneg_right (cellPoint_lt hn j).le hX0.le
  have hmono {f : ℝ → ℝ} (hi : IntervalIntegrable f volume X (2*X)) (j : ℕ) (hj : j < n) :
      IntervalIntegrable f volume (cellPoint n j * X) (cellPoint n (j+1) * X) := by
    apply hi.mono_set
    simpa only [uIcc_of_le (hle j), uIcc_of_le (by linarith : X ≤ 2*X)] using hc j hj
  have hwX : ContinuousOn (fun x => w (x/X)) (Icc X (2*X)) :=
    hw.comp (continuous_id.div_const X).continuousOn (fun x hx =>
      ⟨(le_div_iff₀ hX0).2 (by simpa using hx.1), (div_le_iff₀ hX0).2 hx.2⟩)
  have hwp : IntervalIntegrable (fun x => w (x/X) * macroIncrement E a θ X x *
      macroIncrement E b θ X x) volume X (2*X) := by
    simpa only [mul_assoc] using hp.continuousOn_mul
      (by simpa only [uIcc_of_le (by linarith : X ≤ 2*X)] using hwX)
  have hsum (f : ℝ → ℝ) (hi : IntervalIntegrable f volume X (2*X)) :
      (∑ j ∈ Finset.range n, ∫ x in (cellPoint n j * X)..(cellPoint n (j+1)*X), f x) =
        ∫ x in X..(2*X), f x := by
    convert intervalIntegral.sum_integral_adjacent_intervals (fun j hj => hmono hi j hj) using 1
    all_goals norm_num [cellPoint, hn.ne']
  have hblock (j : ℕ) (hj : j ∈ Finset.range n) :
      |(∫ x in (cellPoint n j * X)..(cellPoint n (j+1)*X),
          w (x/X) * macroIncrement E a θ X x * macroIncrement E b θ X x) -
        w (cellPoint n j) * (∫ x in (cellPoint n j * X)..(cellPoint n (j+1)*X),
          increment E (X^θ*a (cellPoint n j)) x * increment E (X^θ*b (cellPoint n j)) x)| ≤
      d * ((∫ x in (cellPoint n j * X)..(cellPoint n (j+1)*X), macroIncrement E a θ X x ^ 2) +
        (∫ x in (cellPoint n j * X)..(cellPoint n (j+1)*X), macroIncrement E b θ X x ^ 2)) +
      K * (((∫ x in (cellPoint n j * X)..(cellPoint n (j+1)*X),
          (macroIncrement E a θ X x - increment E (X^θ*a (cellPoint n j)) x)^2) +
        (∫ x in (cellPoint n j * X)..(cellPoint n (j+1)*X),
          (macroIncrement E b θ X x - increment E (X^θ*b (cellPoint n j)) x)^2)) / r +
        r * ((∫ x in (cellPoint n j * X)..(cellPoint n (j+1)*X), macroIncrement E b θ X x ^ 2) +
          (∫ x in (cellPoint n j * X)..(cellPoint n (j+1)*X), increment E (X^θ*a (cellPoint n j)) x ^ 2))) := by
    have hjn := Finset.mem_range.mp hj
    let A := cellPoint n j * X
    let B := cellPoint n (j+1) * X
    let f := macroIncrement E a θ X
    let g := macroIncrement E b θ X
    let F := fun x => increment E (X^θ*a (cellPoint n j)) x
    let G := fun x => increment E (X^θ*b (cellPoint n j)) x
    have hconst (c e : ℝ) : IntervalIntegrable (fun x => increment E c x * increment E e x) volume A B :=
      (VarianceTransfer.increment_product_comp_integrableOn hE isCompact_uIcc
        continuous_const continuous_id continuous_const continuous_id).intervalIntegrable
    have hFsq : IntervalIntegrable (fun x => F x ^ 2) volume A B := by
      simpa only [F, pow_two] using hconst (X^θ*a (cellPoint n j)) (X^θ*a (cellPoint n j))
    have hGsq : IntervalIntegrable (fun x => G x ^ 2) volume A B := by
      simpa only [G, pow_two] using hconst (X^θ*b (cellPoint n j)) (X^θ*b (cellPoint n j))
    have hcross (c : ℝ) (e : ℝ → ℝ) (he : ContinuousOn e (Icc (1 : ℝ) 2)) :
        IntervalIntegrable (fun x => macroIncrement E e θ X x * increment E c x) volume A B := by
      have hh := macro_product_integrable (θ := θ) hE hX0 he
        (continuousOn_const : ContinuousOn (fun _ : ℝ => c / X^θ) (Icc (1:ℝ) 2))
      apply (hmono hh j hjn).congr
      intro x _
      dsimp [macroIncrement]
      congr 2
      field_simp [(Real.rpow_pos_of_pos hX0 θ).ne']

    have hfa : IntervalIntegrable (fun x => (f x-F x)^2) volume A B := by
      have h := ((hmono hsqa j hjn).sub ((hcross (X^θ*a (cellPoint n j)) a ha.1.continuousOn).const_mul 2)).add hFsq
      convert h using 1
      ext x
      dsimp [f, F]
      ring
    have hgb : IntervalIntegrable (fun x => (g x-G x)^2) volume A B := by
      have h := ((hmono hsqb j hjn).sub ((hcross (X^θ*b (cellPoint n j)) b hb.1.continuousOn).const_mul 2)).add hGsq
      convert h using 1
      ext x
      dsimp [g, G]
      ring
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub
      (hmono hwp j hjn) ((hconst _ _).const_mul _)]
    have hint := intervalIntegral.norm_integral_le_of_norm_le (hle j)
      (f := fun x => w (x/X)*f x*g x-w (cellPoint n j)*(F x*G x))
      (g := fun x => d * (f x^2+g x^2) + K * (((f x-F x)^2+(g x-G x)^2)/r + r*(g x^2+F x^2)))
      (Eventually.of_forall (fun x hx => ?_))
      ((((hmono hsqa j hjn).add (hmono hsqb j hjn)).const_mul d).add
        ((((hfa.add hgb).div_const r).add (((hmono hsqb j hjn).add hFsq).const_mul r)).const_mul K))
    · rw [intervalIntegral.integral_add
        (((hmono hsqa j hjn).add (hmono hsqb j hjn)).const_mul d)
        ((((hfa.add hgb).div_const r).add
          (((hmono hsqb j hjn).add hFsq).const_mul r)).const_mul K)] at hint
      simp only [intervalIntegral.integral_const_mul] at hint
      rw [intervalIntegral.integral_add (hmono hsqa j hjn) (hmono hsqb j hjn),
        intervalIntegral.integral_add ((hfa.add hgb).div_const r)
          (((hmono hsqb j hjn).add hFsq).const_mul r)] at hint
      simp only [intervalIntegral.integral_div, intervalIntegral.integral_const_mul] at hint
      rw [intervalIntegral.integral_add hfa hgb,
        intervalIntegral.integral_add (hmono hsqb j hjn) hFsq] at hint
      exact hint
    · have hxm : x/X ∈ Icc (cellPoint n j) (cellPoint n (j+1)) :=
        ⟨(le_div_iff₀ hX0).2 hx.1.le, (div_le_iff₀ hX0).2 hx.2⟩
      have hwj := hwb _ (cellPoint_mem hn hjn.le)
      have hwerr := hweight j hjn _ hxm
      have heq : w (x/X)*f x*g x-w (cellPoint n j)*F x*G x =
          (w (x/X)-w (cellPoint n j))*(f x*g x) +
          w (cellPoint n j)*((f x-F x)*g x+F x*(g x-G x)) := by ring
      change |w (x/X)*f x*g x-w (cellPoint n j)*(F x*G x)| ≤ _
      rw [← mul_assoc, heq]
      calc
        _ ≤ |w (x/X)-w (cellPoint n j)| * |f x*g x| +
            |w (cellPoint n j)| *(|(f x-F x)*g x| + |F x*(g x-G x)|) := by
          apply (abs_add_le _ _).trans
          simp only [abs_mul]
          exact add_le_add le_rfl
            (mul_le_mul_of_nonneg_left (by
              simpa only [abs_mul] using (abs_add_le ((f x-F x)*g x) (F x*(g x-G x))))
              (abs_nonneg _))
        _ ≤ d*(f x^2+g x^2) + K*(((f x-F x)^2+(g x-G x)^2)/r+r*(g x^2+F x^2)) := by
          have hfg : |f x*g x| ≤ f x^2+g x^2 := by simpa using young_abs (by norm_num : (0:ℝ)<1) (f x) (g x)
          have hy₁ := young_abs hr (f x-F x) (g x)
          have hy₂ := young_abs hr (g x-G x) (F x)
          rw [mul_comm (F x)]
          have hh := add_le_add (mul_le_mul hwerr hfg (abs_nonneg _) hd)
            (mul_le_mul hwj (add_le_add hy₁ hy₂) (by positivity) hK)
          convert hh using 1 <;> ring
  rw [weightedMacroCovariance, ← hsum _ hwp, ← sub_div, abs_div, abs_of_pos hS]
  apply (div_le_iff₀ hS).2
  rw [← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hblock).trans_eq ?_)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div]
  rw [hsum _ hsqa, hsum _ hsqb]
  dsimp [normalizedSquare, freezingError]
  field_simp
  <;> ring


/-- Nonnegative continuously differentiable macroscopic lengths have the weighted overlap covariance limit. -/
theorem weighted_covariance_tendsto {E : ℝ → ℝ} {α θ β : ℝ}
    (hE : LocallyBoundedMeasurable E) (hB : ValidBand α θ β)
    (hV : CumulativeVarianceBandAsymptoticFor E α β)
    {a b w : ℝ → ℝ} (ha : ContDiffOn ℝ 1 a (Icc (1 : ℝ) 2))
    (hb : ContDiffOn ℝ 1 b (Icc (1 : ℝ) 2))
    (ha0 : ∀ u ∈ Icc (1 : ℝ) 2, 0 ≤ a u)
    (hb0 : ∀ u ∈ Icc (1 : ℝ) 2, 0 ≤ b u)
    (hw : ContinuousOn w (Icc (1 : ℝ) 2)) :
    Tendsto (weightedMacroCovariance E a b w θ) atTop
      (𝓝 (kappa θ * ∫ u in (1 : ℝ)..2, w u * min (a u) (b u))) := by
  obtain ⟨A, hA⟩ := isCompact_Icc.exists_bound_of_continuousOn ha.continuousOn
  obtain ⟨B, hBb⟩ := isCompact_Icc.exists_bound_of_continuousOn hb.continuousOn
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (ha.continuousOn_derivWithin (uniqueDiffOn_Icc (by norm_num : (1 : ℝ)<2)) (by norm_num))
  obtain ⟨D, hD⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hb.continuousOn_derivWithin (uniqueDiffOn_Icc (by norm_num : (1 : ℝ)<2)) (by norm_num))
  obtain ⟨W, hW⟩ := isCompact_Icc.exists_bound_of_continuousOn hw
  let M := 1 + |A| + |B|
  let L := |C| + |D|
  let K := |W| + 1
  have hM : 1 ≤ M := by dsimp [M]; linarith [abs_nonneg A, abs_nonneg B]
  have hM0 : 0 < M := by linarith
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  have hab : MacroscopicLengthBounds a M L := by
    refine ⟨ha, fun u hu => ⟨ha0 u hu, ?_⟩, fun u hu => ?_⟩
    · have := hA u hu; dsimp [M]; rw [Real.norm_eq_abs] at this
      linarith [le_abs_self (a u), le_abs_self A, abs_nonneg B]
    · have := hC u hu; dsimp [L]; rw [Real.norm_eq_abs] at this
      linarith [le_abs_self C, abs_nonneg D]
  have hbb : MacroscopicLengthBounds b M L := by
    refine ⟨hb, fun u hu => ⟨hb0 u hu, ?_⟩, fun u hu => ?_⟩
    · have := hBb u hu; dsimp [M]; rw [Real.norm_eq_abs] at this
      linarith [le_abs_self (b u), le_abs_self B, abs_nonneg A]
    · have := hD u hu; dsimp [L]; rw [Real.norm_eq_abs] at this
      linarith [le_abs_self D, abs_nonneg C]
  have hwb : ∀ u ∈ Icc (1 : ℝ) 2, |w u| ≤ K := by
    intro u hu
    have := hW u hu
    dsimp [K]
    rw [Real.norm_eq_abs] at this
    linarith [le_abs_self W]
  let g := fun u => w u * min (a u) (b u)
  have hg : ContinuousOn g (Icc (1 : ℝ) 2) := hw.mul (ha.continuousOn.inf hb.continuousOn)
  have hriemann : Tendsto (fun n : ℕ => (1 / (n : ℝ)) *
      ∑ j ∈ Finset.range n, g (cellPoint n j)) atTop
      (𝓝 (∫ u in (1 : ℝ)..2, g u)) := by
    have hc : ContinuousOn (fun v : ℝ => g (1 + v)) (Icc (0 : ℝ) 1) :=
      hg.comp (by fun_prop) (by intro v hv; constructor <;> linarith [hv.1, hv.2])
    have ht := CycleGeodesic.continuous_leftRiemann_tendsto hc
    have hi : (∫ v in (0 : ℝ)..1, g (1 + v)) = ∫ u in (1 : ℝ)..2, g u := by
      simpa only [add_zero, show (1 : ℝ) + 1 = 2 by norm_num] using
        intervalIntegral.integral_comp_add_left g 1 (a := 0) (b := 1)
    have hsum (n : ℕ) : (∑ k : Fin n, g (1 + (k : ℝ) / n)) =
        ∑ j ∈ Finset.range n, g (1 + (j : ℝ) / n) :=
      Fin.sum_univ_eq_sum_range (fun j => g (1 + (j : ℝ) / n)) n
    simp_rw [hsum] at ht
    simpa only [hi, cellPoint] using ht
  have hκ : kappa θ ∈ Icc (0 : ℝ) 1 := by
    dsimp [kappa]
    constructor <;> linarith [hB.1, hB.2.1, hB.2.2.1, hB.2.2.2]
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let d := ε / (16 * (1760*M+1))
  let r := ε / (16 * (K+1) * (881*M+1))
  let e := r * ε / (64 * (K+1))
  have hd : 0 < d := by dsimp [d]; positivity
  have hr : 0 < r := by dsimp [r]; positivity
  have he : 0 < e := by dsimp [e]; positivity
  obtain ⟨δw, hδw, hmodw⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hw) d hd
  have ht : Tendsto (fun n : ℕ => (1:ℝ)/(n:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have ht' := ht.const_mul (120*(1+L))
  simp only [mul_zero] at ht'
  obtain ⟨n, hn, hnw, hriem, hne⟩ := ((eventually_gt_atTop (0 : ℕ)).and
    ((ht.eventually (gt_mem_nhds hδw)).and
      ((hriemann.eventually (Metric.ball_mem_nhds _ (by positivity : 0 < ε / 4))).and
        (ht'.eventually (gt_mem_nhds he))))).exists
  rw [Real.dist_eq] at hriem
  have hm {f : ℝ → ℝ} {c δ : ℝ} (hδ : 1/(n:ℝ)<δ)
      (hmod : ∀ x ∈ Icc (1:ℝ) 2, ∀ y ∈ Icc (1:ℝ) 2, dist x y < δ → dist (f x) (f y) < c) :
      ∀ j < n, ∀ u ∈ Icc (cellPoint n j) (cellPoint n (j+1)), |f u-f (cellPoint n j)| ≤ c := by
    intro j hj u hu
    apply le_of_lt
    apply hmod u ⟨(cellPoint_mem hn hj.le).1.trans hu.1,
      hu.2.trans (cellPoint_mem hn (Nat.succ_le_of_lt hj)).2⟩ _ (cellPoint_mem hn hj.le)
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hu.1)]
    exact (sub_le_sub_right hu.2 _).trans_lt ((cellPoint_step hn j).symm ▸ hδ)
  let q := kappa θ / (n:ℝ) * ∑ j ∈ Finset.range n, g (cellPoint n j)
  have hq : |q-kappa θ * ∫ u in (1:ℝ)..2, g u| ≤ ε/4 := by
    calc
      _ = kappa θ * |(1/(n:ℝ))*∑ j ∈ Finset.range n, g (cellPoint n j)-∫ u in (1:ℝ)..2, g u| := by
        have heq : q-kappa θ * ∫ u in (1:ℝ)..2, g u =
            kappa θ * ((1/(n:ℝ))*∑ j ∈ Finset.range n, g (cellPoint n j)-∫ u in (1:ℝ)..2, g u) := by dsimp [q]; ring
        rw [heq, abs_mul, abs_of_nonneg hκ.1]
      _ ≤ 1 * (ε/4) := mul_le_mul hκ.2 hriem.le (abs_nonneg _) (by norm_num)
      _ = _ := one_mul _
  let F := fun X => (∑ j ∈ Finset.range n, ∫ x in (cellPoint n j*X)..(cellPoint n (j+1)*X),
    increment E (X^θ*a (cellPoint n j)) x ^ 2) / varianceScale θ X
  let Q := fun X => (∑ j ∈ Finset.range n, w (cellPoint n j) *
    (∫ x in (cellPoint n j*X)..(cellPoint n (j+1)*X), increment E (X^θ*a (cellPoint n j)) x *
      increment E (X^θ*b (cellPoint n j)) x)) / varianceScale θ X
  have hf : ∀ᶠ X : ℝ in atTop, F X ≤ M+1 := by
    have hh := fixed_block_square_tendsto hE hB hV hM0 hn
      (fun j hj => hab.2.1 _ (cellPoint_mem hn (Finset.mem_range.mp hj).le))
    have hh' := fixed_block_square_limit_mem hB hn
      (fun j hj => hab.2.1 _ (cellPoint_mem hn (Finset.mem_range.mp hj).le))
    exact (hh.eventually (gt_mem_nhds (show kappa θ/(n:ℝ)*∑ j ∈ Finset.range n, a (cellPoint n j)<M+1 by linarith [hh'.2]))).mono (fun _ h => h.le)
  have hQ : Tendsto Q atTop (𝓝 q) := fixed_block_covariance_tendsto hE hB hV hM0 hn
    (fun j hj => hab.2.1 _ (cellPoint_mem hn (Finset.mem_range.mp hj).le))
    (fun j hj => hbb.2.1 _ (cellPoint_mem hn (Finset.mem_range.mp hj).le))
  have hevent : ∀ᶠ X : ℝ in atTop,
      dist (weightedMacroCovariance E a b w θ X) (kappa θ*∫ u in (1:ℝ)..2, g u)<ε := by
    filter_upwards [MacroscopicFreezing.normalized_square_eventually hE hB hV hM hL,
      MacroscopicFreezing.freezing_eventually hE hB hV hM hL hn e he,
      hf, (Metric.tendsto_nhds.mp hQ) (ε/4) (by positivity), eventually_gt_atTop (1:ℝ)]
      with X hs heX hfX hQX hX
    have hfa := heX a hab
    have hfb := heX b hbb
    have hna := hs a hab
    have hnb := hs b hbb
    have herr := block_product_error (θ := θ) hE hX hn hab hbb hw hd.le hK.le hr (hm hnw hmodw) hwb
    have hsmall : d*(880*M+880*M)+K*((2*(120*(1+L)/(n:ℝ)+e))/r+r*(880*M+(M+1))) < ε/2 := by
      have hd' : d*(1760*M) < ε/16 := by
        have hh : d*(1760*M)<d*(1760*M+1) := mul_lt_mul_of_pos_left (by linarith) hd
        have heq : d*(1760*M+1)=ε/16 := by dsimp [d]; field_simp
        linarith
      have hr' : K*r*(881*M+1) < ε/16 := by
        have hh : K*r*(881*M+1) < (K+1)*r*(881*M+1) := by nlinarith
        have heq : (K+1)*r*(881*M+1)=ε/16 := by dsimp [r]; field_simp
        linarith
      have he' : K*(4*e)/r < ε/16 := by
        have hh : K*(4*e)/r < (K+1)*(4*e)/r := by gcongr; linarith
        have heq : (K+1)*(4*e)/r=ε/16 := by dsimp [e]; field_simp; ring
        linarith
      have hn' : 120*(1+L)/(n:ℝ)<e := by simpa only [mul_one_div] using hne
      have hh : K*(2*(120*(1+L)/(n:ℝ)+e))/r ≤ K*(4*e)/r :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (by linarith : 2*(120*(1+L)/(n:ℝ)+e) ≤ 4*e) hK.le) hr.le
      calc
        _ = d*(1760*M)+K*(2*(120*(1+L)/(n:ℝ)+e))/r+K*r*(881*M+1) := by ring
        _ < ε/2 := by linarith
    have herr' : |weightedMacroCovariance E a b w θ X-Q X| < ε/2 := by
      apply herr.trans_lt
      apply lt_of_le_of_lt ?_ hsmall
      gcongr
      linarith
    rw [Real.dist_eq] at hQX ⊢
    calc
      _ ≤ |weightedMacroCovariance E a b w θ X-Q X| + |Q X-q| + |q-kappa θ*∫ u in (1:ℝ)..2, g u| := by
        exact (abs_sub_le _ _ _).trans (add_le_add_left (abs_sub_le _ _ _) _)
      _ < ε := by linarith
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp hevent
  exact ⟨X₀, hX₀⟩

end
end D5.S3.Arith.Robin.ForwardKernel.MacroscopicWeightedCovariance
