/- GID: D5/S3/Arith/Robin/ForwardKernel/MovingShortAverage
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/MovingShortAverage
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Averaging moving short increments gains the ratio of the short and averaging scales. -/

import D5.S3.Arith.Robin.ForwardKernel.MovingAverageIdentity
import D5.S3.Arith.Robin.ForwardKernel.MovingEndpointVariance
import D5.S3.Arith.Robin.ForwardKernel.ProfileLengthComparison

/-! Averaged moving increments on fixed spatial enlargements. -/

namespace D5.S3.Arith.Robin.ForwardKernel.MovingShortAverage

open Set MeasureTheory Filter
open VarianceTransferDefs VarianceTransfer CrossExponentDefs

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private lemma rectangle_square_bound {F : ℝ × ℝ → ℝ} {l r H K : ℝ}
    (hlr : l ≤ r) (hH : 0 ≤ H)
    (hF : Integrable (fun p => F p ^ 2)
      ((volume.restrict (Ioc l r)).prod (volume.restrict (Ioc (0 : ℝ) H))))
    (hK : ∀ t ∈ Icc (0 : ℝ) H, (∫ x in l..r, F (x, t) ^ 2) ≤ K) :
    IntervalIntegrable (fun x => ∫ t in (0 : ℝ)..H, F (x, t) ^ 2) volume l r ∧
    (∫ x in l..r, ∫ t in (0 : ℝ)..H, F (x, t) ^ 2) ≤ H * K := by
  constructor
  · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hlr]
    simpa only [IntegrableOn, intervalIntegral.integral_of_le hH] using hF.integral_prod_left
  · simp_rw [intervalIntegral.integral_of_le hlr, intervalIntegral.integral_of_le hH]
    rw [integral_integral_swap hF]
    calc
      _ ≤ ∫ _t in Ioc (0 : ℝ) H, K := by
        apply setIntegral_mono_on hF.integral_prod_right (integrableOn_const (by simp))
          measurableSet_Ioc
        intro t ht
        simpa only [intervalIntegral.integral_of_le hlr] using hK t ⟨ht.1.le, ht.2⟩
      _ = _ := by simp [hH]

private lemma integral_square_mono {f g : ℝ → ℝ} {l r : ℝ} (hlr : l ≤ r)
    (hg : IntervalIntegrable g volume l r)
    (h : ∀ x ∈ Icc l r, f x ^ 2 ≤ g x) :
    (∫ x in l..r, f x ^ 2) ≤ ∫ x in l..r, g x := by
  simp only [intervalIntegral.integral_of_le hlr]
  apply integral_mono_of_nonneg (Eventually.of_forall (fun _ => sq_nonneg _)) hg.1
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  exact h x ⟨hx.1.le, hx.2⟩

private lemma endpoint_family_integrable {E : ℝ → ℝ}
    (hE : LocallyBoundedMeasurable E) {p q : ℝ × ℝ → ℝ}
    (hp : Continuous p) (hq : Continuous q) (l r H : ℝ) :
    Integrable (fun z => (E (q z) - E (p z)) ^ 2)
      ((volume.restrict (Ioc l r)).prod (volume.restrict (Ioc (0 : ℝ) H))) := by
  rw [Measure.prod_restrict]
  have hi := increment_product_comp_integrableOn (μ := volume.prod volume) hE
    (K := Icc l r ×ˢ Icc (0 : ℝ) H) (isCompact_Icc.prod isCompact_Icc)
    (hq.sub hp) hp (hq.sub hp) hp
  simpa only [increment, Pi.sub_apply, add_sub_cancel, pow_two, IntegrableOn] using
    hi.mono_set (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)

private lemma endpoint_section_integrable {E : ℝ → ℝ}
    (hE : LocallyBoundedMeasurable E) {p q : ℝ → ℝ}
    (hp : Continuous p) (hq : Continuous q) (H : ℝ) :
    IntervalIntegrable (fun t => E (q t) - E (p t)) volume 0 H ∧
    IntervalIntegrable (fun t => (E (q t) - E (p t)) ^ 2) volume 0 H := by
  constructor
  · simpa only [increment, Pi.sub_apply, add_sub_cancel] using
      (increment_comp_integrableOn (μ := volume) (K := uIcc (0 : ℝ) H)
        hE isCompact_uIcc (hq.sub hp) hp).intervalIntegrable
  · simpa only [increment, Pi.sub_apply, add_sub_cancel, pow_two] using
      (increment_product_comp_integrableOn (μ := volume) (K := uIcc (0 : ℝ) H) hE isCompact_uIcc
        (hq.sub hp) hp (hq.sub hp) hp).intervalIntegrable

private lemma moving_average_square_bound {E : ℝ → ℝ} {a s l r M H D C₀ K Y : ℝ}
    (hE : LocallyBoundedMeasurable E) (ha : 0 < a) (hs : 0 ≤ s)
    (hl : 1 ≤ l) (hlr : l ≤ r) (hM : 0 < M) (hH : 0 < H) (hD : 0 ≤ D)
    (hDM : D * M ≤ H) (hC : 1 + 2 * H / M ≤ C₀)
    (hY : r + M + 2 * H ≤ Y) (hK : 0 ≤ K)
    (hL : ∀ y ∈ Icc l (r + M), s * y ^ a ∈ Icc (0 : ℝ) H)
    (hLp : ∀ y ∈ Icc l (r + M), s * (a * y ^ (a - 1)) ∈ Icc (0 : ℝ) D)
    (hV : ∀ u ∈ Icc M ((C₀ + 2) * M), cumulativeVariance E Y u ≤ K) :
    (∫ x in l..r, (M * windowAverage M (movingIncrement E a s) x) ^ 2) ≤
      9 * H ^ 2 * (2 * (C₀ + 2) * K) := by
  let L : ℝ → ℝ := fun x => s * x ^ a
  let Lp : ℝ → ℝ := fun x => s * (a * x ^ (a - 1))
  have hLc : Continuous L := continuous_const.mul (Real.continuous_rpow_const ha.le)
  have hdL (x : ℝ) (hx : 0 < x) : HasDerivAt L (Lp x) x :=
    (Real.hasDerivAt_rpow_const (Or.inl hx.ne')).const_mul s
  have hx0 (x : ℝ) (hx : x ∈ Icc l (r + M)) : 0 < x := by linarith [hx.1]
  have hC0 : 0 ≤ C₀ := by positivity [le_trans (by positivity : (0 : ℝ) ≤ 1 + 2 * H / M) hC]
  have hgap : M + 2 * H ≤ C₀ * M := by
    have := (div_le_iff₀ hM).mp (show (M + 2 * H) / M ≤ C₀ by
      rw [add_div, div_self hM.ne']; exact hC)
    linarith
  have hdelta (x : ℝ) (hx : x ∈ Icc l r) :
      L (x + M) - L x ∈ Icc (0 : ℝ) H := by
    have hx0' : 0 < x := by linarith [hx.1]
    have hm := Real.rpow_le_rpow hx0'.le (by linarith : x ≤ x + M) ha.le
    have hb := norm_image_sub_le_of_norm_deriv_le_segment'
      (f := L) (f' := Lp) (a := x) (b := x + M)
      (fun y hy => (hdL y (by linarith [hy.1])).hasDerivWithinAt)
      (fun y hy => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hLp y ⟨by linarith [hy.1, hx.1],
          by linarith [hy.2, hx.2]⟩).1]
        exact (hLp y ⟨by linarith [hy.1, hx.1], by linarith [hy.2, hx.2]⟩).2)
      (x + M) ⟨by linarith, le_rfl⟩
    refine ⟨sub_nonneg.mpr (mul_le_mul_of_nonneg_left hm hs), ?_⟩
    have hb' : L (x + M) - L x ≤ D * M := by
      simpa only [Real.norm_eq_abs, add_sub_cancel_left] using (le_abs_self _).trans hb
    exact hb'.trans hDM
  let K₁ := 2 * (C₀ + 2) * K
  have hbound {p q dp dq : ℝ → ℝ}
      (hp : Continuous p) (hq : Continuous q)
      (hdp : ∀ x ∈ Icc l r, HasDerivAt p (dp x) x)
      (hdq : ∀ x ∈ Icc l r, HasDerivAt q (dq x) x)
      (hp1 : ∀ x ∈ Icc l r, 1 ≤ dp x)
      (hq1 : ∀ x ∈ Icc l r, 1 ≤ dq x)
      (hi : ∀ x ∈ Icc l r, p x ∈ Icc (1 : ℝ) Y ∧ q x ∈ Icc (1 : ℝ) Y)
      (hg : ∀ x ∈ Icc l r, q x - p x ∈ Icc (0 : ℝ) (C₀ * M)) :
      (∫ x in l..r, (E (q x) - E (p x)) ^ 2) ≤ K₁ := by
    simpa only [div_one, K₁] using
      MovingEndpointVariance.two_endpoint_increment_square_le hE hlr hM hC0 zero_lt_one hK
        hp.continuousOn hq.continuousOn (fun x hx => (hdp x hx).hasDerivWithinAt)
        (fun x hx => (hdq x hx).hasDerivWithinAt) hp1 hq1 hi hg hV
  let F₁ : ℝ × ℝ → ℝ := fun z => E (z.1 + z.2 + M) - E (z.1 + z.2)
  let F₂ : ℝ × ℝ → ℝ := fun z => E (z.1 + z.2 + L (z.1 + z.2)) - E z.1
  let F₃ : ℝ × ℝ → ℝ := fun z => E (z.1 + M + L z.1 + z.2) - E z.1
  have hb₁ : ∀ t ∈ Icc (0 : ℝ) H, (∫ x in l..r, F₁ (x, t) ^ 2) ≤ K₁ := by
    intro t ht
    apply hbound (p := fun x => x + t) (q := fun x => x + t + M) (by fun_prop) (by fun_prop)
      (fun x _ => (hasDerivAt_id x).add_const t)
      (fun x _ => ((hasDerivAt_id x).add_const t).add_const M)
      (fun _ _ => le_rfl) (fun _ _ => le_rfl)
    · intro x hx
      exact ⟨⟨by linarith [hx.1, ht.1], by linarith [hx.2, ht.2]⟩,
        ⟨by linarith [hx.1, ht.1], by linarith [hx.2, ht.2]⟩⟩
    · intro x hx
      constructor <;> linarith
  have hb₂ : ∀ t ∈ Icc (0 : ℝ) M, (∫ x in l..r, F₂ (x, t) ^ 2) ≤ K₁ := by
    intro t ht
    have hxt (x : ℝ) (hx : x ∈ Icc l r) : x + t ∈ Icc l (r + M) :=
      ⟨by linarith [hx.1, ht.1], by linarith [hx.2, ht.2]⟩
    apply hbound (p := fun x => x) (q := fun x => x + t + L (x + t))
      continuous_id (by fun_prop)
      (fun x _ => hasDerivAt_id x)
      (fun x hx => by
        have hd := (hdL (x + t) (hx0 _ (hxt x hx))).comp x
          ((hasDerivAt_id x).add_const t)
        convert ((hasDerivAt_id x).add_const t).add hd using 1
        simp [Function.comp_def]
        rfl)
      (fun _ _ => le_rfl)
    · intro x hx
      linarith [(hLp (x + t) (hxt x hx)).1]
    · intro x hx
      exact ⟨⟨by linarith [hx.1], by linarith [hx.2]⟩,
        ⟨by linarith [(hL _ (hxt x hx)).1, hx.1, ht.1],
          by linarith [(hL _ (hxt x hx)).2, hx.2, ht.2]⟩⟩
    · intro x hx
      constructor <;> dsimp only [L] <;>
        linarith [(hL _ (hxt x hx)).1, (hL _ (hxt x hx)).2, ht.1, ht.2]
  have hb₃ : ∀ t ∈ Icc (0 : ℝ) H, (∫ x in l..r, F₃ (x, t) ^ 2) ≤ K₁ := by
    intro t ht
    have hxx (x : ℝ) (hx : x ∈ Icc l r) : x ∈ Icc l (r + M) :=
      ⟨hx.1, by linarith [hx.2]⟩
    apply hbound (p := fun x => x) (q := fun x => x + M + L x + t)
      continuous_id (by fun_prop)
      (fun x _ => hasDerivAt_id x)
      (fun x hx => (((hasDerivAt_id x).add_const M).add
        (hdL x (hx0 _ (hxx x hx)))).add_const t)
      (fun _ _ => le_rfl)
    · intro x hx
      linarith [(hLp x (hxx x hx)).1]
    · intro x hx
      exact ⟨⟨by linarith [hx.1], by linarith [hx.2]⟩,
        ⟨by linarith [(hL _ (hxx x hx)).1, hx.1, ht.1],
          by linarith [(hL _ (hxx x hx)).2, hx.2, ht.2]⟩⟩
    · intro x hx
      constructor <;> dsimp only [L] <;>
        linarith [(hL _ (hxx x hx)).1, (hL _ (hxx x hx)).2, ht.1, ht.2]
  obtain ⟨hi₁, hi₁b⟩ := rectangle_square_bound hlr hH.le
    (endpoint_family_integrable hE (p := fun z => z.1 + z.2)
      (q := fun z => z.1 + z.2 + M) (by fun_prop) (by fun_prop) l r H) hb₁
  obtain ⟨hi₂, hi₂b⟩ := rectangle_square_bound hlr hM.le
    (endpoint_family_integrable hE (p := fun z => z.1)
      (q := fun z => z.1 + z.2 + L (z.1 + z.2)) (by fun_prop) (by fun_prop) l r M) hb₂
  obtain ⟨hi₃, hi₃b⟩ := rectangle_square_bound hlr hH.le
    (endpoint_family_integrable hE (p := fun z => z.1)
      (q := fun z => z.1 + M + L z.1 + z.2) (by fun_prop) (by fun_prop) l r H) hb₃
  let G : ℝ → ℝ := fun x => 3 *
    (H * (∫ t in (0 : ℝ)..H, F₁ (x, t) ^ 2) +
      D ^ 2 * M * (∫ t in (0 : ℝ)..M, F₂ (x, t) ^ 2) +
      H * (∫ t in (0 : ℝ)..H, F₃ (x, t) ^ 2))
  have hiG : IntervalIntegrable G volume l r :=
    (((hi₁.const_mul H).add (hi₂.const_mul (D ^ 2 * M))).add
      (hi₃.const_mul H)).const_mul 3
  have hpt (x : ℝ) (hx : x ∈ Icc l r) :
      (M * windowAverage M (movingIncrement E a s) x) ^ 2 ≤ G x := by
    have hxx : x ∈ Icc l (r + M) := ⟨hx.1, by linarith [hx.2]⟩
    obtain ⟨hif₁, hif₁2⟩ := endpoint_section_integrable hE
      (p := fun t => x + t) (q := fun t => x + t + M) (by fun_prop) (by fun_prop) H
    obtain ⟨hif₂, hif₂2⟩ := endpoint_section_integrable hE
      (p := fun _ => x) (q := fun t => x + t + L (x + t)) (by fun_prop) (by fun_prop) M
    obtain ⟨hif₃, hif₃2⟩ := endpoint_section_integrable hE
      (p := fun _ => x) (q := fun t => x + M + L x + t) (by fun_prop) (by fun_prop) H
    have hcap_eq {T H' : ℝ} (hT : T ∈ Icc (0 : ℝ) H') (w f : ℝ → ℝ) :
        (∫ t in (0 : ℝ)..H', (Iic T).indicator w t * f t) =
          ∫ t in (0 : ℝ)..T, w t * f t := by
      rw [← intervalIntegral.integral_indicator (f := fun t => w t * f t)
        (μ := volume) hT]
      apply intervalIntegral.integral_congr
      intro t ht
      by_cases htT : t ≤ T
      · change (Iic T).indicator w t * f t =
          (Iic T).indicator (fun t => w t * f t) t
        rw [Set.indicator_of_mem (show t ∈ Iic T from htT),
          Set.indicator_of_mem (show t ∈ Iic T from htT)]
      · change (Iic T).indicator w t * f t =
          (Iic T).indicator (fun t => w t * f t) t
        rw [Set.indicator_of_notMem (show t ∉ Iic T from htT),
          Set.indicator_of_notMem (show t ∉ Iic T from htT)]
        simp
    have hc₁ := ProfileLengthComparison.bounded_factor_square_le
      (f := fun t => F₁ (x, t))
      (k := (Iic (L x)).indicator (fun _ => 1)) (a := (0 : ℝ)) (b := H) (C := 1)
      hH.le (by norm_num) hif₁ hif₁2 (by
        intro t ht
        by_cases htT : t ≤ L x
        · rw [Set.indicator_of_mem (show t ∈ Iic (L x) from htT)]
          norm_num
        · rw [Set.indicator_of_notMem (show t ∉ Iic (L x) from htT)]
          simp)
    rw [hcap_eq (H' := H) (hL x hxx) (fun _ => 1) (fun t => F₁ (x, t))] at hc₁
    have hc₂ := ProfileLengthComparison.bounded_factor_square_le
      (f := fun t => F₂ (x, t))
      (k := (Iic M).indicator (fun t => Lp (x + t))) (a := (0 : ℝ)) (b := M) (C := D)
      hM.le (by exact hD) hif₂ hif₂2 (by
        intro t ht
        by_cases htT : t ≤ M
        · rw [Set.indicator_of_mem (show t ∈ Iic M from htT)]
          have hxt : x + t ∈ Icc l (r + M) :=
            ⟨by linarith [hx.1, ht.1], by linarith [hx.2, ht.2]⟩
          exact (abs_of_nonneg (hLp _ hxt).1).le.trans (hLp _ hxt).2
        · rw [Set.indicator_of_notMem (show t ∉ Iic M from htT)]
          simp [hD])
    rw [hcap_eq (H' := M) (show M ∈ Icc (0 : ℝ) M from ⟨hM.le, le_rfl⟩)
      (fun t => Lp (x + t)) (fun t => F₂ (x, t))] at hc₂
    have hc₃ := ProfileLengthComparison.bounded_factor_square_le
      (f := fun t => F₃ (x, t))
      (k := (Iic (L (x + M) - L x)).indicator (fun _ => 1))
      (a := (0 : ℝ)) (b := H) (C := 1) hH.le (by norm_num) hif₃ hif₃2 (by
        intro t ht
        by_cases htT : t ≤ L (x + M) - L x
        · rw [Set.indicator_of_mem
            (show t ∈ Iic (L (x + M) - L x) from htT)]
          norm_num
        · rw [Set.indicator_of_notMem
            (show t ∉ Iic (L (x + M) - L x) from htT)]
          simp)
    rw [hcap_eq (H' := H) (hdelta x hx) (fun _ => 1) (fun t => F₃ (x, t))] at hc₃
    simp only [one_mul, one_pow] at hc₁ hc₃
    have hid := MovingAverageIdentity.moving_average_forward_identity hE ha hs
      (by linarith [hx.1] : 0 < x) hM
    dsimp only at hid
    change M * windowAverage M (movingIncrement E a s) x =
      (∫ t in (0 : ℝ)..L x, F₁ (x, t)) -
      (∫ t in (0 : ℝ)..M, Lp (x + t) * F₂ (x, t)) +
      (∫ t in (0 : ℝ)..(L (x + M) - L x), F₃ (x, t)) at hid
    rw [hid]
    dsimp only [G]
    nlinarith [sq_nonneg ((∫ t in (0 : ℝ)..L x, F₁ (x, t)) +
        (∫ t in (0 : ℝ)..M, Lp (x + t) * F₂ (x, t))),
      sq_nonneg ((∫ t in (0 : ℝ)..L x, F₁ (x, t)) -
        (∫ t in (0 : ℝ)..(L (x + M) - L x), F₃ (x, t))),
      sq_nonneg ((∫ t in (0 : ℝ)..M, Lp (x + t) * F₂ (x, t)) +
        (∫ t in (0 : ℝ)..(L (x + M) - L x), F₃ (x, t)))]
  calc
    _ ≤ ∫ x in l..r, G x := integral_square_mono hlr hiG hpt
    _ = 3 * (H * (∫ x in l..r, ∫ t in (0 : ℝ)..H, F₁ (x, t) ^ 2) +
        D ^ 2 * M * (∫ x in l..r, ∫ t in (0 : ℝ)..M, F₂ (x, t) ^ 2) +
        H * (∫ x in l..r, ∫ t in (0 : ℝ)..H, F₃ (x, t) ^ 2)) := by
      dsimp only [G]
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_add ((hi₁.const_mul H).add (hi₂.const_mul _))
          (hi₃.const_mul H),
        intervalIntegral.integral_add (hi₁.const_mul H) (hi₂.const_mul _)]
      simp only [intervalIntegral.integral_const_mul]
      rfl
    _ ≤ 3 * (H * (H * K₁) + D ^ 2 * M * (M * K₁) + H * (H * K₁)) := by
      gcongr
    _ ≤ 9 * H ^ 2 * K₁ := by
      have hs := (sq_le_sq₀ (mul_nonneg hD hM.le) hH.le).mpr hDM
      have hK₁ : 0 ≤ K₁ := by dsimp [K₁]; positivity
      nlinarith [mul_le_mul_of_nonneg_right hs hK₁]

/-- Uniformly in the moving-length parameter, averaging gains the ratio of the
short power scale to the averaging scale on every fixed spatial enlargement. -/
theorem averaged_moving_increment_l2_bound
    {E M : ℝ → ℝ} {a A B : ℝ}
    (hE : LocallyBoundedMeasurable E)
    (ha : 0 < a) (ha1 : a < 1)
    (hA : 0 < A) (hAB : A ≤ B)
    (hM : ComparableLengthVarianceUpperFor E M)
    (hhM : Asymptotics.IsBigO atTop (fun X : ℝ => X ^ a) M)
    (hMX : Asymptotics.IsLittleO atTop M (fun X : ℝ => X)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℝ in atTop,
      ∀ s ∈ Icc (0 : ℝ) 1,
        intervalL2 (A * X) (B * X)
          (windowAverage (M X) (movingIncrement E a s)) ≤
        C * (X ^ a / M X) *
          Real.sqrt (X * Real.log X) * Real.sqrt (M X) := by
  have hB : 0 < B := hA.trans_le hAB
  obtain ⟨J, hJ, hJh⟩ := hhM.exists_pos
  let c := (B + 1) ^ a + a * A ^ (a - 1) + 1
  have hc : 0 < c := by dsimp [c]; positivity
  have hc₁ : (B + 1) ^ a ≤ c := by
    dsimp [c]; linarith [mul_nonneg ha.le (Real.rpow_nonneg hA.le (a - 1))]
  have hc₂ : a * A ^ (a - 1) ≤ c := by
    dsimp [c]; linarith [Real.rpow_nonneg (show 0 ≤ B + 1 by linarith) a]
  let C₀ := 1 + 2 * c * J
  have hC₀ : 0 ≤ C₀ := by dsimp [C₀]; positivity
  obtain ⟨K, hK, hKv⟩ := hM.2 1 (C₀ + 2) (B + 3)
    zero_lt_one (by dsimp [C₀]; nlinarith [mul_pos hc hJ]) (by positivity)
  let C := 3 * c * Real.sqrt (2 * (C₀ + 2) * K)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  filter_upwards [hM.1, hJh.bound, hMX.bound (c := 1) zero_lt_one,
    hMX.bound (c := 1 / (c * J)) (by positivity), hKv,
    eventually_ge_atTop (1 : ℝ), eventually_ge_atTop (1 / A)] with
    X hMX0 hJh hMX1 hMX2 hKv hX hAX
  have hX0 : 0 < X := zero_lt_one.trans_le hX
  have hXa : 0 < X ^ a := Real.rpow_pos_of_pos hX0 a
  simp only [Real.norm_eq_abs, abs_of_pos hXa, abs_of_pos hMX0,
    abs_of_pos hX0, one_mul] at hJh hMX1 hMX2
  have hl : 1 ≤ A * X := (div_le_iff₀ hA).mp hAX |>.trans_eq (mul_comm X A)
  have hlr : A * X ≤ B * X := mul_le_mul_of_nonneg_right hAB hX0.le
  let H := c * X ^ a
  let D := H / X
  have hH : 0 < H := mul_pos hc hXa
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hHM : H ≤ c * J * M X := by dsimp [H]; nlinarith [mul_le_mul_of_nonneg_left hJh hc.le]
  have hHX : H ≤ X := by
    calc
      H ≤ c * J * M X := hHM
      _ ≤ c * J * (1 / (c * J) * X) :=
        mul_le_mul_of_nonneg_left hMX2 (by positivity)
      _ = X := by field_simp
  have hDM : D * M X ≤ H := by
    calc
      D * M X ≤ D * X := mul_le_mul_of_nonneg_left hMX1 hD
      _ = H := div_mul_cancel₀ _ hX0.ne'
  have hCbound : 1 + 2 * H / M X ≤ C₀ := by
    have hh := (div_le_iff₀ hMX0).mpr (show 2 * H ≤ (2 * c * J) * M X by nlinarith)
    dsimp [C₀]
    linarith
  have hL (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      ∀ y ∈ Icc (A * X) (B * X + M X), s * y ^ a ∈ Icc (0 : ℝ) H := by
    intro y hy
    have hy0 : 0 < y := (mul_pos hA hX0).trans_le hy.1
    refine ⟨by positivity [hs.1], ?_⟩
    calc
      s * y ^ a ≤ y ^ a := mul_le_of_le_one_left (Real.rpow_pos_of_pos hy0 a).le hs.2
      _ ≤ ((B + 1) * X) ^ a :=
        Real.rpow_le_rpow hy0.le (by linarith [hy.2]) ha.le
      _ = (B + 1) ^ a * X ^ a := Real.mul_rpow (by positivity) hX0.le
      _ ≤ H := mul_le_mul_of_nonneg_right hc₁ hXa.le
  have hLp (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      ∀ y ∈ Icc (A * X) (B * X + M X),
        s * (a * y ^ (a - 1)) ∈ Icc (0 : ℝ) D := by
    intro y hy
    have hy0 : 0 < y := (mul_pos hA hX0).trans_le hy.1
    refine ⟨by positivity [hs.1], ?_⟩
    calc
      s * (a * y ^ (a - 1)) ≤ a * y ^ (a - 1) :=
        mul_le_of_le_one_left (by positivity) hs.2
      _ ≤ a * (A * X) ^ (a - 1) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos (mul_pos hA hX0) hy.1 (by linarith)) ha.le
      _ = (a * A ^ (a - 1)) * X ^ a / X := by
        rw [Real.mul_rpow hA.le hX0.le, Real.rpow_sub_one hX0.ne']
        ring
      _ ≤ D := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hc₂ hXa.le) hX0.le
  intro s hs
  have hb := moving_average_square_bound hE ha hs.1 hl hlr hMX0 hH hD hDM hCbound
    (show B * X + M X + 2 * H ≤ (B + 3) * X by linarith) (by positivity [Real.log_nonneg hX])
    (hL s hs) (hLp s hs) (fun u hu => hKv u (by simpa only [one_mul] using hu))
  simp only [mul_pow, intervalIntegral.integral_const_mul] at hb
  have hlog : 0 ≤ X * Real.log X := mul_nonneg hX0.le (Real.log_nonneg hX)
  unfold intervalL2
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity [Real.log_nonneg hX])).mp
  rw [Real.sq_sqrt (intervalIntegral.integral_nonneg hlr (fun _ _ => sq_nonneg _))]
  apply le_of_mul_le_mul_left (a := (M X) ^ 2) _ (sq_pos_of_pos hMX0)
  calc
    _ ≤ 9 * H ^ 2 * (2 * (C₀ + 2) * (K * X * M X * Real.log X)) := hb
    _ = (M X) ^ 2 *
        (C * (X ^ a / M X) * Real.sqrt (X * Real.log X) * Real.sqrt (M X)) ^ 2 := by
      dsimp only [C, H]
      simp only [mul_pow, div_pow, Real.sq_sqrt hlog, Real.sq_sqrt hMX0.le,
        Real.sq_sqrt (by positivity : 0 ≤ 2 * (C₀ + 2) * K)]
      field_simp
      ring

end
end D5.S3.Arith.Robin.ForwardKernel.MovingShortAverage
