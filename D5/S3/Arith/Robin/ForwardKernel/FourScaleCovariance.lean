/- GID: D5/S3/Arith/Robin/ForwardKernel/FourScaleCovariance
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/FourScaleCovariance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Four separated variance scales bound moving-increment covariance on every subinterval. -/

import D5.S3.Arith.Robin.ForwardKernel.MovingShortAverage
import D5.S3.Arith.Robin.ForwardKernel.TranslationStripBounds
import D5.S3.Arith.Robin.ForwardKernel.AveragingBounds
import D5.S3.Arith.Robin.ForwardKernel.AveragingRegularity

/-! Four separated scales control covariance uniformly over dyadic subintervals. -/

namespace D5.S3.Arith.Robin.ForwardKernel.FourScaleCovariance

open Set MeasureTheory Filter
open scoped Topology
open VarianceTransferDefs VarianceTransfer CrossExponentDefs

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private lemma pairing_le {f g : ℝ → ℝ} {l r : ℝ} (hlr : l ≤ r)
    (hf : MemLp f 2 (volume.restrict (Ioc l r)))
    (hg : MemLp g 2 (volume.restrict (Ioc l r))) :
    |∫ x in l..r, f x * g x| ≤ intervalL2 l r f * intervalL2 l r g := by
  have hc := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
    (show MemLp f (ENNReal.ofReal 2) _ by simpa using hf)
    (show MemLp g (ENNReal.ofReal 2) _ by simpa using hg)
  have hn := (norm_integral_le_integral_norm (fun x => f x * g x)).trans
    (by simpa only [norm_mul] using hc)
  simpa only [Real.norm_eq_abs, Real.rpow_two, sq_abs, ← Real.sqrt_eq_rpow,
    intervalIntegral.integral_of_le hlr, intervalL2] using hn

lemma moving_memLp {E : ℝ → ℝ} (hE : LocallyBoundedMeasurable E)
    {a s : ℝ} (ha : 0 < a) (l r : ℝ) :
    MemLp (movingIncrement E a s) 2 (volume.restrict (Ioc l r)) := by
  have hu : Continuous (fun x : ℝ => s * x ^ a) :=
    continuous_const.mul (Real.continuous_rpow_const ha.le)
  have hm : Measurable (movingIncrement E a s) :=
    (hE.1.comp (continuous_id.add hu).measurable).sub hE.1
  apply (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr
  exact (TranslationStripBounds.moving_sq_integrable hE ha l r).1

lemma average_memLp {E : ℝ → ℝ} (hE : LocallyBoundedMeasurable E)
    {a s M l r : ℝ} (ha : 0 < a) :
    MemLp (windowAverage M (movingIncrement E a s)) 2
      (volume.restrict (Ioc l r)) := by
  have hu : Continuous (fun x : ℝ => s * x ^ a) :=
    continuous_const.mul (Real.continuous_rpow_const ha.le)
  have hi (A B : ℝ) : IntervalIntegrable (movingIncrement E a s) volume A B :=
    (increment_comp_integrableOn hE isCompact_uIcc hu continuous_id).intervalIntegrable
  have hc : Continuous (windowAverage M (movingIncrement E a s)) :=
    AveragingRegularity.windowAverage_continuous_of_intervalIntegrable hi M
  apply (memLp_two_iff_integrable_sq hc.aestronglyMeasurable).mpr
  exact ((hc.pow 2).integrableOn_Icc).mono_set Ioc_subset_Icc_self

private lemma translation_pairing_identity {f z : ℝ → ℝ} {l r v : ℝ}
    (hi : ∀ A B, IntervalIntegrable (fun x => f x * z x) volume A B)
    (hj : IntervalIntegrable (fun x => f (x + v) * z x) volume l r) :
    (∫ x in l..r, f (x + v) * z x) - (∫ x in l..r, f x * z x) =
      (∫ x in l..r, f (x + v) * (z x - z (x + v))) +
      (∫ x in r..(r + v), f x * z x) -
      (∫ x in l..(l + v), f x * z x) := by
  have ht : IntervalIntegrable (fun x => f (x + v) * z (x + v)) volume l r :=
    by simpa using (hi (l + v) (r + v)).comp_add_right v
  have hs := intervalIntegral.integral_sub hj ht
  have he := intervalIntegral.integral_interval_sub_interval_comm
    (hi l r) (hi (l + v) (r + v)) (hi l (l + v))
  rw [← intervalIntegral.integral_comp_add_right (fun x => f x * z x) v] at he
  have hp : (fun x => f (x + v) * (z x - z (x + v))) =
      (fun x => f (x + v) * z x - f (x + v) * z (x + v)) := by
    ext x; ring
  rw [hp, hs]
  linarith

private lemma translated_memLp {f : ℝ → ℝ} {l r v : ℝ} (hlr : l ≤ r)
    (hf : MemLp f 2 (volume.restrict (Ioc (l + v) (r + v)))) :
    MemLp (fun x => f (x + v)) 2 (volume.restrict (Ioc l r)) := by
  have hlrv : l + v ≤ r + v := by linarith
  have hi : IntervalIntegrable f volume (l + v) (r + v) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hlrv).mpr
      (hf.integrable (by norm_num))
  have hs : IntervalIntegrable (fun x => f x ^ 2) volume (l + v) (r + v) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hlrv).mpr
      ((memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mp hf)
  have hi' : IntervalIntegrable (fun x => f (x + v)) volume l r := by
    simpa using hi.comp_add_right v
  apply (memLp_two_iff_integrable_sq
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hlr).mp hi').aestronglyMeasurable).mpr
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hlr).mp
    (by simpa using hs.comp_add_right v)

lemma covariance_of_norm_bounds {f z : ℝ → ℝ} {l r M F Z U D S : ℝ}
    (hlr : l ≤ r) (hM : 0 < M) (hF0 : 0 ≤ F) (hU0 : 0 ≤ U)
    (hfi : ∀ A B, MemLp f 2 (volume.restrict (Ioc A B)))
    (hzi : ∀ A B, MemLp z 2 (volume.restrict (Ioc A B)))
    (havg : MemLp (windowAverage M f) 2 (volume.restrict (Ioc l r)))
    (hjoint : Integrable (fun p : ℝ × ℝ => f (p.1 + p.2) * z p.1)
      ((volume.restrict (Ioc l r)).prod (volume.restrict (Ioc (0 : ℝ) M))))
    (hfn : ∀ v ∈ Icc (0 : ℝ) M, intervalL2 (l + v) (r + v) f ≤ F)
    (hzn : intervalL2 l r z ≤ Z)
    (han : intervalL2 l r (windowAverage M f) ≤ U)
    (hdn : ∀ v ∈ Icc (0 : ℝ) M,
      intervalL2 l r (fun x => z (x + v) - z x) ≤ D)
    (hstrip : ∀ v ∈ Icc (0 : ℝ) M, ∀ e ∈ ({l, r} : Set ℝ),
      intervalL2 e (e + v) f ≤ F ∧ intervalL2 e (e + v) z ≤ S) :
    |∫ x in l..r, f x * z x| ≤ U * Z + F * D + 2 * F * S := by
  have hi (A B : ℝ) : IntervalIntegrable (fun x => f x * z x) volume A B := by
    rcases le_total A B with h | h
    · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le h).mpr
        ((hfi A B).integrable_mul (hzi A B))
    · exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le h).mpr
        ((hfi B A).integrable_mul (hzi B A))).symm
  have hj (v : ℝ) : IntervalIntegrable (fun x => f (x + v) * z x) volume l r :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hlr).mpr
      ((translated_memLp hlr (hfi _ _)).integrable_mul (hzi l r))
  have hpoint (v : ℝ) (hv : v ∈ Icc (0 : ℝ) M) :
      |(∫ x in l..r, f (x + v) * z x) - ∫ x in l..r, f x * z x| ≤
        F * D + 2 * F * S := by
    have htrans : |∫ x in l..r, f (x + v) * (z x - z (x + v))| ≤ F * D := by
      have hf := translated_memLp hlr (hfi (l + v) (r + v))
      have hz := translated_memLp hlr (hzi (l + v) (r + v))
      have hc := pairing_le hlr hf ((hzi l r).sub hz)
      have hn : intervalL2 l r (fun x => f (x + v)) ≤ F := by
        change Real.sqrt (∫ x in l..r, (fun y => f y ^ 2) (x + v)) ≤ F
        rw [intervalIntegral.integral_comp_add_right (fun y => f y ^ 2) v]
        exact hfn v hv
      have hd : intervalL2 l r (fun x => z x - z (x + v)) ≤ D := by
        have he : intervalL2 l r (fun x => z x - z (x + v)) =
            intervalL2 l r (fun x => z (x + v) - z x) := by
          unfold intervalL2
          congr 1
          apply intervalIntegral.integral_congr
          intro x _
          ring
        rw [he]
        exact hdn v hv
      exact hc.trans (mul_le_mul hn hd (Real.sqrt_nonneg _) hF0)
    have hs (e : ℝ) (he : e ∈ ({l, r} : Set ℝ)) :
        |∫ x in e..(e + v), f x * z x| ≤ F * S :=
      (pairing_le (by linarith [hv.1]) (hfi _ _) (hzi _ _)).trans
        (mul_le_mul (hstrip v hv e he).1 (hstrip v hv e he).2
          (Real.sqrt_nonneg _) hF0)
    rw [translation_pairing_identity hi (hj v)]
    calc
      _ ≤ |(∫ x in l..r, f (x + v) * (z x - z (x + v))) +
          ∫ x in r..(r + v), f x * z x| + |∫ x in l..(l + v), f x * z x| :=
        abs_sub _ _
      _ ≤ (|∫ x in l..r, f (x + v) * (z x - z (x + v))| +
          |∫ x in r..(r + v), f x * z x|) + |∫ x in l..(l + v), f x * z x| :=
        add_le_add (abs_add_le _ _) le_rfl
      _ ≤ _ := by linarith [hs l (by simp), hs r (by simp)]
  have hinner : IntervalIntegrable
      (fun v => ∫ x in l..r, f (x + v) * z x) volume 0 M := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hM.le]
    simpa only [IntegrableOn, intervalIntegral.integral_of_le hlr] using
      hjoint.integral_prod_right
  have hd : |(∫ x in l..r, windowAverage M f x * z x) -
      ∫ x in l..r, f x * z x| ≤ F * D + 2 * F * S := by
    rw [AveragingBounds.windowAverage_pairing_eq hM.le hlr hjoint]
    have he : (1 / M) * (∫ v in (0 : ℝ)..M, ∫ x in l..r, f (x + v) * z x) -
        (∫ x in l..r, f x * z x) =
        (1 / M) * ∫ v in (0 : ℝ)..M,
          ((∫ x in l..r, f (x + v) * z x) - ∫ x in l..r, f x * z x) := by
      rw [intervalIntegral.integral_sub hinner intervalIntegrable_const]
      simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
      field_simp
    rw [he, abs_mul, abs_of_pos (one_div_pos.mpr hM)]
    have hb : |∫ v in (0 : ℝ)..M,
        ((∫ x in l..r, f (x + v) * z x) - ∫ x in l..r, f x * z x)| ≤
        (F * D + 2 * F * S) * M := by
      simpa only [Real.norm_eq_abs, sub_zero, abs_of_pos hM] using
        (intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := M)
          (f := fun v => (∫ x in l..r, f (x + v) * z x) - ∫ x in l..r, f x * z x)
          (C := F * D + 2 * F * S) (by
          intro v hv
          rw [uIoc_of_le hM.le] at hv
          exact hpoint v ⟨hv.1.le, hv.2⟩))
    exact (mul_le_mul_of_nonneg_left hb (by positivity)).trans_eq (by field_simp)
  have ha := (pairing_le hlr havg (hzi l r)).trans
    (mul_le_mul han hzn (Real.sqrt_nonneg _) hU0)
  have ht := abs_sub (∫ x in l..r, windowAverage M f x * z x)
    ((∫ x in l..r, windowAverage M f x * z x) - ∫ x in l..r, f x * z x)
  simp only [sub_sub_cancel] at ht
  linarith

private lemma scale_algebra {Q h m t k A B U D S J : ℝ}
    (hQ : 0 ≤ Q) (hh : 0 < h) (hm : 0 < m) (ht : 0 < t) (hk : 0 < k)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hU : 0 ≤ U) (hD : 0 ≤ D) (hS : 0 ≤ S)
    (hJ : 0 < J) (htk : t ≤ J * k) :
    (U * (h / m) * Real.sqrt Q * Real.sqrt m) * (B * Real.sqrt Q * Real.sqrt k) +
      (A * Real.sqrt Q * Real.sqrt h) * (D * Real.sqrt Q * Real.sqrt m) +
      2 * (A * Real.sqrt Q * Real.sqrt h) *
        (S * Real.sqrt Q * (Real.sqrt (m * k / t) + Real.sqrt t)) ≤
      (U * B + A * D * Real.sqrt J + 2 * A * S) * Q * Real.sqrt (h * k) *
        (Real.sqrt (h / m) + Real.sqrt (m / t) + Real.sqrt (t / k)) := by
  have sqQ := Real.mul_self_sqrt hQ
  have sqm := Real.mul_self_sqrt hm.le
  have sqh := Real.mul_self_sqrt hh.le
  have hsm : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm
  have hsk : 0 < Real.sqrt k := Real.sqrt_pos.mpr hk
  have hsJ : 0 ≤ Real.sqrt J := Real.sqrt_nonneg _
  have he₁ : (h / m) * Real.sqrt m * Real.sqrt k =
      Real.sqrt (h * k) * Real.sqrt (h / m) := by
    rw [Real.sqrt_mul hh.le, Real.sqrt_div hh.le]
    rw [← mul_div_assoc]
    apply (eq_div_iff hsm.ne').mpr
    calc
      _ = h * Real.sqrt k * (Real.sqrt m * Real.sqrt m / m) := by ring
      _ = h * Real.sqrt k := by rw [sqm, div_self hm.ne', mul_one]
      _ = _ := by nlinarith [sqh]
  have he₂ : Real.sqrt h * Real.sqrt (m * k / t) =
      Real.sqrt (h * k) * Real.sqrt (m / t) := by
    rw [Real.sqrt_div (mul_nonneg hm.le hk.le), Real.sqrt_mul hm.le,
      Real.sqrt_mul hh.le, Real.sqrt_div hm.le]
    ring
  have he₃ : Real.sqrt h * Real.sqrt t =
      Real.sqrt (h * k) * Real.sqrt (t / k) := by
    rw [Real.sqrt_mul hh.le, Real.sqrt_div ht.le]
    rw [← mul_div_assoc]
    apply (eq_div_iff hsk.ne').mpr
    ring
  have hratio : Real.sqrt m ≤ Real.sqrt J * Real.sqrt (m * k / t) := by
    rw [← Real.sqrt_mul hJ.le]
    apply Real.sqrt_le_sqrt
    rw [← mul_div_assoc]
    apply (le_div_iff₀ ht).mpr
    nlinarith [mul_le_mul_of_nonneg_left htk hm.le]
  have heU : (U * (h / m) * Real.sqrt Q * Real.sqrt m) *
        (B * Real.sqrt Q * Real.sqrt k) =
      U * B * Q * Real.sqrt (h * k) * Real.sqrt (h / m) := by
    calc
      _ = U * B * (Real.sqrt Q * Real.sqrt Q) *
          ((h / m) * Real.sqrt m * Real.sqrt k) := by ring
      _ = _ := by rw [sqQ, he₁]; ring
  have heD : (A * Real.sqrt Q * Real.sqrt h) * (D * Real.sqrt Q * Real.sqrt m) ≤
      A * D * Real.sqrt J * Q * Real.sqrt (h * k) * Real.sqrt (m / t) := by
    calc
      _ = A * D * (Real.sqrt Q * Real.sqrt Q) * Real.sqrt h * Real.sqrt m := by ring
      _ = A * D * Q * Real.sqrt h * Real.sqrt m := by rw [sqQ]
      _ ≤ A * D * Q * Real.sqrt h * (Real.sqrt J * Real.sqrt (m * k / t)) :=
        mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = A * D * Real.sqrt J * Q *
          (Real.sqrt h * Real.sqrt (m * k / t)) := by ring
      _ = _ := by rw [he₂]; ring
  have heS : 2 * (A * Real.sqrt Q * Real.sqrt h) *
        (S * Real.sqrt Q * (Real.sqrt (m * k / t) + Real.sqrt t)) =
      2 * A * S * Q * Real.sqrt (h * k) *
        (Real.sqrt (m / t) + Real.sqrt (t / k)) := by
    calc
      _ = 2 * A * S * (Real.sqrt Q * Real.sqrt Q) *
          (Real.sqrt h * Real.sqrt (m * k / t) + Real.sqrt h * Real.sqrt t) := by ring
      _ = _ := by rw [sqQ, he₂, he₃]; ring
  rw [heU, heS]
  calc
    _ ≤ U * B * Q * Real.sqrt (h * k) * Real.sqrt (h / m) +
        A * D * Real.sqrt J * Q * Real.sqrt (h * k) * Real.sqrt (m / t) +
        2 * A * S * Q * Real.sqrt (h * k) *
          (Real.sqrt (m / t) + Real.sqrt (t / k)) := by linarith [heD]
    _ ≤ _ := by
      apply sub_nonneg.mp
      ring_nf
      positivity

/-- Four comparable-variance scales control covariance uniformly on all dyadic subintervals. -/
theorem four_scale_covariance_bound
    {E M T : ℝ → ℝ} {a b : ℝ}
    (hE : LocallyBoundedMeasurable E)
    (ha : 0 < a) (hab : a < b) (hb : b < 1)
    (hh : ComparableLengthVarianceUpperFor E (fun X : ℝ => X ^ a))
    (hM : ComparableLengthVarianceUpperFor E M)
    (hT : ComparableLengthVarianceUpperFor E T)
    (hk : ComparableLengthVarianceUpperFor E (fun X : ℝ => X ^ b))
    (hhM : Asymptotics.IsBigO atTop (fun X : ℝ => X ^ a) M)
    (hMT : Asymptotics.IsBigO atTop M T)
    (hTk : Asymptotics.IsBigO atTop T (fun X : ℝ => X ^ b)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℝ in atTop,
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      ∀ l ∈ Icc X (2 * X), ∀ r ∈ Icc l (2 * X),
        |∫ x in l..r, movingIncrement E a s x * movingIncrement E b t x| ≤
          C * (X * Real.log X) * Real.sqrt (X ^ a * X ^ b) *
            (Real.sqrt (X ^ a / M X) + Real.sqrt (M X / T X) +
              Real.sqrt (T X / X ^ b)) := by
  have ha1 : a < 1 := hab.trans hb
  have hb0 : 0 < b := ha.trans hab
  have hMk := hMT.trans hTk
  have hkX : Asymptotics.IsLittleO atTop (fun X : ℝ => X ^ b) (fun X => X) := by
    apply Asymptotics.isLittleO_of_tendsto'
      (by filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX hz; exact (hX.ne' hz).elim)
    apply (tendsto_rpow_neg_atTop (sub_pos.mpr hb)).congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
    rw [show -(1 - b) = b - 1 by ring, Real.rpow_sub hX, Real.rpow_one]
  have hMX := hMk.trans_isLittleO hkX
  obtain ⟨J, hJ, hJv⟩ := hTk.exists_pos
  obtain ⟨Cf, hCf, hfv⟩ := TranslationStripBounds.moving_square_bound_of_comparable
    hE ha ha1 (A := 1) (B := 3) zero_lt_one (by norm_num) hh
  obtain ⟨Cz, hCz, hzv⟩ := TranslationStripBounds.moving_square_bound_of_comparable
    hE hb0 hb (A := 1) (B := 3) zero_lt_one (by norm_num) hk
  obtain ⟨Ca, hCa, hav⟩ := MovingShortAverage.averaged_moving_increment_l2_bound
    hE ha ha1 (A := 1) (B := 2) zero_lt_one (by norm_num) hM hhM hMX
  obtain ⟨Cd, hCd, hdv⟩ := TranslationStripBounds.moving_increment_translation_l2_bound
    hE hb0 hb (A := 1) (B := 2) zero_lt_one (by norm_num) hM hMk
  obtain ⟨Cs, hCs, hsv⟩ := TranslationStripBounds.moving_increment_short_strip_square_bound
    hE hb0 hb (A := 1) (B := 3) zero_lt_one (by norm_num) hT hk hTk
  refine ⟨Ca * Real.sqrt Cz + Real.sqrt Cf * Cd * Real.sqrt J +
    2 * Real.sqrt Cf * Real.sqrt Cs, by positivity, ?_⟩
  filter_upwards [hfv, hzv, hav, hdv, hsv, hM.1, hT.1, hJv.bound,
    hMX.bound (c := 1) zero_lt_one, eventually_ge_atTop (1 : ℝ)] with
    X hfv hzv hav hdv hsv hMX0 hTX0 hJX hMX1 hX
  have hX0 : 0 < X := zero_lt_one.trans_le hX
  have hh0 : 0 < X ^ a := Real.rpow_pos_of_pos hX0 _
  have hk0 : 0 < X ^ b := Real.rpow_pos_of_pos hX0 _
  have hQ : 0 ≤ X * Real.log X := mul_nonneg hX0.le (Real.log_nonneg hX)
  simp only [Real.norm_eq_abs, abs_of_pos hTX0, abs_of_pos hk0] at hJX
  simp only [Real.norm_eq_abs, abs_of_pos hMX0, abs_of_pos hX0, one_mul] at hMX1
  simp only [one_mul] at hfv hzv hav hdv hsv
  intro s hs t ht l hl r hr
  have hlr : l ≤ r := hr.1
  let f := movingIncrement E a s
  let z := movingIncrement E b t
  have hfi := moving_memLp hE (s := s) ha
  have hzi := moving_memLp hE (s := t) hb0
  have hfn : ∀ A B : ℝ, X ≤ A → A ≤ B → B ≤ 3 * X →
      intervalL2 A B f ≤ Real.sqrt Cf * Real.sqrt (X * Real.log X) * Real.sqrt (X ^ a) := by
    intro A B hXA hAB hBX
    have hi : IntervalIntegrable (fun x => f x ^ 2) volume X (3 * X) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).mpr
        ((memLp_two_iff_integrable_sq (hfi X (3 * X)).aestronglyMeasurable).mp (hfi X (3 * X)))
    have hmono := intervalIntegral.integral_mono_interval hXA hAB hBX
      (Eventually.of_forall (fun x => sq_nonneg (f x))) hi
    apply (Real.sqrt_le_sqrt (hmono.trans (hfv s hs))).trans_eq
    rw [show Cf * X * X ^ a * Real.log X = Cf * (X * Real.log X) * X ^ a by ring,
      Real.sqrt_mul (mul_nonneg hCf.le hQ), Real.sqrt_mul hCf.le]
  have hzn : intervalL2 l r z ≤
      Real.sqrt Cz * Real.sqrt (X * Real.log X) * Real.sqrt (X ^ b) := by
    have hi : IntervalIntegrable (fun x => z x ^ 2) volume X (3 * X) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).mpr
        ((memLp_two_iff_integrable_sq (hzi X (3 * X)).aestronglyMeasurable).mp (hzi X (3 * X)))
    apply (Real.sqrt_le_sqrt ((intervalIntegral.integral_mono_interval hl.1 hlr
      (by linarith [hr.2]) (Eventually.of_forall (fun x => sq_nonneg (z x))) hi).trans
        (hzv t ht))).trans_eq
    rw [show Cz * X * X ^ b * Real.log X = Cz * (X * Real.log X) * X ^ b by ring,
      Real.sqrt_mul (mul_nonneg hCz.le hQ), Real.sqrt_mul hCz.le]
  have han : intervalL2 l r (windowAverage (M X) f) ≤
      Ca * (X ^ a / M X) * Real.sqrt (X * Real.log X) * Real.sqrt (M X) := by
    have hmem := average_memLp (s := s) (M := M X) (l := X) (r := 2 * X)
      hE ha
    have hi : IntervalIntegrable (fun x => windowAverage (M X) f x ^ 2) volume X (2 * X) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).mpr
        ((memLp_two_iff_integrable_sq hmem.aestronglyMeasurable).mp hmem)
    exact (Real.sqrt_le_sqrt (intervalIntegral.integral_mono_interval hl.1 hlr hr.2
      (Eventually.of_forall (fun x => sq_nonneg _)) hi)).trans (hav s hs)
  have hstrip : ∀ v ∈ Icc (0 : ℝ) (M X), ∀ e ∈ ({l, r} : Set ℝ),
      intervalL2 e (e + v) f ≤
        Real.sqrt Cf * Real.sqrt (X * Real.log X) * Real.sqrt (X ^ a) ∧
      intervalL2 e (e + v) z ≤
        Real.sqrt Cs * Real.sqrt (X * Real.log X) *
          (Real.sqrt (M X * X ^ b / T X) + Real.sqrt (T X)) := by
    intro v hv e he
    have heX : e ∈ Icc X (2 * X) := by
      simp only [mem_insert_iff, mem_singleton_iff] at he
      rcases he with rfl | rfl
      · exact hl
      · exact ⟨hl.1.trans hr.1, hr.2⟩
    have hev : e + v ≤ 3 * X := by linarith [heX.2, hv.2]
    refine ⟨hfn e (e + v) heX.1 (by linarith [hv.1]) hev, ?_⟩
    have hbnd := hsv t ht (M X) hMX0.le e ⟨heX.1, by linarith [heX.2]⟩
      (e + v) ⟨by linarith [hv.1], hev⟩ (by linarith [hv.2])
    apply (Real.sqrt_le_sqrt hbnd).trans
    rw [Real.sqrt_mul (mul_nonneg hCs.le hQ), Real.sqrt_mul hCs.le]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · have hsq₁ := Real.sq_sqrt (show 0 ≤ M X * X ^ b / T X by positivity)
      have hsq₂ := Real.sq_sqrt hTX0.le
      nlinarith [mul_nonneg (Real.sqrt_nonneg (M X * X ^ b / T X))
        (Real.sqrt_nonneg (T X))]
  have hjoint : Integrable (fun p : ℝ × ℝ => f (p.1 + p.2) * z p.1)
      ((volume.restrict (Ioc l r)).prod (volume.restrict (Ioc (0 : ℝ) (M X)))) := by
    rw [Measure.prod_restrict]
    have hi := increment_product_comp_integrableOn (μ := volume.prod volume)
      (K := Icc l r ×ˢ Icc (0 : ℝ) (M X))
      (u := fun p : ℝ × ℝ => s * (p.1 + p.2) ^ a)
      (x := fun p : ℝ × ℝ => p.1 + p.2)
      (v := fun p : ℝ × ℝ => t * p.1 ^ b) (y := fun p : ℝ × ℝ => p.1)
      hE (isCompact_Icc.prod isCompact_Icc)
      (continuous_const.mul ((Real.continuous_rpow_const ha.le).comp
        (continuous_fst.add continuous_snd))) (continuous_fst.add continuous_snd)
      (continuous_const.mul ((Real.continuous_rpow_const hb0.le).comp continuous_fst))
      continuous_fst
    exact hi.mono_set (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  have hcov := covariance_of_norm_bounds hlr hMX0 (by positivity) (by positivity)
    hfi hzi (average_memLp hE ha) hjoint
    (by
      intro v hv
      exact hfn (l + v) (r + v) (by linarith [hl.1, hv.1])
        (by linarith) (by linarith [hr.2, hv.2]))
    hzn han (fun v hv => hdv t ht v hv l hl r hr) hstrip
  exact hcov.trans (scale_algebra hQ hh0 hMX0 hTX0 hk0
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hCa.le hCd.le (Real.sqrt_nonneg _)
    hJ hJX)

end
end D5.S3.Arith.Robin.ForwardKernel.FourScaleCovariance
