/- GID: D5/S3/Entropy/RenyiCombining/HircheCachinCombiningConcavity
   generality: G
   mirror-B: D5/B/S3/Entropy/RenyiCombining/HircheCachinCombiningConcavity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Binary Renyi information combining is concave at every real order at least two. -/

import D5.S3.Entropy.RenyiCombining.CachinElasticityMonotone
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Homeomorph.Lemmas

/-! Concavity of binary Renyi information combining at real orders at least two. -/

noncomputable section

open Set Filter
open scoped Topology

namespace D5.S3.Entropy.RenyiCombining.HircheCachinCombiningConcavity

noncomputable def h (α p : ℝ) : ℝ :=
  Real.log (p ^ α + (1 - p) ^ α) / (1 - α)

noncomputable def hInv (α : ℝ) : ℝ → ℝ :=
  Function.invFunOn (h α) (Icc 0 (1 / 2))

def star (a b : ℝ) : ℝ := a + b - 2 * a * b

noncomputable def G (α x y : ℝ) : ℝ := h α (star (hInv α x) (hInv α y))

def claim : Prop := ∀ α : ℝ, 2 ≤ α → ∀ y ∈ Icc 0 (Real.log 2),
  ConcaveOn ℝ (Icc 0 (Real.log 2)) (fun x => G α x y)

private def psi (α t : ℝ) : ℝ := h α ((1 - t) / 2)
private def inverseBias (α x : ℝ) : ℝ := 1 - 2 * hInv α x
private def slope (α t : ℝ) : ℝ :=
  α * (((1 + t) / 2) ^ (α - 1) - ((1 - t) / 2) ^ (α - 1)) /
    (2 * (α - 1) * (((1 + t) / 2) ^ α + ((1 - t) / 2) ^ α))

private lemma powerSum_pos {α p : ℝ} (hp : p ∈ Icc 0 (1 / 2)) :
    0 < p ^ α + (1 - p) ^ α := by
  have hw : 0 < 1 - p := by linarith [hp.2]
  exact add_pos_of_nonneg_of_pos (Real.rpow_nonneg hp.1 _) (Real.rpow_pos_of_pos hw _)

private lemma h_continuousOn {α : ℝ} (hα : 2 ≤ α) : ContinuousOn (h α) (Icc 0 (1 / 2)) := by
  apply ContinuousOn.div_const
  apply ContinuousOn.log _ (fun p hp => (powerSum_pos hp).ne')
  exact (continuousOn_id.rpow_const (fun _ _ => Or.inr (by linarith))).add
    ((continuousOn_const.sub continuousOn_id).rpow_const (fun _ _ => Or.inr (by linarith)))

private lemma h_zero {α : ℝ} (hα : 2 ≤ α) : h α 0 = 0 := by
  simp [h, Real.zero_rpow (show α ≠ 0 by linarith)]

private lemma h_half {α : ℝ} (hα : 2 ≤ α) : h α (1 / 2) = Real.log 2 := by
  have ha : 1 - α ≠ 0 := by linarith
  have hp : (0 : ℝ) < 1 / 2 := by norm_num
  have he : (1 / 2 : ℝ) ^ α + (1 - 1 / 2 : ℝ) ^ α =
      (1 / 2 : ℝ) ^ (α - 1) := by
    rw [show (1 - 1 / 2 : ℝ) = 1 / 2 by ring,
      Real.rpow_sub hp _ _, Real.rpow_one]
    ring
  rw [h, he, Real.log_rpow hp, Real.log_div (by norm_num) (by norm_num), Real.log_one]
  field_simp
  <;> ring

private lemma h_hasDerivAt {α p : ℝ} (hα : 2 ≤ α) (hp : p ∈ Ioo 0 (1 / 2)) :
    HasDerivAt (h α)
      (α * (p ^ (α - 1) - (1 - p) ^ (α - 1)) /
        ((1 - α) * (p ^ α + (1 - p) ^ α))) p := by
  have hw : 0 < 1 - p := by linarith [hp.2]
  have hd := (((hasDerivAt_id p).rpow_const (p := α) (Or.inl hp.1.ne')).add
    (((hasDerivAt_const p 1).sub (hasDerivAt_id p)).rpow_const
      (p := α) (Or.inl hw.ne'))).log (powerSum_pos ⟨hp.1.le, hp.2.le⟩).ne'
  convert hd.div_const (1 - α) using 1 <;> dsimp
  · rfl
  · field_simp
    <;> ring

private lemma h_strictMonoOn {α : ℝ} (hα : 2 ≤ α) : StrictMonoOn (h α) (Icc 0 (1 / 2)) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) (h_continuousOn hα)
  intro p hp
  rw [interior_Icc] at hp
  rw [(h_hasDerivAt hα hp).deriv]
  have hpw : p < 1 - p := by linarith [hp.2]
  have hr := Real.rpow_lt_rpow hp.1.le hpw (show 0 < α - 1 by linarith)
  have hs := powerSum_pos (α := α) ⟨hp.1.le, hp.2.le⟩
  exact div_pos_of_neg_of_neg (mul_neg_of_pos_of_neg (by linarith) (sub_neg.mpr hr))
    (mul_neg_of_neg_of_pos (by linarith) hs)

private lemma h_image {α : ℝ} (hα : 2 ≤ α) : h α '' Icc 0 (1 / 2) = Icc 0 (Real.log 2) := by
  rw [(h_continuousOn hα).image_Icc_of_monotoneOn (by norm_num)
    (h_strictMonoOn hα).monotoneOn, h_zero hα, h_half hα]

private lemma hInv_spec {α x : ℝ} (hα : 2 ≤ α) (hx : x ∈ Icc 0 (Real.log 2)) :
    hInv α x ∈ Icc 0 (1 / 2) ∧ h α (hInv α x) = x := by
  have him : x ∈ h α '' Icc 0 (1 / 2) := by rw [h_image hα]; exact hx
  exact ⟨Function.invFunOn_mem him, Function.invFunOn_eq him⟩

private lemma hInv_h {α p : ℝ} (hα : 2 ≤ α) (hp : p ∈ Icc 0 (1 / 2)) :
    hInv α (h α p) = p :=
  (h_strictMonoOn hα).injOn.leftInvOn_invFunOn hp

private lemma hInv_continuousOn {α : ℝ} (hα : 2 ≤ α) :
    ContinuousOn (hInv α) (Icc 0 (Real.log 2)) := by
  let e : Icc (0 : ℝ) (1 / 2) ≃ Icc (0 : ℝ) (Real.log 2) :=
    { toFun := fun p => ⟨h α p, by rw [← h_image hα]; exact mem_image_of_mem _ p.property⟩
      invFun := fun x => ⟨hInv α x, (hInv_spec hα x.property).1⟩
      left_inv := fun p => Subtype.ext (hInv_h hα p.property)
      right_inv := fun x => Subtype.ext (hInv_spec hα x.property).2 }
  have he : Continuous e :=
    ((h_continuousOn hα).domRestrict).subtype_mk _
  exact continuousOn_iff_continuous_domRestrict.mpr
    (continuous_subtype_val.comp he.continuous_symm_of_equiv_compact_to_t2)

private lemma hInv_interior {α x : ℝ} (hα : 2 ≤ α) (hx : x ∈ Ioo 0 (Real.log 2)) :
    hInv α x ∈ Ioo 0 (1 / 2) := by
  obtain ⟨hp, he⟩ := hInv_spec hα ⟨hx.1.le, hx.2.le⟩
  constructor
  · by_contra hn
    have hz : hInv α x = 0 := le_antisymm (not_lt.mp hn) hp.1
    rw [hz, h_zero hα] at he
    linarith [hx.1]
  · by_contra hn
    have hz : hInv α x = 1 / 2 := le_antisymm hp.2 (not_lt.mp hn)
    rw [hz, h_half hα] at he
    linarith [hx.2]

private lemma psi_continuousOn {α : ℝ} (hα : 2 ≤ α) : ContinuousOn (psi α) (Icc 0 1) :=
  (h_continuousOn hα).comp ((continuousOn_const.sub continuousOn_id).div_const 2)
    (fun t ht => ⟨by linarith [ht.2], by linarith [ht.1]⟩)

private lemma slope_pos {α t : ℝ} (hα : 2 ≤ α) (ht : t ∈ Ioo 0 1) : 0 < slope α t := by
  have hw : 0 < (1 - t) / 2 := by linarith [ht.2]
  have hu : 0 < (1 + t) / 2 := by linarith [ht.1]
  have hwu : (1 - t) / 2 < (1 + t) / 2 := by linarith [ht.1]
  have hr := Real.rpow_lt_rpow hw.le hwu (show 0 < α - 1 by linarith)
  unfold slope
  exact div_pos (mul_pos (by linarith) (sub_pos.mpr hr))
    (mul_pos (mul_pos (by norm_num) (by linarith))
      (add_pos (Real.rpow_pos_of_pos hu _) (Real.rpow_pos_of_pos hw _)))

private lemma psi_hasDerivAt {α t : ℝ} (hα : 2 ≤ α) (ht : t ∈ Ioo 0 1) :
    HasDerivAt (psi α) (-slope α t) t := by
  have hp : (1 - t) / 2 ∈ Ioo (0 : ℝ) (1 / 2) :=
    ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hd := (h_hasDerivAt hα hp).comp t
    (((hasDerivAt_const t 1).sub (hasDerivAt_id t)).div_const 2)
  convert hd using 1
  · rfl
  · rw [show 1 - (1 - t) / 2 = (1 + t) / 2 by ring]
    unfold slope
    have hs : 0 < ((1 + t) / 2) ^ α + ((1 - t) / 2) ^ α :=
      add_pos (Real.rpow_pos_of_pos (by linarith [ht.1]) _)
        (Real.rpow_pos_of_pos (by linarith [ht.2]) _)
    rw [add_comm (((1 - t) / 2) ^ α) (((1 + t) / 2) ^ α)]
    field_simp [(show α - 1 ≠ 0 by linarith), (show 1 - α ≠ 0 by linarith), hs.ne']
    <;> ring

private lemma psi_strictAntiOn {α : ℝ} (hα : 2 ≤ α) : StrictAntiOn (psi α) (Icc 0 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _) (psi_continuousOn hα)
  intro t ht
  rw [interior_Icc] at ht
  rw [(psi_hasDerivAt hα ht).deriv]
  exact neg_neg_of_pos (slope_pos hα ht)

private lemma inverseBias_spec {α x : ℝ} (hα : 2 ≤ α) (hx : x ∈ Icc 0 (Real.log 2)) :
    inverseBias α x ∈ Icc 0 1 ∧ psi α (inverseBias α x) = x := by
  obtain ⟨hp, he⟩ := hInv_spec hα hx
  constructor
  · constructor <;> dsimp [inverseBias] <;> linarith [hp.1, hp.2]
  · simpa [psi, inverseBias, show (1 - (1 - 2 * hInv α x)) / 2 = hInv α x by ring] using he

private lemma inverseBias_interior {α x : ℝ} (hα : 2 ≤ α) (hx : x ∈ Ioo 0 (Real.log 2)) :
    inverseBias α x ∈ Ioo 0 1 := by
  have hp := hInv_interior hα hx
  constructor <;> dsimp [inverseBias] <;> linarith [hp.1, hp.2]

private lemma inverseBias_continuousOn {α : ℝ} (hα : 2 ≤ α) :
    ContinuousOn (inverseBias α) (Icc 0 (Real.log 2)) :=
  continuousOn_const.sub (continuousOn_const.mul (hInv_continuousOn hα))

private lemma inverseBias_hasDerivAt {α x : ℝ} (hα : 2 ≤ α) (hx : x ∈ Ioo 0 (Real.log 2)) :
    HasDerivAt (inverseBias α) (-slope α (inverseBias α x))⁻¹ x := by
  apply HasDerivAt.of_local_left_inverse
    ((inverseBias_continuousOn hα x ⟨hx.1.le, hx.2.le⟩).continuousAt
      (Icc_mem_nhds hx.1 hx.2))
    (psi_hasDerivAt hα (inverseBias_interior hα hx))
    (neg_ne_zero.mpr (slope_pos hα (inverseBias_interior hα hx)).ne')
  filter_upwards [Icc_mem_nhds hx.1 hx.2] with z hz
  exact (inverseBias_spec hα hz).2

private def ratio (t : ℝ) : ℝ := (1 - t) / (1 + t)

private lemma ratio_mem {t : ℝ} (ht : t ∈ Ioo 0 1) : ratio t ∈ Ioo 0 1 := by
  have hd : 0 < 1 + t := by linarith [ht.1]
  exact ⟨div_pos (by linarith [ht.2]) hd,
    (div_lt_one hd).mpr (by linarith [ht.1])⟩

private lemma ratio_hasDerivAt {t : ℝ} (ht : 0 < t) :
    HasDerivAt ratio (-2 / (1 + t) ^ (2 : ℕ)) t := by
  convert (((hasDerivAt_const t 1).sub (hasDerivAt_id t)).div
    ((hasDerivAt_const t 1).add (hasDerivAt_id t)) (by linarith : 1 + t ≠ 0)) using 1
  · rfl
  · dsimp
    ring

private lemma ratio_anti : AntitoneOn ratio (Ioo 0 1) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ioo _ _)
    (fun t ht => (ratio_hasDerivAt ht.1).continuousAt.continuousWithinAt)
    (fun t ht => (ratio_hasDerivAt (interior_subset ht).1).differentiableAt.differentiableWithinAt)
  intro t ht
  rw [(ratio_hasDerivAt (interior_subset ht).1).deriv]
  exact div_nonpos_of_nonpos_of_nonneg (by norm_num) (sq_nonneg _)

private lemma T_ratio {α t : ℝ} (ht : t ∈ Ioo 0 1) :
    CachinElasticityMonotone.T (α - 1) (ratio t) =
      ((((1 + t) / 2) ^ (α - 1) - ((1 - t) / 2) ^ (α - 1)) /
        (((1 + t) / 2) ^ (α - 1) + ((1 - t) / 2) ^ (α - 1))) := by
  have hu : 0 < (1 + t) / 2 := by linarith [ht.1]
  have hw : 0 < (1 - t) / 2 := by linarith [ht.2]
  have he : ratio t = ((1 - t) / 2) / ((1 + t) / 2) := by
    unfold ratio
    field_simp
  rw [CachinElasticityMonotone.T, he, Real.div_rpow hw.le hu.le]
  have hU := Real.rpow_pos_of_pos hu (α - 1)
  have hW := Real.rpow_pos_of_pos hw (α - 1)
  field_simp
  <;> ring

private lemma slope_eq {α t : ℝ} (hα : 2 ≤ α) (ht : t ∈ Ioo 0 1) :
    slope α t = α / (α - 1) * CachinElasticityMonotone.T (α - 1) (ratio t) /
      (1 + t * CachinElasticityMonotone.T (α - 1) (ratio t)) := by
  have hu : 0 < (1 + t) / 2 := by linarith [ht.1]
  have hw : 0 < (1 - t) / 2 := by linarith [ht.2]
  have hU := Real.rpow_pos_of_pos hu (α - 1)
  have hW := Real.rpow_pos_of_pos hw (α - 1)
  have huα : ((1 + t) / 2) ^ α = ((1 + t) / 2) ^ (α - 1) * ((1 + t) / 2) := by
    simpa using (Real.rpow_add_one hu.ne' (α - 1))
  have hwα : ((1 - t) / 2) ^ α = ((1 - t) / 2) ^ (α - 1) * ((1 - t) / 2) := by
    simpa using (Real.rpow_add_one hw.ne' (α - 1))
  rw [T_ratio ht]
  unfold slope
  rw [huα, hwα]
  field_simp
  <;> ring

private lemma T_comp_hasDerivAt {n t : ℝ} (hn : 1 ≤ n) (ht : t ∈ Ioo 0 1) :
    HasDerivAt (fun s => CachinElasticityMonotone.T n (ratio s))
      (CachinElasticityMonotone.T n (ratio t) * CachinElasticityMonotone.A n (ratio t) / t) t := by
  have hr := ratio_mem ht
  have hd := (CachinElasticityMonotone.T_hasDerivAt n (ratio t) hr.1).comp t (ratio_hasDerivAt ht.1)
  convert hd using 1
  · rfl
  · rw [CachinElasticityMonotone.A_eq n (ratio t) hr.1]
    unfold CachinElasticityMonotone.T
    have hp := Real.rpow_pos_of_pos hr.1 n
    have hl := Real.rpow_lt_one hr.1.le hr.2 (show 0 < n by linarith)
    have hd0 : 1 + t ≠ 0 := by linarith [ht.1]
    field_simp [hd0, ht.1.ne', (sub_pos.mpr hl).ne', (by linarith : 1 + (ratio t) ^ n ≠ 0)]
    unfold ratio
    field_simp [hd0]
    <;> ring

private lemma slope_hasDerivAt {α t : ℝ} (hα : 2 ≤ α) (ht : t ∈ Ioo 0 1) :
    HasDerivAt (slope α)
      (slope α t * CachinElasticityMonotone.F (α - 1) (ratio t) / t) t := by
  have hn : 1 ≤ α - 1 := by linarith
  have hr := ratio_mem ht
  have hT := CachinElasticityMonotone.T_pos (α - 1) (ratio t) hn hr
  have hd0 : 1 + t * CachinElasticityMonotone.T (α - 1) (ratio t) ≠ 0 :=
    (add_pos zero_lt_one (mul_pos ht.1 hT)).ne'
  have he : (1 - ratio t) / (1 + ratio t) = t := by
    apply (div_eq_iff (show 1 + ratio t ≠ 0 by linarith [hr.1])).mpr
    unfold ratio
    field_simp [show 1 + t ≠ 0 by linarith [ht.1]]
    <;> ring
  have hd := ((T_comp_hasDerivAt hn ht).const_mul (α / (α - 1))).div
    ((hasDerivAt_const t 1).add ((hasDerivAt_id t).mul (T_comp_hasDerivAt hn ht))) hd0
  have hd' : HasDerivAt (slope α)
      (((α / (α - 1) * (CachinElasticityMonotone.T (α - 1) (ratio t) * CachinElasticityMonotone.A (α - 1) (ratio t) / t)) *
          (1 + t * CachinElasticityMonotone.T (α - 1) (ratio t)) -
        (α / (α - 1) * CachinElasticityMonotone.T (α - 1) (ratio t)) *
          (CachinElasticityMonotone.T (α - 1) (ratio t) + t * (CachinElasticityMonotone.T (α - 1) (ratio t) * CachinElasticityMonotone.A (α - 1) (ratio t) / t))) /
        (1 + t * CachinElasticityMonotone.T (α - 1) (ratio t)) ^ (2 : ℕ)) t := by
    dsimp at hd
    simp only [zero_add, one_mul] at hd
    apply hd.congr_of_eventuallyEq
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    exact slope_eq hα hs
  convert hd' using 1
  rw [slope_eq hα ht]
  unfold CachinElasticityMonotone.F CachinElasticityMonotone.B
  rw [he]
  field_simp [hd0, ht.1.ne']
  <;> ring

private lemma elasticity_anti {α : ℝ} (hα : 2 ≤ α) :
    AntitoneOn (fun t => CachinElasticityMonotone.F (α - 1) (ratio t)) (Ioo 0 1) := by
  intro a ha b hb hab
  exact CachinElasticityMonotone.monotoneOn_F (α - 1) (by linarith) (ratio_mem hb) (ratio_mem ha)
    (ratio_anti ha hb hab)

private lemma slope_ratio_monotone {α v : ℝ} (hα : 2 ≤ α) (hv : v ∈ Ioo 0 1) :
    MonotoneOn (fun t => v * slope α (v * t) / slope α t) (Ioo 0 1) := by
  have hvt : ∀ t ∈ Ioo (0 : ℝ) 1, v * t ∈ Ioo (0 : ℝ) 1 := by
    intro t ht
    exact ⟨mul_pos hv.1 ht.1, by nlinarith [ht.2, mul_pos (sub_pos.mpr hv.2) ht.1]⟩
  have hd : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt
      (fun s => v * slope α (v * s) / slope α s)
      (v * slope α (v * t) / (t * slope α t) *
        (CachinElasticityMonotone.F (α - 1) (ratio (v * t)) - CachinElasticityMonotone.F (α - 1) (ratio t))) t := by
    intro t ht
    have hf := (slope_hasDerivAt hα (hvt t ht)).comp t ((hasDerivAt_id t).const_mul v)
    convert (hf.const_mul v).div (slope_hasDerivAt hα ht) (slope_pos hα ht).ne' using 1
    · rfl
    · dsimp
      field_simp [hv.1.ne', ht.1.ne', (slope_pos hα ht).ne']
      <;> ring
  apply monotoneOn_of_deriv_nonneg (convex_Ioo _ _)
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt)
  intro t ht
  have ht' := interior_subset ht
  rw [(hd t ht').deriv]
  apply mul_nonneg
  · exact div_nonneg (mul_pos hv.1 (slope_pos hα (hvt t ht'))).le
      (mul_pos ht'.1 (slope_pos hα ht')).le
  · exact sub_nonneg.mpr (elasticity_anti hα (hvt t ht') ht'
      (by nlinarith [hv.2, ht'.1] : v * t ≤ t))

private lemma bias_combining (α x y : ℝ) :
    G α x y = psi α (inverseBias α y * inverseBias α x) := by
  unfold G psi inverseBias star
  congr 1
  ring

private lemma transported_continuousOn {α v : ℝ} (hα : 2 ≤ α) (hv : v ∈ Icc 0 1) :
    ContinuousOn (fun x => psi α (v * inverseBias α x)) (Icc 0 (Real.log 2)) := by
  apply (psi_continuousOn hα).comp (continuousOn_const.mul (inverseBias_continuousOn hα))
  intro x hx
  have ht := (inverseBias_spec hα hx).1
  exact ⟨mul_nonneg hv.1 ht.1, by
    change v * inverseBias α x ≤ 1
    nlinarith [ht.2, mul_nonneg (sub_nonneg.mpr hv.2) ht.1]⟩

private lemma transported_hasDerivAt {α v x : ℝ} (hα : 2 ≤ α) (hv : v ∈ Ioo 0 1)
    (hx : x ∈ Ioo 0 (Real.log 2)) :
    HasDerivAt (fun z => psi α (v * inverseBias α z))
      (v * slope α (v * inverseBias α x) / slope α (inverseBias α x)) x := by
  have ht := inverseBias_interior hα hx
  have hvt : v * inverseBias α x ∈ Ioo (0 : ℝ) 1 :=
    ⟨mul_pos hv.1 ht.1, by nlinarith [ht.2, mul_pos (sub_pos.mpr hv.2) ht.1]⟩
  convert (psi_hasDerivAt hα hvt).comp x ((inverseBias_hasDerivAt hα hx).const_mul v) using 1
  · rfl
  · simp only [inv_neg, div_eq_mul_inv]
    ring

private lemma inverseBias_anti {α : ℝ} (hα : 2 ≤ α) :
    AntitoneOn (inverseBias α) (Icc 0 (Real.log 2)) := by
  intro x hx y hy hxy
  have ht := inverseBias_spec hα hx
  have hu := inverseBias_spec hα hy
  by_contra hbad
  have hr := psi_strictAntiOn hα ht.1 hu.1 (not_le.mp hbad)
  rw [ht.2, hu.2] at hr
  exact (not_lt_of_ge hxy) hr

private lemma transported_concaveOn {α v : ℝ} (hα : 2 ≤ α) (hv : v ∈ Icc 0 1) :
    ConcaveOn ℝ (Icc 0 (Real.log 2)) (fun x => psi α (v * inverseBias α x)) := by
  by_cases hv0 : v = 0
  · subst v
    simpa using concaveOn_const (psi α 0) (convex_Icc (0 : ℝ) (Real.log 2))
  by_cases hv1 : v = 1
  · subst v
    apply (concaveOn_id (convex_Icc (0 : ℝ) (Real.log 2))).congr
    intro x hx
    simpa using (inverseBias_spec hα hx).2.symm
  have hv' : v ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne hv.1 (Ne.symm hv0), lt_of_le_of_ne hv.2 hv1⟩
  apply AntitoneOn.concaveOn_of_deriv (convex_Icc _ _) (transported_continuousOn hα hv)
  · intro x hx
    rw [interior_Icc] at hx
    exact (transported_hasDerivAt hα hv' hx).differentiableAt.differentiableWithinAt
  · intro x hx y hy hxy
    rw [interior_Icc] at hx hy
    rw [(transported_hasDerivAt hα hv' hx).deriv, (transported_hasDerivAt hα hv' hy).deriv]
    exact slope_ratio_monotone hα hv' (inverseBias_interior hα hy)
      (inverseBias_interior hα hx) (inverseBias_anti hα ⟨hx.1.le, hx.2.le⟩
        ⟨hy.1.le, hy.2.le⟩ hxy)

theorem result : claim := by
  intro α hα y hy
  simpa only [bias_combining] using
    transported_concaveOn hα (inverseBias_spec hα hy).1

end D5.S3.Entropy.RenyiCombining.HircheCachinCombiningConcavity
