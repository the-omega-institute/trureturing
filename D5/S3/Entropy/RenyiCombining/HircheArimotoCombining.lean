/- GID: D5/S3/Entropy/RenyiCombining/HircheArimotoCombining
   generality: G
   mirror-B: D5/B/S3/Entropy/RenyiCombining/HircheArimotoCombining
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Binary Arimoto combining in its real-power coordinate. -/

import D5.S3.Entropy.RenyiCombining.HircheCachinCombiningConcavity
import D5.S3.Entropy.RenyiCombining.ArimotoHyperbolic
import D5.S3.Weil.Budget.LinearCayleyScaleFlow
import Mathlib.Tactic.LinearCombination

/-! Real-power coordinates and the probability inverse on the binary half interval. -/

open Set Filter
open scoped Topology
noncomputable section
namespace D5.S3.Entropy.RenyiCombining.HircheArimotoCombining

private abbrev C := D5.S3.Entropy.RenyiCombining.HircheCachinCombiningConcavity.h

def k (α p : ℝ) : ℝ := (p ^ α + (1 - p) ^ α) ^ (1 / α)
def delta (α : ℝ) : ℝ := (2 : ℝ) ^ ((1 - α) / α)
def I (α : ℝ) : Set ℝ := Icc (min 1 (delta α)) (max 1 (delta α))
def kInv (α : ℝ) : ℝ → ℝ := Function.invFunOn (k α) (Icc 0 (1 / 2))
abbrev star := BinaryRenyiCombining.bconv
def G (α x y : ℝ) : ℝ := k α (star (kInv α x) (kInv α y))

def claim : Prop := ∃ αhat : ℝ, 1 < αhat ∧ αhat < (15783 : ℝ) / 10000 ∧
  (∀ α : ℝ, 0 < α → α < 1 → ∀ y ∈ I α,
    ConvexOn ℝ (I α) (fun x => G α x y)) ∧
  (∀ α : ℝ, 1 < α → α ≤ αhat → ∀ y ∈ I α,
    ConcaveOn ℝ (I α) (fun x => G α x y))

private def c (α : ℝ) : ℝ := (1 - α) / α
private def psi (α t : ℝ) : ℝ := k α ((1 - t) / 2)
private def slope (α t : ℝ) : ℝ :=
  -c α * psi α t * HircheCachinCombiningConcavity.slope α t
private def inverseBias (α x : ℝ) : ℝ := 1 - 2 * kInv α x

private lemma k_eq_exp {α p : ℝ} (hne : α ≠ 1) (hp : p ∈ Icc 0 (1 / 2)) :
    k α p = Real.exp (c α * C α p) := by
  have hs := HircheCachinCombiningConcavity.powerSum_pos (α := α) hp
  rw [k, Real.rpow_def_of_pos hs]
  dsimp [c, C]
  rw [HircheCachinCombiningConcavity.h_eq]
  simp only [if_neg hne]
  congr 1
  field_simp
  <;> ring

private lemma k_pos {α p : ℝ} (hp : p ∈ Icc 0 (1 / 2)) : 0 < k α p :=
  Real.rpow_pos_of_pos (HircheCachinCombiningConcavity.powerSum_pos hp) _

private lemma k_continuousOn {α : ℝ} (hα : 0 < α) :
    ContinuousOn (k α) (Icc 0 (1 / 2)) := by
  apply ContinuousOn.rpow_const
  · exact (continuousOn_id.rpow_const (fun _ _ => Or.inr hα.le)).add
      ((continuousOn_const.sub continuousOn_id).rpow_const (fun _ _ => Or.inr hα.le))
  · intro p hp
    exact Or.inl (HircheCachinCombiningConcavity.powerSum_pos hp).ne'

private lemma k_zero {α : ℝ} (hα : 0 < α) : k α 0 = 1 := by
  simp [k, Real.zero_rpow hα.ne']

private lemma k_half {α : ℝ} (hα : 0 < α) : k α (1 / 2) = delta α := by
  have hp : (0 : ℝ) < 1 / 2 := by norm_num
  have he : (1 / 2 : ℝ) ^ α + (1 - 1 / 2 : ℝ) ^ α = (1 / 2 : ℝ) ^ (α - 1) := by
    rw [show (1 - 1 / 2 : ℝ) = 1 / 2 by ring, Real.rpow_sub hp _ _, Real.rpow_one]
    ring
  rw [k, he, ← Real.rpow_mul hp.le, one_div, ← Real.rpow_neg_eq_inv_rpow]
  unfold delta
  congr 1
  field_simp
  <;> ring

private lemma k_strictMonoOn {α : ℝ} (hα : 0 < α) (ha : α < 1) :
    StrictMonoOn (k α) (Icc 0 (1 / 2)) := by
  intro p hp q hq hpq
  rw [k_eq_exp (ne_of_lt ha) hp, k_eq_exp (ne_of_lt ha) hq, Real.exp_lt_exp]
  exact mul_lt_mul_of_pos_left (HircheCachinCombiningConcavity.h_strictMonoOn hα hp hq hpq)
    (div_pos (sub_pos.mpr ha) hα)

private lemma k_strictAntiOn {α : ℝ} (ha : 1 < α) :
    StrictAntiOn (k α) (Icc 0 (1 / 2)) := by
  intro p hp q hq hpq
  rw [k_eq_exp (ne_of_gt ha) hq, k_eq_exp (ne_of_gt ha) hp, Real.exp_lt_exp]
  exact mul_lt_mul_of_neg_left
    (HircheCachinCombiningConcavity.h_strictMonoOn (by linarith) hp hq hpq)
    (div_neg_of_neg_of_pos (sub_neg.mpr ha) (by linarith))

private lemma k_image {α : ℝ} (hα : 0 < α) (hne : α ≠ 1) :
    k α '' Icc 0 (1 / 2) = I α := by
  rcases lt_or_gt_of_ne hne with ha | ha
  · have hd : 1 ≤ delta α := by
      have hd := (k_strictMonoOn hα ha).monotoneOn (by norm_num : (0 : ℝ) ∈ Icc 0 (1 / 2))
          (by norm_num : (1 / 2 : ℝ) ∈ Icc 0 (1 / 2)) (by norm_num)
      rw [k_zero hα, k_half hα] at hd
      exact hd
    rw [(k_continuousOn hα).image_Icc_of_monotoneOn (by norm_num)
      (k_strictMonoOn hα ha).monotoneOn, k_zero hα, k_half hα]
    simp [I, min_eq_left hd, max_eq_right hd]
  · have hd : delta α ≤ 1 := by
      have hd := (k_strictAntiOn ha).antitoneOn (by norm_num : (0 : ℝ) ∈ Icc 0 (1 / 2))
          (by norm_num : (1 / 2 : ℝ) ∈ Icc 0 (1 / 2)) (by norm_num)
      rw [k_zero hα, k_half hα] at hd
      exact hd
    rw [(k_continuousOn hα).image_Icc_of_antitoneOn (by norm_num)
      (k_strictAntiOn ha).antitoneOn, k_zero hα, k_half hα]
    simp [I, min_eq_right hd, max_eq_left hd]

private lemma kInv_spec {α x : ℝ} (hα : 0 < α) (hne : α ≠ 1) (hx : x ∈ I α) :
    kInv α x ∈ Icc 0 (1 / 2) ∧ k α (kInv α x) = x := by
  have hi : x ∈ k α '' Icc 0 (1 / 2) := by rw [k_image hα hne]; exact hx
  exact ⟨Function.invFunOn_mem hi, Function.invFunOn_eq hi⟩

/-- The inverse is the existing Cachin inverse after a scalar logarithmic change of coordinate. -/
private lemma kInv_eq {α x : ℝ} (hα : 0 < α) (hne : α ≠ 1) (hx : x ∈ I α) :
    kInv α x = HircheCachinCombiningConcavity.hInv α (Real.log x / c α) := by
  obtain ⟨hp, he⟩ := kInv_spec hα hne hx
  have hc : c α ≠ 0 := div_ne_zero (sub_ne_zero.mpr (Ne.symm hne)) hα.ne'
  have he' : Real.log x / c α = C α (kInv α x) := by
    conv_lhs => rw [← he, k_eq_exp hne hp, Real.log_exp]
    exact mul_div_cancel_left₀ _ hc
  rw [he', HircheCachinCombiningConcavity.hInv_h hα hp]

private lemma log_coordinate {α x : ℝ} (hα : 0 < α) (hne : α ≠ 1) (hx : x ∈ I α) :
    Real.log x / c α ∈ Icc 0 (Real.log 2) := by
  obtain ⟨hp, he⟩ := kInv_spec hα hne hx
  have hc : c α ≠ 0 := div_ne_zero (sub_ne_zero.mpr (Ne.symm hne)) hα.ne'
  have he' : Real.log x / c α = C α (kInv α x) := by
    conv_lhs => rw [← he, k_eq_exp hne hp, Real.log_exp]
    exact mul_div_cancel_left₀ _ hc
  rw [he', ← HircheCachinCombiningConcavity.h_image hα]
  exact mem_image_of_mem _ hp

private lemma kInv_continuousOn {α : ℝ} (hα : 0 < α) (hne : α ≠ 1) :
    ContinuousOn (kInv α) (I α) := by
  have hxpos : ∀ x ∈ I α, 0 < x := by
    intro x hx
    obtain ⟨hp, he⟩ := kInv_spec hα hne hx
    rw [← he]
    exact k_pos hp
  have hc : ContinuousOn (fun x => Real.log x / c α) (I α) :=
    (continuousOn_id.log (fun x hx => (hxpos x hx).ne')).div_const _
  exact ((HircheCachinCombiningConcavity.hInv_continuousOn hα).comp hc
    (fun x hx => log_coordinate hα hne hx)).congr
      (fun x hx => kInv_eq hα hne hx)

private lemma psi_continuousOn {α : ℝ} (hα : 0 < α) :
    ContinuousOn (psi α) (Icc 0 1) :=
  (k_continuousOn hα).comp ((continuousOn_const.sub continuousOn_id).div_const 2)
    (fun t ht => ⟨by linarith [ht.2], by linarith [ht.1]⟩)

private lemma psi_hasDerivAt {α t : ℝ} (hα : 0 < α) (hne : α ≠ 1)
    (ht : t ∈ Ioo 0 1) : HasDerivAt (psi α) (slope α t) t := by
  have hd := ((HircheCachinCombiningConcavity.psi_hasDerivAt hα ht).const_mul (c α)).exp
  have he : psi α =ᶠ[𝓝 t]
      (fun z => Real.exp (c α * HircheCachinCombiningConcavity.psi α z)) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with z hz
    exact k_eq_exp hne ⟨by linarith [hz.2], by linarith [hz.1]⟩
  convert hd.congr_of_eventuallyEq he using 1
  dsimp [slope]
  rw [he.eq_of_nhds]
  ring

private lemma slope_ne {α t : ℝ} (hα : 0 < α) (hne : α ≠ 1)
    (ht : t ∈ Ioo 0 1) : slope α t ≠ 0 := by
  apply mul_ne_zero
  · exact mul_ne_zero (neg_ne_zero.mpr
      (div_ne_zero (sub_ne_zero.mpr (Ne.symm hne)) hα.ne'))
      (k_pos ⟨by linarith [ht.2], by linarith [ht.1]⟩).ne'
  · exact (HircheCachinCombiningConcavity.slope_pos hα ht).ne'

private def E (α t : ℝ) : ℝ :=
  CachinElasticityMonotone.F (α - 1) (HircheCachinCombiningConcavity.ratio t) -
    c α * t * HircheCachinCombiningConcavity.slope α t

private lemma slope_hasDerivAt {α t : ℝ} (hα : 0 < α) (hne : α ≠ 1)
    (ht : t ∈ Ioo 0 1) :
    HasDerivAt (slope α) (slope α t * E α t / t) t := by
  have hd := (((psi_hasDerivAt hα hne ht).const_mul (-c α)).mul
    (HircheCachinCombiningConcavity.slope_hasDerivAt hα hne ht))
  convert hd using 1
  · rfl
  · dsimp [slope, E]
    field_simp [ht.1.ne']
    <;> ring

private lemma E_eq {α t : ℝ} (hα : 0 < α) (hne : α ≠ 1) (ht : t ∈ Ioo 0 1) :
    E α t = CachinElasticityMonotone.A (α - 1) (HircheCachinCombiningConcavity.ratio t) /
      (1 + t * CachinElasticityMonotone.T (α - 1) (HircheCachinCombiningConcavity.ratio t)) := by
  have hr := HircheCachinCombiningConcavity.ratio_mem ht
  have he : (1 - HircheCachinCombiningConcavity.ratio t) /
      (1 + HircheCachinCombiningConcavity.ratio t) = t := by
    apply (div_eq_iff (show 1 + HircheCachinCombiningConcavity.ratio t ≠ 0 by linarith [hr.1])).mpr
    unfold HircheCachinCombiningConcavity.ratio
    field_simp [show 1 + t ≠ 0 by linarith [ht.1]]
    <;> ring
  have hn : α - 1 ≠ 0 := sub_ne_zero.mpr hne
  unfold E CachinElasticityMonotone.F CachinElasticityMonotone.B
  rw [he, HircheCachinCombiningConcavity.slope_eq hne ht]
  dsimp [c]
  field_simp [hα.ne', hn]
  <;> ring

private lemma tanh_hasDerivAt (s : ℝ) :
    HasDerivAt Real.tanh (1 / Real.cosh s ^ 2) s := by
  exact (D5.S3.Weil.Budget.LinearCayleyScaleFlow.real_tanh_hasDerivAt s).congr_deriv (by
    rw [Real.tanh_eq_sinh_div_cosh]
    field_simp [(Real.cosh_pos s).ne']
    nlinarith [Real.cosh_sq_sub_sinh_sq s])

lemma ratio_tanh (s : ℝ) :
    HircheCachinCombiningConcavity.ratio (Real.tanh s) = Real.exp (-2 * s) := by
  rw [HircheCachinCombiningConcavity.ratio, Real.tanh_eq, Real.exp_neg,
    show -2 * s = -(s + s) by ring, Real.exp_neg, Real.exp_add]
  field_simp [(Real.exp_pos s).ne', (Real.exp_pos s).ne']
  <;> ring

private lemma T_tanh (b s : ℝ) :
    CachinElasticityMonotone.T b (HircheCachinCombiningConcavity.ratio (Real.tanh s)) =
      Real.tanh (b * s) := by
  rw [CachinElasticityMonotone.T, ratio_tanh, ← Real.exp_mul,
    show (-2 * s) * b = -(b * s) - b * s by ring, Real.exp_sub, Real.tanh_eq]
  field_simp [(Real.exp_pos (b * s)).ne',
    (add_pos (Real.exp_pos (b * s)) (Real.exp_pos (-(b * s)))).ne']
  <;> ring

lemma tanh_mem {s : ℝ} (hs : 0 < s) : Real.tanh s ∈ Ioo (0 : ℝ) 1 := by
  exact ⟨by rw [Real.tanh_eq_sinh_div_cosh]
            exact div_pos (Real.sinh_pos_iff.mpr hs) (Real.cosh_pos s), Real.tanh_lt_one s⟩

private lemma E_tanh {α s : ℝ} (hα : 0 < α) (hne : α ≠ 1) (hs : 0 < s) :
    E α (Real.tanh s) = ArimotoHyperbolic.elasticity (α - 1) s := by
  have ht := tanh_mem hs
  have hn : α - 1 ≠ 0 := sub_ne_zero.mpr hne
  have hd := (HircheCachinCombiningConcavity.T_comp_hasDerivAt hn ht).comp s
    (tanh_hasDerivAt s)
  have hd' := ((tanh_hasDerivAt ((α - 1) * s)).comp s
    ((hasDerivAt_id s).const_mul (α - 1))).congr_of_eventuallyEq
      (Filter.Eventually.of_forall (fun z => T_tanh (α - 1) z))
  have he := hd.unique hd'
  rw [T_tanh] at he
  have hsn : Real.sinh ((α - 1) * s) ≠ 0 :=
    Real.sinh_ne_zero.mpr (mul_ne_zero hn hs.ne')
  have htn : Real.tanh ((α - 1) * s) ≠ 0 := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_ne_zero hsn (Real.cosh_pos _).ne'
  have hA : CachinElasticityMonotone.A (α - 1)
      (HircheCachinCombiningConcavity.ratio (Real.tanh s)) =
      (α - 1) * Real.tanh s * Real.cosh s ^ 2 /
        (Real.cosh ((α - 1) * s) ^ 2 * Real.tanh ((α - 1) * s)) := by
    apply (eq_div_iff (mul_ne_zero (pow_ne_zero _ (Real.cosh_pos _).ne') htn)).mpr
    field_simp [ht.1.ne', (Real.cosh_pos s).ne',
      (Real.cosh_pos ((α - 1) * s)).ne'] at he
    nlinarith [he]
  rw [E_eq hα hne ht, hA, T_tanh]
  have hadd : Real.cosh (α * s) =
      Real.cosh ((α - 1) * s) * Real.cosh s +
        Real.sinh ((α - 1) * s) * Real.sinh s := by
    rw [← Real.cosh_add]
    congr 1
    ring
  unfold ArimotoHyperbolic.elasticity
  rw [show (α - 1 + 1) * s = α * s by ring]
  simp only [Real.tanh_eq_sinh_div_cosh]
  have hadd' : Real.cosh s * Real.cosh ((α - 1) * s) +
      Real.sinh s * Real.sinh ((α - 1) * s) = Real.cosh (α * s) := by
    nlinarith [hadd]
  have hsum : Real.cosh s * Real.cosh ((α - 1) * s) +
      Real.sinh s * Real.sinh ((α - 1) * s) ≠ 0 := by
    rw [hadd']
    exact (Real.cosh_pos _).ne'
  field_simp [hsn, (Real.cosh_pos s).ne', (Real.cosh_pos ((α - 1) * s)).ne',
    (Real.cosh_pos (α * s)).ne', hsum]
  <;> nlinarith [hadd]

private lemma E_monotoneOn {α : ℝ}
    (ha : (0 < α ∧ α < 1) ∨ (1 < α ∧ α ≤ 3 / 2)) :
    MonotoneOn (E α) (Ioo 0 1) := by
  have hα : 0 < α := by rcases ha with ha | ha <;> linarith [ha.1]
  have hn : α ≠ 1 := by rcases ha with ha | ha <;> linarith [ha.1, ha.2]
  have hb : (-1 < α - 1 ∧ α - 1 < 0) ∨ (0 < α - 1 ∧ α - 1 ≤ 1 / 2) := by
    rcases ha with ha | ha
    · left; constructor <;> linarith [ha.1, ha.2]
    · right; constructor <;> linarith [ha.1, ha.2]
  intro t ht u hu htu
  have ht' : t ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [ht.1], ht.2⟩
  have hu' : u ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hu.1], hu.2⟩
  rw [← Real.tanh_artanh ht', E_tanh hα hn (Real.artanh_pos ht),
    ← Real.tanh_artanh hu', E_tanh hα hn (Real.artanh_pos hu)]
  exact (ArimotoHyperbolic.strictMonoOn_elasticity hb).monotoneOn
    (Real.artanh_pos ht) (Real.artanh_pos hu)
    (by
      rcases htu.eq_or_lt with h | h
      · rw [h]
      · exact ((Real.artanh_lt_artanh_iff ht' hu').mpr h).le)

private lemma inverseBias_spec {α x : ℝ} (hα : 0 < α) (hne : α ≠ 1) (hx : x ∈ I α) :
    inverseBias α x ∈ Icc 0 1 ∧ psi α (inverseBias α x) = x := by
  obtain ⟨hp, he⟩ := kInv_spec hα hne hx
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · dsimp [inverseBias]; linarith [hp.2]
  · dsimp [inverseBias]; linarith [hp.1]
  · simpa [psi, inverseBias, show (1 - (1 - 2 * kInv α x)) / 2 = kInv α x by ring] using he

private lemma inverseBias_interior {α x : ℝ} (hα : 0 < α) (hne : α ≠ 1)
    (hx : x ∈ interior (I α)) : inverseBias α x ∈ Ioo (0 : ℝ) 1 := by
  obtain ⟨ht, he⟩ := inverseBias_spec hα hne (interior_subset hx)
  rw [I, interior_Icc] at hx
  have hδ : x ≠ delta α := by
    intro heq
    rw [heq] at hx
    rcases le_total 1 (delta α) with h | h
    · simpa [max_eq_right h] using hx.2
    · simpa [min_eq_right h] using hx.1
  have h1 : x ≠ 1 := by
    intro heq
    rw [heq] at hx
    rcases le_total 1 (delta α) with h | h
    · simpa [min_eq_left h] using hx.1
    · simpa [max_eq_left h] using hx.2
  constructor
  · by_contra hn
    have ht0 : inverseBias α x = 0 := le_antisymm (not_lt.mp hn) ht.1
    rw [ht0] at he
    exact hδ (he.symm.trans (by simpa [psi] using k_half hα))
  · by_contra hn
    have ht1 : inverseBias α x = 1 := le_antisymm ht.2 (not_lt.mp hn)
    rw [ht1] at he
    exact h1 (he.symm.trans (by simpa [psi] using k_zero hα))

private lemma inverseBias_continuousOn {α : ℝ} (hα : 0 < α) (hne : α ≠ 1) :
    ContinuousOn (inverseBias α) (I α) :=
  continuousOn_const.sub (continuousOn_const.mul (kInv_continuousOn hα hne))

private lemma inverseBias_hasDerivAt {α x : ℝ} (hα : 0 < α) (hne : α ≠ 1)
    (hx : x ∈ interior (I α)) :
    HasDerivAt (inverseBias α) (slope α (inverseBias α x))⁻¹ x := by
  have hx' := hx
  rw [I, interior_Icc] at hx'
  apply HasDerivAt.of_local_left_inverse
    ((inverseBias_continuousOn hα hne x (interior_subset hx)).continuousAt
      (Icc_mem_nhds hx'.1 hx'.2))
    (psi_hasDerivAt hα hne (inverseBias_interior hα hne hx))
    (slope_ne hα hne (inverseBias_interior hα hne hx))
  filter_upwards [Icc_mem_nhds hx'.1 hx'.2] with z hz
  exact (inverseBias_spec hα hne hz).2

private lemma mul_mem {v t : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    v * t ∈ Ioo (0 : ℝ) 1 :=
  ⟨mul_pos hv.1 ht.1, by nlinarith [ht.2, mul_pos (sub_pos.mpr hv.2) ht.1]⟩

private lemma slope_positive {α t : ℝ} (ha : 1 < α) (ht : t ∈ Ioo (0 : ℝ) 1) :
    0 < slope α t := by
  dsimp [slope, c]
  exact mul_pos (mul_pos (neg_pos.mpr (div_neg_of_neg_of_pos (by linarith) (by linarith)))
    (k_pos ⟨by linarith [ht.2], by linarith [ht.1]⟩))
    (HircheCachinCombiningConcavity.slope_pos (by linarith) ht)

private lemma slope_negative {α t : ℝ} (hα : 0 < α) (ha : α < 1)
    (ht : t ∈ Ioo (0 : ℝ) 1) : slope α t < 0 := by
  dsimp [slope, c]
  exact mul_neg_of_neg_of_pos
    (mul_neg_of_neg_of_pos (neg_neg_of_pos (div_pos (by linarith) hα))
      (k_pos ⟨by linarith [ht.2], by linarith [ht.1]⟩))
    (HircheCachinCombiningConcavity.slope_pos hα ht)

private lemma ratio_antitone {α v : ℝ}
    (ha : (0 < α ∧ α < 1) ∨ (1 < α ∧ α ≤ 3 / 2)) (hv : v ∈ Ioo (0 : ℝ) 1) :
    AntitoneOn (fun t => v * slope α (v * t) / slope α t) (Ioo 0 1) := by
  have hα : 0 < α := by rcases ha with ha | ha <;> linarith [ha.1]
  have hn : α ≠ 1 := by rcases ha with ha | ha <;> linarith [ha.1, ha.2]
  have hd (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
      HasDerivAt (fun t => v * slope α (v * t) / slope α t)
        (v * slope α (v * t) / (t * slope α t) * (E α (v * t) - E α t)) t := by
    convert (((slope_hasDerivAt hα hn (mul_mem hv ht)).comp t
      ((hasDerivAt_id t).const_mul v)).const_mul v).div
      (slope_hasDerivAt hα hn ht) (slope_ne hα hn ht) using 1
    · rfl
    · dsimp
      field_simp [ht.1.ne', hv.1.ne', slope_ne hα hn ht]
      <;> ring
  apply antitoneOn_of_deriv_nonpos (convex_Ioo _ _)
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt)
  intro t ht
  have ht' : t ∈ Ioo (0 : ℝ) 1 := interior_subset ht
  rw [(hd t ht').deriv]
  apply mul_nonpos_of_nonneg_of_nonpos
  · rcases ha with ha | ha
    · exact (div_pos_of_neg_of_neg (mul_neg_of_pos_of_neg hv.1
        (slope_negative ha.1 ha.2 (mul_mem hv ht')))
        (mul_neg_of_pos_of_neg ht'.1 (slope_negative ha.1 ha.2 ht'))).le
    · exact (div_pos (mul_pos hv.1 (slope_positive ha.1 (mul_mem hv ht')))
        (mul_pos ht'.1 (slope_positive ha.1 ht'))).le
  · exact sub_nonpos.mpr (E_monotoneOn ha (mul_mem hv ht') ht' (by nlinarith [hv.2, ht'.1]))

private lemma bias_combining (α x y : ℝ) :
    G α x y = psi α (inverseBias α y * inverseBias α x) := by
  unfold G psi inverseBias
  congr 1
  have hb := BinaryRenyiCombining.bconv_bias (kInv α x) (kInv α y)
  nlinarith [hb]

private lemma transported_continuousOn {α v : ℝ} (hα : 0 < α) (hne : α ≠ 1)
    (hv : v ∈ Icc (0 : ℝ) 1) :
    ContinuousOn (fun x => psi α (v * inverseBias α x)) (I α) := by
  apply (psi_continuousOn hα).comp
    (continuousOn_const.mul (inverseBias_continuousOn hα hne))
  intro x hx
  have ht := (inverseBias_spec hα hne hx).1
  exact ⟨mul_nonneg hv.1 ht.1, by
    change v * inverseBias α x ≤ 1
    nlinarith [ht.2, mul_nonneg (sub_nonneg.mpr hv.2) ht.1]⟩

private lemma transported_hasDerivAt {α v x : ℝ} (hα : 0 < α) (hne : α ≠ 1)
    (hv : v ∈ Ioo (0 : ℝ) 1) (hx : x ∈ interior (I α)) :
    HasDerivAt (fun z => psi α (v * inverseBias α z))
      (v * slope α (v * inverseBias α x) / slope α (inverseBias α x)) x := by
  convert (psi_hasDerivAt hα hne (mul_mem hv (inverseBias_interior hα hne hx))).comp x
    ((inverseBias_hasDerivAt hα hne hx).const_mul v) using 1
  · rfl
  · ring

private lemma inverseBias_order {α : ℝ} (hα : 0 < α) (hne : α ≠ 1) :
    (α < 1 → AntitoneOn (inverseBias α) (I α)) ∧
    (1 < α → MonotoneOn (inverseBias α) (I α)) := by
  have hs (x : ℝ) (hx : x ∈ I α) := inverseBias_spec hα hne hx
  constructor
  · intro ha x hx y hy hxy
    by_contra hbad
    have ht := (hs x hx).1
    have hu := (hs y hy).1
    have hp := k_strictMonoOn hα ha
      (show (1 - inverseBias α y) / 2 ∈ Icc 0 (1 / 2) from
        ⟨by linarith [hu.2], by linarith [hu.1]⟩)
      (show (1 - inverseBias α x) / 2 ∈ Icc 0 (1 / 2) from
        ⟨by linarith [ht.2], by linarith [ht.1]⟩) (by linarith [not_le.mp hbad])
    change psi α (inverseBias α y) < psi α (inverseBias α x) at hp
    rw [(hs x hx).2, (hs y hy).2] at hp
    exact (not_lt_of_ge hxy) hp
  · intro ha x hx y hy hxy
    by_contra hbad
    have ht := (hs x hx).1
    have hu := (hs y hy).1
    have hp := k_strictAntiOn ha
      (show (1 - inverseBias α x) / 2 ∈ Icc 0 (1 / 2) from
        ⟨by linarith [ht.2], by linarith [ht.1]⟩)
      (show (1 - inverseBias α y) / 2 ∈ Icc 0 (1 / 2) from
        ⟨by linarith [hu.2], by linarith [hu.1]⟩) (by linarith [not_le.mp hbad])
    change psi α (inverseBias α y) < psi α (inverseBias α x) at hp
    rw [(hs x hx).2, (hs y hy).2] at hp
    exact (not_lt_of_ge hxy) hp

private lemma transported_convexOn {α v : ℝ} (hα : 0 < α) (ha : α < 1)
    (hv : v ∈ Icc (0 : ℝ) 1) :
    ConvexOn ℝ (I α) (fun x => psi α (v * inverseBias α x)) := by
  have hn : α ≠ 1 := ne_of_lt ha
  by_cases hv0 : v = 0
  · subst v
    simpa only [zero_mul] using (show ConvexOn ℝ (I α) (fun _ : ℝ => psi α 0) from
      convexOn_const _ (convex_Icc _ _))
  by_cases hv1 : v = 1
  · subst v
    apply (convexOn_id (convex_Icc (min 1 (delta α)) (max 1 (delta α)))).congr
    intro x hx
    simpa using (inverseBias_spec hα hn hx).2.symm
  have hv' : v ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne hv.1 (Ne.symm hv0), lt_of_le_of_ne hv.2 hv1⟩
  apply MonotoneOn.convexOn_of_deriv (convex_Icc _ _) (transported_continuousOn hα hn hv)
  · intro x hx
    exact (transported_hasDerivAt hα hn hv' hx).differentiableAt.differentiableWithinAt
  · intro x hx y hy hxy
    rw [(transported_hasDerivAt hα hn hv' hx).deriv,
      (transported_hasDerivAt hα hn hv' hy).deriv]
    exact ratio_antitone (Or.inl ⟨hα, ha⟩) hv' (inverseBias_interior hα hn hy)
      (inverseBias_interior hα hn hx)
      ((inverseBias_order hα hn).1 ha (interior_subset hx) (interior_subset hy) hxy)

private lemma transported_concaveOn {α v : ℝ} (ha : 1 < α) (hb : α ≤ 3 / 2)
    (hv : v ∈ Icc (0 : ℝ) 1) :
    ConcaveOn ℝ (I α) (fun x => psi α (v * inverseBias α x)) := by
  have hα : 0 < α := by linarith
  have hn : α ≠ 1 := ne_of_gt ha
  by_cases hv0 : v = 0
  · subst v
    simpa only [zero_mul] using (show ConcaveOn ℝ (I α) (fun _ : ℝ => psi α 0) from
      concaveOn_const _ (convex_Icc _ _))
  by_cases hv1 : v = 1
  · subst v
    apply (concaveOn_id (convex_Icc (min 1 (delta α)) (max 1 (delta α)))).congr
    intro x hx
    simpa using (inverseBias_spec hα hn hx).2.symm
  have hv' : v ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne hv.1 (Ne.symm hv0), lt_of_le_of_ne hv.2 hv1⟩
  apply AntitoneOn.concaveOn_of_deriv (convex_Icc _ _) (transported_continuousOn hα hn hv)
  · intro x hx
    exact (transported_hasDerivAt hα hn hv' hx).differentiableAt.differentiableWithinAt
  · intro x hx y hy hxy
    rw [(transported_hasDerivAt hα hn hv' hx).deriv,
      (transported_hasDerivAt hα hn hv' hy).deriv]
    exact ratio_antitone (Or.inr ⟨ha, hb⟩) hv' (inverseBias_interior hα hn hx)
      (inverseBias_interior hα hn hy)
      ((inverseBias_order hα hn).2 ha (interior_subset hx) (interior_subset hy) hxy)

/-- Hirche's Conjecture IV.6, with witness three halves. -/
theorem result : claim := by
  refine ⟨3 / 2, by norm_num, by norm_num, ?_, ?_⟩
  · intro α hα ha y hy
    have hv := (inverseBias_spec hα (ne_of_lt ha) hy).1
    simpa only [bias_combining] using transported_convexOn hα ha hv
  · intro α ha hb y hy
    have hv := (inverseBias_spec (by linarith) (ne_of_gt ha) hy).1
    simpa only [bias_combining] using transported_concaveOn ha hb hv

end D5.S3.Entropy.RenyiCombining.HircheArimotoCombining
