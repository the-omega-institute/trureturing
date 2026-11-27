/- GID: D5/S3/Quantum/Information/RecordWriting/TwoRegisterInformation
   generality: G
   mirror-B: D5/B/S3/Quantum/Information/RecordWriting/TwoRegisterInformation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Sharp common marginal information at fixed bath variation for two binary registers. -/

import D5.S3.Quantum.Information.RecordWriting.TwoRegister
import D5.S3.DivergenceSupport.LogSumInequality
import D5.S3.TotalVariation.ProductSubadditive
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Logic.Equiv.Bool

/-! Wonyong Chung, *The thermodynamic budget of objectivity*, arXiv:2611.34909v1,
Section II, specifies the population information deficit. Section VIII after Eq. (7)
asks about collective gates. For two initially uniform binary registers and an equiprobable
event, this module gives the exact common marginal mutual-information threshold achievable
by finite protocols with arbitrary event-controlled joint permutations. The attaining
protocols use the same two local baths in both branches. Their weight-one resets, including
pure reset laws, are ideal operations of the finite model. Continuous entropy-production
and activity optimization requires a separate analytic argument. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Quantum.Information.RecordWriting.TwoRegisterInformation

open Set
open Real (binEntropy)
open TwoRegister
open D5.S3.Divergence.ClassicalDPI (klDivergence)
open D5.S3.DivergenceSupport.LogSumInequality (kl_divergence_joint_convex)

/-- Mutual information in nats for a binary readout of an equiprobable event,
with conditional probabilities `p` and `q` of the same outcome. -/
def J (p q : ℝ) : ℝ :=
  binEntropy ((p + q) / 2) - (binEntropy p + binEntropy q) / 2

private theorem J_comm (p q : ℝ) : J p q = J q p := by
  simp only [J, add_comm p q, add_comm (binEntropy p) (binEntropy q)]

private theorem J_reflect (p q : ℝ) : J (1 - p) (1 - q) = J p q := by
  have h : (1 - p + (1 - q)) / 2 = 1 - (p + q) / 2 := by ring
  simp only [J, h, Real.binEntropy_one_sub]

/-- The upper endpoint conditional probability for the extremal oriented readout. -/
def r (t : ℝ) : ℝ := min 1 (1 / 2 + t)

/-- The lower conditional probability for the extremal oriented readout. -/
def s (t : ℝ) : ℝ := r t - t

/-- The extremal information curve, parametrized by the mean absolute sign bias. -/
def g (t : ℝ) : ℝ := J (r t) (s t)

private def bernoulli (p : ℝ) (b : Bool) : ℝ := if b then 1 - p else p

private theorem bernoulli_nonneg {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) (b : Bool) :
    0 ≤ bernoulli p b := by
  cases b
  · exact hp.1
  · exact sub_nonneg.mpr hp.2

private theorem bernoulli_mix (a p q : ℝ) :
    bernoulli (a * p + (1 - a) * q) =
      fun b => a * bernoulli p b + (1 - a) * bernoulli q b := by
  funext b
  cases b
  · rfl
  · change 1 - (a * p + (1 - a) * q) = a * (1 - p) + (1 - a) * (1 - q)
    ring

private theorem bernoulli_mid (p q : ℝ) (b : Bool) :
    bernoulli ((p + q) / 2) b = (bernoulli p b + bernoulli q b) / 2 := by
  cases b
  · rfl
  · change 1 - (p + q) / 2 = ((1 - p) + (1 - q)) / 2
    ring

private theorem J_eq_mean_kl {p q : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) (hq : q ∈ Icc (0 : ℝ) 1) :
    J p q =
      (klDivergence (bernoulli p) (bernoulli ((p + q) / 2)) +
        klDivergence (bernoulli q) (bernoulli ((p + q) / 2))) / 2 := by
  have splitLog {x y : ℝ} (hx₀ : 0 ≤ x) (hy : 0 ≤ y) :
      x * Real.log (x / ((x + y) / 2)) =
        x * Real.log x - x * Real.log ((x + y) / 2) := by
    by_cases hx : x = 0
    · simp [hx]
    have hm : (x + y) / 2 ≠ 0 := by
      have := lt_of_le_of_ne hx₀ (Ne.symm hx)
      linarith
    rw [Real.log_div hx hm, mul_sub]
  unfold J klDivergence
  simp only [Fintype.sum_bool, bernoulli, Bool.false_eq_true, ↓reduceIte]
  rw [show 1 - (p + q) / 2 = ((1 - p) + (1 - q)) / 2 by ring]
  rw [splitLog hp.1 hq.1, splitLog (sub_nonneg.mpr hp.2) (sub_nonneg.mpr hq.2)]
  rw [add_comm p q, add_comm (1 - p) (1 - q)]
  rw [splitLog hq.1 hp.1, splitLog (sub_nonneg.mpr hq.2) (sub_nonneg.mpr hp.2)]
  simp only [binEntropy, Real.log_inv]
  rw [show ((1 - q) + (1 - p)) / 2 = 1 - (q + p) / 2 by ring]
  ring

private theorem J_mix_le {p₁ p₂ q₁ q₂ a : ℝ}
    (hp₁ : p₁ ∈ Icc (0 : ℝ) 1) (hp₂ : p₂ ∈ Icc (0 : ℝ) 1)
    (hq₁ : q₁ ∈ Icc (0 : ℝ) 1) (hq₂ : q₂ ∈ Icc (0 : ℝ) 1)
    (ha : a ∈ Icc (0 : ℝ) 1) :
    J (a * p₁ + (1 - a) * p₂) (a * q₁ + (1 - a) * q₂) ≤
      a * J p₁ q₁ + (1 - a) * J p₂ q₂ := by
  have mix_mem {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
      a * x + (1 - a) * y ∈ Icc (0 : ℝ) 1 := by
    have h := sub_nonneg.mpr ha.2
    exact ⟨add_nonneg (mul_nonneg ha.1 hx.1) (mul_nonneg h hy.1),
      by nlinarith [mul_nonneg ha.1 (sub_nonneg.mpr hx.2),
      mul_nonneg h (sub_nonneg.mpr hy.2)]⟩
  have mid_mem {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
      (x + y) / 2 ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hx.1, hy.1], by linarith [hx.2, hy.2]⟩
  have kl_mix {x₁ x₂ y₁ y₂ : ℝ}
      (hx₁ : x₁ ∈ Icc (0 : ℝ) 1) (hx₂ : x₂ ∈ Icc (0 : ℝ) 1)
      (hy₁ : y₁ ∈ Icc (0 : ℝ) 1) (hy₂ : y₂ ∈ Icc (0 : ℝ) 1) :
      klDivergence (bernoulli (a * x₁ + (1 - a) * x₂))
          (bernoulli (a * ((x₁ + y₁) / 2) + (1 - a) * ((x₂ + y₂) / 2))) ≤
        a * klDivergence (bernoulli x₁) (bernoulli ((x₁ + y₁) / 2)) +
          (1 - a) * klDivergence (bernoulli x₂) (bernoulli ((x₂ + y₂) / 2)) := by
    have support {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1)
        (b : Bool) (hb : bernoulli ((x + y) / 2) b = 0) : bernoulli x b = 0 := by
      rw [bernoulli_mid] at hb
      linarith [bernoulli_nonneg hx b, bernoulli_nonneg hy b]
    have h := kl_divergence_joint_convex (bernoulli x₁) (bernoulli x₂)
      (bernoulli ((x₁ + y₁) / 2)) (bernoulli ((x₂ + y₂) / 2)) a ha
      (bernoulli_nonneg hx₁) (bernoulli_nonneg hx₂)
      (bernoulli_nonneg (mid_mem hx₁ hy₁)) (bernoulli_nonneg (mid_mem hx₂ hy₂))
      (support hx₁ hy₁) (support hx₂ hy₂)
    simpa only [bernoulli_mix] using h
  rw [J_eq_mean_kl (mix_mem hp₁ hp₂) (mix_mem hq₁ hq₂), J_eq_mean_kl hp₁ hq₁,
    J_eq_mean_kl hp₂ hq₂]
  have h₁ := kl_mix hp₁ hp₂ hq₁ hq₂
  have h₂ := kl_mix hq₁ hq₂ hp₁ hp₂
  rw [add_comm q₁ p₁, add_comm q₂ p₂] at h₂
  rw [show (a * p₁ + (1 - a) * p₂ + (a * q₁ + (1 - a) * q₂)) / 2 =
    a * ((p₁ + q₁) / 2) + (1 - a) * ((p₂ + q₂) / 2) by ring]
  linarith

private def biasProb (u : ℝ) : ℝ := (1 + u) / 2

private theorem entropy_bias_neg (u : ℝ) :
    binEntropy (biasProb (-u)) = binEntropy (biasProb u) := by
  rw [show biasProb (-u) = 1 - biasProb u by unfold biasProb; ring, Real.binEntropy_one_sub]

private theorem entropy_bias_abs (u : ℝ) :
    binEntropy (biasProb |u|) = binEntropy (biasProb u) := by
  rcases le_total 0 u with hu | hu
  · rw [abs_of_nonneg hu]
  · rw [abs_of_nonpos hu, entropy_bias_neg]

private theorem orient_biases {u v : ℝ} (hu : |u| ≤ 1) (hv : |v| ≤ 1) :
    J (biasProb u) (biasProb v) ≤ J (biasProb |u|) (biasProb (-|v|)) := by
  have hm : abs (|u| - |v|) ≤ |u + v| := by
    simpa only [abs_neg, sub_neg_eq_add] using abs_abs_sub_abs_le_abs_sub u (-v)
  have hsum : |u + v| ≤ 2 := (abs_add_le u v).trans (by linarith)
  have havg (x y : ℝ) : (biasProb x + biasProb y) / 2 = biasProb ((x + y) / 2) := by
    unfold biasProb
    ring
  unfold J
  rw [havg, havg, entropy_bias_abs, entropy_bias_neg, entropy_bias_abs]
  apply sub_le_sub_right
  rw [← entropy_bias_abs ((u + v) / 2), ← entropy_bias_abs ((|u| + -|v|) / 2)]
  simp only [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2), ← sub_eq_add_neg]
  exact Real.binEntropy_strictAntiOn.antitoneOn
    ⟨by unfold biasProb; linarith [abs_nonneg (|u| - |v|)], by unfold biasProb; linarith⟩
    ⟨by unfold biasProb; linarith [abs_nonneg (u + v)], by unfold biasProb; linarith⟩
    (by unfold biasProb; linarith)

private theorem center_convex {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ConvexOn ℝ (Icc (-min t (1 - t)) (min t (1 - t)))
      (fun z => J (biasProb (z + t)) (biasProb (z - t))) := by
  have probs {z : ℝ} (hz : z ∈ Icc (-min t (1 - t)) (min t (1 - t))) :
      biasProb (z + t) ∈ Icc (0 : ℝ) 1 ∧ biasProb (z - t) ∈ Icc (0 : ℝ) 1 := by
    have lo := hz.1
    have hi := hz.2
    have hm := min_le_right t (1 - t)
    unfold biasProb
    exact ⟨⟨by linarith [ht.1], by linarith⟩, ⟨by linarith, by linarith [ht.1]⟩⟩
  refine ⟨convex_Icc _ _, ?_⟩
  intro x hx y hy a b ha hb hab
  have hb' : b = 1 - a := by linarith
  have a_mem : a ∈ Icc (0 : ℝ) 1 := ⟨ha, by linarith⟩
  simp only [smul_eq_mul, hb']
  rw [show biasProb (a * x + (1 - a) * y + t) =
    a * biasProb (x + t) + (1 - a) * biasProb (y + t) by unfold biasProb; ring]
  rw [show biasProb (a * x + (1 - a) * y - t) =
    a * biasProb (x - t) + (1 - a) * biasProb (y - t) by unfold biasProb; ring]
  exact J_mix_le (probs hx).1 (probs hy).1 (probs hx).2 (probs hy).2 a_mem

private theorem center_reflect (t z : ℝ) :
    J (biasProb (-z + t)) (biasProb (-z - t)) =
      J (biasProb (z + t)) (biasProb (z - t)) := by
  rw [show biasProb (-z + t) = 1 - biasProb (z - t) by unfold biasProb; ring,
    show biasProb (-z - t) = 1 - biasProb (z + t) by unfold biasProb; ring,
    J_reflect, J_comm]

private theorem r_eq_extreme (t : ℝ) : r t = biasProb (min t (1 - t) + t) := by
  rcases le_total t (1 - t) with h | h
  · rw [r, min_eq_left h, min_eq_right (by linarith : (1 : ℝ) / 2 + t ≤ 1)]
    unfold biasProb
    ring
  · rw [r, min_eq_right h, min_eq_left (by linarith : (1 : ℝ) ≤ 1 / 2 + t)]
    unfold biasProb
    ring

private theorem s_eq_extreme (t : ℝ) : s t = biasProb (min t (1 - t) - t) := by
  rw [s, r_eq_extreme]
  unfold biasProb
  ring

/-- For prescribed mean absolute sign bias, the information is maximized at
the oriented endpoint where one conditional probability reaches `1/2` or `1`. -/
theorem J_le_g_of_bias (u v : ℝ) (hu : |u| ≤ 1) (hv : |v| ≤ 1) :
    J ((1 + u) / 2) ((1 + v) / 2) ≤ g ((|u| + |v|) / 2) := by
  let t := (|u| + |v|) / 2
  let z := (|u| - |v|) / 2
  let m := min t (1 - t)
  have ht : t ∈ Icc (0 : ℝ) 1 := ⟨by dsimp [t]; positivity, by dsimp [t]; linarith⟩
  have hm : 0 ≤ m := le_min ht.1 (sub_nonneg.mpr ht.2)
  have hz : z ∈ Icc (-m) m := by
    have h : |z| ≤ m := by
      unfold m
      exact le_min
        (abs_le.mpr ⟨by dsimp [t, z]; linarith [abs_nonneg u],
          by dsimp [t, z]; linarith [abs_nonneg v]⟩)
        (abs_le.mpr ⟨by dsimp [t, z]; linarith, by dsimp [t, z]; linarith⟩)
    exact abs_le.mp h
  refine (orient_biases hu hv).trans ?_
  have h := (center_convex ht).le_max_of_mem_Icc
    (show -m ∈ Icc (-m) m from ⟨le_rfl, by linarith⟩)
    (show m ∈ Icc (-m) m from ⟨by linarith, le_rfl⟩) hz
  change J (biasProb (z + t)) (biasProb (z - t)) ≤
    max (J (biasProb (-m + t)) (biasProb (-m - t)))
      (J (biasProb (m + t)) (biasProb (m - t))) at h
  rw [center_reflect, max_self, ← r_eq_extreme, ← s_eq_extreme] at h
  rwa [show z + t = |u| by dsimp [z, t]; ring,
    show z - t = -|v| by dsimp [z, t]; ring] at h

private theorem J_strictMono_left {q : ℝ} (hq : 0 ≤ q) :
    StrictMonoOn (fun p => J p q) (Icc q 1) := by
  have entropyAnti : StrictAntiOn (deriv binEntropy) (Ioo (0 : ℝ) 1) := by
    have h := Real.strictConcave_binEntropy.subset Ioo_subset_Icc_self (convex_Ioo 0 1)
    refine h.strictAntiOn_deriv ?_
    intro x hx
    exact Real.differentiableAt_binEntropy hx.1.ne' hx.2.ne
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) (by unfold J; fun_prop)
  intro p hp
  rw [interior_Icc] at hp
  have hp' : p ∈ Ioo (0 : ℝ) 1 := ⟨hq.trans_lt hp.1, hp.2⟩
  have hm : (p + q) / 2 ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hp'.1], by linarith [hp.1, hp.2]⟩
  have h := entropyAnti hm hp' (by linarith [hp.1] : (p + q) / 2 < p)
  rw [Real.deriv_binEntropy, Real.deriv_binEntropy] at h
  have ha : HasDerivAt (fun x : ℝ => (x + q) / 2) (1 / 2) p :=
    ((hasDerivAt_id p).add_const q).div_const 2
  have hd := ((Real.hasDerivAt_binEntropy hm.1.ne' hm.2.ne).comp p ha).sub
      (((Real.hasDerivAt_binEntropy hp'.1.ne' hp'.2.ne).add_const (binEntropy q)).div_const 2)
  unfold J
  rw [show deriv (fun x => binEntropy ((x + q) / 2) - (binEntropy x + binEntropy q) / 2) p =
    _ from hd.deriv]
  linarith

private theorem g_left {t : ℝ} (ht : t ≤ 1 / 2) : g t = J (1 / 2 + t) (1 / 2) := by
  unfold g s r
  rw [min_eq_right (by linarith : (1 : ℝ) / 2 + t ≤ 1)]
  congr 1
  ring

private theorem g_right {t : ℝ} (ht : 1 / 2 ≤ t) : g t = J t 0 := by
  unfold g s r
  rw [min_eq_left (by linarith : (1 : ℝ) ≤ 1 / 2 + t), ← J_reflect, sub_self]
  rw [show 1 - (1 - t) = t by ring, J_comm]

/-- The maximum information increases strictly over the full closed interval. -/
theorem strictMonoOn_g : StrictMonoOn g (Icc (0 : ℝ) 1) := by
  have left : StrictMonoOn g (Icc (0 : ℝ) (1 / 2)) := by
    intro a ha b hb hab
    rw [g_left ha.2, g_left hb.2]
    exact J_strictMono_left (by norm_num : (0 : ℝ) ≤ 1 / 2)
      ⟨by linarith [ha.1], by linarith [ha.2]⟩
      ⟨by linarith [hb.1], by linarith [hb.2]⟩ (by linarith)
  have right : StrictMonoOn g (Icc (1 / 2 : ℝ) 1) := by
    intro a ha b hb hab
    rw [g_right ha.1, g_right hb.1]
    exact J_strictMono_left le_rfl ⟨by linarith [ha.1], ha.2⟩
      ⟨by linarith [hb.1], hb.2⟩ hab
  intro a ha b hb hab
  by_cases hb' : b ≤ 1 / 2
  · exact left ⟨ha.1, hab.le.trans hb'⟩ ⟨hb.1, hb'⟩ hab
  by_cases ha' : 1 / 2 ≤ a
  · exact right ⟨ha', ha.2⟩ ⟨ha'.trans hab.le, hb.2⟩ hab
  exact (left ⟨ha.1, le_of_not_ge ha'⟩ ⟨by norm_num, le_rfl⟩ (lt_of_not_ge ha')).trans
    (right ⟨le_rfl, by norm_num⟩ ⟨le_of_not_ge hb', hb.2⟩ (lt_of_not_ge hb'))

/-- Each binary information threshold determines exactly one variation budget. -/
theorem existsUnique_budget {k : ℝ} (hk : k ∈ Icc (0 : ℝ) (Real.log 2)) :
    ∃! t : ℝ, t ∈ Icc (0 : ℝ) 1 ∧ g t = k := by
  have hg : Continuous g := by
    unfold g s r J
    fun_prop
  have h₀ : g 0 = 0 := by norm_num [g, r, s, J]
  have h₁ : g 1 = Real.log 2 := by
    norm_num [g, r, s, J]
    simpa only [one_div] using Real.binEntropy_two_inv
  have hk' : k ∈ Icc (g 0) (g 1) := by simpa [h₀, h₁] using hk
  obtain ⟨t, ht, hgt⟩ := intermediate_value_Icc
    (by norm_num : (0 : ℝ) ≤ 1) hg.continuousOn hk'
  exact ⟨t, ⟨ht, hgt⟩, fun u hu => strictMonoOn_g.injOn hu.1 ht (hu.2.trans hgt.symm)⟩

private theorem extreme_biases {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    min 1 (2 * t) ∈ Icc (0 : ℝ) 1 ∧ 2 * t - min 1 (2 * t) ∈ Icc (0 : ℝ) 1 := by
  have h₀ := ht.1
  have h₁ := ht.2
  rcases le_total (2 * t) 1 with h | h
  · rw [min_eq_right h]
    exact ⟨⟨by linarith, h⟩, ⟨by linarith, by linarith⟩⟩
  · rw [min_eq_left h]
    exact ⟨⟨zero_le_one, le_rfl⟩, ⟨by linarith, by linarith⟩⟩

/-- The extreme pair attains the information envelope. -/
private theorem J_eq_g_at_extreme (t : ℝ) :
    let x := min 1 (2 * t)
    let y := 2 * t - x
    J ((1 + x) / 2) ((1 - y) / 2) = g t := by
  dsimp
  rcases le_total (2 * t) 1 with h | h
  · rw [min_eq_right h, g_left (by linarith)]
    congr 1 <;> ring
  · rw [min_eq_left h]
    have hr : r t = 1 := min_eq_left (by linarith : (1 : ℝ) ≤ 1 / 2 + t)
    rw [g, s, hr]
    congr 1 <;> ring

/-- The first register's readout information from the actual conditional laws. -/
def firstInformation (p q : Law Point) : ℝ :=
  J (marginalFirst p.mass false) (marginalFirst q.mass false)

/-- The second register's readout information from the actual conditional laws. -/
def secondInformation (p q : Law Point) : ℝ :=
  J (marginalSecond p.mass false) (marginalSecond q.mass false)

private theorem marginal_biases (p : Law Point) :
    (|momentA p.mass| ≤ 1 ∧ marginalFirst p.mass false = biasProb (momentA p.mass)) ∧
    (|momentB p.mass| ≤ 1 ∧ marginalSecond p.mass false = biasProb (momentB p.mass)) := by
  have h := p.normalized
  simp only [Fintype.sum_prod_type, Fintype.sum_bool] at h
  have hff := p.nonneg (false, false)
  have hft := p.nonneg (false, true)
  have htf := p.nonneg (true, false)
  have htt := p.nonneg (true, true)
  refine ⟨⟨abs_le.mpr ⟨?_, ?_⟩, ?_⟩, ⟨abs_le.mpr ⟨?_, ?_⟩, ?_⟩⟩ <;>
    (simp only [momentA, momentB, biasProb, marginalFirst, marginalSecond]; linarith)

private theorem run_bias_bound (protocol : List Step) :
    |momentA (run protocol uniform).mass| + |momentB (run protocol uniform).mass| ≤
      2 * bathVariation protocol uniform := by
  have h := run_potential_le protocol uniform
  have h₀ : potential uniform.mass = 0 := by
    norm_num [potential, momentA, momentB, momentC, uniform]
  rw [h₀, zero_add] at h
  exact (le_max_left _ _).trans h

private theorem bias_ge_of_information {t u v : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hu : |u| ≤ 1) (hv : |v| ≤ 1) (h : g t ≤ J (biasProb u) (biasProb v)) :
    t ≤ (|u| + |v|) / 2 := by
  have hmem : (|u| + |v|) / 2 ∈ Icc (0 : ℝ) 1 :=
    ⟨by positivity, by linarith⟩
  by_contra! hlt
  exact ((strictMonoOn_g hmem ht hlt).not_ge) (h.trans (J_le_g_of_bias u v hu hv))

/-- If both output registers carry at least `g t` nats, the mean bath endpoint variation
of the two uniform event branches is at least `t`. -/
theorem recording_information_bound {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (protocol0 protocol1 : List Step)
    (h₁ : g t ≤ firstInformation (run protocol0 uniform) (run protocol1 uniform))
    (h₂ : g t ≤ secondInformation (run protocol0 uniform) (run protocol1 uniform)) :
    t ≤ (bathVariation protocol0 uniform + bathVariation protocol1 uniform) / 2 := by
  obtain ⟨⟨ha₀, hfa₀⟩, ⟨hb₀, hfb₀⟩⟩ := marginal_biases (run protocol0 uniform)
  obtain ⟨⟨ha₁, hfa₁⟩, ⟨hb₁, hfb₁⟩⟩ := marginal_biases (run protocol1 uniform)
  unfold firstInformation at h₁
  unfold secondInformation at h₂
  rw [hfa₀, hfa₁] at h₁
  rw [hfb₀, hfb₁] at h₂
  linarith [bias_ge_of_information ht ha₀ ha₁ h₁, bias_ge_of_information ht hb₀ hb₁ h₂,
    run_bias_bound protocol0, run_bias_bound protocol1]

private def fullBath (p : ℝ) (hp : p ∈ Icc (0 : ℝ) 1) : Bath where
  weight := 1
  weight_nonneg := zero_le_one
  weight_le_one := le_rfl
  reset := ⟨bernoulli p, bernoulli_nonneg hp, by simp [bernoulli]⟩

private def productMass (p q : ℝ) : Mass := fun z => bernoulli p z.1 * bernoulli q z.2

private theorem product_marginals (p q : ℝ) (b : Bool) :
    marginalFirst (productMass p q) b = bernoulli p b ∧
      marginalSecond (productMass p q) b = bernoulli q b := by
  have hsum (v : ℝ) : bernoulli v false + bernoulli v true = 1 := by simp [bernoulli]
  constructor
  · simp only [marginalFirst, productMass, ← mul_add, hsum, mul_one]
  · simp only [marginalSecond, productMass, ← add_mul, hsum, one_mul]

private theorem first_full (p : ℝ) (hp : p ∈ Icc (0 : ℝ) 1) (a : Law Point) (z : Point) :
    (firstBath (fullBath p hp) a).mass z = bernoulli p z.1 * marginalSecond a.mass z.2 := by
  simp [firstBath, fullBath]

open D5.S3.TotalVariation.Pinsker (totalVariation)
open D5.S3.TotalVariation.ProductSubadditive (total_variation_product_subadditive)

private theorem variation_bernoulli_half {p : ℝ} (hp : 1 / 2 ≤ p) :
    totalVariation (bernoulli p) (bernoulli (1 / 2)) = p - 1 / 2 := by
  have hd : 1 - p - (1 - 1 / 2) = -(p - 1 / 2) := by ring
  simp only [totalVariation, Fintype.sum_bool, bernoulli, Bool.false_eq_true, ↓reduceIte]
  rw [hd, abs_neg, abs_of_nonneg (sub_nonneg.mpr hp)]
  ring

private theorem product_preparation {p q : ℝ}
    (hp : p ∈ Icc (0 : ℝ) 1) (hq : q ∈ Icc (0 : ℝ) 1)
    (hp' : 1 / 2 ≤ p) (hq' : 1 / 2 ≤ q) :
    let protocol := [Step.first (fullBath p hp), Step.second (fullBath q hq)]
    (run protocol uniform).mass = productMass p q ∧
      bathVariation protocol uniform = p + q - 1 := by
  let a := firstBath (fullBath p hp) uniform
  let b := secondBath (fullBath q hq) a
  have half_mem : (1 / 2 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hu : uniform.mass = productMass (1 / 2) (1 / 2) := by
    funext ⟨x, y⟩
    cases x <;> cases y <;> norm_num [uniform, productMass, bernoulli]
  have ha : a.mass = productMass p (1 / 2) := by
    funext z
    change (firstBath (fullBath p hp) uniform).mass z = _
    rw [first_full, hu, (product_marginals _ _ _).2]
    rfl
  have hb : b.mass = productMass p q := by
    funext ⟨x, y⟩
    change (firstBath (fullBath q hq) (permute swap a)).mass (y, x) = _
    rw [first_full]
    change bernoulli q y * marginalFirst a.mass x = bernoulli p x * bernoulli q y
    rw [ha, (product_marginals _ _ _).1, mul_comm]
  have hmass {v : ℝ} (hv : v ∈ Icc (0 : ℝ) 1) : (∑ i : Bool, |bernoulli v i|) ≤ 1 := by
    simp_rw [abs_of_nonneg (bernoulli_nonneg hv _)]
    simp [bernoulli]
  have hcostA : totalVariation a.mass uniform.mass ≤ p - 1 / 2 := by
    rw [ha, hu, ← variation_bernoulli_half hp']
    have h := total_variation_product_subadditive (bernoulli p) (bernoulli (1 / 2))
      (bernoulli (1 / 2)) (bernoulli (1 / 2)) (hmass hp) (hmass half_mem)
    rwa [show totalVariation (bernoulli (1 / 2)) (bernoulli (1 / 2)) = 0 by
      simp [totalVariation], add_zero] at h
  have hcostB : totalVariation b.mass a.mass ≤ q - 1 / 2 := by
    rw [hb, ha, ← variation_bernoulli_half hq']
    have h := total_variation_product_subadditive (bernoulli p) (bernoulli p)
      (bernoulli q) (bernoulli (1 / 2)) (hmass hp) (hmass half_mem)
    rwa [show totalVariation (bernoulli p) (bernoulli p) = 0 by simp [totalVariation],
      zero_add] at h
  refine ⟨hb, le_antisymm ?_ ?_⟩
  · change totalVariation a.mass uniform.mass + (totalVariation b.mass a.mass + 0) ≤ p + q - 1
    linarith
  · have h := run_bias_bound [Step.first (fullBath p hp), Step.second (fullBath q hq)]
    change |momentA b.mass| + |momentB b.mass| ≤ _ at h
    obtain ⟨⟨_, hA⟩, ⟨_, hB⟩⟩ := marginal_biases b
    rw [hb, (product_marginals _ _ _).1] at hA
    rw [hb, (product_marginals _ _ _).2] at hB
    simp only [bernoulli, Bool.false_eq_true, ↓reduceIte, biasProb] at hA hB
    rw [← hb] at hA hB
    linarith [le_abs_self (momentA b.mass), le_abs_self (momentB b.mass)]

/-- Swap the two registers and complement both outcomes. -/
def swapComplement : Equiv.Perm Point :=
  swap.trans (Equiv.prodCongr Equiv.boolNot Equiv.boolNot)

private theorem swapComplement_product {a : Law Point} {p q : ℝ}
    (ha : a.mass = productMass p q) :
    (permute swapComplement a).mass = productMass (1 - q) (1 - p) := by
  funext ⟨x, y⟩
  change a.mass (!y, !x) = _
  rw [ha]
  cases x <;> cases y <;> simp [productMass, bernoulli, mul_comm]

/-- The bound is attained for every threshold `g t` in the finite model. Both branches
use the same two weight-one local resets. Only the second branch then swaps and
complements the two registers. The pure reset endpoints are ideal finite-model operations. -/
theorem recording_information_bound_sharp {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ∃ bath₁ bath₂ : Bath, bath₁.weight = 1 ∧ bath₂.weight = 1 ∧
      let protocol0 := [Step.first bath₁, Step.second bath₂]
      let protocol1 := [Step.first bath₁, Step.second bath₂, Step.reversible swapComplement]
      firstInformation (run protocol0 uniform) (run protocol1 uniform) = g t ∧
      secondInformation (run protocol0 uniform) (run protocol1 uniform) = g t ∧
      (bathVariation protocol0 uniform + bathVariation protocol1 uniform) / 2 = t := by
  let x := min 1 (2 * t)
  let y := 2 * t - x
  let p := biasProb x
  let q := biasProb y
  obtain ⟨hx, hy⟩ := extreme_biases ht
  have hp : p ∈ Icc (0 : ℝ) 1 := ⟨by dsimp [p, biasProb]; linarith [hx.1],
    by dsimp [p, biasProb]; linarith [hx.2]⟩
  have hq : q ∈ Icc (0 : ℝ) 1 := ⟨by dsimp [q, biasProb]; linarith [hy.1],
    by dsimp [q, biasProb]; linarith [hy.2]⟩
  let a := fullBath p hp
  let b := fullBath q hq
  let protocol0 := [Step.first a, Step.second b]
  let protocol1 := [Step.first a, Step.second b, Step.reversible swapComplement]
  obtain ⟨hprod, hcost⟩ := product_preparation hp hq
    (by dsimp [p, biasProb]; linarith [hx.1]) (by dsimp [q, biasProb]; linarith [hy.1])
  change (run protocol0 uniform).mass = productMass p q at hprod
  change bathVariation protocol0 uniform = p + q - 1 at hcost
  have hprod' : (run protocol1 uniform).mass = productMass (1 - q) (1 - p) :=
    swapComplement_product hprod
  have hfirst : J p (1 - q) = g t := by
    rw [show 1 - q = (1 - y) / 2 by dsimp [q, biasProb]; ring]
    exact J_eq_g_at_extreme t
  refine ⟨a, b, rfl, rfl, ?_, ?_, ?_⟩
  · change firstInformation (run protocol0 uniform) (run protocol1 uniform) = _
    simp only [firstInformation, hprod, hprod', (product_marginals _ _ _).1,
      bernoulli, Bool.false_eq_true, ↓reduceIte]
    exact hfirst
  · change secondInformation (run protocol0 uniform) (run protocol1 uniform) = _
    simp only [secondInformation, hprod, hprod', (product_marginals _ _ _).2,
      bernoulli, Bool.false_eq_true, ↓reduceIte]
    rw [J_comm q (1 - p), ← show 1 - (1 - q) = q by ring, J_reflect]
    exact hfirst
  · change (bathVariation protocol0 uniform + bathVariation protocol1 uniform) / 2 = t
    have hcost' : bathVariation protocol1 uniform = bathVariation protocol0 uniform := by
      simp [protocol1, protocol0, bathVariation, Step.cost]
    rw [hcost', hcost]
    dsimp [p, q, biasProb, y]
    ring

end D5.S3.Quantum.Information.RecordWriting.TwoRegisterInformation
