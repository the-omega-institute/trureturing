/- GID: D5/S3/Fourier/Asymptotics/CyclicParityLimit
   generality: G
   mirror-B: D5/B/S3/Fourier/Asymptotics/CyclicParityLimit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The parity-dependent correction to the two-cosine cyclic minimum. -/

import D5.S3.Fourier.Asymptotics.CyclicParityCorrection
import Mathlib.Analysis.Complex.Trigonometric

/-! The finite certificates squeeze the minimum to second order in the mesh.
Only a fixed front window contributes to the clipped quadratic. -/

open Finset Filter
open scoped Topology
open D5.S3.Fourier.Asymptotics.CyclicToLatticeComparison
open D5.S3.Fourier.Asymptotics.LatticeSquareMomentActivation
open D5.S3.Fourier.Asymptotics.CyclicParityCorrection

noncomputable section

namespace D5.S3.Fourier.Asymptotics.CyclicParityLimit

set_option autoImplicit false

def cosineFourth (x h : ℝ) : ℝ :=
  (Real.cos (x * h) - (1 - (x * h) ^ 2 / 2)) / h ^ 4

def cosineSecond (x h : ℝ) : ℝ :=
  x ^ 2 / 2 - h ^ 2 * cosineFourth x h

theorem cosineSecond_eq (x : ℝ) {h : ℝ} (hn : h ≠ 0) :
    1 - Real.cos (x * h) = h ^ 2 * cosineSecond x h := by
  unfold cosineSecond cosineFourth
  field_simp [hn]
  ring

private theorem cos_fourth_remainder (x : ℝ) (hx : |x| ≤ 1) :
    |Real.cos x - (1 - x ^ 2 / 2 + x ^ 4 / 24)| ≤ |x| ^ 6 / 360 := by
  let z := (x : ℂ) * Complex.I
  have hz : ‖z‖ = |x| := by simp [z, Complex.norm_mul]
  have h := Complex.exp_bound' (x := z) (n := 6) (by rw [hz]; linarith)
  have ht : (∑ m ∈ range 6, z ^ m / (m.factorial : ℂ)).re =
      1 - x ^ 2 / 2 + x ^ 4 / 24 := by
    norm_num [z, sum_range_succ, mul_pow, pow_succ, Complex.mul_re, Complex.mul_im,
      Complex.div_re, Complex.normSq_apply]
    ring
  have hr := Complex.abs_re_le_norm (Complex.exp z - ∑ m ∈ range 6, z ^ m / (m.factorial : ℂ))
  rw [Complex.sub_re, ht, show (Complex.exp z).re = Real.cos x from Complex.exp_ofReal_mul_I_re x] at hr
  rw [hz] at h
  norm_num at h
  exact hr.trans (by linarith only [h])

theorem cosineFourth_tendsto {ι : Type*} {l : Filter ι} {h : ι → ℝ}
    (hh : Tendsto h l (𝓝 0)) (hn : ∀ᶠ i in l, h i ≠ 0) (x : ℝ) :
    Tendsto (fun i => cosineFourth x (h i)) l (𝓝 (x ^ 4 / 24)) := by
  have hxh : Tendsto (fun i => |x * h i|) l (𝓝 0) := by
    simpa using (hh.const_mul x).abs
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero' (g := fun i => |x| ^ 6 / 360 * h i ^ 2)
    (Eventually.of_forall fun _ => dist_nonneg) ?_ ?_
  · filter_upwards [hn, hxh.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))]
      with i hi hx
    have hr := cos_fourth_remainder (x * h i) hx.le
    have hid : cosineFourth x (h i) - x ^ 4 / 24 =
        (Real.cos (x * h i) - (1 - (x * h i) ^ 2 / 2 + (x * h i) ^ 4 / 24)) / h i ^ 4 := by
      unfold cosineFourth
      field_simp [hi]
      ring
    rw [Real.dist_eq, hid, abs_div, abs_of_nonneg (by positivity : 0 ≤ h i ^ 4)]
    have hpow : 0 < h i ^ 4 := by
      rw [show h i ^ 4 = (h i ^ 2) ^ 2 by ring]
      exact pow_pos (sq_pos_of_ne_zero hi) 2
    apply (div_le_iff₀ hpow).mpr
    calc
      _ ≤ |x * h i| ^ 6 / 360 := hr
      _ = (|x| ^ 6 / 360 * h i ^ 2) * h i ^ 4 := by
        rw [abs_mul, mul_pow, ← abs_pow (h i), abs_of_nonneg (by positivity : 0 ≤ h i ^ 6)]
        ring
  · simpa using (hh.pow 2).const_mul (|x| ^ 6 / 360)

theorem cosineSecond_tendsto {ι : Type*} {l : Filter ι} {h : ι → ℝ}
    (hh : Tendsto h l (𝓝 0)) (hn : ∀ᶠ i in l, h i ≠ 0) (x : ℝ) :
    Tendsto (fun i => cosineSecond x (h i)) l (𝓝 (x ^ 2 / 2)) := by
  simpa [cosineSecond] using
    tendsto_const_nhds.sub ((hh.pow 2).mul (cosineFourth_tendsto hh hn x))

private theorem clip_sq_correction {ι : Type*} {l : Filter ι} {s r : ι → ℝ}
    {b a : ℝ} (hs : Tendsto s l (𝓝 0)) (hspos : ∀ᶠ i in l, 0 < s i)
    (hr : Tendsto r l (𝓝 a)) :
    Tendsto (fun i => ((max 0 (b + s i * r i)) ^ 2 - (max 0 b) ^ 2) / s i)
      l (𝓝 (2 * max 0 b * a)) := by
  have hpert : Tendsto (fun i => b + s i * r i) l (𝓝 b) := by
    simpa using tendsto_const_nhds.add (hs.mul hr)
  rcases lt_trichotomy b 0 with hb | rfl | hb
  · rw [max_eq_left hb.le, mul_zero, zero_mul]
    apply tendsto_const_nhds.congr'
    filter_upwards [hpert.eventually (eventually_lt_nhds hb)] with i hi
    simp [max_eq_left hi.le]
  · simp only [max_self, mul_zero, zero_mul, zero_pow two_ne_zero, sub_zero]
    have hmax : Tendsto (fun i => max 0 (r i)) l (𝓝 (max 0 a)) :=
      tendsto_const_nhds.max hr
    have ht := hs.mul (hmax.pow 2)
    simp only [zero_mul] at ht
    apply ht.congr'
    filter_upwards [hspos] with i hi
    have he : max 0 (s i * r i) = s i * max 0 (r i) := by
      rw [mul_max_of_nonneg _ _ hi.le, mul_zero]
    rw [zero_add, he]
    field_simp [hi.ne']
  · rw [max_eq_right hb.le]
    have ht := hr.mul ((hpert.add_const b))
    have ht' : Tendsto (fun i => r i * (b + s i * r i + b)) l (𝓝 (2 * b * a)) := by
      rwa [show a * (b + b) = 2 * b * a by ring] at ht
    apply ht'.congr'
    filter_upwards [hspos, hpert.eventually (eventually_gt_nhds hb)] with i hi hp
    rw [max_eq_right hp.le]
    field_simp [hi.ne']
    ring

def parityModulus (odd : Bool) (k : ℕ) : ℕ := 2 * k + if odd then 1 else 2

instance parityNeZero (odd : Bool) (k : ℕ) : NeZero (parityModulus odd k) :=
  ⟨by cases odd <;> simp [parityModulus]⟩

def parityOffset (odd : Bool) : ℝ := if odd then 1 / 2 else 0

theorem parity_offset (odd : Bool) (k : ℕ) :
    (↑(parityModulus odd k % 2) : ℝ) / 2 = parityOffset odd := by
  cases odd <;> simp [parityModulus, parityOffset, Nat.add_mod]

private theorem parity_modulus_eventually_gt (odd : Bool) (M : ℕ) :
    ∀ᶠ k in atTop, M < parityModulus odd k := by
  filter_upwards [eventually_ge_atTop (M + 1)] with k hk
  unfold parityModulus
  omega

theorem mesh_tendsto (odd : Bool) :
    Tendsto (fun k => mesh (parityModulus odd k)) atTop (𝓝 0) := by
  have hq : Tendsto (fun k => parityModulus odd k) atTop atTop :=
    tendsto_atTop.2 fun M => (parity_modulus_eventually_gt odd M).mono fun _ h => h.le
  exact tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp hq)

private def beta (t d h : ℝ) : ℝ :=
  (t - (2 * cosineSecond d h - h ^ 2 * cosineSecond d h ^ 2)) / (1 + Real.cos (d * h))

private def frontCorrection (t Z d x h : ℝ) : ℝ :=
  (2 * cosineFourth x h + cosineSecond x h ^ 2 - beta t d h * cosineSecond x h) / Z

private theorem beta_eq (t d : ℝ) {h : ℝ} (hn : h ≠ 0) :
    beta t d h = (t - (h ^ 2)⁻¹ * (1 - (-Real.cos (d * h)) ^ 2)) /
      (1 - (-Real.cos (d * h))) := by
  unfold beta
  congr 1
  · have hc := cosineSecond_eq d hn
    have he : Real.cos (d * h) = 1 - h ^ 2 * cosineSecond d h := by linarith only [hc]
    rw [he]
    field_simp [hn]
    ring
  · ring

private theorem beta_tendsto {ι : Type*} {l : Filter ι} {h : ι → ℝ}
    (hh : Tendsto h l (𝓝 0)) (hn : ∀ᶠ i in l, h i ≠ 0) (t d : ℝ) :
    Tendsto (fun i => beta t d (h i)) l (𝓝 ((t - d ^ 2) / 2)) := by
  have hs := cosineSecond_tendsto hh hn d
  have hc : Tendsto (fun i => Real.cos (d * h i)) l (𝓝 1) := by
    have hc' : Tendsto Real.cos (𝓝 (d * 0)) (𝓝 1) := by
      have ht := Real.continuous_cos.continuousAt (x := d * 0)
      simpa only [ContinuousAt, mul_zero, Real.cos_zero] using ht
    exact hc'.comp (hh.const_mul d)
  unfold beta
  have hx := (hs.const_mul 2).sub ((hh.pow 2).mul (hs.pow 2))
  have ht := ((tendsto_const_nhds (x := t)).sub hx).div
    (hc.const_add 1) (by norm_num : (1 : ℝ) + 1 ≠ 0)
  convert ht using 1
  congr 1
  ring

private theorem frontCorrection_tendsto {ι : Type*} {l : Filter ι} {h : ι → ℝ}
    (hh : Tendsto h l (𝓝 0)) (hn : ∀ᶠ i in l, h i ≠ 0) (t Z d x : ℝ) :
    Tendsto (fun i => frontCorrection t Z d x (h i)) l
      (𝓝 ((x ^ 4 / 3 - ((t - d ^ 2) / 2) * (x ^ 2 / 2)) / Z)) := by
  unfold frontCorrection
  have hs := cosineSecond_tendsto hh hn x
  convert (((cosineFourth_tendsto hh hn x).const_mul 2).add (hs.pow 2) |>.sub
    ((beta_tendsto hh hn t d).mul hs)).div_const Z using 1
  congr 1
  ring

private theorem frontDual_eq (t Z d x : ℝ) {h : ℝ} (hn : h ≠ 0) :
    (t - (h ^ 2)⁻¹ * (1 - Real.cos (x * h) ^ 2) -
      beta t d h * (1 - Real.cos (x * h))) / Z =
      (t - x ^ 2) / Z + h ^ 2 * frontCorrection t Z d x h := by
  have hc := cosineSecond_eq x hn
  have he : Real.cos (x * h) = 1 - h ^ 2 * cosineSecond x h := by linarith only [hc]
  conv_lhs => rw [he]
  unfold frontCorrection
  have hh : (h ^ 2)⁻¹ * (1 - (1 - h ^ 2 * cosineSecond x h) ^ 2) =
      2 * cosineSecond x h - h ^ 2 * cosineSecond x h ^ 2 := by
    field_simp [hn]
    ring
  rw [hh]
  unfold cosineSecond
  ring

private theorem centered_sum_window {q : ℕ} [NeZero q] (K : ℕ) (hq : 2 * K < q)
    (f : ZMod q → ℝ) (hf : ∀ i, i.valMinAbs ∉ Icc (-(K : ℤ)) (K : ℤ) → f i = 0) :
    (∑ i, f i) = ∑ j ∈ Icc (-(K : ℤ)) (K : ℤ), f (j : ZMod q) := by
  let S := Icc (-(K : ℤ)) (K : ℤ)
  let g (j : ℤ) := if j ∈ S then f (j : ZMod q) else 0
  have hg (j : ℤ) (hj : j ∉ S) : g j = 0 := if_neg hj
  calc
    (∑ i, f i) = ∑ i : ZMod q, g i.valMinAbs := by
      apply sum_congr rfl
      intro i _
      by_cases hi : i.valMinAbs ∈ S
      · simp [g, hi, ZMod.coe_valMinAbs]
      · rw [hf i hi, hg _ hi]
    _ = ∑' j, g j := sum_centered_eq_tsum hq g hg
    _ = ∑ j ∈ S, f (j : ZMod q) := by
      rw [(hasSum_sum_of_ne_finset_zero hg).tsum_eq]
      exact sum_congr rfl fun j hj => if_pos hj

theorem valMinAbs_of_window {q : ℕ} [NeZero q] {K : ℕ} (hq : 2 * K < q)
    {j : ℤ} (hj : j ∈ Icc (-(K : ℤ)) (K : ℤ)) :
    (j : ZMod q).valMinAbs = j := by
  have := mem_Icc.mp hj
  exact (ZMod.valMinAbs_spec _ _).mpr ⟨rfl, by constructor <;> omega⟩

private theorem sample_le_window {q K : ℕ} [NeZero q]
    (i : ZMod q) (hi : i.valMinAbs ∉ Icc (-(K : ℤ)) (K : ℤ)) :
    sample i ≤ Real.cos ((K : ℝ) * mesh q) := by
  rw [sample, centeredAngle_eq_mesh, ← Real.cos_abs ((i.valMinAbs : ℝ) * mesh q), abs_mul,
    abs_of_pos mesh_pos]
  have hnat : K ≤ i.valMinAbs.natAbs := by
    have h : ¬ (-(K : ℤ) ≤ i.valMinAbs ∧ i.valMinAbs ≤ K) := by simpa using hi
    omega
  have hbound : |(i.valMinAbs : ℝ)| * mesh q ≤ Real.pi := by
    simpa only [centeredAngle_eq_mesh, abs_mul, abs_of_pos mesh_pos]
      using abs_centeredAngle_le_pi i
  refine Real.cos_le_cos_of_nonneg_of_le_pi (mul_nonneg (Nat.cast_nonneg _) mesh_pos.le) hbound
    (mul_le_mul_of_nonneg_right ?_ mesh_pos.le)
  rw [← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]
  exact_mod_cast hnat

private theorem weight_zero_outside {m t Z : ℝ} {w : ℤ → ℝ} {n : ℕ}
    (act : Activation m n t Z w) {j : ℤ} (hj : j ∉ Icc (-((n + 2 : ℕ) : ℤ)) (↑(n + 2) : ℤ)) :
    w j = 0 := by
  apply activation_zero_outside act
  have hR : latticeSupportRadius n m ≤ n + 2 := by
    unfold latticeSupportRadius
    split <;> omega
  intro h
  apply hj
  have hR' : (latticeSupportRadius n m : ℤ) ≤ (↑(n + 2) : ℤ) := by
    exact_mod_cast hR
  have bounds := mem_Icc.mp h
  exact mem_Icc.mpr ⟨by linarith [bounds.1], bounds.2.trans hR'⟩

private def frontWeight (t Z : ℝ) (j : ℤ) : ℝ := (t - (j : ℝ) ^ 2) / Z

private theorem activation_clip {m t Z : ℝ} {n : ℕ} {w : ℤ → ℝ}
    (act : Activation m n t Z w) (j : ℤ) : max 0 (frontWeight t Z j) = w j := by
  rw [act.law, frontWeight, ← max_div_div_right act.normalizer_pos.le, zero_div]

private theorem lattice_sum {m t Z : ℝ} {n : ℕ} {w : ℤ → ℝ}
    (act : Activation m n t Z w) (f : ℤ → ℝ) :
    (∑ j ∈ Icc (-((n + 2 : ℕ) : ℤ)) (↑(n + 2) : ℤ), f j * w j) =
      ∑' j, f j * w j := by
  apply (hasSum_sum_of_ne_finset_zero ?_).tsum_eq.symm
  intro j hj
  rw [weight_zero_outside act hj, mul_zero]

private theorem lattice_energy_window {m t Z : ℝ} {n : ℕ} {w : ℤ → ℝ}
    (act : Activation m n t Z w) :
    (∑ j ∈ Icc (-((n + 2 : ℕ) : ℤ)) (↑(n + 2) : ℤ), w j ^ 2) = (t - m) / Z ∧
    (∑' j, w j ^ 2) = (t - m) / Z := by
  have henergy := lattice_energy_eq act
  have hwindow : (∑ j ∈ Icc (-((n + 2 : ℕ) : ℤ)) (↑(n + 2) : ℤ), w j ^ 2) =
      ∑' j, w j ^ 2 := by
    simpa only [pow_two] using lattice_sum act w
  exact ⟨hwindow.trans henergy, henergy⟩

section ParityLimits

variable (odd : Bool)

private abbrev qAt (k : ℕ) := parityModulus odd k
private abbrev hAt (k : ℕ) := mesh (qAt odd k)
private abbrev sAt (k : ℕ) := hAt odd k ^ 2
private abbrev CAt (k : ℕ) := -Real.cos (parityOffset odd * hAt odd k)

private theorem sAt_pos (k : ℕ) : 0 < sAt odd k := pow_pos mesh_pos _

private theorem sAt_tendsto : Tendsto (sAt odd) atTop (𝓝 0) := by
  simpa using (mesh_tendsto odd).pow 2

private theorem mesh_ne : ∀ᶠ k in atTop, hAt odd k ≠ 0 :=
  Eventually.of_forall fun _ => mesh_pos.ne'

private theorem CAt_tendsto : Tendsto (CAt odd) atTop (𝓝 (-1)) := by
  have hc' : Tendsto Real.cos (𝓝 (parityOffset odd * 0)) (𝓝 1) := by
    have ht := Real.continuous_cos.continuousAt (x := parityOffset odd * 0)
    simpa only [ContinuousAt, mul_zero, Real.cos_zero] using ht
  have hc : Tendsto (fun k => Real.cos (parityOffset odd * hAt odd k)) atTop (𝓝 1) :=
    hc'.comp ((mesh_tendsto odd).const_mul (parityOffset odd))
  exact hc.neg

private abbrev pAt (t Z : ℝ) (k : ℕ) (i : ZMod (qAt odd k)) : ℝ :=
  (t - (sAt odd k)⁻¹ * (1 - sample i ^ 2) -
    beta t (parityOffset odd) (hAt odd k) * (1 - sample i)) / Z

private abbrev rAt (t Z : ℝ) (j : ℤ) (k : ℕ) : ℝ :=
  frontCorrection t Z (parityOffset odd) (j : ℝ) (hAt odd k)

private theorem pAt_front (t Z : ℝ) (K k : ℕ) (hk : 2 * K < qAt odd k)
    {j : ℤ} (hj : j ∈ Icc (-(K : ℤ)) (K : ℤ)) :
    pAt odd t Z k (j : ZMod (qAt odd k)) = frontWeight t Z j + sAt odd k * rAt odd t Z j k := by
  have hs : sample (j : ZMod (qAt odd k)) = Real.cos ((j : ℝ) * hAt odd k) := by
    unfold sample
    rw [centeredAngle_eq_mesh, valMinAbs_of_window hk hj]
  dsimp only [pAt]
  rw [hs]
  exact frontDual_eq t Z (parityOffset odd) (j : ℝ) mesh_pos.ne'

private theorem pAt_certificate (t Z a : ℝ) (hz : 0 < Z) (k : ℕ) (hc : CAt odd k < 1) :
    let β := beta t (parityOffset odd) (hAt odd k)
    let ρ := -CAt odd k - β * sAt odd k
    sample ((↑(qAt odd k / 2) : ℤ) : ZMod (qAt odd k)) = CAt odd k ∧
    (∀ i, CAt odd k ≤ sample i ∧
      pAt odd t Z k i = (sAt odd k)⁻¹ * (sample i - CAt odd k) * (sample i - ρ) / Z ∧
      (0 < max 0 (pAt odd t Z k i) ↔ CAt odd k < sample i ∧ ρ < sample i)) ∧
    ∀ v : ZMod (qAt odd k) → ℝ, (∑ i, v i) = 1 →
      energy v =
        (2 * (t - ((sAt odd k)⁻¹ / 2 + β) * (1 - a)) / Z -
          ∑ i, (max 0 (pAt odd t Z k i)) ^ 2) +
        (∑ i, (v i - max 0 (pAt odd t Z k i)) ^ 2) +
        2 * (∑ i, v i * (max 0 (pAt odd t Z k i) - pAt odd t Z k i)) +
        (2 * β / Z) * (cosineMoment 1 v - a) +
        ((sAt odd k)⁻¹ / Z) * (cosineMoment 2 v - a) := by
  have hp := antipodal_dual_certificate (qAt odd k) t (sAt odd k)⁻¹ Z a
    (inv_pos.mpr (sAt_pos odd k)) hz (by simpa [qAt, parity_offset] using hc)
  dsimp only at hp ⊢
  simpa only [pAt, beta_eq t (parityOffset odd) (mesh_pos (q := qAt odd k)).ne',
    qAt, hAt, sAt, CAt, parity_offset, div_inv_eq_mul] using hp

private theorem pAt_support {t Z : ℝ} (hz : 0 < Z) {K : ℕ} (hK : t < (K : ℝ) ^ 2) :
    ∀ᶠ k in atTop, ∀ i : ZMod (qAt odd k),
      i.valMinAbs ∉ Icc (-(K : ℤ)) (K : ℤ) → max 0 (pAt odd t Z k i) = 0 := by
  have hd := cosineSecond_tendsto (mesh_tendsto odd) (mesh_ne odd) (parityOffset odd)
  have hb := beta_tendsto (mesh_tendsto odd) (mesh_ne odd) t (parityOffset odd)
  have hsum : Tendsto (fun k => cosineSecond (parityOffset odd) (hAt odd k) +
      beta t (parityOffset odd) (hAt odd k)) atTop (𝓝 (t / 2)) := by
    convert hd.add hb using 1
    congr 1
    ring
  have hfront := cosineSecond_tendsto (mesh_tendsto odd) (mesh_ne odd) (K : ℝ)
  have hcut := hsum.eventually_lt hfront (by linarith only [hK])
  have hC := (CAt_tendsto odd).eventually (eventually_lt_nhds (by norm_num : (-1 : ℝ) < 1))
  filter_upwards [hcut, hC,
    parity_modulus_eventually_gt odd (2 * K)] with k hcut hc hk i hi
  have hr := (pAt_certificate odd t Z 0 hz k hc).2.1 i
  have hw := sample_le_window i hi
  have he₁ := cosineSecond_eq (K : ℝ) (mesh_pos (q := qAt odd k)).ne'
  have he₂ := cosineSecond_eq (parityOffset odd) (mesh_pos (q := qAt odd k)).ne'
  have hs := mul_lt_mul_of_pos_left hcut (sAt_pos odd k)
  have hρ : sample i ≤ -CAt odd k - beta t (parityOffset odd) (hAt odd k) * sAt odd k := by
    dsimp only [CAt]
    linarith only [hw, he₁, he₂, hs]
  apply le_antisymm _ (le_max_left _ _)
  exact le_of_not_gt fun hp => (not_lt_of_ge hρ) ((hr.2.2.mp hp).2)

private theorem pAt_sq_window_limit {m t Z : ℝ} {n : ℕ} {w : ℤ → ℝ}
    (act : Activation m n t Z w) :
    Tendsto (fun k =>
      ((∑ i, (max 0 (pAt odd t Z k i)) ^ 2) - (t - m) / Z) / sAt odd k) atTop
      (𝓝 (2 / Z * ((∑' j : ℤ, (j : ℝ) ^ 4 * w j) / 3 -
        ((t - parityOffset odd ^ 2) / 2) * m / 2))) := by
  let K := n + 2
  let S := Icc (-(K : ℤ)) (K : ℤ)
  let b := frontWeight t Z
  let β₀ := (t - parityOffset odd ^ 2) / 2
  let a := fun j : ℤ => ((j : ℝ) ^ 4 / 3 - β₀ * ((j : ℝ) ^ 2 / 2)) / Z
  have hK : t < (K : ℝ) ^ 2 := by
    have hn := Nat.cast_nonneg (α := ℝ) n
    dsimp [K]
    push_cast
    nlinarith only [act.radius_upper, hn]
  have h₁ (j : ℤ) : Tendsto (rAt odd t Z j) atTop (𝓝 (a j)) :=
    frontCorrection_tendsto (mesh_tendsto odd) (mesh_ne odd) t Z (parityOffset odd) (j : ℝ)
  have hs := tendsto_finsetSum S fun j _ =>
    clip_sq_correction (b := b j) (sAt_tendsto odd) (Eventually.of_forall (sAt_pos odd)) (h₁ j)
  have hm₂ : ∑ j ∈ S, (j : ℝ) ^ 2 * w j = m :=
    (lattice_sum act _).trans act.second_moment.tsum_eq
  have hcalc : ∑ j ∈ S, 2 * max 0 (b j) * a j =
      2 / Z * ((∑' j : ℤ, (j : ℝ) ^ 4 * w j) / 3 - β₀ * m / 2) := by
    have he (j : ℤ) : 2 * max 0 (b j) * a j = 2 / Z *
        (((j : ℝ) ^ 4 * w j) / 3 - β₀ / 2 * ((j : ℝ) ^ 2 * w j)) := by
      change 2 * max 0 (frontWeight t Z j) * a j = _
      rw [activation_clip act]
      unfold a
      ring
    simp_rw [he]
    rw [← mul_sum, sum_sub_distrib, ← sum_div, ← mul_sum, hm₂, lattice_sum act]
    ring
  rw [hcalc] at hs
  apply hs.congr'
  filter_upwards [pAt_support odd act.normalizer_pos hK, parity_modulus_eventually_gt odd (2 * K)]
    with k hsupport hk
  rw [centered_sum_window K hk _ (fun i hi => by rw [hsupport i hi, zero_pow two_ne_zero]),
    ← (lattice_energy_window act).1]
  change _ = ((∑ j ∈ S, _) - (∑ j ∈ S, w j ^ 2)) / _
  rw [← sum_sub_distrib, sum_div]
  apply sum_congr rfl
  intro j hj
  rw [pAt_front odd t Z K k hk hj]
  rw [← activation_clip act j]

private abbrev uAt (w : ℤ → ℝ) (k : ℕ) (i : ZMod (qAt odd k)) : ℝ :=
  w i.valMinAbs

private theorem embedded_sum_window {m t Z : ℝ} {n : ℕ} {w : ℤ → ℝ}
    (act : Activation m n t Z w) {k : ℕ} (hk : 2 * (n + 2) < qAt odd k)
    (f : ZMod (qAt odd k) → ℝ) :
    (∑ i, uAt odd w k i * f i) =
      ∑ j ∈ Icc (-((n + 2 : ℕ) : ℤ)) (↑(n + 2) : ℤ), w j * f (j : ZMod (qAt odd k)) := by
  rw [centered_sum_window (n + 2) hk _ (fun i hi => by
    rw [uAt, weight_zero_outside act hi, zero_mul])]
  apply sum_congr rfl
  intro j hj
  rw [uAt, valMinAbs_of_window hk hj]

private theorem embedded_mass {m t Z : ℝ} {n : ℕ} {w : ℤ → ℝ}
    (act : Activation m n t Z w) {k : ℕ} (hk : 2 * (n + 2) < qAt odd k) :
    (∑ i, uAt odd w k i) = 1 := by
  simpa only [mul_one, one_mul, act.mass.tsum_eq] using
    (embedded_sum_window odd act hk (fun _ => 1)).trans
      (show (∑ j ∈ Icc (-((n + 2 : ℕ) : ℤ)) (↑(n + 2) : ℤ), w j * 1) = 1 by
        simpa only [mul_one, one_mul, act.mass.tsum_eq] using lattice_sum act (fun _ => 1))

private def windowFourth (n : ℕ) (r : ℝ) (w : ℤ → ℝ) (h : ℝ) : ℝ :=
  ∑ j ∈ Icc (-((n + 2 : ℕ) : ℤ)) (↑(n + 2) : ℤ), w j * cosineFourth (r * (j : ℝ)) h

private theorem windowFourth_tendsto (n : ℕ) (r : ℝ) (w : ℤ → ℝ) :
    Tendsto (fun k => windowFourth n r w (hAt odd k)) atTop
      (𝓝 (∑ j ∈ Icc (-((n + 2 : ℕ) : ℤ)) (↑(n + 2) : ℤ), w j * (r * (j : ℝ)) ^ 4 / 24)) := by
  unfold windowFourth
  simp_rw [mul_div_assoc]
  exact tendsto_finsetSum _ fun j _ =>
    (cosineFourth_tendsto (mesh_tendsto odd) (mesh_ne odd) (r * (j : ℝ))).const_mul (w j)

private theorem embedded_deficit {m t Z : ℝ} {n : ℕ} {w : ℤ → ℝ}
    (act : Activation m n t Z w) {k : ℕ} (hk : 2 * (n + 2) < qAt odd k) (r : ℕ) :
    1 - cosineMoment r (uAt odd w k) =
      sAt odd k * ((r : ℝ) ^ 2 * m / 2 -
        sAt odd k * windowFourth n (r : ℝ) w (hAt odd k)) := by
  have hmass := embedded_mass odd act hk
  have he : 1 - cosineMoment r (uAt odd w k) =
      ∑ i, uAt odd w k i * (1 - Real.cos ((r : ℝ) * centeredAngle i)) := by
    rw [cosineMoment_eq_centered]
    simp_rw [mul_sub, mul_one]
    rw [sum_sub_distrib, hmass]
  rw [he, embedded_sum_window odd act hk]
  have hterm (j : ℤ) (hj : j ∈ Icc (-((n + 2 : ℕ) : ℤ)) (↑(n + 2) : ℤ)) :
      w j * (1 - Real.cos ((r : ℝ) * centeredAngle (j : ZMod (qAt odd k)))) =
        sAt odd k * (((r : ℝ) ^ 2 / 2) * ((j : ℝ) ^ 2 * w j) -
          sAt odd k * (w j * cosineFourth ((r : ℝ) * (j : ℝ)) (hAt odd k))) := by
    rw [centeredAngle_eq_mesh, valMinAbs_of_window hk hj, ← mul_assoc]
    rw [cosineSecond_eq _ (mesh_pos (q := qAt odd k)).ne']
    unfold cosineSecond
    ring
  rw [sum_congr rfl hterm, ← mul_sum, sum_sub_distrib, ← mul_sum, ← mul_sum,
    (lattice_sum act _).trans act.second_moment.tsum_eq]
  unfold windowFourth
  ring

private abbrev UAt (k : ℕ) := 1 - CAt odd k
private abbrev Vnorm (k : ℕ) :=
  2 * (2 * cosineSecond (parityOffset odd) (hAt odd k) -
    sAt odd k * cosineSecond (parityOffset odd) (hAt odd k) ^ 2)

private theorem Vnorm_eq (k : ℕ) :
    2 * (1 - CAt odd k ^ 2) = sAt odd k * Vnorm odd k := by
  have he := cosineSecond_eq (parityOffset odd) (mesh_pos (q := qAt odd k)).ne'
  have hc : Real.cos (parityOffset odd * hAt odd k) =
      1 - sAt odd k * cosineSecond (parityOffset odd) (hAt odd k) := by linarith only [he]
  dsimp only [CAt, Vnorm]
  conv_lhs => rw [hc]
  ring

private abbrev denAt (k : ℕ) := cosineSecond 2 (hAt odd k) -
  sAt odd k * Vnorm odd k * cosineSecond 1 (hAt odd k) / UAt odd k

private theorem primal_mesh_limits :
    Tendsto (UAt odd) atTop (𝓝 2) ∧
    Tendsto (Vnorm odd) atTop (𝓝 (2 * parityOffset odd ^ 2)) ∧
    Tendsto (denAt odd) atTop (𝓝 2) := by
  have hu : Tendsto (UAt odd) atTop (𝓝 2) := by
    convert (CAt_tendsto odd).const_sub 1 using 1
    norm_num
  have hs := sAt_tendsto odd
  have hS (x : ℝ) := cosineSecond_tendsto (mesh_tendsto odd) (mesh_ne odd) x
  have hv : Tendsto (Vnorm odd) atTop (𝓝 (2 * parityOffset odd ^ 2)) := by
    convert (((hS (parityOffset odd)).const_mul 2).sub
      (hs.mul ((hS (parityOffset odd)).pow 2))).const_mul 2 using 1
    congr 1
    ring
  refine ⟨hu, hv, ?_⟩
  have hd := (hS 2).sub (((hs.mul hv).mul (hS 1)).div hu (by norm_num))
  convert hd using 1
  norm_num

private def firstRemaining (m : ℝ) (n : ℕ) (w : ℤ → ℝ) (k : ℕ) : ℝ :=
  3 * m / 2 + sAt odd k * windowFourth n 1 w (hAt odd k)

private def deltaNorm (m : ℝ) (n : ℕ) (w : ℤ → ℝ) (k : ℕ) : ℝ :=
  (windowFourth n 2 w (hAt odd k) - Vnorm odd k * firstRemaining odd m n w k / UAt odd k) /
    denAt odd k

private def muNorm (m : ℝ) (n : ℕ) (w : ℤ → ℝ) (k : ℕ) : ℝ :=
  (firstRemaining odd m n w k -
    sAt odd k * cosineSecond 1 (hAt odd k) * deltaNorm odd m n w k) / UAt odd k

private theorem primal_norm_limits (m : ℝ) (n : ℕ) (w : ℤ → ℝ) :
    ∃ L : ℝ, Tendsto (deltaNorm odd m n w) atTop (𝓝 L) ∧
      Tendsto (muNorm odd m n w) atTop (𝓝 (3 * m / 4)) := by
  obtain ⟨hu, hv, hden⟩ := primal_mesh_limits odd
  have hs := sAt_tendsto odd
  have hrem : Tendsto (firstRemaining odd m n w) atTop (𝓝 (3 * m / 2)) := by
    unfold firstRemaining
    simpa only [zero_mul, add_zero] using
      (hs.mul (windowFourth_tendsto odd n 1 w)).const_add (3 * m / 2)
  have hd : Tendsto (deltaNorm odd m n w) atTop _ :=
    ((windowFourth_tendsto odd n 2 w).sub ((hv.mul hrem).div hu (by norm_num))).div
      hden (by norm_num)
  refine ⟨_, hd, ?_⟩
  have h1 := cosineSecond_tendsto (mesh_tendsto odd) (mesh_ne odd) 1
  have ht := (hrem.sub ((hs.mul h1).mul hd)).div hu (by norm_num)
  change Tendsto (muNorm odd m n w) atTop _ at ht
  convert ht using 1
  simp only [zero_mul, sub_zero]
  congr 1
  ring

private theorem lattice_front_pos {m t Z : ℝ} {n : ℕ} {w : ℤ → ℝ} (hn : 0 < n)
    (hm : 0 < m) (act : Activation m n t Z w) :
    1 < t ∧ 0 < w 0 ∧ 0 < w 1 ∧ 0 < w (-1) := by
  have ht : 1 < t := by
    by_cases hn1 : n = 1
    · subst n
      have ht := act.radius_lower
      norm_num at ht
      apply lt_of_le_of_ne ht
      intro h
      have he := act.lower_endpoint.mpr (by simpa using h.symm)
      norm_num at he
      linarith only [hm, he]
    · have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast (show 2 ≤ n by omega)
      nlinarith only [act.radius_lower, sq_nonneg ((n : ℝ) - 2), hn2]
  refine ⟨ht, ?_, ?_, ?_⟩ <;> rw [act.law] <;> apply div_pos _ act.normalizer_pos
  all_goals apply lt_of_lt_of_le _ (le_max_right _ _)
  all_goals norm_num; linarith only [ht]

private abbrev δAt (m : ℝ) (n : ℕ) (w : ℤ → ℝ) (k : ℕ) :=
  sAt odd k * deltaNorm odd m n w k

private abbrev μAt (m : ℝ) (n : ℕ) (w : ℤ → ℝ) (k : ℕ) :=
  sAt odd k * muNorm odd m n w k

private abbrev vAt (m : ℝ) (n : ℕ) (w : ℤ → ℝ) (k : ℕ) :=
  adjusted (uAt odd w k) (δAt odd m n w k) (μAt odd m n w k) (δAt odd m n w k / 2)

private theorem vAt_feasible {m t Z : ℝ} {n : ℕ} {w : ℤ → ℝ}
    (hn : 0 < n) (hm : 0 < m) (act : Activation m n t Z w) :
    ∀ᶠ k in atTop, vAt odd m n w k ∈ feasible (qAt odd k) (1 - 2 * m * sAt odd k) ∧
      cosineMoment 1 (vAt odd m n w k) = 1 - 2 * m * sAt odd k ∧
      cosineMoment 2 (vAt odd m n w k) = 1 - 2 * m * sAt odd k := by
  obtain ⟨L, hd, hμ⟩ := primal_norm_limits odd m n w
  obtain ⟨hu, _, hden⟩ := primal_mesh_limits odd
  obtain ⟨_, hw0, hw1, hwn⟩ := lattice_front_pos hn hm act
  have hs := sAt_tendsto odd
  have hδ0 : Tendsto (δAt odd m n w) atTop (𝓝 0) := by simpa using hs.mul hd
  have hμ0 : Tendsto (μAt odd m n w) atTop (𝓝 0) := by simpa using hs.mul hμ
  have h0 := ((hδ0.const_sub (w 0)).sub hμ0)
  have h1 := (hδ0.div_const 2).const_add (w 1)
  have hneg := (hδ0.div_const 2).const_add (w (-1))
  simp only [sub_zero, zero_div, add_zero] at h0 h1 hneg
  filter_upwards [parity_modulus_eventually_gt odd (2 * (n + 2)),
    hu.eventually (eventually_gt_nhds (by norm_num : (0 : ℝ) < 2)),
    hden.eventually (eventually_gt_nhds (by norm_num : (0 : ℝ) < 2)),
    hμ.eventually (eventually_gt_nhds (by positivity : 0 < 3 * m / 4)),
    h0.eventually (eventually_gt_nhds hw0), h1.eventually (eventually_gt_nhds hw1),
    hneg.eventually (eventually_gt_nhds hwn)] with k hk hU hden hμ hk0 hk1 hkn
  let q := qAt odd k
  let U := UAt odd k
  let s := sAt odd k
  let A := 2 * m * s
  let u := uAt odd w k
  let F := 1 - Real.cos (hAt odd k)
  let G := 1 - Real.cos (2 * hAt odd k)
  let V := 2 * (1 - CAt odd k ^ 2)
  have hq : 4 < q := by
    change 2 * (n + 2) < q at hk
    omega
  have hsne : s ≠ 0 := (sAt_pos odd k).ne'
  have hF : F = s * cosineSecond 1 (hAt odd k) := by
    simpa [F] using cosineSecond_eq 1 (mesh_pos (q := q)).ne'
  have hG : G = s * cosineSecond 2 (hAt odd k) := cosineSecond_eq 2 (mesh_pos (q := q)).ne'
  have hV : V = s * Vnorm odd k := Vnorm_eq odd k
  have hDen : G - V * F / U = s * denAt odd k := by
    rw [hF, hG, hV]
    dsimp only [denAt, s]
    ring
  have hD1 : A - (1 - cosineMoment 1 u) = s * firstRemaining odd m n w k := by
    rw [embedded_deficit odd act hk]
    dsimp [A, firstRemaining, s]
    push_cast
    ring
  have hD2 : A - (1 - cosineMoment 2 u) = s ^ 2 * windowFourth n 2 w (hAt odd k) := by
    rw [embedded_deficit odd act hk]
    dsimp [A, s]
    ring
  have hδ : (A - (1 - cosineMoment 2 u) - V * (A - (1 - cosineMoment 1 u)) / U) /
      (G - V * F / U) = δAt odd m n w k := by
    rw [hDen, hD1, hD2, hV]
    let M := windowFourth n 2 w (hAt odd k)
    let N := Vnorm odd k * firstRemaining odd m n w k
    let D := denAt odd k
    change (s ^ 2 * M - s * Vnorm odd k * (s * firstRemaining odd m n w k) / U) /
      (s * D) = s * ((M - N / U) / D)
    rw [show s ^ 2 * M - s * Vnorm odd k * (s * firstRemaining odd m n w k) / U =
      s * (s * (M - N / U)) by dsimp only [N]; ring]
    rw [mul_div_mul_left _ _ hsne, mul_div_assoc]
  have hmu : (A - (1 - cosineMoment 1 u) - F * δAt odd m n w k) / U =
      μAt odd m n w k := by
    rw [hD1, hF]
    dsimp only [δAt, μAt, muNorm, s]
    ring
  have front (j : ℤ) (hj : j ∈ Icc (-((n + 2 : ℕ) : ℤ)) (↑(n + 2) : ℤ)) :
      u (j : ZMod q) = w j := by
    dsimp only [u, uAt]
    rw [valMinAbs_of_window hk hj]
  have hrep0 : u 0 = w 0 := by
    simpa using front 0 (mem_Icc.mpr ⟨by omega, by omega⟩)
  have hrep1 : u 1 = w 1 := by simpa using front 1 (mem_Icc.mpr ⟨by omega, by omega⟩)
  have hrepn : u (-1) = w (-1) := by simpa using front (-1) (mem_Icc.mpr ⟨by omega, by omega⟩)
  have hv := adjusted_matches_moments q hq.le u A (fun i _ _ _ _ => act.nonneg _)
    (embedded_mass odd act hk)
  simp only [q, parity_offset] at hv
  have hv' := hv
  change 0 ≤ u 0 - _ - _ → _ at hv'
  change 0 ≤ u 0 - ((A - (1 - cosineMoment 2 u) - V *
    (A - (1 - cosineMoment 1 u)) / U) / (G - V * F / U)) - _ → _ at hv'
  rw [hδ, hmu, hrep0, hrep1, hrepn] at hv'
  exact hv' hk0.le hk1.le hkn.le
    (add_nonneg (act.nonneg _) (mul_nonneg (sAt_pos odd k).le hμ.le))

private theorem transfer_sq_bound {q : ℕ} [NeZero q] (w : ZMod q → ℝ) (δ μ : ℝ) :
    (∑ i, (adjusted w δ μ (δ / 2) i - w i) ^ 2) ≤
      4 * ((δ + μ) ^ 2 + (δ / 2) ^ 2 + (δ / 2) ^ 2 + μ ^ 2) := by
  have h (j : ZMod q) (x : ℝ) :
      (∑ i, ((Pi.single j x : ZMod q → ℝ) i) ^ 2) = x ^ 2 := by
    simp [Pi.single_apply, ite_pow]
  calc
    _ ≤ ∑ i, 4 * (((Pi.single 0 (δ + μ) : ZMod q → ℝ) i) ^ 2 +
        ((Pi.single 1 (δ / 2) : ZMod q → ℝ) i) ^ 2 +
        ((Pi.single (-1) (δ / 2) : ZMod q → ℝ) i) ^ 2 +
        ((Pi.single ((↑(q / 2) : ℤ) : ZMod q) μ : ZMod q → ℝ) i) ^ 2) := by
      apply sum_le_sum
      intro i _
      let a := (Pi.single 0 (δ + μ) : ZMod q → ℝ) i
      let b := (Pi.single 1 (δ / 2) : ZMod q → ℝ) i
      let c := (Pi.single (-1) (δ / 2) : ZMod q → ℝ) i
      let d := (Pi.single ((↑(q / 2) : ℤ) : ZMod q) μ : ZMod q → ℝ) i
      change (w i - a + b + c + d - w i) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2)
      nlinarith only [sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (a + d),
        sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d)]
    _ = _ := by rw [← mul_sum, sum_add_distrib, sum_add_distrib, sum_add_distrib, h, h, h, h]

private theorem primal_distance {m t Z : ℝ} {n : ℕ} {w : ℤ → ℝ}
    (act : Activation m n t Z w) :
    Tendsto (fun k =>
      (∑ i, (vAt odd m n w k i - max 0 (pAt odd t Z k i)) ^ 2) / sAt odd k)
      atTop (𝓝 0) := by
  let K := n + 2
  let S := Icc (-(K : ℤ)) (K : ℤ)
  have hK : t < (K : ℝ) ^ 2 := by
    have hn := Nat.cast_nonneg (α := ℝ) n
    dsimp [K]
    push_cast
    nlinarith only [act.radius_upper, hn]
  obtain ⟨L, hδ, hμ⟩ := primal_norm_limits odd m n w
  have hR := tendsto_finsetSum S fun j _ =>
    (frontCorrection_tendsto (mesh_tendsto odd) (mesh_ne odd) t Z
      (parityOffset odd) (j : ℝ)).pow 2
  let upper := fun k => 2 * sAt odd k * (
    4 * ((deltaNorm odd m n w k + muNorm odd m n w k) ^ 2 +
      (deltaNorm odd m n w k / 2) ^ 2 + (deltaNorm odd m n w k / 2) ^ 2 +
      muNorm odd m n w k ^ 2) + ∑ j ∈ S, rAt odd t Z j k ^ 2)
  have hlim : Tendsto upper atTop (𝓝 0) := by
    have he := ((((hδ.add hμ).pow 2).add ((hδ.div_const 2).pow 2)).add
      ((hδ.div_const 2).pow 2)).add (hμ.pow 2)
    simpa only [upper, mul_zero, zero_mul] using
      ((sAt_tendsto odd).const_mul 2).mul ((he.const_mul 4).add hR)
  refine squeeze_zero' (Eventually.of_forall fun k =>
    div_nonneg (sum_nonneg fun _ _ => sq_nonneg _) (sAt_pos odd k).le) ?_ hlim
  filter_upwards [parity_modulus_eventually_gt odd (2 * K), pAt_support odd act.normalizer_pos hK]
    with k hk hs
  let s := sAt odd k
  let u := uAt odd w k
  let p := fun i => max 0 (pAt odd t Z k i)
  let v := vAt odd m n w k
  have h1 := transfer_sq_bound u (δAt odd m n w k) (μAt odd m n w k)
  have h2 : (∑ i, (u i - p i) ^ 2) ≤ s ^ 2 * ∑ j ∈ S, rAt odd t Z j k ^ 2 := by
    rw [centered_sum_window K hk _ (fun i hi => by
      change (w i.valMinAbs - max 0 (pAt odd t Z k i)) ^ 2 = 0
      rw [hs i hi, weight_zero_outside act hi, sub_zero, zero_pow two_ne_zero]), mul_sum]
    apply sum_le_sum
    intro j hj
    change (w (j : ZMod (qAt odd k)).valMinAbs - max 0 (pAt odd t Z k (j : ZMod _))) ^ 2 ≤ _
    rw [valMinAbs_of_window hk hj, pAt_front odd t Z K k hk hj, ← activation_clip act j,
      ← mul_pow]
    rw [← sq_abs (_ - _), ← sq_abs (s * _)]
    apply (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).2
    have he := abs_max_sub_max_le_abs (frontWeight t Z j)
      (frontWeight t Z j + s * rAt odd t Z j k) (0 : ℝ)
    simpa [max_comm _ (0 : ℝ), show frontWeight t Z j -
      (frontWeight t Z j + s * rAt odd t Z j k) = -(s * rAt odd t Z j k) by ring] using he
  have h3 : (∑ i, (v i - p i) ^ 2) ≤ 2 * (∑ i, (v i - u i) ^ 2) +
      2 * (∑ i, (u i - p i) ^ 2) := by
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    exact sum_le_sum fun i _ => by nlinarith only [sq_nonneg (v i - u i - (u i - p i))]
  apply (div_le_iff₀ (sAt_pos odd k)).2
  calc
    _ ≤ _ := h3
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left h1 (by norm_num))
      (mul_le_mul_of_nonneg_left h2 (by norm_num))
    _ = _ := by dsimp only [upper, δAt, μAt, s]; ring

private theorem primal_complementarity {m t Z : ℝ} {n : ℕ} {w : ℤ → ℝ}
    (hn : 0 < n) (hm : 0 < m) (act : Activation m n t Z w) :
    ∀ᶠ k in atTop, ∀ i,
      vAt odd m n w k i * (max 0 (pAt odd t Z k i) - pAt odd t Z k i) = 0 := by
  let K := n + 2
  let S := Icc (-(K : ℤ)) (K : ℤ)
  have hpos : ∀ᶠ k in atTop, ∀ j ∈ S,
      0 < w j → 0 < frontWeight t Z j + sAt odd k * rAt odd t Z j k :=
    (eventually_all_finset S).2 fun j _ => by
      by_cases hj : 0 < w j
      · have hb : 0 < frontWeight t Z j := by
          rw [← activation_clip act j, lt_max_iff] at hj
          exact hj.resolve_left (lt_irrefl _)
        have hr := frontCorrection_tendsto (mesh_tendsto odd) (mesh_ne odd) t Z
          (parityOffset odd) (j : ℝ)
        have ht : Tendsto (fun k => frontWeight t Z j + sAt odd k * rAt odd t Z j k)
            atTop (𝓝 (frontWeight t Z j)) := by
          simpa only [zero_mul, add_zero] using ((sAt_tendsto odd).mul hr).const_add
            (frontWeight t Z j)
        exact (ht.eventually (eventually_gt_nhds hb)).mono fun _ h _ => h
      · exact Eventually.of_forall fun _ h => (hj h).elim
  have hC := (CAt_tendsto odd).eventually (eventually_lt_nhds (by norm_num : (-1 : ℝ) < 1))
  filter_upwards [parity_modulus_eventually_gt odd (2 * K), hpos, hC]
    with k hk hp hC i
  have hpj (j : ℤ) (hj : j ∈ S) (hw : 0 < w j) :
      0 ≤ pAt odd t Z k (j : ZMod (qAt odd k)) := by
    rw [pAt_front odd t Z K k hk hj]
    exact (hp j hj hw).le
  obtain ⟨_, h0, h1, hneg⟩ := lattice_front_pos hn hm act
  have h0' : 0 ≤ pAt odd t Z k 0 := by simpa using hpj 0 (by simp [S]) h0
  have h1' : 0 ≤ pAt odd t Z k 1 := by
    simpa using hpj 1 (mem_Icc.mpr ⟨by dsimp [K]; omega, by dsimp [K]; omega⟩) h1
  have hn' : 0 ≤ pAt odd t Z k (-1) := by
    simpa using hpj (-1) (mem_Icc.mpr ⟨by dsimp [K]; omega, by dsimp [K]; omega⟩) hneg
  let antipode : ZMod (qAt odd k) := (↑(qAt odd k / 2) : ℤ)
  have hcert := pAt_certificate odd t Z 0 act.normalizer_pos k hC
  have hc : sample antipode = CAt odd k := hcert.1
  have hA : pAt odd t Z k antipode = 0 := by
    have hd := (hcert.2.1 antipode).2.1
    rw [hc, sub_self, mul_zero, zero_mul, zero_div] at hd
    exact hd
  by_cases hi : 0 ≤ pAt odd t Z k i
  · simp [max_eq_right hi]
  have hz : w i.valMinAbs = 0 := by
    by_contra! hne
    have hin : i.valMinAbs ∈ S := by
      by_contra hh
      exact hne (weight_zero_outside act hh)
    have hp' := hpj _ hin (lt_of_le_of_ne (act.nonneg _) hne.symm)
    rw [ZMod.coe_valMinAbs] at hp'
    exact hi hp'
  have hi0 : i ≠ 0 := fun he => hi (he.symm ▸ h0')
  have hi1 : i ≠ 1 := fun he => hi (he.symm ▸ h1')
  have hin : i ≠ -1 := fun he => hi (he.symm ▸ hn')
  have hiA : i ≠ antipode := fun he => hi (he.symm ▸ hA.ge)
  change i ≠ ((↑(qAt odd k / 2) : ℤ) : ZMod (qAt odd k)) at hiA
  simp only [vAt, adjusted, uAt, Pi.single_eq_of_ne hi0, Pi.single_eq_of_ne hi1,
    Pi.single_eq_of_ne hin, Pi.single_eq_of_ne hiA, hz, sub_zero, add_zero, zero_mul]

private abbrev boundAt (m t Z : ℝ) (k : ℕ) : ℝ :=
  2 * (t - m - beta t (parityOffset odd) (hAt odd k) * (2 * m * sAt odd k)) / Z -
    ∑ i, (max 0 (pAt odd t Z k i)) ^ 2

private theorem boundAt_limit {m t Z : ℝ} {n : ℕ} {w : ℤ → ℝ}
    (act : Activation m n t Z w) :
    Tendsto (fun k => ((t - m) / Z - boundAt odd m t Z k) / sAt odd k) atTop
      (𝓝 (2 / Z * ((∑' j : ℤ, (j : ℝ) ^ 4 * w j) / 3 +
        3 * m / 4 * (t - parityOffset odd ^ 2)))) := by
  have hc := pAt_sq_window_limit odd act
  have hβ := beta_tendsto (mesh_tendsto odd) (mesh_ne odd) t (parityOffset odd)
  have ht := hc.add (hβ.const_mul (4 * m / Z))
  have he :
      2 / Z * ((∑' j : ℤ, (j : ℝ) ^ 4 * w j) / 3 -
        (t - parityOffset odd ^ 2) / 2 * m / 2) +
        (4 * m / Z) * ((t - parityOffset odd ^ 2) / 2) =
      2 / Z * ((∑' j : ℤ, (j : ℝ) ^ 4 * w j) / 3 +
        3 * m / 4 * (t - parityOffset odd ^ 2)) := by ring
  rw [he] at ht
  apply ht.congr'
  refine Eventually.of_forall fun k => ?_
  dsimp only [boundAt]
  set s := sAt odd k
  set P := ∑ i, (max 0 (pAt odd t Z k i)) ^ 2
  have hne : s ≠ 0 := (sAt_pos odd k).ne'
  field_simp [hne, act.normalizer_pos.ne']
  ring

private theorem minimum_between {m t Z : ℝ} {n : ℕ} {w : ℤ → ℝ}
    (hn : 0 < n) (hm : 0 < m) (act : Activation m n t Z w) :
    ∀ᶠ k in atTop, ∀ v ∈ feasible (qAt odd k) (1 - 2 * m * sAt odd k),
      IsMinOn energy (feasible (qAt odd k) (1 - 2 * m * sAt odd k)) v →
      boundAt odd m t Z k ≤ energy v ∧
      energy v ≤ boundAt odd m t Z k +
        ∑ i, (vAt odd m n w k i - max 0 (pAt odd t Z k i)) ^ 2 := by
  obtain ⟨ht, _, _, _⟩ := lattice_front_pos hn hm act
  have hd : parityOffset odd ^ 2 ≤ 1 := by cases odd <;> norm_num [parityOffset]
  have hb := (beta_tendsto (mesh_tendsto odd) (mesh_ne odd) t (parityOffset odd)).eventually
    (eventually_gt_nhds (show 0 < (t - parityOffset odd ^ 2) / 2 by linarith only [ht, hd]))
  have hC := (CAt_tendsto odd).eventually (eventually_lt_nhds (by norm_num : (-1 : ℝ) < 1))
  filter_upwards [hb, hC, vAt_feasible odd hn hm act, primal_complementarity odd hn hm act]
    with k hβ hC hv₀ hzero v hv hmin
  let s := sAt odd k
  let β := beta t (parityOffset odd) (hAt odd k)
  let a := 1 - 2 * m * s
  let B := boundAt odd m t Z k
  let p := pAt odd t Z k
  let v₀ := vAt odd m n w k
  have hs : s ≠ 0 := (sAt_pos odd k).ne'
  have hB : 2 * (t - (s⁻¹ / 2 + β) * (1 - a)) / Z - ∑ i, (max 0 (p i)) ^ 2 = B := by
    dsimp only [B, boundAt, a]
    field_simp [hs]
    ring
  have hcert := (pAt_certificate odd t Z a act.normalizer_pos k hC).2.2
  have hcert₁ := hcert v hv.2.1
  have hcert₂ := hcert v₀ hv₀.1.2.1
  change energy v = (2 * (t - (s⁻¹ / 2 + β) * (1 - a)) / Z - _) + _ + _ + _ + _ at hcert₁
  change energy v₀ = (2 * (t - (s⁻¹ / 2 + β) * (1 - a)) / Z - _) + _ + _ + _ + _ at hcert₂
  rw [hB] at hcert₁ hcert₂
  refine ⟨?_, (hmin hv₀.1).trans_eq ?_⟩
  · have hd : 0 ≤ ∑ i, (v i - max 0 (p i)) ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
    have hj : 0 ≤ ∑ i, v i * (max 0 (p i) - p i) :=
      sum_nonneg fun i _ => mul_nonneg (hv.1 i) (sub_nonneg.mpr (le_max_right _ _))
    have h1 := mul_nonneg
      (div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hβ.le) act.normalizer_pos.le)
      (sub_nonneg.mpr hv.2.2.1)
    have h2 := mul_nonneg (div_nonneg (inv_nonneg.mpr (sAt_pos odd k).le) act.normalizer_pos.le)
      (sub_nonneg.mpr hv.2.2.2)
    linarith only [hcert₁, hd, hj, h1, h2]
  · have he : (∑ i, v₀ i * (max 0 (p i) - p i)) = 0 :=
      sum_eq_zero fun i _ => hzero i
    rw [hv₀.2.1, hv₀.2.2, he, sub_self, mul_zero, mul_zero, mul_zero, add_zero, add_zero,
      add_zero] at hcert₂
    exact hcert₂

private theorem actual_threshold (lam : ℝ) (k : ℕ) :
    2 * (lam / (8 * Real.pi ^ 2)) * sAt odd k = lam / (qAt odd k : ℝ) ^ 2 := by
  have hq : (qAt odd k : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne (qAt odd k))
  unfold sAt hAt mesh
  field_simp [hq, Real.pi_ne_zero]
  ring

end ParityLimits

/-- On each parity the scaled gap from the lattice minimum has its exact limit
for every positive budget, including the endpoints of the activation intervals. -/
theorem cyclic_parity_correction (lam : ℝ) (hlam : 0 < lam) :
    let factor := fun Z : ℝ => 2 / Z
    let m := lam / (8 * Real.pi ^ 2)
    ∃ (n : ℕ) (t Z : ℝ) (w : ℤ → ℝ), 0 < n ∧
      ((n : ℝ) ^ 2 - 1) / 5 ≤ m ∧ m < (n : ℝ) * (n + 2) / 5 ∧
      Activation m n t Z w ∧
      ∀ odd : Bool, ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop,
        let q := parityModulus odd k
        let a := 1 - lam / (q : ℝ) ^ 2
        let d := parityOffset odd
        let L := ∑' j : ℤ, w j ^ 2
        let m₄ := ∑' j : ℤ, (j : ℝ) ^ 4 * w j
        let coefficient := factor Z * ((t - d ^ 2) * (3 * lam / 8) + (4 * Real.pi ^ 2 / 3) * m₄)
        (∃ v ∈ feasible q a, IsMinOn energy (feasible q a) v) ∧
        ∀ v ∈ feasible q a, IsMinOn energy (feasible q a) v →
          |(q : ℝ) ^ 2 * (L - energy v) - coefficient| < ε := by
  dsimp only
  let m := lam / (8 * Real.pi ^ 2)
  have hm : 0 < m := div_pos hlam (by positivity)
  obtain ⟨⟨n, t, Z, w⟩, ⟨hn, hinterval, act⟩, _⟩ :=
    (exists_lattice_square_moment_minimizer m).mp hm.le
  refine ⟨n, t, Z, w, hn, hinterval.1, hinterval.2, act, ?_⟩
  intro odd ε hε
  let m₄ := ∑' j : ℤ, (j : ℝ) ^ 4 * w j
  let c := 2 / Z * ((t - parityOffset odd ^ 2) * (3 * lam / 8) + (4 * Real.pi ^ 2 / 3) * m₄)
  let scale := (2 * Real.pi) ^ 2
  have hs : 0 < scale := by dsimp [scale]; positivity
  have hA := boundAt_limit odd act
  have hD := primal_distance odd act
  have hlim₁ : Tendsto (fun k =>
      scale * (((t - m) / Z - boundAt odd m t Z k) / sAt odd k)) atTop (𝓝 c) := by
    have h := hA.const_mul scale
    convert h using 1
    congr 1
    dsimp only [scale, c, m]
    field_simp [Real.pi_ne_zero]
    ring
  have hlim₂ : Tendsto (fun k =>
      scale * (((t - m) / Z - boundAt odd m t Z k) / sAt odd k -
        (∑ i, (vAt odd m n w k i - max 0 (pAt odd t Z k i)) ^ 2) / sAt odd k))
      atTop (𝓝 c) := by
    have hd := hD.const_mul scale
    simp only [mul_zero] at hd
    simpa only [sub_zero, mul_sub] using hlim₁.sub hd
  have hle := hlim₁.eventually (eventually_lt_nhds (show c < c + ε by linarith only [hε]))
  have hge := hlim₂.eventually (eventually_gt_nhds (show c - ε < c by linarith only [hε]))
  filter_upwards [minimum_between odd hn hm act, hle, hge, parity_modulus_eventually_gt odd (2*n)]
    with k hb hle hge hq
  have hfit : 2 * latticeSupportRadius n m < qAt odd k := by
    change 2 * n < qAt odd k at hq
    unfold latticeSupportRadius
    split <;> omega
  obtain ⟨_, _, _, _, _, v₀, hv₀, hmin₀, _, _, _⟩ :=
    cyclic_to_lattice_comparison (qAt odd k) n hn lam hfit hinterval.1 hinterval.2.le
  refine ⟨⟨v₀, hv₀, hmin₀⟩, ?_⟩
  intro v hv hmin
  rw [← actual_threshold odd lam k] at hv hmin
  obtain ⟨hlo, hhi⟩ := hb v hv hmin
  rw [(lattice_energy_window act).2]
  change |(qAt odd k : ℝ) ^ 2 * ((t - m) / Z - energy v) - c| < ε
  have hscale : (qAt odd k : ℝ) ^ 2 = scale / sAt odd k := by
    have hqn : (qAt odd k : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne (qAt odd k))
    unfold scale sAt hAt mesh
    field_simp [hqn, Real.pi_ne_zero]
  have hupper := mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right (sub_le_sub_left hlo ((t - m) / Z)) (sAt_pos odd k).le) hs.le
  have hlower := mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right (sub_le_sub_left hhi ((t - m) / Z)) (sAt_pos odd k).le) hs.le
  rw [hscale, abs_sub_lt_iff]
  constructor
  · have hc : scale / sAt odd k * ((t - m) / Z - energy v) ≤
        scale * (((t - m) / Z - boundAt odd m t Z k) / sAt odd k) := by
      simpa only [div_mul_eq_mul_div, mul_div_assoc] using hupper
    linarith only [hc, hle]
  · have hc : scale * (((t - m) / Z - boundAt odd m t Z k) / sAt odd k -
          (∑ i, (vAt odd m n w k i - max 0 (pAt odd t Z k i)) ^ 2) / sAt odd k) ≤
        scale / sAt odd k * ((t - m) / Z - energy v) := by
      convert hlower using 1 <;> ring
    linarith only [hge, hc]

end D5.S3.Fourier.Asymptotics.CyclicParityLimit
