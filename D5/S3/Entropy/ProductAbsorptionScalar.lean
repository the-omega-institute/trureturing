/- GID: D5/S3/Entropy/ProductAbsorptionScalar
   generality: G
   mirror-B: D5/B/S3/Entropy/ProductAbsorptionScalar
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The complete closed-domain binary-entropy scalar inequality for product absorption. -/

import D5.S3.Entropy.ProductAbsorptionLogMoment

noncomputable section
namespace D5.S3.Entropy.ProductAbsorptionScalar
open Set Filter MeasureTheory
open scoped Topology
open D5.S3.Entropy.ProductAbsorptionLogKernel
open D5.S3.Entropy.ProductAbsorptionLogIntegral
open D5.S3.Entropy.ProductAbsorptionLogMoment
open D5.S3.Entropy.BinaryEntropyLogIntegral

private def entropyWeight (c s : ℝ) : ℝ := (Real.sqrt (1 + c * s))⁻¹

private lemma weight_data {c s : ℝ} (hc : 0 ≤ c) (hs : 0 < s) :
    0 < entropyWeight c s ∧ entropyWeight c s ≤ 1 := by
  have harg : 0 ≤ 1 + c * s := by positivity
  have hsq := Real.sq_sqrt harg
  have hroot := Real.sqrt_nonneg (1 + c * s)
  have hge : 1 ≤ Real.sqrt (1 + c * s) := by nlinarith [mul_nonneg hc hs.le]
  dsimp [entropyWeight]
  exact ⟨inv_pos.mpr (by linarith), (inv_le_one₀ (by linarith)).mpr hge⟩

private lemma weight_antitone {c : ℝ} (hc : 0 ≤ c) :
    AntitoneOn (entropyWeight c) (Ioi 0) := by
  intro s hs t ht hst
  dsimp [entropyWeight]
  have hpos : 0 < Real.sqrt (1 + c * s) := Real.sqrt_pos.mpr (by positivity)
  apply (inv_le_inv₀ (Real.sqrt_pos.mpr (by positivity : 0 < 1 + c * t)) hpos).mpr
  exact Real.sqrt_le_sqrt (by nlinarith)

private lemma weighted_kernel_integral_nonneg {u v c : ℝ}
    (hu : u ∈ Icc (0 : ℝ) 1) (hv : v ∈ Icc (0 : ℝ) 1) (hc : 0 ≤ c) :
    IntegrableOn (fun s => productLogKernel u v s / Real.sqrt (1 + c * s)) (Ioi 0) ∧
      0 ≤ ∫ s in Ioi (0 : ℝ), productLogKernel u v s / Real.sqrt (1 + c * s) := by
  obtain ⟨hi, he⟩ := product_log_kernel_integrable_integral hu hv
  have hm : 0 ≤ ∫ s in Ioi (0 : ℝ), productLogKernel u v s := by
    rw [he]
    exact product_log_moment_nonneg hu hv
  have hw : AEStronglyMeasurable (entropyWeight c) (volume.restrict (Ioi 0)) := by
    have hmeas : Measurable (entropyWeight c) := by unfold entropyWeight; fun_prop
    exact hmeas.aestronglyMeasurable
  have hb : ∀ᵐ s ∂volume.restrict (Ioi (0 : ℝ)), ‖entropyWeight c s‖ ≤ 1 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    rw [Real.norm_eq_abs, abs_of_pos (weight_data hc hs).1]
    exact (weight_data hc hs).2
  have hwi : IntegrableOn (fun s => productLogKernel u v s * entropyWeight c s) (Ioi 0) :=
    hi.mul_bdd hw hb
  refine ⟨by simpa only [entropyWeight, div_eq_mul_inv] using hwi, ?_⟩
  change 0 ≤ ∫ s in Ioi (0 : ℝ), productLogKernel u v s * entropyWeight c s
  rcases product_log_kernel_single_crossing hu hv with h | ⟨r, hr, heq, hp, hn⟩
  · apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact mul_nonneg (h s hs) (weight_data hc hs).1.le
  · have hpoint : ∀ s ∈ Ioi (0 : ℝ),
        productLogKernel u v s * entropyWeight c r ≤
          productLogKernel u v s * entropyWeight c s := by
      intro s hs
      rcases lt_trichotomy s r with hsr | hsr | hrs
      · exact mul_le_mul_of_nonneg_left (weight_antitone hc hs hr hsr.le)
          (hp s ⟨hs, hsr⟩).le
      · rw [hsr]
      · exact mul_le_mul_of_nonpos_left (weight_antitone hc hr hs hrs.le)
          (hn s hrs).le
    have hi' := hi.mul_const (entropyWeight c r)
    have hcmp := integral_mono_ae hi' hwi (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact hpoint s hs)
    rw [integral_mul_const] at hcmp
    exact (mul_nonneg hm (weight_data hc hr).1.le).trans hcmp

private lemma parameter_bounds {u v : ℝ} (hu : u ∈ Icc (0 : ℝ) 1)
    (hv : v ∈ Icc (0 : ℝ) 1) :
    let A := u + v
    let B := u * v
    let q := Real.sqrt (B * (1 - A + B))
    A - B ∈ Icc (0 : ℝ) 1 ∧ A - 2 * B + 2 * q ∈ Icc (0 : ℝ) 1 ∧
      A - 2 * B - 2 * q ∈ Icc (0 : ℝ) 1 := by
  let A := u + v
  let B := u * v
  let q := Real.sqrt (B * (1 - A + B))
  have hB : 0 ≤ B := mul_nonneg hu.1 hv.1
  have hcomp : 0 ≤ 1 - A + B := by
    have h := mul_nonneg (sub_nonneg.mpr hu.2) (sub_nonneg.mpr hv.2)
    dsimp [A, B]
    nlinarith
  have hmiddle : 0 ≤ A - 2 * B := by
    have h1 := mul_nonneg hu.1 (sub_nonneg.mpr hv.2)
    have h2 := mul_nonneg hv.1 (sub_nonneg.mpr hu.2)
    dsimp [A, B]
    nlinarith
  have hq : 0 ≤ q := Real.sqrt_nonneg _
  have hq2 : q ^ 2 = B * (1 - A + B) := Real.sq_sqrt (mul_nonneg hB hcomp)
  have hlow : (A - 2 * B) ^ 2 - 4 * q ^ 2 = (u - v) ^ 2 := by
    rw [hq2]
    dsimp [A, B]
    ring
  have hhigh : (1 - A + 2 * B) ^ 2 - 4 * q ^ 2 = (1 - A) ^ 2 := by
    rw [hq2]
    ring
  change A - B ∈ Icc (0 : ℝ) 1 ∧ A - 2 * B + 2 * q ∈ Icc (0 : ℝ) 1 ∧
    A - 2 * B - 2 * q ∈ Icc (0 : ℝ) 1
  exact ⟨⟨by linarith, by linarith⟩,
    ⟨by linarith, by nlinarith [sq_nonneg (1 - A)]⟩,
    ⟨by nlinarith [sq_nonneg (u - v)], by nlinarith [sq_nonneg (1 - A)]⟩⟩

private def rootEntropy (x : ℝ) : ℝ := Real.binEntropy ((1 + Real.sqrt (1 - x)) / 2)

private lemma scaled_entropy_integral {c x : ℝ} (hc : 0 < c) (hcx : c * x ∈ Icc (0 : ℝ) 1) :
    IntegrableOn (fun s : ℝ => Real.log (1 + x / s) / Real.sqrt (1 + c * s)) (Ioi 0) ∧
      rootEntropy (c * x) = (c / 4) *
        ∫ s in Ioi (0 : ℝ), Real.log (1 + x / s) / Real.sqrt (1 + c * s) := by
  let g := fun s : ℝ => Real.log (1 + (c * x) / s) / Real.sqrt (1 + s)
  obtain ⟨hi, he⟩ := binEntropy_sqrt_log_integral hcx
  have hic : IntegrableOn (fun s => g (c * s)) (Ioi 0) :=
    (integrableOn_Ioi_comp_mul_left_iff g 0 hc).mpr (by simpa only [mul_zero] using hi)
  have hcomp : (fun s => g (c * s)) =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (fun s => Real.log (1 + x / s) / Real.sqrt (1 + c * s)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    dsimp [g]
    congr 3
    field_simp [hc.ne', hs.ne']
  have hsub := integral_comp_mul_left_Ioi' g 0 hc
  simp only [mul_zero, smul_eq_mul] at hsub
  rw [integral_congr_ae hcomp] at hsub
  refine ⟨hic.congr hcomp, ?_⟩
  change rootEntropy (c * x) = (1 / 4 : ℝ) * ∫ s in Ioi (0 : ℝ), g s at he
  change rootEntropy (c * x) = _
  rw [he, ← hsub]
  ring

private lemma root_entropy_absorption {u v c : ℝ} (hu : u ∈ Icc (0 : ℝ) 1)
    (hv : v ∈ Icc (0 : ℝ) 1) (hc : c ∈ Icc (0 : ℝ) 1) :
    let A := u + v
    let B := u * v
    let L := A - B
    let q := Real.sqrt (B * (1 - A + B))
    rootEntropy (c * u) + rootEntropy (c * v) - 2 * rootEntropy (c * L) +
      (rootEntropy (c * (A - 2 * B + 2 * q)) +
        rootEntropy (c * (A - 2 * B - 2 * q))) / 2 ≥ 0 := by
  by_cases hc0 : c = 0
  · subst c
    simp [rootEntropy]
  have hcp : 0 < c := lt_of_le_of_ne hc.1 (Ne.symm hc0)
  let A := u + v
  let B := u * v
  let L := A - B
  let q := Real.sqrt (B * (1 - A + B))
  let mp := A - 2 * B + 2 * q
  let mm := A - 2 * B - 2 * q
  obtain ⟨hL, hp, hm⟩ := parameter_bounds hu hv
  have hscale {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : c * x ∈ Icc (0 : ℝ) 1 :=
    ⟨mul_nonneg hc.1 hx.1, by nlinarith [mul_nonneg (sub_nonneg.mpr hc.2) hx.1]⟩
  obtain ⟨hiu, heu⟩ := scaled_entropy_integral hcp (hscale hu)
  obtain ⟨hiv, hev⟩ := scaled_entropy_integral hcp (hscale hv)
  obtain ⟨hiL, heL⟩ := scaled_entropy_integral hcp (hscale hL)
  obtain ⟨hip, hep⟩ := scaled_entropy_integral hcp (hscale hp)
  obtain ⟨him, hem⟩ := scaled_entropy_integral hcp (hscale hm)
  have hlinear := (((hiu.add hiv).sub (hiL.const_mul 2)).add ((hip.add him).div_const 2))
  have heI : (∫ s in Ioi (0 : ℝ), productLogKernel u v s / Real.sqrt (1 + c * s)) =
      (∫ s in Ioi (0 : ℝ), Real.log (1 + u / s) / Real.sqrt (1 + c * s)) +
      (∫ s in Ioi (0 : ℝ), Real.log (1 + v / s) / Real.sqrt (1 + c * s)) -
      2 * (∫ s in Ioi (0 : ℝ), Real.log (1 + L / s) / Real.sqrt (1 + c * s)) +
      ((∫ s in Ioi (0 : ℝ), Real.log (1 + mp / s) / Real.sqrt (1 + c * s)) +
        (∫ s in Ioi (0 : ℝ), Real.log (1 + mm / s) / Real.sqrt (1 + c * s))) / 2 := by
    have hefun : (fun s => productLogKernel u v s / Real.sqrt (1 + c * s)) =
        (fun s => Real.log (1 + u / s) / Real.sqrt (1 + c * s) +
          Real.log (1 + v / s) / Real.sqrt (1 + c * s) -
          2 * (Real.log (1 + L / s) / Real.sqrt (1 + c * s)) +
          (Real.log (1 + mp / s) / Real.sqrt (1 + c * s) +
            Real.log (1 + mm / s) / Real.sqrt (1 + c * s)) / 2) := by
      funext s
      dsimp [productLogKernel, L, mp, mm, q, A, B]
      ring
    rw [hefun, integral_add ((hiu.add hiv).sub (hiL.const_mul 2)) ((hip.add him).div_const 2),
      integral_sub (hiu.add hiv) (hiL.const_mul 2), integral_add hiu hiv,
      integral_const_mul, integral_div, integral_add hip him]
  have hnonneg := (weighted_kernel_integral_nonneg hu hv hc.1).2
  rw [heI] at hnonneg
  change 0 ≤ rootEntropy (c * u) + rootEntropy (c * v) - 2 * rootEntropy (c * L) +
    (rootEntropy (c * mp) + rootEntropy (c * mm)) / 2
  rw [heu, hev, heL, hep, hem]
  convert mul_nonneg (div_nonneg hc.1 (by norm_num : (0 : ℝ) ≤ 4)) hnonneg using 1 <;> ring

/-- The actual binary entropy at the radius of a binary phase-noise qubit. -/
def phaseNoiseEntropy (b t : ℝ) : ℝ :=
  Real.binEntropy ((1 + Real.sqrt (b ^ 2 + (1 - b ^ 2) * t ^ 2)) / 2)

private lemma root_entropy_phase (b t : ℝ) :
    rootEntropy ((1 - b ^ 2) * (1 - t ^ 2)) = phaseNoiseEntropy b t := by
  unfold rootEntropy phaseNoiseEntropy
  rw [show 1 - (1 - b ^ 2) * (1 - t ^ 2) = b ^ 2 + (1 - b ^ 2) * t ^ 2 by ring]

/-- The complete scalar product-absorption inequality for actual natural-log
binary entropy. All signs, zero bias, unit bias, zero roots and coincident roots
are included. This is a scalar theorem; it makes no claim about entangled or
mixed quantum states. -/
theorem product_binary_entropy_absorption {z w b : ℝ}
    (hz : z ∈ Icc (-1 : ℝ) 1) (hw : w ∈ Icc (-1 : ℝ) 1)
    (hb : b ∈ Icc (0 : ℝ) 1) :
    let l := z * w
    let T := Real.sqrt ((1 - z ^ 2) * (1 - w ^ 2))
    0 ≤ phaseNoiseEntropy b z + phaseNoiseEntropy b w - 2 * phaseNoiseEntropy b l +
      (phaseNoiseEntropy b (l + T) + phaseNoiseEntropy b (l - T)) / 2 := by
  let u := 1 - z ^ 2
  let v := 1 - w ^ 2
  let c := 1 - b ^ 2
  let A := u + v
  let B := u * v
  let l := z * w
  let T := Real.sqrt (u * v)
  let q := Real.sqrt (B * (1 - A + B))
  have hzs : z ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg (show 0 ≤ 1 + z by linarith [hz.1])
      (show 0 ≤ 1 - z by linarith [hz.2])]
  have hws : w ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg (show 0 ≤ 1 + w by linarith [hw.1])
      (show 0 ≤ 1 - w by linarith [hw.2])]
  have hbs : b ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg hb.1 (sub_nonneg.mpr hb.2)]
  have hu : u ∈ Icc (0 : ℝ) 1 := ⟨by dsimp [u]; linarith, by dsimp [u]; nlinarith⟩
  have hv : v ∈ Icc (0 : ℝ) 1 := ⟨by dsimp [v]; linarith, by dsimp [v]; nlinarith⟩
  have hc : c ∈ Icc (0 : ℝ) 1 := ⟨by dsimp [c]; linarith, by dsimp [c]; nlinarith⟩
  have hT : 0 ≤ T := Real.sqrt_nonneg _
  have hT2 : T ^ 2 = B := Real.sq_sqrt (mul_nonneg hu.1 hv.1)
  have hcomp : 1 - A + B = l ^ 2 := by dsimp [A, B, u, v, l]; ring
  have hq : q = |l| * T := by
    have he : B * (1 - A + B) = (l * T) ^ 2 := by rw [mul_pow, hT2, hcomp]; ring
    dsimp only [q]
    rw [he, Real.sqrt_sq_eq_abs, abs_mul, abs_of_nonneg hT]
  have hL : A - B = 1 - l ^ 2 := by linarith [hcomp]
  have hbase : A - 2 * B = 1 - l ^ 2 - T ^ 2 := by rw [hT2]; linarith [hL]
  have h := root_entropy_absorption hu hv hc
  change 0 ≤ rootEntropy (c * u) + rootEntropy (c * v) - 2 * rootEntropy (c * (A - B)) +
    (rootEntropy (c * (A - 2 * B + 2 * q)) + rootEntropy (c * (A - 2 * B - 2 * q))) / 2 at h
  rw [hL] at h
  have hpair : rootEntropy (c * (A - 2 * B + 2 * q)) +
      rootEntropy (c * (A - 2 * B - 2 * q)) =
      rootEntropy (c * (1 - (l + T) ^ 2)) + rootEntropy (c * (1 - (l - T) ^ 2)) := by
    rw [hbase, hq]
    by_cases hl : 0 ≤ l
    · rw [abs_of_nonneg hl,
        show 1 - l ^ 2 - T ^ 2 + 2 * (l * T) = 1 - (l - T) ^ 2 by ring,
        show 1 - l ^ 2 - T ^ 2 - 2 * (l * T) = 1 - (l + T) ^ 2 by ring]
      exact add_comm _ _
    · rw [abs_of_neg (lt_of_not_ge hl),
        show 1 - l ^ 2 - T ^ 2 + 2 * (-l * T) = 1 - (l + T) ^ 2 by ring,
        show 1 - l ^ 2 - T ^ 2 - 2 * (-l * T) = 1 - (l - T) ^ 2 by ring]
  rw [hpair] at h
  change 0 ≤ rootEntropy ((1 - b ^ 2) * (1 - z ^ 2)) +
    rootEntropy ((1 - b ^ 2) * (1 - w ^ 2)) - 2 * rootEntropy ((1 - b ^ 2) * (1 - l ^ 2)) +
    (rootEntropy ((1 - b ^ 2) * (1 - (l + T) ^ 2)) +
      rootEntropy ((1 - b ^ 2) * (1 - (l - T) ^ 2))) / 2 at h
  simp only [root_entropy_phase] at h
  exact h

#print axioms product_binary_entropy_absorption
end D5.S3.Entropy.ProductAbsorptionScalar
