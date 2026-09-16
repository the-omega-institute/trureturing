/- GID: D5/S3/Observer/Monodromy/GainRobustGaussianDiscrimination
   generality: G
   mirror-B: D5/B/S3/Observer/Monodromy/GainRobustGaussianDiscrimination
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual two-pulse variance families have a sharp gain-uncertainty collision boundary and a reference-assisted calibration-free certificate. -/

import D5.S3.Observer.Monodromy.TwoPulseCovarianceTomography
import Mathlib.Data.Matrix.Notation
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# Calibration uncertainty and reference-assisted Gaussian discrimination

The source acts with the previously defined actual dual pulse matrices. The
covariance family is written in the readout frame (q1,p1,p1+q2,p1+p2).
At c=1 and c=1/5 these are the two distinct physical Gaussian covariance
examples developed in the companion theory. Gaussian existence and the
separable/NPT interpretation are external to this matrix theorem.

The first theorem supplies a single threshold for all gains in a box, exactly
when the endpoint condition holds, and constructs equal-variance gains when
it fails. The second theorem uses four actual experimental variances to remove
unknown positive detector gain and a common additive variance offset. Its
certificate is uniform in those unknown parameters and has an explicit
observed-data error radius. It does not assume independent record errors.

No Gaussian probability measures, finite-shot concentration, or physical
hardware calibration are formalized by this file. Global novelty is not asserted.
-/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Monodromy.GainRobustGaussianDiscrimination

open D5.S3.Observer.Monodromy.TransvectionLieFiltration
open D5.S3.Observer.Monodromy.TwoPulseCovarianceTomography

/-- Actual quadrature pairing in the specified readout frame. -/
def pairing : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 1, 1, 1; -1, 0, 0, 0; -1, 0, 0, 1; -1, 0, -1, 0]

/-- Two physical covariance examples occur at c=1 and c=1/5. Other c here
are merely real symmetric matrices unless physicality is separately checked. -/
def covariance (c : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, 7/10, 0; 0, 1, 1, c; 7/10, 1, 2, c; 0, c, c, 2]

/-- Actual dual control: the corresponding state pulses have reverse order. -/
def controlledDirection (s t : ℝ) : Fin 4 → ℝ :=
  dualPulse pairing 3 t (dualPulse pairing 1 s ![1, 0, 0, 0])

def outputVariance (c s t : ℝ) : ℝ :=
  ∑ i : Fin 4, ∑ j : Fin 4,
    controlledDirection s t i * covariance c i j * controlledDirection s t j

/-- Relative calibration box around the nominal pair (1,1). -/
def GainBox (δ s t : ℝ) : Prop :=
  (1-δ ≤ s ∧ s ≤ 1+δ) ∧ (1-δ ≤ t ∧ t ≤ 1+δ)

/-- Sharp separation of all gains, plus an explicit collision when no uniform
threshold exists. The two hypotheses may have different unknown calibrations. -/
theorem sharp_gain_interval_dichotomy (cLo cHi δ : ℝ)
    (hcLo : 0 ≤ cLo) (hc : cLo < cHi) (hδ : 0 ≤ δ) (hδ1 : δ < 1) :
    ((∃ τ : ℝ, ∀ s t : ℝ, GainBox δ s t →
        outputVariance cLo s t < τ ∧ τ < outputVariance cHi s t) ↔
      (3+2*cLo)*(1+δ)^2 < (3+2*cHi)*(1-δ)^2) ∧
    ((3+2*cHi)*(1-δ)^2 ≤ (3+2*cLo)*(1+δ)^2 →
      ∃ s0 t0 s1 t1 : ℝ, GainBox δ s0 t0 ∧ GainBox δ s1 t1 ∧
        outputVariance cHi s0 t0 = outputVariance cLo s1 t1) := by
  have ray (s t : ℝ) : controlledDirection s t = ![1, s, 0, t] := by
    ext i
    fin_cases i <;>
      norm_num [controlledDirection, dualPulse, increment, pairing,
        Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Matrix.one_apply] <;> ring
  have formula (c s t : ℝ) : outputVariance c s t =
      1+s^2+2*c*s*t+2*t^2 := by
    simp [outputVariance, ray, covariance, Fin.sum_univ_succ]
    <;> ring
  let l := 1-δ
  let u := 1+δ
  let K0 := 3+2*cHi
  let K1 := 3+2*cLo
  have hl : 0 < l := by dsimp [l]; linarith
  have hu : 0 < u := by dsimp [u]; linarith
  have hlu : l ≤ u := by dsimp [l, u]; linarith
  have hk1 : 0 < K1 := by dsimp [K1]; linarith
  have hks : K1 < K0 := by dsimp [K1, K0]; linarith
  have diag (c r : ℝ) : outputVariance c r r = 1+(3+2*c)*r^2 := by
    rw [formula]
    ring
  have bounds (c s t : ℝ) (hc0 : 0 ≤ c) (h : GainBox δ s t) :
      1+(3+2*c)*l^2 ≤ outputVariance c s t ∧
        outputVariance c s t ≤ 1+(3+2*c)*u^2 := by
    change (l ≤ s ∧ s ≤ u) ∧ (l ≤ t ∧ t ≤ u) at h
    have hs0 : 0 ≤ s := le_trans hl.le h.1.1
    have ht0 : 0 ≤ t := le_trans hl.le h.2.1
    have hsl : l^2 ≤ s^2 := by nlinarith
    have htl : l^2 ≤ t^2 := by nlinarith
    have hsu : s^2 ≤ u^2 := by nlinarith
    have htu : t^2 ≤ u^2 := by nlinarith
    have hpL : l*l ≤ s*t := mul_le_mul h.1.1 h.2.1 hl.le hs0
    have hpU : s*t ≤ u*u := mul_le_mul h.1.2 h.2.2 ht0 hu.le
    have hcL := mul_le_mul_of_nonneg_left hpL (by positivity : 0 ≤ 2*c)
    have hcU := mul_le_mul_of_nonneg_left hpU (by positivity : 0 ≤ 2*c)
    rw [formula]
    constructor <;> nlinarith
  have boxL : GainBox δ l l := ⟨⟨le_rfl, hlu⟩, ⟨le_rfl, hlu⟩⟩
  have boxU : GainBox δ u u := ⟨⟨hlu, le_rfl⟩, ⟨hlu, le_rfl⟩⟩
  constructor
  · constructor
    · rintro ⟨τ, hτ⟩
      have hLo := (hτ u u boxU).1
      have hHi := (hτ l l boxL).2
      rw [diag] at hLo hHi
      dsimp [l, u] at hLo hHi
      linarith
    · intro hsep
      let τ := (1+K1*u^2 + (1+K0*l^2))/2
      refine ⟨τ, ?_⟩
      intro s t hbox
      have hLow := (bounds cLo s t hcLo hbox).2
      have hHigh := (bounds cHi s t (le_trans hcLo hc.le) hbox).1
      change K1*u^2 < K0*l^2 at hsep
      change outputVariance cLo s t < τ ∧ τ < outputVariance cHi s t
      dsimp [τ, K0, K1] at *
      constructor <;> linarith
  · intro hcollision
    change K0*l^2 ≤ K1*u^2 at hcollision
    let r := Real.sqrt (K0/K1)
    have hratio : 1 < K0/K1 := (one_lt_div hk1).mpr hks
    have hr0 : 0 ≤ r := Real.sqrt_nonneg _
    have hr2 : r^2 = K0/K1 := Real.sq_sqrt (le_trans (by norm_num) hratio.le)
    have hr1 : 1 ≤ r := by nlinarith
    have hscale : K1*r^2 = K0 := by
      rw [hr2]
      field_simp [ne_of_gt hk1]
    have hmatch : K1*(r*l)^2 = K0*l^2 := by
      calc
        K1*(r*l)^2 = (K1*r^2)*l^2 := by ring
        _ = K0*l^2 := by rw [hscale]
    have hrl : l ≤ r*l := by nlinarith
    have hru : r*l ≤ u := by
      by_contra h
      have hgt : u < r*l := lt_of_not_ge h
      have hsquare : u^2 < (r*l)^2 := by nlinarith
      have hm := mul_lt_mul_of_pos_left hsquare hk1
      linarith
    refine ⟨l, l, r*l, r*l, boxL,
      ⟨⟨hrl, hru⟩, ⟨hrl, hru⟩⟩, ?_⟩
    rw [diag, diag]
    change 1+K0*l^2 = 1+K1*(r*l)^2
    rw [hmatch]

/-- Empty, first pulse, second pulse, and both pulses. The positive detector
variance gain and additive variance offset are common to all four settings. -/
def records (c gain offset s t : ℝ) : Fin 4 → ℝ :=
  ![offset+gain*outputVariance c 0 0,
    offset+gain*outputVariance c s 0,
    offset+gain*outputVariance c 0 t,
    offset+gain*outputVariance c s t]

/-- A gain- and offset-blind polynomial decision statistic. -/
def referenceScore (z : Fin 4 → ℝ) : ℝ :=
  (z 3-z 1-z 2+z 0)^2 - (z 1-z 0)*(z 2-z 0)

/-- A computable radius using measured data and a certified per-record error. -/
def scoreRadius (z : Fin 4 → ℝ) (ε : ℝ) : ℝ :=
  (8*|z 3-z 1-z 2+z 0| + 2*|z 1-z 0| + 2*|z 2-z 0|)*ε + 20*ε^2

/-- The same measured-data certificate distinguishes the two inputs for every
unknown positive detector gain, common offset, and nonzero pulse gains.
No calibration-dependent decoder is selected inside the conclusion. -/
theorem certified_reference_discrimination
    (c gain offset s t ε : ℝ) (hc : c = 1 ∨ c = 1/5)
    (hg : 0 < gain) (hs : s ≠ 0) (ht : t ≠ 0) (hε : 0 ≤ ε)
    (z : Fin 4 → ℝ)
    (hz : ∀ k, |z k-records c gain offset s t k| ≤ ε)
    (hcert : scoreRadius z ε < |referenceScore z|) :
    (c = 1 ∧ 0 < referenceScore z) ∨
      (c = 1/5 ∧ referenceScore z < 0) := by
  have ray (s t : ℝ) : controlledDirection s t = ![1, s, 0, t] := by
    ext i
    fin_cases i <;>
      norm_num [controlledDirection, dualPulse, increment, pairing,
        Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Matrix.one_apply] <;> ring
  have formula (c s t : ℝ) : outputVariance c s t =
      1+s^2+2*c*s*t+2*t^2 := by
    simp [outputVariance, ray, covariance, Fin.sum_univ_succ]
    <;> ring
  let r := records c gain offset s t
  have ideal : referenceScore r = 2*(2*c^2-1)*(gain*s*t)^2 := by
    simp [r, records, referenceScore, formula]
    <;> ring
  have hp : 0 < (gain*s*t)^2 :=
    sq_pos_of_ne_zero (mul_ne_zero (mul_ne_zero (ne_of_gt hg) hs) ht)
  have product_error (x y u v η : ℝ) (hη : 0 ≤ η)
      (hux : |u-x| ≤ η) (hvy : |v-y| ≤ η) :
      |u*v-x*y| ≤ (|x|+|y|)*η+η^2 := by
    have he : u*v-x*y = x*(v-y)+y*(u-x)+(u-x)*(v-y) := by ring
    have h1 := abs_add (x*(v-y)+y*(u-x)) ((u-x)*(v-y))
    have h2 := abs_add (x*(v-y)) (y*(u-x))
    have hx := mul_le_mul_of_nonneg_left hvy (abs_nonneg x)
    have hy := mul_le_mul_of_nonneg_left hux (abs_nonneg y)
    have hxy := mul_le_mul hux hvy (abs_nonneg (v-y)) hη
    rw [he]
    simp only [abs_mul] at h1 h2
    nlinarith
  let az := z 1-z 0
  let bz := z 2-z 0
  let dz := z 3-z 1-z 2+z 0
  let ar := r 1-r 0
  let br := r 2-r 0
  let dr := r 3-r 1-r 2+r 0
  have noise (k : Fin 4) : |r k-z k| ≤ ε := by
    simpa [r, abs_sub_comm] using hz k
  have subbound (x y : ℝ) : |x-y| ≤ |x|+|y| := by
    simpa using abs_sub_le x 0 y
  have ha : |ar-az| ≤ 2*ε := by
    have he : ar-az = (r 1-z 1)-(r 0-z 0) := by dsimp [ar, az]; ring
    rw [he]
    linarith [subbound (r 1-z 1) (r 0-z 0), noise 1, noise 0]
  have hb : |br-bz| ≤ 2*ε := by
    have he : br-bz = (r 2-z 2)-(r 0-z 0) := by dsimp [br, bz]; ring
    rw [he]
    linarith [subbound (r 2-z 2) (r 0-z 0), noise 2, noise 0]
  have hd : |dr-dz| ≤ 4*ε := by
    have he : dr-dz = ((r 3-z 3)-(r 1-z 1))-
        (r 2-z 2)+(r 0-z 0) := by dsimp [dr, dz]; ring
    rw [he]
    have h1 := subbound (r 3-z 3) (r 1-z 1)
    have h2 := subbound ((r 3-z 3)-(r 1-z 1)) (r 2-z 2)
    have h3 := abs_add (((r 3-z 3)-(r 1-z 1))-(r 2-z 2)) (r 0-z 0)
    linarith [noise 0, noise 1, noise 2, noise 3]
  have hdprod := product_error dz dz dr dr (4*ε) (by positivity) hd hd
  have habprod := product_error az bz ar br (2*ε) (by positivity) ha hb
  have hdist : |referenceScore r-referenceScore z| ≤ scoreRadius z ε := by
    have he : referenceScore r-referenceScore z =
        (dr*dr-dz*dz)-(ar*br-az*bz) := by
      dsimp [referenceScore, dr, dz, ar, az, br, bz]
      ring
    rw [he]
    have htriangle := subbound (dr*dr-dz*dz) (ar*br-az*bz)
    change |(dr*dr-dz*dz)-(ar*br-az*bz)| ≤
      (8*|dz|+2*|az|+2*|bz|)*ε+20*ε^2
    nlinarith
  rcases hc with hc | hc
  · left
    refine ⟨hc, ?_⟩
    have hpos : 0 < referenceScore r := by rw [ideal, hc]; nlinarith
    by_contra h
    have hn : referenceScore z ≤ 0 := le_of_not_gt h
    rw [abs_of_nonpos hn] at hcert
    have hupper := (abs_le.mp hdist).2
    linarith
  · right
    refine ⟨hc, ?_⟩
    have hneg : referenceScore r < 0 := by rw [ideal, hc]; nlinarith
    by_contra h
    have hn : 0 ≤ referenceScore z := le_of_not_gt h
    rw [abs_of_nonneg hn] at hcert
    have hlower := (abs_le.mp hdist).1
    linarith

#print axioms sharp_gain_interval_dichotomy
#print axioms certified_reference_discrimination

end D5.S3.Observer.Monodromy.GainRobustGaussianDiscrimination
