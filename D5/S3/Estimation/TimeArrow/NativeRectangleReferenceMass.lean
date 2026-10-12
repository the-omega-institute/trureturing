/- GID: D5/S3/Estimation/TimeArrow/NativeRectangleReferenceMass
   generality: G
   mirror-B: D5/B/S3/Estimation/TimeArrow/NativeRectangleReferenceMass
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original floored signal-cell mass has explicit reciprocal-scale bounds. -/

import D5.S3.Estimation.TimeArrow.NativeReferenceVarianceBounds
import D5.S3.Estimation.TimeArrow.NativeRectangleReferenceRatios

open scoped BigOperators
open Finset
open D5.S3.Estimation.SequentialDecisionRisk.FiniteSupportSelectionBayes
open D5.S3.Estimation.TimeArrow.NativeRowMomentTransfer
open D5.S3.Estimation.TimeArrow.NativeReferenceVarianceBounds
open D5.S3.Estimation.TimeArrow.NativeRectangleReferenceRatios

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Estimation.TimeArrow.NativeRectangleReferenceMass
noncomputable section

private theorem poisson_atom_upper (mu : ℝ) (hmu : 0 < mu) {n : ℕ} (hn : 0 < n) :
    Real.exp (-mu) * mu ^ n / n.factorial ≤ 1 / Real.sqrt n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hf : (0 : ℝ) < n.factorial := by positivity
  have hs := (D5.S3.Estimation.TimeArrow.NativeCalibratedArithmeticBridge.log_factorial_envelopes hn).1
  have hl := Real.log_le_sub_one_of_pos (div_pos hmu hnR)
  rw [Real.log_div hmu.ne' hnR.ne'] at hl
  have hh := mul_le_mul_of_nonneg_left hl hnR.le
  have he : (n : ℝ) * (mu / n - 1) = mu - n := by field_simp
  rw [he] at hh
  have hp : 0 < Real.exp (-mu) * mu ^ n / n.factorial := by positivity
  have hlog : Real.log (Real.exp (-mu) * mu ^ n / n.factorial) ≤ -Real.log n / 2 := by
    rw [Real.log_div (by positivity) hf.ne',
      Real.log_mul (Real.exp_pos _).ne' (pow_pos hmu n).ne', Real.log_exp, Real.log_pow]
    linarith only [hs,hh]
  have hx := Real.exp_le_exp.mpr hlog
  rw [Real.exp_log hp] at hx
  calc
    _ ≤ Real.exp (-Real.log n / 2) := hx
    _ = 1 / Real.sqrt n := by
      rw [show -Real.log (n : ℝ) / 2 = -(Real.log (n : ℝ) / 2) by ring,
        Real.exp_neg, ← Real.log_sqrt hnR.le, Real.exp_log (Real.sqrt_pos.mpr hnR)]
      simp only [one_div]

/-- Both bounds refer to k=floor(a lambda), l=lambda-k in the original
signal reference law. In particular q times this mass has scale q/lambda. -/
theorem floored_signal_reference_mass {M q L : ℕ} (S : Support M q)
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (hL : 1 ≤ L)
    (i : Fin M) (hi : i ∈ S.val)
    (hplus : 15 ≤ ((1 + r) / 2) * (L : ℝ))
    (hminus : 30 ≤ ((1 - r) / 2) * (L : ℝ)) :
    let a := (1 + r) / 2
    let b := (1 - r) / 2
    let k := ⌊a * (L : ℝ)⌋₊
    let l := L-k
    Real.exp (-1/a-1) * Real.exp (-1/b-1) /
        (Real.sqrt ((3/2)*a) * Real.sqrt ((3/2)*b) * L) ≤ rowReference S r L i (k,l) ∧
      rowReference S r L i (k,l) ≤ 2 / (Real.sqrt (a*b) * L) := by
  classical
  let a := (1 + r) / 2
  let b := (1 - r) / 2
  let k := ⌊a * (L : ℝ)⌋₊
  let l := L-k
  have ha : 0 < a := by dsimp [a]; linarith only [hr]
  have hb : 0 < b := by dsimp [b]; linarith only [hr1]
  have hLR : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hab : a+b=1 := by dsimp [a,b]; ring
  change 15 ≤ a*(L : ℝ) at hplus
  change 30 ≤ b*(L : ℝ) at hminus
  have hround := original_count_rounding r L hr hr1 hL hplus hminus
  dsimp only at hround
  have hkL : k ≤ L := hround.1
  have hk : 0 < k := hround.2.1
  have hl : 0 < l := hround.2.2.1
  have hklo : (k : ℝ) ≤ a*L := Nat.floor_le (by positivity)
  have hkhi : a*(L : ℝ) < k+1 := Nat.lt_floor_add_one _
  have hlr : (l : ℝ) = (L : ℝ)-k := Nat.cast_sub hkL
  have hll : b*(L : ℝ) ≤ l := by rw [hlr]; nlinarith only [hklo,hab]
  have hlu : (l : ℝ) ≤ b*L+1 := by rw [hlr]; nlinarith only [hkhi,hab]
  have hs : (1 : ℝ) ≤ Real.sqrt L := by
    exact Real.one_le_sqrt.mpr hLR
  dsimp only
  constructor
  · have hm := signal_rectangle_mass_lower S r 1 hr hr1 (by norm_num) hL i hi
      {(k,l)} (by
        intro c hc
        simp only [mem_singleton] at hc
        subst c
        refine ⟨hk,hl,?_,?_,?_,?_⟩
        · change |(k : ℝ)-a*L| ≤ 1*Real.sqrt L
          rw [abs_le]
          constructor <;> nlinarith only [hklo,hkhi,hs]
        · change |(l : ℝ)-b*L| ≤ 1*Real.sqrt L
          rw [abs_le]
          constructor <;> nlinarith only [hll,hlu,hs]
        · change (k : ℝ) ≤ 3/2*a*L
          nlinarith only [hklo,hplus]
        · change (l : ℝ) ≤ 3/2*b*L
          nlinarith only [hlu,hminus])
    simpa only [card_singleton,Nat.cast_one,one_mul,sum_singleton,one_pow] using hm
  · have hp := poisson_atom_upper (a*L) (by positivity) hk
    have hm := poisson_atom_upper (b*L) (by positivity) hl
    have hpair := mul_le_mul hp hm (by positivity) (by positivity)
    have hkp : a*(L : ℝ)/2 ≤ k := by nlinarith only [hkhi,hplus]
    have hlp : b*(L : ℝ)/2 ≤ l := by linarith only [hll,show 0 ≤ b*(L : ℝ) by positivity]
    have hden : Real.sqrt (a*b)*(L : ℝ)/2 ≤ Real.sqrt k*Real.sqrt l := by
      have hh := mul_le_mul (Real.sqrt_le_sqrt hkp) (Real.sqrt_le_sqrt hlp)
        (by positivity) (by positivity)
      have he : Real.sqrt (a*(L : ℝ)/2) * Real.sqrt (b*(L : ℝ)/2) =
          Real.sqrt (a*b)*(L : ℝ)/2 := by
        rw [← Real.sqrt_mul (by positivity),
          show (a*(L : ℝ)/2)*(b*(L : ℝ)/2) = (a*b)*((L : ℝ)/2)^2 by ring,
          Real.sqrt_mul (by positivity),Real.sqrt_sq (by positivity)]
        ring
      rwa [he] at hh
    have hd : 0 < Real.sqrt k*Real.sqrt l := by positivity
    have hu := div_le_div₀ (by norm_num : (0 : ℝ) ≤ 1) le_rfl
      (by positivity : 0 < Real.sqrt (a*b)*(L : ℝ)/2) hden
    simp only [← mul_div_mul_comm,one_mul] at hpair
    have hnorm : 1/(Real.sqrt (a*b)*(L : ℝ)/2) = 2/(Real.sqrt (a*b)*L) := by ring
    rw [hnorm] at hu
    have hh := hpair.trans hu
    unfold rowReference
    simp only [SequentialDecisionRisk.FiniteSupportSelectionBayes.b,if_pos hi]
    have hae : (L : ℝ)*(1+r)/2 = a*L := by dsimp [a]; ring
    have hbe : (L : ℝ)*(1-r)/2 = b*L := by dsimp [b]; ring
    try simp only [Prod.fst,Prod.snd]
    rw [hae,hbe]
    simpa only [a,b,k,l,← mul_div_mul_comm] using hh

end
end D5.S3.Estimation.TimeArrow.NativeRectangleReferenceMass
