/- GID: D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/SharpBorn
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/FiveDimensionalFourierThreshold/SharpBorn
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The exact computational and Fourier Born-law score of any two unit vectors in complex dimension five is at most (14 + 2 sqrt 5) / 5. -/


import D5.S3.Quantum.Information.FiveDimensionalFourierThreshold.SharpRows

/-!
The sharp upper bound for Qian's two-ray score (arXiv:2608.14806v2, Eq. (9)).
Qian's Theorem 6.14 supplies the attaining value separately.
-/

open InnerProductSpace QuantumPhaseEstimationGeneral
open D5.S3.Constants.PentagonCosines
open scoped BigOperators ComplexConjugate InnerProductSpace

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Information.FiveDimensionalFourierThreshold

private def oddCoordinates (x : CoordinateFive) : OddCoordinates :=
  ((x 1 - x 4) / (Real.sqrt 2 : ℂ), (x 2 - x 3) / (Real.sqrt 2 : ℂ))

private def oddVector (z : OddCoordinates) : CoordinateFive :=
  WithLp.toLp 2 ![0, z.1 / (Real.sqrt 2 : ℂ), z.2 / (Real.sqrt 2 : ℂ),
    -(z.2 / (Real.sqrt 2 : ℂ)), -(z.1 / (Real.sqrt 2 : ℂ))]

private def evenPart (x : CoordinateFive) : CoordinateFive :=
  x - oddVector (oddCoordinates x)

private theorem sqrt_two_complex :
    (Real.sqrt 2 : ℂ) ^ 2 = 2 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)

private theorem root_two_ne : (Real.sqrt 2 : ℂ) ≠ 0 := by
  exact_mod_cast (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)).ne'

private theorem evenPart_pairs (x : CoordinateFive) :
    evenPart x 1 = evenPart x 4 ∧ evenPart x 2 = evenPart x 3 := by
  constructor
  · simp [evenPart, oddVector, oddCoordinates, PiLp.sub_apply]
    field_simp [root_two_ne] <;> linear_combination (x 1 - x 4) * sqrt_two_complex
  · simp [evenPart, oddVector, oddCoordinates, PiLp.sub_apply]
    field_simp [root_two_ne] <;> linear_combination (x 2 - x 3) * sqrt_two_complex

private theorem geometryAmplitude_add (x y : CoordinateFive) (r : FiveRow) :
    geometryAmplitude (x + y) r = geometryAmplitude x r + geometryAmplitude y r := by
  simp only [geometryAmplitude_eq_inner, inner_add_right]

private abbrev fiveResidue := ZMod.finEquiv 5

private theorem scaled_phase_difference (k : Idx) (hk : k = 1 ∨ k = 2) :
    scale 5 * (pentagonPhase (-fiveResidue k) - pentagonPhase (fiveResidue k)) =
      -Complex.I * (if k = 1 then (sharpSigma : ℂ) else (sharpH : ℂ)) := by
  let θ : ℝ := 2 * Real.pi * (k.val : ℝ) / 5
  have hθ : 0 < θ ∧ θ < Real.pi := by
    rcases hk with rfl | rfl <;> norm_num [θ] <;> constructor <;> linarith [Real.pi_pos]
  have hp : pentagonPhase (fiveResidue k) = Complex.exp ((θ : ℂ) * Complex.I) := by
    rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]
    congr 1
    have hv : (fiveResidue k).val = k.val := by rcases hk with rfl | rfl <;> decide
    rw [hv]
    dsimp [θ]
    push_cast
    ring
  have hcos : Real.cos θ =
      if k = 1 then (Real.sqrt 5 - 1) / 4 else -(1 + Real.sqrt 5) / 4 := by
    obtain ⟨hc₁, hc₂, _, _⟩ := pentagon_golden_cosines
    rcases hk with rfl | rfl
    · rw [Real.inv_goldenRatio, Real.goldenConj] at hc₂
      norm_num [θ]
      linarith only [hc₂]
    · rw [Real.goldenRatio] at hc₁
      norm_num [θ]
      rw [show 2 * Real.pi * 2 / 5 = Real.pi - Real.pi / 5 by ring, Real.cos_pi_sub]
      linarith only [hc₁]
  have hs : Real.sqrt (5 : ℝ) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have hsinval : 2 * Real.sin θ / Real.sqrt 5 = if k = 1 then sharpSigma else sharpH := by
    have htrig := Real.sin_sq_add_cos_sq θ
    rw [hcos] at htrig
    rcases hk with rfl | rfl
    · rw [if_pos rfl]
      apply (sq_eq_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
      simp only [if_true] at htrig
      rw [div_pow, hs, Real.sq_sqrt (by positivity)]
      nlinarith only [htrig, hs]
    · rw [if_neg (by decide : (2 : Idx) ≠ 1)]
      apply (sq_eq_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
      simp only [if_neg (by decide : (2 : Idx) ≠ 1)] at htrig
      rw [div_pow, hs, Real.sq_sqrt (by linarith only [sharp_sqrt_five_bounds.2])]
      nlinarith only [htrig, hs]
  have hscale : scale 5 = ((Real.sqrt 5)⁻¹ : ℝ) := by
    change ((Real.sqrt (↑(5 : ℕ))) : ℂ)⁻¹ = _
    push_cast
    rfl
  have hd :
      conj (Complex.exp ((θ : ℂ) * Complex.I)) - Complex.exp ((θ : ℂ) * Complex.I) =
        -(2 * (Real.sin θ : ℂ)) * Complex.I := by
    rw [Complex.exp_ofReal_mul_I]
    simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  have hv : (2 : ℂ) * (Real.sin θ : ℂ) / (Real.sqrt 5 : ℂ) =
      if k = 1 then (sharpSigma : ℂ) else (sharpH : ℂ) := by
    rcases hk with rfl | rfl <;>
      simpa only [if_true, if_false, show (2 : Idx) ≠ 1 by decide, Complex.ofReal_div,
        Complex.ofReal_mul, Complex.ofReal_ofNat] using congrArg Complex.ofReal hsinval
  rw [← phase_neg, hp, hscale, hd, ← hv, Complex.ofReal_inv]
  ring

private theorem oddVector_amplitude (z : OddCoordinates) :
    (∀ j, geometryAmplitude (oddVector z) (.inl j) = oddVector z j) ∧
      (∀ j, geometryAmplitude (oddVector z) (.inr j) =
        -Complex.I * oddVector (oddFourier z) j) := by
  refine ⟨fun _ => rfl, ?_⟩
  intro j
  have hd₁ := scaled_phase_difference 1 (Or.inl rfl)
  have hd₂ := scaled_phase_difference 2 (Or.inr rfl)
  change scale 5 * (pentagonPhase 4 - pentagonPhase 1) = _ at hd₁
  change scale 5 * (pentagonPhase 3 - pentagonPhase 2) = _ at hd₂
  norm_num only [if_true, show (2 : Idx) ≠ 1 by decide, if_false] at hd₁ hd₂
  have hrow :
      geometryAmplitude (oddVector z) (.inr j) =
        scale 5 * (pentagonPhase (-(fiveResidue 1 * fiveResidue j)) -
          pentagonPhase (-(fiveResidue 4 * fiveResidue j))) * (z.1 / (Real.sqrt 2 : ℂ)) +
        scale 5 * (pentagonPhase (-(fiveResidue 2 * fiveResidue j)) -
          pentagonPhase (-(fiveResidue 3 * fiveResidue j))) * (z.2 / (Real.sqrt 2 : ℂ)) := by
    rw [inverse_entry, sum_univ_five]
    simp [oddVector]
    ring
  have hrev₁ : scale 5 * (pentagonPhase 1 - pentagonPhase 4) = Complex.I * (sharpSigma : ℂ) := by
    linear_combination -hd₁
  have hrev₂ : scale 5 * (pentagonPhase 2 - pentagonPhase 3) = Complex.I * (sharpH : ℂ) := by
    linear_combination -hd₂
  fin_cases j
  · change _ = scale 5 * (pentagonPhase 0 - pentagonPhase 0) * _ +
      scale 5 * (pentagonPhase 0 - pentagonPhase 0) * _ at hrow
    simpa [oddVector] using hrow
  · change _ = scale 5 * (pentagonPhase 4 - pentagonPhase 1) * _ +
      scale 5 * (pentagonPhase 3 - pentagonPhase 2) * _ at hrow
    rw [hrow, hd₁, hd₂]
    simp [oddVector, oddFourier] <;> ring
  · change _ = scale 5 * (pentagonPhase 3 - pentagonPhase 2) * _ +
      scale 5 * (pentagonPhase 1 - pentagonPhase 4) * _ at hrow
    rw [hrow, hd₂, hrev₁]
    simp [oddVector, oddFourier] <;> ring
  · change _ = scale 5 * (pentagonPhase 2 - pentagonPhase 3) * _ +
      scale 5 * (pentagonPhase 4 - pentagonPhase 1) * _ at hrow
    rw [hrow, hrev₂, hd₁]
    simp [oddVector, oddFourier] <;> ring
  · change _ = scale 5 * (pentagonPhase 1 - pentagonPhase 4) * _ +
      scale 5 * (pentagonPhase 2 - pentagonPhase 3) * _ at hrow
    rw [hrow, hrev₁, hrev₂]
    simp [oddVector, oddFourier] <;> ring

private theorem even_fourier_pairs (x : CoordinateFive) (h₁ : x 1 = x 4) (h₂ : x 2 = x 3) :
    geometryAmplitude x (.inr 1) = geometryAmplitude x (.inr 4) ∧
      geometryAmplitude x (.inr 2) = geometryAmplitude x (.inr 3) := by
  rw [inverse_entry, inverse_entry, inverse_entry, inverse_entry]
  simp only [sum_univ_five, ← h₁, ← h₂]
  constructor
  · change scale 5 * (pentagonPhase 0 * x 0 + pentagonPhase 4 * x 1 +
      pentagonPhase 3 * x 2 + pentagonPhase 2 * x 2 + pentagonPhase 1 * x 1) =
      scale 5 * (pentagonPhase 0 * x 0 + pentagonPhase 1 * x 1 +
      pentagonPhase 2 * x 2 + pentagonPhase 3 * x 2 + pentagonPhase 4 * x 1)
    ring
  · change scale 5 * (pentagonPhase 0 * x 0 + pentagonPhase 3 * x 1 +
      pentagonPhase 1 * x 2 + pentagonPhase 4 * x 2 + pentagonPhase 2 * x 1) =
      scale 5 * (pentagonPhase 0 * x 0 + pentagonPhase 2 * x 1 +
      pentagonPhase 4 * x 2 + pentagonPhase 1 * x 2 + pentagonPhase 3 * x 1)
    ring

private def centeredRowAmplitude (x y : CoordinateFive) (r : FiveRow) : ℂ :=
  let u := geometryAmplitude x r
  let v := geometryAmplitude y r
  match r with
  | .inl j => if j ∈ centeredPair then (sharpBeta : ℂ) * u + (sharpAlpha : ℂ) * v
      else (sharpAlpha : ℂ) * u - (sharpBeta : ℂ) * v
  | .inr j => if j ∈ centeredPair then (sharpAlpha : ℂ) * u + (sharpBeta : ℂ) * v
      else (sharpBeta : ℂ) * u - (sharpAlpha : ℂ) * v

private theorem centeredRowEnergy_eq (x y : CoordinateFive) (r : FiveRow) :
    rowEnergy centeredRankFive x y r = ‖centeredRowAmplitude x y r‖ ^ 2 := by
  cases r with
  | inl j =>
    by_cases h : j ∈ centeredPair
    · simp [rowEnergy, centeredRowAmplitude, rowPhase, majorityAmplitude, minorityAmplitude,
        measuredAmplitude_eq_geometry, centeredRankFive, h, add_comm]
    · simp [rowEnergy, centeredRowAmplitude, rowPhase, majorityAmplitude, minorityAmplitude,
        measuredAmplitude_eq_geometry, centeredRankFive, h]
  | inr j =>
    by_cases h : j ∈ centeredPair
    · simp [rowEnergy, centeredRowAmplitude, rowPhase, majorityAmplitude, minorityAmplitude,
        measuredAmplitude_eq_geometry, centeredRankFive, h]
    · simp only [rowEnergy, centeredRowAmplitude, rowPhase, majorityAmplitude, minorityAmplitude,
        measuredAmplitude_eq_geometry, centeredRankFive, Finset.inr_mem_disjSum, if_neg h,
        one_mul]
      rw [← norm_neg ((sharpBeta : ℂ) * geometryAmplitude x (.inr j) -
        (sharpAlpha : ℂ) * geometryAmplitude y (.inr j)), neg_sub]

private theorem centeredRowAmplitude_add (x y a b : CoordinateFive) (r : FiveRow) :
    centeredRowAmplitude (x + a) (y + b) r =
      centeredRowAmplitude x y r + centeredRowAmplitude a b r := by
  cases r with
  | inl j => by_cases h : j ∈ centeredPair <;> simp [centeredRowAmplitude, geometryAmplitude_add, h] <;> ring
  | inr j => by_cases h : j ∈ centeredPair <;> simp [centeredRowAmplitude, geometryAmplitude_add, h] <;> ring

private theorem centered_decomposition (x : CoordinateFive) :
    evenPart x + oddVector (oddCoordinates x) = x := sub_add_cancel _ _

private theorem pair_sq (a b : ℂ) :
    ‖a + b‖ ^ 2 + ‖a + -b‖ ^ 2 = 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  rw [← sub_eq_add_neg]
  simpa only [mul_add] using parallelogram_law_with_norm ℂ a b

private theorem two_div_root_sq (z : ℂ) : 2 * ‖z / (Real.sqrt 2 : ℂ)‖ ^ 2 = ‖z‖ ^ 2 := by
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring

private theorem two_div_root_sq_real (z : ℂ) : 2 * (‖z‖ / |Real.sqrt 2|) ^ 2 = ‖z‖ ^ 2 := by
  simpa only [norm_div, Complex.norm_real, Real.norm_eq_abs] using two_div_root_sq z

private def centeredWeight (r : FiveRow) : ℝ :=
  if r ∈ centeredLightRows then lightWeight else heavyWeight

private theorem centered_weighted_even_le (x y : CoordinateFive) :
    (∑ r, centeredWeight r * ‖centeredRowAmplitude x y r‖ ^ 2) ≤
      lightWeight * ∑ r, ‖centeredRowAmplitude x y r‖ ^ 2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro r _
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  by_cases h : r ∈ centeredLightRows
  · simp [centeredWeight, h]
  · norm_num [centeredWeight, h, heavyWeight, lightWeight]

private theorem centeredRowAmplitude_even (x y : CoordinateFive) :
    let E := centeredRowAmplitude (evenPart x) (evenPart y)
    E (.inl 1) = E (.inl 4) ∧ E (.inl 2) = E (.inl 3) ∧
      E (.inr 1) = E (.inr 4) ∧ E (.inr 2) = E (.inr 3) := by
  obtain ⟨hx₁, hx₂⟩ := evenPart_pairs x
  obtain ⟨hy₁, hy₂⟩ := evenPart_pairs y
  obtain ⟨hfx₁, hfx₂⟩ := even_fourier_pairs _ hx₁ hx₂
  obtain ⟨hfy₁, hfy₂⟩ := even_fourier_pairs _ hy₁ hy₂
  dsimp only
  have hstd (z : CoordinateFive) (j : Idx) : geometryAmplitude z (.inl j) = z j := rfl
  norm_num [centeredRowAmplitude, centeredPair, hstd, hx₁, hx₂, hy₁, hy₂,
    hfx₁, hfx₂, hfy₁, hfy₂]

private theorem centeredRowAmplitude_odd (u v : OddCoordinates) :
    let O := centeredRowAmplitude (oddVector u) (oddVector v)
    O (.inl 0) = 0 ∧ O (.inr 0) = 0 ∧
    O (.inl 4) = -O (.inl 1) ∧ O (.inl 3) = -O (.inl 2) ∧
    O (.inr 4) = -O (.inr 1) ∧ O (.inr 3) = -O (.inr 2) := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [centeredRowAmplitude, (oddVector_amplitude u).1,
      (oddVector_amplitude v).1, (oddVector_amplitude u).2, (oddVector_amplitude v).2] <;>
    norm_num [centeredPair, oddVector] <;> ring

private theorem centered_weighted_odd (u v : OddCoordinates) :
    (∑ r, centeredWeight r * ‖centeredRowAmplitude (oddVector u) (oddVector v) r‖ ^ 2) =
      oddWeighted u v := by
  let O := centeredRowAmplitude (oddVector u) (oddVector v)
  obtain ⟨h₀, h₁, h₂, h₃, h₄, h₅⟩ := centeredRowAmplitude_odd u v
  change O (.inl 0) = 0 at h₀
  change O (.inr 0) = 0 at h₁
  change O (.inl 4) = -O (.inl 1) at h₂
  change O (.inl 3) = -O (.inl 2) at h₃
  change O (.inr 4) = -O (.inr 1) at h₄
  change O (.inr 3) = -O (.inr 2) at h₅
  change (∑ r, centeredWeight r * ‖O r‖ ^ 2) = _
  rw [Fintype.sum_sum_type, sum_univ_five, sum_univ_five, h₀, h₁, h₂, h₃, h₄, h₅]
  have hleft₁ : O (.inl 1) =
      ((sharpAlpha : ℂ) * u.1 - (sharpBeta : ℂ) * v.1) / (Real.sqrt 2 : ℂ) := by
    simp only [O, centeredRowAmplitude, (oddVector_amplitude u).1,
      (oddVector_amplitude v).1]
    norm_num [centeredPair, oddVector] <;> ring
  have hleft₂ : O (.inl 2) =
      ((sharpBeta : ℂ) * u.2 + (sharpAlpha : ℂ) * v.2) / (Real.sqrt 2 : ℂ) := by
    simp only [O, centeredRowAmplitude, (oddVector_amplitude u).1,
      (oddVector_amplitude v).1]
    norm_num [centeredPair, oddVector] <;> ring
  have hright₁ : O (.inr 1) = -Complex.I *
      (((sharpBeta : ℂ) * (oddFourier u).1 - (sharpAlpha : ℂ) * (oddFourier v).1) /
        (Real.sqrt 2 : ℂ)) := by
    simp only [O, centeredRowAmplitude, (oddVector_amplitude u).2,
      (oddVector_amplitude v).2]
    norm_num [centeredPair, oddVector] <;> ring
  have hright₂ : O (.inr 2) = -Complex.I *
      (((sharpAlpha : ℂ) * (oddFourier u).2 + (sharpBeta : ℂ) * (oddFourier v).2) /
        (Real.sqrt 2 : ℂ)) := by
    simp only [O, centeredRowAmplitude, (oddVector_amplitude u).2,
      (oddVector_amplitude v).2]
    norm_num [centeredPair, oddVector] <;> ring
  rw [hleft₁, hleft₂, hright₁, hright₂]
  norm_num [centeredWeight, centeredLightRows, norm_mul, Complex.norm_I, -norm_div]
  unfold oddWeighted
  linarith only [
    congrArg (lightWeight * ·) (two_div_root_sq_real
      ((sharpAlpha : ℂ) * u.1 - (sharpBeta : ℂ) * v.1)),
    congrArg (heavyWeight * ·) (two_div_root_sq_real
      ((sharpBeta : ℂ) * u.2 + (sharpAlpha : ℂ) * v.2)),
    congrArg (lightWeight * ·) (two_div_root_sq_real
      ((sharpBeta : ℂ) * (oddFourier u).1 - (sharpAlpha : ℂ) * (oddFourier v).1)),
    congrArg (heavyWeight * ·) (two_div_root_sq_real
      ((sharpAlpha : ℂ) * (oddFourier u).2 + (sharpBeta : ℂ) * (oddFourier v).2))]

private theorem centered_weighted_split (x y : CoordinateFive) :
    (∑ r, centeredWeight r * rowEnergy centeredRankFive x y r) =
      oddWeighted (oddCoordinates x) (oddCoordinates y) +
        ∑ r, centeredWeight r * ‖centeredRowAmplitude (evenPart x) (evenPart y) r‖ ^ 2 := by
  rw [← centered_weighted_odd]
  let E := centeredRowAmplitude (evenPart x) (evenPart y)
  let O := centeredRowAmplitude (oddVector (oddCoordinates x)) (oddVector (oddCoordinates y))
  have hrow (r : FiveRow) : rowEnergy centeredRankFive x y r = ‖E r + O r‖ ^ 2 := by
    rw [centeredRowEnergy_eq, ← centered_decomposition x, ← centered_decomposition y,
      centeredRowAmplitude_add]
  obtain ⟨he₁, he₂, he₃, he₄⟩ := centeredRowAmplitude_even x y
  obtain ⟨ho₀, ho₁, ho₂, ho₃, ho₄, ho₅⟩ :=
    centeredRowAmplitude_odd (oddCoordinates x) (oddCoordinates y)
  change E (.inl 1) = E (.inl 4) at he₁
  change E (.inl 2) = E (.inl 3) at he₂
  change E (.inr 1) = E (.inr 4) at he₃
  change E (.inr 2) = E (.inr 3) at he₄
  change O (.inl 0) = 0 at ho₀
  change O (.inr 0) = 0 at ho₁
  change O (.inl 4) = -O (.inl 1) at ho₂
  change O (.inl 3) = -O (.inl 2) at ho₃
  change O (.inr 4) = -O (.inr 1) at ho₄
  change O (.inr 3) = -O (.inr 2) at ho₅
  change (∑ r, centeredWeight r * rowEnergy centeredRankFive x y r) =
    (∑ r, centeredWeight r * ‖O r‖ ^ 2) + ∑ r, centeredWeight r * ‖E r‖ ^ 2
  simp only [hrow, Fintype.sum_sum_type, sum_univ_five, ← he₁, ← he₂, ← he₃,
    ← he₄, ho₀, ho₁, ho₂, ho₃, ho₄, ho₅]
  norm_num [centeredWeight, centeredLightRows]
  linarith only [
    congrArg (lightWeight * ·) (pair_sq (E (.inl 1)) (O (.inl 1))),
    congrArg (heavyWeight * ·) (pair_sq (E (.inl 2)) (O (.inl 2))),
    congrArg (lightWeight * ·) (pair_sq (E (.inr 1)) (O (.inr 1))),
    congrArg (heavyWeight * ·) (pair_sq (E (.inr 2)) (O (.inr 2)))]

private theorem odd_norm_sq (u : OddCoordinates) : ‖oddVector u‖ ^ 2 = oddMass u := by
  rw [EuclideanSpace.norm_sq_eq, sum_univ_five]
  simp [oddVector, oddMass, -norm_div]
  linarith only [two_div_root_sq_real u.1, two_div_root_sq_real u.2]

private theorem centered_norm_split (x : CoordinateFive) :
    ‖x‖ ^ 2 = ‖evenPart x‖ ^ 2 + oddMass (oddCoordinates x) := by
  let E := evenPart x
  let O := oddVector (oddCoordinates x)
  have h : ‖x‖ ^ 2 = ‖E + O‖ ^ 2 := congrArg (fun z : CoordinateFive => ‖z‖ ^ 2)
    (centered_decomposition x).symm
  rw [h, ← odd_norm_sq]
  obtain ⟨he₁, he₂⟩ := evenPart_pairs x
  change E 1 = E 4 at he₁
  change E 2 = E 3 at he₂
  have ho₀ : O 0 = 0 := rfl
  have ho₁ : O 4 = -O 1 := rfl
  have ho₂ : O 3 = -O 2 := rfl
  change ‖E + O‖ ^ 2 = ‖E‖ ^ 2 + ‖O‖ ^ 2
  simp only [EuclideanSpace.norm_sq_eq, sum_univ_five, PiLp.add_apply,
    ← he₁, ← he₂, ho₀, ho₁, ho₂, add_zero, norm_neg, norm_zero, zero_pow two_ne_zero]
  linarith only [pair_sq (E 1) (O 1), pair_sq (E 2) (O 2)]

private theorem centered_mass_split (x : CoordinateFive) :
    maskMass (fiveLaw x) centeredRankFive =
      maskMass (fiveLaw (evenPart x)) centeredRankFive +
        (‖(oddCoordinates x).1‖ ^ 2 + ‖(oddFourier (oddCoordinates x)).2‖ ^ 2) := by
  let u := oddCoordinates x
  let E := evenPart x
  let O := oddVector u
  obtain ⟨he₁, he₂⟩ := evenPart_pairs x
  change E 1 = E 4 at he₁
  change E 2 = E 3 at he₂
  obtain ⟨_, hef₂⟩ := even_fourier_pairs E he₁ he₂
  have hstd (z : CoordinateFive) (j : Idx) : geometryAmplitude z (.inl j) = z j := rfl
  have hrow (r : FiveRow) :
      fiveLaw x r = ‖geometryAmplitude E r + geometryAmplitude O r‖ ^ 2 := by
    rw [fiveLaw_eq_amplitude, measuredAmplitude_eq_geometry, ← centered_decomposition x,
      geometryAmplitude_add]
  have hm : centeredRankFive =
      ({0, 1, 4} : Finset Idx).disjSum ({2, 3} : Finset Idx) := by decide
  change maskMass (fiveLaw x) centeredRankFive =
    maskMass (fiveLaw E) centeredRankFive +
      (‖u.1‖ ^ 2 + ‖(oddFourier u).2‖ ^ 2)
  simp only [hm, maskMass, Finset.sum_disjSum, hrow, fiveLaw_eq_amplitude,
    measuredAmplitude_eq_geometry]
  simp only [O, (oddVector_amplitude u).2, hstd]
  norm_num [oddVector, ← he₁, ← hef₂, -norm_div]
  have hneg (z : ℂ) : -Complex.I * -z = -(-Complex.I * z) := by ring
  simp only [hneg]
  have hf := pair_sq (geometryAmplitude E (.inr 2))
    (Complex.I * ((oddFourier u).2 / (Real.sqrt 2 : ℂ)))
  simp only [norm_mul, Complex.norm_I, one_mul] at hf
  linarith only [hf, pair_sq (E 1) (u.1 / (Real.sqrt 2 : ℂ)),
    two_div_root_sq u.1, two_div_root_sq (oddFourier u).2]

private theorem odd_deficit_eq_mass (u v : OddCoordinates) :
    oddDeficit u v =
      ((1 + sharpC) * oddMass u - (‖u.1‖ ^ 2 + ‖(oddFourier u).2‖ ^ 2)) +
      ((‖v.1‖ ^ 2 + ‖(oddFourier v).2‖ ^ 2) - (1 - sharpC) * oddMass v) := by
  unfold oddDeficit
  rw [oddRayleigh_fourier]
  simp only [oddRayleigh, oddMass, oddFourier]
  change
    ((sharpC - sharpH ^ 2) * ‖u.1‖ ^ 2 +
      2 * (sharpH * sharpSigma) * (u.1.re * u.2.re + u.1.im * u.2.im) +
      (sharpC + sharpH ^ 2) * ‖u.2‖ ^ 2) +
    ((sharpC + sharpH ^ 2) * ‖v.1‖ ^ 2 +
      2 * (-sharpH * sharpSigma) * (v.1.re * v.2.re + v.1.im * v.2.im) +
      (sharpC - sharpH ^ 2) * ‖v.2‖ ^ 2) = _
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
    Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, zero_mul, sub_zero, zero_add, add_zero]
  linear_combination
    ((u.2.re ^ 2 + u.2.im ^ 2) - (v.2.re ^ 2 + v.2.im ^ 2)) * sharp_h_sigma_sq

private theorem centered_deficit_split (x y : CoordinateFive) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    maskDeficit centeredRankFive x y =
      spectralDeficit true (evenPart x) + spectralDeficit false (evenPart y) +
        oddDeficit (oddCoordinates x) (oddCoordinates y) := by
  rw [centered_deficit x y hx hy, spectralDeficit_eq_mass true, spectralDeficit_eq_mass false,
    spectralDeficit_eq_mass true, spectralDeficit_eq_mass false]
  simp only [Bool.false_eq_true, if_true, if_false]
  rw [centered_norm_split x, centered_norm_split y, centered_mass_split x, centered_mass_split y,
    odd_deficit_eq_mass]
  ring

private theorem centered_opposite_inner (z : CoordinateFive) (odd plus : Bool)
    (hs : geometryAmplitude z (.inl 3) =
      (if odd then 1 else -1) * geometryAmplitude z (.inl 2))
    (hf : geometryAmplitude z (.inr 3) =
      (if odd then 1 else -1) * geometryAmplitude z (.inr 2)) :
    criticalCoefficient z (some (odd, plus)) = 0 := by
  rw [criticalCoefficient, centeredEigenbasis_some]
  simp only [geometryAmplitude_eq_inner, Sum.elim_inl, Sum.elim_inr] at hs hf
  have hS : ⟪centeredStandard odd, z⟫_ℂ = 0 := by
    cases odd <;>
      simp only [Bool.false_eq_true, ite_true, ite_false, centeredStandard,
        inner_smul_left, inner_add_left, map_neg, map_one] at hs ⊢ <;>
      rw [hs] <;> ring
  have hF : ⟪centeredFourier odd, z⟫_ℂ = 0 := by
    cases odd <;>
      simp only [Bool.false_eq_true, ite_true, ite_false, centeredFourier,
        inner_smul_left, inner_add_left, map_neg, map_one] at hf ⊢ <;>
      rw [hf] <;> ring
  simp only [centeredRay, principalStandard, ite_true, centeredOutside,
    inner_smul_left, inner_add_left, inner_sub_left, hS, hF, mul_zero, sub_zero, add_zero]

private theorem criticalCoefficient_even_part (x : CoordinateFive) (plus : Bool) :
    criticalCoefficient (evenPart x) (criticalIndex plus) =
      criticalCoefficient x (criticalIndex plus) := by
  let z := oddCoordinates x
  have ho : criticalCoefficient (oddVector z) (criticalIndex plus) = 0 := by
    apply centered_opposite_inner
    · simp only [(oddVector_amplitude z).1]
      norm_num [oddVector, criticalIndex]
    · simp only [(oddVector_amplitude z).2]
      norm_num [oddVector, criticalIndex] <;> ring
  have h := congrArg (fun t => criticalCoefficient t (criticalIndex plus)) (centered_decomposition x)
  change criticalCoefficient (evenPart x + oddVector z) (criticalIndex plus) = _ at h
  rw [show criticalCoefficient (evenPart x + oddVector z) (criticalIndex plus) =
      criticalCoefficient (evenPart x) (criticalIndex plus) +
        criticalCoefficient (oddVector z) (criticalIndex plus) from inner_add_right _ _ _,
    ho, add_zero] at h
  exact h

private theorem criticalCoefficient_even_odd (x : CoordinateFive) (plus : Bool) :
    criticalCoefficient (evenPart x) (some (true, plus)) = 0 := by
  obtain ⟨hs₁, hs₂⟩ := evenPart_pairs x
  obtain ⟨_, hf₂⟩ := even_fourier_pairs _ hs₁ hs₂
  apply centered_opposite_inner
  · change (evenPart x) 3 = 1 * (evenPart x) 2
    simpa using hs₂.symm
  · simpa using hf₂.symm

private def evenLeakage (plus : Bool) (x : CoordinateFive) : ℝ :=
  ‖criticalCoefficient (evenPart x) none‖ ^ 2 +
    ‖criticalCoefficient (evenPart x) (criticalIndex (!plus))‖ ^ 2

private theorem evenLeakage_eq (plus : Bool) (x : CoordinateFive) :
    evenLeakage plus x = ‖evenPart x‖ ^ 2 - criticalOverlap plus x ^ 2 := by
  have h := criticalCoefficient_sum (evenPart x)
  simp only [Fintype.sum_option, Fintype.sum_prod_type, Fintype.sum_bool,
    criticalCoefficient_even_odd, norm_zero, zero_pow two_ne_zero, zero_add, add_zero] at h
  unfold evenLeakage criticalOverlap
  rw [← criticalCoefficient_even_part x plus]
  cases plus <;> simp only [Bool.not_true, Bool.not_false, criticalIndex] <;> linarith only [h]

private theorem evenLeakage_deficit (plus : Bool) (x : CoordinateFive) :
    spectralDeficit plus (evenPart x) =
      sharpC * ‖criticalCoefficient (evenPart x) none‖ ^ 2 +
      (2 * sharpC) * ‖criticalCoefficient (evenPart x) (criticalIndex (!plus))‖ ^ 2 := by
  have h := Finset.sum_erase_add Finset.univ
    (fun i => criticalGap plus i * ‖criticalCoefficient (evenPart x) i‖ ^ 2)
    (Finset.mem_univ (criticalIndex plus))
  simp only [criticalGap_zero, zero_mul, add_zero] at h
  unfold spectralDeficit offReference
  rw [h]
  cases plus <;>
    simp [Fintype.sum_option, Fintype.sum_prod_type, Fintype.sum_bool, criticalGap_middle,
      criticalGap_even, criticalCoefficient_even_odd, criticalIndex]

private theorem oddFourier_mass (z : OddCoordinates) : oddMass (oddFourier z) = oddMass z := by
  simp only [oddMass, oddFourier, Complex.sq_norm, Complex.normSq_apply, Complex.mul_re,
    Complex.mul_im, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero]
  linear_combination (z.1.re ^ 2 + z.1.im ^ 2 + z.2.re ^ 2 + z.2.im ^ 2) * sharp_h_sigma_sq

private theorem odd_sector_mass (x y : OddCoordinates) :
    2 * (oddMass (oddSector 1 x y) + oddMass (oddSector (-1) x y)) =
      oddMass x + oddMass y := by
  rw [← oddFourier_mass y]
  simp only [oddMass, oddSector, Complex.ofReal_one, Complex.ofReal_neg, one_mul,
    neg_one_mul, norm_div, Complex.norm_two, div_pow, ← sub_eq_add_neg]
  have h₁ := parallelogram_law_with_norm ℂ x.1 (oddFourier y).1
  have h₂ := parallelogram_law_with_norm ℂ x.2 (oddFourier y).2
  linarith only [h₁, h₂]

private theorem odd_sector_difference (x y : OddCoordinates) :
    |oddMass x - oddMass y| ≤
      4 * Real.sqrt (oddMass (oddSector 1 x y) * oddMass (oddSector (-1) x y)) := by
  let u := oddSector 1 x y
  let v := oddSector (-1) x y
  have h (a b : ℂ) : |(conj a * b).re| ≤ ‖a‖ * ‖b‖ := by
    simpa only [norm_mul, Complex.norm_conj] using Complex.abs_re_le_norm (conj a * b)
  have hc := sharp_two_errors (sq_nonneg ‖u.1‖) (sq_nonneg ‖u.2‖)
    (sq_nonneg ‖v.1‖) (sq_nonneg ‖v.2‖)
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _),
    Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at hc
  have hd : oddMass x - oddMass y =
      4 * ((conj u.1 * v.1).re + (conj u.2 * v.2).re) := by
    rw [← oddFourier_mass y]
    simp only [u, v, oddMass, oddSector, Complex.ofReal_one, Complex.ofReal_neg, one_mul,
      neg_one_mul, ← sub_eq_add_neg]
    change ‖x.1‖ ^ 2 + ‖x.2‖ ^ 2 -
      (‖(oddFourier y).1‖ ^ 2 + ‖(oddFourier y).2‖ ^ 2) = _
    simp only [show ∀ a : ℂ, a / 2 = ((1 / 2 : ℝ) : ℂ) * a by
      intro a; push_cast; ring, Complex.sq_norm, Complex.normSq_apply,
      Complex.conj_re, Complex.conj_im, Complex.mul_re, Complex.mul_im, Complex.add_re,
      Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, zero_mul, sub_zero, add_zero]
    ring
  rw [hd, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact (abs_add_le ..).trans ((add_le_add (h _ _) (h _ _)).trans hc)

private theorem even_and_odd_leakage (x y : CoordinateFive) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    let e := evenLeakage true x + evenLeakage false y
    2 * (oddMass (oddSector 1 (oddCoordinates x) (oddCoordinates y)) +
      oddMass (oddSector (-1) (oddCoordinates x) (oddCoordinates y))) + e =
      2 - criticalOverlap true x ^ 2 - criticalOverlap false y ^ 2 ∧
    |criticalOverlap true x ^ 2 - criticalOverlap false y ^ 2| ≤
      4 * Real.sqrt (oddMass (oddSector 1 (oddCoordinates x) (oddCoordinates y)) *
        oddMass (oddSector (-1) (oddCoordinates x) (oddCoordinates y))) + e := by
  have hnx := centered_norm_split x
  have hny := centered_norm_split y
  rw [hx, one_pow] at hnx
  rw [hy, one_pow] at hny
  have hex : 0 ≤ evenLeakage true x := by unfold evenLeakage; positivity
  have hey : 0 ≤ evenLeakage false y := by unfold evenLeakage; positivity
  have h := odd_sector_difference (oddCoordinates x) (oddCoordinates y)
  dsimp only
  constructor
  · rw [odd_sector_mass, evenLeakage_eq, evenLeakage_eq]
    linarith only [hnx, hny]
  · have hid : criticalOverlap true x ^ 2 - criticalOverlap false y ^ 2 =
        (oddMass (oddCoordinates y) - oddMass (oddCoordinates x)) +
          (evenLeakage false y - evenLeakage true x) := by
      rw [evenLeakage_eq, evenLeakage_eq]
      linarith only [hnx, hny]
    rw [hid]
    refine (abs_add_le ..).trans (add_le_add ?_ ?_)
    · rwa [abs_sub_comm]
    · exact abs_le.2 ⟨by linarith only [hex, hey], by linarith only [hex, hey]⟩

private theorem centered_difference_eq :
    centeredProjectionDifference true = LinearMap.id - geometryMask centeredRankFour := by
  rw [centeredRankFour_eq]
  change LinearMap.id - P - Q = LinearMap.id - (P + Q)
  rw [sub_sub]

private theorem centered_difference_middle :
    centeredProjectionDifference true (criticalBasis none) = criticalBasis none := by
  rw [centered_difference_eq, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_self]
  apply ext_inner_left ℂ
  intro z
  rw [inner_geometryMask, inner_zero_right]
  refine Finset.sum_eq_zero fun r hr => ?_
  cases r with
  | inl j =>
    have hj : j ∈ centeredPair := by simpa [centeredRankFour] using hr
    have h := (centeredRankFive_middle_pair_mass j hj).1
    rw [pow_eq_zero_iff two_ne_zero, norm_eq_zero] at h
    rw [h, mul_zero]
  | inr j =>
    have hj : j ∈ centeredPair := by simpa [centeredRankFour] using hr
    have h := (centeredRankFive_middle_pair_mass j hj).2
    rw [pow_eq_zero_iff two_ne_zero, norm_eq_zero] at h
    rw [h, mul_zero]

private theorem centered_difference_extreme (plus : Bool) :
    centeredProjectionDifference true (criticalBasis (criticalIndex plus)) =
      (sharpB : ℂ) • criticalBasis (criticalIndex (!plus)) := by
  simpa only [criticalIndex, centeredEigenbasis_some, centeredCoupling, if_true,
    centeredOverlap, Bool.false_eq_true, if_false] using
    centeredProjectionDifference_ray true false plus

private theorem geometry_cross_sum (x y : CoordinateFive) :
    (∑ r, conj (geometryAmplitude x r) * geometryAmplitude y r) = 2 * ⟪x, y⟫_ℂ := by
  rw [Fintype.sum_sum_type]
  simp only [geometryAmplitude_eq_inner, Sum.elim_inl, Sum.elim_inr, inner_conj_symm,
    coordinateBasisFive.sum_inner_mul_inner, fourierBasisFive.sum_inner_mul_inner, two_mul]

private theorem geometry_sq_sum (x : CoordinateFive) :
    (∑ r, ‖geometryAmplitude x r‖ ^ 2) = 2 * ‖x‖ ^ 2 := by
  rw [Fintype.sum_sum_type]
  simp only [geometryAmplitude_eq_inner, Sum.elim_inl, Sum.elim_inr,
    coordinateBasisFive.sum_sq_norm_inner_right, fourierBasisFive.sum_sq_norm_inner_right, two_mul]

private theorem centered_unweighted_energy (x y : CoordinateFive) :
    (∑ r, ‖centeredRowAmplitude x y r‖ ^ 2) =
      2 * sharpC * (spectralDeficit true x + spectralDeficit false y) +
      2 * sharpD * (‖x‖ ^ 2 + ‖y‖ ^ 2) -
      4 * sharpB * (⟪x, centeredProjectionDifference true y⟫_ℂ).re := by
  let p (r : FiveRow) := ‖geometryAmplitude x r‖ ^ 2
  let q (r : FiveRow) := ‖geometryAmplitude y r‖ ^ 2
  let f (r : FiveRow) := (conj (geometryAmplitude x r) * geometryAmplitude y r).re
  have hplus (a b : ℝ) (u v : ℂ) :
      ‖(a : ℂ) * u + (b : ℂ) * v‖ ^ 2 =
        a ^ 2 * ‖u‖ ^ 2 + b ^ 2 * ‖v‖ ^ 2 + 2 * (a * b) * (conj u * v).re := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.conj_re, Complex.conj_im,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, zero_mul, sub_zero, zero_add, add_zero]
    ring
  have hminus (a b : ℝ) (u v : ℂ) :
      ‖(a : ℂ) * u - (b : ℂ) * v‖ ^ 2 =
        a ^ 2 * ‖u‖ ^ 2 + b ^ 2 * ‖v‖ ^ 2 - 2 * (a * b) * (conj u * v).re := by
    simpa only [Complex.ofReal_neg, neg_mul, ← sub_eq_add_neg, neg_sq, mul_neg, neg_mul]
      using hplus a (-b) u v
  have hrow (r : FiveRow) :
      ‖centeredRowAmplitude x y r‖ ^ 2 =
        (1 + sharpC) * p r + (1 - sharpC) * q r -
          2 * sharpC * (if r ∈ centeredRankFive then p r - q r else 0) -
          2 * sharpB * f r + 4 * sharpB * (if r ∈ centeredRankFour then f r else 0) := by
    cases r with
    | inl j =>
      by_cases hj : j ∈ centeredPair <;>
        simp [centeredRowAmplitude, centeredRankFive, centeredRankFour, hj, hplus, hminus,
          sharp_alpha_sq, sharp_beta_sq, sharp_alpha_mul_beta, mul_comm sharpBeta sharpAlpha,
          p, q, f] <;> ring
    | inr j =>
      by_cases hj : j ∈ centeredPair <;>
        simp [centeredRowAmplitude, centeredRankFive, centeredRankFour, hj, hplus, hminus,
          sharp_alpha_sq, sharp_beta_sq, sharp_alpha_mul_beta, mul_comm sharpBeta sharpAlpha,
          p, q, f] <;> ring
  have hmask (z : CoordinateFive) :
      (∑ r ∈ centeredRankFive, ‖geometryAmplitude z r‖ ^ 2) =
        maskMass (fiveLaw z) centeredRankFive := by
    simp only [maskMass, fiveLaw_eq_amplitude, measuredAmplitude_eq_geometry]
  have hc₁ : (∑ r, f r) = 2 * (⟪x, y⟫_ℂ).re := by
    simpa [f, Complex.re_sum, Complex.mul_re] using congrArg Complex.re (geometry_cross_sum x y)
  have hc₂ : (∑ r ∈ centeredRankFour, f r) =
      (⟪x, geometryMask centeredRankFour y⟫_ℂ).re := by
    rw [inner_geometryMask, Complex.re_sum]
  have hc₃ :
      (⟪x, centeredProjectionDifference true y⟫_ℂ).re =
        (⟪x, y⟫_ℂ).re - (⟪x, geometryMask centeredRankFour y⟫_ℂ).re := by
    rw [centered_difference_eq, LinearMap.sub_apply, LinearMap.id_apply, inner_sub_right,
      Complex.sub_re]
  simp_rw [hrow]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  simp only [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_sub_distrib, hc₁, hc₂, hc₃,
    spectralDeficit_eq_mass, Bool.false_eq_true, if_true, if_false]
  dsimp only [p, q]
  rw [geometry_sq_sum, geometry_sq_sum, hmask, hmask, sharpD_eq]
  ring

private theorem even_basis_expansion (x : CoordinateFive) :
    evenPart x =
      criticalCoefficient (evenPart x) none • criticalBasis none +
        criticalCoefficient (evenPart x) (criticalIndex false) • criticalBasis (criticalIndex false) +
        criticalCoefficient (evenPart x) (criticalIndex true) • criticalBasis (criticalIndex true) := by
  have h := criticalBasis.sum_repr' (evenPart x)
  change (∑ i, criticalCoefficient (evenPart x) i • criticalBasis i) = evenPart x at h
  simpa only [Fintype.sum_option, Fintype.sum_prod_type, Fintype.sum_bool,
    criticalIndex, criticalCoefficient_even_odd, zero_smul, zero_add, add_zero,
    add_comm, add_left_comm, add_assoc] using h.symm

private theorem neg_re_conj_mul_le (z w : ℂ) :
    -(conj z * w).re ≤ (‖z‖ ^ 2 + ‖w‖ ^ 2) / 2 := by
  have h := le_abs_self (-(conj z * w).re)
  rw [abs_neg] at h
  have hh := Complex.abs_re_le_norm (conj z * w)
  rw [norm_mul, Complex.norm_conj] at hh
  nlinarith only [h, hh, sq_nonneg (‖z‖ - ‖w‖)]

/-- The two extreme even rays couple with coefficient b, and the middle ray with 1. -/
private theorem centered_even_energy (x y : CoordinateFive)
    (hpx : criticalCoefficient x (criticalIndex true) = (criticalOverlap true x : ℂ))
    (hpy : criticalCoefficient y (criticalIndex false) = (criticalOverlap false y : ℂ))
    (he : sharpC * (evenLeakage true x + evenLeakage false y) ≤
      spectralDeficit true (evenPart x) + spectralDeficit false (evenPart y)) :
    (∑ r, ‖centeredRowAmplitude (evenPart x) (evenPart y) r‖ ^ 2) ≤
      evenCoefficient * (spectralDeficit true (evenPart x) + spectralDeficit false (evenPart y)) +
      2 * sharpD * (criticalOverlap true x - criticalOverlap false y) ^ 2 := by
  let X := evenPart x
  let Y := evenPart y
  let a := criticalOverlap true x
  let a' := criticalOverlap false y
  let m := criticalCoefficient X none
  let m' := criticalCoefficient Y none
  let p := criticalCoefficient X (criticalIndex false)
  let p' := criticalCoefficient Y (criticalIndex true)
  let δ := spectralDeficit true X + spectralDeficit false Y
  let e := evenLeakage true x + evenLeakage false y
  have ha : criticalCoefficient X (criticalIndex true) = (a : ℂ) :=
    (criticalCoefficient_even_part x true).trans hpx
  have ha' : criticalCoefficient Y (criticalIndex false) = (a' : ℂ) :=
    (criticalCoefficient_even_part y false).trans hpy
  have hY :=
    congrArg (centeredProjectionDifference true) (even_basis_expansion y)
  change centeredProjectionDifference true Y =
    centeredProjectionDifference true
      (m' • criticalBasis none + criticalCoefficient Y (criticalIndex false) •
        criticalBasis (criticalIndex false) + p' • criticalBasis (criticalIndex true)) at hY
  rw [ha', map_add, map_add, map_smul, map_smul, map_smul,
    centered_difference_middle, centered_difference_extreme, centered_difference_extreme,
    smul_smul, smul_smul] at hY
  have hc : (⟪X, centeredProjectionDifference true Y⟫_ℂ).re =
      (conj m * m').re + sharpB * (a * a') + sharpB * (conj p * p').re := by
    rw [hY]
    have hcoeff (i : CenteredEigenIndex) :
        ⟪X, criticalBasis i⟫_ℂ = conj (criticalCoefficient X i) :=
      (inner_conj_symm X _).symm
    simp only [inner_add_right, inner_smul_right, hcoeff, Bool.not_false, Bool.not_true]
    change (m' * conj m + (a' : ℂ) * (sharpB : ℂ) *
      conj (criticalCoefficient X (criticalIndex true)) +
      p' * (sharpB : ℂ) * conj p).re = _
    rw [ha]
    simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.conj_ofReal,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero, zero_add, add_zero]
    ring
  have hb : 0 ≤ sharpB := by linarith only [sharp_b_bounds.1]
  have hb₁ : sharpB ≤ 1 := by linarith only [sharp_b_bounds.2]
  have hm := neg_re_conj_mul_le m m'
  have hp := (mul_le_mul_of_nonneg_left (neg_re_conj_mul_le p p') hb).trans
    (mul_le_of_le_one_left (by positivity) hb₁)
  have hcross : -(⟪X, centeredProjectionDifference true Y⟫_ℂ).re ≤
      -sharpB * (a * a') + e / 2 := by
    rw [hc]
    change -( (conj m * m').re + sharpB * (a * a') + sharpB * (conj p * p').re) ≤
      -sharpB * (a * a') + (‖m‖ ^ 2 + ‖p‖ ^ 2 + (‖m'‖ ^ 2 + ‖p'‖ ^ 2)) / 2
    linarith only [hm, hp]
  have hn : ‖X‖ ^ 2 + ‖Y‖ ^ 2 = a ^ 2 + a' ^ 2 + e := by
    dsimp only [e, X, Y, a, a']
    rw [evenLeakage_eq, evenLeakage_eq]
    ring
  have hbudget : e ≤ δ / sharpC := (le_div_iff₀ sharpC_pos).2 (by
    rw [mul_comm]
    exact he)
  have hmul := mul_le_mul_of_nonneg_left hbudget (show 0 ≤ 2 * sharpB * (sharpB + 1) by positivity)
  have hc' := mul_le_mul_of_nonneg_left hcross (show 0 ≤ 4 * sharpB by positivity)
  change (∑ r, ‖centeredRowAmplitude X Y r‖ ^ 2) ≤
    evenCoefficient * δ + 2 * sharpD * (a - a') ^ 2
  rw [centered_unweighted_energy, hn]
  calc
    _ ≤ 2 * sharpC * δ + 2 * sharpD * (a - a') ^ 2 + 2 * sharpB * (sharpB + 1) * e := by
      rw [← sharpB_sq]
      change 2 * sharpC * δ + 2 * sharpB ^ 2 * (a ^ 2 + a' ^ 2 + e) -
        4 * sharpB * (⟪X, centeredProjectionDifference true Y⟫_ℂ).re ≤ _
      nlinarith only [hc']
    _ ≤ _ := by
      unfold evenCoefficient
      linarith only [show 2 * sharpB * (sharpB + 1) * e ≤
        2 * sharpB * (sharpB + 1) / sharpC * δ from
          hmul.trans_eq (by ring)]

private theorem centered_energy_data (x y : CoordinateFive)
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hδ : maskDeficit centeredRankFive x y < 0.075)
    (hpx : criticalCoefficient x (criticalIndex true) = (criticalOverlap true x : ℂ))
    (hpy : criticalCoefficient y (criticalIndex false) = (criticalOverlap false y : ℂ)) :
    Nonempty (CriticalEnergyData centeredRankFive x y) := by
  let δe := spectralDeficit true (evenPart x) + spectralDeficit false (evenPart y)
  let e := evenLeakage true x + evenLeakage false y
  obtain ⟨hτ, _, _, ha⟩ := centered_overlap_bounds x y hx hy hδ
  obtain ⟨hleak, hdiff⟩ := even_and_odd_leakage x y hx hy
  have heb : sharpC * e ≤ δe := by
    dsimp [e, δe]
    rw [evenLeakage_deficit, evenLeakage_deficit]
    unfold evenLeakage
    simp only [Bool.not_true, Bool.not_false]
    nlinarith only [
      mul_nonneg sharpC_pos.le
        (sq_nonneg ‖criticalCoefficient (evenPart x) (criticalIndex false)‖),
      mul_nonneg sharpC_pos.le
        (sq_nonneg ‖criticalCoefficient (evenPart y) (criticalIndex true)‖)]
  refine ⟨{
    lightRows := centeredLightRows
    oddX := oddCoordinates x
    oddY := oddCoordinates y
    evenDeficit := δe
    evenLeak := e
    overlapX := criticalOverlap true x
    overlapY := criticalOverlap false y
    deficit_split := centered_deficit_split x y hx hy
    even_nonneg := add_nonneg (spectralDeficit_nonneg _ _) (spectralDeficit_nonneg _ _)
    even_leak_nonneg := by dsimp [e, evenLeakage]; positivity
    even_leak_budget := heb
    total_leak := hleak.trans_le hτ.le
    overlap_sum := ha
    overlap_diff := hdiff
    posterior := centered_heavy_posterior x y hx hy hδ hpx hpy
    energy_split := ?_
  }⟩
  change (∑ r, centeredWeight r * rowEnergy centeredRankFive x y r) ≤ _
  rw [centered_weighted_split]
  refine add_le_add le_rfl ((centered_weighted_even_le _ _).trans ?_)
  apply mul_le_mul_of_nonneg_left _ (by norm_num [lightWeight])
  exact centered_even_energy x y hpx hpy heb

private theorem fiveLaw_affine (u : (ZMod 5)ˣ) (a b : ZMod 5) (x : CoordinateFive)
    (r : FiveRow) :
    fiveLaw (affineState u a b x) (affineRows u a b r) = fiveLaw x r := by
  simp only [fiveLaw_eq_amplitude, measuredAmplitude_eq_geometry, geometryAmplitude_affine,
    norm_mul, norm_affineRowPhase, one_mul]

private theorem critical_mask_centering (s : Finset FiveRow) (hc : CriticalFiveMask s) :
    ∃ (u : (ZMod 5)ˣ) (a b : ZMod 5),
      centeredRankFive.map (affineRows u a b).toEmbedding = s ∨
        centeredRankFive.map (affineRows u a b).toEmbedding = sᶜ := by
  rcases hc with ⟨_, i, i', j, j', hI, hJ, h⟩ | ⟨_, i, i', j, j', hI, hJ, h⟩
  · obtain ⟨u, a, b, _, hp, _⟩ := criticalMasks_affine i i' j j' h
    refine ⟨u, a, b, Or.inr ?_⟩
    have hleft : (sᶜ).toLeft = s.toLeftᶜ := by ext k; simp
    have hright : (sᶜ).toRight = s.toRightᶜ := by ext k; simp
    rw [hp, ← hI, ← hJ, ← hleft, ← hright, Finset.toLeft_disjSum_toRight]
  · obtain ⟨u, a, b, _, hp, _⟩ := criticalMasks_affine i i' j j' h
    refine ⟨u, a, b, Or.inl ?_⟩
    rw [hp, ← hI, ← hJ, compl_compl, Finset.toLeft_disjSum_toRight]

private theorem maskDeficit_swap_compl (s : Finset FiveRow) (x y : CoordinateFive)
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    maskDeficit sᶜ y x = maskDeficit s x y := by
  have h₁ := (maskMass_add_compl (fiveLaw x) s).trans (fiveLaw_sum_unit x hx)
  have h₂ := (maskMass_add_compl (fiveLaw y) s).trans (fiveLaw_sum_unit y hy)
  unfold maskDeficit
  linarith only [h₁, h₂]

private theorem aligned_critical_coefficient (plus : Bool) (z : CoordinateFive) :
    ∃ p : ℂ, ‖p‖ = 1 ∧
      criticalCoefficient (p • z) (criticalIndex plus) = (criticalOverlap plus (p • z) : ℂ) := by
  obtain ⟨p, hp, ha⟩ := align_inner (criticalBasis (criticalIndex plus)) z
  have hm : criticalOverlap plus (p • z) = criticalOverlap plus z := by
    simp only [criticalOverlap, criticalCoefficient, inner_smul_right, norm_mul, hp, one_mul]
  refine ⟨p, hp, ?_⟩
  rw [hm]
  exact ha

private theorem transport_centered_energy (s : Finset FiveRow) (x y : CoordinateFive)
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hs : SignCompatible (fiveLaw x) (fiveLaw y) s)
    (hδ : maskDeficit s x y < 0.075) (u : (ZMod 5)ˣ) (a b : ZMod 5)
    (hmap : centeredRankFive.map (affineRows u a b).toEmbedding = s) :
    ∃ X Y : CoordinateFive, ‖X‖ = 1 ∧ ‖Y‖ = 1 ∧ fiveScore X Y = fiveScore x y ∧
      SignCompatible (fiveLaw X) (fiveLaw Y) centeredRankFive ∧
      Nonempty (CriticalEnergyData centeredRankFive X Y) := by
  let f := affineState u a b
  let e := affineRows u a b
  let x' := f.symm x
  let y' := f.symm y
  obtain ⟨p, hp, hpx⟩ := aligned_critical_coefficient true x'
  obtain ⟨q, hq, hpy⟩ := aligned_critical_coefficient false y'
  let X := p • x'
  let Y := q • y'
  have hX : ‖X‖ = 1 := by simp [X, x', norm_smul, hp, hx]
  have hY : ‖Y‖ = 1 := by simp [Y, y', norm_smul, hq, hy]
  have hlawX (r : FiveRow) : fiveLaw X r = fiveLaw x (e r) := by
    rw [show X = p • x' from rfl, fiveLaw_unit_phase x' p hp, ← fiveLaw_affine u a b x' r]
    simp only [x', f, LinearIsometryEquiv.apply_symm_apply, e]
  have hlawY (r : FiveRow) : fiveLaw Y r = fiveLaw y (e r) := by
    rw [show Y = q • y' from rfl, fiveLaw_unit_phase y' q hq, ← fiveLaw_affine u a b y' r]
    simp only [y', f, LinearIsometryEquiv.apply_symm_apply, e]
  have hmem (r : FiveRow) : e r ∈ s ↔ r ∈ centeredRankFive := by
    rw [← hmap]
    exact Finset.mem_map' e.toEmbedding
  have hmass (U V : CoordinateFive) (h : ∀ r, fiveLaw U r = fiveLaw V (e r)) :
      maskMass (fiveLaw U) centeredRankFive = maskMass (fiveLaw V) s := by
    rw [← hmap]
    simp only [maskMass, Finset.sum_map, Equiv.toEmbedding_apply, h, e]
  refine ⟨X, Y, hX, hY, ?_, ⟨?_, ?_⟩, centered_energy_data X Y hX hY ?_ hpx hpy⟩
  · change (∑ r, scoreTerm (fiveLaw X r) (fiveLaw Y r)) =
      ∑ r, scoreTerm (fiveLaw x r) (fiveLaw y r)
    simp_rw [hlawX, hlawY]
    exact e.sum_comp (fun r => scoreTerm (fiveLaw x r) (fiveLaw y r))
  · intro r hr
    rw [hlawX, hlawY]
    exact hs.1 (e r) ((hmem r).2 hr)
  · intro r hr
    rw [hlawX, hlawY]
    exact hs.2 (e r) (fun hm => hr ((hmem r).1 hm))
  · simpa only [maskDeficit, hmass X x hlawX, hmass Y y hlawY] using hδ

private theorem critical_energy_data (s : Finset FiveRow) (x y : CoordinateFive)
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hs : SignCompatible (fiveLaw x) (fiveLaw y) s)
    (hc : CriticalFiveMask s) (hδ : maskDeficit s x y < 0.075) :
    ∃ X Y : CoordinateFive, ‖X‖ = 1 ∧ ‖Y‖ = 1 ∧ fiveScore X Y = fiveScore x y ∧
      SignCompatible (fiveLaw X) (fiveLaw Y) centeredRankFive ∧
      Nonempty (CriticalEnergyData centeredRankFive X Y) := by
  obtain ⟨u, a, b, hmap | hmap⟩ := critical_mask_centering s hc
  · exact transport_centered_energy s x y hx hy hs hδ u a b hmap
  · have h := transport_centered_energy sᶜ y x hy hx (signCompatible_compl hs)
      (by simpa only [maskDeficit_swap_compl s x y hx hy] using hδ) u a b hmap
    simpa only [fiveScore_swap x y] using h

/-- Sharp upper bound on the actual Born laws, for arbitrary complex unit vectors. -/
theorem fiveScore_le_sharp (x y : CoordinateFive) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    fiveScore x y ≤ (14 + 2 * Real.sqrt 5) / 5 := by
  classical
  change fiveScore x y ≤ sharpCutoff
  by_cases hS : sharpCutoff ≤ fiveScore x y
  · let s : Finset FiveRow := Finset.univ.filter fun i => fiveLaw y i < fiveLaw x i
    have hs : SignCompatible (fiveLaw x) (fiveLaw y) s := by
      constructor
      · intro i hi
        exact le_of_lt (by simpa [s] using hi)
      · intro i hi
        exact le_of_not_gt (by simpa [s] using hi)
    have hc := (critical_sign_mask_at_cutoff x y s hx hy hS hs).2
    have ht := sign_mask_mass_gap (fiveLaw_nonneg x) (fiveLaw_nonneg y)
      (fiveLaw_sum_unit x hx) hs (harmonicOverlap_le_sharpD_of_cutoff hx hy hS)
    have hδ : maskDeficit s x y < 0.075 := by
      unfold maskDeficit
      nlinarith only [ht, sharp_budget_lt]
    obtain ⟨X, Y, hX, hY, hscore, hs', ⟨d⟩⟩ := critical_energy_data s x y hx hy hs hc hδ
    rw [← hscore]
    exact score_le_of_energy_data centeredRankFive X Y hX hY hs' d
  · exact le_of_lt (lt_of_not_ge hS)

theorem positiveFourierScore_le_sharp (x y : CoordinateFive) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    positiveFourierScore x y ≤ (14 + 2 * Real.sqrt 5) / 5 := by
  let C (v : CoordinateFive) : CoordinateFive := WithLp.toLp 2 (fun i => conj (v i))
  have hn (v : CoordinateFive) : ‖C v‖ = ‖v‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp only [EuclideanSpace.norm_sq_eq, C, Complex.norm_conj]
  have hk (v : CoordinateFive) (i : Idx) :
      inverseQFT 5 (WithLp.ofLp (C v)) i = conj (QFT 5 (WithLp.ofLp v) i) := by
    simp [C, inverseQFT, QFT, scale]
  have hscore : fiveScore (C x) (C y) = positiveFourierScore x y := by
    rw [fiveScore_eq_sum]
    simp only [positiveFourierScore, hk, C, PiLp.toLp_apply, Complex.norm_conj]
  rw [← hscore]
  exact fiveScore_le_sharp _ _ ((hn x).trans hx) ((hn y).trans hy)

end D5.S3.Quantum.Information.FiveDimensionalFourierThreshold
