/- GID: D5/S3/Quantum/Information/QutritMagicCoherenceBound
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/QutritMagicCoherenceBound
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Pure qutrit sum negativity is bounded below by half-coherence times its defect root. -/

import D5.S3.Quantum.PureState.PureStateHandshake
import D5.S3.Quantum.Information.CorrelatedCoherenceMonogamyRefutation

/-! The pure-qutrit magic–coherence inequality of Mukhopadhyay–Sazim–Pati,
arXiv:1801.04807v3, Eq. (18), for the Wigner convention of Eq. (12).

The negative mass of each column is controlled by its first two moments. For
amplitude norms `a, b, c`, the defects `a² - bc`, `b² - ac`, `c² - ab` obey
a second moment identity. Their total negative mass then satisfies a quadratic
bound, and a nonnegative square gives the required coefficient. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Information.QutritMagicCoherenceBound

open D5.S3.Quantum.PureState.PureStateHandshake
open D5.S3.Quantum.Information.CorrelatedCoherenceMonogamyRefutation

/-- The nine qutrit Wigner entries, with zero-based phase-space indices. -/
noncomputable def wigner (ρ : Matrix (Fin 3) (Fin 3) ℂ) : Fin 3 → Fin 3 → ℝ :=
  fun p q =>
    ![![(ρ 0 0).re + 2 * (ρ 1 2).re,
        (ρ 1 1).re + 2 * (ρ 0 2).re,
        (ρ 2 2).re + 2 * (ρ 0 1).re],
      ![(ρ 0 0).re - (ρ 1 2).re - Real.sqrt 3 * (ρ 1 2).im,
        (ρ 1 1).re - (ρ 0 2).re + Real.sqrt 3 * (ρ 0 2).im,
        (ρ 2 2).re - (ρ 0 1).re - Real.sqrt 3 * (ρ 0 1).im],
      ![(ρ 0 0).re - (ρ 1 2).re + Real.sqrt 3 * (ρ 1 2).im,
        (ρ 1 1).re - (ρ 0 2).re - Real.sqrt 3 * (ρ 0 2).im,
        (ρ 2 2).re - (ρ 0 1).re + Real.sqrt 3 * (ρ 0 1).im]] p q / 3

/-- The sum negativity, in the normalization of Eq. (13). -/
noncomputable def sumNegativity (ρ : Matrix (Fin 3) (Fin 3) ℂ) : ℝ :=
  (∑ p, ∑ q, |wigner ρ p q|) - 1

/-- Eq. (18) for every normalized complex qutrit amplitude vector. -/
def claim : Prop := ∀ x : Fin 3 → ℂ, ∑ i, Complex.normSq (x i) = 1 →
  l1Coherence (rankOneDensity x) / 2 *
      Real.sqrt (1 - l1Coherence (rankOneDensity x) / 2) ≤
    sumNegativity (rankOneDensity x)

private noncomputable def negMass (a b c : ℝ) : ℝ :=
  max (-a) 0 + max (-b) 0 + max (-c) 0

/-- The second moment is at most the sum of the squared positive and negative masses. -/
private theorem parts_bound (a b c : ℝ) :
    a ^ 2 + b ^ 2 + c ^ 2 ≤ (a + b + c + negMass a b c) ^ 2 +
      (negMass a b c) ^ 2 := by
  have parts (z : ℝ) : z ^ 2 = (max z 0) ^ 2 + (max (-z) 0) ^ 2 := by
    rcases le_total 0 z with hz | hz
    · simp [max_eq_left hz, max_eq_right (neg_nonpos.mpr hz)]
    · simp [max_eq_right hz, max_eq_left (neg_nonneg.mpr hz)]
  have hp := Finset.sum_sq_le_sq_sum_of_nonneg
    (s := Finset.univ) (f := fun i : Fin 3 => max (![a, b, c] i) 0)
    (fun _ _ => le_max_right _ _)
  have hn := Finset.sum_sq_le_sq_sum_of_nonneg
    (s := Finset.univ) (f := fun i : Fin 3 => max (-(![a, b, c] i)) 0)
    (fun _ _ => le_max_right _ _)
  simp only [Fin.sum_univ_three] at hp hn
  change (max a 0) ^ 2 + (max b 0) ^ 2 + (max c 0) ^ 2 ≤
    (max a 0 + max b 0 + max c 0) ^ 2 at hp
  change (max (-a) 0) ^ 2 + (max (-b) 0) ^ 2 + (max (-c) 0) ^ 2 ≤
    (max (-a) 0 + max (-b) 0 + max (-c) 0) ^ 2 at hn
  have hsum : max a 0 + max b 0 + max c 0 =
      a + b + c + negMass a b c := by
    calc
      _ = (max a 0 - max (-a) 0) + (max b 0 - max (-b) 0) +
          (max c 0 - max (-c) 0) + negMass a b c := by rw [negMass.eq_1]; ring
      _ = _ := by
        change (posPart a - negPart a) + (posPart b - negPart b) +
          (posPart c - negPart c) + negMass a b c = _
        rw [posPart_sub_negPart, posPart_sub_negPart, posPart_sub_negPart]
  rw [hsum] at hp
  rw [negMass.eq_1] at *
  linarith [parts a, parts b, parts c]

/-- First and second column moments force negative mass when the off-diagonal radius exceeds `A`. -/
private theorem column_bound (A R α a b c : ℝ) (hA : 0 ≤ A) (hR : 0 ≤ R)
    (hα : 0 ≤ α) (hαsq : α ^ 2 = 3) (hsum : a + b + c = 3 * A)
    (hsq : a ^ 2 + b ^ 2 + c ^ 2 = 3 * A ^ 2 + 6 * R ^ 2) :
    α * max (R - A) 0 ≤ negMass a b c := by
  have hN : 0 ≤ negMass a b c := by rw [negMass.eq_1]; positivity
  have hconstant : 3 ≤ 2 * α := by nlinarith
  have hparts := parts_bound a b c
  rw [hsum, hsq] at hparts
  have hbase : 3 * R ^ 2 ≤ 3 * A ^ 2 + 3 * A * negMass a b c +
      (negMass a b c) ^ 2 := by nlinarith only [hparts]
  have hcross := mul_nonneg (by linarith : 0 ≤ 2 * α - 3) (mul_nonneg hA hN)
  have hcompare : (α * R) ^ 2 ≤ (α * A + negMass a b c) ^ 2 := by
    nlinarith only [hbase, hcross, hαsq]
  have hroot : α * R ≤ α * A + negMass a b c :=
    (sq_le_sq₀ (mul_nonneg hα hR) (by positivity)).mp hcompare
  rcases le_total R A with h | h
  · rw [max_eq_right (sub_nonpos.mpr h), mul_zero]
    exact hN
  · rw [max_eq_left (sub_nonneg.mpr h)]
    linarith

/-- Normalized nonnegative amplitudes give `D² + vD ≥ sv` for the three defects. -/
private theorem amplitude_bound (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hnorm : a ^ 2 + b ^ 2 + c ^ 2 = 1) :
    let s := a * b + a * c + b * c
    let v := 1 - s
    let D := negMass (a ^ 2 - b * c) (b ^ 2 - a * c) (c ^ 2 - a * b)
    0 ≤ s ∧ 0 ≤ v ∧ 0 ≤ D ∧ s * v ≤ D ^ 2 + v * D := by
  dsimp only
  have hs : 0 ≤ a * b + a * c + b * c := by positivity
  have hv : 0 ≤ 1 - (a * b + a * c + b * c) := by
    nlinarith only [hnorm, sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
  have hD : 0 ≤ negMass (a ^ 2 - b * c) (b ^ 2 - a * c) (c ^ 2 - a * b) := by
    rw [negMass.eq_1]
    positivity
  refine ⟨hs, hv, hD, ?_⟩
  have hid : (a ^ 2 - b * c) ^ 2 + (b ^ 2 - a * c) ^ 2 +
      (c ^ 2 - a * b) ^ 2 =
      (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 - (a * b + a * c + b * c) ^ 2 := by ring
  have hsum : (a ^ 2 - b * c) + (b ^ 2 - a * c) + (c ^ 2 - a * b) =
      1 - (a * b + a * c + b * c) := by linarith only [hnorm]
  have hparts := parts_bound (a ^ 2 - b * c) (b ^ 2 - a * c) (c ^ 2 - a * b)
  rw [hid, hnorm, hsum] at hparts
  nlinarith only [hparts]

/-- A square bounds the comparison root of the defect quadratic. -/
private theorem constant_bound (s v D α u : ℝ) (hs : 0 ≤ s) (hv : 0 ≤ v)
    (hD : 0 ≤ D) (hsv : s + v = 1) (hquad : s * v ≤ D ^ 2 + v * D)
    (hα : 0 ≤ α) (hαsq : α ^ 2 = 3) (hu : 0 ≤ u) (husq : u ^ 2 = v) :
    α / 2 * s * u ≤ D := by
  let T := α / 2 * s * u
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hid : s * v - (T ^ 2 + v * T) = s * v / 4 * (α * u - 1) ^ 2 := by
    dsimp only [T]
    rw [show s = 1 - v by linarith only [hsv]]
    ring_nf
    rw [hαsq, husq]
    ring
  have hsmall : T ^ 2 + v * T ≤ s * v := by
    nlinarith only [hid, mul_nonneg (by positivity : 0 ≤ s * v / 4)
      (sq_nonneg (α * u - 1))]
  change T ≤ D
  apply (sq_le_sq₀ hT hD).mp
  by_contra h
  have hsq : D ^ 2 < T ^ 2 := lt_of_not_ge h
  have hlt : D < T := (sq_lt_sq₀ hD hT).mp hsq
  have hmul := mul_le_mul_of_nonneg_left hlt.le hv
  nlinarith only [hsmall, hquad, hsq, hmul]

private theorem phase_column_bound (A R ell μ α : ℝ) (hA : 0 ≤ A) (hR : 0 ≤ R)
    (hα : 0 ≤ α) (hαsq : α ^ 2 = 3) (hphase : ell ^ 2 + μ ^ 2 = R ^ 2) :
    α * max (R - A) 0 ≤ negMass (A + 2 * ell) (A - ell - α * μ)
      (A - ell + α * μ) := by
  apply column_bound A R α _ _ _ hA hR hα hαsq (by ring)
  calc
    _ = 3 * A ^ 2 + 6 * ell ^ 2 + 2 * α ^ 2 * μ ^ 2 := by ring
    _ = 3 * A ^ 2 + 6 * R ^ 2 := by rw [hαsq]; nlinarith only [hphase]

/-- Pure-state entries identify half-coherence and bound negativity by amplitude defects. -/
private theorem pure_state_reduction (x : Fin 3 → ℂ)
    (hr : ‖x 0‖ ^ 2 + ‖x 1‖ ^ 2 + ‖x 2‖ ^ 2 = 1) :
    let s := ‖x 0‖ * ‖x 1‖ + ‖x 0‖ * ‖x 2‖ + ‖x 1‖ * ‖x 2‖
    let D := negMass (‖x 0‖ ^ 2 - ‖x 1‖ * ‖x 2‖)
      (‖x 1‖ ^ 2 - ‖x 0‖ * ‖x 2‖) (‖x 2‖ ^ 2 - ‖x 0‖ * ‖x 1‖)
    l1Coherence (rankOneDensity x) = 2 * s ∧
      (2 * Real.sqrt 3 / 3) * D ≤ sumNegativity (rankOneDensity x) := by
  let ρ := rankOneDensity x
  have hdiag (i : Fin 3) : (ρ i i).re = ‖x i‖ ^ 2 := by
    change (x i * star (x i)).re = ‖x i‖ ^ 2
    simp only [Complex.star_def, Complex.mul_conj, Complex.ofReal_re,
      Complex.normSq_eq_norm_sq]
  have hentry (j k : Fin 3) : (ρ j k).re ^ 2 + (ρ j k).im ^ 2 =
      (‖x j‖ * ‖x k‖) ^ 2 := by
    calc
      _ = Complex.normSq (ρ j k) := by rw [Complex.normSq_apply]; ring
      _ = (‖x j‖ * ‖x k‖) ^ 2 := by
        rw [Complex.normSq_eq_norm_sq]
        change ‖x j * star (x k)‖ ^ 2 = _
        rw [norm_mul, norm_star]
  have hcoherence : l1Coherence (rankOneDensity x) =
      2 * (‖x 0‖ * ‖x 1‖ + ‖x 0‖ * ‖x 2‖ + ‖x 1‖ * ‖x 2‖) := by
    norm_num [l1Coherence.eq_1, Fin.sum_univ_three, rankOneDensity.eq_1,
      Matrix.vecMulVec_apply, Pi.star_apply, norm_mul, norm_star]
    ring
  refine ⟨hcoherence, ?_⟩
  let N0 := negMass (‖x 0‖ ^ 2 + 2 * (ρ 1 2).re)
    (‖x 0‖ ^ 2 - (ρ 1 2).re - Real.sqrt 3 * (ρ 1 2).im)
    (‖x 0‖ ^ 2 - (ρ 1 2).re + Real.sqrt 3 * (ρ 1 2).im)
  let N1 := negMass (‖x 1‖ ^ 2 + 2 * (ρ 0 2).re)
    (‖x 1‖ ^ 2 - (ρ 0 2).re + Real.sqrt 3 * (ρ 0 2).im)
    (‖x 1‖ ^ 2 - (ρ 0 2).re - Real.sqrt 3 * (ρ 0 2).im)
  let N2 := negMass (‖x 2‖ ^ 2 + 2 * (ρ 0 1).re)
    (‖x 2‖ ^ 2 - (ρ 0 1).re - Real.sqrt 3 * (ρ 0 1).im)
    (‖x 2‖ ^ 2 - (ρ 0 1).re + Real.sqrt 3 * (ρ 0 1).im)
  have hN0 : Real.sqrt 3 * max (‖x 1‖ * ‖x 2‖ - ‖x 0‖ ^ 2) 0 ≤ N0 :=
    phase_column_bound _ _ _ _ _ (sq_nonneg _) (by positivity)
      (Real.sqrt_nonneg _) (Real.sq_sqrt (by norm_num)) (hentry 1 2)
  have hN1 : Real.sqrt 3 * max (‖x 0‖ * ‖x 2‖ - ‖x 1‖ ^ 2) 0 ≤ N1 := by
    have h := phase_column_bound (‖x 1‖ ^ 2) (‖x 0‖ * ‖x 2‖)
      (ρ 0 2).re (ρ 0 2).im (Real.sqrt 3) (sq_nonneg _) (by positivity)
      (Real.sqrt_nonneg _) (Real.sq_sqrt (by norm_num)) (hentry 0 2)
    simpa only [N1, negMass.eq_1, add_right_comm] using h
  have hN2 : Real.sqrt 3 * max (‖x 0‖ * ‖x 1‖ - ‖x 2‖ ^ 2) 0 ≤ N2 :=
    phase_column_bound _ _ _ _ _ (sq_nonneg _) (by positivity)
      (Real.sqrt_nonneg _) (Real.sq_sqrt (by norm_num)) (hentry 0 1)
  have habs (z : ℝ) : |z| = z + 2 * max (-z) 0 := by
    simpa only [nsmul_eq_mul, Nat.cast_ofNat, negPart_def, add_comm] using
      (sub_eq_iff_eq_add.mp (abs_sub_eq_two_nsmul_negPart z))
  have hmass : sumNegativity ρ = (2 / 3 : ℝ) * (N0 + N1 + N2) := by
    simp only [sumNegativity.eq_1, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero,
      wigner.eq_1, Matrix.cons_val_zero, Matrix.cons_val_succ, hdiag]
    simp only [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    simp only [habs, N0, N1, N2, negMass.eq_1]
    nlinarith only [hr]
  change (2 * Real.sqrt 3 / 3) *
    negMass (‖x 0‖ ^ 2 - ‖x 1‖ * ‖x 2‖) (‖x 1‖ ^ 2 - ‖x 0‖ * ‖x 2‖)
      (‖x 2‖ ^ 2 - ‖x 0‖ * ‖x 1‖) ≤ sumNegativity ρ
  rw [hmass, negMass.eq_1]
  simp only [neg_sub]
  linarith only [hN0, hN1, hN2]

/-- The pure-qutrit magic–coherence lower bound. -/
theorem result : claim := by
  intro x hnorm
  let s := ‖x 0‖ * ‖x 1‖ + ‖x 0‖ * ‖x 2‖ + ‖x 1‖ * ‖x 2‖
  let v := 1 - s
  let D := negMass (‖x 0‖ ^ 2 - ‖x 1‖ * ‖x 2‖)
    (‖x 1‖ ^ 2 - ‖x 0‖ * ‖x 2‖) (‖x 2‖ ^ 2 - ‖x 0‖ * ‖x 1‖)
  have hr : ‖x 0‖ ^ 2 + ‖x 1‖ ^ 2 + ‖x 2‖ ^ 2 = 1 := by
    simpa only [Fin.sum_univ_three, Complex.normSq_eq_norm_sq] using hnorm
  obtain ⟨hs, hv, hD, hquad⟩ := amplitude_bound _ _ _
    (norm_nonneg (x 0)) (norm_nonneg (x 1)) (norm_nonneg (x 2)) hr
  have hconstant : Real.sqrt 3 / 2 * s * Real.sqrt v ≤ D :=
    constant_bound s v D (Real.sqrt 3) (Real.sqrt v) hs hv hD (by dsimp [v]; ring)
      hquad (Real.sqrt_nonneg _) (Real.sq_sqrt (by norm_num))
      (Real.sqrt_nonneg _) (Real.sq_sqrt hv)
  obtain ⟨hcoherence, hmagic⟩ := pure_state_reduction x hr
  have hscaled := mul_le_mul_of_nonneg_left hconstant
    (by positivity : 0 ≤ 2 * Real.sqrt 3 / 3)
  have hcancel : (2 * Real.sqrt 3 / 3) *
      (Real.sqrt 3 / 2 * s * Real.sqrt v) = s * Real.sqrt v := by
    ring_nf
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    ring
  rw [hcancel] at hscaled
  rw [hcoherence]
  change (2 * s) / 2 * Real.sqrt (1 - (2 * s) / 2) ≤ _
  have hhalf : (2 * s) / 2 = s := mul_div_cancel_left₀ s (by norm_num)
  rw [hhalf]
  exact hscaled.trans hmagic

end D5.S3.Quantum.Information.QutritMagicCoherenceBound
