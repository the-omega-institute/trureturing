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
arXiv:1801.04807v3, Eq. (18), for the Wigner convention of Eq. (12). -/

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

private theorem parts_bound (a b c : ℝ) :
    a ^ 2 + b ^ 2 + c ^ 2 ≤ (a + b + c + negMass a b c) ^ 2 +
      (negMass a b c) ^ 2 := by
  have parts (z : ℝ) : z + max (-z) 0 = max z 0 ∧
      z ^ 2 = (max z 0) ^ 2 + (max (-z) 0) ^ 2 := by
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
    rw [negMass.eq_1]
    linarith [(parts a).1, (parts b).1, (parts c).1]
  rw [hsum] at hp
  rw [negMass.eq_1] at *
  linarith [(parts a).2, (parts b).2, (parts c).2]

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

/-- The pure-qutrit magic–coherence lower bound. -/
theorem result : claim := by
  sorry

end D5.S3.Quantum.Information.QutritMagicCoherenceBound
