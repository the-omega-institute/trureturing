/- GID: D5/S3/Quantum/Measurements/ThreeDistinguishabilityProductRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurements/ThreeDistinguishabilityProductRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Measurements/ThreeDistinguishabilityProductRefutation.claim; result=D5/S3/Quantum/Measurements/ThreeDistinguishabilityProductRefutation.result; claim=D5/S3/Quantum/Measurements/ThreeDistinguishabilityProductRefutation.claim
   digest: Three orthogonal pure states exclude every labelling of the product ansatz. -/

import D5.S3.Combinatorics.PerfectMatchings.FiniteBandSwitch
import D5.S0.Carrier.GoldenRatio
import D5.S3.Analytic.Adelic.FiniteToroidalFrameReconstruction
import D5.S3.Quantum.PureState.PureStateHandshake
import D5.S3.Quantum.Dynamics.PositivePauliClockOrder
import D5.S3.Observer.WindowRegister
import D5.S3.QuantumBounds.RebitExclusionDistance

/-! Korzekwa, Czachórski, Puchała and Życzkowski, arXiv:1812.09083v3,
Equation (30). Classical versions are the real diagonals in the preferred basis;
perfect distinguishability is pairwise orthogonality of density-matrix supports. -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators ComplexConjugate ComplexOrder

open D5.S3.Quantum.PureState.PureStateHandshake (rankOneDensity)
open D5.S3.Analytic.Adelic.FiniteToroidalFrameReconstruction (weightedFrame)
open D5.S3.Observer.WindowRegister (windowRoot windowRoot_isPrimitiveRoot)

open D5.S3.Combinatorics.PerfectMatchings.FiniteBandSwitch.FourEndpoint
  (J0 J1 thirdPairing pairing_three_forms)

namespace D5.S3.Quantum.Measurements.ThreeDistinguishabilityProductRefutation

/-- The source's three-distinguishability region, with classical version `diag ρ`. -/
def InRegion (p : Fin 4 → ℝ) : Prop :=
  ((∀ k, 0 ≤ p k) ∧ ∑ k, p k = 1) ∧
    ∃ ρ : Fin 3 → Matrix (Fin 4) (Fin 4) ℂ,
      (∀ i, (ρ i).PosSemidef ∧ Matrix.trace (ρ i) = 1) ∧
      (∀ i j, i ≠ j → ρ i * ρ j = 0) ∧
      ∀ i k, (Matrix.diag (ρ i) k).re = p k

/-- The product ansatz with two independent parameters in the unit interval. -/
def ProductForm (f : Fin 4 → Fin 4 → ℝ) (p : Fin 4 → ℝ) : Prop :=
  ∃ a b : ℝ, 0 ≤ a ∧ a ≤ 1 ∧ 0 ≤ b ∧ b ≤ 1 ∧
    p = (a * b) • f 0 + (a * (1 - b)) • f 1 +
      ((1 - a) * b) • f 2 + ((1 - a) * (1 - b)) • f 3

/-- Equation (30), allowing any labelling of the four face centres. -/
def claim : Prop :=
  ∃ σ : Equiv.Perm (Fin 4), ∀ p, InRegion p →
    ProductForm (fun i => D5.S3.QuantumBounds.RebitExclusionDistance.target (σ i)) p

private def point : Fin 4 → ℝ :=
  ![(5 - Real.sqrt 5) / 10, (5 - Real.sqrt 5) / 20,
    (5 - Real.sqrt 5) / 10, (Real.sqrt 5 - 1) / 4]

private def ζ : ℂ := windowRoot 10

private def phases : Fin 3 → Fin 4 → ℂ :=
  ![![1, 1, 1, 1], ![1, ζ ^ 2, ζ ^ 4, ζ ^ 7], ![-1, ζ ^ 9, ζ ^ 3, ζ ^ 9]]

private def state (i : Fin 3) (k : Fin 4) : ℂ :=
  weightedFrame (Finset.univ : Finset (Fin 4)) point
    (fun k _ => phases i k) 0 ⟨k, Finset.mem_univ k⟩

private lemma point_simplex : (∀ k, 0 ≤ point k) ∧ ∑ k, point k = 1 := by
  constructor
  · intro k
    fin_cases k <;> norm_num [point] <;>
      nlinarith [show (1 : ℝ) < (1 + Real.sqrt 5) / 2 by
        simpa only [Real.goldenRatio] using Real.one_lt_goldenRatio,
        show (1 + Real.sqrt 5) / 2 < (2 : ℝ) by
          simpa only [Real.goldenRatio] using Real.goldenRatio_lt_two]
  · norm_num [point, Fin.sum_univ_succ]
    ring

private lemma phase_unit : conj ζ * ζ = 1 := by
  rw [show ζ = Complex.exp ((Real.pi / 5 : ℝ) * Complex.I) by
    dsimp only [ζ, windowRoot]; congr 1; push_cast; ring]
  simpa only [Complex.star_def, Complex.ofReal_neg, mul_neg, neg_mul, neg_neg,
    mul_comm] using
    D5.S3.Quantum.Dynamics.PositivePauliClockOrder.phase_unit (-(Real.pi / 5))

private lemma phase_fifth : ζ ^ 5 = -1 := by
  exact IsPrimitiveRoot.eq_neg_one_of_two_right
    ((windowRoot_isPrimitiveRoot 10).pow_of_dvd (p := 5) (by decide) (by decide))

private lemma phase_quadratic : ζ ^ 2 = ((1 + Real.sqrt 5 : ℝ) / 2 : ℂ) * ζ - 1 := by
  have hr : ζ.re = (1 + Real.sqrt 5) / 4 := by
    rw [show ζ = Complex.exp ((Real.pi / 5 : ℝ) * Complex.I) by
      dsimp only [ζ, windowRoot]; congr 1; push_cast; ring, Complex.exp_ofReal_mul_I_re]
    exact Real.cos_pi_div_five
  have hs : conj ζ + ζ = ((1 + Real.sqrt 5 : ℝ) / 2 : ℂ) := by
    rw [add_comm, Complex.add_conj, hr]
    push_cast
    ring
  linear_combination ζ * hs - phase_unit

private lemma phases_unit (i : Fin 3) (k : Fin 4) :
    conj (phases i k) * phases i k = 1 := by
  fin_cases i <;> fin_cases k <;> norm_num [phases] <;>
    rw [← mul_pow, phase_unit, one_pow]

private lemma phase_powers :
    let t : ℂ := ((1 + Real.sqrt 5 : ℝ) / 2 : ℂ)
    ζ ^ 3 = t * ζ - t ∧ ζ ^ 4 = ζ - t ∧ ζ ^ 7 = 1 - t * ζ ∧
      ζ ^ 9 = t - ζ ∧ conj ζ = t - ζ := by
  let t : ℂ := ((1 + Real.sqrt 5 : ℝ) / 2 : ℂ)
  have ht : t ^ 2 = t + 1 := by
    have hg : (Real.goldenRatio : ℂ) ^ 2 = (Real.goldenRatio : ℂ) + 1 := by
      exact_mod_cast D5.S0.Carrier.golden_ratio_spec.2.1
    simpa only [t, Real.goldenRatio, Complex.ofReal_div, Complex.ofReal_ofNat] using hg
  have h2 : ζ ^ 2 = t * ζ - 1 := phase_quadratic
  have h3 : ζ ^ 3 = t * ζ - t := by
    linear_combination (ζ + t) * h2 + ζ * ht
  have h4 : ζ ^ 4 = ζ - t := by
    linear_combination ζ * h3 + t * h2 + ζ * ht
  have h7 : ζ ^ 7 = 1 - t * ζ := by
    calc
      ζ ^ 7 = ζ ^ 5 * ζ ^ 2 := pow_add ζ 5 2
      _ = 1 - t * ζ := by rw [phase_fifth, h2]; ring
  have h9 : ζ ^ 9 = t - ζ := by
    calc
      ζ ^ 9 = ζ ^ 5 * ζ ^ 4 := pow_add ζ 5 4
      _ = t - ζ := by rw [phase_fifth, h4]; ring
  have hc : conj ζ = t - ζ := by
    have hz : ζ ≠ 0 := Complex.exp_ne_zero _
    apply mul_right_cancel₀ hz
    linear_combination phase_unit + h2
  exact ⟨h3, h4, h7, h9, hc⟩

private lemma weighted_orthogonality (i j : Fin 3) (h : i ≠ j) :
    ∑ k, (point k : ℂ) * (conj (phases i k) * phases j k) = 0 := by
  rcases phase_powers with ⟨h3, h4, h7, h9, hc⟩
  have h2 := phase_quadratic
  have hr : (Real.sqrt 5 : ℂ) ^ 2 = 5 := by
    exact_mod_cast Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  fin_cases i <;> fin_cases j
  all_goals try exact (h rfl).elim
  all_goals
    simp only [point.eq_1, phases.eq_1, Fin.sum_univ_succ, Matrix.cons_val_zero,
      Matrix.cons_val_succ, Matrix.cons_val_fin_one]
    simp only [h2, h3, h4, h7, h9]
    push_cast
    norm_num only [map_ofNat]
    ring_nf
  all_goals
    try simp only [map_one, map_neg, map_add, map_mul, map_sub, map_ofNat,
      map_div₀, Complex.conj_ofReal, hc]
    ring_nf
  all_goals
    have hr3 : (Real.sqrt 5 : ℂ) ^ 3 = 5 * (Real.sqrt 5 : ℂ) := by
      rw [pow_succ, hr]
    simp only [hr, hr3]
    ring_nf
  all_goals
    rw [h2]
    push_cast
    ring_nf; simp only [hr]; ring

private lemma state_diagonal (i : Fin 3) (k : Fin 4) :
    state i k * conj (state i k) = (point k : ℂ) := by
  have hs : (Real.sqrt (point k) : ℂ) ^ 2 = (point k : ℂ) := by
    exact_mod_cast Real.sq_sqrt (point_simplex.1 k)
  have hp := phases_unit i k
  dsimp only [state, weightedFrame]
  rw [map_mul, Complex.conj_ofReal]
  calc
    _ = (Real.sqrt (point k) : ℂ) ^ 2 *
        (conj (phases i k) * phases i k) := by ring
    _ = (point k : ℂ) := by rw [hs, hp, mul_one]

private lemma state_orthogonality (i j : Fin 3) (h : i ≠ j) :
    star (state i) ⬝ᵥ state j = 0 := by
  change ∑ k, conj (state i k) * state j k = 0
  convert weighted_orthogonality i j h using 1
  apply Finset.sum_congr rfl
  intro k _
  have hs : (Real.sqrt (point k) : ℂ) ^ 2 = (point k : ℂ) := by
    exact_mod_cast Real.sq_sqrt (point_simplex.1 k)
  dsimp only [state, weightedFrame]
  rw [map_mul, Complex.conj_ofReal]
  calc
    _ = (Real.sqrt (point k) : ℂ) ^ 2 *
        (conj (phases i k) * phases j k) := by ring
    _ = _ := by rw [hs]

private lemma density_region : InRegion point := by
  refine ⟨point_simplex, fun i => rankOneDensity (state i), ?_, ?_, ?_⟩
  · intro i
    refine ⟨Matrix.posSemidef_vecMulVec_self_star (state i), ?_⟩
    change Matrix.trace (Matrix.vecMulVec (state i) (star (state i))) = 1
    rw [Matrix.trace_vecMulVec]
    change ∑ k, state i k * conj (state i k) = 1
    simp only [state_diagonal, ← Complex.ofReal_sum, point_simplex.2, Complex.ofReal_one]
  · intro i j h
    dsimp only [rankOneDensity]
    rw [Matrix.vecMulVec_mul_vecMulVec, state_orthogonality i j h, zero_smul]
    exact Matrix.vecMulVec_zero _
  · intro i k
    change (state i k * conj (state i k)).re = point k
    rw [state_diagonal, Complex.ofReal_re]

private lemma product_pairing (σ : Equiv.Perm (Fin 4)) (p : Fin 4 → ℝ)
    (h : ProductForm
      (fun i => D5.S3.QuantumBounds.RebitExclusionDistance.target (σ i)) p) :
    (1 - 3 * p (σ 0)) * (1 - 3 * p (σ 3)) =
      (1 - 3 * p (σ 1)) * (1 - 3 * p (σ 2)) := by
  rcases h with ⟨a, b, _, _, _, _, hp⟩
  have hv (i : Fin 4) := congrFun hp (σ i)
  have hv0 := hv 0
  have hv1 := hv 1
  have hv2 := hv 2
  have hv3 := hv 3
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    D5.S3.QuantumBounds.RebitExclusionDistance.target.eq_1,
    Equiv.apply_eq_iff_eq, Fin.isValue, ite_true, Fin.zero_eq_one_iff,
    Fin.reduceEq, ite_false, mul_zero, zero_add, add_zero] at hv0 hv1 hv2 hv3
  norm_num only at hv0 hv1 hv2 hv3
  simp only [ite_false] at hv1
  rw [hv0, hv1, hv2, hv3]
  ring

private lemma permutation_pairing (σ : Equiv.Perm (Fin 4)) (q : Fin 4 → ℝ)
    (h : q (σ 0) * q (σ 3) = q (σ 1) * q (σ 2)) :
    q 0 * q 1 = q 2 * q 3 ∨ q 0 * q 2 = q 1 * q 3 ∨
      q 0 * q 3 = q 1 * q 2 := by
  let P := σ.permCongr J1
  have hJinv : J1⁻¹ = J1 := by
    ext i
    fin_cases i <;> rfl
  have hfree : ∀ i : Fin 4, J1 i ≠ i := by
    intro i
    fin_cases i <;> decide
  have hPinv : P⁻¹ = P := by
    change (σ.permCongrHom J1)⁻¹ = σ.permCongrHom J1
    rw [← map_inv, hJinv]
  have hP : Function.Involutive P := by
    intro i
    exact (congrArg (fun f : Equiv.Perm (Fin 4) => f (P i)) hPinv.symm).trans
      (P.symm_apply_apply i)
  have hPfree : ∀ i, P i ≠ i := by
    intro i
    simpa only [P, Equiv.permCongr_apply, Equiv.apply_symm_apply] using
      σ.injective.ne (hfree (σ.symm i))
  have hp (i : Fin 4) : q i * q (P i) = q (σ 0) * q (σ 3) := by
    obtain ⟨j, rfl⟩ := σ.surjective i
    fin_cases j
    · simp [P, J1, Equiv.Perm.mul_apply,
        Equiv.swap_apply_def]
    · simpa [P, Equiv.permCongr_apply, J1, Equiv.Perm.mul_apply,
        Equiv.swap_apply_def] using h.symm
    · simpa [P, Equiv.permCongr_apply, J1, Equiv.Perm.mul_apply,
        Equiv.swap_apply_def, mul_comm] using h.symm
    · simp [P, J1, Equiv.Perm.mul_apply,
        Equiv.swap_apply_def, mul_comm]
  rcases pairing_three_forms P hP hPfree with h0 | h0 | h0
  · right; left
    simpa [h0, J0, Equiv.Perm.mul_apply, Equiv.swap_apply_def] using
      (hp 0).trans (hp 1).symm
  · left
    simpa [h0, thirdPairing, Equiv.Perm.mul_apply, Equiv.swap_apply_def] using
      (hp 0).trans (hp 2).symm
  · right; right
    simpa [h0, J1, Equiv.Perm.mul_apply, Equiv.swap_apply_def] using
      (hp 0).trans (hp 1).symm

private lemma point_pairings :
    let q := fun k => 1 - 3 * point k
    q 0 * q 1 ≠ q 2 * q 3 ∧ q 0 * q 2 ≠ q 1 * q 3 ∧
      q 0 * q 3 ≠ q 1 * q 2 := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    change (1 - 3 * ((5 - Real.sqrt 5) / 10)) *
        (1 - 3 * ((5 - Real.sqrt 5) / 20)) =
      (1 - 3 * ((5 - Real.sqrt 5) / 10)) *
        (1 - 3 * ((Real.sqrt 5 - 1) / 4)) at h
    apply (Nat.Prime.irrational_sqrt (by decide : Nat.Prime 5)).ne_rat (7 / 3 : ℚ)
    norm_num
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
  · intro h
    change (1 - 3 * ((5 - Real.sqrt 5) / 10)) *
        (1 - 3 * ((5 - Real.sqrt 5) / 10)) =
      (1 - 3 * ((5 - Real.sqrt 5) / 20)) *
        (1 - 3 * ((Real.sqrt 5 - 1) / 4)) at h
    apply (Nat.Prime.irrational_sqrt (by decide : Nat.Prime 5)).ne_rat (11 / 5 : ℚ)
    norm_num
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
  · intro h
    change (1 - 3 * ((5 - Real.sqrt 5) / 10)) *
        (1 - 3 * ((Real.sqrt 5 - 1) / 4)) =
      (1 - 3 * ((5 - Real.sqrt 5) / 20)) *
        (1 - 3 * ((5 - Real.sqrt 5) / 10)) at h
    apply (Nat.Prime.irrational_sqrt (by decide : Nat.Prime 5)).ne_rat (7 / 3 : ℚ)
    norm_num
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]

private lemma point_not_product (σ : Equiv.Perm (Fin 4)) :
    ¬ ProductForm
      (fun i => D5.S3.QuantumBounds.RebitExclusionDistance.target (σ i)) point := by
  intro h
  rcases permutation_pairing σ (fun k => 1 - 3 * point k) (product_pairing σ point h)
    with h | h | h
  · exact point_pairings.1 h
  · exact point_pairings.2.1 h
  · exact point_pairings.2.2 h

/-- No labelling makes the product ansatz contain the three-distinguishability region. -/
theorem result : ¬ claim := by
  rintro ⟨σ, h⟩
  exact point_not_product σ (h point density_region)

end D5.S3.Quantum.Measurements.ThreeDistinguishabilityProductRefutation
