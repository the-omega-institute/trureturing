/- GID: D5/S3/Quantum/Analysis/NullConeGravity/NonperturbativePhaseResummation
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/NullConeGravity/NonperturbativePhaseResummation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite-coupling phase resummation versus cubic harmonic divergence at zero coupling. -/

import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.PSeries
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Nonperturbative Phase Resummation versus Perturbative Harmonic Divergence

Motivated by the graviton pair-creation amplitude on a null cone in Chandrasekaran
(arXiv:2611.34924v1, Section 4.4, Eqs. 4.33–4.34), this module formalizes the exact
non-commutativity between summing over arbitrarily short radial modes at finite coupling
`g = 1/s = 4 G_N ħ / A > 0` and expanding perturbatively in `g` around `g = 0`:

1. For every real `g`, the mode series `∑_{k=0}^∞ (g² / 2) exp(-2 i (k + 1) g) / (k + 1)²`
   converges absolutely with uniform norm bound `‖∑' k, modeTerm g k‖ ≤ g²`.
2. For every finite mode cutoff `N`, the exact third-order perturbative coefficient at `g = 0`
   satisfies `(1 / 6) * iteratedDeriv 3 (partialPhaseSum N) 0 = -i * ∑_{k < N} 1 / (k + 1)`.
3. As `N → ∞`, the magnitude of this cubic perturbative coefficient diverges to `+∞` like the
   harmonic series, even though the resummed series stays uniformly bounded by `g²` for every `g`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped BigOperators
open Filter

namespace D5.S3.Quantum.Analysis.NullConeGravity.NonperturbativePhaseResummation

/-- The `k`-th radial mode term `(g² / 2) * exp(-2 i (k + 1) g) / (k + 1)²` at coupling `g`. -/
def modeTerm (g : ℝ) (k : ℕ) : ℂ :=
  ((g ^ 2 / 2 : ℝ) : ℂ) *
    Complex.exp (-2 * Complex.I * ((k + 1 : ℕ) : ℂ) * (g : ℂ)) /
    (((k + 1 : ℕ) : ℂ) ^ 2)

/-- The `N`-mode partial sum `F_N(g) = ∑_{k < N} modeTerm g k`. -/
def partialPhaseSum (N : ℕ) (g : ℝ) : ℂ :=
  ∑ k ∈ Finset.range N, modeTerm g k

/-- Elementary telescoping bound `∑_{k < N} 1 / (k + 1)² ≤ 2`. -/
private lemma sum_inv_sq_le_two (N : ℕ) :
    ∑ k ∈ Finset.range N, (1 : ℝ) / ((k + 1 : ℕ) : ℝ) ^ 2 ≤ 2 := by
  have hstrong : ∀ n : ℕ, 1 ≤ n →
      ∑ k ∈ Finset.range n, (1 : ℝ) / ((k + 1 : ℕ) : ℝ) ^ 2 ≤ 2 - 1 / (n : ℝ) := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base =>
      simp
      norm_num
    | succ m hm ih =>
      rw [Finset.sum_range_succ]
      have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (by omega)
      have hm1_pos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
      have hstep :
          (1 : ℝ) / ((m + 1 : ℕ) : ℝ) ^ 2 ≤ 1 / (m : ℝ) - 1 / ((m + 1 : ℕ) : ℝ) := by
        have heq :
            (1 : ℝ) / (m : ℝ) - 1 / ((m + 1 : ℕ) : ℝ) =
              1 / ((m : ℝ) * ((m + 1 : ℕ) : ℝ)) := by
          field_simp [hm_pos.ne', hm1_pos.ne']
          push_cast
          ring
        rw [heq]
        apply one_div_le_one_div_of_le (mul_pos hm_pos hm1_pos)
        have hle : (m : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by
          push_cast
          linarith
        nlinarith [hm1_pos]
      linarith
  cases N with
  | zero =>
    simp
  | succ m =>
    have h1 := hstrong (m + 1) (Nat.succ_pos m)
    have hpos : (0 : ℝ) ≤ 1 / ((m + 1 : ℕ) : ℝ) := by positivity
    linarith

/-- Norm of the `k`-th mode term equals `(g² / 2) / (k + 1)²`. -/
private lemma norm_modeTerm (g : ℝ) (k : ℕ) :
    ‖modeTerm g k‖ = (g ^ 2 / 2) * (1 / ((k + 1 : ℕ) : ℝ) ^ 2) := by
  unfold modeTerm
  rw [norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity : 0 ≤ g ^ 2 / 2)]
  have hexp : ‖Complex.exp (-2 * Complex.I * ((k + 1 : ℕ) : ℂ) * (g : ℂ))‖ = 1 := by
    have harg :
        -2 * Complex.I * ((k + 1 : ℕ) : ℂ) * (g : ℂ) =
          (((-2 * ((k + 1 : ℕ) : ℝ) * g : ℝ) : ℂ) * Complex.I) := by
      push_cast
      ring
    rw [harg, Complex.norm_exp_ofReal_mul_I]
  rw [hexp, mul_one, norm_pow, Complex.norm_natCast]
  ring

/-- Absolute convergence and uniform `g²` bound for the nonperturbative phase-resummed series at
every real coupling `g`. -/
theorem summable_and_norm_le_modeTerm (g : ℝ) :
    Summable (modeTerm g) ∧ ‖∑' k : ℕ, modeTerm g k‖ ≤ g ^ 2 := by
  have hinv_sum : Summable (fun k : ℕ => (1 : ℝ) / ((k + 1 : ℕ) : ℝ) ^ 2) := by
    have hp : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) := by simp
    exact hp.comp_injective Nat.succ_injective
  have hnorm_sum : Summable (fun k : ℕ => ‖modeTerm g k‖) := by
    simp_rw [norm_modeTerm]
    exact hinv_sum.mul_left (g ^ 2 / 2)
  have hsum : Summable (modeTerm g) := hnorm_sum.of_norm
  have htsum_inv : ∑' k : ℕ, (1 : ℝ) / ((k + 1 : ℕ) : ℝ) ^ 2 ≤ 2 := by
    apply Real.tsum_le_of_sum_range_le (fun _ => by positivity)
    exact sum_inv_sq_le_two
  refine ⟨hsum, ?_⟩
  calc
    ‖∑' k : ℕ, modeTerm g k‖ ≤ ∑' k : ℕ, ‖modeTerm g k‖ := norm_tsum_le_tsum_norm hnorm_sum
    _ = ∑' k : ℕ, (g ^ 2 / 2) * (1 / ((k + 1 : ℕ) : ℝ) ^ 2) := by simp_rw [norm_modeTerm]
    _ = (g ^ 2 / 2) * ∑' k : ℕ, (1 : ℝ) / ((k + 1 : ℕ) : ℝ) ^ 2 := tsum_mul_left
    _ ≤ (g ^ 2 / 2) * 2 := mul_le_mul_of_nonneg_left htsum_inv (by positivity)
    _ = g ^ 2 := by ring

/-- Exact derivative formula for a single radial mode `g ↦ modeTerm g k`. -/
private lemma hasDerivAt_modeTerm_triple (k : ℕ) :
    let m : ℂ := ((k + 1 : ℕ) : ℂ)
    let e : ℝ → ℂ := fun g => Complex.exp (-2 * Complex.I * m * (g : ℂ))
    let f0 : ℝ → ℂ := fun g => modeTerm g k
    let f1 : ℝ → ℂ := fun g => (((g : ℂ) / m ^ 2) - Complex.I * (g : ℂ) ^ 2 / m) * e g
    let f2 : ℝ → ℂ := fun g =>
      ((1 / m ^ 2) - 4 * Complex.I * (g : ℂ) / m - 2 * (g : ℂ) ^ 2) * e g
    let f3 : ℝ → ℂ := fun g =>
      ((-6 * Complex.I / m) - 12 * (g : ℂ) + 4 * Complex.I * m * (g : ℂ) ^ 2) * e g
    (∀ g : ℝ, HasDerivAt f0 (f1 g) g) ∧
    (∀ g : ℝ, HasDerivAt f1 (f2 g) g) ∧
    (∀ g : ℝ, HasDerivAt f2 (f3 g) g) := by
  intro m e f0 f1 f2 f3
  have hm0 : m ≠ 0 := by
    dsimp [m]
    exact_mod_cast Nat.succ_ne_zero k
  have hc_ofReal : ∀ g : ℝ, HasDerivAt (fun x : ℝ => (x : ℂ)) 1 g := fun g =>
    Complex.ofRealCLM.hasDerivAt
  have he_deriv : ∀ g : ℝ, HasDerivAt e ((-2 * Complex.I * m) * e g) g := by
    intro g
    have hlin : HasDerivAt (fun x : ℝ => -2 * Complex.I * m * (x : ℂ))
        (-2 * Complex.I * m) g := by
      simpa using (hc_ofReal g).const_mul (-2 * Complex.I * m)
    have hexp := hlin.cexp
    convert hexp using 1
    dsimp [e]
    ring
  have hsq : ∀ g : ℝ, HasDerivAt (fun x : ℝ => (x : ℂ) ^ 2) (2 * (g : ℂ)) g := by
    intro g
    have hm := (hc_ofReal g).mul (hc_ofReal g)
    have hfun : (fun x : ℝ => (x : ℂ) ^ 2) = fun x : ℝ => (x : ℂ) * (x : ℂ) := by
      ext x
      ring
    rw [hfun]
    exact hm.congr_deriv (by ring)
  refine ⟨?_, ?_, ?_⟩
  · -- f0' = f1
    intro g
    have hcoeff :
        HasDerivAt (fun x : ℝ => ((x : ℂ) ^ 2 / (2 * m ^ 2))) ((g : ℂ) / m ^ 2) g := by
      exact ((hsq g).div_const (2 * m ^ 2)).congr_deriv (by field_simp [hm0])
    have hprod := hcoeff.mul (he_deriv g)
    have hf0_eq : f0 = fun x : ℝ => ((x : ℂ) ^ 2 / (2 * m ^ 2)) * e x := by
      ext x
      dsimp [f0, modeTerm, m, e]
      push_cast
      field_simp [hm0]
    rw [hf0_eq]
    refine hprod.congr_deriv ?_
    dsimp [f1]
    field_simp [hm0]
    ring
  · -- f1' = f2
    intro g
    have h1 : HasDerivAt (fun x : ℝ => (x : ℂ) / m ^ 2) (1 / m ^ 2) g :=
      (hc_ofReal g).div_const (m ^ 2)
    have h2 : HasDerivAt (fun x : ℝ => Complex.I * (x : ℂ) ^ 2 / m)
        (2 * Complex.I * (g : ℂ) / m) g :=
      (((hsq g).const_mul Complex.I).div_const m).congr_deriv (by ring)
    have hprod := (h1.sub h2).mul (he_deriv g)
    refine hprod.congr_deriv ?_
    dsimp [f2]
    field_simp [hm0]
    have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
    linear_combination (2 * (g : ℂ) ^ 2 * m ^ 2 * e g) * hI2
  · -- f2' = f3
    intro g
    have h0 : HasDerivAt (fun _ : ℝ => (1 : ℂ) / m ^ 2) 0 g := hasDerivAt_const g _
    have h1 : HasDerivAt (fun x : ℝ => 4 * Complex.I * (x : ℂ) / m)
        (4 * Complex.I / m) g :=
      (((hc_ofReal g).const_mul (4 * Complex.I)).div_const m).congr_deriv (by ring)
    have h2 : HasDerivAt (fun x : ℝ => 2 * (x : ℂ) ^ 2) (4 * (g : ℂ)) g :=
      ((hsq g).const_mul (2 : ℂ)).congr_deriv (by ring)
    have hprod := ((h0.sub h1).sub h2).mul (he_deriv g)
    refine hprod.congr_deriv ?_
    dsimp [f3]
    field_simp [hm0]
    have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
    linear_combination (8 * (g : ℂ) * m * e g) * hI2

/-- Exact cubic perturbative coefficient of `partialPhaseSum N` at `g = 0` (Chandrasekaran
arXiv:2611.34924v1, Eq. 4.34): `(1 / 6) * iteratedDeriv 3 (partialPhaseSum N) 0 = -i H_N`. -/
theorem iteratedDeriv_three_partialPhaseSum_zero (N : ℕ) :
    (1 / 6 : ℂ) * iteratedDeriv 3 (partialPhaseSum N) 0 =
      -Complex.I * ∑ k ∈ Finset.range N, (1 : ℂ) / ((k + 1 : ℕ) : ℂ) := by
  let f1 : ℕ → ℝ → ℂ := fun k g =>
    (((g : ℂ) / ((k + 1 : ℕ) : ℂ) ^ 2) -
      Complex.I * (g : ℂ) ^ 2 / ((k + 1 : ℕ) : ℂ)) *
    Complex.exp (-2 * Complex.I * ((k + 1 : ℕ) : ℂ) * (g : ℂ))
  let f2 : ℕ → ℝ → ℂ := fun k g =>
    ((1 / ((k + 1 : ℕ) : ℂ) ^ 2) -
      4 * Complex.I * (g : ℂ) / ((k + 1 : ℕ) : ℂ) - 2 * (g : ℂ) ^ 2) *
    Complex.exp (-2 * Complex.I * ((k + 1 : ℕ) : ℂ) * (g : ℂ))
  let f3 : ℕ → ℝ → ℂ := fun k g =>
    ((-6 * Complex.I / ((k + 1 : ℕ) : ℂ)) - 12 * (g : ℂ) +
      4 * Complex.I * ((k + 1 : ℕ) : ℂ) * (g : ℂ) ^ 2) *
    Complex.exp (-2 * Complex.I * ((k + 1 : ℕ) : ℂ) * (g : ℂ))
  have hd0 : ∀ k : ℕ, ∀ g : ℝ, HasDerivAt (fun x : ℝ => modeTerm x k) (f1 k g) g :=
    fun k => (hasDerivAt_modeTerm_triple k).1
  have hd1 : ∀ k : ℕ, ∀ g : ℝ, HasDerivAt (f1 k) (f2 k g) g :=
    fun k => (hasDerivAt_modeTerm_triple k).2.1
  have hd2 : ∀ k : ℕ, ∀ g : ℝ, HasDerivAt (f2 k) (f3 k g) g :=
    fun k => (hasDerivAt_modeTerm_triple k).2.2
  have hderiv1 : deriv (partialPhaseSum N) = fun g : ℝ => ∑ k ∈ Finset.range N, f1 k g := by
    ext g
    exact (HasDerivAt.fun_sum fun k _ => hd0 k g).deriv
  have hderiv2 :
      deriv (deriv (partialPhaseSum N)) = fun g : ℝ => ∑ k ∈ Finset.range N, f2 k g := by
    rw [hderiv1]
    ext g
    exact (HasDerivAt.fun_sum fun k _ => hd1 k g).deriv
  have hderiv3 : iteratedDeriv 3 (partialPhaseSum N) 0 = ∑ k ∈ Finset.range N, f3 k 0 := by
    rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one, hderiv2]
    exact (HasDerivAt.fun_sum fun k _ => hd2 k 0).deriv
  rw [hderiv3]
  have hf30 : ∀ k ∈ Finset.range N, f3 k 0 = -6 * Complex.I / ((k + 1 : ℕ) : ℂ) := by
    intro k _
    dsimp [f3]
    simp
  rw [Finset.sum_congr rfl hf30, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- The magnitude of the perturbative cubic coefficient at `g = 0` diverges to `+∞` as the mode
cutoff `N → ∞`, witnessing the non-commutativity of the UV limit `N → ∞` and perturbative
expansion `g → 0⁺`. -/
theorem tendsto_neg_im_cubic_coeff_atTop :
    Tendsto (fun N : ℕ => -((1 / 6 : ℂ) * iteratedDeriv 3 (partialPhaseSum N) 0).im)
      atTop atTop := by
  have heq : ∀ N : ℕ,
      -((1 / 6 : ℂ) * iteratedDeriv 3 (partialPhaseSum N) 0).im =
        ∑ k ∈ Finset.range N, (1 : ℝ) / ((k : ℝ) + 1) := by
    intro N
    rw [iteratedDeriv_three_partialPhaseSum_zero N]
    have hreal :
        (∑ k ∈ Finset.range N, (1 : ℂ) / ((k + 1 : ℕ) : ℂ)) =
          ((∑ k ∈ Finset.range N, (1 : ℝ) / ((k : ℝ) + 1) : ℝ) : ℂ) := by
      rw [Complex.ofReal_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      push_cast
      rfl
    rw [hreal, neg_mul, Complex.neg_im, Complex.I_mul_im, Complex.ofReal_re, neg_neg]
  simp_rw [heq]
  exact Real.tendsto_sum_range_one_div_nat_succ_atTop

#print axioms summable_and_norm_le_modeTerm
#print axioms iteratedDeriv_three_partialPhaseSum_zero
#print axioms tendsto_neg_im_cubic_coeff_atTop

end D5.S3.Quantum.Analysis.NullConeGravity.NonperturbativePhaseResummation
