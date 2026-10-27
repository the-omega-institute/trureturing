/- GID: D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/LaguerreSevenHalfFourthGraph
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:finite-gaussian-helper)
   anchors: []
   utility: none
   digest: Actual finite even Gaussian fourth graph estimate from Jacobi recurrence. -/
/-
SPDX-License-Identifier: Apache-2.0
Finite-source Gaussian graph estimate, 2026-10-27.
All imported supplier attribution and license notices remain applicable.

Actual finite-polynomial x^2 graph estimate. The proof uses the existing
alpha=7/2 normalized modes, physical multiplication recurrence, and actual
integral orthogonality. No graph estimate, coefficient completeness, or
matrix enclosure is assumed. All private helpers are consumed by the final
actual weighted-integral theorem. No Lp/weighted-sequence framework is added.

Prior search: repository FiniteGaussianCap4, generic norm/Jacobi bounds,
and fixed Mathlib inner-product / finite-sum APIs. No exact fourth graph
estimate found; existing physicalX and polynomialPair APIs are reused.
-/
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.LaguerreSevenHalfFiniteJacobi

/-! A fourth graph bound for finite even normalized Laguerre expansions. -/

set_option autoImplicit false
noncomputable section
open Polynomial MeasureTheory Set
open scoped BigOperators

namespace FiniteGaussianCap4.LaguerreSevenHalf

private def graphSynthesis {ι : Type*} (s : Finset ι) (mode : ι → ℕ)
    (c : ι → ℝ) : ℝ[X] :=
  ∑ i ∈ s, C (c i) * psiPolynomial (mode i)

private def graphLower (n : ℕ) : ℝ :=
  if n = 0 then 0 else jacobiUpper (n - 1)

private theorem graphPair_nonneg (p : ℝ[X]) : 0 ≤ polynomialPair p p := by
  rw [← integral_physical_product]
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have h := mul_nonneg (Real.rpow_nonneg hx.le (7 / 2 : ℝ))
    (sq_nonneg (physicalPolynomial p x))
  simpa only [pow_two, mul_assoc, Pi.zero_apply] using h

private theorem graphPair_three (p q r : ℝ[X]) :
    polynomialPair (p - q - r) (p - q - r) ≤
      3 * (polynomialPair p p + polynomialPair q q + polynomialPair r r) := by
  have h₁ := graphPair_nonneg (p + q)
  have h₂ := graphPair_nonneg (p + r)
  have h₃ := graphPair_nonneg (q - r)
  simp only [polynomialPair_add_left, polynomialPair_add_right,
    polynomialPair_sub_left, polynomialPair_sub_right] at h₁ h₂ h₃ ⊢
  simp only [polynomialPair_comm q p, polynomialPair_comm r p,
    polynomialPair_comm r q] at h₁ h₂ h₃ ⊢
  linarith

private theorem graphSynthesis_pair {ι : Type*} (s : Finset ι)
    (mode : ι → ℕ) (c : ι → ℝ) (hinj : Set.InjOn mode (s : Set ι)) :
    polynomialPair (graphSynthesis s mode c) (graphSynthesis s mode c) =
      ∑ i ∈ s, c i ^ 2 := by
  classical
  have hinner (i : ι) (hi : i ∈ s) :
      polynomialPair (psiPolynomial (mode i)) (graphSynthesis s mode c) = c i := by
    change polynomialPair (psiPolynomial (mode i))
      (∑ j ∈ s, C (c j) * psiPolynomial (mode j)) = c i
    rw [polynomialPair_comm, polynomialPair_sum_left]
    simp_rw [polynomialPair_C_left, polynomialPair_psi]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j hj hji
      have hne : mode j ≠ mode i := fun h => hji (hinj hj hi h)
      simp only [ite_eq_right hne, mul_zero]
    · exact fun h => (h hi).elim
  change polynomialPair (∑ i ∈ s, C (c i) * psiPolynomial (mode i))
    (graphSynthesis s mode c) = ∑ i ∈ s, c i ^ 2
  rw [polynomialPair_sum_left]
  apply Finset.sum_congr rfl
  intro i hi
  rw [polynomialPair_C_left, hinner i hi]
  ring

private theorem graphX_psi (n : ℕ) :
    physicalX (psiPolynomial n) =
      C ((n : ℝ) + 9 / 4) * psiPolynomial n -
      C (jacobiUpper n) * psiPolynomial (n + 1) -
      C (graphLower n) * psiPolynomial (n - 1) := by
  cases n with
  | zero => simpa [graphLower] using physicalX_psi_zero
  | succ n =>
      simpa only [graphLower, ite_eq_right (Nat.succ_ne_zero n),
        Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] using physicalX_psi_succ n

private theorem graphX_synthesis {ι : Type*} (s : Finset ι)
    (mode : ι → ℕ) (c : ι → ℝ) :
    physicalX (graphSynthesis s mode c) =
      graphSynthesis s mode (fun i => ((mode i : ℝ) + 9 / 4) * c i) -
      graphSynthesis s (fun i => mode i + 1) (fun i => jacobiUpper (mode i) * c i) -
      graphSynthesis (s.filter fun i => 0 < mode i) (fun i => mode i - 1)
        (fun i => graphLower (mode i) * c i) := by
  classical
  have hsum : physicalX (graphSynthesis s mode c) =
      ∑ i ∈ s, C (c i) * physicalX (psiPolynomial (mode i)) := by
    simp only [graphSynthesis, physicalX, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hterm (i : ι) :
      C (c i) * physicalX (psiPolynomial (mode i)) =
        C (((mode i : ℝ) + 9 / 4) * c i) * psiPolynomial (mode i) -
        C (jacobiUpper (mode i) * c i) * psiPolynomial (mode i + 1) -
        C (graphLower (mode i) * c i) * psiPolynomial (mode i - 1) := by
    rw [graphX_psi]
    simp only [map_mul]
    ring
  rw [hsum]
  simp_rw [hterm, Finset.sum_sub_distrib]
  have hfilter :
      (∑ i ∈ s, C (graphLower (mode i) * c i) * psiPolynomial (mode i - 1)) =
      ∑ i ∈ s.filter (fun i => 0 < mode i),
        C (graphLower (mode i) * c i) * psiPolynomial (mode i - 1) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hn : 0 < mode i
    · simp only [ite_eq_left hn]
    · have hz : mode i = 0 := by omega
      simp [hz, graphLower]
  rw [hfilter]
  rfl

private theorem graphLower_injective {ι : Type*} (s : Finset ι)
    (mode : ι → ℕ) (hinj : Set.InjOn mode (s : Set ι)) :
    Set.InjOn (fun i => mode i - 1) (↑(s.filter fun i => 0 < mode i) : Set ι) := by
  classical
  intro i hi j hj he
  obtain ⟨his, hip⟩ := Finset.mem_filter.mp hi
  obtain ⟨hjs, hjp⟩ := Finset.mem_filter.mp hj
  dsimp only at he
  exact hinj his hjs (by omega)

private theorem graph_coefficient_sq (n : ℕ) :
    ((n : ℝ) + 9 / 4) ^ 2 ≤ 9 * ((n : ℝ) + 1) ^ 2 ∧
    jacobiUpper n ^ 2 ≤ 9 * ((n : ℝ) + 1) ^ 2 ∧
    graphLower n ^ 2 ≤ 9 * ((n : ℝ) + 1) ^ 2 := by
  have hn := Nat.cast_nonneg (α := ℝ) n
  constructor
  · nlinarith
  constructor
  · rw [jacobiUpper_sq]
    nlinarith
  · cases n with
    | zero => norm_num [graphLower]
    | succ n =>
        rw [graphLower, ite_eq_right (Nat.succ_ne_zero n), Nat.add_sub_cancel,
          jacobiUpper_sq]
        push_cast
        have hn := Nat.cast_nonneg (α := ℝ) n
        nlinarith

private theorem graphX_bound {ι : Type*} (s : Finset ι)
    (mode : ι → ℕ) (c : ι → ℝ) (hinj : Set.InjOn mode (s : Set ι)) :
    polynomialPair (physicalX (graphSynthesis s mode c))
      (physicalX (graphSynthesis s mode c)) ≤
        81 * ∑ i ∈ s, ((mode i : ℝ) + 1) ^ 2 * c i ^ 2 := by
  classical
  have hup : Set.InjOn (fun i => mode i + 1) (s : Set ι) := by
    intro i hi j hj h
    dsimp only at h
    exact hinj hi hj (by omega)
  have hdown := graphLower_injective s mode hinj
  simp only [graphX_synthesis]
  refine (graphPair_three _ _ _).trans ?_
  rw [graphSynthesis_pair s mode _ hinj, graphSynthesis_pair s _ _ hup,
    graphSynthesis_pair _ _ _ hdown]
  have hd : (∑ i ∈ s, (((mode i : ℝ) + 9 / 4) * c i) ^ 2) ≤
      9 * ∑ i ∈ s, ((mode i : ℝ) + 1) ^ 2 * c i ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    simpa only [mul_pow, mul_assoc] using
      mul_le_mul_of_nonneg_right (graph_coefficient_sq (mode i)).1 (sq_nonneg (c i))
  have hu : (∑ i ∈ s, (jacobiUpper (mode i) * c i) ^ 2) ≤
      9 * ∑ i ∈ s, ((mode i : ℝ) + 1) ^ 2 * c i ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    simpa only [mul_pow, mul_assoc] using
      mul_le_mul_of_nonneg_right (graph_coefficient_sq (mode i)).2.1 (sq_nonneg (c i))
  have hl : (∑ i ∈ s.filter (fun i => 0 < mode i), (graphLower (mode i) * c i) ^ 2) ≤
      9 * ∑ i ∈ s, ((mode i : ℝ) + 1) ^ 2 * c i ^ 2 := by
    rw [Finset.sum_filter, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    split_ifs with hn
    · simpa only [mul_pow, mul_assoc] using
        mul_le_mul_of_nonneg_right (graph_coefficient_sq (mode i)).2.2 (sq_nonneg (c i))
    · positivity
  linarith

private theorem graph_weighted_coefficient_sq (n : ℕ) :
    ((n : ℝ) + 1) ^ 2 * ((n : ℝ) + 9 / 4) ^ 2 ≤
      36 * ((n : ℝ) + 1) ^ 4 ∧
    ((n : ℝ) + 2) ^ 2 * jacobiUpper n ^ 2 ≤
      36 * ((n : ℝ) + 1) ^ 4 ∧
    (((n - 1 : ℕ) : ℝ) + 1) ^ 2 * graphLower n ^ 2 ≤
      36 * ((n : ℝ) + 1) ^ 4 := by
  have hn := Nat.cast_nonneg (α := ℝ) n
  obtain ⟨hd, hu, hl⟩ := graph_coefficient_sq n
  have hs : 0 ≤ ((n : ℝ) + 1) ^ 2 := sq_nonneg _
  have hs4 : 0 ≤ ((n : ℝ) + 1) ^ 4 := pow_nonneg (by positivity) _
  constructor
  · have h := mul_le_mul_of_nonneg_left hd hs
    nlinarith only [h, hs4]
  constructor
  · have hshift : ((n : ℝ) + 2) ^ 2 ≤ 4 * ((n : ℝ) + 1) ^ 2 := by nlinarith
    have h := mul_le_mul hshift hu (sq_nonneg _) (by positivity)
    nlinarith only [h]
  · have hpred : ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast Nat.sub_le n 1
    have hpred0 := Nat.cast_nonneg (α := ℝ) (n - 1)
    have hshift : (((n - 1 : ℕ) : ℝ) + 1) ^ 2 ≤ 4 * ((n : ℝ) + 1) ^ 2 := by
      have h := pow_le_pow_left₀ (by positivity : 0 ≤ ((n - 1 : ℕ) : ℝ) + 1)
        (show ((n - 1 : ℕ) : ℝ) + 1 ≤ (n : ℝ) + 1 by linarith) 2
      nlinarith [sq_nonneg ((n : ℝ) + 1)]
    have h := mul_le_mul hshift hl (sq_nonneg _) (by positivity)
    nlinarith only [h]

private theorem graphXX_bound {ι : Type*} (s : Finset ι)
    (mode : ι → ℕ) (c : ι → ℝ) (hinj : Set.InjOn mode (s : Set ι)) :
    polynomialPair (physicalX (physicalX (graphSynthesis s mode c)))
      (physicalX (physicalX (graphSynthesis s mode c))) ≤
        26244 * ∑ i ∈ s, ((mode i : ℝ) + 1) ^ 4 * c i ^ 2 := by
  classical
  have hup : Set.InjOn (fun i => mode i + 1) (s : Set ι) := by
    intro i hi j hj h
    dsimp only at h
    exact hinj hi hj (by omega)
  have hdown := graphLower_injective s mode hinj
  have hsplit : physicalX (physicalX (graphSynthesis s mode c)) =
      physicalX (graphSynthesis s mode (fun i => ((mode i : ℝ) + 9 / 4) * c i)) -
      physicalX (graphSynthesis s (fun i => mode i + 1)
        (fun i => jacobiUpper (mode i) * c i)) -
      physicalX (graphSynthesis (s.filter fun i => 0 < mode i) (fun i => mode i - 1)
        (fun i => graphLower (mode i) * c i)) := by
    rw [graphX_synthesis]
    simp only [physicalX, mul_sub]
  simp only [hsplit]
  refine (graphPair_three _ _ _).trans ?_
  have hd := graphX_bound s mode (fun i => ((mode i : ℝ) + 9 / 4) * c i) hinj
  have hu := graphX_bound s (fun i => mode i + 1) (fun i => jacobiUpper (mode i) * c i) hup
  have hl := graphX_bound (s.filter fun i => 0 < mode i) (fun i => mode i - 1)
    (fun i => graphLower (mode i) * c i) hdown
  have hdcost : (∑ i ∈ s, ((mode i : ℝ) + 1) ^ 2 *
      (((mode i : ℝ) + 9 / 4) * c i) ^ 2) ≤
      36 * ∑ i ∈ s, ((mode i : ℝ) + 1) ^ 4 * c i ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    simpa only [mul_pow, mul_assoc] using mul_le_mul_of_nonneg_right
      (graph_weighted_coefficient_sq (mode i)).1 (sq_nonneg (c i))
  have hucost : (∑ i ∈ s, (((mode i + 1 : ℕ) : ℝ) + 1) ^ 2 *
      (jacobiUpper (mode i) * c i) ^ 2) ≤
      36 * ∑ i ∈ s, ((mode i : ℝ) + 1) ^ 4 * c i ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have h := mul_le_mul_of_nonneg_right
      (graph_weighted_coefficient_sq (mode i)).2.1 (sq_nonneg (c i))
    simpa only [mul_pow, mul_assoc, Nat.cast_add, Nat.cast_one,
      show (1 : ℝ) + 1 = 2 by norm_num, add_assoc] using h
  have hlcost : (∑ i ∈ s.filter (fun i => 0 < mode i),
      (((mode i - 1 : ℕ) : ℝ) + 1) ^ 2 * (graphLower (mode i) * c i) ^ 2) ≤
      36 * ∑ i ∈ s, ((mode i : ℝ) + 1) ^ 4 * c i ^ 2 := by
    rw [Finset.sum_filter, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    split_ifs with hn
    · simpa only [mul_pow, mul_assoc] using mul_le_mul_of_nonneg_right
        (graph_weighted_coefficient_sq (mode i)).2.2 (sq_nonneg (c i))
    · positivity
  linarith

/-- The actual fourth graph bound for any finite even coefficient vector.
Both the integral's domain and its numerical upper bound are proved. -/
theorem finite_even_physical_x2_graph_bound (d : ℕ → ℝ) (N : ℕ) :
    IntegrableOn (fun x : ℝ => x ^ (15 / 2 : ℝ) *
      (∑ k ∈ Finset.range N, d k * centralPsi x (2 * k)) ^ 2) (Ioi 0) ∧
    (∫ x in Ioi (0 : ℝ), x ^ (15 / 2 : ℝ) *
      (∑ k ∈ Finset.range N, d k * centralPsi x (2 * k)) ^ 2) ≤
      (648 : ℝ) ^ 2 * ∑ k ∈ Finset.range N, ((k : ℝ) + 1) ^ 4 * d k ^ 2 := by
  have hinj : Set.InjOn (fun k : ℕ => 2 * k) (↑(Finset.range N) : Set ℕ) := by
    intro i hi j hj he
    dsimp only at he
    omega
  have hgraph := graphXX_bound (Finset.range N) (fun k => 2 * k) d hinj
  have heven : graphSynthesis (Finset.range N) (fun k => 2 * k) d = evenPolynomial d N := rfl
  rw [heven] at hgraph
  let p := physicalX (physicalX (evenPolynomial d N))
  have hfun (x : ℝ) (hx : x ∈ Ioi (0 : ℝ)) :
      x ^ (7 / 2 : ℝ) * physicalPolynomial p x * physicalPolynomial p x =
        x ^ (15 / 2 : ℝ) *
          (∑ k ∈ Finset.range N, d k * centralPsi x (2 * k)) ^ 2 := by
    dsimp only [p]
    rw [physicalPolynomial_X, physicalPolynomial_X, physical_evenPolynomial]
    have hpow : x ^ (15 / 2 : ℝ) = x ^ (7 / 2 : ℝ) * x ^ (4 : ℕ) := by
      calc
        x ^ (15 / 2 : ℝ) = x ^ (7 / 2 + (4 : ℝ)) := by congr 1 <;> norm_num
        _ = x ^ (7 / 2 : ℝ) * x ^ (4 : ℝ) := Real.rpow_add hx _ _
        _ = x ^ (7 / 2 : ℝ) * x ^ (4 : ℕ) :=
          congrArg (fun t : ℝ => x ^ (7 / 2 : ℝ) * t) (Real.rpow_ofNat x 4)
    rw [hpow]
    ring
  have hint := (integrable_physical_product p p).congr_fun hfun measurableSet_Ioi
  have heq :
      (∫ x in Ioi (0 : ℝ), x ^ (15 / 2 : ℝ) *
        (∑ k ∈ Finset.range N, d k * centralPsi x (2 * k)) ^ 2) = polynomialPair p p := by
    rw [← integral_physical_product]
    exact setIntegral_congr_fun measurableSet_Ioi (fun x hx => (hfun x hx).symm)
  refine ⟨hint, ?_⟩
  rw [heq]
  refine hgraph.trans ?_
  have hweight : (∑ k ∈ Finset.range N, ((2 * k : ℕ) + 1 : ℝ) ^ 4 * d k ^ 2) ≤
      16 * ∑ k ∈ Finset.range N, ((k : ℝ) + 1) ^ 4 * d k ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    have hk0 := Nat.cast_nonneg (α := ℝ) k
    have hk2 : (2 * (k : ℝ) + 1) ^ 4 ≤ 16 * ((k : ℝ) + 1) ^ 4 := by
      have h := pow_le_pow_left₀ (by positivity : 0 ≤ 2 * (k : ℝ) + 1)
        (show 2 * (k : ℝ) + 1 ≤ 2 * ((k : ℝ) + 1) by linarith) 4
      simpa only [mul_pow, show (2 : ℝ) ^ 4 = 16 by norm_num] using h
    have h := mul_le_mul_of_nonneg_right hk2 (sq_nonneg (d k))
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, mul_assoc] using h
  have h := mul_le_mul_of_nonneg_left hweight (by norm_num : (0 : ℝ) ≤ 26244)
  convert h using 1 <;> ring

end FiniteGaussianCap4.LaguerreSevenHalf
