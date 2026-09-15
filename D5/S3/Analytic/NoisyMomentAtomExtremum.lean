/- GID: D5/S3/Analytic/NoisyMomentAtomExtremum
   generality: G
   mirror-B: D5/B/S3/Analytic/NoisyMomentAtomExtremum
   mirror-E: none(waiver:constructive-sharp-moment-extremum)
   anchors: []
   utility: none
   digest: Lagrange weights admit an explicit positivity-preserving worst-case noise perturbation attaining the exact exterior-atom optimum. -/

import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Exact small-noise exterior-atom optimization

The unknowns are normalized nonnegative finite probability weights. N raw
moments are observed, including the exactly normalized zeroth moment.
The theorem proves an IsGreatest statement by constructing both probability
vectors and matching a polynomial dual bound. The node set is arbitrary,
finite, nonempty and injectively indexed. No moment-matching, positivity or
optimality witness is supplied as a hypothesis.

The constructive step perturbs the Lagrange weights in the sign direction
of the dual polynomial's coefficients. The explicit noise radius guarantees
that no nodal weight changes sign. This is additional proof content beyond
interpolation, and not a matrix-spectrum re-binding.

The finite-grid theorem does not assert the Chebyshev continuum specialization,
a physical Hamiltonian, optimality outside the stated noise interval, or
validity for arbitrary sampling times. Those distinctions are in the theory.
Relevant background: de Castro--Gamboa, arXiv:1103.4951, and Musco et al.,
arXiv:2408.12385v3. They are not claimed to state this exact local formula.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Analytic.NoisyMomentAtomExtremum

open Polynomial Finset
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Feasible mass at y when two probability vectors on x plus y and on x
have coordinatewise-close raw moments through degree card(ι)-1.
The exact normalizations force the zeroth-moment difference to be zero. -/
def momentAtomSet (x : ι → ℝ) (y ε : ℝ) : Set ℝ :=
  {w | 0 ≤ w ∧ ∃ u v : ι → ℝ,
    (∀ i, 0 ≤ u i) ∧ (∀ i, 0 ≤ v i) ∧
    w + ∑ i, u i = 1 ∧ (∑ i, v i) = 1 ∧
    ∀ k : ℕ, k < Fintype.card ι →
      |w * y ^ k + ∑ i, u i * x i ^ k - ∑ i, v i * x i ^ k| ≤ ε}

private def direction (p : ℝ[X]) (k : ℕ) : ℝ :=
  if k = 0 then 0 else if 0 ≤ p.coeff k then 1 else -1

private def coefficientCost (N : ℕ) (p : ℝ[X]) : ℝ :=
  ∑ k ∈ range N, if k = 0 then 0 else |p.coeff k|

private def noiseFunctional (N : ℕ) (p : ℝ[X]) : ℝ[X] →ₗ[ℝ] ℝ where
  toFun f := ∑ k ∈ range N, direction p k * f.coeff k
  map_add' f g := by
    simp only [coeff_add, mul_add, sum_add_distrib]
  map_smul' a f := by
    simp only [coeff_smul, smul_eq_mul, RingHom.id_apply, mul_sum]
    apply sum_congr rfl
    intro k hk
    ring

private theorem noise_constant (N : ℕ) (p : ℝ[X]) (a : ℝ) :
    noiseFunctional N p (C a) = 0 := by
  change (∑ k ∈ range N, direction p k * (C a).coeff k) = 0
  apply sum_eq_zero
  intro k hk
  by_cases h : k = 0
  · subst k
    simp [direction]
  · simp [coeff_C, h]

private theorem noise_power (N : ℕ) (p : ℝ[X]) (k : ℕ) (hk : k < N) :
    noiseFunctional N p (X ^ k) = direction p k := by
  simp [noiseFunctional, coeff_X_pow, hk]

private theorem noise_self (N : ℕ) (p : ℝ[X]) :
    noiseFunctional N p p = coefficientCost N p := by
  unfold coefficientCost
  change (∑ k ∈ range N, direction p k * p.coeff k) = _
  apply sum_congr rfl
  intro k hk
  by_cases h0 : k = 0
  · simp [direction, h0]
  · by_cases hp : 0 ≤ p.coeff k
    · simp [direction, h0, hp, abs_of_nonneg hp]
    · simp [direction, h0, hp, abs_of_neg (lt_of_not_ge hp)]

private theorem direction_abs_le (p : ℝ[X]) (k : ℕ) :
    |direction p k| ≤ 1 := by
  unfold direction
  split_ifs <;> norm_num

private theorem cost_nonneg (N : ℕ) (p : ℝ[X]) :
    0 ≤ coefficientCost N p := by
  apply sum_nonneg
  intro k hk
  split_ifs <;> positivity

private theorem weighted_eval_expansion (a x : ι → ℝ) (p : ℝ[X])
    (N : ℕ) (hp : p.natDegree < N) :
    (∑ i, a i * p.eval (x i)) =
      ∑ k ∈ range N, p.coeff k * (∑ i, a i * x i ^ k) := by
  simp_rw [Polynomial.eval_eq_sum_range' hp, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro k hk
  apply sum_congr rfl
  intro i hi
  ring

private theorem raw_moment_dual_bound (x : ι → ℝ) (y ε w : ℝ)
    (u v : ι → ℝ) (hu : ∀ i, 0 ≤ u i) (hv : ∀ i, 0 ≤ v i)
    (hmu : w + ∑ i, u i = 1) (hnu : (∑ i, v i) = 1)
    (hnoise : ∀ k : ℕ, k < Fintype.card ι →
      |w * y ^ k + ∑ i, u i * x i ^ k - ∑ i, v i * x i ^ k| ≤ ε)
    (p : ℝ[X]) (hp : p.natDegree < Fintype.card ι)
    (hvalues : ∀ i, 0 ≤ p.eval (x i) ∧ p.eval (x i) ≤ 1) :
    w * p.eval y ≤ 1 + ε * coefficientCost (Fintype.card ι) p := by
  let e : ℕ → ℝ := fun k =>
    w * y ^ k + ∑ i, u i * x i ^ k - ∑ i, v i * x i ^ k
  have he0 : e 0 = 0 := by
    dsimp [e]
    simp only [pow_zero, mul_one]
    linarith
  have hidentity : w * p.eval y + (∑ i, u i * p.eval (x i)) -
      (∑ i, v i * p.eval (x i)) =
      ∑ k ∈ range (Fintype.card ι), p.coeff k * e k := by
    rw [weighted_eval_expansion u x p _ hp, weighted_eval_expansion v x p _ hp,
      Polynomial.eval_eq_sum_range' hp y, mul_sum,
      ← sum_add_distrib, ← sum_sub_distrib]
    apply sum_congr rfl
    intro k hk
    dsimp [e]
    ring
  have hbudget : (∑ k ∈ range (Fintype.card ι), p.coeff k * e k) ≤
      ε * coefficientCost (Fintype.card ι) p := by
    unfold coefficientCost
    rw [mul_sum]
    apply sum_le_sum
    intro k hk
    by_cases h0 : k = 0
    · subst k
      simp [he0]
    · rw [if_neg h0]
      calc
        p.coeff k * e k ≤ |p.coeff k * e k| := le_abs_self _
        _ = |p.coeff k| * |e k| := abs_mul _ _
        _ ≤ |p.coeff k| * ε :=
          mul_le_mul_of_nonneg_left (hnoise k (mem_range.mp hk)) (abs_nonneg _)
        _ = ε * |p.coeff k| := mul_comm _ _
  have hulo : 0 ≤ ∑ i, u i * p.eval (x i) :=
    sum_nonneg fun i _ => mul_nonneg (hu i) (hvalues i).1
  have hvhi : (∑ i, v i * p.eval (x i)) ≤ 1 := by
    calc
      (∑ i, v i * p.eval (x i)) ≤ ∑ i, v i * 1 :=
        sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hvalues i).2 (hv i)
      _ = 1 := by simpa using hnu
  linarith

/-- Exact small-noise optimum, with matching positive normalized witnesses.
All quantities determining the value and the noise interval are computed
from the nodes, the exterior point and ordinary Lagrange polynomials.

The upper certificate is the 0/1 interpolant selected by the signs of the
extrapolation weights. The lower construction perturbs every nodal weight
in the worst raw-moment error direction while preserving all signs.
The conclusion optimizes over every feasible pair of probability vectors,
not merely over the particular constructed family. -/
theorem finite_noisy_exterior_atom_sharp [Nonempty ι]
    (x : ι → ℝ) (hx : Function.Injective x) (y : ℝ)
    (hy : ∀ i, y ≠ x i) :
    let ell : ι → ℝ[X] := fun i => Lagrange.basis univ x i
    let c : ι → ℝ := fun i => (ell i).eval y
    let p : ℝ[X] := Lagrange.interpolate univ x (fun i => if 0 < c i then 1 else 0)
    let P : ℝ := p.eval y
    let L : ℝ := ∑ k ∈ range (Fintype.card ι), if k = 0 then 0 else |p.coeff k|
    let d : ℕ → ℝ := fun k => if k = 0 then 0 else if 0 ≤ p.coeff k then 1 else -1
    let r : ι → ℝ := fun i => ∑ k ∈ range (Fintype.card ι), d k * (ell i).coeff k
    let B : ℝ := ∑ i, |L / P - r i / c i|
    0 < P ∧ ∀ ε : ℝ, 0 ≤ ε → ε * (1 + B) ≤ (1 / P) / 2 →
      IsGreatest (momentAtomSet x y ε) ((1 + ε * L) / P) := by
  classical
  let ell : ι → ℝ[X] := fun i => Lagrange.basis univ x i
  let c : ι → ℝ := fun i => (ell i).eval y
  let J : Finset ι := univ.filter (fun i => 0 < c i)
  let p : ℝ[X] := Lagrange.interpolate univ x (fun i => if 0 < c i then 1 else 0)
  let P : ℝ := p.eval y
  let L : ℝ := coefficientCost (Fintype.card ι) p
  let D : ℝ[X] →ₗ[ℝ] ℝ := noiseFunctional (Fintype.card ι) p
  let r : ι → ℝ := fun i => D (ell i)
  let B : ℝ := ∑ i, |L / P - r i / c i|
  change 0 < P ∧ ∀ ε : ℝ, 0 ≤ ε → ε * (1 + B) ≤ (1 / P) / 2 →
    IsGreatest (momentAtomSet x y ε) ((1 + ε * L) / P)
  have hellsum : (∑ i, ell i) = 1 :=
    Lagrange.sum_basis (s := univ) (v := x) hx.injOn univ_nonempty
  have hcsum : (∑ i, c i) = 1 := by
    have h := congrArg (fun f : ℝ[X] => f.eval y) hellsum
    simpa [c, eval_finsetSum] using h
  have hcne : ∀ i, c i ≠ 0 := by
    intro i
    dsimp [c, ell]
    simp only [Lagrange.basis, eval_prod, Lagrange.basisDivisor,
      eval_mul, eval_C, eval_sub, eval_X]
    apply prod_ne_zero_iff.mpr
    intro j hj
    have hji : j ≠ i := (mem_erase.mp hj).1
    exact mul_ne_zero
      (inv_ne_zero (sub_ne_zero.mpr (fun h => hji (hx h).symm)))
      (sub_ne_zero.mpr (hy j))
  have hpJ : p = ∑ i ∈ J, ell i := by
    simp [p, J, ell, Lagrange.interpolate_apply, sum_filter]
  have hPJ : P = ∑ i ∈ J, c i := by
    dsimp [P]
    rw [hpJ, eval_finsetSum]
  have hPone : 1 ≤ P := by
    rw [hPJ, ← hcsum]
    change (∑ i, c i) ≤ ∑ i ∈ univ.filter (fun i => 0 < c i), c i
    rw [sum_filter]
    apply sum_le_sum
    intro i hi
    by_cases hci : 0 < c i
    · simp [hci]
    · simpa [hci] using (le_of_not_gt hci)
  have hP : 0 < P := lt_of_lt_of_le (by norm_num) hPone
  have hP0 : P ≠ 0 := ne_of_gt hP
  have hL : 0 ≤ L := cost_nonneg _ _
  have hD1 : D 1 = 0 := by
    simpa [D] using noise_constant (Fintype.card ι) p 1
  have hDp : D p = L := noise_self _ _
  have hrsum : (∑ i, r i) = 0 := by
    change (∑ i, D (ell i)) = 0
    rw [← map_sum, hellsum, hD1]
  have hrJ : (∑ i ∈ J, r i) = L := by
    change (∑ i ∈ J, D (ell i)) = L
    rw [← map_sum, ← hpJ, hDp]
  have hpnode : ∀ i, p.eval (x i) = if 0 < c i then 1 else 0 := by
    intro i
    exact Lagrange.eval_interpolate_at_node _ hx.injOn (mem_univ i)
  have hpdeg : p.degree < (Fintype.card ι : WithBot ℕ) := by
    simpa [p] using Lagrange.degree_interpolate_lt (s := univ) (v := x)
      (fun i => if 0 < c i then (1 : ℝ) else 0) hx.injOn
  have hpne : p ≠ 0 := by
    intro hz
    have : P = 0 := by simp [P, hz]
    exact hP0 this
  have hpnat : p.natDegree < Fintype.card ι :=
    (natDegree_lt_iff_degree_lt hpne).mpr hpdeg
  have hrepr (f : ℝ[X]) (hf : f.degree < (Fintype.card ι : WithBot ℕ)) :
      f = ∑ i, f.eval (x i) • ell i := by
    have h := Lagrange.eq_interpolate (s := univ) (v := x) (f := f) hx.injOn
      (by simpa using hf)
    simpa [ell, Lagrange.interpolate_apply, Polynomial.smul_eq_C_mul] using h
  have hcmon (k : ℕ) (hk : k < Fintype.card ι) :
      (∑ i, c i * x i ^ k) = y ^ k := by
    have hf : (X ^ k : ℝ[X]).degree < (Fintype.card ι : WithBot ℕ) := by
      simpa only [Polynomial.degree_X_pow, Nat.cast_withBot, WithBot.coe_lt_coe] using hk
    have h := congrArg (fun f : ℝ[X] => f.eval y) (hrepr (X ^ k) hf)
    simpa [c, eval_finsetSum, eval_smul, mul_comm] using h.symm
  have hrmon (k : ℕ) (hk : k < Fintype.card ι) :
      (∑ i, r i * x i ^ k) = direction p k := by
    have hf : (X ^ k : ℝ[X]).degree < (Fintype.card ι : WithBot ℕ) := by
      simpa only [Polynomial.degree_X_pow, Nat.cast_withBot, WithBot.coe_lt_coe] using hk
    have h := congrArg D (hrepr (X ^ k) hf)
    rw [show D (X ^ k) = direction p k from noise_power _ _ k hk] at h
    simpa [r, map_sum, map_smul, smul_eq_mul, mul_comm] using h.symm
  refine ⟨hP, ?_⟩
  intro ε hε hsmall
  let w : ℝ := (1 + ε * L) / P
  let b : ι → ℝ := fun i => w * c i - ε * r i
  let u : ι → ℝ := fun i => max (-b i) 0
  let v : ι → ℝ := fun i => max (b i) 0
  have hwpos : 0 < w := div_pos (by nlinarith [mul_nonneg hε hL]) hP
  have hB : 0 ≤ B := sum_nonneg fun i _ => abs_nonneg _
  have hslopes (i : ι) : ε * |L / P - r i / c i| ≤ (1 / P) / 2 := by
    have hterm : |L / P - r i / c i| ≤ B :=
      single_le_sum (fun j _ => abs_nonneg (L / P - r j / c j)) (mem_univ i)
    calc
      ε * |L / P - r i / c i| ≤ ε * B :=
        mul_le_mul_of_nonneg_left hterm hε
      _ ≤ ε * (1 + B) := by nlinarith
      _ ≤ (1 / P) / 2 := hsmall
  have hfactor (i : ι) : 0 < 1 / P + ε * (L / P - r i / c i) := by
    have hlo := neg_abs_le (L / P - r i / c i)
    have hmul := mul_le_mul_of_nonneg_left hlo hε
    have hinv : 0 < 1 / P := one_div_pos.mpr hP
    have hbound := hslopes i
    nlinarith
  have hbi (i : ι) : b i = c i * (1 / P + ε * (L / P - r i / c i)) := by
    dsimp [b, w]
    field_simp [hP0, hcne i] <;> ring
  have hvJ : ∀ i, v i = if 0 < c i then b i else 0 := by
    intro i
    by_cases hi : 0 < c i
    · have hbpos : 0 < b i := by rw [hbi]; exact mul_pos hi (hfactor i)
      simp [v, hi, max_eq_left hbpos.le]
    · have hci : c i < 0 := lt_of_le_of_ne (le_of_not_gt hi) (hcne i)
      have hbneg : b i < 0 := by
        rw [hbi]
        exact mul_neg_of_neg_of_pos hci (hfactor i)
      simp [v, hi, max_eq_right hbneg.le]
  have huv (i : ι) : v i - u i = b i := by
    dsimp [u, v]
    by_cases hi : 0 ≤ b i
    · rw [max_eq_left hi, max_eq_right (neg_nonpos.mpr hi)]
      ring
    · have hi' : b i ≤ 0 := le_of_not_ge hi
      rw [max_eq_right hi', max_eq_left (neg_nonneg.mpr hi')]
      ring
  have hvsum : (∑ i, v i) = 1 := by
    calc
      (∑ i, v i) = ∑ i ∈ J, b i := by simp_rw [hvJ]; simp [J, sum_filter]
      _ = w * (∑ i ∈ J, c i) - ε * (∑ i ∈ J, r i) := by
        simp [b, mul_sum, sum_sub_distrib]
      _ = w * P - ε * L := by rw [← hPJ, hrJ]
      _ = 1 := by
        dsimp [w]
        field_simp [hP0] <;> ring
  have hbsum : (∑ i, b i) = w := by
    simp [b, sum_sub_distrib, ← mul_sum, hcsum, hrsum]
  have husum : w + (∑ i, u i) = 1 := by
    have h : (∑ i, v i) - (∑ i, u i) = w := by
      rw [← sum_sub_distrib]
      simpa only [huv] using hbsum
    rw [hvsum] at h
    linarith
  have hmoment (k : ℕ) (hk : k < Fintype.card ι) :
      w * y ^ k + ∑ i, u i * x i ^ k - ∑ i, v i * x i ^ k =
        ε * direction p k := by
    have hsumdiff : (∑ i, v i * x i ^ k) - (∑ i, u i * x i ^ k) =
        w * y ^ k - ε * direction p k := by
      calc
        (∑ i, v i * x i ^ k) - (∑ i, u i * x i ^ k) =
            ∑ i, b i * x i ^ k := by
          rw [← sum_sub_distrib]
          apply sum_congr rfl
          intro i hi
          rw [← sub_mul, huv]
        _ = w * (∑ i, c i * x i ^ k) - ε * (∑ i, r i * x i ^ k) := by
          simp only [b, sub_mul, mul_assoc, sum_sub_distrib, mul_sum]
        _ = w * y ^ k - ε * direction p k := by rw [hcmon k hk, hrmon k hk]
    linarith
  change IsGreatest (momentAtomSet x y ε) w
  constructor
  · refine ⟨hwpos.le, u, v, (fun i => le_max_right _ _),
      (fun i => le_max_right _ _), husum, hvsum, ?_⟩
    intro k hk
    rw [hmoment k hk, abs_mul, abs_of_nonneg hε]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (direction_abs_le p k) hε
  · intro z hz
    rcases hz with ⟨hz, u', v', hu', hv', hmu', hnu', hnoise'⟩
    have hvalues : ∀ i, 0 ≤ p.eval (x i) ∧ p.eval (x i) ≤ 1 := by
      intro i
      rw [hpnode]
      split_ifs <;> norm_num
    have hub := raw_moment_dual_bound x y ε z u' v' hu' hv' hmu' hnu'
      hnoise' p hpnat hvalues
    change z * P ≤ 1 + ε * L at hub
    exact (le_div_iff₀ hP).mpr hub

#print axioms momentAtomSet
#print axioms finite_noisy_exterior_atom_sharp

end D5.S3.Analytic.NoisyMomentAtomExtremum
