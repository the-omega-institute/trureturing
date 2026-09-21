/- GID: D5/S3/Analytic/NoisyMomentPhaseBoundary
   generality: G
   mirror-B: D5/B/S3/Analytic/NoisyMomentPhaseBoundary
   mirror-E: none(waiver:exact-symbolic-noise-phase)
   anchors: []
   utility: none
   digest: Saturation of a noisy moment optimum forces its entire probability pair and gives the exact first support-transition threshold. -/

import D5.S3.Analytic.GoldenTomography.FinitePronyHankelReconstruction
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Tactic

/-!
# Exact first phase of noisy exterior-atom optimization

The small-noise optimum uses a sign-preserving perturbation of Lagrange
weights. This module addresses its converse: can a different probability pair
continue to attain the same affine value after that perturbation loses a sign?
For nonzero nonconstant dual coefficients the answer is no. Saturation forces
every noisy moment coordinate, and interpolation then forces every weight.
The conclusion is an exact classification for every nonnegative noise level,
including the first boundary where one of the constructed weights vanishes.

The observation is the existing finite Prony sum. No moment-matching witness,
optimality certificate, or sign-preservation radius is supplied as a hypothesis.
No assertion about zero dual coefficients or subsequent optimal phases is made.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Analytic.NoisyMomentPhaseBoundary

open Polynomial Finset
open scoped BigOperators
open D5.S3.Analytic.GoldenTomography.FinitePronyHankelReconstruction

/-- Exact classification of all probability pairs attaining the initial affine
upper value. Nonzero nonconstant coefficients make the noise face rigid.
All nodes, polynomials, directions and transition slopes are computed here.
At equality in a transition constraint the vanishing weight is allowed. -/
theorem exact_noise_phase_classification
    {N : ℕ} (hN : 0 < N) (x : Fin N → ℝ) (hx : Function.Injective x)
    (y : ℝ) (hy : ∀ i, y ≠ x i) :
    let ell : Fin N → ℝ[X] := fun i => Lagrange.basis univ x i
    let c : Fin N → ℝ := fun i => (ell i).eval y
    let p : ℝ[X] := Lagrange.interpolate univ x (fun i => if 0 < c i then 1 else 0)
    let P : ℝ := p.eval y
    let L : ℝ := ∑ k ∈ range N, if k = 0 then 0 else |p.coeff k|
    let d : ℕ → ℝ := fun k => if k = 0 then 0 else if 0 ≤ p.coeff k then 1 else -1
    let r : Fin N → ℝ := fun i => ∑ k ∈ range N, d k * (ell i).coeff k
    (∀ k : ℕ, k < N → k ≠ 0 → p.coeff k ≠ 0) →
    ∀ ε : ℝ, 0 ≤ ε →
    let w := (1 + ε * L) / P
    let b : Fin N → ℝ := fun i => w * c i - ε * r i
    ∀ u v : Fin N → ℝ,
      ((∀ i, 0 ≤ u i) ∧ (∀ i, 0 ≤ v i) ∧
        w + ∑ i, u i = 1 ∧ (∑ i, v i) = 1 ∧
        ∀ k : ℕ, k < N →
          |w * y ^ k + pronyMoment x u k - pronyMoment x v k| ≤ ε) ↔
      ((∀ i, ε * (P * r i / c i - L) ≤ 1) ∧
        u = (fun i => max (-b i) 0) ∧ v = (fun i => max (b i) 0)) := by
  classical
  letI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  let ell : Fin N → ℝ[X] := fun i => Lagrange.basis univ x i
  let c : Fin N → ℝ := fun i => (ell i).eval y
  let J : Finset (Fin N) := univ.filter (fun i => 0 < c i)
  let p : ℝ[X] := Lagrange.interpolate univ x (fun i => if 0 < c i then 1 else 0)
  let P : ℝ := p.eval y
  let L : ℝ := ∑ k ∈ range N, if k = 0 then 0 else |p.coeff k|
  let d : ℕ → ℝ := fun k => if k = 0 then 0 else if 0 ≤ p.coeff k then 1 else -1
  let D : ℝ[X] →ₗ[ℝ] ℝ :=
    { toFun := fun f => ∑ k ∈ range N, d k * f.coeff k
      map_add' := by intro f g; simp [coeff_add, mul_add, sum_add_distrib]
      map_smul' := by
        intro a f
        simp only [coeff_smul, smul_eq_mul, RingHom.id_apply, mul_sum]
        apply sum_congr rfl
        intro k hk
        ring }
  let r : Fin N → ℝ := fun i => D (ell i)
  change (∀ k : ℕ, k < N → k ≠ 0 → p.coeff k ≠ 0) → _
  intro hcoeff ε hε
  let w : ℝ := (1 + ε * L) / P
  let b : Fin N → ℝ := fun i => w * c i - ε * r i
  change ∀ u v : Fin N → ℝ,
    ((∀ i, 0 ≤ u i) ∧ (∀ i, 0 ≤ v i) ∧
      w + ∑ i, u i = 1 ∧ (∑ i, v i) = 1 ∧
      ∀ k : ℕ, k < N →
        |w * y ^ k + pronyMoment x u k - pronyMoment x v k| ≤ ε) ↔
    ((∀ i, ε * (P * r i / c i - L) ≤ 1) ∧
      u = (fun i => max (-b i) 0) ∧ v = (fun i => max (b i) 0))
  have hellsum : (∑ i, ell i) = 1 :=
    Lagrange.sum_basis hx.injOn univ_nonempty
  have hcsum : (∑ i, c i) = 1 := by
    have h := congrArg (fun f : ℝ[X] => f.eval y) hellsum
    simpa [c, eval_finsetSum] using h
  have hcne (i : Fin N) : c i ≠ 0 := by
    dsimp [c, ell]
    simp only [Lagrange.basis, eval_prod, Lagrange.basisDivisor,
      eval_mul, eval_C, eval_sub, eval_X]
    apply prod_ne_zero_iff.mpr
    intro j hj
    have hji := (mem_erase.mp hj).1
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
    by_cases h : 0 < c i
    · simp [h]
    · simpa [h] using le_of_not_gt h
  have hP : 0 < P := lt_of_lt_of_le (by norm_num) hPone
  have hP0 : P ≠ 0 := ne_of_gt hP
  have hline : w * P = 1 + ε * L := by
    dsimp [w]
    exact div_mul_cancel₀ _ hP0
  have hpnode (i : Fin N) : p.eval (x i) = if 0 < c i then 1 else 0 :=
    Lagrange.eval_interpolate_at_node _ hx.injOn (mem_univ i)
  have hpvals (i : Fin N) : 0 ≤ p.eval (x i) ∧ p.eval (x i) ≤ 1 := by
    rw [hpnode]
    split_ifs <;> norm_num
  have hpne : p ≠ 0 := by
    intro hz
    apply hP0
    simp [P, hz]
  have hpdeg : p.natDegree < N := by
    apply (natDegree_lt_iff_degree_lt hpne).mpr
    simpa [p] using Lagrange.degree_interpolate_lt
      (s := (univ : Finset (Fin N))) (v := x)
      (fun i => if 0 < c i then (1 : ℝ) else 0) hx.injOn
  have helldeg (i : Fin N) : (ell i).natDegree < N := by
    rw [show (ell i).natDegree = N - 1 by
      simpa [ell] using Lagrange.natDegree_basis hx.injOn (mem_univ i)]
    omega
  have hellnode (i j : Fin N) : (ell i).eval (x j) = if i = j then 1 else 0 := by
    by_cases h : i = j
    · subst j
      simpa [ell] using Lagrange.eval_basis_self hx.injOn (mem_univ i)
    · simpa [ell, h] using Lagrange.eval_basis_of_ne (s := univ) (v := x) h (mem_univ j)
  have hD1 : D 1 = 0 := by
    change (∑ k ∈ range N, d k * (1 : ℝ[X]).coeff k) = 0
    apply sum_eq_zero
    intro k hk
    by_cases h : k = 0
    · subst k; simp [d]
    · rw [Polynomial.coeff_one, if_neg h, mul_zero]
  have hDp : D p = L := by
    change (∑ k ∈ range N, d k * p.coeff k) = _
    apply sum_congr rfl
    intro k hk
    by_cases h0 : k = 0
    · simp [d, h0]
    · by_cases hs : 0 ≤ p.coeff k
      · simp [d, h0, hs, abs_of_nonneg hs]
      · simp [d, h0, hs, abs_of_neg (lt_of_not_ge hs)]
  have hrsum : (∑ i, r i) = 0 := by
    change (∑ i, D (ell i)) = 0
    rw [← map_sum, hellsum, hD1]
  have hrJ : (∑ i ∈ J, r i) = L := by
    change (∑ i ∈ J, D (ell i)) = L
    rw [← map_sum, ← hpJ, hDp]
  have hrepr (f : ℝ[X]) (hf : f.degree < (N : WithBot ℕ)) :
      f = ∑ i, f.eval (x i) • ell i := by
    have h := Lagrange.eq_interpolate (s := univ) (v := x) (f := f) hx.injOn
      (by simpa using hf)
    simpa [ell, Lagrange.interpolate_apply, Polynomial.smul_eq_C_mul] using h
  have hcmon (k : ℕ) (hk : k < N) : (∑ i, c i * x i ^ k) = y ^ k := by
    have hf : (X ^ k : ℝ[X]).degree < (N : WithBot ℕ) := by
      simpa only [degree_X_pow, Nat.cast_withBot, WithBot.coe_lt_coe] using hk
    have h := congrArg (fun f : ℝ[X] => f.eval y) (hrepr (X ^ k) hf)
    simpa [c, eval_finsetSum, eval_smul, mul_comm] using h.symm
  have hrmon (k : ℕ) (hk : k < N) : (∑ i, r i * x i ^ k) = d k := by
    have hf : (X ^ k : ℝ[X]).degree < (N : WithBot ℕ) := by
      simpa only [degree_X_pow, Nat.cast_withBot, WithBot.coe_lt_coe] using hk
    have h := congrArg D (hrepr (X ^ k) hf)
    have hpow : D (X ^ k) = d k := by simp [D, coeff_X_pow, hk]
    rw [hpow] at h
    simpa [r, map_sum, map_smul, smul_eq_mul, mul_comm] using h.symm
  have hfactor (i : Fin N) :
      b i = (c i / P) * (1 - ε * (P * r i / c i - L)) := by
    dsimp [b, w]
    field_simp [hP0, hcne i] <;> ring
  have hratio (i : Fin N) :
      P * (b i / c i) = 1 - ε * (P * r i / c i - L) := by
    dsimp [b, w]
    field_simp [hP0, hcne i] <;> ring
  intro u v
  constructor
  · rintro ⟨hu, hv, hmu, hnu, hnoise⟩
    let e : ℕ → ℝ := fun k => w * y ^ k + pronyMoment x u k - pronyMoment x v k
    have he0 : e 0 = 0 := by
      dsimp [e, pronyMoment]
      simp only [pow_zero, mul_one]
      linarith
    have hweighted (a : Fin N → ℝ) (f : ℝ[X]) (hf : f.natDegree < N) :
        (∑ i, a i * f.eval (x i)) =
          ∑ k ∈ range N, f.coeff k * (∑ i, a i * x i ^ k) := by
      simp_rw [Polynomial.eval_eq_sum_range' hf, mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro k hk
      apply sum_congr rfl
      intro i hi
      ring
    have hbridge (f : ℝ[X]) (hf : f.natDegree < N) :
        w * f.eval y + (∑ i, u i * f.eval (x i)) - (∑ i, v i * f.eval (x i)) =
          ∑ k ∈ range N, f.coeff k * e k := by
      rw [hweighted u f hf, hweighted v f hf,
        Polynomial.eval_eq_sum_range' hf y, mul_sum,
        ← sum_add_distrib, ← sum_sub_distrib]
      apply sum_congr rfl
      intro k hk
      dsimp [e, pronyMoment]
      ring
    let slack : ℕ → ℝ := fun k =>
      (if k = 0 then 0 else ε * |p.coeff k|) - p.coeff k * e k
    have hslack (k : ℕ) (hk : k < N) : 0 ≤ slack k := by
      by_cases h0 : k = 0
      · subst k; simp [slack, he0]
      · have hbound : p.coeff k * e k ≤ ε * |p.coeff k| := by
          calc
            _ ≤ |p.coeff k * e k| := le_abs_self _
            _ = |p.coeff k| * |e k| := abs_mul _ _
            _ ≤ |p.coeff k| * ε :=
              mul_le_mul_of_nonneg_left (hnoise k hk) (abs_nonneg _)
            _ = _ := mul_comm _ _
        simpa [slack, h0] using sub_nonneg.mpr hbound
    have hsumslack : (∑ k ∈ range N, slack k) =
        ε * L - (w * P + (∑ i, u i * p.eval (x i)) - (∑ i, v i * p.eval (x i))) := by
      dsimp [slack, L]
      rw [sum_sub_distrib, mul_sum, hbridge p hpdeg]
      congr 1
      apply sum_congr rfl
      intro k hk
      split_ifs <;> simp
    have hu0 : 0 ≤ ∑ i, u i * p.eval (x i) :=
      sum_nonneg fun i _ => mul_nonneg (hu i) (hpvals i).1
    have hv0 : 0 ≤ ∑ i, v i * (1 - p.eval (x i)) :=
      sum_nonneg fun i _ => mul_nonneg (hv i) (sub_nonneg.mpr (hpvals i).2)
    have hvcomplement : (∑ i, v i * (1 - p.eval (x i))) =
        1 - ∑ i, v i * p.eval (x i) := by
      simp only [mul_sub, mul_one, sum_sub_distrib, hnu]
    have hs0 : 0 ≤ ∑ k ∈ range N, slack k :=
      sum_nonneg fun k hk => hslack k (mem_range.mp hk)
    have hs_eq : (∑ k ∈ range N, slack k) = 0 := by
      rw [hline] at hsumslack
      linarith
    have hu_eq : (∑ i, u i * p.eval (x i)) = 0 := by
      rw [hline] at hsumslack
      linarith
    have hv_eq : (∑ i, v i * (1 - p.eval (x i))) = 0 := by
      rw [hline] at hsumslack
      linarith
    have hslackzero (k : ℕ) (hk : k < N) : slack k = 0 := by
      have hle := single_le_sum (fun j hj => hslack j (mem_range.mp hj)) (mem_range.mpr hk)
      rw [hs_eq] at hle
      exact le_antisymm hle (hslack k hk)
    have hesaturated (k : ℕ) (hk : k < N) : e k = ε * d k := by
      by_cases h0 : k = 0
      · subst k; simp [he0, d]
      · have hzero := hslackzero k hk
        have hpn := hcoeff k hk h0
        have hprod : p.coeff k * (e k - ε * d k) = 0 := by
          by_cases hs : 0 ≤ p.coeff k
          · simp only [slack, if_neg h0, abs_of_nonneg hs] at hzero
            simp only [d, if_neg h0, if_pos hs]
            nlinarith
          · simp only [slack, if_neg h0, abs_of_neg (lt_of_not_ge hs)] at hzero
            simp only [d, if_neg h0, if_neg hs]
            nlinarith
        exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left hpn)
    have hsigned (i : Fin N) : v i - u i = b i := by
      have h := hbridge (ell i) (helldeg i)
      have hsum : (∑ k ∈ range N, (ell i).coeff k * e k) = ε * r i := by
        change (∑ k ∈ range N, (ell i).coeff k * e k) =
          ε * ∑ k ∈ range N, d k * (ell i).coeff k
        rw [mul_sum]
        apply sum_congr rfl
        intro k hk
        rw [hesaturated k (mem_range.mp hk)]
        ring
      rw [hsum] at h
      have hnodal (a : Fin N → ℝ) : (∑ j, a j * (ell i).eval (x j)) = a i := by
        simp_rw [hellnode]
        simp
      rw [hnodal u, hnodal v] at h
      change w * c i + u i - v i = ε * r i at h
      dsimp [b]
      linarith
    have husupport (i : Fin N) (hi : 0 < c i) : u i = 0 := by
      have hle := single_le_sum (fun j _ => mul_nonneg (hu j) (hpvals j).1) (mem_univ i)
      rw [hu_eq, hpnode, if_pos hi, mul_one] at hle
      exact le_antisymm hle (hu i)
    have hvsupport (i : Fin N) (hi : ¬ 0 < c i) : v i = 0 := by
      have hle := single_le_sum
        (fun j _ => mul_nonneg (hv j) (sub_nonneg.mpr (hpvals j).2)) (mem_univ i)
      rw [hv_eq, hpnode, if_neg hi] at hle
      simp only [sub_zero, mul_one] at hle
      exact le_antisymm hle (hv i)
    have hsign (i : Fin N) : 0 ≤ b i / c i := by
      by_cases hi : 0 < c i
      · rw [← hsigned, husupport i hi, sub_zero]
        exact div_nonneg (hv i) hi.le
      · rw [← hsigned, hvsupport i hi, zero_sub]
        exact div_nonneg_of_nonpos (neg_nonpos.mpr (hu i)) (le_of_not_gt hi)
    refine ⟨?_, ?_, ?_⟩
    · intro i
      have h := mul_nonneg hP.le (hsign i)
      rw [hratio] at h
      linarith
    · ext i
      by_cases hi : 0 < c i
      · have hu_i := husupport i hi
        have hb_i : 0 ≤ b i := by rw [← hsigned, hu_i, sub_zero]; exact hv i
        rw [hu_i, max_eq_right (neg_nonpos.mpr hb_i)]
      · have hv_i := hvsupport i hi
        have hb_i : b i = -u i := by rw [← hsigned, hv_i, zero_sub]
        rw [hb_i, neg_neg, max_eq_left (hu i)]
    · ext i
      by_cases hi : 0 < c i
      · have hu_i := husupport i hi
        have hb_i : b i = v i := by rw [← hsigned, hu_i, sub_zero]
        rw [hb_i, max_eq_left (hv i)]
      · have hv_i := hvsupport i hi
        have hb_i : b i ≤ 0 := by rw [← hsigned, hv_i, zero_sub]; exact neg_nonpos.mpr (hu i)
        rw [hv_i, max_eq_right hb_i]
  · rintro ⟨hthreshold, rfl, rfl⟩
    have hbpos (i : Fin N) (hi : 0 < c i) : 0 ≤ b i := by
      rw [hfactor]
      exact mul_nonneg (div_nonneg hi.le hP.le) (sub_nonneg.mpr (hthreshold i))
    have hbneg (i : Fin N) (hi : ¬ 0 < c i) : b i ≤ 0 := by
      rw [hfactor]
      exact mul_nonpos_of_nonpos_of_nonneg
        (div_nonpos_of_nonpos_of_nonneg (le_of_not_gt hi) hP.le)
        (sub_nonneg.mpr (hthreshold i))
    have hparts (i : Fin N) : max (b i) 0 - max (-b i) 0 = b i := by
      by_cases h : 0 ≤ b i
      · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h)]; ring
      · have h' : b i ≤ 0 := le_of_not_ge h
        rw [max_eq_right h', max_eq_left (neg_nonneg.mpr h')]; ring
    have hvJ (i : Fin N) : max (b i) 0 = if 0 < c i then b i else 0 := by
      by_cases hi : 0 < c i
      · rw [if_pos hi, max_eq_left (hbpos i hi)]
      · rw [if_neg hi, max_eq_right (hbneg i hi)]
    have hvsum : (∑ i, max (b i) 0) = 1 := by
      calc
        (∑ i, max (b i) 0) = ∑ i ∈ J, b i := by simp_rw [hvJ]; simp [J, sum_filter]
        _ = w * (∑ i ∈ J, c i) - ε * (∑ i ∈ J, r i) := by
          simp [b, mul_sum, sum_sub_distrib]
        _ = w * P - ε * L := by rw [← hPJ, hrJ]
        _ = 1 := by rw [hline]; ring
    have hbsum : (∑ i, b i) = w := by
      simp [b, sum_sub_distrib, ← mul_sum, hcsum, hrsum]
    have husum : w + (∑ i, max (-b i) 0) = 1 := by
      have h : (∑ i, max (b i) 0) - (∑ i, max (-b i) 0) = w := by
        rw [← sum_sub_distrib]
        simpa only [hparts] using hbsum
      rw [hvsum] at h
      linarith
    refine ⟨(fun _ => le_max_right _ _), (fun _ => le_max_right _ _), husum, hvsum, ?_⟩
    intro k hk
    have hdiff : pronyMoment x (fun i => max (b i) 0) k -
        pronyMoment x (fun i => max (-b i) 0) k = w * y ^ k - ε * d k := by
      calc
        _ = ∑ i, b i * x i ^ k := by
          unfold pronyMoment
          rw [← sum_sub_distrib]
          apply sum_congr rfl
          intro i hi
          rw [← sub_mul, hparts]
        _ = w * (∑ i, c i * x i ^ k) - ε * (∑ i, r i * x i ^ k) := by
          simp only [b, sub_mul, mul_assoc, sum_sub_distrib, mul_sum]
        _ = w * y ^ k - ε * d k := by rw [hcmon k hk, hrmon k hk]
    have heq : w * y ^ k + pronyMoment x (fun i => max (-b i) 0) k -
        pronyMoment x (fun i => max (b i) 0) k = ε * d k := by linarith
    rw [heq, abs_mul, abs_of_nonneg hε]
    have hd : |d k| ≤ 1 := by dsimp [d]; split_ifs <;> norm_num
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hd hε

#print axioms exact_noise_phase_classification

end D5.S3.Analytic.NoisyMomentPhaseBoundary
