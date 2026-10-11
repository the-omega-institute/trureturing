/- GID: D5/S3/Analytic/Interpolation/UniformCoefficientBudget
   generality: G
   mirror-B: D5/B/S3/Analytic/Interpolation/UniformCoefficientBudget
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Derivative budgets bound exact interpolation without node separation. -/

import D5.S3.Analytic.SincSquareDerivativeBudget
import Mathlib.Data.Finsupp.Basic
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic

/-!
The coefficient one-norm definition and its range, addition, scalar, and multiplication
lemmas are adapted from Causalean, Copyright 2026 Jiyuan Tan, Apache-2.0:
https://github.com/Jiyuan-Tan/CausalSmith/tree/e56c1daecf6fc95cad721ff71d188e8fc526cbca/
Causalean/Mathlib/Analysis/Approximation/Chebyshev/{TrigExtraction,PolynomialOneNorm}.lean.
License and notice: docs/reports/interpolation-suppliers/Causalean-LICENSE.txt and
Causalean-NOTICE.txt. Adaptations: local names; expose consumed addition/multiplication
interfaces; share the addition helper; apply the monomial sum API; omit unrelated results.
Retirement: replace these portions by direct calls when this repository's pinned
Mathlib supplies equivalent coefficient one-norm declarations.

Newton interpolation and its derivative mean-value formula are classical results.
The analytic statement concerns a smooth function near a closed real interval;
no lower bound on distances between distinct interpolation nodes is imposed.
-/

noncomputable section

open Finset Set Polynomial

namespace D5.S3.Analytic.Interpolation.UniformCoefficientBudget

/-- Sum of absolute monomial coefficients of a real polynomial. -/
noncomputable def coeffL1 (p : Polynomial ℝ) : ℝ :=
  ∑ n ∈ p.support, |p.coeff n|

private lemma coeffL1_eq_sum_range_of_natDegree_lt (p : Polynomial ℝ) {m : ℕ}
    (hp : p.natDegree < m) :
    coeffL1 p = ∑ k ∈ Finset.range m, |p.coeff k| := by
  change p.sum (fun _ c => |c|) = _
  exact p.sum_over_range' (fun _ => abs_zero) m hp

/-- The coefficient budget satisfies the triangle inequality. -/
theorem coeffL1_add_le (p q : Polynomial ℝ) :
    coeffL1 (p + q) ≤ coeffL1 p + coeffL1 q := by
  -- Put all three coefficient sums over one range, then use the scalar triangle inequality.
  let m := max p.natDegree q.natDegree + 1
  rw [coeffL1_eq_sum_range_of_natDegree_lt (p + q)
      (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (Nat.lt_succ_self _)),
    coeffL1_eq_sum_range_of_natDegree_lt p
      (lt_of_le_of_lt (le_max_left _ _) (Nat.lt_succ_self _)),
    coeffL1_eq_sum_range_of_natDegree_lt q
      (lt_of_le_of_lt (le_max_right _ _) (Nat.lt_succ_self _)),
    ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => by
    simpa only [Polynomial.coeff_add] using abs_add_le (p.coeff i) (q.coeff i)

private theorem coeffL1_smul (c : ℝ) (p : Polynomial ℝ) :
    coeffL1 (c • p) = |c| * coeffL1 p := by
  rw [coeffL1_eq_sum_range_of_natDegree_lt (c • p)
      (lt_of_le_of_lt (Polynomial.natDegree_smul_le _ _) (Nat.lt_succ_self _)),
    coeffL1_eq_sum_range_of_natDegree_lt p (Nat.lt_succ_self _)]
  simp only [Polynomial.coeff_smul, smul_eq_mul, abs_mul, Finset.mul_sum]

/-- The coefficient budget is submultiplicative. -/
theorem coeffL1_mul_le (p q : Polynomial ℝ) :
    coeffL1 (p * q) ≤
      coeffL1 p * coeffL1 q := by
  classical
  have hzero : coeffL1 (0 : Polynomial ℝ) = 0 := by
    simp [coeffL1]
  have hsum (s : Finset ℕ) (f : ℕ → Polynomial ℝ) :
      coeffL1 (∑ i ∈ s, f i) ≤
        ∑ i ∈ s, coeffL1 (f i) := by
    induction s using Finset.induction_on with
    | empty => simp [hzero]
    | @insert i s hi ih =>
        simp only [Finset.sum_insert hi]
        exact (coeffL1_add_le _ _).trans (add_le_add_right ih _)
  have hmono (n : ℕ) (a : ℝ) :
      coeffL1 (monomial n a) = |a| := by
    exact Polynomial.sum_monomial_index a (fun _ c => |c|) (by simp)
  rw [Polynomial.mul_eq_sum_sum]
  calc
    coeffL1
        (∑ i ∈ p.support, q.sum fun j a ↦ monomial (i + j) (p.coeff i * a))
        ≤ ∑ i ∈ p.support,
            coeffL1
              (q.sum fun j a ↦ monomial (i + j) (p.coeff i * a)) := by
            exact hsum p.support
              (fun i ↦ q.sum fun j a ↦ monomial (i + j) (p.coeff i * a))
    _ ≤ ∑ i ∈ p.support, ∑ j ∈ q.support,
          coeffL1 (monomial (i + j) (p.coeff i * q.coeff j)) := by
        apply Finset.sum_le_sum
        intro i hi
        simpa only [Polynomial.sum] using
          (hsum q.support (fun j ↦ monomial (i + j) (p.coeff i * q.coeff j)))
    _ = coeffL1 p * coeffL1 q := by
        simp only [hmono, abs_mul]
        change (∑ i ∈ p.support, ∑ j ∈ q.support,
            |p.coeff i| * |q.coeff j|) =
          (∑ i ∈ p.support, |p.coeff i|) *
            (∑ j ∈ q.support, |q.coeff j|)
        rw [Finset.sum_mul]
        simp only [Finset.mul_sum]

/-- Iterated Rolle on an ordered family of distinct zeros. -/
private theorem rolle_nodes (n : ℕ) (f : ℝ → ℝ) (a b : ℝ)
    (z : Fin (n + 1) → ℝ) (hz : StrictMono z)
    (hzi : ∀ i, z i ∈ Icc a b) (hfz : ∀ i, f (z i) = 0)
    (hc : ∀ j < n, ContinuousOn (iteratedDeriv j f) (Icc a b)) :
    ∃ x ∈ Icc a b, iteratedDeriv n f x = 0 := by
  induction n generalizing f with
  | zero => exact ⟨z 0, hzi 0, by simpa using hfz 0⟩
  | succ n ih =>
    have hstep (i : Fin (n + 1)) :
        ∃ x ∈ Ioo (z i.castSucc) (z i.succ), deriv f x = 0 := by
      apply exists_deriv_eq_zero (hz (by simp))
      · exact (show ContinuousOn f (Icc a b) by simpa using hc 0 (by omega)).mono
          (Icc_subset_Icc (hzi i.castSucc).1 (hzi i.succ).2)
      · rw [hfz, hfz]
    choose w hw hwzero using hstep
    have hwmono : StrictMono w := by
      intro i j hij
      exact (hw i).2.trans_le ((hz.monotone (by simpa using hij)).trans (hw j).1.le)
    have hwi (i : Fin (n + 1)) : w i ∈ Icc a b :=
      ⟨(hzi i.castSucc).1.trans (hw i).1.le, (hw i).2.le.trans (hzi i.succ).2⟩
    obtain ⟨x, hx, hzero⟩ := ih (deriv f) w hwmono hwi hwzero (by
      intro j hj
      simpa only [← iteratedDeriv_succ'] using hc (j + 1) (by omega))
    exact ⟨x, hx, by simpa only [iteratedDeriv_succ'] using hzero⟩

private theorem polynomial_top_deriv (p : ℝ[X]) (n : ℕ) (hp : p.natDegree ≤ n)
    (x : ℝ) : iteratedDeriv n (fun t => p.eval t) x = (n.factorial : ℝ) * p.coeff n := by
  have hcomm : Function.Semiconj (fun q : ℝ[X] => fun t => q.eval t)
      Polynomial.derivative deriv := by
    intro q
    funext t
    exact (q.deriv).symm
  rw [iteratedDeriv_eq_iterate, ← hcomm.iterate_right n p]
  have hdeg : (Polynomial.derivative^[n] p).natDegree ≤ 0 :=
    (natDegree_iterate_derivative p n).trans (Nat.sub_eq_zero_of_le hp ▸ le_rfl)
  change (Polynomial.derivative^[n] p).eval x = _
  rw [eq_C_of_natDegree_le_zero hdeg, eval_C, coeff_iterate_derivative]
  simp [Nat.descFactorial_self, nsmul_eq_mul]

/-- The top interpolation coefficient is a derivative value divided by the factorial.
The nodes may be arbitrarily close. Smoothness is required only near the closed interval. -/
private theorem interpolate_coeff_mean (s : Finset ℝ) (n : ℕ) (hcard : s.card = n + 1)
    (a b : ℝ) (f : ℝ → ℝ) (hs : ∀ z ∈ s, z ∈ Icc a b)
    (hf : ∀ x ∈ Icc a b, ContDiffAt ℝ n f x) :
    ∃ x ∈ Icc a b,
      (n.factorial : ℝ) * (Lagrange.interpolate s id f).coeff n = iteratedDeriv n f x := by
  let p := Lagrange.interpolate s id f
  have hpinj : Set.InjOn (id : ℝ → ℝ) s := Function.injective_id.injOn
  have hpdeg : p.natDegree ≤ n := by
    apply natDegree_le_of_degree_le
    simpa [p, hcard] using Lagrange.degree_interpolate_le f hpinj
  have hp : ContDiff ℝ n (fun t => p.eval t) := by
    simpa only [coe_aeval_eq_eval] using p.contDiff_aeval (𝕜 := ℝ) n
  let z := s.orderEmbOfFin hcard
  have hzi (i : Fin (n + 1)) : z i ∈ Icc a b :=
    hs _ (s.orderEmbOfFin_mem hcard i)
  have hg : ∀ x ∈ Icc a b, ContDiffAt ℝ n (fun t => f t - p.eval t) x :=
    fun x hx => (hf x hx).sub hp.contDiffAt
  obtain ⟨x, hx, hz⟩ := rolle_nodes n (fun t => f t - p.eval t) a b z z.strictMono hzi
    (by
      intro i
      dsimp [p]
      apply sub_eq_zero.mpr
      exact (Lagrange.eval_interpolate_at_node f hpinj (s.orderEmbOfFin_mem hcard i)).symm) (by
      intro j hj x hx
      rw [iteratedDeriv_eq_equiv_comp]
      exact ((ContinuousMultilinearMap.piFieldEquiv ℝ (Fin j) ℝ).symm.continuous.continuousAt.comp
        ((hg x hx).continuousAt_iteratedFDeriv (by exact_mod_cast hj.le))).continuousWithinAt)
  refine ⟨x, hx, ?_⟩
  rw [iteratedDeriv_fun_sub (hf x hx) hp.contDiffAt, polynomial_top_deriv p n hpdeg] at hz
  exact (sub_eq_zero.mp hz).symm

/-- Multiplication by a constant scales the coefficient budget by its absolute value. -/
theorem coeffL1_C_mul (c : ℝ) (p : ℝ[X]) :
    coeffL1 (C c * p) = |c| * coeffL1 p := by
  simpa only [smul_eq_C_mul] using coeffL1_smul c p

/-- Exact coefficient budget of a linear nodal factor. -/
theorem coeffL1_X_sub_C (x : ℝ) : coeffL1 (X - C x) = 1 + |x| := by
  rw [coeffL1_eq_sum_range_of_natDegree_lt _ (m := 2) (by
    simp)]
  simp [sum_range_succ, add_comm]

private theorem coeffL1_nodal_le (s : Finset ℝ) (hs : ∀ x ∈ s, |x| ≤ 1) :
    coeffL1 (Lagrange.nodal s id) ≤ (2 : ℝ) ^ s.card := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Lagrange.nodal_empty, Finset.card_empty, pow_zero]
    change (C (1 : ℝ)).sum (fun _ c => |c|) ≤ 1
    rw [Polynomial.sum_C_index (by simp)]
    norm_num
  | @insert x s hx ih =>
    rw [Lagrange.nodal_insert_eq_nodal hx, card_insert_of_notMem hx, pow_succ]
    refine (coeffL1_mul_le _ _).trans ?_
    rw [coeffL1_X_sub_C]
    calc
      (1 + |id x|) * coeffL1 (Lagrange.nodal s id) ≤
          2 * (2 : ℝ)^s.card := mul_le_mul
        (by have := hs x (mem_insert_self x s); dsimp; linarith)
        (ih (fun y hy => hs y (mem_insert_of_mem hy)))
        (by apply sum_nonneg; intro i hi; exact abs_nonneg _)
        (by norm_num)
      _ = (2 : ℝ)^s.card * 2 := mul_comm _ _

/-- Adding a node changes the interpolant by a scalar multiple of the previous nodal product. -/
private theorem interpolate_insert (s : Finset ℝ) (x : ℝ) (hx : x ∉ s) (f : ℝ → ℝ) :
    Lagrange.interpolate (insert x s) id f = Lagrange.interpolate s id f +
      C ((Lagrange.interpolate (insert x s) id f).coeff s.card) * Lagrange.nodal s id := by
  classical
  let q := Lagrange.interpolate s id f
  let w := Lagrange.nodal s id
  let c := (f x - q.eval x) / w.eval x
  have hwx : w.eval x ≠ 0 := Lagrange.eval_nodal_not_at_node (by
    intro y hy heq
    exact hx (heq ▸ hy))
  have hqdeg : q.degree < (s.card : WithBot ℕ) :=
    Lagrange.degree_interpolate_lt f Function.injective_id.injOn
  have hrepr : q + C c * w = Lagrange.interpolate (insert x s) id f := by
    apply Lagrange.eq_interpolate_of_eval_eq f Function.injective_id.injOn
    · rw [card_insert_of_notMem hx]
      apply (degree_add_le _ _).trans_lt
      apply max_lt
      · exact hqdeg.trans (by exact_mod_cast Nat.lt_succ_self s.card)
      · rw [← smul_eq_C_mul]
        apply (degree_smul_le c w).trans_lt
        simpa [w] using (show (s.card : WithBot ℕ) < ((s.card + 1 : ℕ) : WithBot ℕ) by
          exact_mod_cast Nat.lt_succ_self s.card)
    · intro y hy
      rcases mem_insert.mp hy with rfl | hy
      · simp only [id_eq, eval_add, eval_mul, eval_C]
        dsimp [c]
        rw [div_mul_cancel₀ _ hwx]
        ring
      · simp only [id_eq, eval_add, eval_mul, eval_C]
        have hwy : w.eval y = 0 := Lagrange.eval_nodal_at_node (v := id) hy
        rw [hwy, mul_zero, add_zero]
        exact Lagrange.eval_interpolate_at_node f Function.injective_id.injOn hy
  have hc : (Lagrange.interpolate (insert x s) id f).coeff s.card = c := by
    rw [← hrepr, coeff_add, coeff_C_mul, coeff_eq_zero_of_degree_lt hqdeg]
    have hwtop : w.coeff s.card = 1 := by
      simpa [w] using (Lagrange.nodal_monic (s := s) (v := id)).coeff_natDegree
    rw [hwtop, mul_one, zero_add]
  rw [hc]
  exact hrepr.symm

/-- Uniform coefficient budget for exact interpolation on arbitrary finite distinct nodes.
The derivative bounds and unit-radius node bounds introduce no inverse separation factor. -/
theorem interpolate_coeffL1_le (s : Finset ℝ) (a b : ℝ) (f : ℝ → ℝ) (B : ℕ → ℝ)
    (hs : ∀ x ∈ s, x ∈ Icc a b) (hsunit : ∀ x ∈ s, |x| ≤ 1)
    (hf : ∀ x ∈ Icc a b, ContDiffAt ℝ (s.card - 1 : ℕ) f x)
    (hB : ∀ j < s.card, 0 ≤ B j)
    (hderiv : ∀ j < s.card, ∀ x ∈ Icc a b,
      |iteratedDeriv j f x| ≤ (j.factorial : ℝ) * B j) :
    coeffL1 (Lagrange.interpolate s id f) ≤ ∑ j ∈ range s.card, (2 : ℝ)^j * B j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [coeffL1]
  | @insert x s hx ih =>
    have hcard : (insert x s).card = s.card + 1 := card_insert_of_notMem hx
    have hsc (y : ℝ) (hy : y ∈ s) := hs y (mem_insert_of_mem hy)
    have hsu (y : ℝ) (hy : y ∈ s) := hsunit y (mem_insert_of_mem hy)
    have hfi : ∀ y ∈ Icc a b, ContDiffAt ℝ s.card f y := by simpa [hcard] using hf
    obtain ⟨y, hy, hmean⟩ := interpolate_coeff_mean (insert x s) s.card hcard a b f hs hfi
    have hcoeff : |(Lagrange.interpolate (insert x s) id f).coeff s.card| ≤ B s.card := by
      have hb := hderiv s.card (by omega) y hy
      rw [← hmean, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < s.card.factorial)] at hb
      exact (mul_le_mul_iff_right₀ (by positivity : (0 : ℝ) < s.card.factorial)).mp hb
    rw [interpolate_insert s x hx f, hcard, sum_range_succ]
    refine (coeffL1_add_le _ _).trans (add_le_add ?_ ?_)
    · exact ih hsc hsu (fun y hy => (hfi y hy).of_le (by exact_mod_cast Nat.sub_le s.card 1))
        (fun j hj => hB j (by omega)) (fun j hj => hderiv j (by omega))
    · rw [coeffL1_C_mul]
      exact (mul_le_mul hcoeff (coeffL1_nodal_le s hsu)
        (by apply sum_nonneg; intro i hi; exact abs_nonneg _) (hB _ (by omega))).trans_eq
        (mul_comm _ _)

end D5.S3.Analytic.Interpolation.UniformCoefficientBudget
