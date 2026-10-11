/- GID: D5/S3/Analytic/Interpolation/UniformCoefficientBudget
   generality: G
   mirror-B: D5/B/S3/Analytic/Interpolation/UniformCoefficientBudget
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Derivative budgets bound exact interpolation without node separation. -/

import D5.S3.Analytic.SincSquareDerivativeBudget
import Mathlib.Data.Finsupp.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
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

/-- A separation-free polynomial certificate on the actual union of two atomic supports.
The weights are attached to distinct real nodes, so coincident atoms have combined mass.
Only the larger endpoint needs a lower mass bound. -/
theorem atomic_endpoint_certificate (α β : ℝ →₀ ℝ) (η b y : ℝ)
    (hη : 0 < η) (hby : b < y) (hy : y ≤ 1)
    (hα : ∀ x, 0 ≤ α x) (hβ : ∀ x, 0 ≤ β x)
    (hβtotal : β.sum (fun _ w => w) = 1)
    (hαsupport : ∀ x ∈ α.support, x ∈ Icc 0 y)
    (hβsupport : ∀ x ∈ β.support, x ∈ Icc 0 b)
    (hmass : η ≤ α y) :
    ∃ P : ℝ[X], P.natDegree < (α.support ∪ β.support).card ∧
      1 ≤ α.sum (fun x w => w * P.eval x) - β.sum (fun x w => w * P.eval x) ∧
      coeffL1 P ≤ (2 / η) * ∑ j ∈ range (α.support ∪ β.support).card,
        (16 / (η * (y - b))) ^ j / (2 * j).factorial := by
  classical
  obtain ⟨hH, hH0, hHpos, hHtail, hHderiv⟩ :=
    SincSquareDerivativeBudget.endpoint_budget hη
  let δ := y - b
  have hδ : 0 < δ := sub_pos.mpr hby
  let f : ℝ → ℝ := fun x => SincSquareDerivativeBudget.endpoint η ((y - x) / δ)
  let s := α.support ∪ β.support
  let B : ℕ → ℝ := fun j => (8 / (η * δ)) ^ j / (2 * j).factorial
  let I := Lagrange.interpolate s id f
  have hs (x : ℝ) (hx : x ∈ s) : x ∈ Icc 0 y := by
    rcases mem_union.mp hx with hx | hx
    · exact hαsupport x hx
    · exact ⟨(hβsupport x hx).1, (hβsupport x hx).2.trans hby.le⟩
  have hf : ContDiff ℝ ⊤ f := hH.comp ((contDiff_const.sub contDiff_id).div_const δ)
  have hderiv (j : ℕ) (x : ℝ) (hx : x ∈ Icc 0 y) :
      |iteratedDeriv j f x| ≤ (j.factorial : ℝ) * B j := by
    have heq : f = fun x =>
        (fun t => SincSquareDerivativeBudget.endpoint η (δ⁻¹ * t)) (y - x) := by
      funext t
      dsimp [f]
      congr 1
      ring
    rw [heq, iteratedDeriv_comp_const_sub j
      (fun t => SincSquareDerivativeBudget.endpoint η (δ⁻¹ * t)) y,
      iteratedDeriv_comp_const_mul (hH.of_le (by simp))]
    simp only [smul_eq_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_pos (inv_pos.mpr hδ)]
    have hb := (div_le_iff₀ (by positivity : (0 : ℝ) < j.factorial)).mp
      (hHderiv j (δ⁻¹ * (y - x)) (mul_nonneg (inv_nonneg.mpr hδ.le)
        (sub_nonneg.mpr hx.2)))
    calc
      (δ⁻¹) ^ j * |iteratedDeriv j (SincSquareDerivativeBudget.endpoint η)
          (δ⁻¹ * (y - x))| ≤
          (δ⁻¹) ^ j * ((8 / η) ^ j / (2 * j).factorial * j.factorial) :=
        mul_le_mul_of_nonneg_left hb (pow_nonneg (inv_nonneg.mpr hδ.le) j)
      _ = (j.factorial : ℝ) * B j := by
        dsimp [B]
        rw [show 8 / (η * δ) = δ⁻¹ * (8 / η) by
          simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc], mul_pow]
        ring
  have hbudget : coeffL1 I ≤ ∑ j ∈ range s.card, (16 / (η * δ))^j / (2*j).factorial := by
    refine (interpolate_coeffL1_le s 0 y f B hs (fun x hx => ?_)
      (fun x _ => hf.contDiffAt.of_le (by simp))
      (fun j _ => by dsimp [B]; positivity) (fun j _ x hx => hderiv j x hx)).trans_eq ?_
    · rw [abs_of_nonneg (hs x hx).1]
      exact (hs x hx).2.trans hy
    · apply sum_congr rfl
      intro j hj
      dsimp [B]
      rw [← mul_div_assoc, ← mul_pow]
      congr 2
      ring
  have hyα : y ∈ α.support := Finsupp.mem_support_iff.mpr (ne_of_gt (hη.trans_le hmass))
  have hIe (x : ℝ) (hx : x ∈ s) : I.eval x = f x :=
    Lagrange.eval_interpolate_at_node f Function.injective_id.injOn hx
  have hfy : f y = 1 := by simp [f, hH0]
  have hIα : η ≤ α.sum (fun x w => w * I.eval x) := by
    calc
      η ≤ α y := hmass
      _ = α y * I.eval y := by rw [hIe y (mem_union_left _ hyα), hfy, mul_one]
      _ ≤ α.sum (fun x w => w * I.eval x) := by
        apply single_le_sum (fun x hx => ?_) hyα
        rw [hIe x (mem_union_left _ hx)]
        exact mul_nonneg (hα x) (hHpos _ (div_nonneg
          (sub_nonneg.mpr (hαsupport x hx).2) hδ.le))
  have hIβ : β.sum (fun x w => w * I.eval x) ≤ η / 2 := by
    calc
      β.sum (fun x w => w * I.eval x) ≤ β.sum (fun x w => w * (η / 2)) := by
        apply sum_le_sum
        intro x hx
        dsimp only
        rw [hIe x (mem_union_right _ hx)]
        apply mul_le_mul_of_nonneg_left (hHtail _ ?_) (hβ x)
        apply (le_div_iff₀ hδ).mpr
        dsimp [δ]
        linarith [(hβsupport x hx).2]
      _ = η / 2 := by
        change (∑ x ∈ β.support, β x * (η / 2)) = _
        rw [← sum_mul]
        change β.sum (fun _ w => w) * (η / 2) = _
        rw [hβtotal, one_mul]
  refine ⟨C (2 / η) * I, ?_, ?_, ?_⟩
  · apply lt_of_le_of_lt (natDegree_C_mul_le _ _)
    apply (natDegree_lt_iff_degree_lt (show I ≠ 0 from fun hz => by
      have := hIe y (mem_union_left _ hyα)
      rw [hz, eval_zero, hfy] at this
      norm_num at this)).mpr
    exact Lagrange.degree_interpolate_lt f Function.injective_id.injOn
  · have hscale (γ : ℝ →₀ ℝ) :
        γ.sum (fun x w => w * (C (2 / η) * I).eval x) =
          (2 / η) * γ.sum (fun x w => w * I.eval x) := by
      simp only [Finsupp.sum, eval_mul, eval_C, mul_left_comm _ (2 / η), mul_sum]
    rw [hscale, hscale, ← mul_sub]
    calc
      1 = (2 / η) * (η / 2) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  · rw [coeffL1_C_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 / η)]
    exact mul_le_mul_of_nonneg_left hbudget (by positivity)

/-- The even factorial denominator supplies a square in the truncation order. -/
private theorem factorial_series_le (z : ℝ) (hz : 0 ≤ z) (q : ℕ) (hq : 0 < q) :
    (∑ j ∈ range (q + 1), z ^ j / (2 * j).factorial) ≤
      (Real.exp 1 * max 1 (z / (q : ℝ)^2)) ^ q := by
  let B := max 1 (z / (q : ℝ)^2)
  have hB : 1 ≤ B := le_max_left _ _
  have hqR : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hzB : z ≤ B * (q : ℝ)^2 := by
    exact (div_le_iff₀ (sq_pos_of_pos hqR)).mp (le_max_right _ _)
  calc
    (∑ j ∈ range (q + 1), z ^ j / (2 * j).factorial) ≤
        ∑ j ∈ range (q + 1), B^q * ((q : ℝ)^(2*j) / (2*j).factorial) := by
      apply sum_le_sum
      intro j hj
      have hjq : j ≤ q := Nat.le_of_lt_succ (mem_range.mp hj)
      have hp := (pow_le_pow_left₀ hz hzB j).trans
        (show (B * (q : ℝ)^2)^j ≤ B^q * (q : ℝ)^(2*j) by
          rw [mul_pow, ← pow_mul]
          exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hB hjq) (by positivity))
      simpa only [mul_div_assoc] using
        div_le_div_of_nonneg_right hp (by positivity : (0 : ℝ) ≤ (2*j).factorial)
    _ = B^q * ∑ j ∈ range (q + 1), (q : ℝ)^(2*j) / (2*j).factorial :=
      (mul_sum ..).symm
    _ ≤ B^q * Real.cosh q := mul_le_mul_of_nonneg_left
      (sum_le_hasSum (range (q + 1)) (fun j _ => by positivity) (Real.hasSum_cosh (q : ℝ)))
      (by positivity)
    _ ≤ B^q * Real.exp q := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [Real.cosh_eq]
      have he := Real.exp_le_exp.mpr (show -(q : ℝ) ≤ q by linarith [hqR])
      linarith
    _ = (Real.exp 1 * B)^q := by
      rw [show (q : ℝ) = q * 1 by ring, Real.exp_nat_mul, mul_pow]
      ring

/-- The sparse endpoint certificate with a square-order coefficient budget. -/
theorem sparse_endpoint_coefficient_certificate (α β : ℝ →₀ ℝ) (η b y : ℝ)
    (q : ℕ) (hq : 0 < q) (hN : (α.support ∪ β.support).card ≤ q + 1)
    (hη : 0 < η) (hby : b < y) (hy : y ≤ 1)
    (hα : ∀ x, 0 ≤ α x) (hβ : ∀ x, 0 ≤ β x)
    (hβtotal : β.sum (fun _ w => w) = 1)
    (hαsupport : ∀ x ∈ α.support, x ∈ Icc 0 y)
    (hβsupport : ∀ x ∈ β.support, x ∈ Icc 0 b)
    (hmass : η ≤ α y) :
    ∃ P : ℝ[X], P.natDegree ≤ q ∧
      1 ≤ α.sum (fun x w => w * P.eval x) - β.sum (fun x w => w * P.eval x) ∧
      coeffL1 P ≤ (2 / η) *
        (Real.exp 1 * max 1 ((16 / (η * (y - b))) / (q : ℝ)^2)) ^ q := by
  obtain ⟨P, hPdeg, hPsep, hPnorm⟩ := atomic_endpoint_certificate α β η b y
    hη hby hy hα hβ hβtotal hαsupport hβsupport hmass
  refine ⟨P, by omega, hPsep, hPnorm.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply le_trans (sum_le_sum_of_subset_of_nonneg (range_mono hN) (fun j _ _ => ?_))
    (factorial_series_le _ (by positivity) q hq)
  positivity

/-- The Laplace curve of finitely supported real atomic weights. -/
def atomicLaplace (μ : ℝ →₀ ℝ) (t : ℝ) : ℝ :=
  μ.sum (fun E w => w * Real.exp (-t * E))

/-- A sparse Laplace certificate on one fixed sampling grid.
No assumption separates atoms, and only the lower endpoint of μ needs a mass bound. -/
theorem sparse_laplace_grid_certificate (μ ν : ℝ →₀ ℝ) (η gμ gν h : ℝ)
    (q : ℕ) (hq : 0 < q) (hN : μ.support.card + ν.support.card ≤ q + 1)
    (hη : 0 < η) (hh : 0 < h) (hg : gμ < gν) (hgμ : 0 ≤ gμ)
    (hμ : ∀ E, 0 ≤ μ E) (hν : ∀ E, 0 ≤ ν E)
    (hνtotal : ν.sum (fun _ w => w) = 1)
    (hμsupport : ∀ E ∈ μ.support, gμ ≤ E)
    (hνsupport : ∀ E ∈ ν.support, gν ≤ E)
    (hmass : η ≤ μ gμ) :
    ∃ a : ℕ → ℝ,
      1 ≤ ∑ k ∈ range (q + 1), a k *
        (atomicLaplace μ ((k : ℝ) * h) - atomicLaplace ν ((k : ℝ) * h)) ∧
      (∑ k ∈ range (q + 1), |a k|) ≤ (2 / η) *
        (Real.exp 1 * max 1
          ((16 / (η * (Real.exp (-h * gμ) - Real.exp (-h * gν)))) / (q : ℝ)^2))^q := by
  classical
  let x : ℝ ↪ ℝ := ⟨fun E => Real.exp (-h * E), by
    intro a b hab
    have he := Real.exp_injective hab
    exact (mul_right_inj' (neg_ne_zero.mpr hh.ne')).mp he⟩
  let α := Finsupp.mapDomain x μ
  let β := Finsupp.mapDomain x ν
  have hpush (σ : ℝ →₀ ℝ) (F : ℝ → ℝ) :
      (Finsupp.mapDomain x σ).sum (fun t w => w * F t) =
        σ.sum (fun E w => w * F (x E)) :=
    Finsupp.sum_mapDomain_index (fun _ => zero_mul _) (fun _ _ _ => add_mul ..)
  have hpos (σ : ℝ →₀ ℝ) (hσ : ∀ E, 0 ≤ σ E) (t : ℝ) :
      0 ≤ (Finsupp.mapDomain x σ) t := by
    by_cases ht : (Finsupp.mapDomain x σ) t = 0
    · rw [ht]
    · obtain ⟨E, rfl⟩ := Finsupp.mem_range_of_mapDomain_ne_zero ht
      simpa only [Finsupp.mapDomain_apply x.injective] using hσ E
  have hsupp (σ : ℝ →₀ ℝ) (g : ℝ) (hσ : ∀ E ∈ σ.support, g ≤ E) :
      ∀ t ∈ (Finsupp.mapDomain x σ).support, t ∈ Icc 0 (x g) := by
    intro t ht
    rw [Finsupp.support_mapDomain_embedding] at ht
    obtain ⟨E, hE, rfl⟩ := mem_map.mp ht
    refine ⟨(Real.exp_pos _).le, Real.exp_le_exp.mpr ?_⟩
    exact mul_le_mul_of_nonpos_left (hσ E hE) (neg_nonpos.mpr hh.le)
  have htotal : β.sum (fun _ w => w) = 1 := by
    simpa only [mul_one] using (hpush ν (fun _ => 1)).trans (by simpa using hνtotal)
  have hcard : (α.support ∪ β.support).card ≤ q + 1 := by
    apply (Finset.card_union_le _ _).trans
    simpa only [α, β, Finsupp.support_mapDomain_embedding, card_map] using hN
  obtain ⟨P, hdeg, hsep, hnorm⟩ := sparse_endpoint_coefficient_certificate α β η (x gν) (x gμ)
    q hq hcard hη (Real.exp_lt_exp.mpr (by nlinarith))
    (by exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) hgμ))
    (hpos μ hμ) (hpos ν hν) htotal (hsupp μ gμ hμsupport) (hsupp ν gν hνsupport)
    (by simpa only [α, Finsupp.mapDomain_apply x.injective] using hmass)
  have hpoly (σ : ℝ →₀ ℝ) :
      (Finsupp.mapDomain x σ).sum (fun t w => w * P.eval t) =
        ∑ k ∈ range (q + 1), P.coeff k * atomicLaplace σ ((k : ℝ) * h) := by
    rw [hpush]
    change (∑ E ∈ σ.support, σ E * P.eval (x E)) = _
    calc
      _ = ∑ E ∈ σ.support, ∑ k ∈ range (q + 1),
          P.coeff k * (σ E * Real.exp (-((k : ℝ) * h) * E)) := by
        apply sum_congr rfl
        intro E hE
        rw [eval_eq_sum_range' (Nat.lt_succ_of_le hdeg), mul_sum]
        apply sum_congr rfl
        intro k hk
        change σ E * (P.coeff k * Real.exp (-h * E)^k) = _
        rw [← Real.exp_nat_mul]
        rw [show (k : ℝ) * (-h * E) = -((k : ℝ) * h) * E by ring]
        ring
      _ = ∑ k ∈ range (q + 1), ∑ E ∈ σ.support,
          P.coeff k * (σ E * Real.exp (-((k : ℝ) * h) * E)) := sum_comm
      _ = _ := by simp only [atomicLaplace, Finsupp.sum, mul_sum]
  refine ⟨P.coeff, ?_, ?_⟩
  · rw [hpoly, hpoly] at hsep
    simpa only [mul_sub, sum_sub_distrib] using hsep
  · rw [← coeffL1_eq_sum_range_of_natDegree_lt P (Nat.lt_succ_of_le hdeg)]
    exact hnorm

/-- Sparse Laplace separation with one jointly chosen degree and legal time grid.
The scale condition is satisfied by the sparse branch of the uniform order selection. -/
theorem sparse_laplace_window_certificate (μ ν : ℝ →₀ ℝ) (η E gμ gν U : ℝ)
    (m : ℕ) (hm : 0 < m) (hU : 0 < U) (hE : 0 < E)
    (hη : 0 < η) (hη1 : η ≤ 1) (hgμ : 0 ≤ gμ) (hg : gμ < gν) (hgν : gν ≤ E)
    (hμ : ∀ t, 0 ≤ μ t) (hν : ∀ t, 0 ≤ ν t)
    (hνtotal : ν.sum (fun _ w => w) = 1)
    (hμsupport : ∀ t ∈ μ.support, gμ ≤ t)
    (hνsupport : ∀ t ∈ ν.support, gν ≤ t)
    (hmass : η ≤ μ gμ) (hμcard : μ.support.card ≤ m) (hνcard : ν.support.card ≤ m)
    (hmcap : m ≤ ⌈3 / Real.sqrt (η * ((gν - gμ) / E))⌉₊) :
    let q := 2 * m - 1
    let M := max 1 ((q : ℝ) / U)
    let h := 1 / (M * E)
    ∃ a : ℕ → ℝ,
      (∀ k ≤ q, (k : ℝ) * h ∈ Icc 0 (U / E)) ∧
      1 ≤ ∑ k ∈ range (q + 1), a k *
        (atomicLaplace μ ((k : ℝ) * h) - atomicLaplace ν ((k : ℝ) * h)) ∧
      (∑ k ∈ range (q + 1), |a k|) ≤
        (288 * M / (η^2 * (m : ℝ)^2 * ((gν - gμ) / E)))^q := by
  classical
  dsimp only
  let q := 2 * m - 1
  let M := max 1 ((q : ℝ) / U)
  let h := 1 / (M * E)
  let Δ := (gν - gμ) / E
  let δ := Real.exp (-h * gμ) - Real.exp (-h * gν)
  let t := M / ((m : ℝ)^2 * Δ)
  have hq : 0 < q := by dsimp [q]; omega
  have hmq : m ≤ q := by dsimp [q]; omega
  have hqR : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hM1 : 1 ≤ M := le_max_left _ _
  have hM : 0 < M := zero_lt_one.trans_le hM1
  have hh : 0 < h := by dsimp [h]; positivity
  have hΔ : 0 < Δ := div_pos (sub_pos.mpr hg) hE
  have hδ : 0 < δ := sub_pos.mpr (Real.exp_lt_exp.mpr (by nlinarith))
  have ht : 0 < t := by dsimp [t]; positivity
  have hscale : (m : ℝ)^2 * Δ ≤ 16 / η := by
    have hΔ1 : Δ ≤ 1 := (div_le_one hE).mpr (by linarith)
    have hηΔ : 0 < η * Δ := mul_pos hη hΔ
    have hsqrt : 0 < Real.sqrt (η * Δ) := Real.sqrt_pos.mpr hηΔ
    have hsqrt1 : Real.sqrt (η * Δ) ≤ 1 := by
      apply (Real.sqrt_le_one).mpr
      exact (mul_le_mul_of_nonneg_left hΔ1 hη.le).trans (by simpa using hη1)
    have hceil := Nat.ceil_lt_add_one (by positivity : 0 ≤ 3 / Real.sqrt (η * Δ))
    have hmr : (m : ℝ) ≤ (⌈3 / Real.sqrt (η * Δ)⌉₊ : ℕ) := by exact_mod_cast hmcap
    have hmul := mul_le_mul_of_nonneg_right (hmr.trans hceil.le) hsqrt.le
    rw [add_mul, div_mul_cancel₀ _ hsqrt.ne', one_mul] at hmul
    have hprod : (m : ℝ) * Real.sqrt (η * Δ) ≤ 4 := by linarith
    have hprod0 : 0 ≤ (m : ℝ) * Real.sqrt (η * Δ) := by positivity
    have hsquare := sq_le_sq₀ hprod0 (by norm_num : (0 : ℝ) ≤ 4) |>.mpr hprod
    rw [mul_pow, Real.sq_sqrt hηΔ.le] at hsquare
    apply (le_div_iff₀ hη).mpr
    nlinarith
  have htlow : η / 16 ≤ t := by
    apply (le_div_iff₀ (by positivity : 0 < (m : ℝ)^2 * Δ)).mpr
    have hs : (m : ℝ)^2 * Δ * η ≤ 16 := (le_div_iff₀ hη).mp hscale
    nlinarith
  have hhE : h * E ≤ 1 := by
    dsimp [h]
    field_simp
    exact hM1
  have hbase : (Real.exp 1)⁻¹ ≤ Real.exp (-h * gν) := by
    rw [← Real.exp_neg]
    apply Real.exp_le_exp.mpr
    have hu := mul_le_mul_of_nonneg_left hgν hh.le
    linarith
  have hgap : h * (gν - gμ) * Real.exp (-h * gν) ≤ δ := by
    have he := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (h * (gν - gμ)))
      (Real.exp_pos (-h * gν)).le
    rw [← Real.exp_add, show h * (gν - gμ) + (-h * gν) = -h * gμ by ring] at he
    dsimp [δ]
    nlinarith
  have hδlower : Δ ≤ 3 * M * δ := by
    have hfirst := (mul_le_mul_of_nonneg_left hbase
      (mul_nonneg hh.le (sub_nonneg.mpr hg.le))).trans hgap
    have hid : h * (gν - gμ) * (Real.exp 1)⁻¹ = Δ / (Real.exp 1 * M) := by
      dsimp [h, Δ]
      ring
    rw [hid] at hfirst
    have hb := (div_le_iff₀ (mul_pos (Real.exp_pos 1) hM)).mp hfirst
    have he := mul_le_mul_of_nonneg_right Real.exp_one_lt_three.le (mul_nonneg hM.le hδ.le)
    nlinarith
  have hmqsq : (m : ℝ)^2 ≤ (q : ℝ)^2 := by exact_mod_cast Nat.pow_le_pow_left hmq 2
  have hz : (16 / (η * δ)) / (q : ℝ)^2 ≤ 48 * t / η := by
    rw [div_div, show 48 * t / η = (48 * M) / (η * (m : ℝ)^2 * Δ) by dsimp [t]; ring]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have ha := mul_le_mul_of_nonneg_left hδlower (sq_nonneg (m : ℝ))
    have hb := mul_le_mul_of_nonneg_left hmqsq (by positivity : 0 ≤ 3 * M * δ)
    have hc : (m : ℝ)^2 * Δ ≤ 3 * M * δ * (q : ℝ)^2 := by nlinarith
    have hd := mul_le_mul_of_nonneg_left hc hη.le
    nlinarith
  have hmax : max 1 ((16 / (η * δ)) / (q : ℝ)^2) ≤ 48 * t / η := by
    apply max_le _ hz
    apply (le_div_iff₀ hη).mpr
    linarith
  have hcoeff : (2 / η) *
      (Real.exp 1 * max 1 ((16 / (η * δ)) / (q : ℝ)^2))^q ≤
        (288 * M / (η^2 * (m : ℝ)^2 * Δ))^q := by
    have ha : 1 ≤ 2 / η := (le_div_iff₀ hη).mpr (by linarith)
    have hb : Real.exp 1 * max 1 ((16 / (η * δ)) / (q : ℝ)^2) ≤ 144 * t / η := by
      calc
        _ ≤ 3 * (48 * t / η) := mul_le_mul Real.exp_one_lt_three.le hmax
          (by positivity) (by norm_num)
        _ = _ := by ring
    calc
      _ ≤ (2 / η)^q * (144 * t / η)^q := mul_le_mul
        (by simpa using pow_le_pow_right₀ ha (show 1 ≤ q by omega))
        (pow_le_pow_left₀ (by positivity) hb q) (by positivity) (by positivity)
      _ = _ := by
        rw [← mul_pow]
        congr 1
        dsimp [t]
        ring
  obtain ⟨a, hsep, hnorm⟩ := sparse_laplace_grid_certificate μ ν η gμ gν h q hq
    (by dsimp [q]; omega) hη hh hg hgμ hμ hν hνtotal hμsupport hνsupport hmass
  refine ⟨a, ?_, hsep, hnorm.trans hcoeff⟩
  intro k hk
  refine ⟨mul_nonneg (Nat.cast_nonneg _) hh.le, ?_⟩
  have hkR : (k : ℝ) ≤ q := Nat.cast_le.mpr hk
  have hwin : (q : ℝ) ≤ M * U := (div_le_iff₀ hU).mp (le_max_right _ _)
  change (k : ℝ) * (1 / (M * E)) ≤ U / E
  rw [mul_one_div]
  apply (div_le_div_iff₀ (mul_pos hM hE) hE).mpr
  nlinarith [mul_le_mul_of_nonneg_right (hkR.trans hwin) hE.le]


end D5.S3.Analytic.Interpolation.UniformCoefficientBudget
