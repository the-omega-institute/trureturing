/- GID: D5/S3/Zeros/Jensen/SourceJensenPositiveExtension
   generality: I
   mirror-B: D5/B/S3/Zeros/Jensen/SourceJensenPositiveExtension
   mirror-E: none(waiver:universal-positive-extension)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.SchurComplement]
   utility: none
   digest: Nonnegative source residues exactly characterize positive real extension. -/

import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Algebra.Polynomial.Reverse
import D5.S3.Zeros.Jensen.SourceJensenIntegralExtension
import D5.S3.Zeros.Jensen.SourceThetaMomentBounds
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.Zeros.Jensen.SourceJensenPositiveExtension
open Polynomial Matrix NormalizedJensenDegreeLowering SourceThetaMomentBounds
open SourceJensenIntegralExtension

/-- The specified real symmetric arrow matrix; the index sum has size n+2. -/
def arrow (n : ℕ) (a : ℝ) (t eta : Fin (n+1) → ℝ) :
    Matrix (Fin 1 ⊕ Fin (n+1)) (Fin 1 ⊕ Fin (n+1)) ℝ :=
  fromBlocks (of fun _ _ => a / ((n+2 : ℕ) : ℝ))
    (of fun _ i => Real.sqrt (eta i)) (of fun i _ => Real.sqrt (eta i)) (diagonal t)

private theorem arrow_hermitian (n : ℕ) (a : ℝ) (t eta : Fin (n+1) → ℝ) :
    (arrow n a t eta).IsHermitian := by
  ext (i | i) (j | j) <;> simp [arrow, Matrix.fromBlocks, conjTranspose_apply, diagonal, eq_comm]
  split_ifs with h
  · subst j; rfl
  · rfl

private theorem arrow_schur (n : ℕ) (a : ℝ) (t eta : Fin (n+1) → ℝ)
    (heta : ∀ i, 0 ≤ eta i) (x : ℝ) (hx : ∀ i, x ≠ t i) :
    (arrow n a t eta).charpoly.eval x =
      (∏ i, (x-t i)) * (x-a/((n+2 : ℕ) : ℝ) - ∑ i, eta i/(x-t i)) := by
  let v : Fin (n+1) → ℝ := fun i => x-t i
  letI : Invertible v := {
    invOf := fun i => (x-t i)⁻¹
    invOf_mul_self := by funext i; exact inv_mul_cancel₀ (sub_ne_zero.mpr (hx i))
    mul_invOf_self := by funext i; exact mul_inv_cancel₀ (sub_ne_zero.mpr (hx i)) }
  letI : Invertible (diagonal v) := diagonalInvertible v
  have hinv : ⅟(diagonal v) = diagonal (fun i => (x-t i)⁻¹) := by
    rw [invOf_diagonal_eq]
    rfl
  rw [eval_charpoly]
  have hm : scalar (Fin 1 ⊕ Fin (n+1)) x - arrow n a t eta =
      fromBlocks (of fun _ _ : Fin 1 => x-a/((n+2 : ℕ) : ℝ))
        (of fun (_ : Fin 1) i => -Real.sqrt (eta i))
        (of fun i (_ : Fin 1) => -Real.sqrt (eta i)) (diagonal v) := by
    ext (i | i) (j | j)
    · simp [arrow, Matrix.fromBlocks, scalar, diagonal, v, Subsingleton.elim i j]
    · simp [arrow, Matrix.fromBlocks, scalar, diagonal, v]
    · simp [arrow, Matrix.fromBlocks, scalar, diagonal, v]
    · by_cases hij : i = j <;> simp [arrow, Matrix.fromBlocks, scalar, diagonal, v, hij]
  rw [hm, det_fromBlocks₂₂, det_diagonal, det_fin_one, hinv]
  congr 1
  simp only [Matrix.sub_apply, Matrix.mul_apply, of_apply, diagonal_apply, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have hs := Real.sq_sqrt (heta i)
  rw [div_eq_mul_inv]
  calc
    _ = Real.sqrt (eta i)^2 * (x-t i)⁻¹ := by ring
    _ = _ := by rw [hs]

private theorem nodal_derivative (n : ℕ) (q : ℝ[X]) (t : Fin (n+1) → ℝ)
    (ht : Function.Injective t) (hq : q.natDegree ≤ n+2) (hmonic : q.coeff (n+2) = 1)
    (hcrit : ∀ i, q.derivative.eval (t i) = 0) :
    q.derivative = C ((n+2 : ℕ) : ℝ) * Lagrange.nodal Finset.univ t := by
  have hdeg : q.natDegree = n+2 :=
    natDegree_eq_of_le_of_coeff_ne_zero hq (by rw [hmonic]; exact one_ne_zero)
  have hqmonic : q.Monic := by simpa only [Monic, leadingCoeff, hdeg] using hmonic
  have hd : ((n+2 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (show n+2 ≠ 0 by omega)
  have hder : q.derivative.degree = (n+1 : ℕ) := by
    rw [degree_eq_natDegree (derivative_ne_zero.mpr (by omega)), natDegree_derivative, hdeg]
    simp
  apply Polynomial.eq_of_degree_le_of_eval_index_eq Finset.univ ht.injOn
  · simpa using hder.le
  · rw [hder, degree_C_mul hd, Lagrange.degree_nodal]
    simp
  · rw [leadingCoeff_derivative, hqmonic, hdeg,
      Lagrange.nodal_monic.leadingCoeff_C_mul]
    simp
  · intro i _
    simp [hcrit, Lagrange.eval_nodal_at_node (Finset.mem_univ i)]

private theorem q_ratio_formula (n : ℕ) (q : ℝ[X]) (a : ℝ)
    (t : Fin (n+1) → ℝ) (ht : Function.Injective t)
    (hdeg : q.natDegree ≤ n+2) (hmonic : q.coeff (n+2) = 1)
    (hlinear : q.coeff (n+1) = -a)
    (hcrit : ∀ i, q.derivative.eval (t i) = 0)
    (x : ℝ) (hx : ∀ i, x ≠ t i) :
    (∏ i, (x-t i)) * (x-a/((n+2 : ℕ) : ℝ) -
      ∑ i, (-((n+2 : ℕ) : ℝ)*q.eval (t i)/q.derivative.derivative.eval (t i))/(x-t i)) =
      q.eval x := by
  let d : ℝ := ((n+2 : ℕ) : ℝ)
  have hd : d ≠ 0 := by dsimp [d]; exact_mod_cast (show n+2 ≠ 0 by omega)
  have hdc : (n : ℝ) + 2 ≠ 0 := by exact_mod_cast (show n+2 ≠ 0 by omega)
  let R := q - C d⁻¹ * X * q.derivative + C (a / d^2) * q.derivative
  have hc (k : ℕ) : R.coeff k = q.coeff k - d⁻¹ * (q.coeff k * (k : ℝ)) +
      (a/d^2) * (q.coeff (k+1) * ((k+1 : ℕ) : ℝ)) := by
    have hh : (X*q.derivative).coeff k = q.coeff k * (k : ℝ) := by
      cases k <;> simp [coeff_X_mul, coeff_derivative]
    simp only [R, coeff_add, coeff_sub, mul_assoc, coeff_C_mul, hh, coeff_derivative]
    push_cast
    rfl
  have hRdeg : R.degree < (n+1 : ℕ) := by
    apply (degree_lt_iff_coeff_zero R (n+1)).mpr
    intro k hk
    rw [hc]
    by_cases hk₁ : k = n+1
    · subst k
      rw [hlinear, hmonic]
      dsimp [d]
      push_cast
      field_simp [hdc]
      ring
    · by_cases hk₂ : k = n+2
      · subst k
        rw [hmonic, coeff_eq_zero_of_natDegree_lt (by omega : q.natDegree < n+2+1)]
        dsimp [d]
        push_cast
        field_simp [hdc]
        ring
      · rw [coeff_eq_zero_of_natDegree_lt (by omega : q.natDegree < k),
          coeff_eq_zero_of_natDegree_lt (by omega : q.natDegree < k+1)]
        ring
  have hRe (i : Fin (n+1)) : R.eval (t i) = q.eval (t i) := by
    simp [R, hcrit]
  have hnodal := nodal_derivative n q t ht hdeg hmonic hcrit
  have hdd (i : Fin (n+1)) : q.derivative.derivative.eval (t i) =
      d * ∏ j ∈ Finset.univ.erase i, (t i-t j) := by
    rw [hnodal, derivative_C_mul, eval_mul, eval_C,
      Lagrange.eval_nodal_derivative_eval_node_eq (Finset.mem_univ i), Lagrange.eval_nodal]
  have hinterp := Lagrange.eq_interpolate (s := Finset.univ) (v := t) (f := R)
    ht.injOn (by simpa using hRdeg)
  have hv := congrArg (fun f : ℝ[X] => f.eval x) hinterp
  rw [Lagrange.eval_interpolate_not_at_node _ (fun i _ => hx i)] at hv
  simp only [hRe] at hv
  have hs : (∑ i, Lagrange.nodalWeight Finset.univ t i * (x-t i)⁻¹ * q.eval (t i)) =
      -(∑ i, (-d*q.eval (t i)/q.derivative.derivative.eval (t i))/(x-t i)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [Lagrange.nodalWeight_eq_eval_nodal_erase_inv, Lagrange.eval_nodal, hdd]
    simp [div_eq_mul_inv, mul_inv, hd, mul_assoc, mul_left_comm, mul_comm]
  have hder : q.derivative.eval x = d * (∏ i, (x-t i)) := by
    rw [hnodal, eval_mul, eval_C, Lagrange.eval_nodal]
  rw [hs, Lagrange.eval_nodal] at hv
  simp only [R, eval_add, eval_sub, eval_mul, eval_C, eval_X, hder] at hv
  change (∏ i, (x-t i)) * (x-a/d -
    ∑ i, (-d*q.eval (t i)/q.derivative.derivative.eval (t i))/(x-t i)) = q.eval x
  field_simp [hd] at hv ⊢
  linear_combination -hv

private def LaguerreAt (p : ℝ[X]) (x : ℝ) : Prop :=
  0 ≤ p.derivative.eval x ^ 2 - p.eval x * p.derivative.derivative.eval x

private theorem laguerre_splits (p : ℝ[X]) (hp : p.Splits) (x : ℝ) : LaguerreAt p x := by
  classical
  by_cases hx : p.eval x = 0
  · simp [LaguerreAt, hx, sq_nonneg]
  have hp0 : p ≠ 0 := by intro h; simp [h] at hx
  have hsum (y : ℝ) : (p.roots.map (fun z => 1/(y-z))).sum =
      ∑ z ∈ p.roots.toFinset, (p.roots.count z : ℝ)/(y-z) := by
    rw [Finset.sum_multiset_map_count]
    simp [nsmul_eq_mul, div_eq_mul_inv]
  have hf := (p.derivative.hasDerivAt x).fun_div (p.hasDerivAt x) hx
  have hg : HasDerivAt
      (fun y : ℝ => ∑ z ∈ p.roots.toFinset, (p.roots.count z : ℝ)/(y-z))
      (∑ z ∈ p.roots.toFinset, -(p.roots.count z : ℝ)/(x-z)^2) x := by
    apply HasDerivAt.fun_sum
    intro z hz
    have hxz : x-z ≠ 0 := by
      apply sub_ne_zero.mpr
      intro he
      apply hx
      rw [he]
      exact (mem_roots hp0).mp (Multiset.mem_toFinset.mp hz)
    simpa using (hasDerivAt_const x (p.roots.count z : ℝ)).fun_div
      ((hasDerivAt_id x).sub_const z) hxz
  have heq : (fun y : ℝ => p.derivative.eval y / p.eval y) =ᶠ[nhds x]
      (fun y : ℝ => ∑ z ∈ p.roots.toFinset, (p.roots.count z : ℝ)/(y-z)) := by
    filter_upwards [(p.hasDerivAt x).continuousAt.eventually_ne hx] with y hy
    exact (hp.eval_derivative_div_eval_of_ne_zero hy).trans (hsum y)
  have hi := hf.unique (hg.congr_of_eventuallyEq heq)
  have hn : (∑ z ∈ p.roots.toFinset, -(p.roots.count z : ℝ)/(x-z)^2) ≤ 0 := by
    apply Finset.sum_nonpos
    intro z _
    rw [neg_div]
    exact neg_nonpos.mpr (div_nonneg (by positivity) (sq_nonneg _))
  have hfrac : (p.derivative.derivative.eval x*p.eval x -
      p.derivative.eval x*p.derivative.eval x) / p.eval x^2 ≤ 0 := by rw [hi]; exact hn
  have hnum := mul_le_mul_of_nonneg_right hfrac (sq_nonneg (p.eval x))
  rw [div_mul_cancel₀ _ (pow_ne_zero 2 hx), zero_mul] at hnum
  dsimp only [LaguerreAt]
  nlinarith only [hnum]

private theorem arrow_charpoly (n : ℕ) (q : ℝ[X]) (a : ℝ)
    (t : Fin (n+1) → ℝ) (ht : Function.Injective t)
    (hdeg : q.natDegree ≤ n+2) (hmonic : q.coeff (n+2) = 1)
    (hlinear : q.coeff (n+1) = -a)
    (hcrit : ∀ i, q.derivative.eval (t i) = 0)
    (heta : ∀ i, 0 ≤ -((n+2 : ℕ) : ℝ)*q.eval (t i)/q.derivative.derivative.eval (t i)) :
    (arrow n a t (fun i => -((n+2 : ℕ) : ℝ)*q.eval (t i)/
      q.derivative.derivative.eval (t i))).charpoly = q := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.infinite_univ.sdiff (Set.finite_range t)).mono
  intro x hx
  have hxt : ∀ i, x ≠ t i := by
    intro i hi
    exact hx.2 ⟨i, hi.symm⟩
  change (arrow n a t _).charpoly.eval x = q.eval x
  rw [arrow_schur n a t _ heta x hxt]
  exact q_ratio_formula n q a t ht hdeg hmonic hlinear hcrit x hxt

private theorem residue_nonneg (n : ℕ) (q : ℝ[X]) (x : ℝ)
    (hsplit : q.Splits) (hcrit : q.derivative.eval x = 0)
    (hsecond : q.derivative.derivative.eval x ≠ 0) :
    0 ≤ -((n+2 : ℕ) : ℝ)*q.eval x/q.derivative.derivative.eval x := by
  have hL := laguerre_splits q hsplit x
  have hm : 0 ≤ -q.eval x * q.derivative.derivative.eval x := by
    simpa [LaguerreAt, hcrit] using hL
  calc
    _ = ((n+2 : ℕ) : ℝ) * (-q.eval x * q.derivative.derivative.eval x) /
      q.derivative.derivative.eval x ^ 2 := by field_simp
    _ ≥ 0 := div_nonneg (mul_nonneg (by positivity) hm) (sq_nonneg _)

def PositiveSplit (q : ℝ[X]) : Prop := q.Splits ∧ ∀ x, q.eval x = 0 → 0 < x

private theorem arrow_criterion (n : ℕ) (q : ℝ[X]) (a : ℝ)
    (t : Fin (n+1) → ℝ) (ht : Function.Injective t)
    (hdeg : q.natDegree ≤ n+2) (hmonic : q.coeff (n+2) = 1)
    (hlinear : q.coeff (n+1) = -a)
    (hcrit : ∀ i, q.derivative.eval (t i) = 0)
    (hno : ∀ x, x ≤ 0 → q.eval x ≠ 0) :
    let eta := fun i => -((n+2 : ℕ) : ℝ)*q.eval (t i)/q.derivative.derivative.eval (t i)
    (∀ i, q.derivative.derivative.eval (t i) ≠ 0) ∧
    (PositiveSplit q ↔ ∀ i, 0 ≤ eta i) ∧
      ((∀ i, 0 ≤ eta i) → (arrow n a t eta).PosDef ∧ (arrow n a t eta).charpoly = q) := by
  dsimp only
  let eta := fun i => -((n+2 : ℕ) : ℝ)*q.eval (t i)/q.derivative.derivative.eval (t i)
  have hnonzero (i : Fin (n+1)) : q.derivative.derivative.eval (t i) ≠ 0 := by
    have hnodal := nodal_derivative n q t ht hdeg hmonic hcrit
    rw [hnodal, derivative_C_mul, eval_mul, eval_C,
      Lagrange.eval_nodal_derivative_eval_node_eq (Finset.mem_univ i), Lagrange.eval_nodal]
    apply mul_ne_zero (by positivity)
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    apply sub_ne_zero.mpr
    exact fun h => (Finset.mem_erase.mp hj).1 (ht h).symm
  have hrootpos : ∀ x, q.eval x = 0 → 0 < x := by
    intro x hx
    exact lt_of_not_ge (fun h => hno x h hx)
  have hc (he : ∀ i, 0 ≤ eta i) : (arrow n a t eta).charpoly = q :=
    arrow_charpoly n q a t ht hdeg hmonic hlinear hcrit he
  have hh := arrow_hermitian n a t eta
  have hpd (he : ∀ i, 0 ≤ eta i) : (arrow n a t eta).PosDef := by
    apply hh.posDef_iff_eigenvalues_pos.mpr
    intro i
    apply hrootpos
    rw [← hc he, hh.charpoly_eq, eval_prod]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp
  refine ⟨hnonzero, ⟨?_, ?_⟩, fun he => ⟨hpd he, hc he⟩⟩
  · intro hp i
    exact residue_nonneg n q (t i) hp.1 (hcrit i) (hnonzero i)
  · intro he
    refine ⟨?_, hrootpos⟩
    rw [← hc he, hh.charpoly_eq]
    exact Splits.prod (fun i _ => Splits.X_sub_C _)

private theorem p_coeff (d k : ℕ) (hk : k ≤ d) :
    (sourceP d).coeff k = (d.descFactorial k : ℝ)/(d : ℝ)^k*sourceThetaCoefficient k := by
  simp only [sourceP, finsetSum_coeff, coeff_C_mul_X_pow]
  simp [Finset.mem_range, show k < d+1 by omega]

private theorem p_degree (d : ℕ) : (sourceP d).natDegree ≤ d := by
  apply natDegree_sum_le_of_forall_le
  intro k hk
  exact (natDegree_C_mul_X_pow_le _ _).trans (by simpa using Finset.mem_range.mp hk)

private theorem q_degree (d : ℕ) : (sourceQ d).natDegree ≤ d := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  change (((sourceP d).comp (C (-1)*X)).reflect d).coeff k = 0
  simp only [coeff_reflect, revAt_eq_self_of_lt hk, comp_C_mul_X_coeff]
  rw [coeff_eq_zero_of_natDegree_lt ((p_degree d).trans_lt hk), zero_mul]

private theorem q_coeff (d k : ℕ) (hk : k ≤ d) :
    (sourceQ d).coeff k = (sourceP d).coeff (d-k)*(-1)^(d-k) := by
  change (((sourceP d).comp (C (-1)*X)).reflect d).coeff k = _
  simp only [coeff_reflect, revAt_le hk, comp_C_mul_X_coeff]

private theorem q_no_nonpositive (d : ℕ) (hd : 1 ≤ d)
    (ha : ∀ k, 0 < sourceThetaCoefficient k) : ∀ x, x ≤ 0 → (sourceQ d).eval x ≠ 0 := by
  intro x hx
  by_cases hx0 : x = 0
  · subst x
    rw [← coeff_zero_eq_eval_zero, q_coeff d 0 (by omega), Nat.sub_zero,
      p_coeff d d le_rfl]
    exact mul_ne_zero (ne_of_gt (mul_pos
      (div_pos (by exact_mod_cast Nat.descFactorial_pos.mpr le_rfl)
        (pow_pos (by exact_mod_cast (show 0 < d by omega)) _)) (ha d)))
      (pow_ne_zero _ (by norm_num))
  have hpv : 0 < (sourceP d).eval (-1/x) := by
    have hy : 0 ≤ -1/x := div_nonneg_of_nonpos (by norm_num) hx
    simp only [sourceP, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
    apply Finset.sum_pos'
    · intro k hk
      exact mul_nonneg (mul_nonneg (div_nonneg (by positivity) (by positivity)) (ha k).le)
        (pow_nonneg hy k)
    · refine ⟨0, by simp, ?_⟩
      simpa using ha 0
  have hdeg : ((sourceP d).comp (C (-1)*X)).natDegree ≤ d := by
    apply natDegree_comp_le.trans
    calc
      _ ≤ (sourceP d).natDegree*1 := Nat.mul_le_mul_left _ (by
        simpa using (natDegree_mul_le (p := C (-1 : ℝ)) (q := X)))
      _ ≤ d := by simpa using p_degree d
  letI : Invertible (x⁻¹) := invertibleOfNonzero (inv_ne_zero hx0)
  have hh := eval₂_reflect_mul_pow (RingHom.id ℝ) (x⁻¹) d
    ((sourceP d).comp (C (-1)*X)) hdeg
  simp only [invOf_eq_inv, inv_inv, eval₂_id, eval_comp, eval_mul, eval_C,
    eval_X, neg_one_mul] at hh
  intro hzero
  change (sourceQ d).eval x * x⁻¹^d = (sourceP d).eval (-x⁻¹) at hh
  rw [hzero, zero_mul] at hh
  apply ne_of_gt hpv
  simpa [div_eq_mul_inv] using hh.symm

/-- The source residue, used at the simple critical nodes certified below. -/
def sourceCoupling (d : ℕ) (x : ℝ) : ℝ :=
  -(d : ℝ) * (sourceQ d).eval x / (sourceQ d).derivative.derivative.eval x

/-- The exact positive-root criterion and its specified positive definite realization.
The hypotheses are the preceding degree's distinct positive roots, not independently
assumed critical points. Zero couplings and repeated roots of the next degree are allowed. -/
theorem source_jensen_positive_extension (n : ℕ) (h0 : sourceThetaCoefficient 0 = 1)
    (lam : Fin (n+1) → ℝ) (hlam : Function.Injective lam)
    (hlampos : ∀ i, 0 < lam i) (hroot : ∀ i, (sourceQ (n+1)).eval (lam i) = 0) :
    let t := fun i => scale (n+2) * lam i
    let eta := fun i => sourceCoupling (n+2) (t i)
    (∀ i, 0 < t i) ∧
    (∀ i, (sourceQ (n+2)).derivative.derivative.eval (t i) ≠ 0) ∧
    (PositiveSplit (sourceQ (n+2)) ↔ ∀ i, 0 ≤ eta i) ∧
    ((∀ i, 0 ≤ eta i) →
      (arrow n (sourceThetaCoefficient 1) t eta).PosDef ∧
      (arrow n (sourceThetaCoefficient 1) t eta).charpoly = sourceQ (n+2)) := by
  let t := fun i => scale (n+2) * lam i
  have hs : 0 < scale (n+2) := by
    dsimp [scale]
    exact div_pos (by exact_mod_cast (show 0 < n+2-1 by omega)) (by positivity)
  have ht : Function.Injective t := by
    intro i j hij
    exact hlam (mul_left_cancel₀ hs.ne' hij)
  have hcrit (i : Fin (n+1)) : (sourceQ (n+2)).derivative.eval (t i) = 0 := by
    rw [(source_jensen_integral_extension (n+2) (by omega)).2.1]
    simp only [eval_mul, eval_C, eval_comp, eval_X]
    have hx : (scale (n+2))⁻¹ * t i = lam i := by
      dsimp [t]
      rw [← mul_assoc, inv_mul_cancel₀ hs.ne', one_mul]
    rw [hx, show n+2-1=n+1 by omega, hroot i, mul_zero]
  refine ⟨fun i => mul_pos hs (hlampos i), ?_⟩
  apply arrow_criterion n (sourceQ (n+2)) (sourceThetaCoefficient 1) t ht (q_degree (n+2))
  · rw [q_coeff _ _ le_rfl, Nat.sub_self, p_coeff _ _ (by omega)]
    simp [h0]
  · rw [q_coeff _ _ (by omega), show n+2-(n+1)=1 by omega,
      p_coeff _ _ (by omega)]
    have hd : (n : ℝ)+2 ≠ 0 := by positivity
    simp [Nat.descFactorial, hd]
  · exact hcrit
  · exact q_no_nonpositive (n+2) (by omega) (source_theta_normalization h0).2.2.2

#print axioms source_jensen_positive_extension
end D5.S3.Zeros.Jensen.SourceJensenPositiveExtension
