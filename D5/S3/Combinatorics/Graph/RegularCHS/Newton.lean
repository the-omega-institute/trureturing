/- GID: D5/S3/Combinatorics/Graph/RegularCHS/Newton
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/RegularCHS/Newton
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.RingTheory.PowerSeries.Derivative]
   utility: none
   digest: Closed walk Newton recurrence and coefficient comparison for graph CHS norms. -/

import D5.S3.Combinatorics.Graph.RegularCHS.Interface
import D5.S3.Combinatorics.Graph.PathCHS.PathCHSNormClosedForm
import Mathlib.RingTheory.PowerSeries.Derivative

noncomputable section
open Classical Finset Matrix PowerSeries
open scoped BigOperators
open D5.S3.Combinatorics.Graph.RegularCHS.Defs
open D5.S3.Combinatorics.Graph.RegularCHS.Interface
open D5.S3.Combinatorics.Graph.PathCHS.PathCHSNormClosedForm (hsymm_series_product geometric_mul_linear)

namespace D5.S3.Combinatorics.Graph.RegularCHS.Newton

/-- All comparison coefficients are nonnegative. -/
theorem bseq_nonneg (n r m : ℕ) : 0 ≤ bseq n r m := by
  induction m with
  | zero => exact (bseq_zero n r).symm ▸ (zero_le_one : (0 : ℝ) ≤ 1)
  | succ m ih =>
    rw [bseq]
    have h : (0 : ℝ) ≤ (n : ℝ) + 2 * (m + 1) - 2 := by
      nlinarith [Nat.cast_nonneg n (α := ℝ), Nat.cast_nonneg m (α := ℝ)]
    exact div_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) h) ih) (by positivity)

/-- Increasing the degree parameter increases every comparison coefficient. -/
theorem bseq_mono {n r : ℕ} (hr : 4 ≤ r) (m : ℕ) :
    bseq n 4 m ≤ bseq n r m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [bseq, bseq]
    have h : (0 : ℝ) ≤ (n : ℝ) + 2 * (m + 1) - 2 := by
      nlinarith [Nat.cast_nonneg n (α := ℝ), Nat.cast_nonneg m (α := ℝ)]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul (mul_le_mul_of_nonneg_right (by exact_mod_cast hr) h) ih
      (bseq_nonneg n 4 m) (mul_nonneg (Nat.cast_nonneg _) h)

/-- Real matrix traces agree with the natural closed walk count. -/
theorem trace_pow_eq_closedWalks {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) :
    ((G.adjMatrix ℝ) ^ k).trace = (closedWalks G k : ℝ) := by
  have hm : (G.adjMatrix ℕ).map (Nat.castRingHom ℝ) = G.adjMatrix ℝ := by
    ext i j
    simp only [Matrix.map_apply, SimpleGraph.adjMatrix_apply]
    split_ifs <;> simp
  have hp := (Nat.castRingHom ℝ).mapMatrix.map_pow (G.adjMatrix ℕ) k
  change ((G.adjMatrix ℕ) ^ k).map (Nat.castRingHom ℝ) = _ at hp
  rw [show (Nat.castRingHom ℝ).mapMatrix (G.adjMatrix ℕ) = G.adjMatrix ℝ from hm] at hp
  rw [← hp]
  simp [Matrix.trace, closedWalks]

/-- Spectral power sums count rooted closed walks. -/
theorem sum_eigenvalues_pow_eq_closedWalks {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) :
    ∑ i, (adjMatrix_isHermitian G).eigenvalues i ^ k = (closedWalks G k : ℝ) := by
  rw [← trace_pow_eq_closedWalks]
  have hs := (adjMatrix_isHermitian G).spectral_theorem
  conv_rhs => rw [hs, ← map_pow]
  simp only [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, Matrix.one_mul, Matrix.diagonal_pow,
    Matrix.trace_diagonal, RCLike.ofReal_real_eq_id]
  simp [Pi.pow_apply]

private def geometric (a : ℝ) : PowerSeries ℝ := mk fun k => a ^ k

private theorem derivative_geometric (a : ℝ) :
    derivative (geometric a) = C a * geometric a ^ 2 := by
  have h := (derivative (R := ℝ)).leibniz_of_mul_eq_one (geometric_mul_linear a)
  change derivative (geometric a) =
    -(geometric a) ^ 2 • derivative (1 - C a * X) at h
  simp only [map_sub, derivative_one, Derivation.leibniz, derivative_C, derivative_X,
    smul_eq_mul, mul_one, mul_zero, add_zero, zero_sub, mul_neg] at h
  simpa [mul_comm] using h

private theorem derivative_prod_geometric {ι : Type*} [DecidableEq ι]
    (a : ι → ℝ) (s : Finset ι) :
    derivative (∏ i ∈ s, geometric (a i)) =
      (∏ i ∈ s, geometric (a i)) * ∑ i ∈ s, C (a i) * geometric (a i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [prod_insert hi, sum_insert hi, Derivation.leibniz, derivative_geometric, ih]
    simp only [smul_eq_mul]
    ring

private theorem hsymm_series_eq_geometric {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℝ) :
    (mk fun d => MvPolynomial.eval a (MvPolynomial.hsymm ι ℝ d)) =
      ∏ i, geometric (a i) := by
  let H : PowerSeries ℝ := mk fun d => MvPolynomial.eval a (MvPolynomial.hsymm ι ℝ d)
  let P : PowerSeries ℝ := ∏ i, (1 - C (a i) * X)
  have hH : H * P = 1 := hsymm_series_product a
  have hP : (∏ i, geometric (a i)) * P = 1 := by
    rw [show P = ∏ i, (1 - C (a i) * X) from rfl, ← prod_mul_distrib]
    simp only [geometric, geometric_mul_linear, prod_const_one]
  change H = _
  calc
    H = H * ((∏ i, geometric (a i)) * P) := by rw [hP, mul_one]
    _ = (∏ i, geometric (a i)) * (H * P) := by ring
    _ = ∏ i, geometric (a i) := by rw [hH, mul_one]

/-- Newton's recurrence for evaluated complete homogeneous symmetric polynomials. -/
theorem hsymm_newton {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℝ) (d : ℕ) :
    ((d + 1 : ℕ) : ℝ) * MvPolynomial.eval a (MvPolynomial.hsymm ι ℝ (d + 1)) =
      ∑ k ∈ range (d + 1), (∑ i, a i ^ (k + 1)) *
        MvPolynomial.eval a (MvPolynomial.hsymm ι ℝ (d - k)) := by
  let H : PowerSeries ℝ := mk fun d => MvPolynomial.eval a (MvPolynomial.hsymm ι ℝ d)
  have hD : derivative H = (∑ i, C (a i) * geometric (a i)) * H := by
    rw [show H = ∏ i, geometric (a i) from hsymm_series_eq_geometric a,
      derivative_prod_geometric, mul_comm]
  have he := congrArg (coeff d) hD
  rw [coeff_derivative, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at he
  simp only [H, coeff_mk, map_sum, coeff_C_mul, geometric] at he
  simpa only [pow_succ, mul_comm, Nat.cast_add, Nat.cast_one] using he

/-- The graph Newton recurrence, expressed entirely through natural closed walk counts. -/
theorem chs_newton {n : ℕ} (G : SimpleGraph (Fin n)) (d : ℕ) :
    ((d + 1 : ℕ) : ℝ) * chs G (d + 1) =
      ∑ k ∈ range (d + 1), (closedWalks G (k + 1) : ℝ) * chs G (d - k) := by
  simpa only [chs, sum_eigenvalues_pow_eq_closedWalks] using
    hsymm_newton (adjMatrix_isHermitian G).eigenvalues d

/-- All adjacency CHS coefficients, including odd degrees, are nonnegative. -/
theorem chs_nonneg {n : ℕ} (G : SimpleGraph (Fin n)) (d : ℕ) : 0 ≤ chs G d := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    cases d with
    | zero => simp [chs, MvPolynomial.hsymm_zero]
    | succ d =>
      apply nonneg_of_mul_nonneg_right (a := ((d + 1 : ℕ) : ℝ)) ?_
        (by positivity : (0 : ℝ) < ((d + 1 : ℕ) : ℝ))
      rw [chs_newton]
      exact sum_nonneg fun k hk => mul_nonneg (Nat.cast_nonneg _) (ih _ (by
        have := mem_range.mp hk
        omega))

/-- Domination of positive closed walk moments implies domination of every CHS coefficient. -/
theorem chs_le_of_closedWalks_le {n : ℕ} (F G : SimpleGraph (Fin n))
    (hwalk : ∀ k, 1 ≤ k → closedWalks F k ≤ closedWalks G k) (d : ℕ) :
    chs F d ≤ chs G d := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    cases d with
    | zero => simp [chs, MvPolynomial.hsymm_zero]
    | succ d =>
      apply (mul_le_mul_iff_right₀ (by positivity : (0 : ℝ) < ((d + 1 : ℕ) : ℝ))).mp
      rw [chs_newton, chs_newton]
      apply sum_le_sum
      intro k hk
      exact mul_le_mul (by exact_mod_cast hwalk (k + 1) (by omega))
        (ih _ (by have := mem_range.mp hk; omega))
        (chs_nonneg F _) (Nat.cast_nonneg _)

private theorem adjMatrix_pow_mono {n : ℕ} {F G : SimpleGraph (Fin n)}
    (hFG : F ≤ G) (k : ℕ) : ∀ i j, ((F.adjMatrix ℕ) ^ k) i j ≤ ((G.adjMatrix ℕ) ^ k) i j := by
  induction k with
  | zero => simp
  | succ k ih =>
    intro i j
    simp only [pow_succ, Matrix.mul_apply]
    apply sum_le_sum
    intro v _
    apply Nat.mul_le_mul (ih i v)
    simp only [SimpleGraph.adjMatrix_apply]
    split_ifs with hF hG hG
    · rfl
    · exact (hG (hFG hF)).elim
    · omega
    · rfl

/-- The complete graph maximizes every adjacency CHS coefficient. -/
theorem chs_le_top {n : ℕ} (G : SimpleGraph (Fin n)) (d : ℕ) :
    chs G d ≤ chs (⊤ : SimpleGraph (Fin n)) d := by
  apply chs_le_of_closedWalks_le G ⊤ _ d
  intro k _
  exact sum_le_sum fun v _ => adjMatrix_pow_mono le_top k v v

/-- The even coefficient needed for the root comparison is nonnegative. -/
theorem chs_two_mul_pos {n : ℕ} (G : SimpleGraph (Fin n)) (m : ℕ) :
    0 ≤ chs G (2 * m) := chs_nonneg G _

/-- The comparison sequence satisfies the even Newton convolution. -/
theorem bseq_convolution (n r m : ℕ) :
    (2 * m : ℝ) * bseq n r m =
      (n : ℝ) * ∑ j ∈ range m, (r : ℝ) ^ (j + 1) * bseq n r (m - 1 - j) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hs : (∑ j ∈ range (m + 1), (r : ℝ) ^ (j + 1) *
        bseq n r (m + 1 - 1 - j)) =
        (r : ℝ) * bseq n r m +
          (r : ℝ) * ∑ j ∈ range m, (r : ℝ) ^ (j + 1) * bseq n r (m - 1 - j) := by
      rw [sum_range_succ', add_comm]
      simp only [Nat.add_sub_cancel, Nat.sub_zero, zero_add, pow_one]
      rw [mul_sum]
      congr 1
      apply sum_congr rfl
      intro j _
      rw [show m - (j + 1) = m - 1 - j by omega, pow_succ]
      ring
    simp only [Nat.cast_add, Nat.cast_one]
    have hrec := bseq_recurrence n r (m + 1) (by omega)
    simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel] at hrec
    rw [hrec, hs]
    linear_combination (r : ℝ) * ih

/-- Even closed walk lower bounds give the comparison-sequence lower bound. -/
theorem chs_ge_bseq {n : ℕ} (G : SimpleGraph (Fin n)) (r : ℕ)
    (hwalk : ∀ j, 1 ≤ j → n * r ^ j ≤ closedWalks G (2 * j)) (m : ℕ) :
    bseq n r m ≤ chs G (2 * m) := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    cases m with
    | zero => simp [chs, MvPolynomial.hsymm_zero]
    | succ m =>
      apply (mul_le_mul_iff_right₀ (by positivity : (0 : ℝ) < 2 * ((m + 1 : ℕ) : ℝ))).mp
      rw [bseq_convolution]
      have he : 2 * (m + 1) = (2 * m + 1) + 1 := by omega
      have hN := chs_newton G (2 * m + 1)
      rw [← he, Nat.cast_mul, Nat.cast_ofNat] at hN
      rw [hN, mul_sum]
      apply sum_le_sum_of_injOn (fun j => 2 * j + 1)
      · intro i hi j hj hij
        dsimp only at hij
        omega
      · intro k hk
        obtain ⟨j, hj, rfl⟩ := mem_image.mp hk
        have := mem_range.mp hj
        exact mem_range.mpr (by omega)
      · intro j hj
        have hjm : j ≤ m := by have := mem_range.mp hj; omega
        have hw : (n : ℝ) * (r : ℝ) ^ (j + 1) ≤ (closedWalks G (2 * (j + 1)) : ℝ) := by
          exact_mod_cast hwalk (j + 1) (by omega)
        have hc := ih (m - j) (by omega)
        have hidx : 2 * m + 1 - (2 * j + 1) = 2 * (m - j) := by omega
        simp only [Nat.add_sub_cancel, hidx, show 2 * j + 1 + 1 = 2 * (j + 1) by omega]
        rw [← mul_assoc]
        exact mul_le_mul hw hc (bseq_nonneg n r _) (Nat.cast_nonneg _)
      · intro k hk hkn
        exact mul_nonneg (Nat.cast_nonneg _) (chs_nonneg G _)

end D5.S3.Combinatorics.Graph.RegularCHS.Newton
