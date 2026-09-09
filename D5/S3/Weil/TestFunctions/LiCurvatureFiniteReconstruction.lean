/- GID: D5/S3/Weil/TestFunctions/LiCurvatureFiniteReconstruction
   generality: I
   mirror-B: D5/B/S3/Weil/TestFunctions/LiCurvatureFiniteReconstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Algebra.BigOperators.Intervals, mathlib/module/Mathlib.Analysis.InnerProductSpace.Rayleigh]
   utility: none
   digest: Finite reconstruction of normalized Hermitian curvature sequences and their Toeplitz quadratic forms. -/

import D5.S3.Weil.TestFunctions.LiCurvatureCriterion
import D5.S3.Weil.Probability.CanonicalLiCurvatureZeroFree
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.InnerProductSpace.Rayleigh

/- The statements quantify over arbitrary sequences and every natural size.
   They provide symbolic identities and bounds, not certified finite instances. -/

noncomputable section

open scoped BigOperators ComplexConjugate ComplexOrder
open Matrix

namespace D5.S3.Weil.TestFunctions.LiCurvatureFiniteReconstruction

open LiCurvatureCriterion

private def weighted (r : Nat → Real) (n : Nat) : Real :=
  ∑ k ∈ Finset.Ico 1 n, ((n : Real) - k) * r k

private theorem weighted_step (r : Nat → Real) (n : Nat) (hn : 1 ≤ n) :
    weighted r (n + 1) = weighted r n + ∑ k ∈ Finset.Ico 1 (n + 1), r k := by
  unfold weighted
  rw [Finset.sum_Ico_succ_top hn, Finset.sum_Ico_succ_top hn]
  simp only [Nat.cast_add, Nat.cast_one]
  have hs : (∑ k ∈ Finset.Ico 1 n, ((n : Real) + 1 - k) * r k) =
      (∑ k ∈ Finset.Ico 1 n, ((n : Real) - k) * r k) +
        ∑ k ∈ Finset.Ico 1 n, r k := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hs]
  ring

private theorem weighted_second (r : Nat → Real) (n : Nat) (hn : 1 ≤ n) :
    weighted r (n + 1) - 2 * weighted r n + weighted r (n - 1) = r n := by
  by_cases h : n = 1
  · subst n
    norm_num [weighted]
  have hn' : 1 ≤ n - 1 := by omega
  have hprev := weighted_step r (n - 1) hn'
  rw [Nat.sub_add_cancel hn] at hprev
  rw [weighted_step r n hn, Finset.sum_Ico_succ_top hn]
  linarith

/-- The normalized second-difference recurrence reconstructs the full weighted finite sum. -/
theorem recurrence_eq_weighted_curvature_sum
    (u : Nat → Real) (L : Real) (c : Int → Complex)
    (h0 : u 0 = 0) (h1 : u 1 = L) (hL : 0 ≤ L)
    (hc0 : c 0 = 1) (hHerm : ∀ k : Int, c (-k) = star (c k))
    (hRec : ∀ n : Nat, 1 ≤ n →
      u (n + 1) - 2 * u n + u (n - 1) = 2 * L * (c (n : Int)).re) :
    ∀ n : Nat, u n = L * ((n : Real) +
      2 * ∑ k ∈ Finset.Ico 1 n, ((n : Real) - k) * (c (k : Int)).re) := by
  let v : Nat → Real := fun n => L * ((n : Real) + 2 * weighted (fun k => (c k).re) n)
  have hv : u = v := second_difference_recurrence_unique u v
    (fun n => 2 * L * (c n).re)
    (by simpa [v, weighted] using h0)
    (by simpa [v, weighted] using h1) hRec (by
      intro n hn
      have hw := weighted_second (fun k => (c k).re) n hn
      dsimp [v]
      rw [Nat.cast_add, Nat.cast_one, Nat.cast_sub hn, Nat.cast_one]
      nlinarith)
  intro n
  exact congrFun hv n

private theorem strict_triangle (f : Nat → Complex) (n : Nat) :
    (∑ j ∈ Finset.range n, ∑ k ∈ Finset.range j, f (j - k)) =
      ∑ k ∈ Finset.Ico 1 n, ((n : Complex) - k) * f k := by
  have href (j : Nat) : (∑ k ∈ Finset.range j, f (j - k)) =
      ∑ k ∈ Finset.Ico 1 (j + 1), f k := by
    simpa using Finset.sum_Ico_reflect f 0 (m := j) (n := j) (by omega)
  simp_rw [href]
  by_cases hn : n = 0
  · subst n
    simp
  rw [Finset.sum_range_eq_add_Ico _ (by omega : 0 < n)]
  simp only [Finset.Ico_self, Finset.sum_empty, zero_add]
  rw [← Finset.sum_Ico_Ico_comm 1 n (fun k _ => f k)]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
  rw [Nat.cast_sub (Finset.mem_Ico.mp hk).2.le]

/-- Signed diagonals of a finite Toeplitz quadratic form, without symmetry assumptions. -/
theorem toeplitz_ones_diagonal_count (c : Int → Complex) (n : Nat) :
    star (fun _ : Fin n => (1 : Complex)) ⬝ᵥ
      ((fun j k : Fin n => c ((j : Int) - (k : Int))) *ᵥ
        (fun _ : Fin n => (1 : Complex))) =
      (n : Complex) * c 0 + ∑ k ∈ Finset.Ico 1 n,
        ((n : Complex) - k) * (c (k : Int) + c (-(k : Int))) := by
  classical
  simp only [dotProduct, mulVec, Pi.star_apply, star_one, one_mul, mul_one]
  rw [Fin.sum_univ_eq_sum_range (fun j : Nat =>
    ∑ k : Fin n, c ((j : Int) - (k : Int)))]
  have hinner (j : Nat) : (∑ k : Fin n, c ((j : Int) - (k : Int))) =
      ∑ k ∈ Finset.range n, c ((j : Int) - k) :=
    Fin.sum_univ_eq_sum_range (fun k : Nat => c ((j : Int) - k)) n
  simp_rw [hinner]
  have hsplit (j : Nat) (hj : j ∈ Finset.range n) :
      (∑ k ∈ Finset.range n, c ((j : Int) - k)) =
      (∑ k ∈ Finset.range j, c ((j : Int) - k)) +
        ∑ k ∈ Finset.Ico j n, c ((j : Int) - k) :=
    (Finset.sum_range_add_sum_Ico _ (Finset.mem_range.mp hj).le).symm
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
  have hswap : (∑ j ∈ Finset.range n, ∑ k ∈ Finset.Ico j n,
      c ((j : Int) - k)) =
      ∑ k ∈ Finset.range n, ∑ j ∈ Finset.range (k + 1), c ((j : Int) - k) := by
    simpa using Finset.sum_Ico_Ico_comm 0 n (fun j k => c ((j : Int) - k))
  rw [hswap]
  simp_rw [Finset.sum_range_succ, sub_self]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [← add_assoc, ← Finset.sum_add_distrib]
  have htri : (∑ j ∈ Finset.range n,
      ((∑ k ∈ Finset.range j, c ((j : Int) - k)) +
        ∑ k ∈ Finset.range j, c ((k : Int) - j))) =
      ∑ j ∈ Finset.range n, ∑ k ∈ Finset.range j,
        (c ((j - k : Nat) : Int) + c (-((j - k : Nat) : Int))) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Nat.cast_sub (Finset.mem_range.mp hk).le]
    congr 2
    ring
  rw [htri, strict_triangle (fun k => c k + c (-(k : Int))) n]
  ring

private theorem size_transport (c : Int → Complex) (n : Nat) (hn : 1 ≤ n) :
    (fun j k : Fin n => c ((j : Int) - (k : Int))) =
      (toeplitzMatrix c (n - 1)).submatrix
        (finCongr (Nat.sub_add_cancel hn)).symm
        (finCongr (Nat.sub_add_cancel hn)).symm := by
  ext j k
  simp [toeplitzMatrix, Matrix.submatrix]

private theorem quadratic_transport (c : Int → Complex) (n : Nat) (hn : 1 ≤ n) :
    star (fun _ : Fin n => (1 : Complex)) ⬝ᵥ
      ((fun j k : Fin n => c ((j : Int) - (k : Int))) *ᵥ (fun _ => 1)) =
    star (fun _ : Fin (n - 1 + 1) => (1 : Complex)) ⬝ᵥ
      (toeplitzMatrix c (n - 1) *ᵥ (fun _ => 1)) := by
  rw [size_transport c n hn, Matrix.submatrix_mulVec_equiv]
  simpa only [Function.comp_def, Pi.star_def, star_one] using
    dotProduct_comp_equiv_symm (fun _ : Fin n => (1 : Complex))
      (toeplitzMatrix c (n - 1) *ᵥ (fun _ => 1)) (finCongr (Nat.sub_add_cancel hn))

/-- The reconstructed coefficient equals the quadratic form at the size-n ones vector. -/
theorem recurrence_eq_toeplitz_ones_quadratic
    (u : Nat → Real) (L : Real) (c : Int → Complex)
    (h0 : u 0 = 0) (h1 : u 1 = L) (hL : 0 ≤ L)
    (hc0 : c 0 = 1) (hHerm : ∀ k : Int, c (-k) = star (c k))
    (hRec : ∀ n : Nat, 1 ≤ n →
      u (n + 1) - 2 * u n + u (n - 1) = 2 * L * (c (n : Int)).re)
    (n : Nat) (hn : 1 ≤ n) :
    u n = L * (star (fun _ : Fin n => (1 : Complex)) ⬝ᵥ
      ((fun j k : Fin n => c ((j : Int) - (k : Int))) *ᵥ
        (fun _ : Fin n => (1 : Complex)))).re := by
  have hcount := toeplitz_ones_diagonal_count c n
  rw [quadratic_transport c n hn] at hcount ⊢
  rw [hcount]
  rw [recurrence_eq_weighted_curvature_sum u L c h0 h1 hL hc0 hHerm hRec n]
  simp only [hc0, mul_one, Complex.add_re, Complex.natCast_re, Complex.re_sum,
    hHerm, Complex.add_re, Complex.star_def, Complex.conj_re, Complex.mul_re,
    Complex.sub_re, Complex.sub_im, Complex.natCast_im, sub_self, zero_mul, sub_zero]
  congr 1
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- Positivity of all finite Toeplitz matrices implies nonnegativity of the recurrence. -/
theorem recurrence_nonneg_of_toeplitz_posSemidef
    (u : Nat → Real) (L : Real) (c : Int → Complex)
    (h0 : u 0 = 0) (h1 : u 1 = L) (hL : 0 ≤ L)
    (hc0 : c 0 = 1) (hHerm : ∀ k : Int, c (-k) = star (c k))
    (hRec : ∀ n : Nat, 1 ≤ n →
      u (n + 1) - 2 * u n + u (n - 1) = 2 * L * (c (n : Int)).re)
    (hPSD : ∀ N : Nat, (toeplitzMatrix c N).PosSemidef) :
    ∀ n : Nat, 0 ≤ u n := by
  intro n
  by_cases hn : n = 0
  · simp [hn, h0]
  have hn' : 1 ≤ n := by omega
  rw [recurrence_eq_toeplitz_ones_quadratic u L c h0 h1 hL hc0 hHerm hRec n hn']
  apply mul_nonneg hL
  rw [size_transport c n hn']
  exact ((hPSD (n - 1)).submatrix _).re_dotProduct_nonneg _

private theorem hermitian (c : Int → Complex)
    (hHerm : ∀ k : Int, c (-k) = star (c k)) (n : Nat) :
    Matrix.IsHermitian (fun j k : Fin n => c ((j : Int) - (k : Int))) := by
  apply Matrix.ext
  intro j k
  change star (c ((k : Int) - (j : Int))) = c ((j : Int) - (k : Int))
  rw [← hHerm]
  congr 1
  ring

/-- A negative recurrence value bounds the actual last descending eigenvalue. -/
theorem negative_recurrence_bounds_smallest_eigenvalue
    (u : Nat → Real) (L : Real) (c : Int → Complex)
    (h0 : u 0 = 0) (h1 : u 1 = L) (hL : 0 ≤ L)
    (hc0 : c 0 = 1) (hHerm : ∀ k : Int, c (-k) = star (c k))
    (hRec : ∀ n : Nat, 1 ≤ n →
      u (n + 1) - 2 * u n + u (n - 1) = 2 * L * (c (n : Int)).re)
    (n : Nat) (hn : 1 ≤ n) (hLpos : 0 < L) (hu : u n < 0) :
    ∃ hT : Matrix.IsHermitian (fun j k : Fin n => c ((j : Int) - (k : Int))),
      hT.eigenvalues₀ ⟨n - 1, by simpa using (Nat.sub_lt hn (by decide : 0 < 1))⟩ ≤
        u n / ((n : Real) * L) ∧ u n / ((n : Real) * L) < 0 := by
  let T : Matrix (Fin n) (Fin n) Complex := fun j k => c ((j : Int) - (k : Int))
  have hT : T.IsHermitian := hermitian c hHerm n
  let e : EuclideanSpace Complex (Fin n) := WithLp.toLp 2 (fun _ => 1)
  have henorm : ‖e‖ ^ 2 = (n : Real) := by simp [e, EuclideanSpace.norm_sq_eq]
  have hnpos : (0 : Real) < n := by exact_mod_cast hn
  have he : e ≠ 0 := by
    intro h
    rw [h, norm_zero, zero_pow (by decide)] at henorm
    linarith
  let : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hS := Matrix.isSymmetric_toEuclideanLin_iff.mpr hT
  let A := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := Complex) T
  let q : {x : EuclideanSpace Complex (Fin n) // x ≠ 0} → Real :=
    fun x => RCLike.re (inner Complex (T.toEuclideanLin x) x) / ‖(x : EuclideanSpace Complex (Fin n))‖ ^ 2
  obtain ⟨i, hi⟩ := hS.exists_eigenvalues_eq finrank_euclideanSpace
    hS.hasEigenvalue_iInf_of_finiteDimensional
  have hival : hT.eigenvalues₀ i = ⨅ x, q x := by
    exact_mod_cast hi
  have hbdd : BddBelow (Set.range q) := by
    refine ⟨-‖A‖, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact (abs_le.mp (A.rayleighQuotient_le_norm x)).1
  have hbound := ciInf_le hbdd (⟨e, he⟩ : {x : EuclideanSpace Complex (Fin n) // x ≠ 0})
  have hnum : (inner Complex (T.toEuclideanLin e) e).re =
      (star (fun _ : Fin n => (1 : Complex)) ⬝ᵥ
        (T *ᵥ (fun _ : Fin n => (1 : Complex)))).re := by
    calc
      _ = (inner Complex e (T.toEuclideanLin e)).re :=
        inner_re_symm (𝕜 := Complex) (T.toEuclideanLin e) e
      _ = _ := by
        change ((T *ᵥ (fun _ : Fin n => (1 : Complex))) ⬝ᵥ
          star (fun _ : Fin n => (1 : Complex))).re = _
        rw [dotProduct_comm]
  have hquot : q ⟨e, he⟩ = u n / ((n : Real) * L) := by
    dsimp [q]
    rw [henorm, hnum, recurrence_eq_toeplitz_ones_quadratic u L c h0 h1 hL hc0 hHerm hRec n hn]
    dsimp [T]
    field_simp [ne_of_gt hnpos, ne_of_gt hLpos]
  refine ⟨hT, ?_, div_neg_of_neg_of_pos hu (mul_pos hnpos hLpos)⟩
  calc
    hT.eigenvalues₀ _ ≤ hT.eigenvalues₀ i := hT.eigenvalues₀_antitone (by
      change i.val ≤ n - 1
      have := i.isLt
      simp only [Fintype.card_fin] at this
      omega)
    _ = ⨅ x, q x := hival
    _ ≤ q ⟨e, he⟩ := hbound
    _ = _ := hquot

private theorem triangular_total (n : Nat) :
    (n : Real) + 2 * ∑ k ∈ Finset.Ico 1 n, ((n : Real) - k) = (n : Real) ^ 2 := by
  by_cases hn : n = 0
  · subst n
    simp
  have hn' : 1 ≤ n := by omega
  have hg : (∑ k ∈ Finset.range n, (k : Real)) * 2 = (n : Real) * (n - 1) := by
    simpa only [Nat.cast_mul, Nat.cast_sum, Nat.cast_sub hn', Nat.cast_one,
      Nat.cast_ofNat] using congrArg (fun k : Nat => (k : Real))
        (Finset.sum_range_id_mul_two n)
  rw [Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul,
    Nat.cast_sub hn', Nat.cast_one, Finset.sum_Ico_eq_sub _ hn']
  simp only [Finset.sum_range_one, Nat.cast_zero, sub_zero]
  nlinarith

private theorem pair_norm_bound (c : Int → Complex) (hc0 : c 0 = 1)
    (hHerm : ∀ k : Int, c (-k) = star (c k))
    (hPair : ∀ (N : Nat) (p : Fin 2 → Fin (N + 1)), Function.Injective p →
      ((toeplitzMatrix c N).submatrix p p).PosSemidef)
    (k : Nat) (hk : 1 ≤ k) : ‖c (k : Int)‖ ≤ 1 := by
  let p : Fin 2 → Fin (k + 1) := fun i => if i = 0 then ⟨0, by omega⟩ else ⟨k, by omega⟩
  have hp : Function.Injective p := by
    intro a b hab
    apply Fin.ext
    have hv := congrArg Fin.val hab
    fin_cases a <;> fin_cases b <;> norm_num [p] at hv ⊢ <;> omega
  have hd := (hPair k p hp).det_nonneg
  have hr := (Complex.nonneg_iff.mp hd).1
  simp only [Matrix.det_fin_two, Matrix.submatrix_apply] at hr
  norm_num [p, toeplitzMatrix, hc0, hHerm, Complex.mul_re, Complex.star_def,
    Complex.normSq_apply, Complex.normSq_eq_norm_sq] at hr
  have hs : ‖c (k : Int)‖ ^ 2 = (c (k : Int)).re ^ 2 + (c (k : Int)).im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  nlinarith [norm_nonneg (c (k : Int))]

/-- Arbitrary-gap two-point positivity gives the exact absolute quadratic bound. -/
theorem two_point_posSemidef_abs_recurrence_bound
    (u : Nat → Real) (L : Real) (c : Int → Complex)
    (h0 : u 0 = 0) (h1 : u 1 = L) (hL : 0 ≤ L)
    (hc0 : c 0 = 1) (hHerm : ∀ k : Int, c (-k) = star (c k))
    (hRec : ∀ n : Nat, 1 ≤ n →
      u (n + 1) - 2 * u n + u (n - 1) = 2 * L * (c (n : Int)).re)
    (hPair : ∀ (N : Nat) (p : Fin 2 → Fin (N + 1)), Function.Injective p →
      ((toeplitzMatrix c N).submatrix p p).PosSemidef) :
    ∀ n : Nat,
      |u n| ≤ L * ((n : Real) + 2 * ∑ k ∈ Finset.Ico 1 n, ((n : Real) - k)) ∧
      L * ((n : Real) + 2 * ∑ k ∈ Finset.Ico 1 n, ((n : Real) - k)) = L * (n : Real) ^ 2 := by
  have hbound := Probability.CanonicalLiCurvatureZeroFree.quadratic_of_bounded_second_difference
    u L h0 (by rw [h1, abs_of_nonneg hL]) (by
      intro n hn
      rw [hRec n hn, abs_mul, abs_of_nonneg (mul_nonneg (by norm_num) hL)]
      have hr := (Complex.abs_re_le_norm (c (n : Int))).trans
        (pair_norm_bound c hc0 hHerm hPair n hn)
      nlinarith)
  intro n
  rw [triangular_total]
  exact ⟨hbound n, rfl⟩

#print axioms recurrence_eq_weighted_curvature_sum
#print axioms toeplitz_ones_diagonal_count
#print axioms recurrence_eq_toeplitz_ones_quadratic
#print axioms recurrence_nonneg_of_toeplitz_posSemidef
#print axioms negative_recurrence_bounds_smallest_eigenvalue
#print axioms two_point_posSemidef_abs_recurrence_bound

end D5.S3.Weil.TestFunctions.LiCurvatureFiniteReconstruction
