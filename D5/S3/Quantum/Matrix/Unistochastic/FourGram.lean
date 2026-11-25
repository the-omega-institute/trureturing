/- GID: D5/S3/Quantum/Matrix/Unistochastic/FourGram
   generality: I
   mirror-B: D5/B/S3/Quantum/Matrix/Unistochastic/FourGram
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact order-four unistochasticity by two planar Gram matrices. -/

import D5.S3.QuadraticForms.RankBoundedChordalPsdCompletion
import D5.S3.Quantum.Matrix.CirculantBraceletNonUnistochastic

/-!
# The order-four coupled planar Gram criterion

The phase completion antecedent is Haagerup's procedure in Rajchel, Gąsiorowski
and Życzkowski, arXiv:1804.10715v2, Appendix A, equations (7.1)–(7.5).
The Bloch step uses rank-one coordinates and an explicit rotation of the last
two rows of a unitary. The second Bloch coordinate uses the reflected convention
corresponding to the imaginary part of the upper-right entry.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped BigOperators InnerProductSpace Matrix
open Matrix
open D5.S3.Quantum.Matrix.CirculantBraceletNonUnistochastic (IsUnistochastic)
open D5.S3.QuadraticForms.RankBoundedChordalPsdCompletion
  (gram_factor_rank exists_linearIsometryEquiv_of_inner_eq)

namespace D5.S3.Quantum.Matrix.Unistochastic.FourGram

abbrev RealFour := Matrix (Fin 4) (Fin 4) ℝ
abbrev ComplexFour := Matrix (Fin 4) (Fin 4) ℂ

private abbrev ns := Complex.normSq

/-- The two diagonal profiles in the order of the two row pairs. -/
def q (B : RealFour) (i : Fin 4) : ℝ := B 0 i * B 1 i
def p (B : RealFour) (i : Fin 4) : ℝ := B 2 i * B 3 i

private def c (B : RealFour) (i : Fin 4) : ℝ := B 2 i + B 3 i
private def d (B : RealFour) (i : Fin 4) : ℝ := B 2 i - B 3 i

/-- The difference from the first phase Gram matrix to the second. -/
def coupling (B : RealFour) : RealFour :=
  Matrix.of (fun i j =>
    (B 0 i * B 0 j + B 1 i * B 1 j - B 2 i * B 2 j - B 3 i * B 3 j) / 2) +
    Matrix.diagonal (fun i => c B i - 1 / 2)

def CoupledPlanarGrams (B : RealFour) : Prop :=
  ∃ S : RealFour, S.PosSemidef ∧ S.rank ≤ 2 ∧
    (∀ i, (∑ j, S i j) = 0) ∧ (∀ i, S i i = q B i) ∧
    (S + coupling B).PosSemidef ∧ (S + coupling B).rank ≤ 2

private lemma column_balance {B : RealFour} (hB : B ∈ doublyStochastic ℝ (Fin 4))
    (i : Fin 4) : B 0 i + B 1 i + c B i = 1 := by
  have hi := (mem_doublyStochastic_iff_sum.mp hB).2.2 i
  simpa [Fin.sum_univ_four, c, add_assoc] using hi

@[simp] theorem coupling_diag {B : RealFour} (hB : B ∈ doublyStochastic ℝ (Fin 4))
    (i : Fin 4) : coupling B i i = p B i - q B i := by
  have hi := column_balance hB i
  simp only [coupling, Matrix.add_apply, Matrix.of_apply, Matrix.diagonal_apply_eq, p, q, c] at ⊢
  unfold c at hi
  linear_combination ((B 0 i + B 1 i - B 2 i - B 3 i + 1) / 2) * hi

private lemma coupling_offdiag (B : RealFour) {i j : Fin 4} (hij : i ≠ j) :
    coupling B i j =
      (B 0 i * B 0 j + B 1 i * B 1 j - B 2 i * B 2 j - B 3 i * B 3 j) / 2 := by
  simp [coupling, hij]

theorem coupling_row_sum {B : RealFour} (hB : B ∈ doublyStochastic ℝ (Fin 4))
    (i : Fin 4) : (∑ j, coupling B i j) = 0 := by
  have hrow := (mem_doublyStochastic_iff_sum.mp hB).2.1
  have hsum :
      (∑ j, coupling B i j) =
        (B 0 i * (∑ j, B 0 j) + B 1 i * (∑ j, B 1 j) -
          B 2 i * (∑ j, B 2 j) - B 3 i * (∑ j, B 3 j)) / 2 + (c B i - 1 / 2) := by
    fin_cases i <;> norm_num [coupling, Matrix.diagonal_apply, Fin.sum_univ_four] <;> ring
  rw [hsum]
  have hi := column_balance hB i
  simp only [hrow, mul_one]
  dsimp [c] at hi ⊢
  linarith

private def phaseGram (z : Fin 4 → ℂ) : RealFour :=
  Matrix.of fun i j => (z i * star (z j)).re

private lemma phaseGram_diag (z : Fin 4 → ℂ) (i : Fin 4) :
    phaseGram z i i = ns (z i) := by
  simp [phaseGram, Complex.normSq_apply, Complex.mul_re]

private lemma phaseGram_psd_rank (z : Fin 4 → ℂ) :
    (phaseGram z).PosSemidef ∧ (phaseGram z).rank ≤ 2 := by
  let X : Matrix (Fin 2) (Fin 4) ℝ := Matrix.of (fun k j => ![(z j).re, (z j).im] k)
  have hX : phaseGram z = Xᴴ * X := by
    ext i j
    simp [phaseGram, X, Matrix.mul_apply, Fin.sum_univ_two, Complex.mul_re]
  rw [hX, Matrix.rank_conjTranspose_mul_self]
  exact ⟨Matrix.posSemidef_conjTranspose_mul_self X, by simpa using X.rank_le_card_height⟩

private lemma phaseGram_row_sum (z : Fin 4 → ℂ) (hz : (∑ i, z i) = 0) (i : Fin 4) :
    (∑ j, phaseGram z i j) = 0 := by
  change (∑ j, (z i * star (z j)).re) = 0
  rw [← Complex.re_sum, ← Finset.mul_sum]
  change (z i * (∑ j, starRingEnd ℂ (z j))).re = 0
  rw [← map_sum]
  simp [hz]

private lemma sum_eq_zero_of_phaseGram {S : RealFour} {z : Fin 4 → ℂ}
    (hGram : phaseGram z = S) (hS : ∀ i, (∑ j, S i j) = 0) :
    (∑ i, z i) = 0 := by
  let total := ∑ i, z i
  have h : phaseGram (fun _ => total) 0 0 = 0 := by
    change ((∑ i, z i) * star (∑ j, z j)).re = 0
    rw [show star (∑ j, z j) = ∑ j, star (z j) from map_sum (starRingEnd ℂ) _ _]
    rw [Finset.sum_mul, Complex.re_sum]
    simp_rw [Finset.mul_sum, Complex.re_sum]
    change (∑ i, ∑ j, phaseGram z i j) = 0
    simp [hGram, hS]
  exact Complex.normSq_eq_zero.mp (by rwa [phaseGram_diag] at h)

private lemma realize_phaseGram {S : RealFour} (hS : S.PosSemidef) (hrank : S.rank ≤ 2)
    (hrows : ∀ i, (∑ j, S i j) = 0) :
    ∃ z : Fin 4 → ℂ, phaseGram z = S ∧ (∑ j, z j) = 0 := by
  obtain ⟨v, hv⟩ := gram_factor_rank (V := Fin 4) 2 S hS
    (by simpa only [Matrix.rank_eq_finrank_span_cols] using hrank)
  let z (i : Fin 4) : ℂ := ⟨v i 0, v i 1⟩
  have hZ : phaseGram z = S := by
    ext i j
    rw [← hv i j]
    simp [z, phaseGram, PiLp.inner_apply, Fin.sum_univ_two, Complex.mul_re]
    ring
  exact ⟨z, hZ, sum_eq_zero_of_phaseGram hZ hrows⟩

private def rowLink (U : ComplexFour) (r s j : Fin 4) : ℂ := U r j * star (U s j)

private def colPair (U : ComplexFour) (r s i j : Fin 4) : ℂ :=
  U r i * star (U r j) + U s i * star (U s j)

private lemma normSqMatrix_apply (U : ComplexFour) (i j : Fin 4) :
    RHLinalg.normSqMatrix U i j = ns (U i j) := Complex.sq_norm _

private lemma colPair_norm (U : ComplexFour) (r s i j : Fin 4) :
    ns (colPair U r s i j) =
      ns (U r i) * ns (U r j) + ns (U s i) * ns (U s j) +
        2 * phaseGram (rowLink U r s) i j := by
  simp [colPair, phaseGram, rowLink, Complex.normSq_apply, Complex.mul_re,
    Complex.mul_im]
  ring

private lemma colPair_add {U : ComplexFour} (hU : U ∈ Matrix.unitaryGroup (Fin 4) ℂ)
    (i j : Fin 4) : colPair U 0 1 i j + colPair U 2 3 i j = if i = j then 1 else 0 := by
  have h := congrArg (fun A : ComplexFour => A j i) (Unitary.star_mul_self_of_mem hU)
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply, Fin.sum_univ_four] at h
  unfold colPair
  by_cases hij : i = j
  · subst j
    rw [ite_eq_left rfl] at h ⊢
    linear_combination h
  · rw [ite_eq_right (Ne.symm hij)] at h
    rw [ite_eq_right hij]
    linear_combination h

private lemma colPair_diag (U : ComplexFour) (r s i : Fin 4) :
    colPair U r s i i = ((ns (U r i) + ns (U s i) : ℝ) : ℂ) := by
  rw [Complex.ofReal_add, Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_conj_mul_self]
  simp [colPair, mul_comm]

private lemma sum_rowLink_eq_zero {U : ComplexFour}
    (hU : U ∈ Matrix.unitaryGroup (Fin 4) ℂ) {r s : Fin 4} (hrs : r ≠ s) :
    (∑ j, rowLink U r s j) = 0 := by
  have h := congrArg (fun A : ComplexFour => A r s) (Unitary.mul_star_self_of_mem hU)
  simpa [rowLink, Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply, hrs] using h

theorem coupledPlanarGrams_of_unitary {U : ComplexFour}
    (hU : U ∈ Matrix.unitaryGroup (Fin 4) ℂ) :
    CoupledPlanarGrams (RHLinalg.normSqMatrix U) := by
  let S := phaseGram (rowLink U 0 1)
  let T := phaseGram (rowLink U 2 3)
  have hB := RHLinalg.normSqMatrix_mem_doublyStochastic_of_unitary hU
  have hT : T = S + coupling (RHLinalg.normSqMatrix U) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp only [S, T, Matrix.add_apply, coupling_diag hB, phaseGram_diag, rowLink,
        p, q, normSqMatrix_apply, Complex.normSq_mul, Complex.star_def, Complex.normSq_conj]
      ring
    · have h := colPair_add hU i j
      rw [ite_eq_right hij] at h
      have hn : ns (colPair U 2 3 i j) = ns (colPair U 0 1 i j) := by
        rw [eq_neg_of_add_eq_zero_right h, Complex.normSq_neg]
      rw [colPair_norm, colPair_norm] at hn
      change T i j = S i j + coupling (RHLinalg.normSqMatrix U) i j
      rw [coupling_offdiag _ hij]
      simp only [normSqMatrix_apply]
      change ns (U 2 i) * ns (U 2 j) + ns (U 3 i) * ns (U 3 j) + 2 * T i j =
        ns (U 0 i) * ns (U 0 j) + ns (U 1 i) * ns (U 1 j) + 2 * S i j at hn
      linarith only [hn]
  obtain ⟨hS, hSr⟩ := phaseGram_psd_rank (rowLink U 0 1)
  obtain ⟨hTpsd, hTr⟩ := phaseGram_psd_rank (rowLink U 2 3)
  have hsum := sum_rowLink_eq_zero hU (r := 0) (s := 1) (by decide)
  refine ⟨S, hS, hSr, phaseGram_row_sum _ hsum, ?_, ?_, ?_⟩
  · intro i
    simp [S, phaseGram_diag, rowLink, q, normSqMatrix_apply, map_mul, Complex.normSq_conj]
  · exact hT ▸ hTpsd
  · exact hT ▸ hTr

/-- Split a complex link with squared modulus `a * b` into two amplitudes.
The link vanishes when the first amplitude is zero. -/
private lemma amplitudes_of_link {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (z : ℂ)
    (hz : ns z = a * b) :
    ∃ u v : ℂ, ns u = a ∧ ns v = b ∧ u * star v = z := by
  let u : ℂ := (Real.sqrt a : ℝ)
  have hu : ns u = a := by
    simpa [u, Complex.normSq_ofReal] using Real.mul_self_sqrt ha
  by_cases ha0 : a = 0
  · have hzero : z = 0 := Complex.normSq_eq_zero.mp (by simp [hz, ha0])
    refine ⟨u, (Real.sqrt b : ℝ), hu, ?_, ?_⟩
    · simpa [Complex.normSq_ofReal] using Real.mul_self_sqrt hb
    · simp [u, ha0, hzero]
  · have hu0 : u ≠ 0 := fun h => ha0 (by simpa [h] using hu.symm)
    let v := star (z / u)
    refine ⟨u, v, ?_, ?_, ?_⟩
    · exact hu
    · simp only [v, Complex.star_def, Complex.normSq_conj, Complex.normSq_div, hz, hu]
      exact mul_div_cancel_left₀ b ha0
    · simp only [v, star_star]
      rw [mul_comm, div_mul_cancel₀ _ hu0]

private lemma exists_unitary_with_rows (u v : Fin 4 → ℂ)
    (hu : (∑ i, ns (u i)) = 1) (hv : (∑ i, ns (v i)) = 1)
    (huv : (∑ i, u i * star (v i)) = 0) :
    ∃ U : ComplexFour, U ∈ Matrix.unitaryGroup (Fin 4) ℂ ∧ U 0 = u ∧ U 1 = v := by
  let rows : Fin 4 → EuclideanSpace ℂ (Fin 4) :=
    ![WithLp.toLp 2 u, WithLp.toLp 2 v, 0, 0]
  have huu : (∑ i, star (u i) * u i) = 1 := by
    simp_rw [show ∀ w : ℂ, star w * w = (ns w : ℂ) from
      fun w => (Complex.normSq_eq_conj_mul_self (z := w)).symm]
    rw [← Complex.ofReal_sum, hu, Complex.ofReal_one]
  have hvv : (∑ i, star (v i) * v i) = 1 := by
    simp_rw [show ∀ w : ℂ, star w * w = (ns w : ℂ) from
      fun w => (Complex.normSq_eq_conj_mul_self (z := w)).symm]
    rw [← Complex.ofReal_sum, hv, Complex.ofReal_one]
  have hvu : (∑ i, star (u i) * v i) = 0 := by
    have h := congrArg (fun z : ℂ => starRingEnd ℂ z) huv
    change starRingEnd ℂ (∑ i, u i * star (v i)) = starRingEnd ℂ 0 at h
    rw [map_sum, map_zero] at h
    simpa only [starRingEnd_apply, star_mul, star_star, mul_comm] using h
  have hon : Orthonormal ℂ (({0, 1} : Set (Fin 4)).domRestrict rows) := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, hi⟩ ⟨j, hj⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi hj
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;>
      simp only [Set.domRestrict_apply, rows, Matrix.cons_val_zero, Matrix.cons_val_one,
        PiLp.inner_apply, RCLike.inner_apply', Subtype.mk.injEq, ite_true,
        ite_eq_right (show (0 : Fin 4) ≠ 1 by decide),
        ite_eq_right (show (1 : Fin 4) ≠ 0 by decide)]
    · exact huu
    · exact hvu
    · calc
        (∑ i, star (v i) * u i) = ∑ i, u i * star (v i) :=
          Finset.sum_congr rfl (fun i _ => mul_comm _ _)
        _ = 0 := huv
    · exact hvv
  obtain ⟨basis, hb⟩ := hon.exists_orthonormalBasis_extension_of_card_eq (by simp)
  let U : ComplexFour := Matrix.of (fun i j => basis i j)
  refine ⟨U, Matrix.mem_unitaryGroup_iff.mpr ?_, ?_, ?_⟩
  · ext i j
    change (U * Uᴴ) i j = (1 : ComplexFour) i j
    rw [← inner_matrix_row_row U U j i]
    change ⟪basis j, basis i⟫_ℂ = (1 : ComplexFour) i j
    rw [orthonormal_iff_ite.mp basis.orthonormal, Matrix.one_apply]
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij, Ne.symm hij]
  · funext i
    exact congrArg (fun w : EuclideanSpace ℂ (Fin 4) => w i) (hb 0 (by simp))
  · funext i
    exact congrArg (fun w : EuclideanSpace ℂ (Fin 4) => w i) (hb 1 (by simp))

private abbrev ThreeSpace := EuclideanSpace ℝ (Fin 3)

/-- Bloch coordinates of the outer product of the column `(x,y)`. -/
private def bloch (x y : ℂ) : ThreeSpace :=
  WithLp.toLp 2 ![2 * (x * star y).re, 2 * (x * star y).im, ns x - ns y]

private lemma bloch_inner (x y x' y' : ℂ) :
    ⟪bloch x y, bloch x' y'⟫_ℝ =
      2 * ns (x * star x' + y * star y') - (ns x + ns y) * (ns x' + ns y') := by
  simp [bloch, PiLp.inner_apply, Fin.sum_univ_three, Complex.normSq_apply,
    Complex.mul_re, Complex.mul_im]
  ring

private lemma bloch_readout (s t x y : ℂ) :
    2 * ns (star s * x + star t * y) =
      (ns s + ns t) * (ns x + ns y) + ⟪bloch s t, bloch x y⟫_ℝ := by
  simp [bloch, PiLp.inner_apply, Fin.sum_univ_three, Complex.normSq_apply,
    Complex.mul_re, Complex.mul_im]
  ring

private lemma exists_bloch_amplitudes (n : ThreeSpace) (hn : ‖n‖ = 1) :
    ∃ s t : ℂ, ns s + ns t = 1 ∧ bloch s t = n := by
  have hsquares : n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1 := by
    simpa [Fin.sum_univ_three, hn, add_assoc] using
      (EuclideanSpace.real_norm_sq_eq n).symm
  let a := (1 + n 2) / 2
  let b := (1 - n 2) / 2
  let z : ℂ := ⟨n 0 / 2, n 1 / 2⟩
  have hn2sq : n 2 ^ 2 ≤ 1 ^ 2 := by
    nlinarith only [hsquares, sq_nonneg (n 0), sq_nonneg (n 1)]
  have hn2 : |n 2| ≤ 1 := (sq_le_sq₀ (abs_nonneg _) zero_le_one).mp (by simpa using hn2sq)
  have ha : 0 ≤ a := by
    dsimp [a]
    linarith only [(abs_le.mp hn2).1]
  have hb : 0 ≤ b := by
    dsimp [b]
    linarith only [(abs_le.mp hn2).2]
  have hz : ns z = a * b := by
    simp only [z, a, b, Complex.normSq_mk]
    nlinarith only [hsquares]
  obtain ⟨s, t, hs, ht, hst⟩ := amplitudes_of_link ha hb z hz
  refine ⟨s, t, ?_, ?_⟩
  · rw [hs, ht]
    dsimp [a, b]
    ring
  · apply WithLp.ofLp_injective 2
    funext k
    fin_cases k
    · change 2 * (s * star t).re = n 0
      rw [hst]
      dsimp [z]
      ring
    · change 2 * (s * star t).im = n 1
      rw [hst]
      dsimp [z]
      ring
    · change ns s - ns t = n 2
      rw [hs, ht]
      dsimp [a, b]
      ring

/-- Align a Gram realization with an actual family of Bloch vectors. The added vector
is the third coordinate vector in the realization and becomes the readout axis. -/
private lemma exists_readout_axis (v : Fin 4 → ThreeSpace) (d : Fin 4 → ℝ)
    (T : RealFour) (hT : T.PosSemidef) (hrank : T.rank ≤ 2)
    (hG : ∀ i j, ⟪v i, v j⟫_ℝ = d i * d j + 4 * T i j) :
    ∃ n : ThreeSpace, ‖n‖ = 1 ∧ ∀ i, ⟪n, v i⟫_ℝ = d i := by
  obtain ⟨u, hu⟩ := gram_factor_rank (V := Fin 4) 2 T hT
    (by simpa only [Matrix.rank_eq_finrank_span_cols] using hrank)
  let axis : ThreeSpace := WithLp.toLp 2 ![0, 0, 1]
  let model (i : Fin 4) : ThreeSpace := WithLp.toLp 2 ![2 * u i 0, 2 * u i 1, d i]
  -- First align just the column vectors. The isometry extends over all of ℝ³.
  have heq (i j : Fin 4) :
      ⟪model i, model j⟫_ℝ = ⟪v i, v j⟫_ℝ := by
    rw [hG, ← hu i j]
    simp [model, PiLp.inner_apply, Fin.sum_univ_three, Fin.sum_univ_two]
    ring
  obtain ⟨O, hO⟩ := exists_linearIsometryEquiv_of_inner_eq (v := model) (w := v) heq
  refine ⟨O axis, ?_, ?_⟩
  · rw [O.norm_map]
    have hn : ‖axis‖ ^ 2 = 1 := by
      norm_num [axis, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
    exact (sq_eq_sq₀ (norm_nonneg axis) zero_le_one).mp (by simpa using hn)
  · intro i
    rw [← hO i, O.inner_map_map]
    simp [axis, model, PiLp.inner_apply, Fin.sum_univ_three]

private def rotateLastRows (s t : ℂ) : ComplexFour :=
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, star s, star t; 0, 0, -t, s]

private lemma rotateLastRows_mem_unitary (s t : ℂ) (hst : ns s + ns t = 1) :
    rotateLastRows s t ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
  have hn : starRingEnd ℂ s * s + starRingEnd ℂ t * t = 1 := by
    rw [← Complex.normSq_eq_conj_mul_self, ← Complex.normSq_eq_conj_mul_self,
      ← Complex.ofReal_add, hst, Complex.ofReal_one]
  apply Matrix.mem_unitaryGroup_iff.mpr
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [rotateLastRows, Matrix.mul_apply, Matrix.star_apply, Fin.sum_univ_four,
      Matrix.one_apply] <;> first | exact hn | simpa only [mul_comm, add_comm] using hn | ring

/-- The Gram witnesses produce an actual unitary with squared moduli `B`. -/
theorem exists_unitary_of_coupledPlanarGrams {B : RealFour}
    (hB : B ∈ doublyStochastic ℝ (Fin 4)) (hGram : CoupledPlanarGrams B) :
    ∃ U ∈ Matrix.unitaryGroup (Fin 4) ℂ, B = RHLinalg.normSqMatrix U := by
  obtain ⟨S, hS, hSr, hrows, hdiag, hT, hTr⟩ := hGram
  let T := S + coupling B
  obtain ⟨z, hz, hsum⟩ := realize_phaseGram hS hSr hrows
  have hnorm (i : Fin 4) : ns (z i) = B 0 i * B 1 i := by
    rw [← phaseGram_diag z i, hz, hdiag, q]
  obtain ⟨hnonneg, hrow, _⟩ := mem_doublyStochastic_iff_sum.mp hB
  choose u v hu hv huv using
    fun i => amplitudes_of_link (hnonneg 0 i) (hnonneg 1 i) (z i) (hnorm i)
  obtain ⟨U, hU, hU0, hU1⟩ := exists_unitary_with_rows u v
    (by simp only [hu]; exact hrow 0) (by simp only [hv]; exact hrow 1)
    (by simp only [huv]; exact hsum)
  have htop (i j : Fin 4) :
      ns (colPair U 0 1 i j) = B 0 i * B 0 j + B 1 i * B 1 j + 2 * S i j := by
    have hlink : rowLink U 0 1 = z := by
      funext k
      simpa only [rowLink, hU0, hU1] using huv k
    simp only [colPair_norm, hU0, hU1, hu, hv, hlink, hz]
  have hbottom_diag (i : Fin 4) : ns (U 2 i) + ns (U 3 i) = c B i := by
    have h := colPair_add hU i i
    rw [ite_eq_left rfl, colPair_diag, colPair_diag, hU0, hU1, hu, hv] at h
    have hreal := congrArg Complex.re h
    simp only [Complex.add_re, Complex.ofReal_re, Complex.one_re] at hreal
    linarith only [hreal, column_balance hB i]
  have hbottom (i j : Fin 4) :
      ns (colPair U 2 3 i j) = B 2 i * B 2 j + B 3 i * B 3 j + 2 * T i j := by
    by_cases hij : i = j
    · subst j
      rw [colPair_diag, hbottom_diag, Complex.normSq_ofReal]
      have hti : T i i = p B i := by
        simp only [T, Matrix.add_apply, hdiag, coupling_diag hB]
        ring
      rw [hti]
      simp only [c, p]
      ring
    · have h := colPair_add hU i j
      rw [ite_eq_right hij] at h
      rw [eq_neg_of_add_eq_zero_right h, Complex.normSq_neg, htop]
      simp only [T, Matrix.add_apply, coupling_offdiag _ hij]
      ring
  let vectors (i : Fin 4) := bloch (U 2 i) (U 3 i)
  have hG (i j : Fin 4) :
      ⟪vectors i, vectors j⟫_ℝ = d B i * d B j + 4 * T i j := by
    change ⟪bloch (U 2 i) (U 3 i), bloch (U 2 j) (U 3 j)⟫_ℝ = _
    rw [bloch_inner]
    change 2 * ns (colPair U 2 3 i j) -
      (ns (U 2 i) + ns (U 3 i)) * (ns (U 2 j) + ns (U 3 j)) = _
    rw [hbottom, hbottom_diag, hbottom_diag]
    simp only [c, d]
    ring
  obtain ⟨n, hn, haxis⟩ := exists_readout_axis vectors (d B) T hT hTr hG
  obtain ⟨s, t, hst, hb⟩ := exists_bloch_amplitudes n hn
  let V := rotateLastRows s t * U
  have hV : V ∈ Matrix.unitaryGroup (Fin 4) ℂ :=
    (Matrix.unitaryGroup (Fin 4) ℂ).mul_mem (rotateLastRows_mem_unitary s t hst) hU
  have hV0 (i : Fin 4) : V 0 i = u i := by
    simp [V, rotateLastRows, Matrix.vecMul, dotProduct, Fin.sum_univ_four, hU0]
  have hV1 (i : Fin 4) : V 1 i = v i := by
    simp [V, rotateLastRows, Matrix.vecMul, dotProduct, Fin.sum_univ_four, hU1]
  have hV2 (i : Fin 4) : V 2 i = star s * U 2 i + star t * U 3 i := by
    simp [V, rotateLastRows, Matrix.vecMul, dotProduct, Fin.sum_univ_four]
  have hread (i : Fin 4) : ns (V 2 i) = B 2 i := by
    rw [hV2]
    have h := bloch_readout s t (U 2 i) (U 3 i)
    rw [hst, one_mul, hb, hbottom_diag] at h
    change 2 * ns (star s * U 2 i + star t * U 3 i) =
      c B i + ⟪n, vectors i⟫_ℝ at h
    rw [haxis] at h
    change 2 * ns (star s * U 2 i + star t * U 3 i) =
      (B 2 i + B 3 i) + (B 2 i - B 3 i) at h
    linarith only [h]
  have hV3 (i : Fin 4) : ns (V 3 i) = B 3 i := by
    have h := column_balance (RHLinalg.normSqMatrix_mem_doublyStochastic_of_unitary hV) i
    simp only [c, normSqMatrix_apply, hV0, hV1, hu, hv, hread] at h
    have hB' := column_balance hB i
    dsimp [c] at hB'
    linarith only [h, hB']
  refine ⟨V, hV, ?_⟩
  ext r i
  rw [normSqMatrix_apply]
  fin_cases r
  · exact (hu i).symm.trans (congrArg ns (hV0 i)).symm
  · exact (hv i).symm.trans (congrArg ns (hV1 i)).symm
  · exact (hread i).symm
  · exact (hV3 i).symm

/-- Exact order-four unistochasticity criterion, including zero entries. -/
theorem unistochastic_iff_coupledPlanarGrams {B : RealFour}
    (hB : B ∈ doublyStochastic ℝ (Fin 4)) :
    IsUnistochastic B ↔
      CoupledPlanarGrams B := by
  constructor
  · rintro ⟨U, hU, rfl⟩
    exact coupledPlanarGrams_of_unitary hU
  · exact exists_unitary_of_coupledPlanarGrams hB

section CubicConic

private abbrev RealThree := Matrix (Fin 3) (Fin 3) ℝ

private def symmetricThree (a b c x y z : ℝ) : RealThree :=
  !![a, x, y; x, b, z; y, z, c]

private def determinantForm (a b c x y z : ℝ) : ℝ :=
  a * b * c + 2 * x * y * z - a * z ^ 2 - b * y ^ 2 - c * x ^ 2

private lemma det_symmetricThree (a b c x y z : ℝ) :
    (symmetricThree a b c x y z).det = determinantForm a b c x y z := by
  simp [Matrix.det_fin_three, symmetricThree, determinantForm]
  ring

private lemma quadratic_two_nonneg {a b x : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hx : x ^ 2 ≤ a * b) (u v : ℝ) :
    0 ≤ a * u ^ 2 + 2 * x * u * v + b * v ^ 2 := by
  rcases ha.eq_or_lt with ha0 | hap
  · have hz : x = 0 := (sq_nonpos_iff x).mp (by simpa [← ha0] using hx)
    simpa [← ha0, hz] using mul_nonneg hb (sq_nonneg v)
  · have identity :
        a * (a * u ^ 2 + 2 * x * u * v + b * v ^ 2) =
          (a * u + x * v) ^ 2 + (a * b - x ^ 2) * v ^ 2 := by ring
    have h := add_nonneg (sq_nonneg (a * u + x * v))
      (mul_nonneg (sub_nonneg.mpr hx) (sq_nonneg v))
    rw [← identity] at h
    exact nonneg_of_mul_nonneg_right h hap

private lemma hermitian_symmetricThree (a b c x y z : ℝ) :
    (symmetricThree a b c x y z).IsHermitian := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [symmetricThree, Matrix.conjTranspose_apply]

private lemma rank_le_two_of_det_zero {A : RealThree} (hA : A.IsHermitian)
    (hdet : A.det = 0) : A.rank ≤ 2 := by
  classical
  rw [hA.det_eq_prod_eigenvalues] at hdet
  obtain ⟨i, _, hi⟩ := Finset.prod_eq_zero_iff.mp hdet
  have hcard := Fintype.card_subtype_lt
    (p := fun j => hA.eigenvalues j ≠ 0) (x := i) (fun hn => hn (by simpa using hi))
  rw [Fintype.card_fin] at hcard
  rw [hA.rank_eq_card_non_zero_eigs]
  omega

private lemma minor_bound {A : RealThree} (hA : A.PosSemidef) (i j : Fin 3) :
    A i j ^ 2 ≤ A i i * A j j := by
  have h := (hA.submatrix (fun k : Fin 2 => ![i, j] k)).det_nonneg
  have hsymm : A j i = A i j := by
    simpa [Matrix.conjTranspose_apply] using congrArg (fun M : RealThree => M i j) hA.1.eq
  rw [Matrix.det_fin_two] at h
  change 0 ≤ A i i * A j j - A i j * A j i at h
  rw [hsymm] at h
  nlinarith only [h]

/-- The zero determinant and three two-by-two minors characterize PSD of rank
at most two once the diagonal is nonnegative. The leading pivot may vanish. -/
private lemma psd_rank_two_iff {a b c x y z : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    (symmetricThree a b c x y z).PosSemidef ∧ (symmetricThree a b c x y z).rank ≤ 2 ↔
    determinantForm a b c x y z = 0 ∧ x ^ 2 ≤ a * b ∧ y ^ 2 ≤ a * c ∧ z ^ 2 ≤ b * c := by
  constructor
  · rintro ⟨hpsd, hrank⟩
    have hdet : (symmetricThree a b c x y z).det = 0 := by
      by_contra hne
      have h := Matrix.rank_of_det_ne_zero hne
      rw [Fintype.card_fin] at h
      omega
    refine ⟨(det_symmetricThree a b c x y z).symm.trans hdet, ?_, ?_, ?_⟩
    · simpa [symmetricThree] using minor_bound hpsd 0 1
    · simpa [symmetricThree] using minor_bound hpsd 0 2
    · simpa [symmetricThree] using minor_bound hpsd 1 2
  · rintro ⟨hdet, hx, hy, hz⟩
    have hHerm := hermitian_symmetricThree a b c x y z
    refine ⟨Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hHerm fun u => ?_,
      rank_le_two_of_det_zero hHerm ((det_symmetricThree a b c x y z).trans hdet)⟩
    have expand :
        star u ⬝ᵥ (symmetricThree a b c x y z *ᵥ u) =
          a * u 0 ^ 2 + 2 * x * u 0 * u 1 + 2 * y * u 0 * u 2 +
            (b * u 1 ^ 2 + 2 * z * u 1 * u 2 + c * u 2 ^ 2) := by
      simp [Matrix.mulVec, dotProduct, symmetricThree, Fin.sum_univ_three]
      ring
    rw [expand]
    rcases ha.eq_or_lt with ha0 | hap
    · have hx0 : x = 0 := (sq_nonpos_iff x).mp (by simpa [← ha0] using hx)
      have hy0 : y = 0 := (sq_nonpos_iff y).mp (by simpa [← ha0] using hy)
      simpa [← ha0, hx0, hy0] using quadratic_two_nonneg hb hc hz (u 1) (u 2)
    · have hminor :
          (a * z - x * y) ^ 2 ≤ (a * b - x ^ 2) * (a * c - y ^ 2) := by
        have hidentity :
            (a * b - x ^ 2) * (a * c - y ^ 2) - (a * z - x * y) ^ 2 =
              a * determinantForm a b c x y z := by
          unfold determinantForm
          ring
        rw [← sub_nonneg, hidentity, hdet, mul_zero]
      have h := quadratic_two_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hy) hminor (u 1) (u 2)
      have identity :
          a * (a * u 0 ^ 2 + 2 * x * u 0 * u 1 + 2 * y * u 0 * u 2 +
            (b * u 1 ^ 2 + 2 * z * u 1 * u 2 + c * u 2 ^ 2)) =
          (a * u 0 + x * u 1 + y * u 2) ^ 2 +
            ((a * b - x ^ 2) * u 1 ^ 2 + 2 * (a * z - x * y) * u 1 * u 2 +
              (a * c - y ^ 2) * u 2 ^ 2) := by ring
      have htotal := add_nonneg (sq_nonneg (a * u 0 + x * u 1 + y * u 2)) h
      rw [← identity] at htotal
      exact nonneg_of_mul_nonneg_right htotal hap

/-- The third off-diagonal of the leading block is fixed by the last diagonal. -/
def thirdOffdiag (B : RealFour) (x y : ℝ) : ℝ :=
  (q B 3 - q B 0 - q B 1 - q B 2) / 2 - x - y

def cubic (B : RealFour) (x y : ℝ) : ℝ :=
  determinantForm (q B 0) (q B 1) (q B 2) x y (thirdOffdiag B x y)

private def shiftedDet (B : RealFour) (x y : ℝ) : ℝ :=
  determinantForm (p B 0) (p B 1) (p B 2)
    (x + coupling B 0 1) (y + coupling B 0 2) (thirdOffdiag B x y + coupling B 1 2)

/-- The quadratic obtained by cancelling the cubic monomial in the determinant difference. -/
def conic (B : RealFour) (x y : ℝ) : ℝ :=
  let z := thirdOffdiag B x y
  let A := coupling B 0 1
  let D := coupling B 0 2
  let E := coupling B 1 2
  p B 0 * p B 1 * p B 2 - q B 0 * q B 1 * q B 2 +
    2 * (A * y * z + D * x * z + E * x * y + A * D * z + A * E * y +
      D * E * x + A * D * E) -
    p B 0 * (z + E) ^ 2 - p B 1 * (y + D) ^ 2 - p B 2 * (x + A) ^ 2 +
    q B 0 * z ^ 2 + q B 1 * y ^ 2 + q B 2 * x ^ 2

private lemma conic_eq_shiftedDet_sub_cubic (B : RealFour) (x y : ℝ) :
    conic B x y = shiftedDet B x y - cubic B x y := by
  dsimp [conic, shiftedDet, cubic, determinantForm]
  ring

def CubicConicFeasible (B : RealFour) : Prop :=
  ∃ x y : ℝ,
    cubic B x y = 0 ∧ conic B x y = 0 ∧
    x ^ 2 ≤ q B 0 * q B 1 ∧ y ^ 2 ≤ q B 0 * q B 2 ∧
    thirdOffdiag B x y ^ 2 ≤ q B 1 * q B 2 ∧
    (x + coupling B 0 1) ^ 2 ≤ p B 0 * p B 1 ∧
    (y + coupling B 0 2) ^ 2 ≤ p B 0 * p B 2 ∧
    (thirdOffdiag B x y + coupling B 1 2) ^ 2 ≤ p B 1 * p B 2

private def leadingThree (S : RealFour) : RealThree := S.submatrix Fin.castSucc Fin.castSucc

private def sumZeroInclusion : Matrix (Fin 3) (Fin 4) ℝ :=
  !![1, 0, 0, -1; 0, 1, 0, -1; 0, 0, 1, -1]

private def liftThree (M : RealThree) : RealFour :=
  sumZeroInclusionᴴ * M * sumZeroInclusion

private lemma liftThree_psd_rank {M : RealThree} (hM : M.PosSemidef) (hr : M.rank ≤ 2) :
    (liftThree M).PosSemidef ∧ (liftThree M).rank ≤ 2 :=
  ⟨hM.conjTranspose_mul_mul_same _, (Matrix.rank_mul_le_left _ _).trans
    ((Matrix.rank_mul_le_right _ _).trans hr)⟩

private lemma liftThree_entry (M : RealThree) (i j : Fin 3) :
    liftThree M i.castSucc j.castSucc = M i j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [liftThree, sumZeroInclusion, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_three, Matrix.cons_val]

private lemma liftThree_row_sum (M : RealThree) (i : Fin 4) :
    (∑ j, liftThree M i j) = 0 := by
  fin_cases i <;>
    simp [liftThree, sumZeroInclusion, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_four] <;>
    ring

private lemma liftThree_last_diag (B : RealFour) (x y : ℝ) :
    liftThree (symmetricThree (q B 0) (q B 1) (q B 2) x y (thirdOffdiag B x y)) 3 3 =
      q B 3 := by
  simp [liftThree, sumZeroInclusion, symmetricThree, thirdOffdiag, Matrix.mul_apply,
    Fin.sum_univ_three]
  ring

private lemma real_hermitian_entry {S : RealFour} (hS : S.IsHermitian) (i j : Fin 4) :
    S j i = S i j := by
  simpa [Matrix.conjTranspose_apply] using congrArg (fun M : RealFour => M i j) hS.eq

private lemma leadingThree_eq {S : RealFour} (hS : S.IsHermitian) :
    leadingThree S = symmetricThree (S 0 0) (S 1 1) (S 2 2) (S 0 1) (S 0 2) (S 1 2) := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> first
  | rfl
  | exact real_hermitian_entry hS _ _

private lemma eq_of_leadingThree_eq {S T : RealFour}
    (hS : S.IsHermitian) (hT : T.IsHermitian)
    (hs : ∀ i, (∑ j, S i j) = 0) (ht : ∀ i, (∑ j, T i j) = 0)
    (h : leadingThree S = leadingThree T) : S = T := by
  have hentry (i j : Fin 3) : S i.castSucc j.castSucc = T i.castSucc j.castSucc :=
    congrArg (fun A : RealThree => A i j) h
  have hlast (i : Fin 3) : S i.castSucc 3 = T i.castSucc 3 := by
    have hsi := hs i.castSucc
    have hti := ht i.castSucc
    rw [Fin.sum_univ_four] at hsi hti
    change S i.castSucc 0 + S i.castSucc 1 + S i.castSucc 2 + S i.castSucc 3 = 0 at hsi
    change T i.castSucc 0 + T i.castSucc 1 + T i.castSucc 2 + T i.castSucc 3 = 0 at hti
    have h0 : S i.castSucc 0 = T i.castSucc 0 := hentry i 0
    have h1 : S i.castSucc 1 = T i.castSucc 1 := hentry i 1
    have h2 : S i.castSucc 2 = T i.castSucc 2 := hentry i 2
    linarith only [hsi, hti, h0, h1, h2]
  have hrow (j : Fin 3) : S 3 j.castSucc = T 3 j.castSucc :=
    (real_hermitian_entry hS _ _).trans ((hlast j).trans (real_hermitian_entry hT _ _).symm)
  have hlastlast : S 3 3 = T 3 3 := by
    have hsi := hs 3
    have hti := ht 3
    rw [Fin.sum_univ_four] at hsi hti
    have h0 : S 3 0 = T 3 0 := hrow 0
    have h1 : S 3 1 = T 3 1 := hrow 1
    have h2 : S 3 2 = T 3 2 := hrow 2
    linarith only [hsi, hti, h0, h1, h2]
  apply Matrix.ext
  intro i j
  refine Fin.lastCases ?_ (fun i => ?_) i
  · exact Fin.lastCases hlastlast hrow j
  · exact Fin.lastCases (hlast i) (hentry i) j

private lemma thirdOffdiag_of_gram {B S : RealFour} (hS : S.IsHermitian)
    (hrows : ∀ i, (∑ j, S i j) = 0) (hdiag : ∀ i, S i i = q B i) :
    S 1 2 = thirdOffdiag B (S 0 1) (S 0 2) := by
  have h0 := hrows 0
  have h1 := hrows 1
  have h2 := hrows 2
  have h3 := hrows 3
  simp only [Fin.sum_univ_four, hdiag] at h0 h1 h2 h3
  dsimp [thirdOffdiag]
  linarith only [h0, h1, h2, h3, real_hermitian_entry hS 0 1, real_hermitian_entry hS 0 2,
    real_hermitian_entry hS 0 3, real_hermitian_entry hS 1 2, real_hermitian_entry hS 1 3,
    real_hermitian_entry hS 2 3]

private lemma coupling_isHermitian (B : RealFour) : (coupling B).IsHermitian := by
  apply Matrix.ext
  intro i j
  by_cases hij : i = j
  · subst j
    simp [Matrix.conjTranspose_apply]
  · simp [Matrix.conjTranspose_apply, coupling_offdiag B hij,
      coupling_offdiag B (Ne.symm hij), mul_comm]

/-- The two leading determinant equations and six principal-minor inequalities
characterize feasibility of the coupled planar Grams. -/
theorem coupledPlanarGrams_iff_cubicConicFeasible {B : RealFour}
    (hB : B ∈ doublyStochastic ℝ (Fin 4)) :
    CoupledPlanarGrams B ↔ CubicConicFeasible B := by
  have hnn := (mem_doublyStochastic_iff_sum.mp hB).1
  have hq (i : Fin 4) : 0 ≤ q B i := mul_nonneg (hnn 0 i) (hnn 1 i)
  have hp (i : Fin 4) : 0 ≤ p B i := mul_nonneg (hnn 2 i) (hnn 3 i)
  constructor
  · rintro ⟨S, hS, hSr, hrows, hdiag, hT, hTr⟩
    let x := S 0 1
    let y := S 0 2
    have hz := thirdOffdiag_of_gram hS.1 hrows hdiag
    have hST (i : Fin 4) : (S + coupling B) i i = p B i := by
      simp only [Matrix.add_apply, hdiag, coupling_diag hB]
      ring
    have hS₃ : leadingThree S =
        symmetricThree (q B 0) (q B 1) (q B 2) x y (thirdOffdiag B x y) := by
      rw [leadingThree_eq hS.1, hdiag, hdiag, hdiag, hz]
    have hT₃ : leadingThree (S + coupling B) =
        symmetricThree (p B 0) (p B 1) (p B 2)
          (x + coupling B 0 1) (y + coupling B 0 2) (thirdOffdiag B x y + coupling B 1 2) := by
      rw [leadingThree_eq hT.1, hST, hST, hST]
      simp only [Matrix.add_apply, hz, x, y]
    have hs₃ := hS.submatrix Fin.castSucc
    have ht₃ := hT.submatrix Fin.castSucc
    change (leadingThree S).PosSemidef at hs₃
    change (leadingThree (S + coupling B)).PosSemidef at ht₃
    have hsr : (leadingThree S).rank ≤ 2 :=
      (Matrix.rank_submatrix_le S Fin.castSucc Fin.castSucc).trans hSr
    have htr : (leadingThree (S + coupling B)).rank ≤ 2 :=
      (Matrix.rank_submatrix_le _ Fin.castSucc Fin.castSucc).trans hTr
    rw [hS₃] at hs₃ hsr
    rw [hT₃] at ht₃ htr
    obtain ⟨hf, hxy, hxz, hyz⟩ :=
      (psd_rank_two_iff (hq 0) (hq 1) (hq 2)).mp ⟨hs₃, hsr⟩
    obtain ⟨hg, hxy', hxz', hyz'⟩ :=
      (psd_rank_two_iff (hp 0) (hp 1) (hp 2)).mp ⟨ht₃, htr⟩
    exact ⟨x, y, hf, (conic_eq_shiftedDet_sub_cubic B x y).trans
      (sub_eq_zero.mpr (hg.trans hf.symm)), hxy, hxz, hyz, hxy', hxz', hyz'⟩
  · rintro ⟨x, y, hf, hg, hxy, hxz, hyz, hxy', hxz', hyz'⟩
    rw [conic_eq_shiftedDet_sub_cubic] at hg
    have hg' : shiftedDet B x y = 0 := (sub_eq_zero.mp hg).trans hf
    let M := symmetricThree (q B 0) (q B 1) (q B 2) x y (thirdOffdiag B x y)
    let N := symmetricThree (p B 0) (p B 1) (p B 2)
      (x + coupling B 0 1) (y + coupling B 0 2) (thirdOffdiag B x y + coupling B 1 2)
    have hM : M.PosSemidef ∧ M.rank ≤ 2 :=
      (psd_rank_two_iff (hq 0) (hq 1) (hq 2)).mpr ⟨hf, hxy, hxz, hyz⟩
    have hN : N.PosSemidef ∧ N.rank ≤ 2 :=
      (psd_rank_two_iff (hp 0) (hp 1) (hp 2)).mpr ⟨hg', hxy', hxz', hyz'⟩
    let S := liftThree M
    let T := S + coupling B
    have hs := liftThree_psd_rank hM.1 hM.2
    have ht := liftThree_psd_rank hN.1 hN.2
    have hsdiag (i : Fin 4) : S i i = q B i := by
      fin_cases i
      · exact (liftThree_entry M 0 0).trans rfl
      · exact (liftThree_entry M 1 1).trans rfl
      · exact (liftThree_entry M 2 2).trans rfl
      · exact liftThree_last_diag B x y
    have htsym : T.IsHermitian := hs.1.1.add (coupling_isHermitian B)
    have htdiag (i : Fin 4) : T i i = p B i := by
      simp only [T, Matrix.add_apply, hsdiag, coupling_diag hB]
      ring
    have htlead : leadingThree T = leadingThree (liftThree N) := by
      have hNlead : leadingThree (liftThree N) = N :=
        Matrix.ext fun i j => liftThree_entry N i j
      rw [hNlead, leadingThree_eq htsym, htdiag, htdiag, htdiag]
      change symmetricThree (p B 0) (p B 1) (p B 2)
        (S 0 1 + coupling B 0 1) (S 0 2 + coupling B 0 2) (S 1 2 + coupling B 1 2) = N
      rw [show S 0 1 = x from liftThree_entry M 0 1,
        show S 0 2 = y from liftThree_entry M 0 2,
        show S 1 2 = thirdOffdiag B x y from liftThree_entry M 1 2]
    have htrows (i : Fin 4) : (∑ j, T i j) = 0 := by
      simp [T, S, Finset.sum_add_distrib, liftThree_row_sum M i, coupling_row_sum hB i]
    have htEq : T = liftThree N :=
      eq_of_leadingThree_eq htsym ht.1.1 htrows (liftThree_row_sum N) htlead
    refine ⟨S, hs.1, hs.2, liftThree_row_sum M, hsdiag, ?_, ?_⟩
    · change T.PosSemidef
      rw [htEq]
      exact ht.1
    · change T.rank ≤ 2
      rw [htEq]
      exact ht.2

theorem unistochastic_iff_cubicConicFeasible {B : RealFour}
    (hB : B ∈ doublyStochastic ℝ (Fin 4)) :
    IsUnistochastic B ↔
      CubicConicFeasible B :=
  (unistochastic_iff_coupledPlanarGrams hB).trans (coupledPlanarGrams_iff_cubicConicFeasible hB)

end CubicConic

end D5.S3.Quantum.Matrix.Unistochastic.FourGram
