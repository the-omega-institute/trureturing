import D5.S3.Geometry.Hyperideal.CFMPNativeHomeomorphTransient
import D5.S3.Geometry.Hyperideal.SixIndependentLengthRemainder
import Batteries.Tactic.OpenPrivate

/-! UNCOMPILED transient source-only incremental extension of forward.lean.
Zero canonical Lean retention. No compilation, kernel proof or benchmark result.
Original declaration signatures and public queries are preserved verbatim.
Cumulative-file comments refer to the supplied packet; inherited declarations
are supplied by imports here. Any original retention commentary is superseded
by this attempt's zero-retention constraint. -/

noncomputable section
open scoped BigOperators Matrix
open Set
open D5.S3.Geometry.HyperbolicUpperHalfSpace
open D5.S3.Geometry.Hyperideal.LengthGramBody
open D5.S3.Geometry.Hyperideal.LengthGramMetricSegments


/-! Bounded forward construction. UNCOMPILED SOURCE.
The inherited bytes above are unchanged, apart from one additional import
prepended to the file. No full-facet or differentiable realization is asserted. -/
namespace NativeCornerExtractionSource
open private B_apply
  from D5.S3.Geometry.Hyperideal.CFMPNativeCapMetricTransient

namespace NativeForward
set_option autoImplicit false
open D5.S3.Geometry.Hyperideal.FourCycleEnvelopes
open D5.S3.Geometry.Hyperideal.LengthGramPolytope

private theorem gram_diag (l : Fin 6 → ℝ) (i : Fin 4) :
    lengthGram l i i = 1 := by fin_cases i <;> rfl

/-- Bind the original six slots to the existing character-coordinate remainder.
The rational change of basis avoids any new choice of a Lorentz frame. -/
private theorem original_remainder (l : Fin 6 → ℝ) :
    (Real.cosh (l 0)^2 - 1) * (lengthGram l).det =
      (numerator (Real.cosh (l 0)) (Real.cosh (l 1)) (Real.cosh (l 2))
        (Real.cosh (l 3)) (Real.cosh (l 4)) (Real.cosh (l 5)))^2 -
      rad (Real.cosh (l 0)) (Real.cosh (l 1)) (Real.cosh (l 5)) *
      rad (Real.cosh (l 0)) (Real.cosh (l 2)) (Real.cosh (l 4)) := by
  let a := Real.cosh (l 0)
  let b := Real.cosh (l 1)
  let c := Real.cosh (l 2)
  let d := Real.cosh (l 3)
  let e := Real.cosh (l 4)
  let f := Real.cosh (l 5)
  let T : Matrix (Fin 4) (Fin 4) ℝ :=
    !![1/2,1/2,0,0; 0,0,1/2,1/2; 1/2,-1/2,0,0; 0,0,1/2,-1/2]
  let K := D5.S3.Geometry.Hyperideal.SixIndependentLengthRemainder.gram
    a d ((b+e)/2) ((c+f)/2) ((b-e)/2) ((c-f)/2)
  have hcong : T * lengthGram l * T.transpose = (1/2 : ℝ) • K := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [T, K, lengthGram, a, b, c, d, e, f,
        D5.S3.Geometry.Hyperideal.SixIndependentLengthRemainder.gram,
        Matrix.mul_apply, Fin.sum_univ_succ] <;> ring
  have hT : T.det = -(1/4 : ℝ) := by
    -- Reduce the castAdd indices left by succAbove in the concrete minors.
    rw [Matrix.det_succ_row_zero, Fin.sum_univ_four]
    norm_num [T, Matrix.det_fin_three, Matrix.submatrix_apply,
      Fin.succAbove, Fin.lt_def, Fin.succ, Fin.castSucc,
      Fin.castAdd, Fin.castLE, Fin.cast,
      Matrix.cons_val_two, Matrix.cons_val_three]
  have hdet : (lengthGram l).det = K.det := by
    have h := congrArg Matrix.det hcong
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
      Matrix.det_smul, hT] at h
    norm_num at h
    linarith only [h]
  rw [hdet]
  have hrem :=
    D5.S3.Geometry.Hyperideal.SixIndependentLengthRemainder.determinant_remainder_identity
      a d ((b+e)/2) ((c+f)/2) ((b-e)/2) ((c-f)/2)
  change K.det = _ at hrem
  rw [hrem]
  dsimp [D5.S3.Geometry.Hyperideal.SixIndependentLengthRemainder.L,
    D5.S3.Geometry.Hyperideal.SixIndependentLengthRemainder.M,
    D5.S3.Geometry.Hyperideal.SixIndependentLengthRemainder.Xi,
    a, b, c, d, e, f, numerator, rad]
  ring

/-- This is only the algebraic gate to the supplied radial-frame theorem. -/
private theorem radial_gate (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (hdet : (lengthGram l).det < 0) :
    -1 < cosine (Real.cosh (l 0)) (Real.cosh (l 1)) (Real.cosh (l 2))
      (Real.cosh (l 3)) (Real.cosh (l 4)) (Real.cosh (l 5)) ∧
    cosine (Real.cosh (l 0)) (Real.cosh (l 1)) (Real.cosh (l 2))
      (Real.cosh (l 3)) (Real.cosh (l 4)) (Real.cosh (l 5)) < 1 := by
  have hc (k : Fin 6) : 1 < Real.cosh (l k) :=
    Real.one_lt_cosh.mpr (ne_of_gt (hl k))
  let A := rad (Real.cosh (l 0)) (Real.cosh (l 1)) (Real.cosh (l 5))
  let E := rad (Real.cosh (l 0)) (Real.cosh (l 2)) (Real.cosh (l 4))
  let N := numerator (Real.cosh (l 0)) (Real.cosh (l 1)) (Real.cosh (l 2))
    (Real.cosh (l 3)) (Real.cosh (l 4)) (Real.cosh (l 5))
  have hA : 0 < A := by
    dsimp [A, rad]
    have hp : 0 < 2 * Real.cosh (l 0) * Real.cosh (l 1) * Real.cosh (l 5) :=
      mul_pos (mul_pos (mul_pos (by norm_num) (by linarith [hc 0]))
        (by linarith [hc 1])) (by linarith [hc 5])
    nlinarith [sq_nonneg (Real.cosh (l 0)-1), sq_nonneg (Real.cosh (l 1)),
      sq_nonneg (Real.cosh (l 5)), hc 0]
  have hE : 0 < E := by
    dsimp [E, rad]
    have hp : 0 < 2 * Real.cosh (l 0) * Real.cosh (l 2) * Real.cosh (l 4) :=
      mul_pos (mul_pos (mul_pos (by norm_num) (by linarith [hc 0]))
        (by linarith [hc 2])) (by linarith [hc 4])
    nlinarith [sq_nonneg (Real.cosh (l 0)-1), sq_nonneg (Real.cosh (l 2)),
      sq_nonneg (Real.cosh (l 4)), hc 0]
  have hs : 0 < Real.cosh (l 0)^2 - 1 := by nlinarith [hc 0]
  have hneg := mul_neg_of_pos_of_neg hs hdet
  rw [original_remainder] at hneg
  have hgap : N^2 < A*E := by change N^2 - A*E < 0 at hneg; linarith
  let s := Real.sqrt A * Real.sqrt E
  have hsp : 0 < s := mul_pos (Real.sqrt_pos.mpr hA) (Real.sqrt_pos.mpr hE)
  have hs2 : s^2 = A*E := by
    dsimp [s]; rw [mul_pow, Real.sq_sqrt hA.le, Real.sq_sqrt hE.le]
  have hlo : -s < N := by
    by_contra hn
    have hle : N ≤ -s := le_of_not_gt hn
    have hp := mul_nonneg (show 0 ≤ -s-N by linarith)
      (show 0 ≤ s-N by linarith)
    nlinarith only [hp, hgap, hs2]
  have hhi : N < s := by
    by_contra hn
    have hle : s ≤ N := le_of_not_gt hn
    have hp := mul_nonneg (show 0 ≤ N-s by linarith)
      (show 0 ≤ N+s by linarith)
    nlinarith only [hp, hgap, hs2]
  change -1 < N / Real.sqrt A / Real.sqrt E ∧
    N / Real.sqrt A / Real.sqrt E < 1
  rw [div_div]
  constructor
  · exact (lt_div_iff₀ hsp).mpr (by simpa only [neg_one_mul] using hlo)
  · exact (div_lt_iff₀ hsp).mpr (by simpa only [one_mul] using hhi)

/-- Diagonal cofactors are negative principal 3x3 determinants, so the
inverse diagonal is positive. No dual spacelikeness is a caller premise. -/
private theorem inverse_diagonal_positive (l : Fin 6 → ℝ)
    (hl : ∀ k, 0 < l k) (hdet : (lengthGram l).det < 0) :
    ∀ i, 0 < (lengthGram l)⁻¹ i i := by
  have hc (k : Fin 6) : 1 < Real.cosh (l k) :=
    Real.one_lt_cosh.mpr (ne_of_gt (hl k))
  have hminor (x y z : ℝ) (hx : 1 < x) (hy : 1 < y) (hz : 1 < z) :
      1 - x^2 - y^2 - z^2 - 2*x*y*z < 0 := by
    have hx0 : 0 < x := lt_trans zero_lt_one hx
    have hy0 : 0 < y := lt_trans zero_lt_one hy
    have hz0 : 0 < z := lt_trans zero_lt_one hz
    have hp : 0 < 2*x*y*z := by positivity
    nlinarith [sq_nonneg (x-1), sq_nonneg y, sq_nonneg z]
  have hcofactor (i : Fin 4) : (lengthGram l).adjugate i i < 0 := by
    rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
    fin_cases i <;>
      norm_num [lengthGram, Matrix.det_fin_three, Matrix.submatrix_apply,
        Fin.succAbove, Fin.lt_def, Fin.succ, Fin.castSucc,
        Fin.castAdd, Fin.castLE, Fin.cast,
        Matrix.cons_val_two, Matrix.cons_val_three]
    all_goals first
      | nlinarith only [hminor _ _ _ (hc 5) (hc 4) (hc 3)]
      | nlinarith only [hminor _ _ _ (hc 1) (hc 2) (hc 3)]
      | nlinarith only [hminor _ _ _ (hc 0) (hc 2) (hc 4)]
      | nlinarith only [hminor _ _ _ (hc 0) (hc 1) (hc 5)]
  intro i
  rw [Matrix.inv_def, Ring.inverse_eq_inv]
  change 0 < (lengthGram l).det⁻¹ * (lengthGram l).adjugate i i
  exact mul_pos_of_neg_of_neg (inv_lt_zero'.mpr hdet) (hcofactor i)

private theorem row_pair (M N : Matrix (Fin 4) (Fin 4) ℝ) (i j : Fin 4) :
    (M * J * N.transpose) i j = B (M i) (N j) := by
  simp [B_apply, J, Matrix.mul_apply, lorentz, Fin.sum_univ_succ] <;> ring

/-- The cap inverse, rather than a native support normal, defines the dual. -/
private theorem inverse_cap_dual (l : Fin 6 → ℝ)
    (C : Matrix (Fin 4) (Fin 4) ℝ) (hC : C.det ≠ 0)
    (hgram : ∀ i j, B (C i) (C j) = lengthGram l i j) :
    let D := C⁻¹.transpose * J
    (∀ i j, B (C i) (D j) = if i = j then 1 else 0) ∧
    (∀ i j, B (D i) (D j) = (lengthGram l)⁻¹ i j) ∧
    (∀ a i, B (D i) (a ᵥ* C) = a i) := by
  classical
  let D := C⁻¹.transpose * J
  have hunit : IsUnit C.det := isUnit_iff_ne_zero.mpr hC
  have hJJ : J * J = 1 := by
    change Matrix.diagonal ![(1 : ℝ), 1, 1, -1] *
      Matrix.diagonal ![(1 : ℝ), 1, 1, -1] = 1
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_eq_one]
    funext i
    fin_cases i <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three]
  have hJt : J.transpose = J := by simp [J]
  have hJi : J⁻¹ = J := Matrix.inv_eq_right_inv hJJ
  have hG : C * J * C.transpose = lengthGram l := by
    ext i j; rw [row_pair, hgram]
  have hCD : C * J * D.transpose = 1 := by
    dsimp [D]
    rw [Matrix.transpose_mul, Matrix.transpose_transpose, hJt]
    calc
      C * J * (J * C⁻¹) = C * (J * J) * C⁻¹ := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hJJ, Matrix.mul_one, Matrix.mul_nonsing_inv C hunit]
  have hDD : D * J * D.transpose = (lengthGram l)⁻¹ := by
    rw [← hG, Matrix.mul_inv_rev, Matrix.mul_inv_rev,
      ← Matrix.transpose_nonsing_inv, hJi]
    dsimp [D]
    rw [Matrix.transpose_mul, Matrix.transpose_transpose, hJt]
    calc
      C⁻¹.transpose * J * J * (J * C⁻¹) =
          C⁻¹.transpose * (J * J) * J * C⁻¹ := by simp only [Matrix.mul_assoc]
      _ = C⁻¹.transpose * (J * C⁻¹) := by rw [hJJ, Matrix.mul_one, Matrix.mul_assoc]
  have hpair (i j : Fin 4) : B (C i) (D j) = if i = j then 1 else 0 := by
    rw [← row_pair, hCD, Matrix.one_apply]
  refine ⟨hpair, ?_, ?_⟩
  · intro i j; rw [← row_pair, hDD]
  · intro a i
    have hexpand : B (D i) (a ᵥ* C) = ∑ j, a j * B (C j) (D i) := by
      simp [B_apply, lorentz, Matrix.vecMul, dotProduct, Fin.sum_univ_succ] <;> ring
    rw [hexpand]
    simp [hpair]

private theorem marked_lengths (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (d : NativeSupportCorners)
    (hgram : ∀ i j, B (d.cap i) (d.cap j) = lengthGram l i j) :
    actualLengths d = l := by
  have hG : lengthGram (actualLengths d) = lengthGram l := by
    rw [← actual_corner_cap_gram_entries d]
    funext i j
    exact hgram i j
  have hcosh (k : Fin 6) : Real.cosh (actualLengths d k) = Real.cosh (l k) := by
    have h01 := congrFun (congrFun hG 0) 1
    have h02 := congrFun (congrFun hG 0) 2
    have h03 := congrFun (congrFun hG 0) 3
    have h23 := congrFun (congrFun hG 2) 3
    have h13 := congrFun (congrFun hG 1) 3
    have h12 := congrFun (congrFun hG 1) 2
    fin_cases k <;> simp only [lengthGram, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three] at *
    all_goals first
      | exact neg_injective h01 | exact neg_injective h02 | exact neg_injective h03
      | exact neg_injective h23 | exact neg_injective h13 | exact neg_injective h12
  funext k
  exact Real.cosh_strictMonoOn.injOn (actualLengths_positive d k).le (hl k).le (hcosh k)

/-- Arbitrary original positive lengths and a negative determinant produce the
actual eight-halfspace, twelve-corner carrier. The displayed inverse and
radial formulas fix the normal orientation and the original endpoint labels. -/
theorem forward8halfspace_exists (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (hdet : (lengthGram l).det < 0) :
    ∃ d : NativeSupportCorners,
      (∀ i j, B (d.cap i) (d.cap j) = lengthGram l i j) ∧
      (∀ i, d.side i = (-1 / Real.sqrt ((lengthGram l)⁻¹ i i)) •
        ((Matrix.transpose ((Matrix.of d.cap)⁻¹) * J) i)) ∧
      (∀ i j, i ≠ j → lift (d.corner i j) =
        radial l (endpoint l i j) ᵥ* (d.cap : Matrix (Fin 4) (Fin 4) ℝ)) ∧
      actualLengths d = l := by
  classical
  obtain ⟨_, hb, _, hnegative, _, _, _, _, _, hsupply⟩ := shared_radial_body l hl
  obtain ⟨C, hgram0, hC, _, F, _, _, _, _, hcoords⟩ := hsupply (radial_gate l hl hdet)
  have hgram (i j : Fin 4) : B (C i) (C j) = lengthGram l i j := by
    rw [B_apply]; exact hgram0 i j
  have hFlift (v : cutBody l) : lift (F v) = radial l v.val ᵥ* C := by
    obtain ⟨y, hy, hu, ht, hc⟩ := hcoords v
    exact (lift_of_coordinates _ _ hu ht hc).trans hy
  let D := C⁻¹.transpose * J
  let s : Fin 4 → ℝ := fun i => Real.sqrt ((lengthGram l)⁻¹ i i)
  let N : Fin 4 → V := fun i => (-1 / s i) • D i
  have hdpos := inverse_diagonal_positive l hl hdet
  have hs (i : Fin 4) : 0 < s i := Real.sqrt_pos.mpr (hdpos i)
  have hs2 (i : Fin 4) : s i ^ 2 = (lengthGram l)⁻¹ i i := Real.sq_sqrt (hdpos i).le
  obtain ⟨hCD, hDD, hDa⟩ := inverse_cap_dual l C hC.ne' hgram
  have hN (i : Fin 4) : B (N i) (N i) = 1 := by
    change B ((-1 / s i) • D i) ((-1 / s i) • D i) = 1
    rw [LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, hDD, ← hs2]
    field_simp [(hs i).ne'] <;> ring
  have hNa (a : V) (i : Fin 4) : B (N i) (a ᵥ* C) = (-1 / s i) * a i := by
    change B ((-1 / s i) • D i) (a ᵥ* C) = _
    rw [LinearMap.BilinForm.smul_left, hDa]
  have hCa (a : V) (i : Fin 4) : B (C i) (a ᵥ* C) = ∑ j, lengthGram l i j * a j := by
    calc
      B (C i) (a ᵥ* C) = ∑ j, B (C i) (C j) * a j := by
        simp [B_apply, lorentz, Matrix.vecMul, dotProduct, Fin.sum_univ_succ] <;> ring
      _ = _ := by simp only [hgram]
  let P : Set HyperbolicThreeSpace := {p |
    (∀ i, B (C i) (lift p) ≤ 0) ∧ (∀ i, B (N i) (lift p) ≤ 0)}
  have hmem (v : cutBody l) : F v ∈ P := by
    constructor
    · intro i
      rw [hFlift, hCa]
      -- Keep the row visibly function-typed at simp's implicit transparency level.
      change (∑ j : Fin 4, Matrix.row (lengthGram l) i j *
        (v.val j / Real.sqrt (-gramQuadratic l v.val))) ≤ 0
      -- Move each product outside its division before factoring the sum.
      simp only [← mul_div_assoc, ← Finset.sum_div]
      exact div_nonpos_of_nonpos_of_nonneg (v.property.2 i) (Real.sqrt_nonneg _)
    · intro i
      rw [hFlift, hNa]
      exact mul_nonpos_of_nonpos_of_nonneg
        (div_nonpos_of_nonpos_of_nonneg (by norm_num) (hs i).le)
        (div_nonneg (v.property.1.1 i) (Real.sqrt_nonneg _))
  have he := (cut_body_polytope l hl).2.2.2
  let corner : Fin 4 → Fin 4 → HyperbolicThreeSpace := fun i j =>
    if hij : i ≠ j then F ⟨endpoint l i j, (he i j hij).1⟩ else F ⟨_, hb⟩
  have hcorner (i j : Fin 4) (hij : i ≠ j) :
      corner i j = F ⟨endpoint l i j, (he i j hij).1⟩ := by simp [corner, hij]
  have hcornerlift (i j : Fin 4) (hij : i ≠ j) :
      lift (corner i j) = radial l (endpoint l i j) ᵥ* C := by rw [hcorner i j hij, hFlift]
  have hcornermem (i j : Fin 4) (hij : i ≠ j) : corner i j ∈ P := by
    rw [hcorner i j hij]; exact hmem _
  have hcapzero (i j : Fin 4) (hij : i ≠ j) (r : Fin 4) :
      B (C r) (lift (corner i j)) = 0 ↔ r = i := by
    rw [hcornerlift i j hij, hCa]
    have hroot : 0 < Real.sqrt (-gramQuadratic l (endpoint l i j)) :=
      Real.sqrt_pos.mpr (neg_pos.mpr (hnegative _ (he i j hij).1))
    -- As above, expose the function type without unfolding the Gram entries.
    change (∑ k : Fin 4, Matrix.row (lengthGram l) r k *
      (endpoint l i j k / Real.sqrt (-gramQuadratic l (endpoint l i j)))) = 0 ↔ r = i
    simp only [← mul_div_assoc, ← Finset.sum_div, div_eq_zero_iff, hroot.ne', or_false]
    obtain ⟨_, _, _, _, hzero, hstrict⟩ := he i j hij
    constructor
    · intro hz
      by_contra hn
      exact (ne_of_lt (hstrict r hn)) hz
    · rintro rfl; exact hzero
  have hsidezero (i j : Fin 4) (hij : i ≠ j) (r : Fin 4) :
      B (N r) (lift (corner i j)) = 0 ↔ r ≠ i ∧ r ≠ j := by
    rw [hcornerlift i j hij, hNa]
    have hn : -1 / s r ≠ 0 := div_ne_zero (by norm_num) (hs r).ne'
    have hroot : Real.sqrt (-gramQuadratic l (endpoint l i j)) ≠ 0 :=
      (Real.sqrt_pos.mpr (neg_pos.mpr (hnegative _ (he i j hij).1))).ne'
    change (-1 / s r) * (endpoint l i j r /
      Real.sqrt (-gramQuadratic l (endpoint l i j))) = 0 ↔ r ≠ i ∧ r ≠ j
    simp only [mul_eq_zero, hn, false_or, div_eq_zero_iff, hroot, or_false]
    obtain ⟨_, hi, hj, hz, _, _⟩ := he i j hij
    constructor
    · intro hr
      constructor
      · intro h; subst r; exact hi.ne' hr
      · intro h; subst r; exact hj.ne' hr
    · rintro ⟨hri, hrj⟩; exact hz r hri hrj
  let d : NativeSupportCorners :=
    { P := P
      cap := C
      side := N
      corner := corner
      cap_unit := fun i => (hgram i i).trans (gram_diag l i)
      side_unit := hN
      body_halfspaces := rfl
      corner_mem := hcornermem
      cap_incidence := by
        intro i j hij r
        change (corner i j ∈ P ∧ B (C r) (lift (corner i j)) = 0) ↔ r = i
        simp only [hcornermem i j hij, true_and, hcapzero i j hij r]
      side_incidence := by
        intro i j hij r
        change (corner i j ∈ P ∧ B (N r) (lift (corner i j)) = 0) ↔ r ≠ i ∧ r ≠ j
        simp only [hcornermem i j hij, true_and, hsidezero i j hij r]
      orthogonal_incidence := by
        intro j i hji
        change B (C j) ((-1 / s i) • D i) = 0
        rw [LinearMap.BilinForm.smul_right, hCD, if_neg hji, mul_zero] }
  exact ⟨d, hgram, fun _ => rfl, hcornerlift, marked_lengths l hl d hgram⟩

/-- A noncomputable constructor with only the two original mathematical premises. -/
noncomputable def forward8halfspace (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (hdet : (lengthGram l).det < 0) : NativeSupportCorners :=
  Classical.choose (forward8halfspace_exists l hl hdet)

theorem forward8halfspace_spec (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (hdet : (lengthGram l).det < 0) :
    let d := forward8halfspace l hl hdet
    (∀ i j, B (d.cap i) (d.cap j) = lengthGram l i j) ∧
    (∀ i, d.side i = (-1 / Real.sqrt ((lengthGram l)⁻¹ i i)) •
      ((Matrix.transpose ((Matrix.of d.cap)⁻¹) * J) i)) ∧
    (∀ i j, i ≠ j → lift (d.corner i j) =
      radial l (endpoint l i j) ᵥ* (d.cap : Matrix (Fin 4) (Fin 4) ℝ)) ∧
    actualLengths d = l :=
  Classical.choose_spec (forward8halfspace_exists l hl hdet)


/-- Algebraic inversion of the inherited oriented-cap formulas. This binds
our radial endpoint to the conventional unit-speed two-cap expression. -/
private theorem endpoint_cap_formula (l : Fin 6 → ℝ) (d : NativeSupportCorners)
    (hgram : ∀ i j, B (d.cap i) (d.cap j) = lengthGram l i j)
    (i j : Fin 4) (hij : i ≠ j) :
    lift (d.corner i j) =
      (-lengthGram l i j / Real.sqrt ((lengthGram l i j)^2 - 1)) • d.cap i +
      (1 / Real.sqrt ((lengthGram l i j)^2 - 1)) • d.cap j := by
  let X := lift (d.corner i j)
  let Y := lift (d.corner j i)
  let c := Real.cosh (dist (d.corner i j) (d.corner j i))
  let s := Real.sqrt (c^2-1)
  obtain ⟨hc, hs, hi, hj⟩ := actual_corner_oriented_caps d i j hij
  change 1 < c at hc
  change 0 < s at hs
  change d.cap i = (c/s) • X - (1/s) • Y at hi
  change d.cap j = (c/s) • Y - (1/s) • X at hj
  have hg : lengthGram l i j = -c :=
    (hgram i j).symm.trans (actual_corner_cap_pair d i j hij)
  have hs2 : s^2 = c^2-1 := Real.sq_sqrt (by nlinarith only [hc])
  rw [hg]
  simp only [neg_neg, neg_sq]
  change X = (c/s) • d.cap i + (1/s) • d.cap j
  rw [hi, hj]
  funext k
  change X k = (c/s) * ((c/s) * X k - (1/s) * Y k) +
    (1/s) * ((c/s) * Y k - (1/s) * X k)
  have hx := congrArg (fun t : ℝ => t * X k) hs2
  field_simp [hs.ne'] <;> nlinarith only [hx]

/-- Explicit endpoint formula in the ORIGINAL six-length Gram matrix.
Together with the radial formula in `forward8halfspace_spec`, this identifies
both descriptions of the same actual H3 corner; diagonal labels are unused. -/
theorem forward8halfspace_endpoint_lift (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (hdet : (lengthGram l).det < 0) (i j : Fin 4) (hij : i ≠ j) :
    let d := forward8halfspace l hl hdet
    lift (d.corner i j) =
      (-lengthGram l i j / Real.sqrt ((lengthGram l i j)^2 - 1)) • d.cap i +
      (1 / Real.sqrt ((lengthGram l i j)^2 - 1)) • d.cap j :=
  endpoint_cap_formula l (forward8halfspace l hl hdet)
    (forward8halfspace_spec l hl hdet).1 i j hij

end NativeForward
end NativeCornerExtractionSource

#check NativeCornerExtractionSource.NativeForward.forward8halfspace_exists
#print axioms NativeCornerExtractionSource.NativeForward.forward8halfspace_exists
#check NativeCornerExtractionSource.NativeForward.forward8halfspace
#print axioms NativeCornerExtractionSource.NativeForward.forward8halfspace
#check NativeCornerExtractionSource.NativeForward.forward8halfspace_spec
#print axioms NativeCornerExtractionSource.NativeForward.forward8halfspace_spec
#check NativeCornerExtractionSource.NativeForward.forward8halfspace_endpoint_lift
#print axioms NativeCornerExtractionSource.NativeForward.forward8halfspace_endpoint_lift
