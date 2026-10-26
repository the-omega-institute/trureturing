/- GID: D5/S3/Combinatorics/Graph/KyFanGap/MandalMehatariDasSeidelMinimum
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/KyFanGap/MandalMehatariDasSeidelMinimum
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Chain graphs have minimum Seidel energy precisely in Gamma. -/
/- proof_shape: bind-only; helpers are retained only for consumers of the settling proof or shared spectral owners.
escape_witness: none; admission_basis: open-problem-resolution (#21681; Proved).
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/22032.
The literal binary-string and Seidel expressions define claim; the proof uses shared spectral owners. -/
import D5.S3.Observer.Hankel.BalancedHankelSchmidt
import D5.S3.Weil.ZetaLinear.RankTrace
import D5.S3.Weil.ZetaLinear.FullRankInertiaPullback
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
namespace D5.S3.Combinatorics.Graph.KyFanGap.MandalMehatariDasSeidelMinimum
open Matrix
open scoped MatrixOrder
noncomputable def energy {V : Type*} [Fintype V] [DecidableEq V] (M : Matrix V V ℝ) : ℝ := (M.charpoly.roots.map (fun x => |x|)).sum
namespace Spectral
variable {V : Type*} [Fintype V] [DecidableEq V]
theorem sum_abs_eq_trace_sqrt {X : Matrix V V ℝ} (hX : X.IsHermitian) : (∑ i, |hX.eigenvalues i|) = (CFC.sqrt (Xᵀ * X)).trace := by
  let U : Matrix V V ℝ := hX.eigenvectorUnitary; let d : V → ℝ := hX.eigenvalues; let S : Matrix V V ℝ := U * diagonal (fun i => |d i|) * Uᵀ; have huu : U * Uᵀ = 1 := (Matrix.mem_orthogonalGroup_iff V ℝ).mp hX.eigenvectorUnitary.2; have hut : Uᵀ * U = 1 := (Matrix.mem_orthogonalGroup_iff' V ℝ).mp hX.eigenvectorUnitary.2
  have hx : X = U * diagonal d * Uᵀ := by
    simpa [U, d, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using hX.spectral_theorem
  have hp : S.PosSemidef := by
    simpa [S, Matrix.conjTranspose_eq_transpose_of_trivial] using (Matrix.PosSemidef.diagonal (d := fun i => |d i|)
      (fun i => abs_nonneg (d i))).mul_mul_conjTranspose_same U
  have hsq : S * S = Xᵀ * X := by
    rw [hX.isSymm.eq]
    conv_rhs => rw [hx]
    have hd : diagonal (fun i => |d i|) * diagonal (fun i => |d i|) =
        diagonal d * diagonal d := by
      rw [diagonal_mul_diagonal, diagonal_mul_diagonal]; congr 1; funext i; nlinarith only [sq_abs (d i)]
    calc
      S * S = U * (diagonal (fun i => |d i|) * diagonal (fun i => |d i|)) * Uᵀ := by
        dsimp [S]; simp only [Matrix.mul_assoc, ← Matrix.mul_assoc Uᵀ U, hut, one_mul]
      _ = U * (diagonal d * diagonal d) * Uᵀ := by rw [hd]
      _ = (U * diagonal d * Uᵀ) * (U * diagonal d * Uᵀ) := by
        simp only [Matrix.mul_assoc, ← Matrix.mul_assoc Uᵀ U, hut, one_mul]
  rw [CFC.sqrt_unique hsq hp.nonneg]; dsimp [S]; rw [Matrix.trace_mul_cycle, hut, one_mul, Matrix.trace_diagonal]
end Spectral
theorem energy_eigenvalues {V : Type*} [Fintype V] [DecidableEq V] {X : Matrix V V ℝ} (hX : X.IsHermitian) : energy X = ∑ i, |hX.eigenvalues i| := by
  simp [energy, hX.roots_charpoly_eq_eigenvalues, Multiset.map_map, Function.comp_def]
namespace MMDVariational
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
private noncomputable def objective (d : ι → ℝ) (M X : Matrix ι ι ℝ) : ℝ := (diagonal d * (X + M * X⁻¹ * M)).trace / 2
private theorem trace_cross (D M A : Matrix ι ι ℝ) : (D * (M * A * M)).trace = (M * D * M * A).trace := by
  calc
    _ = (D * M * A * M).trace := by simp [mul_assoc]
    _ = (M * (D * M * A)).trace := Matrix.trace_mul_comm _ _
    _ = _ := by simp [mul_assoc]
private theorem trace_complete_square (d : ι → ℝ) (M X Y : Matrix ι ι ℝ) (hY : IsUnit Y) (heq : X * diagonal d * X = M * diagonal d * M) : 2 * objective d M Y - 2 * (diagonal d * X).trace = (diagonal d * (Y - X) * Y⁻¹ * (Y - X)).trace := by
  letI := hY.invertible
  have hs : (Y - X) * Y⁻¹ * (Y - X) = Y - X - X + X * Y⁻¹ * X := by
    calc
      _ = Y * Y⁻¹ * Y - Y * Y⁻¹ * X - X * Y⁻¹ * Y + X * Y⁻¹ * X := by noncomm_ring
      _ = _ := by simp [mul_assoc]
  have ht : (diagonal d * (M * Y⁻¹ * M)).trace =
      (diagonal d * (X * Y⁻¹ * X)).trace := by
    rw [trace_cross, ← heq, ← trace_cross]
  rw [show diagonal d * (Y - X) * Y⁻¹ * (Y - X) =
    diagonal d * ((Y - X) * Y⁻¹ * (Y - X)) by simp [mul_assoc], hs]
  simp only [mul_add, mul_sub, trace_add, trace_sub]; unfold objective; rw [mul_add, trace_add, ht]; ring
private theorem quadratic_diagonal (Y B : Matrix ι ι ℝ) (hB : B.IsSymm) (i : ι) : (B * Y * B) i i = (fun j => B i j) ⬝ᵥ (Y *ᵥ (fun j => B i j)) := by
  rw [Matrix.mul_assoc]; change (fun j => B i j) ⬝ᵥ (Y *ᵥ (fun j => B j i)) = _; congr 2; funext j; exact hB.apply i j
private theorem diagonal_trace_quadratic_nonneg (d : ι → ℝ) (Y B : Matrix ι ι ℝ) (hd : ∀ i, 0 ≤ d i) (hY : Y.PosSemidef) (hB : B.IsSymm) : 0 ≤ (diagonal d * B * Y * B).trace := by
  have hp : (B * Y * B).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, hB.eq] using
      hY.mul_mul_conjTranspose_same B
  simpa only [mul_assoc, RCLike.re_to_real] using
    (RHLinalg.trace_mul_nonneg_of_posSemidef (Matrix.PosSemidef.diagonal hd) hp)
private theorem diagonal_trace_quadratic_pos (d : ι → ℝ) (Y B : Matrix ι ι ℝ) (hd : ∀ i, 0 < d i) (hY : Y.PosDef) (hB : B.IsSymm) (hne : B ≠ 0) : 0 < (diagonal d * B * Y * B).trace := by
  have hrow : ∃ i, (fun j => B i j) ≠ 0 := by
    by_contra h
    push_neg at h
    apply hne; ext i j; exact congrFun (h i) j
  obtain ⟨i, hi⟩ := hrow
  have hp : (B * Y * B).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, hB.eq] using
      hY.posSemidef.mul_mul_conjTranspose_same B
  have hpi : 0 < (B * Y * B) i i := by
    rw [quadratic_diagonal Y B hB i]; simpa only [star_trivial] using hY.dotProduct_mulVec_pos hi
  rw [show diagonal d * B * Y * B = diagonal d * (B * Y * B) by simp [mul_assoc]]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.diagonal_mul]; exact Finset.sum_pos' (fun j _ => mul_nonneg (hd j).le hp.diag_nonneg)
    ⟨i, Finset.mem_univ i, mul_pos (hd i) hpi⟩
private theorem unique_minimizer (d : ι → ℝ) (M X : Matrix ι ι ℝ) (hd : ∀ i, 0 < d i) (hX : X.PosDef) (heq : X * diagonal d * X = M * diagonal d * M) : objective d M X = (diagonal d * X).trace ∧ ∀ Y : Matrix ι ι ℝ, Y.PosDef → (objective d M X ≤ objective d M Y ∧ (objective d M Y = objective d M X ↔ Y = X)) := by
  have hval : objective d M X = (diagonal d * X).trace := by
    have h := trace_complete_square d M X X hX.isUnit heq; simp only [sub_self, mul_zero, zero_mul, trace_zero] at h; linarith
  refine ⟨hval, fun Y hY => ?_⟩; have hB : (Y - X).IsSymm := hY.isHermitian.isSymm.sub hX.isHermitian.isSymm; have hg := trace_complete_square d M X Y hY.isUnit heq; have hn := diagonal_trace_quadratic_nonneg d Y⁻¹ (Y-X) (fun i => (hd i).le)
    hY.inv.posSemidef hB
  refine ⟨by linarith, ?_⟩; constructor
  · intro hh; by_contra hne; have hp := diagonal_trace_quadratic_pos d Y⁻¹ (Y-X) hd hY.inv hB
      (sub_ne_zero.mpr hne)
    linarith
  · intro hh; subst Y; rfl
private noncomputable def compressed (d : ι → ℝ) (M : Matrix ι ι ℝ) : Matrix ι ι ℝ := (diagonal (fun i => Real.sqrt ((d) i))) * M * (diagonal (fun i => Real.sqrt ((d) i)))
private noncomputable def value (d : ι → ℝ) (M : Matrix ι ι ℝ) : ℝ := (CFC.sqrt (compressed d M * compressed d M)).trace
end MMDVariational
namespace MMDSymmetry
open Matrix MMDVariational
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
private theorem compressed_hermitian (d : ι → ℝ) (M : Matrix ι ι ℝ) (hM : M.IsHermitian) : (compressed d M).IsHermitian := by
  have hQ : ((diagonal (fun i => Real.sqrt ((d) i)))).IsHermitian := Matrix.isHermitian_diagonal (fun i => Real.sqrt (d i)); simpa only [compressed, hQ.eq] using Matrix.isHermitian_conjTranspose_mul_mul ((diagonal (fun i => Real.sqrt ((d) i)))) hM
end MMDSymmetry
namespace MMDVariational
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
private theorem attained (d : ι → ℝ) (M : Matrix ι ι ℝ) (hd : ∀ i, 0 < d i) (hM : M.IsHermitian) (hMunit : IsUnit M) : ∃ X : Matrix ι ι ℝ, X.PosDef ∧ X * diagonal d * X = M * diagonal d * M ∧ (diagonal d * X).trace = value d M := by
  let Q := (diagonal (fun i => Real.sqrt ((d) i))); let R := compressed d M; let A := CFC.sqrt (R * R); have hQ : Q.PosDef := Matrix.PosDef.diagonal (fun i => Real.sqrt_pos.mpr (hd i)); letI := hQ.isUnit.invertible
  have hQQ : Q * Q = diagonal d := by
    simp only [Q, diagonal_mul_diagonal]; congr 1; funext i; simpa only [pow_two] using Real.sq_sqrt (hd i).le
  have hR : R.IsHermitian := MMDSymmetry.compressed_hermitian d M hM; have hRunit : IsUnit R := (hQ.isUnit.mul hMunit).mul hQ.isUnit
  have hRR : (R * R).PosSemidef := by
    simpa only [hR.eq] using Matrix.posSemidef_conjTranspose_mul_self R
  have hApsd : A.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (R*R)); have hA : A.PosDef := hApsd.posDef_iff_isUnit.mpr
    ((CFC.isUnit_sqrt_iff (R*R) hRR.nonneg).mpr (hRunit.mul hRunit))
  have hAA : A * A = R * R := CFC.sqrt_mul_sqrt_self (R*R) hRR.nonneg; let X := Q⁻¹ * A * Q⁻¹
  have hX : X.PosDef := by
    have hh := hA.mul_mul_conjTranspose_same (B := Q⁻¹)
      (Matrix.vecMul_injective_iff_isUnit.mpr hQ.inv.isUnit)
    simpa only [hQ.inv.isHermitian.eq] using hh
  refine ⟨X, hX, ?_, ?_⟩
  · calc
      X * diagonal d * X = Q⁻¹ * (A * A) * Q⁻¹ := by
        dsimp [X]; rw [← hQQ]; simp [mul_assoc]
      _ = Q⁻¹ * (R * R) * Q⁻¹ := by rw [hAA]
      _ = M * diagonal d * M := by
        dsimp [R, compressed]; change Q⁻¹ * (Q * M * Q * (Q * M * Q)) * Q⁻¹ = _; rw [← hQQ]; simp [mul_assoc]
  · change (diagonal d * X).trace = A.trace
    calc
      _ = (Q⁻¹ * (diagonal d * Q⁻¹ * A)).trace := by
        simpa only [X, mul_assoc] using Matrix.trace_mul_comm (diagonal d * Q⁻¹ * A) Q⁻¹
      _ = A.trace := by rw [← hQQ]; simp [mul_assoc]
private theorem variational_formula (d : ι → ℝ) (M : Matrix ι ι ℝ) (hd : ∀ i, 0 < d i) (hM : M.IsHermitian) (hMunit : IsUnit M) : ∃ X : Matrix ι ι ℝ, X.PosDef ∧ objective d M X = value d M ∧ (∀ Y : Matrix ι ι ℝ, Y.PosDef → value d M ≤ objective d M Y) ∧ (∀ Y : Matrix ι ι ℝ, Y.PosDef → (objective d M Y = value d M ↔ Y = X)) := by
  obtain ⟨X, hX, heq, hvalue⟩ := attained d M hd hM hMunit; have hh := unique_minimizer d M X hd hX heq; refine ⟨X, hX, hh.1.trans hvalue, ?_, ?_⟩
  · intro Y hY; simpa only [← hvalue, ← hh.1] using (hh.2 Y hY).1
  · intro Y hY; simpa only [← hvalue, ← hh.1] using (hh.2 Y hY).2
end MMDVariational
namespace MMDStrictness
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
private noncomputable def weight (a : ℝ) (i p : ι) : ℝ := if p = i then 1 + a else 1
private noncomputable def vertex (a : ℝ) (i : ι) : Matrix ι ι ℝ := diagonal (weight a i)
private theorem weight_pos {a : ℝ} (ha : 0 < a) (i p : ι) : 0 < weight a i p := by
  simp only [weight]; split_ifs <;> linarith
private theorem vertex_pos {a : ℝ} (ha : 0 < a) (i : ι) : (vertex a i).PosDef := by
  exact Matrix.PosDef.diagonal (weight_pos ha i)
private theorem congruence_commute_ratio (T A B : Matrix ι ι ℝ) (hT : IsUnit T) (hAunit : IsUnit A) (hA : T * A * Tᵀ = A) (hB : T * B * Tᵀ = B) : T * (B * A⁻¹) = (B * A⁻¹) * T := by
  letI := hAunit.invertible; apply (hAunit.mul ((Matrix.isUnit_transpose T).mpr hT)).mul_right_cancel
  calc
    T * (B * A⁻¹) * (A * Tᵀ) = T * B * Tᵀ := by simp [mul_assoc]
    _ = B := hB
    _ = (B * A⁻¹) * (T * A * Tᵀ) := by rw [hA]; simp [mul_assoc]
    _ = (B * A⁻¹) * T * (A * Tᵀ) := by simp [mul_assoc]
private theorem ratio_simple {a : ℝ} (ha : 0 < a) {i j p : ι} (hij : i ≠ j) (hpi : p ≠ i) : weight a j p / weight a i p ≠ weight a j i / weight a i i := by
  have ha1 : 1 + a ≠ 0 := by linarith
  by_cases hpj : p = j
  · subst p; simp only [weight, ite_true, ite_eq_right hij, ite_eq_right hij.symm]; intro h; field_simp at h; nlinarith [sq_pos_of_pos ha]
  · simp only [weight, ite_true, ite_eq_right hij, ite_eq_right hpi, ite_eq_right hpj]; intro h; field_simp at h; linarith
private theorem commutant_simple_row_col (T : Matrix ι ι ℝ) (r : ι → ℝ) (i : ι) (hc : T * diagonal r = diagonal r * T) (hr : ∀ p, p ≠ i → r p ≠ r i) : (∀ p, p ≠ i → T p i = 0) ∧ (∀ p, p ≠ i → T i p = 0) := by
  constructor
  · intro p hpi; have h := congrArg (fun Q : Matrix ι ι ℝ => Q p i) hc; simp only [mul_diagonal, diagonal_mul] at h
    have hz : T p i * (r p - r i) = 0 := by nlinarith [h]
    exact (mul_eq_zero.mp hz).resolve_right (sub_ne_zero.mpr (hr p hpi))
  · intro p hpi; have h := congrArg (fun Q : Matrix ι ι ℝ => Q i p) hc; simp only [mul_diagonal, diagonal_mul] at h
    have hz : T i p * (r p - r i) = 0 := by nlinarith [h]
    exact (mul_eq_zero.mp hz).resolve_right (sub_ne_zero.mpr (hr p hpi))
private theorem congruence_vertex_column {a : ℝ} (ha : 0 < a) (T : Matrix ι ι ℝ) (hT : IsUnit T) {i j : ι} (hij : i ≠ j) (hi : T * vertex a i * Tᵀ = vertex a i) (hj : T * vertex a j * Tᵀ = vertex a j) : (∀ p, p ≠ i → T p i = 0) ∧ T i i ^ 2 = 1 := by
  have hc := congruence_commute_ratio T (vertex a i) (vertex a j) hT
    (vertex_pos ha i).isUnit hi hj
  have hinv : (vertex a i)⁻¹ = diagonal (fun p => (weight a i p)⁻¹) := by
    apply Matrix.inv_eq_left_inv; ext p q; by_cases hpq : p = q
    · subst q; simp [vertex, diagonal_mul_diagonal, ne_of_gt (weight_pos ha i p)]
    · simp [vertex, diagonal_mul_diagonal, hpq]
  rw [hinv] at hc; have hc' : T * diagonal (fun p => weight a j p / weight a i p) =
      diagonal (fun p => weight a j p / weight a i p) * T := by
    simpa only [vertex, diagonal_mul_diagonal, div_eq_mul_inv] using hc
  have hz := commutant_simple_row_col T _ i hc' (fun p hp => ratio_simple ha hij hp); refine ⟨hz.1, ?_⟩; have he := congrArg (fun Q : Matrix ι ι ℝ => Q i i) hi
  have he' : T i i ^ 2 * weight a i i = weight a i i := by
    calc
      T i i ^ 2 * weight a i i = (T * vertex a i * Tᵀ) i i := by
        symm
        rw [Matrix.mul_apply]; simp only [vertex, mul_diagonal, transpose_apply]; rw [Finset.sum_eq_single i]
        · ring
        · intro b _ hbi; rw [hz.2 b hbi]; ring
        · simp
      _ = weight a i i := by simpa only [vertex, diagonal_apply_eq] using he
  exact (mul_right_cancel₀ (ne_of_gt (weight_pos ha i i))) (by simpa using he')
private theorem posDef_two_columns_impossible (X M : Matrix ι ι ℝ) (hX : X.PosDef) {i j : ι} (hij : i ≠ j) (hdiag : M i i = 1 ∧ M j j = 1) (hprod : M i j * M j i = 1) (hi : ∀ p, X p i = M p i) (hj : ∀ p, X p j = M p j) : False := by
  let e : Fin 2 → ι := ![i, j]
  have he : Function.Injective e := by
    exact Matrix.injective_pair_iff_ne.mpr hij
  have hd := (hX.submatrix he).det_pos; simp only [Matrix.det_fin_two, Matrix.submatrix_apply] at hd; change 0 < X i i * X j j - X i j * X j i at hd; rw [hi, hj, hj, hi, hdiag.1, hdiag.2, hprod] at hd; norm_num at hd
private theorem no_common_vertex_equations {a : ℝ} (ha : 0 < a) (M X : Matrix ι ι ℝ) (hM : M.IsSymm) (hMunit : IsUnit M) (hX : X.PosDef) (hdiag : ∀ p, M p p = 1) (hentry : ∀ p q, M p q ^ 2 = 1) {i j : ι} (hij : i ≠ j) (hi : X * vertex a i * X = M * vertex a i * M) (hj : X * vertex a j * X = M * vertex a j * M) : False := by
  let T : Matrix ι ι ℝ := M⁻¹ * X; letI := hMunit.invertible; have hT : IsUnit T := ((Matrix.isUnit_nonsing_inv_iff (A := M)).mpr hMunit).mul hX.isUnit
  have hXT : M * T = X := by exact mul_inv_cancel_left_of_invertible M X
  have hcong (p : ι) (hp : X * vertex a p * X = M * vertex a p * M) :
      T * vertex a p * Tᵀ = vertex a p := by
    have hMi : M⁻¹ᵀ = M⁻¹ := by rw [Matrix.transpose_nonsing_inv, hM.eq]
    dsimp [T]; rw [Matrix.transpose_mul, hX.isHermitian.isSymm.eq, hMi]
    calc
      M⁻¹ * X * vertex a p * (X * M⁻¹) = M⁻¹ * (X * vertex a p * X) * M⁻¹ := by simp [mul_assoc]
      _ = M⁻¹ * (M * vertex a p * M) * M⁻¹ := by rw [hp]
      _ = vertex a p := by simp [← mul_assoc]
  have hci := congruence_vertex_column ha T hT hij (hcong i hi) (hcong j hj); have hcj := congruence_vertex_column ha T hT hij.symm (hcong j hj) (hcong i hi)
  have hcol (p : ι) (hc : (∀ q, q ≠ p → T q p = 0) ∧ T p p ^ 2 = 1) :
      ∀ q, X q p = M q p := by
    have hm (q : ι) : X q p = M q p * T p p := by
      rw [← hXT, Matrix.mul_apply, Finset.sum_eq_single p]
      · intro b _ hbp; rw [hc.1 b hbp, mul_zero]
      · simp
    have hpos : 0 < T p p := by
      have := hX.diag_pos (i := p); simpa only [hm p, hdiag p, one_mul] using this
    have hone : T p p = 1 := by nlinarith [hc.2]
    intro q; simpa only [hone, mul_one] using hm q
  apply posDef_two_columns_impossible X M hX hij ⟨hdiag i, hdiag j⟩ _
    (hcol i hci) (hcol j hcj)
  rw [hM.apply i j, ← pow_two]; exact hentry i j
end MMDStrictness
namespace MMDSimplex
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
private theorem weighted_minimum {w c : ι → ℝ} {m : ℝ} (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1) (hc : ∀ i, m ≤ c i) : m ≤ ∑ i, w i * c i := by
  calc
    m = ∑ i, w i * m := by rw [← Finset.sum_mul, hsum, one_mul]
    _ ≤ ∑ i, w i * c i := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hc i) (hw i))
private theorem positive_weight_attains {w c : ι → ℝ} {m : ℝ} (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1) (hc : ∀ i, m ≤ c i) (heq : ∑ i, w i * c i = m) {i : ι} (hi : 0 < w i) : c i = m := by
  have hz : ∑ j, w j * (c j - m) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum, one_mul, heq, sub_self]
  have hz' := (Finset.sum_eq_zero_iff_of_nonneg
    (fun j (_ : j ∈ (Finset.univ : Finset ι)) => mul_nonneg (hw j) (sub_nonneg.mpr (hc j)))).mp hz i (Finset.mem_univ i)
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz').resolve_left (ne_of_gt hi))
private theorem single_support_of_no_common_minimizer {w c : ι → ℝ} {m : ℝ} {i₀ : ι} (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1) (hc : ∀ i, m ≤ c i) (heq : ∑ i, w i * c i = m) (hbase : 0 < w i₀) (hsep : ∀ i j, i ≠ j → ¬ (c i = m ∧ c j = m)) : w i₀ = 1 ∧ ∀ i, i ≠ i₀ → w i = 0 := by
  have h₀ : c i₀ = m := positive_weight_attains hw hsum hc heq hbase
  have hzero (i : ι) (hi : i ≠ i₀) : w i = 0 := by
    by_contra hne; have hpos : 0 < w i := lt_of_le_of_ne (hw i) (Ne.symm hne); exact hsep i i₀ hi ⟨positive_weight_attains hw hsum hc heq hpos, h₀⟩
  refine ⟨?_, hzero⟩
  have hh : ∑ i, w i = w i₀ := by
    exact Fintype.sum_eq_single i₀ hzero
  linarith
end MMDSimplex
namespace MMDOptimization
open Matrix MMDVariational MMDStrictness
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
private theorem objective_eq_sum (d : ι → ℝ) (M X : Matrix ι ι ℝ) : objective d M X = ∑ p, d p * ((X + M * X⁻¹ * M) p p / 2) := by
  simp only [objective, Matrix.trace, Matrix.diag_apply, Matrix.diagonal_mul,
    Finset.sum_div, mul_div_assoc]
private theorem objective_mixture (w : ι → ℝ) (v : ι → ι → ℝ) (M X : Matrix ι ι ℝ) : objective (fun p => ∑ i, w i * v i p) M X = ∑ i, w i * objective (v i) M X := by
  simp only [objective_eq_sum, Finset.sum_mul, Finset.mul_sum, mul_assoc]; exact Finset.sum_comm
private theorem equation_of_attainment (d : ι → ℝ) (M X : Matrix ι ι ℝ) (hd : ∀ p, 0 < d p) (hM : M.IsHermitian) (hMu : IsUnit M) (hX : X.PosDef) (he : objective d M X = value d M) : X * diagonal d * X = M * diagonal d * M := by
  obtain ⟨Y, hY, heq, hv⟩ := attained d M hd hM hMu; have hu := unique_minimizer d M Y hd hY heq; have hXY : X = Y := (hu.2 X hX).2.mp (he.trans (hu.1.trans hv).symm); simpa only [hXY] using heq
private theorem vertex_simplex_minimum {a : ℝ} (ha : 0 < a) (M : Matrix ι ι ℝ) (hM : M.IsSymm) (hMu : IsUnit M) (hdiag : ∀ p, M p p = 1) (hentry : ∀ p q, M p q ^ 2 = 1) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1) (i₀ : ι) (hbase : 0 < w i₀) (hvertex : ∀ i, value (weight a i) M = value (weight a i₀) M) : value (weight a i₀) M ≤ value (fun p => ∑ i, w i * weight a i p) M ∧ (value (fun p => ∑ i, w i * weight a i p) M = value (weight a i₀) M ↔ w i₀ = 1 ∧ ∀ i, i ≠ i₀ → w i = 0) := by
  let d : ι → ℝ := fun p => ∑ i, w i * weight a i p
  have hd : ∀ p, 0 < d p := by
    intro p; apply Finset.sum_pos'
    · intro i _; exact mul_nonneg (hw i) (weight_pos ha i p).le
    · exact ⟨i₀, Finset.mem_univ i₀, mul_pos hbase (weight_pos ha i₀ p)⟩
  have hMh : M.IsHermitian := Matrix.isHermitian_iff_isSymm.mpr hM; obtain ⟨X, hX, hXv, hXmin, hXu⟩ := variational_formula d M hd hMh hMu
  have hvermin (i : ι) : value (weight a i₀) M ≤ objective (weight a i) M X := by
    obtain ⟨Y, hY, hYv, hYmin, _⟩ := variational_formula (weight a i) M
      (weight_pos ha i) hMh hMu
    rw [← hvertex i]; exact hYmin X hX
  have hmix : value d M = ∑ i, w i * objective (weight a i) M X := by
    rw [← hXv]; exact objective_mixture w (weight a) M X
  have hlow : value (weight a i₀) M ≤ value d M := by
    rw [hmix]; exact MMDSimplex.weighted_minimum hw hsum hvermin
  refine ⟨hlow, ?_⟩; constructor
  · intro heq; apply MMDSimplex.single_support_of_no_common_minimizer hw hsum hvermin
      (hmix.symm.trans heq) hbase
    intro i j hij hh
    have hi : X * vertex a i * X = M * vertex a i * M :=
      equation_of_attainment (weight a i) M X (weight_pos ha i) hMh hMu hX
        (hh.1.trans (hvertex i).symm)
    have hj : X * vertex a j * X = M * vertex a j * M :=
      equation_of_attainment (weight a j) M X (weight_pos ha j) hMh hMu hX
        (hh.2.trans (hvertex j).symm)
    exact no_common_vertex_equations ha M X hM hMu hX hdiag hentry hij hi hj
  · rintro ⟨hi₀, hz⟩
    have hd' : d = weight a i₀ := by
      funext p; change ∑ i, w i * weight a i p = weight a i₀ p; rw [Finset.sum_eq_single i₀]
      · rw [hi₀, one_mul]
      · intro i _ hi; rw [hz i hi, zero_mul]
      · simp
    change value d M = _; rw [hd']
end MMDOptimization
namespace MMDCore
private def entry (p q : ℕ) : ℝ := if (p < q ∧ p % 2 = 0 ∧ q % 2 = 1) ∨ (q < p ∧ q % 2 = 0 ∧ p % 2 = 1) then -1 else 1
private def core (d : ℕ) : Matrix (Fin d) (Fin d) ℝ := fun i j => entry i.val j.val
private theorem entry_diag (p : ℕ) : entry p p = 1 := by
  simp [entry]
private theorem entry_symm (p q : ℕ) : entry p q = entry q p := by
  simp only [entry, or_comm]
private theorem core_symm (d : ℕ) : (core d).IsSymm := by
  ext i j; exact entry_symm j.val i.val
private theorem entry_sq (p q : ℕ) : entry p q ^ 2 = 1 := by
  unfold entry
  split_ifs <;> norm_num
private theorem interior_difference (p j : ℕ) (hj : 1 ≤ j) : entry p (j - 1) - entry p (j + 1) = if p = j then (if j % 2 = 0 then 2 else -2) else 0 := by
  unfold entry
  split_ifs <;> norm_num at * <;> omega
private theorem first_difference {d p : ℕ} (hd : 3 ≤ d) (ho : d % 2 = 1) (hp : p < d) : entry p (d - 1) - entry p 1 = if p = 0 then 2 else 0 := by
  unfold entry
  split_ifs <;> norm_num at * <;> omega
private theorem last_sum {d p : ℕ} (hd : 3 ≤ d) (ho : d % 2 = 1) (hp : p < d) : entry p 0 + entry p (d - 2) = if p = d - 1 then 2 else 0 := by
  unfold entry
  split_ifs <;> norm_num at * <;> omega
private theorem rotation_value {d : ℕ} (hd : 3 ≤ d) (p : Fin d) : (finCycle (⟨2, by omega⟩ : Fin d) p).val = if p.val + 2 < d then p.val + 2 else p.val + 2 - d := by
  rw [finCycle_apply, Fin.val_add_eq_ite]
  split_ifs <;> simp_all only [Fin.val_mk] <;> omega
private def sign {d : ℕ} (p : Fin d) : ℝ := if p.val = d - 2 then -1 else 1
set_option maxHeartbeats 1000000 in
private theorem signed_rotation {d : ℕ} (hd : 3 ≤ d) (ho : d % 2 = 1) (i j : Fin d) : core d ((finCycle (⟨2, by omega⟩ : Fin d)) i) ((finCycle (⟨2, by omega⟩ : Fin d)) j) = sign i * sign j * core d i j := by
  simp only [core, entry, rotation_value hd, sign]
  split_ifs <;> norm_num at * <;> omega
private noncomputable def inverseCore {d : ℕ} (hd : 3 ≤ d) : Matrix (Fin d) (Fin d) ℝ := fun p j => if h0 : j.val = 0 then (Pi.single (M := fun _ : Fin d => ℝ) (⟨d - 1, by omega⟩ : Fin d) (1 / 2 : ℝ) - Pi.single (M := fun _ : Fin d => ℝ) (⟨1, by omega⟩ : Fin d) (1 / 2 : ℝ)) p else if h1 : j.val = d - 1 then (Pi.single (M := fun _ : Fin d => ℝ) (⟨0, by omega⟩ : Fin d) (1 / 2 : ℝ) + Pi.single (M := fun _ : Fin d => ℝ) (⟨d - 2, by omega⟩ : Fin d) (1 / 2 : ℝ)) p else (if j.val % 2 = 0 then (1 / 2 : ℝ) else -1 / 2) * (Pi.single (M := fun _ : Fin d => ℝ) (⟨j.val - 1, by omega⟩ : Fin d) (1 : ℝ) - Pi.single (M := fun _ : Fin d => ℝ) (⟨j.val + 1, by omega⟩ : Fin d) (1 : ℝ)) p
private theorem mul_inverse {d : ℕ} (hd : 3 ≤ d) (ho : d % 2 = 1) : core d * inverseCore hd = 1 := by
  ext i j; change (fun p : Fin d => entry i.val p.val) ⬝ᵥ (fun p : Fin d => inverseCore hd p j) = _; by_cases h0 : j.val = 0
  · have hcol : (fun p : Fin d => inverseCore hd p j) =
        Pi.single (M := fun _ : Fin d => ℝ) (⟨d - 1, by omega⟩ : Fin d) (1 / 2 : ℝ) -
          Pi.single (M := fun _ : Fin d => ℝ) (⟨1, by omega⟩ : Fin d) (1 / 2 : ℝ) := by
      funext p; simp [inverseCore, h0]
    rw [hcol, dotProduct_sub, dotProduct_single, dotProduct_single]; have hh := first_difference hd ho i.isLt; by_cases hij : i = j
    · subst i; simp only [h0, ite_true] at hh; simp only [Matrix.one_apply_eq, h0]; linarith
    · have hi : i.val ≠ 0 := by
        intro h; apply hij; apply Fin.ext; omega
      simp only [hi, ite_false] at hh; simp only [Matrix.one_apply_ne hij]; linarith
  · by_cases h1 : j.val = d - 1
    · have hcol : (fun p : Fin d => inverseCore hd p j) =
          Pi.single (M := fun _ : Fin d => ℝ) (⟨0, by omega⟩ : Fin d) (1 / 2 : ℝ) +
            Pi.single (M := fun _ : Fin d => ℝ) (⟨d - 2, by omega⟩ : Fin d) (1 / 2 : ℝ) := by
        funext p
        have hd0 : d - 1 ≠ 0 := by
          exact Ne.symm (ne_of_ne_of_eq (fun a => h0 (id (Eq.symm a))) h1)
        simp [inverseCore, h1, hd0]
      rw [hcol, dotProduct_add, dotProduct_single, dotProduct_single]; have hh := last_sum hd ho i.isLt; by_cases hij : i = j
      · subst i; simp only [h1, ite_true] at hh; simp only [Matrix.one_apply_eq, h1]; linarith
      · have hi : i.val ≠ d - 1 := by
          intro h; apply hij; apply Fin.ext; omega
        simp only [hi, ite_false] at hh; simp only [Matrix.one_apply_ne hij]; linarith
    · have hcol : (fun p : Fin d => inverseCore hd p j) =
          (if j.val % 2 = 0 then (1 / 2 : ℝ) else -1 / 2) •
            (Pi.single (M := fun _ : Fin d => ℝ) (⟨j.val - 1, by omega⟩ : Fin d) (1 : ℝ) -
              Pi.single (M := fun _ : Fin d => ℝ) (⟨j.val + 1, by omega⟩ : Fin d) (1 : ℝ)) := by
        funext p; simp [inverseCore, h0, h1]
      rw [hcol, dotProduct_smul, dotProduct_sub, dotProduct_single, dotProduct_single]; simp only [mul_one]; rw [interior_difference i.val j.val (by omega)]; by_cases hij : i = j
      · subst i; simp only [ite_true, Matrix.one_apply_eq]
        split_ifs <;> norm_num
      · have hv : i.val ≠ j.val := Fin.val_injective.ne hij; simp [hv, Matrix.one_apply_ne hij]
private theorem inverse_eq {d : ℕ} (hd : 3 ≤ d) (ho : d % 2 = 1) : (core d)⁻¹ = inverseCore hd :=
  Matrix.inv_eq_right_inv (mul_inverse hd ho)
end MMDCore
namespace MMDSymmetry
open Matrix MMDVariational
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
private theorem trace_submatrix_equiv (A : Matrix ι ι ℝ) (r : Equiv.Perm ι) : (A.submatrix r r).trace = A.trace := by
  exact Equiv.sum_comp r (fun i => A i i)
private theorem sqrt_submatrix_equiv (A : Matrix ι ι ℝ) (hA : A.PosSemidef) (r : Equiv.Perm ι) : CFC.sqrt (A.submatrix r r) = (CFC.sqrt A).submatrix r r := by
  have hp : ((CFC.sqrt A).submatrix r r).PosSemidef :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).submatrix r
  apply CFC.sqrt_unique _ hp.nonneg; rw [Matrix.submatrix_mul_equiv]; rw [CFC.sqrt_mul_sqrt_self A hA.nonneg]
private theorem value_reindex (d : ι → ℝ) (M : Matrix ι ι ℝ) (hM : M.IsHermitian) (r : Equiv.Perm ι) : value (d ∘ r) (M.submatrix r r) = value d M := by
  have hQ : (diagonal (fun i => Real.sqrt (((d ∘ r)) i))) = ((diagonal (fun i => Real.sqrt ((d) i)))).submatrix r r := by
    exact (Matrix.submatrix_diagonal_equiv (fun i => Real.sqrt (d i)) r).symm
  have hR : compressed (d ∘ r) (M.submatrix r r) = (compressed d M).submatrix r r := by
    simp only [compressed, hQ, Matrix.submatrix_mul_equiv]
  have hh := compressed_hermitian d M hM
  have hp : (compressed d M * compressed d M).PosSemidef := by
    simpa only [hh.eq] using Matrix.posSemidef_conjTranspose_mul_self (compressed d M)
  unfold value; rw [hR, Matrix.submatrix_mul_equiv, sqrt_submatrix_equiv _ hp r]; exact trace_submatrix_equiv _ r
private theorem trace_sqrt_square_conjugate (A U : Matrix ι ι ℝ) (hA : A.IsHermitian) (hUU : U * Uᵀ = 1) : (CFC.sqrt ((Uᵀ * A * U) * (Uᵀ * A * U))).trace = (CFC.sqrt (A*A)).trace := by
  have hp : (A*A).PosSemidef := by
    simpa only [hA.eq] using Matrix.posSemidef_conjTranspose_mul_self A
  have hB : (CFC.sqrt (A*A)).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (A*A))
  have hc : (Uᵀ * CFC.sqrt (A*A) * U).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, transpose_transpose] using
      hB.mul_mul_conjTranspose_same Uᵀ
  have he : (Uᵀ * CFC.sqrt (A*A) * U) * (Uᵀ * CFC.sqrt (A*A) * U) =
      (Uᵀ * A * U) * (Uᵀ * A * U) := by
    simp only [Matrix.mul_assoc, ← Matrix.mul_assoc U Uᵀ, hUU, one_mul]; rw [← Matrix.mul_assoc (CFC.sqrt (A*A)), CFC.sqrt_mul_sqrt_self (A*A) hp.nonneg]; simp only [Matrix.mul_assoc]
  rw [CFC.sqrt_unique he hc.nonneg, Matrix.trace_mul_cycle, hUU, one_mul]
private theorem value_sign (d s : ι → ℝ) (M : Matrix ι ι ℝ) (hM : M.IsHermitian) (hs : ∀ i, s i ^ 2 = 1) : value d (diagonal s * M * diagonal s) = value d M := by
  have hS : (diagonal s : Matrix ι ι ℝ)ᵀ = diagonal s := Matrix.diagonal_transpose _
  have hSS : (diagonal s : Matrix ι ι ℝ) * diagonal s = 1 := by
    rw [diagonal_mul_diagonal]
    have hh : (fun i => s i * s i) = fun _ => (1 : ℝ) := by
      funext i; simpa only [pow_two] using hs i
    rw [hh, diagonal_one]
  have hR : compressed d (diagonal s * M * diagonal s) =
      diagonal s * compressed d M * diagonal s := by
    ext i j; simp only [compressed, diagonal_mul, mul_diagonal]; ring
  unfold value; rw [hR]; simpa only [hS] using trace_sqrt_square_conjugate (compressed d M) (diagonal s)
    (compressed_hermitian d M hM) (by rwa [hS])
end MMDSymmetry
namespace MMDCoreMinimum
open Matrix MMDCore MMDVariational MMDStrictness MMDSymmetry MMDOptimization
private theorem core_unit {d : ℕ} (hd : 3 ≤ d) (ho : d % 2 = 1) : IsUnit (core d) := by
  exact isUnit_iff_exists_inv.mpr ⟨inverseCore hd, mul_inverse hd ho⟩
private theorem vertex_rotation {d : ℕ} (hd : 3 ≤ d) (ho : d % 2 = 1) (a : ℝ) (i : Fin d) : value (weight a ((finCycle (⟨2, by omega⟩ : Fin d)) i)) (core d) = value (weight a i) (core d) := by
  let r := (finCycle (⟨2, by omega⟩ : Fin d))
  have hr (p : Fin d) : r p = (finCycle (⟨2, by omega⟩ : Fin d)) p := rfl
  have hM : (core d).IsHermitian := Matrix.isHermitian_iff_isSymm.mpr (core_symm d)
  have hcomp : weight a ((finCycle (⟨2, by omega⟩ : Fin d)) i) ∘ r = weight a i := by
    funext p
    have he : r p = (finCycle (⟨2, by omega⟩ : Fin d)) i ↔ p = i := by
      change r p = r i ↔ p = i; exact r.injective.eq_iff
    simp only [Function.comp_apply, weight, he]
  have hsub : (core d).submatrix r r = diagonal sign * core d * diagonal sign := by
    ext p q; simp only [Matrix.submatrix_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, hr]; rw [signed_rotation hd ho]; ring
  have hh := value_reindex (weight a ((finCycle (⟨2, by omega⟩ : Fin d)) i)) (core d) hM r
  rw [hcomp, hsub, value_sign _ _ _ hM (fun p => by unfold sign; split_ifs <;> norm_num)] at hh
  exact hh.symm
open Equiv Equiv.Perm in
private theorem rotation_invariant_constant {d : ℕ} (hd : 3 ≤ d) (ho : d % 2 = 1) (f : Fin d → ℝ) (hf : ∀ i, f ((finCycle (⟨2, by omega⟩ : Fin d)) i) = f i) : ∀ i, f i = f ⟨0, by omega⟩ := by
  let : NeZero d := ⟨by omega⟩
  let r := finCycle (⟨2, by omega⟩ : Fin d)
  have he : r = (finRotate d)^2 := by
    apply Equiv.ext
    intro i
    change finCycle (⟨2, by omega⟩ : Fin d) i = ((finRotate d)^2) i
    rw [Equiv.Perm.coe_pow]
    exact congrFun finCycle_eq_finRotate_iterate i
  have hcy : r.IsCycle := by
    rw [he]
    apply (isCycle_finRotate_of_le (by omega : 2 ≤ d)).pow_iff.mpr
    rw [(isCycle_finRotate_of_le (by omega : 2 ≤ d)).orderOf,
      support_finRotate_of_le (by omega : 2 ≤ d), Finset.card_univ, Fintype.card_fin]
    exact Nat.coprime_two_left.mpr (Nat.odd_iff.mpr ho)
  have hn (i : Fin d) : r i ≠ i := by
    intro h
    have hz : (⟨2, by omega⟩ : Fin d) = 0 :=
      add_left_cancel (a := i) (by simpa [r, finCycle_apply] using h)
    have := congrArg Fin.val hz
    simp only [Fin.val_zero] at this
    omega
  intro i
  obtain ⟨n, hn⟩ := hcy.exists_pow_eq (hn i) (hn ⟨0,by omega⟩)
  have hinv : f ∘ (r : Fin d → Fin d) = f := funext hf
  have hit := congrFun (Function.iterate_invariant hinv n) i
  rw [← Equiv.Perm.coe_pow] at hit
  change f ((r ^ n) i) = f i at hit
  rw [hn] at hit
  exact hit.symm
private theorem equal_vertex_values {d : ℕ} (hd : 3 ≤ d) (ho : d % 2 = 1) (a : ℝ) (i : Fin d) : value (weight a i) (core d) = value (weight a ⟨0, by omega⟩) (core d) := by
  exact rotation_invariant_constant hd ho (fun i => value (weight a i) (core d))
    (vertex_rotation hd ho a) i
private theorem core_simplex_minimum {d : ℕ} (hd : 3 ≤ d) (ho : d % 2 = 1) {a : ℝ} (ha : 0 < a) (w : Fin d → ℝ) (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1) (hbase : 0 < w ⟨0, by omega⟩) : value (weight a ⟨0, by omega⟩) (core d) ≤ value (fun p => ∑ i, w i * weight a i p) (core d) ∧ (value (fun p => ∑ i, w i * weight a i p) (core d) = value (weight a ⟨0, by omega⟩) (core d) ↔ w ⟨0, by omega⟩ = 1 ∧ ∀ i, i ≠ ⟨0, by omega⟩ → w i = 0) := by
  exact vertex_simplex_minimum ha (core d) (core_symm d) (core_unit hd ho)
    (fun p => entry_diag p.val) (fun p q => entry_sq p.val q.val)
    w hw hsum ⟨0, by omega⟩ hbase (equal_vertex_values hd ho a)
open Matrix MMDCore MMDVariational MMDStrictness MMDOptimization
private theorem mixture_coordinates {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ℝ) (w : ι → ℝ) (hsum : ∑ i, w i = 1) (p : ι) : (∑ i, w i * weight a i p) = 1 + a * w p := by
  have ht (i : ι) : w i * weight a i p = w i + if i = p then a * w p else 0 := by
    by_cases hi : i = p
    · subst i; simp only [weight, ite_true]; ring
    · simp [weight, hi, Ne.symm hi]
  simp_rw [ht, Finset.sum_add_distrib]; simp [hsum]
private theorem core_diagonal_minimum {d : ℕ} (hd : 3 ≤ d) (ho : d % 2 = 1) (x : Fin d → ℝ) (hx : ∀ i, 1 ≤ x i) (hbase : 1 < x ⟨0, by omega⟩) : value (weight (∑ i, (x i - 1)) ⟨0, by omega⟩) (core d) ≤ value x (core d) ∧ (value x (core d) = value (weight (∑ i, (x i - 1)) ⟨0, by omega⟩) (core d) ↔ ∀ i, i ≠ ⟨0, by omega⟩ → x i = 1) := by
  let a : ℝ := ∑ i, (x i - 1); let w : Fin d → ℝ := fun i => (x i - 1) / a
  have ha : 0 < a := by
    exact Finset.sum_pos' (fun i _ => sub_nonneg.mpr (hx i))
      ⟨⟨0, by omega⟩, Finset.mem_univ _, sub_pos.mpr hbase⟩
  have hw : ∀ i, 0 ≤ w i := fun i => div_nonneg (sub_nonneg.mpr (hx i)) ha.le
  have hsum : ∑ i, w i = 1 := by
    dsimp only [w]; rw [← Finset.sum_div]; exact div_self (ne_of_gt ha)
  have hwb : 0 < w ⟨0, by omega⟩ := div_pos (sub_pos.mpr hbase) ha
  have hm : (fun p => ∑ i, w i * weight a i p) = x := by
    funext p; rw [mixture_coordinates a w hsum p]; dsimp only [w]; field_simp; ring
  have hh := core_simplex_minimum hd ho ha w hw hsum hwb; rw [hm] at hh; refine ⟨hh.1, ?_⟩; rw [hh.2]; constructor
  · rintro ⟨_, hz⟩ i hi; have h := hz i hi; have h' : x i - 1 = 0 := (div_eq_zero_iff.mp h).resolve_right (ne_of_gt ha); linarith
  · intro hz
    have hzero (i : Fin d) (hi : i ≠ ⟨0, by omega⟩) : w i = 0 := by
      dsimp only [w]; rw [hz i hi, sub_self, zero_div]
    refine ⟨?_, hzero⟩
    have hs : ∑ i, w i = w ⟨0, by omega⟩ := by
      apply Finset.sum_eq_single (⟨0, by omega⟩ : Fin d)
      · intro i _ hi; exact hzero i hi
      · simp
    exact hs.symm.trans hsum
end MMDCoreMinimum
namespace MMDInverseBound
open Matrix MMDCore
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
private theorem sum_abs_two_single (i j : ι) (hij : i ≠ j) (a b : ℝ) : (∑ p, |(Pi.single (M := fun _ : ι => ℝ) i a + Pi.single (M := fun _ : ι => ℝ) j b) p|) = |a| + |b| := by
  have he : (fun p => |(Pi.single (M := fun _ : ι => ℝ) i a + Pi.single (M := fun _ : ι => ℝ) j b) p|) =
      Pi.single (M := fun _ : ι => ℝ) i |a| + Pi.single (M := fun _ : ι => ℝ) j |b| := by
    funext p; by_cases hpi : p = i
    · subst p; simp [hij, Ne.symm hij]
    · by_cases hpj : p = j
      · subst p; simp [hij, Ne.symm hij]
      · simp [Pi.single_apply, hpi, hpj]
  rw [he]; simp [Pi.single_apply, Finset.sum_add_distrib]
private theorem inverse_column_sum {d : ℕ} (hd : 3 ≤ d) (j : Fin d) : ∑ p, |inverseCore hd p j| = 1 := by
  by_cases h0 : j.val = 0
  · have he : (fun p => inverseCore hd p j) =
        Pi.single (M := fun _ : Fin d => ℝ) ⟨d-1, by omega⟩ (1/2 : ℝ) +
          Pi.single ⟨1, by omega⟩ (-1/2 : ℝ) := by
      funext p; simp [inverseCore, h0, sub_eq_add_neg, Pi.single_apply] <;> split_ifs <;> ring
    rw [show (∑ p, |inverseCore hd p j|) = ∑ p, |(fun p => inverseCore hd p j) p| by rfl, he,
      sum_abs_two_single _ _ (by intro h; have hv := congrArg Fin.val h; dsimp at hv; omega)]
    norm_num
  · by_cases h1 : j.val = d-1
    · have hd0 : d-1 ≠ 0 := by
        exact Ne.symm (ne_of_ne_of_eq (fun a => h0 (id (Eq.symm a))) h1)
      have he : (fun p => inverseCore hd p j) =
          Pi.single (M := fun _ : Fin d => ℝ) ⟨0, by omega⟩ (1/2 : ℝ) +
            Pi.single ⟨d-2, by omega⟩ (1/2 : ℝ) := by
        funext p; simp [inverseCore, h1, hd0]
      rw [show (∑ p, |inverseCore hd p j|) = ∑ p, |(fun p => inverseCore hd p j) p| by rfl, he,
        sum_abs_two_single _ _ (by intro h; have hv := congrArg Fin.val h; dsimp at hv; omega)]
      norm_num
    · let c : ℝ := if j.val % 2 = 0 then 1/2 else -1/2; have he : (fun p => inverseCore hd p j) =
          Pi.single (M := fun _ : Fin d => ℝ) ⟨j.val-1, by omega⟩ c +
            Pi.single ⟨j.val+1, by omega⟩ (-c) := by
        funext p; simp only [inverseCore, h0, h1, dite_false]; change c * _ = _; simp only [Pi.sub_apply, Pi.add_apply, Pi.single_apply]
        split_ifs <;> ring
      rw [show (∑ p, |inverseCore hd p j|) = ∑ p, |(fun p => inverseCore hd p j) p| by rfl, he,
        sum_abs_two_single _ _ (by intro h; have hv := congrArg Fin.val h; dsimp at hv; omega)]
      dsimp [c]
      split_ifs <;> norm_num
private theorem inverse_row_sum {d : ℕ} (hd : 3 ≤ d) (ho : d % 2 = 1) (i : Fin d) : ∑ j, |(core d)⁻¹ i j| = 1 := by
  have hs : (core d)⁻¹.IsSymm := (core_symm d).inv
  calc
    _ = ∑ j, |(core d)⁻¹ j i| := by
      apply Finset.sum_congr rfl; intro j _; rw [hs.apply]
    _ = 1 := by rw [inverse_eq hd ho]; exact inverse_column_sum hd i
end MMDInverseBound
namespace MMDScaledInverse
open Matrix MMDCore MMDVariational MMDInverseBound
variable {d : ℕ}
private theorem half_cancel (x : Fin d → ℝ) (hx : ∀ i, 1 ≤ x i) : (diagonal (fun i => Real.sqrt ((x) i))) * D5.S3.Observer.Hankel.BalancedHankelSchmidt.invRootDiagonal x = 1 ∧ D5.S3.Observer.Hankel.BalancedHankelSchmidt.invRootDiagonal x * (diagonal (fun i => Real.sqrt ((x) i))) = 1 := by
  have hn (i : Fin d) : Real.sqrt (x i) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (lt_of_lt_of_le zero_lt_one (hx i))); constructor <;> ext i j <;> by_cases hij : i = j
  all_goals first
    | (subst j; simp [D5.S3.Observer.Hankel.BalancedHankelSchmidt.invRootDiagonal, diagonal_mul_diagonal, hn])
    | simp [D5.S3.Observer.Hankel.BalancedHankelSchmidt.invRootDiagonal, diagonal_mul_diagonal, hij]
private theorem compressed_inverse (hd : 3 ≤ d) (ho : d % 2 = 1) (x : Fin d → ℝ) (hx : ∀ i, 1 ≤ x i) : (compressed x (core d))⁻¹ = D5.S3.Observer.Hankel.BalancedHankelSchmidt.invRootDiagonal x * (core d)⁻¹ * D5.S3.Observer.Hankel.BalancedHankelSchmidt.invRootDiagonal x := by
  have hc := half_cancel x hx; have hMu : IsUnit (core d) := MMDCoreMinimum.core_unit hd ho; letI := hMu.invertible; apply Matrix.inv_eq_right_inv; change ((diagonal (fun i => Real.sqrt ((x) i))) * core d * (diagonal (fun i => Real.sqrt ((x) i)))) *
    (D5.S3.Observer.Hankel.BalancedHankelSchmidt.invRootDiagonal x * (core d)⁻¹ * D5.S3.Observer.Hankel.BalancedHankelSchmidt.invRootDiagonal x) = 1
  calc
    _ = (diagonal (fun i => Real.sqrt ((x) i))) * core d * ((diagonal (fun i => Real.sqrt ((x) i))) * D5.S3.Observer.Hankel.BalancedHankelSchmidt.invRootDiagonal x) * (core d)⁻¹ * D5.S3.Observer.Hankel.BalancedHankelSchmidt.invRootDiagonal x := by simp [mul_assoc]
    _ = 1 := by rw [hc.1]; simp [mul_assoc, hc.1]
private theorem compressed_row_bound (hd : 3 ≤ d) (ho : d % 2 = 1) (x : Fin d → ℝ) (hx : ∀ i, 1 ≤ x i) (i : Fin d) : ∑ j, ‖(compressed x (core d))⁻¹ i j‖ ≤ 1 := by
  have hq (p : Fin d) : |(Real.sqrt (x p))⁻¹| ≤ 1 := by
    rw [abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]; exact inv_le_one_of_one_le₀ (Real.one_le_sqrt.mpr (hx p))
  rw [compressed_inverse hd ho x hx]
  calc
    _ ≤ ∑ j, |(core d)⁻¹ i j| := by
      apply Finset.sum_le_sum; intro j _
      simp only [D5.S3.Observer.Hankel.BalancedHankelSchmidt.invRootDiagonal, Matrix.diagonal_mul, Matrix.mul_diagonal, Real.norm_eq_abs,
        abs_mul]
      calc
        _ ≤ 1 * |(core d)⁻¹ i j| * 1 := mul_le_mul
          (mul_le_mul_of_nonneg_right (hq i) (abs_nonneg _)) (hq j)
          (abs_nonneg _) (by positivity)
        _ = _ := by ring
    _ = 1 := inverse_row_sum hd ho i
end MMDScaledInverse
namespace MMDSpectral
open Matrix Polynomial
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
private theorem eigenvalue_row_bound (A : Matrix ι ι ℝ) {r : ℝ} (hr : r ∈ spectrum ℝ A) (hrow : ∀ i, ∑ j, ‖A i j‖ ≤ 1) : |r| ≤ 1 := by
  have he : Module.End.HasEigenvalue (Matrix.toLin' A) r := by
    apply Module.End.HasEigenvalue.of_mem_spectrum
    rwa [Matrix.spectrum_toLin']
  obtain ⟨k, hk⟩ := eigenvalue_mem_ball he
  have hball : ‖r - A k k‖ ≤ ∑ j ∈ Finset.univ.erase k, ‖A k j‖ := by
    exact Metric.mem_closedBall.mp hk
  calc
    |r| = ‖(r - A k k) + A k k‖ := by rw [sub_add_cancel, Real.norm_eq_abs]
    _ ≤ ‖r-A k k‖ + ‖A k k‖ := norm_add_le _ _
    _ ≤ (∑ j ∈ Finset.univ.erase k, ‖A k j‖) + ‖A k k‖ := by linarith
    _ = ∑ j, ‖A k j‖ := Finset.sum_erase_add _ _ (Finset.mem_univ k)
    _ ≤ 1 := hrow k
private theorem eigenvalue_gap (A : Matrix ι ι ℝ) (hA : A.IsHermitian) (hu : IsUnit A) (hrow : ∀ i, ∑ j, ‖A⁻¹ i j‖ ≤ 1) (i : ι) : 1 ≤ |hA.eigenvalues i| := by
  obtain ⟨u, rfl⟩ := hu; have hr := hA.eigenvalues_mem_spectrum_real i
  have hir : (hA.eigenvalues i)⁻¹ ∈ spectrum ℝ ((u : Matrix ι ι ℝ)⁻¹) := by
    rw [← Matrix.coe_units_inv]; exact spectrum.inv₀_mem_inv hr
  have hb := eigenvalue_row_bound _ hir hrow
  have hne : hA.eigenvalues i ≠ 0 := by
    exact spectrum.ne_zero_of_mem_of_unit hr
  rw [abs_inv] at hb; exact (inv_le_one₀ (abs_pos.mpr hne)).mp hb
private theorem energy_conjugate (A U : Matrix ι ι ℝ) (hUU : Uᵀ*U=1) : energy (U*A*Uᵀ) = energy A := by
  have hc : (U*A*Uᵀ).charpoly = A.charpoly := by
    rw [Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hUU, one_mul]
  simp only [energy, hc]
private theorem energy_diagonal (a : ι → ℝ) : energy (diagonal a) = ∑ i, |a i| := by
  rw [energy, Matrix.charpoly_diagonal, Polynomial.roots_prod]
  · simp
  · exact Finset.prod_ne_zero_iff.mpr (fun i _ => Polynomial.X_sub_C_ne_zero _)
private theorem energy_shift_diagonalized (A : Matrix ι ι ℝ) (hA : A.IsHermitian) : energy (A-1) = ∑ i, |hA.eigenvalues i - 1| := by
  let U : Matrix ι ι ℝ := hA.eigenvectorUnitary; have hUU : Uᵀ*U=1 := (Matrix.mem_orthogonalGroup_iff' ι ℝ).mp hA.eigenvectorUnitary.2; have hUT : U*Uᵀ=1 := (Matrix.mem_orthogonalGroup_iff ι ℝ).mp hA.eigenvectorUnitary.2
  have hdiag : A = U*diagonal hA.eigenvalues*Uᵀ := by
    simpa [U, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using hA.spectral_theorem
  have hs : A-1 = U*diagonal (fun i => hA.eigenvalues i-1)*Uᵀ := by
    conv_lhs => rw [hdiag]
    have hd : diagonal (fun i => hA.eigenvalues i-1) = diagonal hA.eigenvalues - 1 := by
      rw [← Matrix.diagonal_one, ← Matrix.diagonal_sub]
    rw [hd, mul_sub, sub_mul, mul_one, hUT]
  rw [hs, energy_conjugate _ U hUU, energy_diagonal]
private theorem energy_shift_gap (A : Matrix ι ι ℝ) (hA : A.IsHermitian) (hgap : ∀ i, 1 ≤ |hA.eigenvalues i|) : energy (A-1) = energy A + (Fintype.card ι : ℝ) - 2 * (RHLinalg.posIndex hA : ℝ) := by
  rw [energy_shift_diagonalized A hA,
    D5.S3.Combinatorics.Graph.KyFanGap.MandalMehatariDasSeidelMinimum.energy_eigenvalues hA]
  have ht (i : ι) : |hA.eigenvalues i-1| = |hA.eigenvalues i| + 1 -
      2 * (if 0 < hA.eigenvalues i then (1 : ℝ) else 0) := by
    have hg := hgap i; by_cases hp : 0 < hA.eigenvalues i
    · rw [abs_of_pos hp] at hg; rw [if_pos hp, abs_of_pos hp, abs_of_nonneg (by linarith)]; ring
    · have hn : hA.eigenvalues i ≤ 0 := le_of_not_gt hp; rw [if_neg hp, abs_of_nonpos hn, abs_of_nonpos (by linarith)]; ring
  simp_rw [ht]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one, ← Finset.mul_sum]
  congr 1; congr 1; simp only [RHLinalg.posIndex, Nat.cast_sum, Finset.sum_boole]
end MMDSpectral
namespace MMDMatrixEnergy
open Matrix MMDCore MMDVariational MMDStrictness MMDSymmetry MMDCoreMinimum
open MMDScaledInverse MMDSpectral
private theorem compressed_energy {d : ℕ} (hd : 3 ≤ d) (ho : d % 2 = 1) (x : Fin d → ℝ) (hx : ∀ i, 1 ≤ x i) : energy (compressed x (core d)-1) = value x (core d) + (d : ℝ) - 2 * (RHLinalg.posIndex (Matrix.isHermitian_iff_isSymm.mpr (core_symm d)) : ℝ) := by
  have hM : (core d).IsHermitian := Matrix.isHermitian_iff_isSymm.mpr (core_symm d); have hQ : ((diagonal (fun i => Real.sqrt ((x) i)))).PosDef := Matrix.PosDef.diagonal
    (fun i => Real.sqrt_pos.mpr (lt_of_lt_of_le zero_lt_one (hx i)))
  letI := hQ.isUnit.invertible; have hR := compressed_hermitian x (core d) hM; have hRu : IsUnit (compressed x (core d)) := (hQ.isUnit.mul (core_unit hd ho)).mul hQ.isUnit; have hgap := eigenvalue_gap (compressed x (core d)) hR hRu (compressed_row_bound hd ho x hx); have hindex := RHLinalg.posIndex_conj_eq_of_rightInverse hM ((diagonal (fun i => Real.sqrt ((x) i))))
    ((diagonal (fun i => Real.sqrt ((x) i))))⁻¹ (by simp)
  have hindex' : RHLinalg.posIndex hR = RHLinalg.posIndex hM := by
    simpa only [compressed, hQ.isHermitian.eq] using hindex
  rw [energy_shift_gap _ hR hgap, hindex']
  have hv : energy (compressed x (core d)) = value x (core d) := by
    change energy (compressed x (core d)) = (CFC.sqrt (compressed x (core d) * compressed x (core d))).trace
    rw [D5.S3.Combinatorics.Graph.KyFanGap.MandalMehatariDasSeidelMinimum.energy_eigenvalues hR,
      D5.S3.Combinatorics.Graph.KyFanGap.MandalMehatariDasSeidelMinimum.Spectral.sum_abs_eq_trace_sqrt hR,
      hR.isSymm.eq]
  rw [hv]; simp only [Fintype.card_fin]
private theorem core_energy_minimum {d : ℕ} (hd : 3 ≤ d) (ho : d % 2 = 1) (x : Fin d → ℝ) (hx : ∀ i, 1 ≤ x i) (hbase : 1 < x ⟨0, by omega⟩) : energy (compressed (weight (∑ i, (x i - 1)) ⟨0, by omega⟩) (core d)-1) ≤ energy (compressed x (core d)-1) ∧ (energy (compressed x (core d)-1) = energy (compressed (weight (∑ i, (x i - 1)) ⟨0, by omega⟩) (core d)-1) ↔ ∀ i, i ≠ ⟨0, by omega⟩ → x i = 1) := by
  let a : ℝ := ∑ i, (x i-1); have ha : 0 < a := Finset.sum_pos' (fun i _ => sub_nonneg.mpr (hx i))
    ⟨⟨0, by omega⟩, Finset.mem_univ _, sub_pos.mpr hbase⟩
  have hvx : ∀ i : Fin d, 1 ≤ weight a ⟨0, by omega⟩ i := by
    intro i; unfold weight
    split_ifs <;> linarith
  have hmin := core_diagonal_minimum hd ho x hx hbase; rw [compressed_energy hd ho x hx, compressed_energy hd ho _ hvx]; refine ⟨by linarith [hmin.1], ?_⟩; constructor
  · intro he; apply hmin.2.mp; linarith
  · intro he; have hv := hmin.2.mpr he; linarith
end MMDMatrixEnergy
namespace MandalMehatariDasSeidel
def binaryString {k : ℕ} (s t : Fin k → ℕ) : List Bool := (List.ofFn fun i : Fin k => List.replicate (s i) false ++ List.replicate (t i) true).flatten
def chainGraph (b : List Bool) : SimpleGraph (Fin b.length) where
  Adj i j :=
    (i < j ∧ b.get i = false ∧ b.get j = true) ∨
    (j < i ∧ b.get j = false ∧ b.get i = true)
  symm := ⟨fun _ _ h => h.elim Or.inr Or.inl⟩
  loopless := ⟨fun i h => h.elim (fun h => (lt_irrefl i) h.1) (fun h => (lt_irrefl i) h.1)⟩
noncomputable def seidel {n : ℕ} (G : SimpleGraph (Fin n)) : Matrix (Fin n) (Fin n) ℝ := by
  classical
  exact Matrix.of (fun _ _ => 1) - 1 - (2 : ℝ) • G.adjMatrix ℝ
def Gamma (n k : ℕ) (b : List Bool) : Prop := ∃ s₁ tₖ : ℕ, 1 ≤ s₁ ∧ s₁ ≤ n - 2 * k + 1 ∧ 1 ≤ tₖ ∧ tₖ ≤ n - 2 * k + 1 ∧ s₁ + tₖ = n - 2 * k + 2 ∧ b = List.replicate s₁ false ++ (List.replicate (k - 1) [true, false]).flatten ++ List.replicate tₖ true
def claim : Prop := ∀ n k : ℕ, 1 ≤ k → 2 * k ≤ n → ∀ s t : Fin k → ℕ, (∀ i : Fin k, 1 ≤ s i) → (∀ i : Fin k, 1 ≤ t i) → (∑ i : Fin k, (s i + t i)) = n → ∀ h : List Bool, Gamma n k h → energy (seidel (chainGraph h)) ≤ energy (seidel (chainGraph (binaryString s t))) ∧ (energy (seidel (chainGraph (binaryString s t))) = energy (seidel (chainGraph h)) ↔ Gamma n k (binaryString s t))
end MandalMehatariDasSeidel
open MandalMehatariDasSeidel
namespace MMDBoundary
private theorem energy_involution {n : ℕ} (A U : Matrix (Fin n) (Fin n) ℝ) (hUU : U*U=1) : energy (U*A*U) = energy A := by
  have hc : (U*A*U).charpoly = A.charpoly := by
    rw [Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hUU, one_mul]
  simp only [energy, hc]
private theorem seidel_bipartite_switch {n : ℕ} (G : SimpleGraph (Fin n)) (c : Fin n → Bool) (hG : ∀ i j, G.Adj i j ↔ c i ≠ c j) : diagonal (fun i => if c i then (-1 : ℝ) else 1) * seidel G * diagonal (fun i => if c i then (-1 : ℝ) else 1) = Matrix.of (fun _ _ => 1) - 1 := by
  classical
  ext i j
  simp only [diagonal_mul, mul_diagonal, seidel, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.of_apply, Matrix.one_apply, smul_eq_mul, SimpleGraph.adjMatrix_apply]
  by_cases hij : i = j
  · subst j; simp
  · simp only [hij, ite_false]; rw [hG]
    cases hci : c i <;> cases hcj : c j <;> norm_num
private theorem bipartite_energy {n : ℕ} (G : SimpleGraph (Fin n)) (c : Fin n → Bool) (hG : ∀ i j, G.Adj i j ↔ c i ≠ c j) : energy (seidel G) = energy (Matrix.of (fun (_ : Fin n) (_ : Fin n) => (1 : ℝ)) - 1) := by
  let U : Matrix (Fin n) (Fin n) ℝ := diagonal (fun i => if c i then (-1 : ℝ) else 1)
  have hUU : U*U=1 := by
    ext i j; by_cases hij : i = j
    · subst j; simp [U, diagonal_mul_diagonal]
      split_ifs <;> norm_num
    · simp [U, diagonal_mul_diagonal, hij]
  rw [← seidel_bipartite_switch G c hG]; exact (energy_involution _ U hUU).symm
private theorem two_run_get (s t : ℕ) (i : Fin ((List.replicate s false ++ List.replicate t true).length)) : (List.replicate s false ++ List.replicate t true).get i = if i.val < s then false else true := by
  simp only [List.get_eq_getElem, List.getElem_append, List.length_replicate]
  split_ifs <;> simp
private theorem two_run_adj (s t : ℕ) (i j : Fin ((List.replicate s false ++ List.replicate t true).length)) : (chainGraph (List.replicate s false ++ List.replicate t true)).Adj i j ↔ (List.replicate s false ++ List.replicate t true).get i ≠ (List.replicate s false ++ List.replicate t true).get j := by
  change ((i < j ∧ _ ∧ _) ∨ (j < i ∧ _ ∧ _)) ↔ _; rw [two_run_get, two_run_get]; simp only [Fin.lt_iff_val_lt_val]
  split_ifs <;> simp_all <;> omega
private theorem binary_one (s t : Fin 1 → ℕ) : binaryString s t = List.replicate (s 0) false ++ List.replicate (t 0) true := by
  simp [binaryString, List.ofFn_succ]
private theorem binary_length {k : ℕ} (s t : Fin k → ℕ) : (binaryString s t).length = ∑ i, (s i + t i) := by
  simp [binaryString, List.length_flatten, List.map_ofFn, List.sum_ofFn]
private theorem gamma_one_iff (n : ℕ) (hn2 : 2 ≤ n) (b : List Bool) : Gamma n 1 b ↔ ∃ s t : ℕ, 1 ≤ s ∧ 1 ≤ t ∧ s+t=n ∧ b=List.replicate s false ++ List.replicate t true := by
  unfold Gamma; simp only [Nat.mul_one, Nat.sub_self, List.replicate_zero, List.flatten_nil, List.append_nil]; constructor
  · rintro ⟨s,t,hs,_,ht,_,hn,hb⟩; exact ⟨s,t,hs,ht,by omega,hb⟩
  · rintro ⟨s,t,hs,ht,hn,hb⟩; exact ⟨s,t,hs,by omega,ht,by omega,by omega,hb⟩
private noncomputable def completeEnergy (n : ℕ) : ℝ := energy (Matrix.of (fun (_ : Fin n) (_ : Fin n) => (1 : ℝ)) - 1)
private theorem two_run_energy (s t : ℕ) : energy (seidel (chainGraph (List.replicate s false ++ List.replicate t true))) = completeEnergy (s+t) := by
  have h := bipartite_energy (chainGraph (List.replicate s false ++ List.replicate t true))
    (fun i => (List.replicate s false ++ List.replicate t true).get i) (two_run_adj s t)
  change _ = completeEnergy (List.replicate s false ++ List.replicate t true).length at h; simpa only [List.length_append, List.length_replicate] using h
private theorem gamma_one_energy {n : ℕ} (hn2 : 2 ≤ n) {b : List Bool} (hb : Gamma n 1 b) : energy (seidel (chainGraph b)) = completeEnergy n := by
  obtain ⟨s,t,hs,ht,hn,rfl⟩ := (gamma_one_iff n hn2 b).mp hb; rw [two_run_energy, hn]
private theorem binary_one_gamma (n : ℕ) (s t : Fin 1 → ℕ) (hs : ∀ i, 1 ≤ s i) (ht : ∀ i, 1 ≤ t i) (hn : ∑ i, (s i+t i) = n) : Gamma n 1 (binaryString s t) := by
  have hn0 : s 0 + t 0 = n := by exact Nat.add_right_cancel hn
  have hn2 : 2 ≤ n := by have := hs 0; have := ht 0; omega
  rw [binary_one, gamma_one_iff n hn2]; refine ⟨s 0,t 0,hs 0,ht 0,?_,rfl⟩; simpa using hn
private theorem result_one (n : ℕ) (s t : Fin 1 → ℕ) (hs : ∀ i, 1 ≤ s i) (ht : ∀ i, 1 ≤ t i) (hn : ∑ i, (s i+t i) = n) (h : List Bool) (hGamma : Gamma n 1 h) : energy (seidel (chainGraph h)) ≤ energy (seidel (chainGraph (binaryString s t))) ∧ (energy (seidel (chainGraph (binaryString s t))) = energy (seidel (chainGraph h)) ↔ Gamma n 1 (binaryString s t)) := by
  have hn0 : s 0 + t 0 = n := by exact Nat.add_right_cancel hn
  have hn2 : 2 ≤ n := by have := hs 0; have := ht 0; omega
  have hg := binary_one_gamma n s t hs ht hn
  have he : energy (seidel (chainGraph (binaryString s t))) = energy (seidel (chainGraph h)) :=
    (gamma_one_energy hn2 hg).trans (gamma_one_energy hn2 hGamma).symm
  exact ⟨he.ge, ⟨fun _ => hg, fun _ => he⟩⟩
end MMDBoundary
namespace MMDCompression
open Matrix Polynomial
private theorem compression_charpoly {n d : ℕ} (hdn : d ≤ n) (M Q : Matrix (Fin d) (Fin d) ℝ) (Z : Matrix (Fin n) (Fin d) ℝ) (hZ : Zᵀ * Z = Q * Q) : (Z * M * Zᵀ).charpoly = X ^ (n-d) * (Q*M*Q).charpoly := by
  have hh := Matrix.charpoly_mul_comm_of_le Z (M*Zᵀ) (by simpa using hdn); rw [← Matrix.mul_assoc] at hh; simp only [Fintype.card_fin] at hh; rw [hh]; congr 1; rw [Matrix.mul_assoc, hZ]; simpa only [← Matrix.mul_assoc] using Matrix.charpoly_mul_comm (M*Q) Q
private theorem shifted_compression_charpoly {n d : ℕ} (hdn : d ≤ n) (M Q : Matrix (Fin d) (Fin d) ℝ) (Z : Matrix (Fin n) (Fin d) ℝ) (hZ : Zᵀ * Z = Q * Q) : (Z*M*Zᵀ-1).charpoly = (X+C 1)^(n-d) * (Q*M*Q-1).charpoly := by
  have hscalar (m : ℕ) : (Matrix.scalar (Fin m) (1 : ℝ)) = 1 :=
    (Matrix.scalar (Fin m)).map_one
  rw [← hscalar n, Matrix.charpoly_sub_scalar, compression_charpoly hdn M Q Z hZ]
  rw [Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.X_comp,
    ← Matrix.charpoly_sub_scalar, hscalar]
private theorem shifted_compression_energy {n d : ℕ} (hdn : d ≤ n) (M Q : Matrix (Fin d) (Fin d) ℝ) (Z : Matrix (Fin n) (Fin d) ℝ) (hZ : Zᵀ * Z = Q * Q) : energy (Z*M*Zᵀ-1) = (n-d : ℕ) + energy (Q*M*Q-1) := by
  have hc := shifted_compression_charpoly hdn M Q Z hZ
  have hne : (X+C (1 : ℝ))^(n-d) * (Q*M*Q-1).charpoly ≠ 0 := by
    rw [← hc]; exact (Matrix.charpoly_monic _).ne_zero
  simp only [energy, hc, Polynomial.roots_mul hne, Multiset.map_add, Multiset.sum_add,
    Polynomial.roots_pow, Polynomial.roots_X_add_C, Multiset.map_nsmul,
    Multiset.map_singleton, abs_neg, abs_one, Multiset.sum_nsmul,
    Multiset.sum_singleton, nsmul_eq_mul, mul_one]
end MMDCompression
namespace MMDGraphCompression
open Matrix MMDCore
private def merge {k : ℕ} (hk : 2 ≤ k) (r : Fin (2*k)) : Fin (2*k-1) := if h : r.val = 2*k-1 then ⟨0, by omega⟩ else ⟨r.val, by omega⟩
private theorem merged_entry {k : ℕ} (hk : 2 ≤ k) (r q : Fin (2*k)) : core (2*k) r q = MMDCore.sign (Fin.castSucc r) * MMDCore.sign (Fin.castSucc q) * core (2*k-1) (merge hk r) (merge hk q) := by
  unfold core entry merge MMDCore.sign
  simp only [Fin.val_castSucc]
  split_ifs <;> norm_num at * <;> omega
private theorem indicator_compression {n d : ℕ} (c : Fin n → Fin d) (M : Matrix (Fin d) (Fin d) ℝ) : ((1 : Matrix (Fin d) (Fin d) ℝ).submatrix c id) * M * (((1 : Matrix (Fin d) (Fin d) ℝ).submatrix c id))ᵀ = M.submatrix c c := by
  ext u v; simp [Matrix.mul_apply, Matrix.submatrix_apply, Matrix.one_apply, Matrix.transpose_apply, id_eq, ite_mul, mul_ite]
private theorem indicator_gram {n d : ℕ} (c : Fin n → Fin d) : (((1 : Matrix (Fin d) (Fin d) ℝ).submatrix c id))ᵀ * ((1 : Matrix (Fin d) (Fin d) ℝ).submatrix c id) = diagonal (fun p => ((Finset.univ.filter (fun u => c u = p)).card : ℝ)) := by
  ext p q; by_cases hpq : p = q
  · subst q; simp only [Matrix.mul_apply, Matrix.submatrix_apply, Matrix.one_apply, Matrix.transpose_apply, id_eq, Matrix.diagonal_apply_eq]
    calc
      _ = ∑ j, if c j=p then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl; intro j _
        split_ifs <;> norm_num
      _ = _ := by simp
  · simp only [Matrix.mul_apply, Matrix.submatrix_apply, Matrix.one_apply, Matrix.transpose_apply, id_eq, Matrix.diagonal_apply_ne _ hpq]; apply Finset.sum_eq_zero; intro u _; by_cases hcp : c u = p
    · have hcq : c u ≠ q := by exact ne_of_eq_of_ne hcp hpq
      simp [hcq, hcp, hpq]
    · simp [hcp]
private theorem run_adj {b : List Bool} {k : ℕ} (r : Fin b.length → Fin (2*k)) (hmono : Monotone r) (hzero : ∀ i, b.get i = false ↔ (r i).val % 2 = 0) (hone : ∀ i, b.get i = true ↔ (r i).val % 2 = 1) (i j : Fin b.length) : (chainGraph b).Adj i j ↔ ((r i < r j ∧ (r i).val % 2 = 0 ∧ (r j).val % 2 = 1) ∨ (r j < r i ∧ (r j).val % 2 = 0 ∧ (r i).val % 2 = 1)) := by
  have hlt (p q : Fin b.length) (hp : (r p).val % 2 = 0) (hq : (r q).val % 2 = 1) :
      p < q ↔ r p < r q := by
    constructor
    · intro h; have hh := hmono h.le
      have hn : r p ≠ r q := by intro he; rw [he] at hp; omega
      exact lt_of_le_of_ne hh hn
    · intro h; by_contra hn; have hh := hmono (le_of_not_gt hn); exact (not_lt_of_ge hh) h
  change ((i < j ∧ _ ∧ _) ∨ (j < i ∧ _ ∧ _)) ↔ _; rw [hzero i, hone j, hzero j, hone i]; constructor
  · rintro (⟨h,hz,ho⟩ | ⟨h,hz,ho⟩)
    · exact Or.inl ⟨(hlt i j hz ho).mp h,hz,ho⟩
    · exact Or.inr ⟨(hlt j i hz ho).mp h,hz,ho⟩
  · rintro (⟨h,hz,ho⟩ | ⟨h,hz,ho⟩)
    · exact Or.inl ⟨(hlt i j hz ho).mpr h,hz,ho⟩
    · exact Or.inr ⟨(hlt j i hz ho).mpr h,hz,ho⟩
private theorem run_full_matrix {b : List Bool} {k : ℕ} (r : Fin b.length → Fin (2*k)) (hmono : Monotone r) (hzero : ∀ i, b.get i = false ↔ (r i).val % 2 = 0) (hone : ∀ i, b.get i = true ↔ (r i).val % 2 = 1) (i j : Fin b.length) : (seidel (chainGraph b) + 1) i j = core (2*k) (r i) (r j) := by
  classical
  simp only [seidel, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.of_apply, smul_eq_mul, SimpleGraph.adjMatrix_apply]
  rw [run_adj r hmono hzero hone]; unfold core entry; simp only [Fin.lt_def]
  split_ifs <;> norm_num <;> ring
private theorem switched_compression {b : List Bool} {k : ℕ} (hk : 2 ≤ k) (r : Fin b.length → Fin (2*k)) (hmono : Monotone r) (hzero : ∀ i, b.get i = false ↔ (r i).val % 2 = 0) (hone : ∀ i, b.get i = true ↔ (r i).val % 2 = 1) : diagonal (fun u => MMDCore.sign (Fin.castSucc (r u))) * (seidel (chainGraph b) + 1) * diagonal (fun u => MMDCore.sign (Fin.castSucc (r u))) = ((1 : Matrix (Fin (2*k-1)) (Fin (2*k-1)) ℝ).submatrix (fun u => merge hk (r u)) id) * core (2*k-1) * (((1 : Matrix (Fin (2*k-1)) (Fin (2*k-1)) ℝ).submatrix (fun u => merge hk (r u)) id))ᵀ := by
  rw [indicator_compression]; ext u v; simp only [diagonal_mul, mul_diagonal, Matrix.submatrix_apply]; rw [run_full_matrix r hmono hzero hone, merged_entry hk]; unfold MMDCore.sign
  split_ifs <;> ring
end MMDGraphCompression
namespace MMDLabels
private def labels {k : ℕ} (s t : Fin k → ℕ) : List ℕ := (List.ofFn fun i : Fin k => List.replicate (s i) (2*i.val) ++ List.replicate (t i) (2*i.val+1)).flatten
private theorem labels_length {k : ℕ} (s t : Fin k → ℕ) : (labels s t).length = (binaryString s t).length := by
  simp [labels, binaryString, List.length_flatten, List.map_ofFn, Function.comp_def]
private theorem labels_bound {k : ℕ} (s t : Fin k → ℕ) {q : ℕ} (hq : q ∈ labels s t) : q < 2*k := by
  simp only [labels, List.mem_flatten, List.mem_ofFn] at hq; obtain ⟨_, ⟨i,rfl⟩, hi⟩ := hq; simp only [List.mem_append, List.mem_replicate] at hi; rcases hi with ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> have := i.isLt <;> omega
private theorem labels_bits {k : ℕ} (s t : Fin k → ℕ) : (labels s t).map (fun q => decide (q%2=1)) = binaryString s t := by
  simp [labels, binaryString, List.map_flatten, List.map_ofFn, Function.comp_def]
private theorem labels_sorted {k : ℕ} (s t : Fin k → ℕ) : (labels s t).Pairwise (· ≤ ·) := by
  rw [labels, List.pairwise_flatten]; constructor
  · intro l hl; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hl; rw [List.pairwise_append]; refine ⟨List.pairwise_replicate_of_refl, List.pairwise_replicate_of_refl, ?_⟩; intro a ha b hb; obtain ⟨_,rfl⟩ := List.mem_replicate.mp ha; obtain ⟨_,rfl⟩ := List.mem_replicate.mp hb; omega
  · rw [List.pairwise_ofFn]; intro i j hij a ha b hb; simp only [List.mem_append, List.mem_replicate] at ha hb; rcases ha with ⟨_,rfl⟩ | ⟨_,rfl⟩ <;>
      rcases hb with ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> have hv := hij <;> change i.val < j.val at hv <;> omega
private def run {k : ℕ} (s t : Fin k → ℕ) (i : Fin (binaryString s t).length) : Fin (2*k) := ⟨(labels s t).get (Fin.cast (labels_length s t).symm i), labels_bound s t (List.get_mem _ _)⟩
private theorem run_monotone {k : ℕ} (s t : Fin k → ℕ) : Monotone (run s t) := by
  intro i j hij; exact (labels_sorted s t).rel_get_of_le hij
private theorem run_get {k : ℕ} (s t : Fin k → ℕ) (i : Fin (binaryString s t).length) : (binaryString s t).get i = decide ((run s t i).val%2=1) := by
  have he := List.getElem_map (f := fun q : ℕ => decide (q%2=1))
    (l := labels s t) (i := i.val) (h := by simpa only [List.length_map, labels_length] using i.isLt)
  apply Bool.eq_iff_iff.mpr; change ((binaryString s t).get i = true ↔ decide ((run s t i).val%2=1)=true); rw [decide_eq_true_eq]; have hh := Bool.eq_iff_iff.mp he; simpa only [labels_bits, run, List.get_eq_getElem, Fin.val_cast, decide_eq_true_eq] using hh
private theorem run_zero {k : ℕ} (s t : Fin k → ℕ) (i : Fin (binaryString s t).length) : (binaryString s t).get i = false ↔ (run s t i).val%2=0 := by
  rw [run_get]; simp only [decide_eq_false_iff_not]; omega
private theorem run_one {k : ℕ} (s t : Fin k → ℕ) (i : Fin (binaryString s t).length) : (binaryString s t).get i = true ↔ (run s t i).val%2=1 := by
  rw [run_get]; simp
private def rawSize {k : ℕ} (s t : Fin k → ℕ) (q : Fin (2*k)) : ℕ := if q.val%2=0 then s ⟨q.val/2,by have := q.isLt; omega⟩ else t ⟨q.val/2,by have := q.isLt; omega⟩
private theorem labels_count {k : ℕ} (s t : Fin k → ℕ) (q : Fin (2*k)) : (labels s t).count q.val = rawSize s t q := by
  classical
  simp only [labels, List.count_flatten, List.map_ofFn, List.sum_ofFn,
    List.count_append, List.count_replicate, Function.comp_def]
  let j : Fin k := ⟨q.val/2,by have := q.isLt; omega⟩; rw [Finset.sum_eq_single j]
  · dsimp [j,rawSize]; simp only [beq_iff_eq]
    split_ifs <;> omega
  · intro i hi hij
    have hne : i.val ≠ q.val/2 := by intro h; exact hij (Fin.ext h)
    have h0 : ¬ 2*i.val=q.val := by omega
    have h1 : ¬ 2*i.val+1=q.val := by omega
    simp only [List.count_replicate,beq_iff_eq,if_neg h0,if_neg h1,Nat.zero_add]
  · simp
end MMDLabels
namespace MMDCounts
open MMDLabels MMDGraphCompression
private theorem count_ofFn {α : Type*} [DecidableEq α] {n : ℕ} (f : Fin n → α) (p : α) : (List.ofFn f).count p = ∑ i, if f i = p then 1 else 0 := by
  simpa [List.count_eq_countP, Function.comp_def, List.map_ofFn, List.sum_ofFn] using
    (List.countP_flatMap (p := fun a => a == p) (l := List.ofFn f) (f := fun a => [a]))
private theorem fiber_count {α : Type*} [DecidableEq α] {n : ℕ} (f : Fin n → α) (p : α) : (Finset.univ.filter (fun i => f i=p)).card = (List.ofFn f).count p := by
  rw [count_ofFn, Finset.card_eq_sum_ones, Finset.sum_filter]
private theorem ofFn_run {k : ℕ} (s t : Fin k → ℕ) : List.ofFn (fun i => (run s t i).val) = labels s t := by
  calc
    _ = List.ofFn (fun i => (labels s t).get (Fin.cast (labels_length s t).symm i)) := rfl
    _ = List.ofFn (labels s t).get := (List.ofFn_congr (labels_length s t) _).symm
    _ = labels s t := List.ofFn_get _
private def mergeN (k q : ℕ) : ℕ := if q=2*k-1 then 0 else q
private theorem count_merge {k : ℕ} (hk : 2 ≤ k) (l : List ℕ) (p : Fin (2*k-1)) : (l.map (mergeN k)).count p.val = if p.val=0 then l.count 0+l.count (2*k-1) else l.count p.val := by
  induction l with
  | nil => simp
  | cons q l ih =>
    simp only [List.map_cons, List.count_cons, ih, beq_iff_eq]; have hp := p.isLt; unfold mergeN
    split_ifs <;> omega
private noncomputable def classMap {k : ℕ} (hk : 2 ≤ k) (s t : Fin k → ℕ) := fun i => merge hk (run s t i)
private def classSize {k : ℕ} (hk : 2 ≤ k) (s t : Fin k → ℕ) (p : Fin (2*k-1)) : ℕ := if p.val=0 then s ⟨0,by omega⟩+t ⟨k-1,by omega⟩ else rawSize s t ⟨p.val,by have := p.isLt; omega⟩
private theorem classMap_count {k : ℕ} (hk : 2 ≤ k) (s t : Fin k → ℕ) (p : Fin (2*k-1)) : (Finset.univ.filter (fun i => classMap hk s t i=p)).card = classSize hk s t p := by
  classical
  have hf : (Finset.univ.filter (fun i => classMap hk s t i=p)) =
      Finset.univ.filter (fun i => (classMap hk s t i).val=p.val) := by
    exact Finset.filter_congr_decidable Finset.univ (fun i => classMap hk s t i = p) fun a =>
      instDecidableEqFin (2 * k - 1) (classMap hk s t a) p
  rw [hf, fiber_count]
  have hm : List.ofFn (fun i => (classMap hk s t i).val) = (labels s t).map (mergeN k) := by
    rw [← ofFn_run s t, List.map_ofFn]; congr 1; funext i; dsimp [classMap,merge,mergeN]
    split_ifs <;> rfl
  rw [hm, count_merge hk]; by_cases hp : p.val=0
  · have hlast : 2*k-1 < 2*k := by omega
    rw [if_pos hp, labels_count s t (⟨0,by omega⟩ : Fin (2*k)),
      labels_count s t (⟨2*k-1,hlast⟩ : Fin (2*k))]
    have heven : (2*k-1)%2 ≠ 0 := by omega
    simp only [classSize,hp,if_pos,rawSize,Fin.val_mk,Nat.zero_mod,ite_true,Nat.zero_div,if_neg heven]; congr 1; apply congrArg t; apply Fin.ext; simp; omega
  · simp only [if_neg hp, classSize, hp]; exact labels_count s t ⟨p.val,by have := p.isLt; omega⟩
open MMDLabels MMDGraphCompression
private theorem classSize_pos {k : ℕ} (hk : 2 ≤ k) (s t : Fin k → ℕ) (hs : ∀ i, 1 ≤ s i) (ht : ∀ i, 1 ≤ t i) (p : Fin (2*k-1)) : 1 ≤ classSize hk s t p := by
  unfold classSize rawSize
  split_ifs
  · have hh := hs ⟨0,by omega⟩; omega
  · apply hs
  · apply ht
private theorem classSize_base {k : ℕ} (hk : 2 ≤ k) (s t : Fin k → ℕ) (hs : ∀ i, 1 ≤ s i) (ht : ∀ i, 1 ≤ t i) : 2 ≤ classSize hk s t ⟨0,by omega⟩ := by
  simpa [classSize] using Nat.add_le_add (hs ⟨0,by omega⟩) (ht ⟨k-1,by omega⟩)
private theorem classSize_sum {k : ℕ} (hk : 2 ≤ k) (s t : Fin k → ℕ) : ∑ p, classSize hk s t p = (binaryString s t).length := by
  simp_rw [← classMap_count hk s t]; simpa using Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ : Finset (Fin (binaryString s t).length)) Finset.univ (classMap hk s t)
private theorem classSize_even {k : ℕ} (hk : 2 ≤ k) (s t : Fin k → ℕ) (i : Fin k) (hi : i.val ≠ 0) : classSize hk s t ⟨2*i.val,by have := i.isLt; omega⟩ = s i := by
  have hn : 2*i.val ≠ 0 := by omega
  simp [classSize, hn, rawSize]
private theorem classSize_odd {k : ℕ} (hk : 2 ≤ k) (s t : Fin k → ℕ) (i : Fin k) (hi : i.val ≠ k-1) : classSize hk s t ⟨2*i.val+1,by have := i.isLt; omega⟩ = t i := by
  simp only [classSize, Fin.val_mk, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false, rawSize,
    Nat.add_mod, Nat.mul_mod_right, Nat.zero_add, Nat.mod_succ, Nat.one_ne_zero]
  apply congrArg t; apply Fin.ext; simp only [Fin.val_mk]; omega
private theorem classSize_singletons {k : ℕ} (hk : 2 ≤ k) (s t : Fin k → ℕ) : (∀ p : Fin (2*k-1), p ≠ ⟨0,by omega⟩ → classSize hk s t p = 1) ↔ (∀ i : Fin k, i.val ≠ 0 → s i=1) ∧ (∀ i : Fin k, i.val ≠ k-1 → t i=1) := by
  constructor
  · intro h; constructor
    · intro i hi; rw [← classSize_even hk s t i hi]; apply h; intro he; have hv := congrArg Fin.val he; dsimp at hv; omega
    · intro i hi; rw [← classSize_odd hk s t i hi]; apply h; intro he; have hv := congrArg Fin.val he; dsimp at hv; omega
  · rintro ⟨hs,ht⟩ p hp
    have hv : p.val ≠ 0 := by intro h; exact hp (Fin.ext h)
    simp only [classSize, if_neg hv, rawSize, Fin.val_mk]
    split_ifs with he
    · apply hs; dsimp only [Fin.val_mk]; have := p.isLt; omega
    · apply ht; dsimp only [Fin.val_mk]; have := p.isLt; omega
end MMDCounts
namespace MMDLists
private theorem gamma_length {n k : ℕ} (hk : 1 ≤ k) (hn : 2*k ≤ n) {b : List Bool} (hb : Gamma n k b) : b.length = n := by
  obtain ⟨s,t,hs,hsi,ht,hti,hst,rfl⟩ := hb
  simp only [List.length_append, List.length_replicate, List.length_flatten,
    List.map_replicate, List.length_cons, List.length_nil, List.sum_replicate, Nat.nsmul_eq_mul]
  change s + (k-1)*2+t=n; omega
private theorem singleton_word (k : ℕ) (s t : Fin (k+1) → ℕ) (hs : ∀ i, i ≠ 0 → s i = 1) (ht : ∀ i, i ≠ Fin.last k → t i = 1) : binaryString s t = List.replicate (s 0) false ++ (List.replicate k [true,false]).flatten ++ List.replicate (t (Fin.last k)) true := by
  induction k with
  | zero => simp [binaryString, List.ofFn_succ]
  | succ k ih =>
    let ss : Fin (k+1) → ℕ := fun i => s i.succ; let tt : Fin (k+1) → ℕ := fun i => t i.succ
    have hss : ∀ i, i ≠ 0 → ss i = 1 := by
      intro i _; exact hs i.succ (by intro h; have hv := congrArg Fin.val h; simp at hv)
    have htt : ∀ i, i ≠ Fin.last k → tt i = 1 := by
      intro i hi; apply ht i.succ; intro h; apply hi; apply Fin.ext; have hv := congrArg Fin.val h; simp only [Fin.val_succ, Fin.val_last] at hv ⊢; omega
    have htail := ih ss tt hss htt; have hs1 : ss 0 = 1 := hs (Fin.succ 0) (by intro h; have hv := congrArg Fin.val h; simp at hv)
    have ht0 : t 0 = 1 := ht 0 (by intro h; have hv := congrArg Fin.val h; simp at hv)
    have hdecomp : binaryString s t = (List.replicate (s 0) false ++ List.replicate (t 0) true) ++
        binaryString ss tt := by
      simp only [binaryString, List.ofFn_succ, List.flatten_cons]; rfl
    rw [hdecomp, htail, hs1, ht0]; simp [tt, List.replicate_succ, List.flatten_cons, List.append_assoc]
private theorem singleton_runs_gamma (k n : ℕ) (s t : Fin (k+1) → ℕ) (hs : ∀ i, 1 ≤ s i) (ht : ∀ i, 1 ≤ t i) (hsi : ∀ i, i ≠ 0 → s i = 1) (hti : ∀ i, i ≠ Fin.last k → t i = 1) (hn : ∑ i, (s i+t i) = n) : Gamma n (k+1) (binaryString s t) := by
  have hS : ∑ i, s i = s 0+k := by
    rw [Fin.sum_univ_succ]
    have he : ∑ i : Fin k, s i.succ = k := by
      calc
        _ = ∑ _i : Fin k, (1 : ℕ) := Finset.sum_congr rfl (fun i _ => hsi i.succ (by simp))
        _ = k := by simp
    rw [he]
  have hT : ∑ i, t i = k+t (Fin.last k) := by
    rw [Fin.sum_univ_castSucc]
    have he : ∑ i : Fin k, t i.castSucc = k := by
      calc
        _ = ∑ _i : Fin k, (1 : ℕ) := Finset.sum_congr rfl (fun i _ => hti i.castSucc (by
          intro h; have hv := congrArg Fin.val h; simp only [Fin.val_castSucc, Fin.val_last] at hv; omega))
        _ = k := by simp
    rw [he]
  rw [Finset.sum_add_distrib, hS, hT] at hn; have hs0 := hs 0; have htl := ht (Fin.last k); refine ⟨s 0,t (Fin.last k),hs0,by omega,htl,by omega,by omega,?_⟩; simpa only [Nat.add_sub_cancel] using singleton_word k s t hsi hti
private theorem gamma_as_binary (k n : ℕ) (hn : 2*(k+1) ≤ n) (b : List Bool) (hb : Gamma n (k+1) b) : ∃ s t : Fin (k+1) → ℕ, (∀ i, 1 ≤ s i) ∧ (∀ i, 1 ≤ t i) ∧ (∑ i, (s i+t i)) = n ∧ binaryString s t = b ∧ (∀ i, i ≠ 0 → s i = 1) ∧ (∀ i, i ≠ Fin.last k → t i = 1) := by
  obtain ⟨u,v,hu,hui,hv,hvi,huv,hbword⟩ := hb; let s : Fin (k+1) → ℕ := fun i => if i=0 then u else 1; let t : Fin (k+1) → ℕ := fun i => if i=Fin.last k then v else 1
  have hs : ∀ i, 1 ≤ s i := by intro i; dsimp [s]; split_ifs <;> omega
  have ht : ∀ i, 1 ≤ t i := by intro i; dsimp [t]; split_ifs <;> omega
  have hsi : ∀ i, i ≠ 0 → s i = 1 := by exact fun i a => ite_eq_right a
  have hti : ∀ i, i ≠ Fin.last k → t i = 1 := by exact fun i a => ite_eq_right a
  have he : binaryString s t = b := by
    rw [singleton_word k s t hsi hti, hbword]; simp [s,t]
  refine ⟨s,t,hs,ht,?_,he,hsi,hti⟩; have hl := gamma_length (by omega : 1 ≤ k+1) hn
    (b := b) ⟨u,v,hu,hui,hv,hvi,huv,hbword⟩
  have hbl := MMDBoundary.binary_length s t; rw [he] at hbl; exact hbl.symm.trans hl
end MMDLists
namespace MMDGraphEnergy
open Matrix MMDVariational MMDStrictness MMDCore MMDCounts MMDLabels MMDGraphCompression
private theorem weights_pos {k : ℕ} (hk : 2 ≤ k) (s t : Fin k → ℕ) (hs : ∀ i, 1 ≤ s i) (ht : ∀ i, 1 ≤ t i) (p : Fin (2*k-1)) : 1 ≤ (fun p => (classSize hk s t p : ℝ)) p := by
  dsimp only; exact_mod_cast classSize_pos hk s t hs ht p
private theorem weights_base {k : ℕ} (hk : 2 ≤ k) (s t : Fin k → ℕ) (hs : ∀ i, 1 ≤ s i) (ht : ∀ i, 1 ≤ t i) : 1 < (fun p => (classSize hk s t p : ℝ)) ⟨0,by omega⟩ := by
  have hh : (2 : ℝ) ≤ (fun p => (classSize hk s t p : ℝ)) ⟨0,by omega⟩ := by
    dsimp only; exact_mod_cast classSize_base hk s t hs ht
  linarith
private theorem weights_sum {k n : ℕ} (hk : 2 ≤ k) (s t : Fin k → ℕ) (hn : ∑ i, (s i+t i)=n) : ∑ p, (fun p => (classSize hk s t p : ℝ)) p = (n : ℝ) := by
  have hh := classSize_sum hk s t; rw [MMDBoundary.binary_length,hn] at hh; dsimp only; exact_mod_cast hh
private theorem binary_energy {k n : ℕ} (hk : 2 ≤ k) (s t : Fin k → ℕ) (hn : ∑ i, (s i+t i)=n) (hnk : 2*k ≤ n) : energy (seidel (chainGraph (binaryString s t))) = (n-(2*k-1) : ℕ) + energy (compressed ((fun p => (classSize hk s t p : ℝ))) (core (2*k-1))-1) := by
  classical
  let c := classMap hk s t
  let U : Matrix (Fin (binaryString s t).length) (Fin (binaryString s t).length) ℝ :=
    diagonal (fun i => MMDCore.sign (Fin.castSucc (run s t i)))
  have hUU : U*U=1 := by
    rw [diagonal_mul_diagonal]; ext i j; simp only [diagonal_apply, Matrix.one_apply]
    split_ifs <;> simp [MMDCore.sign] <;> split_ifs <;> norm_num
  have hsw : U*(seidel (chainGraph (binaryString s t))+1)*U =
      ((1 : Matrix (Fin (2*k-1)) (Fin (2*k-1)) ℝ).submatrix c id)*core (2*k-1)*(((1 : Matrix (Fin (2*k-1)) (Fin (2*k-1)) ℝ).submatrix c id))ᵀ :=
    switched_compression hk (run s t) (run_monotone s t) (run_zero s t) (run_one s t)
  have he : energy (seidel (chainGraph (binaryString s t))) =
      energy (((1 : Matrix (Fin (2*k-1)) (Fin (2*k-1)) ℝ).submatrix c id)*core (2*k-1)*(((1 : Matrix (Fin (2*k-1)) (Fin (2*k-1)) ℝ).submatrix c id))ᵀ-1) := by
    rw [← MMDBoundary.energy_involution _ U hUU]; congr 1; rw [← hsw, mul_add, add_mul, mul_one, hUU]; abel
  have hgram : (((1 : Matrix (Fin (2*k-1)) (Fin (2*k-1)) ℝ).submatrix c id))ᵀ*((1 : Matrix (Fin (2*k-1)) (Fin (2*k-1)) ℝ).submatrix c id) = (diagonal (fun i => Real.sqrt ((((fun p => (classSize hk s t p : ℝ)))) i)))*(diagonal (fun i => Real.sqrt ((((fun p => (classSize hk s t p : ℝ)))) i))) := by
    rw [indicator_gram]; simp only [diagonal_mul_diagonal]; congr 1; funext p; rw [classMap_count]; exact (Real.mul_self_sqrt (by dsimp only; positivity : 0 ≤ (fun p => (classSize hk s t p : ℝ)) p)).symm
  rw [he, MMDCompression.shifted_compression_energy (by
    rw [MMDBoundary.binary_length,hn]; omega) _ _ _ hgram, MMDBoundary.binary_length, hn]
  rfl
private noncomputable def minimumEnergy (n k : ℕ) (hk : 2 ≤ k) : ℝ := (n-(2*k-1) : ℕ) + energy (compressed (weight ((n : ℝ)-(2*k-1 : ℕ)) ⟨0,by omega⟩) (core (2*k-1))-1)
private theorem binary_minimum {k n : ℕ} (hk : 2 ≤ k) (s t : Fin k → ℕ) (hs : ∀ i, 1 ≤ s i) (ht : ∀ i, 1 ≤ t i) (hn : ∑ i, (s i+t i)=n) (hnk : 2*k ≤ n) : minimumEnergy n k hk ≤ energy (seidel (chainGraph (binaryString s t))) ∧ (energy (seidel (chainGraph (binaryString s t))) = minimumEnergy n k hk ↔ (∀ i : Fin k, i.val ≠ 0 → s i=1) ∧ (∀ i : Fin k, i.val ≠ k-1 → t i=1)) := by
  have hh := MMDMatrixEnergy.core_energy_minimum (by omega : 3 ≤ 2*k-1)
    (by omega : (2*k-1)%2=1) ((fun p => (classSize hk s t p : ℝ))) (weights_pos hk s t hs ht) (weights_base hk s t hs ht)
  have ha : ∑ i, ((fun p => (classSize hk s t p : ℝ)) i-1) = (n : ℝ)-(2*k-1 : ℕ) := by
    rw [Finset.sum_sub_distrib, weights_sum hk s t hn]; simp
  rw [ha] at hh; rw [binary_energy hk s t hn hnk]; constructor
  · simpa only [minimumEnergy,add_comm] using add_le_add_left hh.1 (((n-(2*k-1) : ℕ)) : ℝ)
  · rw [minimumEnergy, add_left_cancel_iff, hh.2]; have he : (∀ i : Fin (2*k-1), i ≠ ⟨0,by omega⟩ → (fun p => (classSize hk s t p : ℝ)) i=1) ↔
        ∀ i : Fin (2*k-1), i ≠ ⟨0,by omega⟩ → classSize hk s t i=1 := by
      simp only [Nat.cast_eq_one]
    exact he.trans (classSize_singletons hk s t)
private theorem gamma_minimum {k n : ℕ} (hk : 2 ≤ k) (hnk : 2*k ≤ n) (b : List Bool) (hb : Gamma n k b) : energy (seidel (chainGraph b)) = minimumEnergy n k hk := by
  obtain ⟨l,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0); obtain ⟨s,t,hs,ht,hn,he,hsi,hti⟩ := MMDLists.gamma_as_binary l n hnk b hb; rw [← he]; apply (binary_minimum hk s t hs ht hn hnk).2.mpr; constructor
  · intro i hi; exact hsi i (by intro h; apply hi; exact congrArg Fin.val h)
  · intro i hi; apply hti i; intro h; apply hi; have hv := congrArg Fin.val h; simpa only [Fin.val_last,Nat.succ_sub_one] using hv
end MMDGraphEnergy
namespace MandalMehatariDasSeidel
open MMDGraphEnergy
theorem result : claim := by
  intro n k hk hnk s t hs ht hsum h hH; by_cases hk1 : k=1
  · subst k; exact MMDBoundary.result_one n s t hs ht hsum h hH
  have hk2 : 2 ≤ k := by omega
  have hlow := binary_minimum hk2 s t hs ht hsum hnk; have hHmin := gamma_minimum hk2 hnk h hH; constructor
  · rw [hHmin]; exact hlow.1
  · constructor
    · intro he; have hsingle := hlow.2.mp (he.trans hHmin); obtain ⟨l,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0); apply MMDLists.singleton_runs_gamma l n s t hs ht
      · intro i hi; apply hsingle.1 i; intro hv; exact hi (Fin.ext hv)
      · intro i hi; apply hsingle.2 i; intro hv; apply hi; apply Fin.ext; simpa only [Fin.val_last,Nat.succ_sub_one] using hv
      · exact hsum
    · intro hg; exact (gamma_minimum hk2 hnk (binaryString s t) hg).trans hHmin.symm
end MandalMehatariDasSeidel
end D5.S3.Combinatorics.Graph.KyFanGap.MandalMehatariDasSeidelMinimum
