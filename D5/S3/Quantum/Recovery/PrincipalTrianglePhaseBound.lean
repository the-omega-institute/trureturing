/- GID: D5/S3/Quantum/Recovery/PrincipalTrianglePhaseBound
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/PrincipalTrianglePhaseBound
   mirror-E: none(waiver:principal-triangle-phase-geometry)
   anchors: []
   utility: none
   digest: The principal same-quotient Gram model has a quantitative near-real error lower bound. -/

import D5.S3.Quantum.Recovery.PrincipalTrianglePhaseGeometry
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic.FinCases
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Positive Gram completion and the cross-entry modulus comparison imply a near-real error bound. -/

namespace D5.S3.Quantum.Recovery.PrincipalTrianglePhase

section

namespace RTPhaseCube
open scoped InnerProductSpace ComplexOrder
set_option maxHeartbeats 1600000
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem two_basis_contraction {v w : Fin 2 → E} (hv : Orthonormal ℂ v) (hw : Orthonormal ℂ w)
    (x y : ℂ) :
    ‖⟪v 0,w 0⟫_ℂ * x + ⟪v 0,w 1⟫_ℂ * y‖ ^ 2 +
    ‖⟪v 1,w 0⟫_ℂ * x + ⟪v 1,w 1⟫_ℂ * y‖ ^ 2 ≤ ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
  have horth : ⟪x • w 0,y • w 1⟫_ℂ = 0 := by
    rw [inner_smul_left, inner_smul_right, (orthonormal_iff_ite.mp hw)]
    norm_num
  have hnorm : ‖x • w 0 + y • w 1‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
    simp only [pow_two]
    rw [norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth]
    simp [norm_smul, hw.norm_eq_one]
  have h := hv.sum_inner_products_le (x • w 0 + y • w 1) (s := Finset.univ)
  rw [hnorm, Fin.sum_univ_two] at h
  simpa only [inner_add_right, inner_smul_right, mul_comm] using h

theorem triangle_gram_det {u v w : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    0 ≤ (Matrix.det !![(1 : ℂ), ⟪u,v⟫_ℂ, ⟪u,w⟫_ℂ;
        star (⟪u,v⟫_ℂ), 1, ⟪v,w⟫_ℂ;
        star (⟪u,w⟫_ℂ), star (⟪v,w⟫_ℂ), 1]).re := by
  let x : Fin 3 → E := ![u,v,w]
  have he : Matrix.gram ℂ x =
        !![(1 : ℂ), ⟪u,v⟫_ℂ, ⟪u,w⟫_ℂ;
        star (⟪u,v⟫_ℂ), 1, ⟪v,w⟫_ℂ;
        star (⟪u,w⟫_ℂ), star (⟪v,w⟫_ℂ), 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [x, inner_conj_symm, inner_self_eq_norm_sq_to_K, hu, hv, hw]
  have h := (Matrix.posSemidef_gram ℂ x).det_nonneg
  rw [he] at h
  exact (Complex.nonneg_iff.mp h).1

/-- Fully proved at the model of three orthonormal pairs in a complex
inner-product space. Native RT's completion into this model is a separate
problem-specific step. -/
theorem orthonormal_pairs_phase
    (m : ℝ) (hm : 1 / 2 < m)
    {u v w : Fin 2 → E}
    (hu : Orthonormal ℂ u) (hv : Orthonormal ℂ v) (hw : Orthonormal ℂ w)
    (ha : ∀ i j, m ≤ ‖⟪u i,v j⟫_ℂ‖) (hb : ∀ j k, m ≤ ‖⟪v j,w k⟫_ℂ‖)
    (hc : ∀ i k, m ≤ ‖⟪u i,w k⟫_ℂ‖) :
    ∃ i j k, Real.sin (cutoffAngle m) ≤
      |Real.sin (Complex.arg (triangleProduct ⟪u i,v j⟫_ℂ ⟪v j,w k⟫_ℂ ⟪u i,w k⟫_ℂ))| := by
  have upper : ‖⟪u 0,v 0⟫_ℂ‖ ≤ 1 := by
    simpa [hu.norm_eq_one, hv.norm_eq_one] using (norm_inner_le_norm (𝕜 := ℂ) (u 0) (v 0))
  have hm1 : m ≤ 1 := (ha 0 0).trans upper
  exact three_fibre_complex_phase m hm hm1 _ _ _ ha hb hc
    (two_basis_contraction hu hv) (two_basis_contraction hu hw)
    (fun i j k => triangle_gram_det (hu.norm_eq_one i) (hv.norm_eq_one j) (hw.norm_eq_one k))

theorem orthonormal_pairs_imag
    (m : ℝ) (hm : 1 / 2 < m)
    {u v w : Fin 2 → E}
    (hu : Orthonormal ℂ u) (hv : Orthonormal ℂ v) (hw : Orthonormal ℂ w)
    (ha : ∀ i j, m ≤ ‖⟪u i,v j⟫_ℂ‖) (hb : ∀ j k, m ≤ ‖⟪v j,w k⟫_ℂ‖)
    (hc : ∀ i k, m ≤ ‖⟪u i,w k⟫_ℂ‖) :
    ∃ i j k, m ^ 3 * Real.sin (cutoffAngle m) ≤
      |(triangleProduct ⟪u i,v j⟫_ℂ ⟪v j,w k⟫_ℂ ⟪u i,w k⟫_ℂ).im| := by
  obtain ⟨i,j,k,h⟩ := orthonormal_pairs_phase m hm hu hv hw ha hb hc
  refine ⟨i,j,k,?_⟩
  let p := triangleProduct ⟪u i,v j⟫_ℂ ⟪v j,w k⟫_ℂ ⟪u i,w k⟫_ℂ
  change m ^ 3 * Real.sin (cutoffAngle m) ≤ |p.im|
  change Real.sin (cutoffAngle m) ≤ |Real.sin p.arg| at h
  have hm0 : 0 ≤ m := by linarith
  have hprod : m ^ 3 ≤ ‖p‖ := by
    simp only [p, triangleProduct, Complex.norm_mul, norm_star, pow_succ, pow_zero, one_mul]
    exact
      (mul_le_mul (mul_le_mul (ha i j) (hb j k) hm0 (norm_nonneg _))
        (hc i k) hm0 (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
  have hs : 0 ≤ Real.sin (cutoffAngle m) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (cutoff_nonneg m)
      ((min_le_right _ _ : cutoffAngle m ≤ Real.pi / 4).trans (by linarith [Real.pi_pos]))
  rw [← Complex.norm_mul_sin_arg p, abs_mul, abs_of_nonneg (norm_nonneg p)]
  exact mul_le_mul hprod h hs (norm_nonneg p)

end RTPhaseCube

end

section

open scoped Matrix ComplexOrder BigOperators
namespace RTPhaseCube

variable {F I : Type*} [Fintype F] [Fintype I] [DecidableEq F] [DecidableEq I]

def fibreBlock (H : Matrix (F × I) (F × I) ℂ) (f : F) : Matrix I I ℂ :=
  H.submatrix (f, ·) (f, ·)

def completeFibres (H : Matrix (F × I) (F × I) ℂ) : Matrix (F × I) (F × I) ℂ :=
  fun p q => if p.1 = q.1 then (1 : Matrix I I ℂ) p.2 q.2 else H p q

omit [Fintype F] [Fintype I] in
@[simp] theorem completeFibres_same (H : Matrix (F × I) (F × I) ℂ) (f : F) (i j : I) :
    completeFibres H (f,i) (f,j) = (1 : Matrix I I ℂ) i j := by
  simp [completeFibres]

omit [Fintype F] [Fintype I] in
theorem completeFibres_cross (H : Matrix (F × I) (F × I) ℂ) (f g : F) (i j : I)
    (h : f ≠ g) : completeFibres H (f,i) (g,j) = H (f,i) (g,j) := by
  simp [completeFibres, h]

def fibreDefect (H : Matrix (F × I) (F × I) ℂ) (f : F) : Matrix (F × I) (F × I) ℂ :=
  fun p q => if p.1 = f ∧ q.1 = f then ((1 : Matrix I I ℂ) - fibreBlock H f) p.2 q.2 else 0

theorem fibreDefect_posSemidef (H : Matrix (F × I) (F × I) ℂ) (f : F)
    (hf : ((1 : Matrix I I ℂ) - fibreBlock H f).PosSemidef) :
    (fibreDefect H f).PosSemidef := by
  let D : Matrix (F × I) (F × I) ℂ :=
    Matrix.diagonal fun p => if p.1 = f then 1 else 0
  have h := (hf.submatrix (Prod.snd : F × I → I)).conjTranspose_mul_mul_same D
  convert h using 1
  ext p q
  by_cases hp : p.1 = f <;> by_cases hq : q.1 = f <;>
    simp [D, fibreDefect, hp, hq, Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem completeFibres_posSemidef (H : Matrix (F × I) (F × I) ℂ)
    (hH : H.PosSemidef) (hf : ∀ f : F, ((1 : Matrix I I ℂ) - fibreBlock H f).PosSemidef) :
    (completeFibres H).PosSemidef := by
  have heq : completeFibres H = H + ∑ f, fibreDefect H f := by
    ext ⟨p,i⟩ ⟨q,j⟩
    by_cases hpq : p = q
    · subst q
      simp [completeFibres, fibreDefect, fibreBlock, Matrix.sum_apply]
    · simp [completeFibres, fibreDefect, Matrix.sum_apply, hpq, show ∀ f, ¬ (p = f ∧ q = f) from
        fun f ⟨hp,hq⟩ => hpq (hp.trans hq.symm)]
  rw [heq]
  exact hH.add (Matrix.posSemidef_sum Finset.univ (fun f _ => fibreDefect_posSemidef H f (hf f)))

end RTPhaseCube

end

section

namespace RTCompletion
open Matrix
open scoped MatrixOrder InnerProductSpace ComplexOrder
set_option maxHeartbeats 1000000

/-- A PSD matrix is represented by column vectors in a genuine Hermitian space. -/
theorem column_gram {n : Type*} [Fintype n] [DecidableEq n]
    {H : Matrix n n ℂ} (h : H.PosSemidef) :
    ∃ v : n → EuclideanSpace ℂ n, ∀ i j, ⟪v i, v j⟫_ℂ = H i j := by
  obtain ⟨A,hA⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp h.nonneg
  refine ⟨fun i => WithLp.toLp 2 (fun k => A k i), fun i j => ?_⟩
  rw [hA, Matrix.star_eq_conjTranspose, Matrix.mul_apply]
  simp only [PiLp.inner_apply, Matrix.conjTranspose_apply, RCLike.inner_apply',
    starRingEnd_apply]

/-- Transfer the triangle-phase obstruction back to the entries of a
positive-semidefinite six-point Gram with orthonormal fibre blocks. -/
theorem psd_gram_phase
    {H : Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℂ}
    (h : H.PosSemidef) (hf : ∀ i u v, H (i,u) (i,v) = if u = v then 1 else 0)
    (m : ℝ) (hm : 1/2 < m)
    (cross : ∀ i j : Fin 3, i ≠ j → ∀ u v : Fin 2, m ≤ ‖H (i,u) (j,v)‖) :
    ∃ u v w : Fin 2, m^3 * Real.sin (RTPhaseCube.cutoffAngle m) ≤
      |(RTPhaseCube.triangleProduct (H (0,u) (1,v)) (H (1,v) (2,w)) (H (0,u) (2,w))).im| := by
  obtain ⟨x, hx⟩ := column_gram h
  have hor (i : Fin 3) : Orthonormal ℂ (fun t : Fin 2 => x (i,t)) :=
    orthonormal_iff_ite.mpr (fun u v => (hx (i,u) (i,v)).trans (hf i u v))
  have h01 (u v : Fin 2) : m ≤ ‖⟪x (0,u), x (1,v)⟫_ℂ‖ := by
    rw [hx]
    exact cross 0 1 (by decide) u v
  have h12 (v w : Fin 2) : m ≤ ‖⟪x (1,v), x (2,w)⟫_ℂ‖ := by
    rw [hx]
    exact cross 1 2 (by decide) v w
  have h02 (u w : Fin 2) : m ≤ ‖⟪x (0,u), x (2,w)⟫_ℂ‖ := by
    rw [hx]
    exact cross 0 2 (by decide) u w
  obtain ⟨u,v,w,hh⟩ := RTPhaseCube.orthonormal_pairs_imag m hm (hor 0) (hor 1) (hor 2) h01 h12 h02
  exact ⟨u,v,w,by simpa only [hx] using hh⟩

end RTCompletion

end

section

namespace RTCompletion
open scoped ComplexOrder InnerProductSpace
abbrev Coord := Fin 3 × Fin 2

theorem correlation_entry_norm_le_one {n : Type*} [Fintype n] [DecidableEq n]
    {R : Matrix n n ℂ} (h : R.PosSemidef) (diag : ∀ i, R i i = 1) (i j : n) :
    ‖R i j‖ ≤ 1 := by
  obtain ⟨v,hv⟩ := column_gram h
  have un (k : n) : ‖v k‖ = 1 := by
    have z := congrArg Complex.re ((hv k k).trans (diag k))
    rw [show (⟪v k, v k⟫_ℂ).re = ‖v k‖^2 from
      inner_self_eq_norm_sq (𝕜 := ℂ) (v k), Complex.one_re] at z
    nlinarith [norm_nonneg (v k)]
  calc
    ‖R i j‖ = ‖⟪v i,v j⟫_ℂ‖ := by rw [hv]
    _ ≤ ‖v i‖ * ‖v j‖ := norm_inner_le_norm _ _
    _ = 1 := by rw [un,un,one_mul]

/-- The lower overlap bound in RT IV (116.8), derived directly from the
original matrix-unit inequality and the principal same-correlation quotient. -/
theorem quotient_overlap_floor {δ : ℝ} (hd : δ < 1/4) {u r : ℂ}
    (hr : ‖r‖ ≤ 1) (hw : ‖(1 / 2 : ℂ) - (u * star r) * u‖ ≤ δ) :
    Real.sqrt (1 / 2 - δ) ≤ ‖u‖ := by
  have hhalf : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num [norm_div]
  have ht := norm_le_norm_add_norm_sub ((u * star r) * u) (1/2 : ℂ)
  rw [hhalf, Complex.norm_mul, Complex.norm_mul, norm_star, norm_sub_rev] at ht
  have hb := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hr (norm_nonneg u)) (norm_nonneg u)
  have hs : (Real.sqrt (1 / 2 - δ))^2 = 1 / 2 - δ := Real.sq_sqrt (by linarith)
  by_contra! bad
  have hp := mul_pos (sub_pos.mpr bad) (show 0 < Real.sqrt (1 / 2 - δ) + ‖u‖ by
    linarith [norm_nonneg u])
  nlinarith

noncomputable def floor (δ : ℝ) : ℝ := Real.sqrt (1 / 2 - δ)

/-- The matrix-unit error yields an overlap floor from cross dominance alone. -/
theorem overlap_floor_of_cross_dominance {δ : ℝ} (hd : δ < 1/4) {g h : ℂ}
    (hdom : ‖g‖ ≤ ‖h‖) (hw : ‖(1 / 2 : ℂ) - g * h‖ ≤ δ) :
    Real.sqrt (1 / 2 - δ) ≤ ‖h‖ := by
  have hhalf : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num [norm_div]
  have ht := norm_le_norm_add_norm_sub (g * h) (1/2 : ℂ)
  rw [hhalf, Complex.norm_mul, norm_sub_rev] at ht
  have hb := mul_le_mul_of_nonneg_right hdom (norm_nonneg h)
  have hs : (Real.sqrt (1 / 2 - δ))^2 = 1 / 2 - δ := Real.sq_sqrt (by linarith)
  by_contra! bad
  have hp := mul_pos (sub_pos.mpr bad) (show 0 < Real.sqrt (1 / 2 - δ) + ‖h‖ by
    linarith [norm_nonneg h])
  nlinarith

/-- Cross dominance and the matrix-unit error witness force a quantitative triangle phase gap. -/
theorem triangle_imag_of_cross_dominance
    (G H : Matrix Coord Coord ℂ)
    (hH : H.PosSemidef)
    (defect : ∀ f : Fin 3, ((1 : Matrix (Fin 2) (Fin 2) ℂ) - RTPhaseCube.fibreBlock H f).PosSemidef)
    (dominates : ∀ i j : Fin 3, i ≠ j → ∀ u v : Fin 2,
      ‖G (i,u) (j,v)‖ ≤ ‖H (i,u) (j,v)‖)
    (δ : ℝ) (hd : δ < 1/4)
    (witness : ∀ i j : Fin 3, i ≠ j → ∀ u v : Fin 2,
      ‖(1/2 : ℂ) - G (i,u) (j,v) * H (i,u) (j,v)‖ ≤ δ) :
    ∃ u v w : Fin 2, (floor δ)^3 * Real.sin (RTPhaseCube.cutoffAngle (floor δ)) ≤
      |(RTPhaseCube.triangleProduct (H (0,u) (1,v)) (H (1,v) (2,w)) (H (0,u) (2,w))).im| := by
  have hm : (1/2 : ℝ) < floor δ := by
    have hq : (floor δ)^2 = 1/2-δ := Real.sq_sqrt (by linarith)
    have hn : 0 ≤ floor δ := Real.sqrt_nonneg _
    by_contra! he
    nlinarith [mul_nonneg (sub_nonneg.mpr he) (show 0 ≤ 1/2 + floor δ by positivity)]
  have hh := RTPhaseCube.completeFibres_posSemidef H hH defect
  have hi (f : Fin 3) (u v : Fin 2) :
      RTPhaseCube.completeFibres H (f,u) (f,v) = if u = v then 1 else 0 := by
    rw [RTPhaseCube.completeFibres_same, Matrix.one_apply]
  have hcross (i j : Fin 3) (hij : i ≠ j) (u v : Fin 2) :
      floor δ ≤ ‖RTPhaseCube.completeFibres H (i,u) (j,v)‖ := by
    rw [RTPhaseCube.completeFibres_cross H i j u v hij]
    exact overlap_floor_of_cross_dominance hd (dominates i j hij u v) (witness i j hij u v)
  obtain ⟨u,v,w,h⟩ := psd_gram_phase hh hi (floor δ) hm hcross
  rw [RTPhaseCube.completeFibres_cross H 0 1 u v (by decide),
      RTPhaseCube.completeFibres_cross H 1 2 v w (by decide),
      RTPhaseCube.completeFibres_cross H 0 2 u w (by decide)] at h
  exact ⟨u,v,w,h⟩

/-- Verified end-to-end from the Gram, the actual common quotient, and
the matrix-unit bound to an explicit non-real triangle. The channel-to-
matrix-unit norm witness is an input, not a theorem about Lean channels. -/
theorem same_quotient_triangle_imag
    (G H R : Matrix Coord Coord ℂ)
    (hH : H.PosSemidef)
    (defect : ∀ f : Fin 3, ((1 : Matrix (Fin 2) (Fin 2) ℂ) - RTPhaseCube.fibreBlock H f).PosSemidef)
    (hR : R.PosSemidef) (rdiag : ∀ i, R i i = 1)
    (quot : ∀ p q, G p q = H p q * star (R p q))
    (δ : ℝ) (hd : δ < 1/4)
    (witness : ∀ i j : Fin 3, i ≠ j → ∀ u v : Fin 2,
      ‖(1/2 : ℂ) - G (i,u) (j,v) * H (i,u) (j,v)‖ ≤ δ) :
    ∃ u v w : Fin 2, (floor δ)^3 * Real.sin (RTPhaseCube.cutoffAngle (floor δ)) ≤
      |(RTPhaseCube.triangleProduct (H (0,u) (1,v)) (H (1,v) (2,w)) (H (0,u) (2,w))).im| := by
  have dominates (i j : Fin 3) (_ : i ≠ j) (u v : Fin 2) :
      ‖G (i,u) (j,v)‖ ≤ ‖H (i,u) (j,v)‖ := by
    rw [quot, Complex.norm_mul, norm_star]
    calc
      _ ≤ ‖H (i,u) (j,v)‖ * 1 :=
        mul_le_mul_of_nonneg_left (correlation_entry_norm_le_one hR rdiag _ _) (norm_nonneg _)
      _ = _ := mul_one _
  exact triangle_imag_of_cross_dominance G H hH defect dominates δ hd witness

end RTCompletion

end

section

namespace RTCompletion
open Real

theorem quantitative_gap_positive {δ : ℝ} (hd : δ < 1/4) :
    0 < (floor δ)^3 * sin (RTPhaseCube.cutoffAngle (floor δ)) := by
  have hq : (floor δ)^2 = 1/2-δ := Real.sq_sqrt (by linarith)
  have hn : 0 ≤ floor δ := Real.sqrt_nonneg _
  have hm : (1/2 : ℝ) < floor δ := by
    by_contra! he
    nlinarith [mul_nonneg (sub_nonneg.mpr he) (show 0 ≤ 1/2 + floor δ by positivity)]
  have hm0 : 0 < floor δ := by linarith
  have ht : 0 < RTPhaseCube.baseAngle (floor δ) :=
    Real.arccos_pos.mpr ((div_lt_iff₀ (show 0 < 2*floor δ by positivity)).mpr (by linarith))
  have hg : 0 < RTPhaseCube.cutoffAngle (floor δ) :=
    lt_min (mul_pos (by norm_num) ht) (by positivity)
  have hπ : RTPhaseCube.cutoffAngle (floor δ) < π :=
    (min_le_right _ _ : RTPhaseCube.cutoffAngle (floor δ) ≤ π/4).trans_lt (by linarith [pi_pos])
  exact mul_pos (pow_pos hm0 _) (Real.sin_pos_of_pos_of_lt_pi hg hπ)

end RTCompletion

end

section

namespace RTCompletion
open Real
set_option maxHeartbeats 1200000

/-- A closed polynomial certificate for the squared phase gap. It removes
the inverse trigonometric function from comparisons with an external bound. -/
theorem squared_gap_lower {m : ℝ} (hm : 1/2 < m) :
    (27/128) * (m^2-1/4) ≤ (m^3*sin (RTPhaseCube.cutoffAngle m))^2 := by
  have hm0 : 0 < m := by linarith
  have hm2 : 1/4 ≤ m^2 := by nlinarith
  have hd : 0 < 2*m := by positivity
  have hu : 1/(2*m) ≤ 1 := (div_le_iff₀ hd).mpr (by linarith)
  have hl : -1 ≤ 1/(2*m) := by
    have h : 0 ≤ (1:ℝ)/(2*m) := by positivity
    linarith
  unfold RTPhaseCube.cutoffAngle
  rcases le_or_gt (2 * RTPhaseCube.baseAngle m) (π/4) with h | h
  · rw [min_eq_left h]
    have he : (m^3*sin (2*RTPhaseCube.baseAngle m))^2 = m^2*(m^2-1/4) := by
      rw [mul_pow, sin_two_mul, mul_pow, mul_pow, RTPhaseCube.baseAngle, cos_arccos hl hu]
      have hx := sin_sq_add_cos_sq (arccos (1/(2*m)))
      rw [cos_arccos hl hu] at hx
      have hb : sin (arccos (1/(2*m)))^2 = 1-(1/(2*m))^2 := by linarith
      rw [hb]
      field_simp [ne_of_gt hm0]; ring
    rw [he]
    exact mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  · rw [min_eq_right h.le]
    have he : (m^3 * sin (π/4))^2 = m^6/2 := by
      rw [sin_pi_div_four, mul_pow, div_pow, Real.sq_sqrt (by norm_num)]
      ring
    rw [he]
    have hf : 64 * m^6 - 27*(m^2-1/4) =
        ((m^2-1/4)+1) * (8*(m^2-1/4)-1)^2 := by ring
    have hh : 0 ≤ ((m^2-1/4)+1) * (8*(m^2-1/4)-1)^2 := by
      exact mul_nonneg (by linarith) (sq_nonneg _)
    linarith

theorem squared_gap_delta {δ : ℝ} (hd : δ < 1/4) :
    (27/128) * (1/4-δ) ≤ ((floor δ)^3*sin (RTPhaseCube.cutoffAngle (floor δ)))^2 := by
  have hq : (floor δ)^2 = 1/2-δ := Real.sq_sqrt (by linarith)
  have hn : 0 ≤ floor δ := Real.sqrt_nonneg _
  have hm : (1/2 : ℝ) < floor δ := by
    by_contra! he
    nlinarith [mul_nonneg (sub_nonneg.mpr he) (show 0 ≤ 1/2 + floor δ by positivity)]
  have h := squared_gap_lower hm
  rwa [hq, show (1/2 - δ - 1/4 : ℝ) = 1/4-δ by ring] at h

end RTCompletion

namespace RTCompletion
open scoped ComplexOrder

/-- Small triangle imaginaries and cross dominance imply a near-quarter lower bound. -/
theorem near_real_error_lower_of_cross_dominance
    (G H : Matrix Coord Coord ℂ)
    (hH : H.PosSemidef)
    (defect : ∀ f : Fin 3, ((1 : Matrix (Fin 2) (Fin 2) ℂ) - RTPhaseCube.fibreBlock H f).PosSemidef)
    (dominates : ∀ i j : Fin 3, i ≠ j → ∀ u v : Fin 2,
      ‖G (i,u) (j,v)‖ ≤ ‖H (i,u) (j,v)‖)
    (δ η : ℝ)
    (witness : ∀ i j : Fin 3, i ≠ j → ∀ u v : Fin 2,
      ‖(1/2 : ℂ) - G (i,u) (j,v) * H (i,u) (j,v)‖ ≤ δ)
    (close : ∀ u v w : Fin 2,
      |(RTPhaseCube.triangleProduct (H (0,u) (1,v)) (H (1,v) (2,w)) (H (0,u) (2,w))).im| ≤ η) :
    1/4 - (128/27) * η^2 ≤ δ := by
  rcases lt_or_ge δ (1/4) with hd | hd
  · obtain ⟨u,v,w,h⟩ := triangle_imag_of_cross_dominance G H hH defect dominates δ hd witness
    have hn := (quantitative_gap_positive hd).le
    have hl := h.trans (close u v w)
    have hs :
        ((floor δ)^3 * Real.sin (RTPhaseCube.cutoffAngle (floor δ)))^2 ≤ η^2 :=
      pow_le_pow_left₀ hn hl 2
    linarith [squared_gap_delta hd]
  · nlinarith [sq_nonneg η]

/-- Approximate-real obstruction at the same-quotient interface: small
absolute triangle imaginaries imply a quantitative near-quarter lower bound. -/
theorem near_real_error_lower
    (G H R : Matrix Coord Coord ℂ)
    (hH : H.PosSemidef)
    (defect : ∀ f : Fin 3, ((1 : Matrix (Fin 2) (Fin 2) ℂ) - RTPhaseCube.fibreBlock H f).PosSemidef)
    (hR : R.PosSemidef) (rdiag : ∀ i, R i i = 1)
    (quot : ∀ p q, G p q = H p q * star (R p q))
    (δ η : ℝ)
    (witness : ∀ i j : Fin 3, i ≠ j → ∀ u v : Fin 2,
      ‖(1/2 : ℂ) - G (i,u) (j,v) * H (i,u) (j,v)‖ ≤ δ)
    (close : ∀ u v w : Fin 2,
      |(RTPhaseCube.triangleProduct (H (0,u) (1,v)) (H (1,v) (2,w)) (H (0,u) (2,w))).im| ≤ η) :
    1/4 - (128/27) * η^2 ≤ δ := by
  have dominates (i j : Fin 3) (_ : i ≠ j) (u v : Fin 2) :
      ‖G (i,u) (j,v)‖ ≤ ‖H (i,u) (j,v)‖ := by
    rw [quot, Complex.norm_mul, norm_star]
    calc
      _ ≤ ‖H (i,u) (j,v)‖ * 1 :=
        mul_le_mul_of_nonneg_left (correlation_entry_norm_le_one hR rdiag _ _) (norm_nonneg _)
      _ = _ := mul_one _
  exact near_real_error_lower_of_cross_dominance G H hH defect dominates δ η witness close

end RTCompletion

end

end D5.S3.Quantum.Recovery.PrincipalTrianglePhase
