/- GID: D5/S3/Observer/Linear/GainRayWorld
   generality: G
   mirror-B: D5/B/S3/Observer/Linear/GainRayWorld
   mirror-E: none(waiver:whole-polynomial-world-semantics)
   anchors: [mathlib/module/Mathlib.Algebra.Polynomial.OfFn, mathlib/module/Mathlib.LinearAlgebra.Matrix.Rank]
   utility: none
   digest: Whole nonzero polynomial worlds have exact ordinary coefficient and positive source coordinates. -/

import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
open scoped Matrix
namespace D5.S3.Observer.Linear.GainRay

abbrev Mat := Matrix (Fin 2) (Fin 2) ℝ
abbrev Coeff (d : ℕ) := Fin (d + 1) → ℝ

def LegalSource (P : Mat) : Prop :=
  (∀ i j, 0 < P i j) ∧ P.rank = 1 ∧ Matrix.trace P = 1

def gain (d : ℕ) (β : Coeff d) : Polynomial ℝ := Polynomial.ofFn (d + 1) β

/-- No condition is imposed on an individual coefficient or sample. -/
structure World (d : ℕ) where
  source : Mat
  legal : LegalSource source
  coeff : Coeff d
  nonzero : coeff ≠ 0
  drift : ℝ

structure PolynomialWorld (d : ℕ) where
  source : Mat
  legal : LegalSource source
  polynomial : Polynomial ℝ
  degree_le : polynomial.natDegree ≤ d
  nonzero : polynomial ≠ 0
  drift : ℝ

/-- Ordinary coefficients, with no actual-degree or root promise. -/
def coefficientEquiv (d : ℕ) : Coeff d ≃ {p : Polynomial ℝ // p.natDegree ≤ d} where
  toFun β := ⟨gain d β, Nat.le_of_lt_succ (Polynomial.ofFn_natDegree_lt (by omega) β)⟩
  invFun p := Polynomial.toFn (d + 1) p.1
  left_inv β := Polynomial.toFn_comp_ofFn_eq_id _ β
  right_inv p := Subtype.ext
    (Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt (by omega : p.1.natDegree < d + 1))

def worldEquiv (d : ℕ) : World d ≃ PolynomialWorld d where
  toFun W := ⟨W.source, W.legal, gain d W.coeff, (coefficientEquiv d W.coeff).2,
    fun h => W.nonzero ((Polynomial.injective_ofFn (d + 1)) (h.trans (by simp))), W.drift⟩
  invFun W := ⟨W.source, W.legal, Polynomial.toFn (d + 1) W.polynomial,
    by
      intro h
      have hp := Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt
        (by omega : W.polynomial.natDegree < d + 1)
      rw [h, map_zero] at hp
      exact W.nonzero hp.symm,
    W.drift⟩
  left_inv W := by cases W; simp [Polynomial.toFn_comp_ofFn_eq_id]
  right_inv W := by
    have hp := Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt
      (by omega : W.polynomial.natDegree < d + 1)
    cases W
    simp_all [gain]

/-- The full positive chart of normalized sources. -/
def sourceChart (x r : ℝ) : Mat := (1 + x * r)⁻¹ • !![1, r; x, x * r]

private theorem chart_rank (x r : ℝ) (hx : 0 < x) (hr : 0 < r) :
    (sourceChart x r).rank = 1 := by
  have hden : 0 < 1 + x * r := by positivity
  have houter : sourceChart x r = Matrix.vecMulVec
      ![(1 + x * r)⁻¹, x / (1 + x * r)] ![1, r] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sourceChart, Matrix.vecMulVec, div_eq_mul_inv] <;> ring
  have hle : (sourceChart x r).rank ≤ 1 := by
    rw [houter]
    exact Matrix.rank_vecMulVec_le _ _
  have hpos : 0 < (sourceChart x r).rank := by
    change 0 < Module.finrank ℝ (LinearMap.range (sourceChart x r).mulVecLin)
    apply Module.finrank_pos_iff_exists_ne_zero.mpr
    refine ⟨⟨(sourceChart x r).mulVec ![1, 0], ⟨![1, 0], rfl⟩⟩, ?_⟩
    intro h
    have he := congrArg (fun v : LinearMap.range (sourceChart x r).mulVecLin => v.1 0) h
    have hn : (1 + x * r)⁻¹ ≠ 0 := inv_ne_zero (ne_of_gt hden)
    exact hn (by simpa [sourceChart, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using he)
  omega

theorem source_chart_legal (x r : ℝ) (hx : 0 < x) (hr : 0 < r) :
    LegalSource (sourceChart x r) := by
  have hd : 0 < 1 + x * r := by positivity
  refine ⟨?_, chart_rank x r hx hr, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [sourceChart] <;> positivity
  · simp [sourceChart, Matrix.trace, Fin.sum_univ_two]
    field_simp

/-- Every original legal source occurs, with its original matrix unchanged. -/
theorem source_chart_exact (P : Mat) (hP : LegalSource P) :
    ∃ x r : ℝ, 0 < x ∧ 0 < r ∧ P = sourceChart x r ∧
      x = P 1 0 / P 0 0 ∧ r = P 0 1 / P 0 0 := by
  have ha := hP.1 0 0
  have hb := hP.1 0 1
  have hc := hP.1 1 0
  have hdet : P.det = 0 := by
    by_contra hn
    have he := Matrix.rank_of_det_ne_zero hn
    rw [hP.2.1] at he
    norm_num at he
  have ht : P 0 0 + P 1 1 = 1 := by
    simpa [Matrix.trace, Fin.sum_univ_two] using hP.2.2
  have hd : P 0 0 * P 1 1 = P 0 1 * P 1 0 := by
    simpa [Matrix.det_fin_two, sub_eq_zero] using hdet
  refine ⟨P 1 0 / P 0 0, P 0 1 / P 0 0, div_pos hc ha, div_pos hb ha, ?_, rfl, rfl⟩
  have hz : P 0 0 ≠ 0 := ne_of_gt ha
  have hinv : (1 + (P 1 0 / P 0 0) * (P 0 1 / P 0 0))⁻¹ = P 0 0 := by
    apply inv_eq_of_mul_eq_one_right
    field_simp
    nlinarith
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sourceChart, hinv]
  · field_simp
  · field_simp
  · field_simp
    nlinarith

/-- Normalization changes gain by the positive trace, without changing any read. -/
theorem normalization_read (R A : Mat) (G δ : ℝ) (hR : Matrix.trace R ≠ 0) :
    (Matrix.trace R * G) * Matrix.trace (A * ((Matrix.trace R)⁻¹ • R)) + δ =
      G * Matrix.trace (A * R) + δ := by
  rw [Matrix.mul_smul, Matrix.trace_smul]
  simp only [smul_eq_mul]
  field_simp

#print axioms source_chart_exact
end D5.S3.Observer.Linear.GainRay
