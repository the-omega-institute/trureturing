import D5.S3.Geometry.Hyperideal.LengthGramMetricSegments
import Mathlib.Analysis.SpecialFunctions.Arcosh

noncomputable section
set_option autoImplicit false
open Set
open scoped Matrix
open D5.S3.Geometry.Hyperideal.LengthGramBody
open D5.S3.Geometry.Hyperideal.LengthGramMetricSegments
open D5.S3.Geometry.Hyperideal.LengthGramPolytope
open D5.S3.Geometry.HyperbolicUpperHalfSpace

namespace CFMPOriginalSixEdgeLengths435Transient

-- The original two cut endpoints, with their actual radial scales.
theorem two_endpoint_distance
    (X Y : Fin 4 → ℝ) (c a b : ℝ) (hc : 1 < c)
    (hX : lorentz X X = 1) (hY : lorentz Y Y = 1)
    (hXY : lorentz X Y = -c)
    (p q : HyperbolicThreeSpace) (ha : 0 < a) (hb : 0 < b)
    (hp : (c/(1+c)) • X + (1/(1+c)) • Y = a • lift p)
    (hq : (1/(1+c)) • X + (c/(1+c)) • Y = b • lift q) :
    dist p q = Real.arcosh c := by
  let U := (c/(1+c)) • X + (1/(1+c)) • Y
  let V := (1/(1+c)) • X + (c/(1+c)) • Y
  have hn : 1+c ≠ 0 := by linarith
  have hUU : lorentz U U = (1-c)/(1+c) := by
    dsimp [U]
    rw [lorentz_linear,lorentz_symm Y X,hX,hY,hXY]
    field_simp [hn]
    <;> ring
  have hVV : lorentz V V = (1-c)/(1+c) := by
    dsimp [V]
    rw [lorentz_linear,lorentz_symm Y X,hX,hY,hXY]
    field_simp [hn]
    <;> ring
  have hUV : lorentz U V = c*((1-c)/(1+c)) := by
    dsimp [U,V]
    rw [lorentz_linear,lorentz_symm Y X,hX,hY,hXY]
    field_simp [hn]
    <;> ring
  have hpa : lorentz U U = -a^2 := by
    rw [show U = a • lift p from hp]
    simpa [lift_unit,pow_two] using (lorentz_linear (lift p) (lift p)
      (lift p) (lift p) a 0 a 0)
  have hqb : lorentz V V = -b^2 := by
    rw [show V = b • lift q from hq]
    simpa [lift_unit,pow_two] using (lorentz_linear (lift q) (lift q)
      (lift q) (lift q) b 0 b 0)
  have hab : a = b := (sq_eq_sq₀ ha.le hb.le).mp (by linarith)
  have hpq : lorentz U V = a*b*(-Real.cosh (dist p q)) := by
    rw [show U = a • lift p from hp,show V = b • lift q from hq]
    simpa only [zero_smul,add_zero,mul_zero,zero_mul,lift_cosh] using
      (lorentz_linear (lift p) (lift p) (lift q) (lift q) a 0 b 0)
  have he : Real.cosh (dist p q) = c := by
    rw [← hUU,hpa] at hUV
    rw [hab] at hpq hUV
    have hb2 : b^2 ≠ 0 := pow_ne_zero 2 hb.ne'
    apply (mul_left_cancel₀ hb2)
    nlinarith only [hpq,hUV]
  rw [← he,Real.arcosh_cosh dist_nonneg]

-- This applies to any supplied original M/f witnesses, for every original edge.
theorem original_edge_distance
    (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (M : Matrix (Fin 4) (Fin 4) ℝ)
    (hG : ∀ i j, lorentz (M i) (M j) = lengthGram l i j)
    (f : cutBody l → HyperbolicThreeSpace)
    (hf : ∀ v, ∃ y : Fin 4 → ℝ, y = (radial l v.val) ᵥ* M ∧
      lorentz y y = -1 ∧ 0 < y 3 ∧
      (f v).coordinates.val = WithLp.toLp 2
        (Complex.mk (y 0/(y 3-y 2)) (y 1/(y 3-y 2)),1/(y 3-y 2)))
    (i j : Fin 4) (hij : i ≠ j) :
    ∃ (p q : cutBody l), p.val = endpoint l i j ∧ q.val = endpoint l j i ∧
      dist (f p) (f q) = Real.arcosh (-lengthGram l i j) := by
  let p : cutBody l := ⟨endpoint l i j,
    ((cut_body_polytope l hl).2.2.2 i j hij).1⟩
  let q : cutBody l := ⟨endpoint l j i,
    ((cut_body_polytope l hl).2.2.2 j i hij.symm).1⟩
  let c := -lengthGram l i j
  have hsym : lengthGram l j i = lengthGram l i j := by
    fin_cases i <;> fin_cases j <;> rfl
  have hd (k : Fin 4) : lengthGram l k k = 1 := by fin_cases k <;> rfl
  have hc : 1 < c := by
    have ht (k : Fin 6) : 1 < Real.cosh (l k) := Real.one_lt_cosh.mpr (hl k).ne'
    dsimp [c]
    fin_cases i <;> fin_cases j <;> first
      | exact (hij rfl).elim
      | simpa [lengthGram] using ht 0
      | simpa [lengthGram] using ht 1
      | simpa [lengthGram] using ht 2
      | simpa [lengthGram] using ht 3
      | simpa [lengthGram] using ht 4
      | simpa [lengthGram] using ht 5
  let scale (v : cutBody l) := Real.sqrt (-gramQuadratic l v.val)
  have hs (v : cutBody l) : 0 < scale v :=
    Real.sqrt_pos.mpr (neg_pos.mpr
      ((shared_radial_body l hl).2.2.2.1 v.val v.property))
  have hraw (v : cutBody l) : v.val ᵥ* M = scale v • lift (f v) := by
    obtain ⟨y,hy,hu,ht,hcoord⟩ := hf v
    have hv : lift (f v) = (radial l v.val) ᵥ* M :=
      (lift_of_coordinates _ _ hu ht hcoord).trans hy
    have hr : radial l v.val = (scale v)⁻¹ • v.val := by
      ext k
      simp [radial,scale,div_eq_mul_inv,mul_comm]
    rw [hv,hr,Matrix.smul_vecMul,smul_smul,mul_inv_cancel₀ (hs v).ne',one_smul]
  refine ⟨p,q,rfl,rfl,?_⟩
  apply two_endpoint_distance (M i) (M j) c (scale p) (scale q) hc
    ((hG i i).trans (hd i)) ((hG j j).trans (hd j))
    (by simpa [c] using hG i j) (f p) (f q) (hs p) (hs q)
  · simpa [p,endpoint,c,Matrix.add_vecMul,Matrix.single_vecMul,sub_eq_add_neg] using hraw p
  · simpa [q,endpoint,c,hsym,Matrix.add_vecMul,Matrix.single_vecMul,sub_eq_add_neg,add_comm]
      using hraw q

def edgeStart : Fin 6 → Fin 4 := ![0,0,0,2,1,1]
def edgeEnd : Fin 6 → Fin 4 := ![1,2,3,3,3,2]

-- The six entries use the original order 01, 02, 03, 23, 13, 12.
theorem all_six_original_lengths
    (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (M : Matrix (Fin 4) (Fin 4) ℝ)
    (hG : ∀ i j, lorentz (M i) (M j) = lengthGram l i j)
    (f : cutBody l → HyperbolicThreeSpace)
    (hf : ∀ v, ∃ y : Fin 4 → ℝ, y = (radial l v.val) ᵥ* M ∧
      lorentz y y = -1 ∧ 0 < y 3 ∧
      (f v).coordinates.val = WithLp.toLp 2
        (Complex.mk (y 0/(y 3-y 2)) (y 1/(y 3-y 2)),1/(y 3-y 2))) :
    ∀ k : Fin 6, ∃ (p q : cutBody l),
      p.val = endpoint l (edgeStart k) (edgeEnd k) ∧
      q.val = endpoint l (edgeEnd k) (edgeStart k) ∧
      dist (f p) (f q) = l k := by
  intro k
  have hij : edgeStart k ≠ edgeEnd k := by
    fin_cases k <;> decide
  have he : -lengthGram l (edgeStart k) (edgeEnd k) = Real.cosh (l k) := by
    fin_cases k <;> simp [edgeStart,edgeEnd,lengthGram]
  obtain ⟨p,q,hp,hq,hd⟩ := original_edge_distance l hl M hG f hf
    (edgeStart k) (edgeEnd k) hij
  refine ⟨p,q,hp,hq,?_⟩
  rw [he,Real.arcosh_cosh (hl k).le] at hd
  exact hd

end CFMPOriginalSixEdgeLengths435Transient
