/- GID: D5/S3/Quantum/Matrix/PsdThreeCubicComplex
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/PsdThreeCubicComplex
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Matrix.PosDef]
   utility: none
   digest: A coefficient criterion for a cubic on every complex PSD three by three matrix. -/

module

public import D5.S3.Quantum.Matrix.PsdThreeCubic
public import Mathlib.Analysis.Matrix.PosDef

/-! There is no rank, phase, radius, invertibility
   or supplied-frame restriction. The Gram witness is constructed directly
   from entries of the original matrix; it uses no source factorization.
   This theorem is abstract in its coefficients. Its HSF specialization still
   needs the scalar certificate and the ordered trace bridge stated separately.
   The proof is elementary PSD geometry; no literature priority is asserted. -/

@[expose] public section
noncomputable section

open Matrix
open scoped ComplexOrder

namespace D5.S3.Quantum.Matrix.PsdThreeCubic

abbrev Mat := Matrix (Fin 3) (Fin 3) ℂ

def cycle (S : Mat) : ℂ := S 0 1 * S 1 2 * S 2 0

def matrixPair (a b c : ℝ) (S : Mat) : ℝ :=
  a*((S 0 0).re+(S 1 1).re)*‖S 0 1‖^2 +
  b*((S 1 1).re+(S 2 2).re)*‖S 1 2‖^2 +
  c*((S 2 2).re+(S 0 0).re)*‖S 2 0‖^2

def cubic (a b c k : ℝ) (S : Mat) : ℝ := matrixPair a b c S + k*(cycle S).re

private theorem quadratic_re (S : Mat) (hS : S.IsHermitian) (v : Fin 3 → ℂ) :
    (star v ⬝ᵥ (S *ᵥ v)).re =
      (S 0 0).re*Complex.normSq (v 0) +
      (S 1 1).re*Complex.normSq (v 1) +
      (S 2 2).re*Complex.normSq (v 2) +
      2*(star (v 0)*S 0 1*v 1 + star (v 1)*S 1 2*v 2 +
        star (v 2)*S 2 0*v 0).re := by
  have h10 : S 1 0 = star (S 0 1) := (hS.apply 1 0).symm
  have h21 : S 2 1 = star (S 1 2) := (hS.apply 2 1).symm
  have h02 : S 0 2 = star (S 2 0) := (hS.apply 0 2).symm
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_succ, h10, h21, h02,
    Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  <;> ring

/-- A direct phase witness, scaled to avoid division in the Gram calculation.
    The three real diagonal entries remain those of S throughout. -/
theorem negative_cycle_gram (S : Mat) (hS : S.PosSemidef) (x y z : ℝ)
    (hx : 0 < x) (hy : 0 < y)
    (ha : Complex.normSq (S 0 1) = x^2)
    (hb : Complex.normSq (S 1 2) = y^2)
    (hcycle : (cycle S).re = -(x*y*z)) :
    ∀ u v w : ℝ, 0 ≤ (S 0 0).re*u^2+(S 1 1).re*v^2+(S 2 2).re*w^2-
      2*(x*u*v+y*v*w+z*w*u) := by
  intro u v w
  let a := S 0 1
  let b := S 1 2
  let c := S 2 0
  let V : Fin 3 → ℂ := ![((x*y*u : ℝ) : ℂ),
    -star a*((y*v : ℝ) : ℂ), star (a*b)*((w : ℝ) : ℂ)]
  have h01 : star (V 0)*a*V 1 = -((x^3*y^2*u*v : ℝ) : ℂ) := by
    change star (((x*y*u : ℝ) : ℂ))*a*(-star a*((y*v : ℝ) : ℂ)) = _
    calc
      _ = -((x*y^2*u*v : ℝ) : ℂ)*(a*star a) := by
        simp only [Complex.star_def, Complex.conj_ofReal]
        push_cast
        ring
      _ = _ := by
        rw [Complex.star_def, Complex.mul_conj, ha]
        push_cast
        ring
  have h12 : star (V 1)*b*V 2 = -((x^2*y^3*v*w : ℝ) : ℂ) := by
    change star (-star a*((y*v : ℝ) : ℂ))*b*(star (a*b)*((w : ℝ) : ℂ)) = _
    calc
      _ = -((y*v*w : ℝ) : ℂ)*((a*b)*star (a*b)) := by
        simp [Complex.star_def, Complex.conj_ofReal]
        ring
      _ = _ := by
        rw [Complex.star_def, Complex.mul_conj, Complex.normSq_mul, ha, hb]
        push_cast
        ring
  have h20 : star (V 2)*c*V 0 = ((x*y*w*u : ℝ) : ℂ)*(a*b*c) := by
    change star (star (a*b)*((w : ℝ) : ℂ))*c*((x*y*u : ℝ) : ℂ) = _
    simp [Complex.star_def, Complex.conj_ofReal]
    ring
  have hq := (Complex.nonneg_iff.mp (hS.dotProduct_mulVec_nonneg V)).1
  rw [quadratic_re S hS.isHermitian V] at hq
  change 0 ≤ (S 0 0).re*Complex.normSq (V 0)+
    (S 1 1).re*Complex.normSq (V 1)+(S 2 2).re*Complex.normSq (V 2)+
    2*(star (V 0)*a*V 1+star (V 1)*b*V 2+star (V 2)*c*V 0).re at hq
  rw [h01, h12, h20] at hq
  have hn0 : Complex.normSq (V 0) = (x*y*u)^2 := by
    simp [V, Complex.normSq_ofReal, pow_two]
    ring
  have hn1 : Complex.normSq (V 1) = x^2*(y*v)^2 := by
    simp [V, a, Complex.normSq_mul, Complex.normSq_conj, ha,
      Complex.normSq_ofReal, pow_two]
    exact Or.inl (by ring)
  have hn2 : Complex.normSq (V 2) = x^2*y^2*w^2 := by
    simp [V, a, b, Complex.normSq_mul, Complex.normSq_conj, ha, hb,
      Complex.normSq_ofReal, pow_two]
  rw [hn0, hn1, hn2] at hq
  have habc : (a*b*c).re = -(x*y*z) := hcycle
  simp only [Complex.add_re, Complex.neg_re, Complex.ofReal_re, Complex.re_ofReal_mul,
    habc] at hq
  have hid : (S 0 0).re*(x*y*u)^2+(S 1 1).re*(x^2*(y*v)^2)+
      (S 2 2).re*(x^2*y^2*w^2)+2*(-(x^3*y^2*u*v)-(x^2*y^3*v*w)+
        (x*y*w*u)*(-(x*y*z))) =
      (x^2*y^2)*((S 0 0).re*u^2+(S 1 1).re*v^2+(S 2 2).re*w^2-
        2*(x*u*v+y*v*w+z*w*u)) := by ring
  have hq' : 0 ≤ (x^2*y^2)*((S 0 0).re*u^2+(S 1 1).re*v^2+(S 2 2).re*w^2-
      2*(x*u*v+y*v*w+z*w*u)) := by
    nlinarith [hq, hid]
  exact nonneg_of_mul_nonneg_right hq' (by positivity : 0 < x^2*y^2)

/-- Every complex PSD three by three matrix satisfies the cubic sign under
    the indicated scalar coefficient criterion. All ranks and zero weights
    are included. No cubic sign or pair bound is assumed. -/
theorem cubic_nonneg (S : Mat) (hS : S.PosSemidef) (a b c k : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hk : 0 ≤ k)
    (hcoeff : k ≤ allowance a b c) : 0 ≤ cubic a b c k S := by
  have hd := (Complex.nonneg_iff.mp (hS.diag_nonneg (i := 0))).1
  have he := (Complex.nonneg_iff.mp (hS.diag_nonneg (i := 1))).1
  have hf := (Complex.nonneg_iff.mp (hS.diag_nonneg (i := 2))).1
  by_cases hW : 0 ≤ (cycle S).re
  · exact add_nonneg (by dsimp [matrixPair]; positivity) (mul_nonneg hk hW)
  · have hWn : (cycle S).re < 0 := lt_of_not_ge hW
    have h01 : S 0 1 ≠ 0 := by intro hz; simp [cycle, hz] at hWn
    have h12 : S 1 2 ≠ 0 := by intro hz; simp [cycle, hz] at hWn
    let x := ‖S 0 1‖
    let y := ‖S 1 2‖
    let z := -(cycle S).re/(x*y)
    have hx : 0 < x := norm_pos_iff.mpr h01
    have hy : 0 < y := norm_pos_iff.mpr h12
    have hz : 0 < z := div_pos (neg_pos.mpr hWn) (mul_pos hx hy)
    have hxyz : x*y*z = -(cycle S).re := by
      dsimp only [z]
      field_simp [ne_of_gt hx, ne_of_gt hy]
      <;> ring
    have hzn : z ≤ ‖S 2 0‖ := by
      have hnorm : -(cycle S).re ≤ x*y*‖S 2 0‖ := by
        calc
          -(cycle S).re ≤ |(cycle S).re| := neg_le_abs _
          _ ≤ ‖cycle S‖ := Complex.abs_re_le_norm _
          _ = x*y*‖S 2 0‖ := by
            simp only [cycle, norm_mul]
            ring
      have hnorm' : -(cycle S).re ≤ x*y*‖S 2 0‖ := by
        simpa [x, y, mul_assoc, mul_comm, mul_left_comm] using hnorm
      exact (div_le_iff₀ (mul_pos hx hy)).mpr (by
        calc
          -(cycle S).re ≤ x*y*‖S 2 0‖ := hnorm'
          _ = ‖S 2 0‖ * (x*y) := by ring)
    have hgram := negative_cycle_gram S hS x y z hx hy
      (Complex.normSq_eq_norm_sq _) (Complex.normSq_eq_norm_sq _)
      (by linarith only [hxyz])
    have hbound := negative_pair_bound a b c (S 0 0).re (S 1 1).re (S 2 2).re
      x y z ha hb hc hx.le hy.le hz.le hgram
    have hreduce : pairEnergy a b c (S 0 0).re (S 1 1).re (S 2 2).re x y z ≤
        matrixPair a b c S := by
      have hsq := (sq_le_sq₀ hz.le (norm_nonneg (S 2 0))).mpr hzn
      have hmul := mul_le_mul_of_nonneg_left hsq (mul_nonneg hc (add_nonneg hf hd))
      dsimp only [pairEnergy, matrixPair, x, y]
      linarith
    have hcW := mul_le_mul_of_nonneg_right hcoeff (neg_nonneg.mpr hWn.le)
    rw [hxyz] at hbound
    dsimp only [cubic]
    nlinarith only [hbound, hreduce, hcW]

end D5.S3.Quantum.Matrix.PsdThreeCubic
