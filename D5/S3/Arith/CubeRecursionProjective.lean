/- GID: D5/S3/Arith/CubeRecursionProjective
   generality: G
   mirror-B: D5/B/S3/Arith/CubeRecursionProjective
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Topology.Compactification.OnePoint.ProjectiveLine, mathlib/module/Mathlib.FieldTheory.RatFunc.AsPolynomial]
   utility: none
   digest: The cubic recursion is a degree three projective map with a two-point fibre excluding power-map conjugacy. -/

import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic

/-! # Projective cubic recursion

The two-point zero fibre obstructs conjugacy to the cubic power map.
-/

open scoped MatrixGroups LinearAlgebra.Projectivization

namespace D5.S3.Arith.CubeRecursionProjective

noncomputable section

open Polynomial OnePoint

/-- The affine numerator over a field. -/
def numerator (t : ℕ) : ℂ[X] := X + C (t : ℂ)

/-- The affine denominator over a field. -/
def denominator (t : ℕ) : ℂ[X] := (X + C (t : ℂ) + 1) ^ 3 - (X + C (t : ℂ))

/-- The rational function, before choosing projective coordinates. -/
def rationalMap (t : ℕ) : RatFunc ℂ :=
  algebraMap ℂ[X] (RatFunc ℂ) (numerator t) /
    algebraMap ℂ[X] (RatFunc ℂ) (denominator t)

/-- The degree of a rational map is the maximum of the reduced polynomial degrees. -/
def mapDegree (f : RatFunc ℂ) : ℕ := max f.num.natDegree f.denom.natDegree

private theorem polynomial_coprime (t : ℕ) :
    IsCoprime (numerator t) (denominator t) := by
  refine ⟨-((numerator t) ^ 2 + 3 * numerator t + 2), 1, ?_⟩
  simp only [numerator, denominator]
  ring

private theorem denominator_monic (t : ℕ) : (denominator t).Monic := by
  unfold denominator
  monicity <;> norm_num

private theorem reduced_polynomials (t : ℕ) :
    (rationalMap t).num = numerator t ∧ (rationalMap t).denom = denominator t := by
  classical
  have hg : GCDMonoid.gcd (numerator t) (denominator t) = 1 := by
    rw [← normalize_gcd, normalize_eq_one]
    exact (polynomial_coprime t).isUnit_of_dvd'
      (gcd_dvd_left _ _) (gcd_dvd_right _ _)
  simp [rationalMap, RatFunc.num_div, RatFunc.denom_div _ (denominator_monic t).ne_zero,
    hg, (denominator_monic t).leadingCoeff]

/-- The true degree is three, using the reduced numerator and denominator. -/
theorem map_degree_three (t : ℕ) :
    (rationalMap t).num.natDegree = 1 ∧
    (rationalMap t).denom.natDegree = 3 ∧ mapDegree (rationalMap t) = 3 := by
  have hn : (numerator t).natDegree = 1 := by
    unfold numerator
    compute_degree <;> norm_num
  have hd : (denominator t).natDegree = 3 := by
    unfold denominator
    compute_degree <;> norm_num
  obtain ⟨hnum, hden⟩ := reduced_polynomials t
  simp [hnum, hden, hn, hd, mapDegree]

/-- The denominator evaluated in an affine chart. -/
def q (t : ℕ) (z : ℂ) : ℂ := (z + t + 1) ^ 3 - (z + t)

/-- The map on the whole projective line: poles map to infinity, infinity to zero. -/
def projectiveMap (t : ℕ) : OnePoint ℂ → OnePoint ℂ
  | ∞ => (0 : ℂ)
  | (z : ℂ) => if q t z = 0 then ∞ else ((z + t) / q t z : ℂ)

/-- Homogeneous numerator of degree three. -/
def homogeneousA (t : ℕ) (x y : ℂ) : ℂ := (x + t * y) * y ^ 2

/-- Homogeneous denominator of degree three. -/
def homogeneousB (t : ℕ) (x y : ℂ) : ℂ :=
  (x + (t + 1) * y) ^ 3 - (x + t * y) * y ^ 2

private theorem homogeneous_nonzero (t : ℕ) (x y : ℂ) (h : x ≠ 0 ∨ y ≠ 0) :
    ![homogeneousA t x y, homogeneousB t x y] ≠ (0 : Fin 2 → ℂ) := by
  intro he
  have ha : homogeneousA t x y = 0 := congrFun he 0
  have hb : homogeneousB t x y = 0 := congrFun he 1
  by_cases hy : y = 0
  · have hx : x ≠ 0 := h.resolve_right (not_ne_iff.mpr hy)
    simpa [homogeneousB, hy, hx] using hb
  · have hu : x + t * y = 0 :=
      (mul_eq_zero.mp ha).resolve_right (pow_ne_zero 2 hy)
    have hx : x = -(t : ℂ) * y := by linear_combination hu
    have hb' : homogeneousB t x y = y ^ 3 := by rw [hx]; unfold homogeneousB; ring
    rw [hb'] at hb
    exact pow_ne_zero 3 hy hb

/-- The point represented by nonzero homogeneous coordinates. -/
def projectivePoint (x y : ℂ) (h : x ≠ 0 ∨ y ≠ 0) : OnePoint ℂ :=
  (OnePoint.equivProjectivization ℂ).symm
    (Projectivization.mk ℂ ![x, y] (by
      intro hv
      have hx : x = 0 := congrFun hv 0
      have hy : y = 0 := congrFun hv 1
      exact h.elim (fun h => h hx) (fun h => h hy)))

/-- The image represented by the nonvanishing homogeneous cubic pair. -/
def homogeneousImage (t : ℕ) (x y : ℂ) (h : x ≠ 0 ∨ y ≠ 0) : OnePoint ℂ :=
  (OnePoint.equivProjectivization ℂ).symm
    (Projectivization.mk ℂ ![homogeneousA t x y, homogeneousB t x y]
      (homogeneous_nonzero t x y h))

/-- Agreement with homogeneous coordinates, including all poles and infinity. -/
theorem homogeneous_coordinates (t : ℕ) (x y : ℂ) (h : x ≠ 0 ∨ y ≠ 0) :
    projectiveMap t (projectivePoint x y h) = homogeneousImage t x y h := by
  unfold projectivePoint homogeneousImage
  rw [OnePoint.equivProjectivization_symm_apply_mk,
    OnePoint.equivProjectivization_symm_apply_mk]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  by_cases hy : y = 0
  · have hx : x ≠ 0 := h.resolve_right (not_ne_iff.mpr hy)
    simp [hy, projectiveMap, homogeneousA, homogeneousB, hx]
  · have hd : q t (y⁻¹ * x) = homogeneousB t x y / y ^ 3 := by
      unfold q homogeneousB
      field_simp
      <;> ring
    have hd0 : q t (y⁻¹ * x) = 0 ↔ homogeneousB t x y = 0 := by
      rw [hd, div_eq_zero_iff]
      simp [hy]
    simp only [hy, ite_false, projectiveMap]
    by_cases hb : homogeneousB t x y = 0
    · simp [hb, hd0.mpr hb]
    · simp only [hb, ite_false, hd0.not.mpr hb]
      rw [hd]
      congr 1
      unfold homogeneousA
      field_simp
      <;> ring

/-- The cubic power map on the whole projective line. -/
def powerMap : OnePoint ℂ → OnePoint ℂ
  | ∞ => ∞
  | (z : ℂ) => (z ^ 3 : ℂ)

/-- The genuine PGL action transported through the canonical projective-line equivalence. -/
def mobius (g : PGL(2, ℂ)) : Equiv.Perm (OnePoint ℂ) :=
  ((OnePoint.equivProjectivization ℂ).trans (MulAction.toPerm g)).trans
    (OnePoint.equivProjectivization ℂ).symm

private theorem mobius_inverse (g : PGL(2, ℂ)) : mobius g⁻¹ = (mobius g).symm := by
  ext p
  simp [mobius]

/-- The affine rational-function evaluation and the projective extension agree in every chart. -/
theorem rational_map_semantics (t : ℕ) :
    projectiveMap t ∞ = (0 : ℂ) ∧
    ∀ z : ℂ, projectiveMap t z =
      if (rationalMap t).denom.eval z = 0 then ∞
      else (RatFunc.eval (RingHom.id ℂ) z (rationalMap t) : ℂ) := by
  obtain ⟨hn, hd⟩ := reduced_polynomials t
  simp [projectiveMap, RatFunc.eval, hn, hd, numerator, denominator, q]
  intro z
  split_ifs with hz <;> simp [hz]

private theorem zero_fibre (t : ℕ) (p : OnePoint ℂ) :
    projectiveMap t p = (0 : ℂ) ↔ p = (-(t : ℂ) : ℂ) ∨ p = ∞ := by
  cases p with
  | infty => simp [projectiveMap]
  | coe z =>
    by_cases hz : q t z = 0
    · have hzt : z ≠ -(t : ℂ) := by
        intro h
        simp [q, h] at hz
      simp [projectiveMap, hz, hzt]
    · simp [projectiveMap, hz, div_eq_zero_iff, add_eq_zero_iff_eq_neg]

private theorem cube_third (u v : ℂ) (hne : u ≠ v) (hc : u ^ 3 = v ^ 3) :
    ∃ w : ℂ, w ≠ u ∧ w ≠ v ∧ w ^ 3 = u ^ 3 := by
  have hf : (u - v) * (u ^ 2 + u * v + v ^ 2) = 0 := by
    linear_combination hc
  have hq : u ^ 2 + u * v + v ^ 2 = 0 :=
    (mul_eq_zero.mp hf).resolve_left (sub_ne_zero.mpr hne)
  have hw (a b : ℂ) (hn : a ≠ b) (h : a ^ 2 + a * b + b ^ 2 = 0) :
      -a - b ≠ a := by
    intro he
    have hb : b = -2 * a := by linear_combination -he
    rw [hb] at h
    have ha2 : a ^ 2 = 0 := by linear_combination (1 / 3 : ℂ) * h
    have ha : a = 0 := eq_zero_of_pow_eq_zero ha2
    apply hn
    simp [hb, ha]
  refine ⟨-u-v, hw u v hne hq, ?_, ?_⟩
  · convert hw v u hne.symm (by linear_combination hq) using 1 <;> ring
  · linear_combination -(2 * u + v) * hq

private theorem power_third (p r : OnePoint ℂ) (hne : p ≠ r)
    (h : powerMap p = powerMap r) :
    ∃ s, s ≠ p ∧ s ≠ r ∧ powerMap s = powerMap p := by
  cases p with
  | infty => cases r <;> simp_all [powerMap]
  | coe u =>
    cases r with
    | infty => simp [powerMap] at h
    | coe v =>
      have huv : u ≠ v := by simpa using hne
      have hc : u ^ 3 = v ^ 3 := by simpa [powerMap] using h
      obtain ⟨w, hwu, hwv, hw⟩ := cube_third u v huv hc
      exact ⟨(w : OnePoint ℂ), by simpa using hwu, by simpa using hwv,
        by simpa [powerMap] using hw⟩

/-- No projective change of coordinates conjugates a member of the family to the cube map. -/
theorem not_conjugate (t : ℕ) (g : PGL(2, ℂ)) :
    ¬ ∀ p : OnePoint ℂ,
      mobius g (projectiveMap t (mobius g⁻¹ p)) = powerMap p := by
  simp only [mobius_inverse]
  intro h
  let e := mobius g
  let a : OnePoint ℂ := (-(t : ℂ) : ℂ)
  let b : OnePoint ℂ := ∞
  have hab : a ≠ b := by simp [a, b]
  have hfa : projectiveMap t a = (0 : ℂ) := (zero_fibre t a).mpr (Or.inl rfl)
  have hfb : projectiveMap t b = (0 : ℂ) := rfl
  have hea : powerMap (e a) = e (0 : ℂ) := by simpa [e, hfa] using (h (e a)).symm
  have heb : powerMap (e b) = e (0 : ℂ) := by simpa [e, hfb] using (h (e b)).symm
  obtain ⟨c, hca, hcb, hc⟩ := power_third (e a) (e b) (e.injective.ne hab) (hea.trans heb.symm)
  have hfc : projectiveMap t (e.symm c) = (0 : ℂ) := by
    apply e.injective
    exact (h c).trans (hc.trans hea)
  rcases (zero_fibre t (e.symm c)).mp hfc with ha | hb
  · apply hca
    exact (e.apply_symm_apply c).symm.trans (congrArg e ha)
  · apply hcb
    exact (e.apply_symm_apply c).symm.trans (congrArg e hb)

/-- The PGL action agrees with the usual fractional-linear formulas at finite points and infinity. -/
theorem mobius_coordinates (g : GL (Fin 2) ℂ) :
    mobius (Matrix.ProjGenLinGroup.mk g) ∞ =
      (if g 1 0 = 0 then ∞ else (g 0 0 / g 1 0 : ℂ)) ∧
    ∀ z : ℂ, mobius (Matrix.ProjGenLinGroup.mk g) z =
      (if g 1 0 * z + g 1 1 = 0 then ∞
       else ((g 0 0 * z + g 0 1) / (g 1 0 * z + g 1 1) : ℂ)) := by
  have he (p : OnePoint ℂ) : mobius (Matrix.ProjGenLinGroup.mk g) p = g • p := by
    apply (OnePoint.equivProjectivization ℂ).injective
    simp only [mobius, Equiv.trans_apply, Equiv.apply_symm_apply,
      OnePoint.equivProjectivization_smul]
    induction (OnePoint.equivProjectivization ℂ p) using Projectivization.ind with
    | h v hv => rfl
  constructor
  · rw [he]; exact OnePoint.smul_infty_eq_ite g
  · intro z; rw [he]; exact OnePoint.smul_some_eq_ite

end

end D5.S3.Arith.CubeRecursionProjective
