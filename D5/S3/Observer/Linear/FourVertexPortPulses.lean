/- GID: D5/S3/Observer/Linear/FourVertexPortPulses
   generality: G
   mirror-B: D5/B/S3/Observer/Linear/FourVertexPortPulses
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [lake/module/D5.S3.Analytic.ExponentialSum.DescartesRule, mathlib/module/Mathlib.Analysis.Normed.Algebra.MatrixExponential, mathlib/module/Mathlib.LinearAlgebra.Matrix.PosDef, mathlib/module/Mathlib.LinearAlgebra.Eigenspace.Basic, mathlib/module/Mathlib.Data.Finset.Sort, mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Exact four-age preparation and uniform three-age separation at a reflected graph port. -/

import D5.S3.Analytic.ExponentialSum.DescartesRule
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic

/-! # Exact preparation and robust separation at the raw port of a reflected four-vertex pair -/

open Matrix Finset
open scoped Matrix BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Linear.FourVertexPortPulses

noncomputable section

abbrev Vertex := Fin 4
abbrev Vec := Vertex → ℝ
abbrev Mat := Matrix Vertex Vertex ℝ

private def ones : Vec := ![1, 1, 1, 1]
private def z : Vec := ![3, -1, -1, -1]
private def v : Vec := ![0, 1, -2, 1]
private def h : Vec := ![0, -1, 0, 1]

/-- The actuator injects at vertex zero. -/
def port : Vec := ![1, 0, 0, 0]

/-- The centered unit target on the original vertex labels. -/
def target : Vec := (Real.sqrt 14)⁻¹ • ![-3, 0, 1, 2]

private def outer (a b : Vec) : Mat := Matrix.of fun i j => a i * b j

/-- Reflection in the hyperplane perpendicular to the hidden direction. -/
def reflection : Mat := 1 - (1 / 3 : ℝ) • outer v v

private def coupling (q : ℝ) : ℝ := q / (2 * Real.sqrt 3)

/-- The positive-label graph is the centered uniform generator plus the signed
star and the hidden coupling. The negative-label graph is its reflection. -/
def laplacian (M γ q : ℝ) (reflected : Bool) : Mat :=
  let uniform := (M / 8) • ((1 : Mat) - (1 / 4 : ℝ) • outer ones ones)
  let starPart := (γ / 2) • (!![0, -1, 2, -1; -1, 1, 0, 0;
    2, 0, -2, 0; -1, 0, 0, 1] : Mat)
  let L := uniform + starPart + coupling q • (outer v h + outer h v)
  if reflected then reflection * L * reflectionᵀ else L

/-- The endpoint of a finite signed pulse train with distinct ages. -/
def endpoint (L : Mat) (S : Finset ℝ) (w : ℝ → ℝ) : Vec :=
  ∑ t ∈ S, w t • (NormedSpace.exp ((-t) • L) *ᵥ port)

private def signedLaplacian (M γ ρ σ : ℝ) : Mat :=
  (M / 8) • ((1 : Mat) - (1 / 4 : ℝ) • outer ones ones)
    - (σ * γ / 6) • (outer z v + outer v z)
    - (γ / 12) • outer v v + (γ / 4) • outer h h
    + (σ * ρ) • (outer v h + outer h v)

private def orientation (reflected : Bool) : ℝ := if reflected then -1 else 1

set_option maxHeartbeats 2000000 in
-- The finite check expands both four-by-four products before normalization.
private theorem laplacian_signed (M γ q : ℝ) (reflected : Bool) :
    laplacian M γ q reflected = signedLaplacian M γ (coupling q) (orientation reflected) := by
  cases reflected <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [laplacian, signedLaplacian, orientation, reflection, outer, Matrix.mul_apply,
      Fin.sum_univ_succ, Matrix.one_apply, ones, z, v, h] <;> ring

private theorem coupling_bounds {q γ : ℝ} (hq : 0 < q) (hqγ : q ≤ γ / 16) :
    0 < coupling q ∧ coupling q ≤ γ / 32 ∧ 12 * coupling q ^ 2 = q ^ 2 := by
  have hr : 0 < Real.sqrt 3 := by positivity
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h₁ : (1 : ℝ) ≤ Real.sqrt 3 := by nlinarith
  unfold coupling
  refine ⟨by positivity, ?_, ?_⟩
  · calc
      q / (2 * Real.sqrt 3) ≤ q / 2 := by
        apply div_le_div_of_nonneg_left hq.le (by norm_num)
        linarith
      _ ≤ γ / 32 := by linarith
  · field_simp [hr.ne']
    nlinarith [congrArg (fun x : ℝ => x * q ^ 2) hs]

private theorem coupling_le {M γ q : ℝ} (hM : 0 < M) (hγ : 0 < γ)
    (hcap : γ ≤ M / 256) (hq : q ≤ γ ^ 2 / M) : q ≤ γ / 16 := by
  apply (le_div_iff₀ hM).mp at hq
  have hm := mul_nonneg hγ.le (show 0 ≤ M / 256 - γ by linarith)
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 16)).mpr
  by_contra! hn
  have := mul_pos (sub_pos.mpr hn) hM
  nlinarith

private theorem signedLaplacian_symm (M γ ρ σ : ℝ) :
    (signedLaplacian M γ ρ σ).IsSymm := by
  ext i j
  simp [signedLaplacian, outer, Matrix.one_apply, eq_comm, mul_comm, add_comm]

private theorem signedLaplacian_rows (M γ ρ σ : ℝ) (i : Vertex) :
    ∑ j, signedLaplacian M γ ρ σ i j = 0 := by
  fin_cases i <;>
    norm_num [signedLaplacian, outer, Fin.sum_univ_succ, Matrix.one_apply, ones, z, v, h] <;> ring

private theorem signedLaplacian_edges {M γ ρ : ℝ} (hρ : 0 < ρ)
    (hρle : ρ ≤ γ / 32) (hcap : γ ≤ M / 256) (r : Bool)
    (i j : Vertex) (hij : i ≠ j) :
    0 < -signedLaplacian M γ ρ (orientation r) i j := by
  cases r <;> fin_cases i <;> fin_cases j <;>
    first | exact (hij rfl).elim |
      norm_num [signedLaplacian, orientation, outer, Matrix.one_apply, ones, z, v, h]; linarith

private theorem weighted_energy (L : Mat) (hs : L.IsSymm)
    (hr : ∀ i, ∑ j, L i j = 0) (y : Vec) :
    y ⬝ᵥ (L *ᵥ y) = ∑ i, ∑ j, (-L i j) * (y i - y j) ^ 2 / 2 := by
  have hh (i j : Vertex) : L j i = L i j := congrFun (congrFun hs i) j
  have hz (i : Vertex) : ∑ j, L j i = 0 := by
    simpa only [hh i] using hr i
  have hrow : (∑ i, ∑ j, y i ^ 2 / 2 * L i j) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [← Finset.mul_sum, hr, mul_zero]
  have hcol : (∑ i, ∑ j, y j ^ 2 / 2 * L i j) = 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro j _
    rw [← Finset.mul_sum, hz, mul_zero]
  have he (i j : Vertex) :
      (-L i j) * (y i - y j) ^ 2 / 2 =
        y i * (L i j * y j) - y i ^ 2 / 2 * L i j - y j ^ 2 / 2 * L i j := by ring
  simp_rw [he, Finset.sum_sub_distrib, hrow, hcol, sub_zero]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]

private theorem graph_properties {M γ q : ℝ} (hM : 0 < M) (hγ : 0 < γ)
    (hcap : γ ≤ M / 256) (hq : 0 < q) (hqle : q ≤ γ ^ 2 / M) (r : Bool) :
    (laplacian M γ q r).PosSemidef ∧ (∀ i, ∑ j, laplacian M γ q r i j = 0) ∧
      ∀ i j, i ≠ j → 0 < -laplacian M γ q r i j := by
  obtain ⟨hp, hle, _⟩ := coupling_bounds hq (coupling_le hM hγ hcap hqle)
  rw [laplacian_signed]
  let L := signedLaplacian M γ (coupling q) (orientation r)
  have hs : L.IsSymm := signedLaplacian_symm ..
  have hr : ∀ i, ∑ j, L i j = 0 := fun i => signedLaplacian_rows _ _ _ _ i
  have he : ∀ i j, i ≠ j → 0 < -L i j := signedLaplacian_edges hp hle hcap r
  refine ⟨Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨?_, ?_⟩, hr, he⟩
  · change Lᴴ = L
    ext i j
    simpa [Matrix.conjTranspose] using congrFun (congrFun hs i) j
  · intro y
    simp only [star_trivial]
    rw [weighted_energy L hs hr]
    refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_
    by_cases hij : i = j
    · simp [hij]
    · exact div_nonneg (mul_nonneg (he i j hij).le (sq_nonneg _)) (by norm_num)

private def quadratic (γ s : ℝ) : ℝ := s ^ 2 + γ * s / 2 - 2 * γ ^ 2

private def cubic (γ q s : ℝ) : ℝ := (s - γ / 2) * quadratic γ s - q ^ 2 * s

private theorem brackets {γ q : ℝ} (hγ : 0 < γ) (hq : 0 < q) (hqle : q ≤ γ / 16) :
    ∃ l m u : ℝ, -2 * γ < l ∧ l < -γ ∧ 0 < m ∧ m < γ / 2 ∧
      γ < u ∧ u < 2 * γ ∧ cubic γ q l = 0 ∧ cubic γ q m = 0 ∧ cubic γ q u = 0 := by
  have hc : Continuous (cubic γ q) := by unfold cubic quadratic; fun_prop
  have hg : 0 < γ ^ 3 := pow_pos hγ _
  have hqg : 0 < q ^ 2 * γ := by positivity
  have hsmall : q ^ 2 * γ ≤ γ ^ 3 / 256 := by
    have hh := mul_nonneg (sub_nonneg.mpr hqle) (show 0 ≤ γ / 16 + q by positivity)
    nlinarith [mul_nonneg (show 0 ≤ (γ / 16) ^ 2 - q ^ 2 by nlinarith) hγ.le]
  have h₁ : cubic γ q (-2 * γ) < 0 := by unfold cubic quadratic; nlinarith
  have h₂ : 0 < cubic γ q (-γ) := by unfold cubic quadratic; nlinarith
  have h₃ : 0 < cubic γ q 0 := by unfold cubic quadratic; nlinarith
  have h₄ : cubic γ q (γ / 2) < 0 := by unfold cubic quadratic; nlinarith
  have h₅ : cubic γ q γ < 0 := by unfold cubic quadratic; nlinarith
  have h₆ : 0 < cubic γ q (2 * γ) := by unfold cubic quadratic; nlinarith
  obtain ⟨l, hl, el⟩ := intermediate_value_Ioo (show -2 * γ ≤ -γ by linarith)
    hc.continuousOn ⟨h₁, h₂⟩
  obtain ⟨m, hm, em⟩ := intermediate_value_Ioo' (half_pos hγ).le
    hc.continuousOn ⟨h₄, h₃⟩
  obtain ⟨u, hu, eu⟩ := intermediate_value_Ioo (show γ ≤ 2 * γ by linarith)
    hc.continuousOn ⟨h₅, h₆⟩
  exact ⟨l, m, u, hl.1, hl.2, hm.1, hm.2, hu.1, hu.2, el, em, eu⟩

private theorem ratio_signs {γ q l m u : ℝ} (hγ : 0 < γ) (hq : 0 < q)
    (hρ : 0 < coupling q) (hρle : coupling q ≤ γ / 32)
    (hl : l < -γ) (hm₀ : 0 < m) (hm₁ : m < γ / 2) (hu : γ < u)
    (el : cubic γ q l = 0) (eu : cubic γ q u = 0) :
    0 < quadratic γ l + 12 * γ * coupling q ∧
    quadratic γ m + 12 * γ * coupling q < 0 ∧
    0 < quadratic γ u + 12 * γ * coupling q := by
  have houter (s : ℝ) (hs : cubic γ q s = 0) :
      (s - γ / 2) * quadratic γ s = q ^ 2 * s := sub_eq_zero.mp hs
  have hlq : 0 < quadratic γ l := by
    rw [show quadratic γ l = q ^ 2 * l / (l - γ / 2) from
      (eq_div_iff (by linarith)).mpr ((mul_comm _ _).trans (houter l el))]
    exact div_pos_of_neg_of_neg (mul_neg_of_pos_of_neg (sq_pos_of_pos hq) (by linarith))
      (by linarith)
  have huq : 0 < quadratic γ u := by
    rw [show quadratic γ u = q ^ 2 * u / (u - γ / 2) from
      (eq_div_iff (by linarith)).mpr ((mul_comm _ _).trans (houter u eu))]
    exact div_pos (mul_pos (sq_pos_of_pos hq) (by linarith)) (by linarith)
  refine ⟨by positivity, ?_, by positivity⟩
  unfold quadratic
  nlinarith [mul_nonneg (sub_nonneg.mpr hm₁.le) (add_nonneg (half_pos hγ).le hm₀.le),
    mul_nonneg hγ.le (sub_nonneg.mpr hm₁.le), mul_nonneg hγ.le (sub_nonneg.mpr hρle),
    sq_pos_of_pos hγ]

private def eigenrow (γ ρ s : ℝ) : Vec :=
  (2 * γ * ρ) • z - (2 * ρ * s) • v - quadratic γ s • h

private def spectralRows (γ ρ l m u : ℝ) : Mat :=
  Matrix.of ![ones, eigenrow γ ρ l, eigenrow γ ρ m, eigenrow γ ρ u]

private theorem eigenrow_mul (M γ q s : ℝ) (hc : cubic γ q s = 0)
    (hq : 12 * coupling q ^ 2 = q ^ 2) :
    eigenrow γ (coupling q) s ᵥ* laplacian M γ q false =
      (M / 8 + s) • eigenrow γ (coupling q) s := by
  rw [laplacian_signed]
  have hs : (s - γ / 2) * quadratic γ s - 12 * coupling q ^ 2 * s = 0 := by
    rw [hq]; exact hc
  funext j
  fin_cases j <;>
    norm_num [Matrix.vecMul, dotProduct, Fin.sum_univ_succ, eigenrow, signedLaplacian,
      orientation, outer, ones, z, v, h, Matrix.one_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul] <;> unfold quadratic at hs ⊢
  · ring
  · linear_combination -hs
  · ring
  · linear_combination hs

private theorem rows_mul (M γ q l m u : ℝ) (hq : 12 * coupling q ^ 2 = q ^ 2)
    (el : cubic γ q l = 0) (em : cubic γ q m = 0) (eu : cubic γ q u = 0) :
    spectralRows γ (coupling q) l m u * laplacian M γ q false =
      diagonal ![0, M / 8 + l, M / 8 + m, M / 8 + u] * spectralRows γ (coupling q) l m u := by
  ext i j
  rw [Matrix.diagonal_mul]
  fin_cases i
  · change (ones ᵥ* laplacian M γ q false) j = 0 * ones j
    rw [laplacian_signed, zero_mul]
    simp only [vecMul, dotProduct]
    have hs := signedLaplacian_symm M γ (coupling q) (orientation false)
    have he (k : Vertex) : signedLaplacian M γ (coupling q) (orientation false) k j =
        signedLaplacian M γ (coupling q) (orientation false) j k :=
      congrFun (congrFun hs j) k
    simp_rw [show ∀ k, ones k = 1 from fun k => by fin_cases k <;> rfl, one_mul, he]
    exact signedLaplacian_rows ..
  · exact congrFun (eigenrow_mul M γ q l el hq) j
  · exact congrFun (eigenrow_mul M γ q m em hq) j
  · exact congrFun (eigenrow_mul M γ q u eu hq) j

private theorem spectralRows_port (γ ρ l m u : ℝ) :
    spectralRows γ ρ l m u *ᵥ port = ![1, 6 * γ * ρ, 6 * γ * ρ, 6 * γ * ρ] := by
  funext i
  fin_cases i <;>
    norm_num [spectralRows, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, port, ones,
      eigenrow, z, v, h, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] <;> ring

private def targetCoordinate (γ ρ s : ℝ) : ℝ :=
  -(2 * (quadratic γ s + 12 * γ * ρ)) / Real.sqrt 14

private theorem spectralRows_target (γ ρ l m u : ℝ) :
    spectralRows γ ρ l m u *ᵥ target =
      ![0, targetCoordinate γ ρ l, targetCoordinate γ ρ m, targetCoordinate γ ρ u] := by
  funext i
  fin_cases i <;>
    norm_num [spectralRows, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, target, ones,
      eigenrow, z, v, h, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      targetCoordinate, div_eq_mul_inv] <;>
    ring

private theorem spectralRows_injective {R L : Mat} {d : Vec}
    (hd : Function.Injective d) (hRL : R * L = diagonal d * R)
    (hport : ∀ i, (R *ᵥ port) i ≠ 0) : Function.Injective R.mulVec := by
  have he (i : Vertex) : Module.End.HasEigenvector Lᵀ.mulVecLin (d i) (R i) := by
    refine Module.End.hasEigenvector_iff.mpr ⟨Module.End.mem_eigenspace_iff.mpr ?_, ?_⟩
    · funext j
      have hij : (R * L) i j = (diagonal d * R) i j := congrFun (congrFun hRL i) j
      rw [Matrix.diagonal_mul, Matrix.mul_apply] at hij
      simpa only [Matrix.mulVecLin_apply, Matrix.mulVec, Matrix.transpose_apply, dotProduct,
        Pi.smul_apply, smul_eq_mul, mul_comm] using hij
    · intro hz
      apply hport i
      change R i ⬝ᵥ port = 0
      rw [hz, zero_dotProduct]
  have hi := Module.End.eigenvectors_linearIndependent' Lᵀ.mulVecLin d hd R he
  exact Matrix.mulVec_injective_iff_isUnit.mpr
    (Matrix.vecMul_injective_iff_isUnit.mp (Matrix.vecMul_injective_iff.mpr hi))

private theorem exp_similarity (P Q A : Mat) (hPQ : P * Q = 1) :
    NormedSpace.exp (P * A * Q) = P * NormedSpace.exp A * Q := by
  have hu : IsUnit Q :=
    (Matrix.isUnit_iff_isUnit_det Q).mpr (Matrix.isUnit_det_of_left_inverse hPQ)
  simpa only [Matrix.inv_eq_left_inv hPQ] using Matrix.exp_conj' Q A hu

private theorem matrix_heat_coordinates {R L : Mat} {d : Vec}
    (hinj : Function.Injective R.mulVec) (hRL : R * L = diagonal d * R) (t : ℝ) :
    R * NormedSpace.exp ((-t) • L) =
      diagonal (fun i => Real.exp (-t * d i)) * R := by
  have hdet := (Matrix.isUnit_iff_isUnit_det R).mp
    (Matrix.mulVec_injective_iff_isUnit.mp hinj)
  have hInv := Matrix.nonsing_inv_mul R hdet
  have hL : L = R⁻¹ * diagonal d * R := by
    rw [mul_assoc, ← hRL, ← mul_assoc, hInv, one_mul]
  have heq : (-t) • L = R⁻¹ * diagonal (fun i => -t * d i) * R := by
    change (-t) • L = R⁻¹ * diagonal ((-t) • d) * R
    rw [Matrix.diagonal_smul, Matrix.mul_smul, Matrix.smul_mul, ← hL]
  rw [heq, exp_similarity _ _ _ hInv, Matrix.exp_diagonal, Pi.exp_def]
  simp only [← Real.exp_eq_exp_ℝ, ← mul_assoc, Matrix.mul_nonsing_inv R hdet, one_mul]

private theorem reflection_facts :
    reflectionᵀ = reflection ∧ reflection * reflection = 1 ∧
      reflection *ᵥ port = port ∧ reflection *ᵥ target = target := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext i j
    simp [reflection, outer, Matrix.one_apply, eq_comm, mul_comm]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [reflection, outer, v, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ]
  · funext i
    fin_cases i <;>
      norm_num [reflection, outer, v, port, Matrix.mulVec, dotProduct, Matrix.one_apply,
        Fin.sum_univ_succ]
  · funext i
    fin_cases i <;>
      norm_num [reflection, outer, v, target, Matrix.mulVec, dotProduct, Matrix.one_apply,
        Fin.sum_univ_succ, Pi.smul_apply, smul_eq_mul] <;> ring

private theorem endpoint_reflection (M γ q : ℝ) (S : Finset ℝ) (w : ℝ → ℝ) :
    endpoint (laplacian M γ q true) S w = reflection *ᵥ endpoint (laplacian M γ q false) S w := by
  obtain ⟨ht, hu, hb, _⟩ := reflection_facts
  have hstep (t : ℝ) :
      NormedSpace.exp ((-t) • laplacian M γ q true) *ᵥ port =
        reflection *ᵥ (NormedSpace.exp ((-t) • laplacian M γ q false) *ᵥ port) := by
    have hL : (-t) • laplacian M γ q true =
        reflection * ((-t) • laplacian M γ q false) * reflection := by
      change (-t) • (reflection * laplacian M γ q false * reflectionᵀ) = _
      rw [ht, Matrix.mul_smul, Matrix.smul_mul]
    rw [hL, exp_similarity _ _ _ hu, ← Matrix.mulVec_mulVec, hb, ← Matrix.mulVec_mulVec]

  change _ = reflection.mulVecLin (endpoint (laplacian M γ q false) S w)
  simp only [endpoint, hstep, map_sum, map_smul, Matrix.mulVecLin_apply]

private def response (S : Finset ℝ) (w : ℝ → ℝ) (s : ℝ) : ℝ :=
  ∑ t ∈ S, w t * Real.exp (-t * s)

private theorem endpoint_coordinates {R L : Mat} {d : Vec}
    (hinj : Function.Injective R.mulVec) (hRL : R * L = diagonal d * R)
    (S : Finset ℝ) (w : ℝ → ℝ) (i : Vertex) :
    (R *ᵥ endpoint L S w) i = response S w (d i) * (R *ᵥ port) i := by
  change R.mulVecLin (endpoint L S w) i = _
  simp only [endpoint, map_sum, map_smul, Matrix.mulVecLin_apply, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, response, Finset.sum_mul, mul_assoc]
  apply Finset.sum_congr rfl
  intro t _
  rw [Matrix.mulVec_mulVec, matrix_heat_coordinates hinj hRL,
    ← Matrix.mulVec_mulVec, Matrix.mulVec_diagonal]

open D5.S3.Analytic.ExponentialSum.DescartesRule (exponentialSum zero_bound)

private theorem exp_zeros {n : ℕ} (a t : Fin n → ℝ) (ht : StrictMono t)
    (ha : ∃ i, a i ≠ 0) (Z : Finset ℝ)
    (hZ : ∀ s ∈ Z, ∑ i, a i * Real.exp (-t i * s) = 0) :
    Z.card ≤ n - 1 := by
  refine (zero_bound a (fun i => -t i) (fun i j hij => neg_lt_neg (ht hij)) ha Z hZ).trans ?_
  unfold List.signVariations
  apply Nat.sub_le_sub_right _ 1
  calc
    _ ≤ ((List.ofFn a).map SignType.sign |>.filter (· ≠ 0)).length :=
      (List.destutter_sublist _ _).length_le
    _ ≤ ((List.ofFn a).map SignType.sign).length := List.length_filter_le _ _
    _ = n := by simp

private theorem response_eq_sum (S : Finset ℝ) (w : ℝ → ℝ) (s : ℝ) :
    response S w s =
      ∑ i : Fin S.card, w (S.orderEmbOfFin rfl i) * Real.exp (-S.orderEmbOfFin rfl i * s) := by
  unfold response
  conv_lhs => rw [← S.map_orderEmbOfFin_univ rfl, Finset.sum_map]
  rfl

private theorem interpolate (d y : Vec) (hd : Function.Injective d) (S : Finset ℝ)
    (hS : S.card = 4) : ∃ w : ℝ → ℝ, ∀ i, response S w (d i) = y i := by
  classical
  let t : Fin 4 ↪o ℝ := S.orderEmbOfFin hS
  let E : Mat := Matrix.of fun i j => Real.exp (-t j * d i)
  have hk : Function.Injective E.mulVecLin := by
    apply LinearMap.ker_eq_bot.mp
    rw [LinearMap.ker_eq_bot']
    intro a ha
    by_contra hn
    have hnz : ∃ i, a i ≠ 0 := by
      by_contra! hz
      exact hn (funext hz)
    let Z := Finset.univ.image d
    have hz (s : ℝ) (hs : s ∈ Z) : ∑ i, a i * Real.exp (-t i * s) = 0 := by
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hs
      simpa [E, Matrix.mulVec, dotProduct, mul_comm] using congrFun ha j
    have hh := exp_zeros a t t.strictMono hnz Z hz
    have hcard : Z.card = 4 := by
      rw [Finset.card_image_of_injective _ hd, Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨a, ha⟩ := LinearMap.injective_iff_surjective.mp hk y
  let w : ℝ → ℝ := fun s =>
    if hs : s ∈ S then a ((S.orderIsoOfFin hS).symm ⟨s, hs⟩) else 0
  refine ⟨w, fun i => ?_⟩
  unfold response
  rw [← S.map_orderEmbOfFin_univ hS, Finset.sum_map]
  have hw (j : Fin 4) : w (t j) = a j := by
    have hm : t j ∈ S := S.orderEmbOfFin_mem hS j
    rw [show w (t j) = a ((S.orderIsoOfFin hS).symm ⟨t j, hm⟩) by simp [w, hm]]
    exact congrArg a ((S.orderIsoOfFin hS).symm_apply_apply j)
  change (∑ j, w (t j) * Real.exp (-t j * d i)) = y i
  simp_rw [hw]
  simpa [E, Matrix.mulVec, dotProduct, mul_comm] using congrFun ha i

private theorem response_minimum (S : Finset ℝ) (w : ℝ → ℝ)
    {l m u : ℝ} (hl : 0 < l) (hlm : l < m) (hmu : m < u)
    (h0 : response S w 0 = 0) (h1 : response S w l < 0)
    (h2 : 0 < response S w m) (h3 : response S w u < 0) :
    4 ≤ S.card := by
  have hcont : Continuous (response S w) :=
    continuous_finsetSum _ fun t _ => continuous_const.mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id))
  obtain ⟨a, ha, ea⟩ := intermediate_value_Ioo hlm.le hcont.continuousOn ⟨h1, h2⟩
  obtain ⟨b, hb, eb⟩ := intermediate_value_Ioo' hmu.le hcont.continuousOn ⟨h3, h2⟩
  have hab : a < b := ha.2.trans hb.1
  have hza : 0 < a := hl.trans ha.1
  have hzb : 0 < b := hza.trans hab
  let Z : Finset ℝ := {0, a, b}
  have hZ : Z.card = 3 := by
    simp [Z, hza.ne, hzb.ne, hab.ne]
  let t := S.orderEmbOfFin rfl
  let c := fun i => w (t i)
  have hnz : ∃ i, c i ≠ 0 := by
    by_contra! hz
    have hh := response_eq_sum S w m
    change response S w m = ∑ i, c i * Real.exp (-t i * m) at hh
    simp [hz] at hh
    linarith
  have h := exp_zeros c t t.strictMono hnz Z (fun s hs => by
    change (s ∈ ({0, a, b} : Finset ℝ)) at hs
    rw [← response_eq_sum S w s]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl | rfl
    · exact h0
    · exact ea
    · exact eb)
  omega

private theorem spectral_response (M γ q : ℝ) (hγ : 0 < γ) (hcap : γ ≤ M / 256)
    (hq : 0 < q) (hqγ : q ≤ γ / 16) :
    ∃ (d y : Vec) (A : Bool → Mat), Function.Injective d ∧ d 0 = 0 ∧
      0 < d 1 ∧ d 1 < d 2 ∧ d 2 < d 3 ∧
      y 0 = 0 ∧ y 1 < 0 ∧ 0 < y 2 ∧ y 3 < 0 ∧
      (∀ r, Function.Injective (A r).mulVec) ∧ (∀ r, A r *ᵥ target = y) ∧
      ∀ r S w i, (A r *ᵥ endpoint (laplacian M γ q r) S w) i = response S w (d i) := by
  obtain ⟨hρ, hρle, hqρ⟩ := coupling_bounds hq hqγ
  obtain ⟨l, m, u, hl₀, hl₁, hm₀, hm₁, hu₀, hu₁, el, em, eu⟩ := brackets hγ hq hqγ
  let R := spectralRows γ (coupling q) l m u
  let d : Vec := ![0, M / 8 + l, M / 8 + m, M / 8 + u]
  have hd₁ : 0 < d 1 := by change 0 < M / 8 + l; linarith
  have hd₁₂ : d 1 < d 2 := by change M / 8 + l < M / 8 + m; linarith
  have hd₂₃ : d 2 < d 3 := by change M / 8 + m < M / 8 + u; linarith
  have hd : Function.Injective d := by
    apply StrictMono.injective
    intro i j hij
    fin_cases i <;> fin_cases j <;> (try contradiction) <;> (try norm_num at hij)
    all_goals first | exact hd₁ | exact hd₁₂ | exact hd₂₃ |
      exact hd₁.trans hd₁₂ | exact hd₁₂.trans hd₂₃ | exact hd₁.trans (hd₁₂.trans hd₂₃)
  have hRL : R * laplacian M γ q false = diagonal d * R := rows_mul M γ q l m u hqρ el em eu
  have hport : ∀ i, (R *ᵥ port) i ≠ 0 := by
    intro i
    change (spectralRows γ (coupling q) l m u *ᵥ port) i ≠ 0
    rw [spectralRows_port]
    have hp : 0 < 6 * γ * coupling q := by positivity
    fin_cases i <;> first | exact one_ne_zero | exact hp.ne'
  let y : Vec := fun i => (R *ᵥ target) i / (R *ᵥ port) i
  let B : Mat := diagonal (fun i => ((R *ᵥ port) i)⁻¹) * R
  let A : Bool → Mat := fun r => if r then B * reflection else B
  have hB (x : Vec) (i : Vertex) : (B *ᵥ x) i = (R *ᵥ x) i / (R *ᵥ port) i := by
    simp [B, ← Matrix.mulVec_mulVec, Matrix.mulVec_diagonal, div_eq_mul_inv, mul_comm]
  have hR := spectralRows_injective hd hRL hport
  have hBinj : Function.Injective B.mulVec := by
    intro x y hxy
    apply hR
    funext i
    have hh := congrFun hxy i
    change (B *ᵥ x) i = (B *ᵥ y) i at hh
    rwa [hB, hB, div_left_inj' (hport i)] at hh
  obtain ⟨_, hU, _, hx⟩ := reflection_facts
  have hAinj (r : Bool) : Function.Injective (A r).mulVec := by
    cases r
    · exact hBinj
    · intro x y hxy
      change (B * reflection) *ᵥ x = (B * reflection) *ᵥ y at hxy
      simp only [← Matrix.mulVec_mulVec _ B reflection] at hxy
      have hr := congrArg (fun a => reflection *ᵥ a) (hBinj hxy)
      simpa only [Matrix.mulVec_mulVec, hU, Matrix.one_mulVec] using hr
  obtain ⟨hneg₁, hpos, hneg₂⟩ := ratio_signs hγ hq hρ hρle hl₁ hm₀ hm₁ hu₀ el eu
  have hcoord₁ : targetCoordinate γ (coupling q) l < 0 := by
    unfold targetCoordinate
    exact div_neg_of_neg_of_pos (by linarith) (by positivity)
  have hcoord₂ : 0 < targetCoordinate γ (coupling q) m := by
    unfold targetCoordinate
    exact div_pos (by linarith) (by positivity)
  have hcoord₃ : targetCoordinate γ (coupling q) u < 0 := by
    unfold targetCoordinate
    exact div_neg_of_neg_of_pos (by linarith) (by positivity)
  refine ⟨d, y, A, hd, rfl, hd₁, hd₁₂, hd₂₃, ?_, ?_, ?_, ?_, hAinj, ?_, ?_⟩
  · change ((spectralRows γ (coupling q) l m u *ᵥ target) 0) /
        ((spectralRows γ (coupling q) l m u *ᵥ port) 0) = 0
    rw [spectralRows_target, spectralRows_port]
    norm_num
  · simpa [y, R, spectralRows_target, spectralRows_port] using
      div_neg_of_neg_of_pos hcoord₁ (show 0 < 6 * γ * coupling q by positivity)
  · simpa [y, R, spectralRows_target, spectralRows_port] using
      div_pos hcoord₂ (show 0 < 6 * γ * coupling q by positivity)
  · simpa [y, R, spectralRows_target, spectralRows_port] using
      div_neg_of_neg_of_pos hcoord₃ (show 0 < 6 * γ * coupling q by positivity)
  · intro r
    have ht : B *ᵥ target = y := funext fun i => hB target i
    cases r
    · exact ht
    · change (B * reflection) *ᵥ target = y
      rw [← Matrix.mulVec_mulVec, hx, ht]
  · intro r S w i
    have he : (B *ᵥ endpoint (laplacian M γ q false) S w) i = response S w (d i) := by
      rw [hB, endpoint_coordinates hR hRL]
      exact (div_eq_iff (hport i)).mpr rfl
    cases r
    · exact he
    · change ((B * reflection) *ᵥ endpoint (laplacian M γ q true) S w) i = _
      rw [endpoint_reflection, ← Matrix.mulVec_mulVec _ B reflection,
        Matrix.mulVec_mulVec _ reflection reflection, hU, Matrix.one_mulVec, he]

private theorem exact_response (M γ q : ℝ) (hγ : 0 < γ) (hcap : γ ≤ M / 256)
    (hq : 0 < q) (hqγ : q ≤ γ / 16) :
    ∃ d y : Vec, Function.Injective d ∧ d 0 = 0 ∧
      0 < d 1 ∧ d 1 < d 2 ∧ d 2 < d 3 ∧
      y 0 = 0 ∧ y 1 < 0 ∧ 0 < y 2 ∧ y 3 < 0 ∧
      ∀ r S w, endpoint (laplacian M γ q r) S w = target ↔
        ∀ i, response S w (d i) = y i := by
  obtain ⟨d, y, A, hd, hd0, hd1, hd12, hd23, hy0, hy1, hy2, hy3, hinj, ht, he⟩ :=
    spectral_response M γ q hγ hcap hq hqγ
  refine ⟨d, y, hd, hd0, hd1, hd12, hd23, hy0, hy1, hy2, hy3, fun r S w => ?_⟩
  rw [← (hinj r).eq_iff, funext_iff]
  exact forall_congr' fun i => by rw [he, ht]

/-- On the reflected pair, exactly four distinct raw ages are needed to prepare
the target. Any four ages admit a common recipe of zero total input. -/
theorem exact_four_ages (M γ q : ℝ) (hM : 0 < M) (hγ : 0 < γ)
    (hcap : γ ≤ M / 256) (hq : 0 < q) (hqle : q ≤ γ ^ 2 / M) :
    (∀ r, (laplacian M γ q r).PosSemidef ∧ (∀ i, ∑ j, laplacian M γ q r i j = 0) ∧
      ∀ i j, i ≠ j → 0 < -laplacian M γ q r i j) ∧
    (∀ r S w, endpoint (laplacian M γ q r) S w = target →
      4 ≤ S.card ∧ ∑ t ∈ S, w t = 0) ∧
    (∀ S : Finset ℝ, S.card = 4 → ∃ w : ℝ → ℝ, (∑ t ∈ S, w t) = 0 ∧
      ∀ r, endpoint (laplacian M γ q r) S w = target) ∧
    ∀ T : ℝ, 0 < T → ∃ (S : Finset ℝ) (w : ℝ → ℝ),
      S.card = 4 ∧ (∀ t ∈ S, 0 < t ∧ t ≤ T) ∧ (∑ t ∈ S, w t) = 0 ∧
      ∀ r, endpoint (laplacian M γ q r) S w = target := by
  obtain ⟨d, y, hd, hd0, hd1, hd12, hd23, hy0, hy1, hy2, hy3, hresp⟩ :=
    exact_response M γ q hγ hcap hq (coupling_le hM hγ hcap hqle)
  have hnet (S : Finset ℝ) (w : ℝ → ℝ) (hw : ∀ i, response S w (d i) = y i) :
      ∑ t ∈ S, w t = 0 := by
    simpa [hd0, hy0, response] using hw 0
  have hmin r S w (hw : endpoint (laplacian M γ q r) S w = target) :
      4 ≤ S.card ∧ ∑ t ∈ S, w t = 0 := by
    have he := (hresp r S w).mp hw
    refine ⟨response_minimum S w hd1 hd12 hd23 ?_ ?_ ?_ ?_, hnet S w he⟩
    · simpa [hd0, hy0] using he 0
    · rw [he 1]; exact hy1
    · rw [he 2]; exact hy2
    · rw [he 3]; exact hy3
  have hany (S : Finset ℝ) (hS : S.card = 4) :
      ∃ w : ℝ → ℝ, (∑ t ∈ S, w t) = 0 ∧
        ∀ r, endpoint (laplacian M γ q r) S w = target := by
    obtain ⟨w, hw⟩ := interpolate d y hd S hS
    exact ⟨w, hnet S w hw, fun r => (hresp r S w).mpr hw⟩
  refine ⟨graph_properties hM hγ hcap hq hqle, hmin, hany, ?_⟩
  intro T hT
  let t : Vertex → ℝ := fun i => ((i.val : ℝ) + 1) * T / 4
  have ht : StrictMono t := by
    intro i j hij
    dsimp only [t]
    gcongr
    exact_mod_cast (show i.val < j.val from hij)
  let S := Finset.univ.image t
  have hS : S.card = 4 := by simp [S, Finset.card_image_of_injective _ ht.injective]
  obtain ⟨w, hw, he⟩ := hany S hS
  refine ⟨S, w, hS, ?_, hw, he⟩
  intro s hs
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hs
  have hi : (i.val : ℝ) ≤ 3 := by exact_mod_cast (show i.val ≤ 3 by omega)
  exact ⟨by dsimp [t]; positivity, by dsimp [t]; nlinarith [mul_nonneg hT.le (sub_nonneg.mpr hi)]⟩

/-- A common positive vertex max-norm distance from the target holds for every
signed recipe with at most three ages. Nonnegative ages allow arbitrary total
input, and zero total input allows arbitrary real ages. -/
theorem three_age_uniform_distance (M γ q : ℝ) (hM : 0 < M) (hγ : 0 < γ)
    (hcap : γ ≤ M / 256) (hq : 0 < q) (hqle : q ≤ γ ^ 2 / M) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (r : Bool) (S : Finset ℝ) (w : ℝ → ℝ), S.card ≤ 3 →
      ((∑ t ∈ S, w t) = 0 ∨ ∀ t ∈ S, 0 ≤ t) →
      ε ≤ ‖endpoint (laplacian M γ q r) S w - target‖ := by
  obtain ⟨d, y, A, _, hd0, hd1, hd12, hd23, hy0, hy1, hy2, hy3, _, ht, he⟩ :=
    spectral_response M γ q hγ hcap hq (coupling_le hM hγ hcap hqle)
  let margin := min (-(y 1)) (min (y 2) (-(y 3)))
  have hmargin : 0 < margin :=
    lt_min (neg_pos.mpr hy1) (lt_min hy2 (neg_pos.mpr hy3))
  have hm₁ : margin ≤ -(y 1) := min_le_left ..
  have hm₂ : margin ≤ y 2 := (min_le_right ..).trans (min_le_left ..)
  have hm₃ : margin ≤ -(y 3) := (min_le_right ..).trans (min_le_right ..)
  let C := 1 + ∑ r : Bool, ∑ i : Vertex, ∑ j : Vertex, |A r i j|
  have hC : 0 < C := by dsimp [C]; positivity
  have hrow (r : Bool) (i : Vertex) : ∑ j : Vertex, |A r i j| ≤ C := by
    have h₁ : ∑ j : Vertex, |A r i j| ≤ ∑ k : Vertex, ∑ j : Vertex, |A r k j| :=
      Finset.single_le_sum (f := fun k => ∑ j : Vertex, |A r k j|)
        (fun _ _ => by positivity) (Finset.mem_univ i)
    have h₂ : ∑ k : Vertex, ∑ j : Vertex, |A r k j| ≤
        ∑ b : Bool, ∑ k : Vertex, ∑ j : Vertex, |A b k j| :=
      Finset.single_le_sum (f := fun b => ∑ k : Vertex, ∑ j : Vertex, |A b k j|)
        (fun _ _ => by positivity) (Finset.mem_univ r)
    exact (h₁.trans h₂).trans (le_add_of_nonneg_left zero_le_one)
  refine ⟨margin / (2 * C), by positivity, fun r S w hS hages => ?_⟩
  let error := endpoint (laplacian M γ q r) S w - target
  change margin / (2 * C) ≤ ‖error‖
  by_contra! hclose
  have hsmall : 2 * (C * ‖error‖) < margin := by
    have hh := (lt_div_iff₀ (show 0 < 2 * C by positivity)).mp hclose
    linarith only [show ‖error‖ * (2 * C) = 2 * (C * ‖error‖) by ring, hh]
  have hnear (i : Vertex) : |response S w (d i) - y i| ≤ C * ‖error‖ := by
    calc
      |response S w (d i) - y i| = |(A r *ᵥ error) i| := by
        dsimp only [error]
        rw [Matrix.mulVec_sub, Pi.sub_apply, he, ht]
      _ ≤ ∑ j : Vertex, |A r i j * error j| :=
        Finset.abs_sum_le_sum_abs (fun j => A r i j * error j) Finset.univ
      _ ≤ ∑ j : Vertex, |A r i j| * ‖error‖ := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul]
        have hj : |error j| ≤ ‖error‖ := by
          simpa only [Real.norm_eq_abs] using (norm_le_pi_norm error j)
        exact mul_le_mul_of_nonneg_left hj (abs_nonneg _)
      _ ≤ C * ‖error‖ := by
        rw [← Finset.sum_mul]
        exact mul_le_mul_of_nonneg_right (hrow r i) (norm_nonneg _)
  have hmass : |response S w 0| ≤ C * ‖error‖ := by
    simpa only [hd0, hy0, sub_zero] using hnear 0
  have hnonempty : S.Nonempty := by
    by_contra! h
    have hh := neg_le_of_abs_le (hnear 2)
    simp [h, response] at hh
    linarith [show 0 ≤ C * ‖error‖ by positivity]
  obtain ⟨t₀, ht₀⟩ := hnonempty
  let corrected : ℝ → ℝ := fun t => w t - if t = t₀ then response S w 0 else 0
  have hcorrect (s : ℝ) :
      response S corrected s = response S w s - response S w 0 * Real.exp (-t₀ * s) := by
    simp [response, corrected, sub_mul, Finset.sum_sub_distrib, ite_mul, ht₀]
  have hcorrection (s : ℝ) (hs : 0 ≤ s) :
      |response S w 0 * Real.exp (-t₀ * s)| ≤ C * ‖error‖ := by
    rcases hages with hzero | hn
    · have hz : response S w 0 = 0 := by simpa [response] using hzero
      simpa [hz] using (show 0 ≤ C * ‖error‖ by positivity)
    · rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      have hdecay : Real.exp (-t₀ * s) ≤ 1 :=
        Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (hn t₀ ht₀)) hs)
      exact (mul_le_of_le_one_right (abs_nonneg _) hdecay).trans hmass
  have hsign (i : Vertex) (hi : 0 ≤ d i) : |response S corrected (d i) - y i| < margin := by
    rw [hcorrect, sub_right_comm]
    have htriangle (a b : ℝ) : |a - b| ≤ |a| + |b| := by
      simpa only [sub_eq_add_neg, abs_neg] using abs_add_le a (-b)
    exact (htriangle _ _).trans_lt
      ((add_le_add (hnear i) (hcorrection (d i) hi)).trans_lt (by linarith))
  have hs₁ := le_abs_self (response S corrected (d 1) - y 1)
  have hs₂ := neg_le_abs (response S corrected (d 2) - y 2)
  have hs₃ := le_abs_self (response S corrected (d 3) - y 3)
  have hzeros := response_minimum S corrected hd1 hd12 hd23
    (by simp [hcorrect])
    (by linarith [hs₁.trans_lt (hsign 1 hd1.le)])
    (by linarith [hs₂.trans_lt (hsign 2 (hd1.trans hd12).le)])
    (by linarith [hs₃.trans_lt (hsign 3 ((hd1.trans hd12).trans hd23).le)])
  omega

end
end D5.S3.Observer.Linear.FourVertexPortPulses
