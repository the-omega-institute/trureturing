/- GID: D5/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D
   generality: G
   mirror-B: D5/B/S3/Geometry/Lorentz/GRLinearizedWavesQuadrupole4D
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Transverse traceless polarization and circular binary quadrupole inspiral. -/

import OmegaBuild.Commands
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

/-! The transverse projection acts on spatial strains in three dimensions.
The circular binary equations use the Newtonian energy and leading quadrupole flux. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix Filter
open scoped BigOperators Matrix Topology

namespace D5.S3.Geometry.Lorentz.GRLinearizedWavesQuadrupole4D

def IsUnitVec3 (n : Fin 3 → ℝ) : Prop := ∑ i : Fin 3, (n i) ^ 2 = 1

def transverseProj (n : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j => (if i = j then 1 else 0) - n i * n j

def ttProj (n : Fin 3 → ℝ) (h : Matrix (Fin 3) (Fin 3) ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  transverseProj n * h * transverseProj n -
    ((1 / 2 : ℝ) * Matrix.trace (transverseProj n * h)) • transverseProj n

private theorem transverseProj_eq (n : Fin 3 → ℝ) :
    transverseProj n = 1 - vecMulVec n n := by
  ext i j
  simp [transverseProj, Matrix.one_apply, Matrix.vecMulVec_apply]

private theorem transverseProj_transpose (n : Fin 3 → ℝ) :
    (transverseProj n)ᵀ = transverseProj n := by
  ext i j
  simp [transverseProj, eq_comm, mul_comm]

theorem transverseProj_spec (n : Fin 3 → ℝ) (hn : IsUnitVec3 n) :
    (transverseProj n)ᵀ = transverseProj n ∧
    transverseProj n * transverseProj n = transverseProj n ∧
    (transverseProj n).mulVec n = 0 ∧ Matrix.trace (transverseProj n) = 2 := by
  have hdot : n ⬝ᵥ n = 1 := by simpa [dotProduct, pow_two, IsUnitVec3] using hn
  refine ⟨transverseProj_transpose n, ?_⟩
  rw [transverseProj_eq]
  constructor
  · simp only [sub_mul, mul_sub]
    rw [Matrix.vecMulVec_mul_vecMulVec, hdot]
    simp
  constructor
  · rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.vecMulVec_mulVec, hdot]
    simp
  · rw [Matrix.trace_sub, Matrix.trace_one, Matrix.trace_vecMulVec, hdot]
    norm_num

theorem ttProj_symmetric (n : Fin 3 → ℝ) (h : Matrix (Fin 3) (Fin 3) ℝ)
    (hh : hᵀ = h) : (ttProj n h)ᵀ = ttProj n h := by
  simp [ttProj, Matrix.transpose_mul, transverseProj_transpose, hh, Matrix.mul_assoc]

theorem ttProj_transverse (n : Fin 3 → ℝ) (hn : IsUnitVec3 n)
    (h : Matrix (Fin 3) (Fin 3) ℝ) : (ttProj n h).mulVec n = 0 := by
  unfold ttProj
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec,
    (transverseProj_spec n hn).2.2.1]
  simp

theorem ttProj_traceless (n : Fin 3 → ℝ) (hn : IsUnitVec3 n)
    (h : Matrix (Fin 3) (Fin 3) ℝ) : Matrix.trace (ttProj n h) = 0 := by
  obtain ⟨_, hidem, _, htr⟩ := transverseProj_spec n hn
  have hcycle := Matrix.trace_mul_cycle (transverseProj n) h (transverseProj n)
  rw [hidem] at hcycle
  rw [ttProj, Matrix.trace_sub, Matrix.trace_smul, hcycle, htr, smul_eq_mul]
  ring

theorem ttProj_idempotent (n : Fin 3 → ℝ) (hn : IsUnitVec3 n)
    (h : Matrix (Fin 3) (Fin 3) ℝ) : ttProj n (ttProj n h) = ttProj n h := by
  let P := transverseProj n
  have hidem : P * P = P := (transverseProj_spec n hn).2.1
  have hleft : P * ttProj n h = ttProj n h := by
    change P * (P * h * P - ((1 / 2 : ℝ) * Matrix.trace (P * h)) • P) = _
    rw [mul_sub, Matrix.mul_smul, hidem, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hidem]
    rfl
  have hright : ttProj n h * P = ttProj n h := by
    change (P * h * P - ((1 / 2 : ℝ) * Matrix.trace (P * h)) • P) * P = _
    rw [sub_mul, Matrix.smul_mul, Matrix.mul_assoc, hidem]
    rfl
  change P * ttProj n h * P - ((1 / 2 : ℝ) * Matrix.trace (P * ttProj n h)) • P = _
  rw [hleft, hright, ttProj_traceless n hn]
  simp

theorem ttProj_selfAdjoint (n : Fin 3 → ℝ) (h k : Matrix (Fin 3) (Fin 3) ℝ) :
    Matrix.trace ((ttProj n h)ᵀ * k) = Matrix.trace (hᵀ * ttProj n k) := by
  let P := transverseProj n
  have hs : Pᵀ = P := transverseProj_transpose n
  have ht : Matrix.trace (hᵀ * P) = Matrix.trace (P * h) := by
    simpa only [hs, Matrix.transpose_mul, Matrix.transpose_transpose] using
      (Matrix.trace_transpose (hᵀ * P)).symm
  have hcycle : Matrix.trace (P * (hᵀ * P) * k) = Matrix.trace (hᵀ * (P * k * P)) := by
    rw [Matrix.mul_assoc P, Matrix.trace_mul_comm P]
    simp only [Matrix.mul_assoc]
  change Matrix.trace ((P * h * P - ((1 / 2 : ℝ) * Matrix.trace (P * h)) • P)ᵀ * k) =
    Matrix.trace (hᵀ * (P * k * P - ((1 / 2 : ℝ) * Matrix.trace (P * k)) • P))
  rw [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_mul,
    Matrix.transpose_smul, hs, sub_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul, hcycle, ht]
  simp only [smul_eq_mul]
  ring

def ePlus : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 0; 0, -1, 0; 0, 0, 0]
def eCross : Matrix (Fin 3) (Fin 3) ℝ := !![0, 1, 0; 1, 0, 0; 0, 0, 0]

def gwStrainZ (hp hc : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := hp • ePlus + hc • eCross

private theorem gwStrainZ_eq (hp hc : ℝ) : gwStrainZ hp hc = !![hp, hc, 0; hc, -hp, 0; 0, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [gwStrainZ, ePlus, eCross, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul]

private theorem gwStrainZ_tt (hp hc : ℝ) :
    (gwStrainZ hp hc)ᵀ = gwStrainZ hp hc ∧ (gwStrainZ hp hc).mulVec ![0, 0, 1] = 0 ∧
      Matrix.trace (gwStrainZ hp hc) = 0 := by
  rw [gwStrainZ_eq]
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> rfl
  · funext i
    fin_cases i <;> norm_num [Matrix.mulVec_apply, dotProduct, Fin.sum_univ_three]
  · simp [Matrix.trace_fin_three]

private theorem tt_z_reconstruct (h : Matrix (Fin 3) (Fin 3) ℝ) (hs : hᵀ = h)
    (hv : h.mulVec ![0, 0, 1] = 0) (ht : Matrix.trace h = 0) :
    h = gwStrainZ (h 0 0) (h 0 1) := by
  have hcol (i : Fin 3) : h i 2 = 0 := by
    simpa [Matrix.mulVec_apply, dotProduct, Fin.sum_univ_three] using congrFun hv i
  have hsym (i j : Fin 3) : h j i = h i j :=
    congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M i j) hs
  have hrow (i : Fin 3) : h 2 i = 0 := (hsym i 2).trans (hcol i)
  have hdiag : h 1 1 = -h 0 0 := by
    rw [Matrix.trace_fin_three, hcol 2, add_zero] at ht
    linarith
  rw [gwStrainZ_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    first | rfl | exact hcol _ | exact hrow _ | exact hdiag | exact hsym 0 1

theorem tt_z_classification (h : Matrix (Fin 3) (Fin 3) ℝ) :
    (hᵀ = h ∧ h.mulVec ![0, 0, 1] = 0 ∧ Matrix.trace h = 0) ↔
      ∃ hp hc : ℝ, h = gwStrainZ hp hc := by
  constructor
  · rintro ⟨hs, hv, ht⟩
    exact ⟨h 0 0, h 0 1, tt_z_reconstruct h hs hv ht⟩
  · rintro ⟨hp, hc, rfl⟩
    exact gwStrainZ_tt hp hc

theorem tt_z_coordinates (h : Matrix (Fin 3) (Fin 3) ℝ) {hp hc : ℝ}
    (hh : h = gwStrainZ hp hc) : hp = h 0 0 ∧ hc = h 0 1 := by
  rw [hh, gwStrainZ_eq]
  exact ⟨rfl, rfl⟩

def TTSubspaceZ : Submodule ℝ (Matrix (Fin 3) (Fin 3) ℝ) where
  carrier := {h | hᵀ = h ∧ h.mulVec ![0, 0, 1] = 0 ∧ Matrix.trace h = 0}
  zero_mem' := by simp
  add_mem' := by
    rintro a b ⟨has, hav, hat⟩ ⟨hbs, hbv, hbt⟩
    simp [Matrix.transpose_add, Matrix.add_mulVec, Matrix.trace_add, has, hav, hat, hbs, hbv, hbt]
  smul_mem' := by
    rintro c a ⟨has, hav, hat⟩
    simp [Matrix.transpose_smul, Matrix.smul_mulVec, Matrix.trace_smul, has, hav, hat]

theorem tt_z_finrank_two : Module.finrank ℝ TTSubspaceZ = 2 := by
  let coords : TTSubspaceZ ≃ₗ[ℝ] (Fin 2 → ℝ) :=
    { toFun := fun h => ![h.val 0 0, h.val 0 1]
      invFun := fun a => ⟨gwStrainZ (a 0) (a 1), gwStrainZ_tt (a 0) (a 1)⟩
      left_inv := by
        intro h
        apply Subtype.ext
        obtain ⟨hs, hv, ht⟩ := h.property
        exact (tt_z_reconstruct h.val hs hv ht).symm
      right_inv := by
        intro a
        obtain ⟨hp, hc⟩ := tt_z_coordinates (gwStrainZ (a 0) (a 1)) rfl
        funext i
        fin_cases i
        · exact hp.symm
        · exact hc.symm
      map_add' := by
        intro a b
        funext i
        fin_cases i <;> rfl
      map_smul' := by
        intro c a
        funext i
        fin_cases i <;> rfl }
  exact coords.finrank_eq.trans (Module.finrank_fin_fun ℝ)

def rotZ3 (φ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![Real.cos φ, -Real.sin φ, 0; Real.sin φ, Real.cos φ, 0; 0, 0, 1]

theorem gw_strain_helicity_two (φ hp hc : ℝ) :
    rotZ3 φ * gwStrainZ hp hc * (rotZ3 φ)ᵀ =
      gwStrainZ (hp * Real.cos (2 * φ) - hc * Real.sin (2 * φ))
        (hp * Real.sin (2 * φ) + hc * Real.cos (2 * φ)) := by
  simp only [gwStrainZ_eq, rotZ3, Real.cos_two_mul', Real.sin_two_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem gw_strain_pi_invariant (hp hc : ℝ) :
    rotZ3 Real.pi * gwStrainZ hp hc * (rotZ3 Real.pi)ᵀ = gwStrainZ hp hc := by
  rw [gw_strain_helicity_two]
  simp [Real.sin_two_mul, Real.cos_two_mul']

theorem gw_strain_half_pi_neg (hp hc : ℝ) :
    rotZ3 (Real.pi / 2) * gwStrainZ hp hc * (rotZ3 (Real.pi / 2))ᵀ = -gwStrainZ hp hc := by
  rw [gw_strain_helicity_two, show 2 * (Real.pi / 2) = Real.pi by ring]
  simp [gwStrainZ, Real.sin_pi, Real.cos_pi, add_comm]

theorem gw_strain_hilbert_schmidt_energy (hp hc : ℝ) :
    Matrix.trace (gwStrainZ hp hc * gwStrainZ hp hc) = 2 * (hp ^ 2 + hc ^ 2) := by
  rw [gwStrainZ_eq, Matrix.trace_fin_three]
  norm_num [Matrix.mul_apply, Fin.sum_univ_three]
  ring

/-! The circular orbit, its quadrupole radiation, and the positive-radius inspiral. -/

def binaryQuadrupole (μ r ω t : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  let x : Fin 3 → ℝ := ![r * Real.cos (ω * t), r * Real.sin (ω * t), 0]
  Matrix.of fun i j => μ * (x i * x j - (1 / 3) * r ^ 2 * (1 : Matrix (Fin 3) (Fin 3) ℝ) i j)

private def orbitalHarmonic (a b d : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![a + b, d, 0; d, a - b, 0; 0, 0, -2 * a]

def binaryQuadrupoleD1 (μ r ω t : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  let a := μ * r ^ 2 * ω
  orbitalHarmonic 0 (-a * Real.sin (2 * ω * t)) (a * Real.cos (2 * ω * t))

def binaryQuadrupoleD2 (μ r ω t : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  let a := 2 * μ * r ^ 2 * ω ^ 2
  orbitalHarmonic 0 (-a * Real.cos (2 * ω * t)) (-a * Real.sin (2 * ω * t))

def binaryQuadrupoleD3 (μ r ω t : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  let a := 4 * μ * r ^ 2 * ω ^ 3
  orbitalHarmonic 0 (a * Real.sin (2 * ω * t)) (-a * Real.cos (2 * ω * t))

private theorem binaryQuadrupole_harmonic (μ r ω t : ℝ) :
    binaryQuadrupole μ r ω t =
      orbitalHarmonic (μ * r ^ 2 / 6) (μ * r ^ 2 / 2 * Real.cos (2 * ω * t))
        (μ * r ^ 2 / 2 * Real.sin (2 * ω * t)) := by
  ext i j
  rw [show 2 * ω * t = 2 * (ω * t) by ring, Real.cos_two_mul, Real.sin_two_mul]
  fin_cases i <;> fin_cases j <;> norm_num [binaryQuadrupole, orbitalHarmonic, Matrix.one_apply]
  all_goals ring_nf
  linear_combination μ * r ^ 2 * Real.sin_sq_add_cos_sq (ω * t)

theorem binaryQuadrupole_symmetric (μ r ω t : ℝ) :
    (binaryQuadrupole μ r ω t)ᵀ = binaryQuadrupole μ r ω t := by
  rw [binaryQuadrupole_harmonic]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem binaryQuadrupole_traceless (μ r ω t : ℝ) :
    Matrix.trace (binaryQuadrupole μ r ω t) = 0 := by
  rw [binaryQuadrupole_harmonic, orbitalHarmonic, Matrix.trace_fin_three_of]
  ring

private theorem orbitalHarmonic_hasDerivAt {b d : ℝ → ℝ} {a b' d' t : ℝ}
    (hb : HasDerivAt b b' t) (hd : HasDerivAt d d' t) (i j : Fin 3) :
    HasDerivAt (fun u => orbitalHarmonic a (b u) (d u) i j)
      (orbitalHarmonic 0 b' d' i j) t := by
  fin_cases i <;> fin_cases j <;> dsimp [orbitalHarmonic] <;>
    first | exact (hasDerivAt_const t a).add hb
          | exact (hasDerivAt_const t a).sub hb
          | exact hd
          | exact hasDerivAt_const t _
          | simpa using hasDerivAt_const t (-2 * a)

private theorem sin_double_orbit_deriv (ω t : ℝ) :
    HasDerivAt (fun u : ℝ => Real.sin (2 * ω * u)) (Real.cos (2 * ω * t) * (2 * ω)) t := by
  simpa using ((hasDerivAt_id t).const_mul (2 * ω)).sin

private theorem cos_double_orbit_deriv (ω t : ℝ) :
    HasDerivAt (fun u : ℝ => Real.cos (2 * ω * u)) (-Real.sin (2 * ω * t) * (2 * ω)) t := by
  simpa using ((hasDerivAt_id t).const_mul (2 * ω)).cos

theorem binaryQuadrupole_hasDerivAt_1 (μ r ω t : ℝ) (i j : Fin 3) :
    HasDerivAt (fun u => binaryQuadrupole μ r ω u i j) (binaryQuadrupoleD1 μ r ω t i j) t := by
  simp_rw [binaryQuadrupole_harmonic]
  have hb := (cos_double_orbit_deriv ω t).const_mul (μ * r ^ 2 / 2)
  have hd := (sin_double_orbit_deriv ω t).const_mul (μ * r ^ 2 / 2)
  refine (orbitalHarmonic_hasDerivAt hb hd i j).congr_deriv ?_
  unfold binaryQuadrupoleD1
  congr 1 <;> ring

theorem binaryQuadrupole_hasDerivAt_2 (μ r ω t : ℝ) (i j : Fin 3) :
    HasDerivAt (fun u => binaryQuadrupoleD1 μ r ω u i j) (binaryQuadrupoleD2 μ r ω t i j) t := by
  have hb := (sin_double_orbit_deriv ω t).const_mul (-(μ * r ^ 2 * ω))
  have hd := (cos_double_orbit_deriv ω t).const_mul (μ * r ^ 2 * ω)
  refine (orbitalHarmonic_hasDerivAt hb hd i j).congr_deriv ?_
  unfold binaryQuadrupoleD2
  congr 1 <;> ring

theorem binaryQuadrupole_hasDerivAt_3 (μ r ω t : ℝ) (i j : Fin 3) :
    HasDerivAt (fun u => binaryQuadrupoleD2 μ r ω u i j) (binaryQuadrupoleD3 μ r ω t i j) t := by
  have hb := (cos_double_orbit_deriv ω t).const_mul (-(2 * μ * r ^ 2 * ω ^ 2))
  have hd := (sin_double_orbit_deriv ω t).const_mul (-(2 * μ * r ^ 2 * ω ^ 2))
  refine (orbitalHarmonic_hasDerivAt hb hd i j).congr_deriv ?_
  unfold binaryQuadrupoleD3
  congr 1 <;> ring

theorem binaryQuadrupole_third_deriv_norm_sq (μ r ω t : ℝ) :
    ∑ i : Fin 3, ∑ j : Fin 3, (binaryQuadrupoleD3 μ r ω t i j) ^ 2 =
      32 * μ ^ 2 * r ^ 4 * ω ^ 6 := by
  simp [Fin.sum_univ_three, binaryQuadrupoleD3, orbitalHarmonic]
  linear_combination 32 * μ ^ 2 * r ^ 4 * ω ^ 6 * Real.sin_sq_add_cos_sq (2 * ω * t)

def chirpMass (m₁ m₂ : ℝ) : ℝ := (m₁ * m₂) ^ (3 / 5 : ℝ) / (m₁ + m₂) ^ (1 / 5 : ℝ)

def quadrupolePower (G c μ r ω : ℝ) : ℝ :=
  (G / (5 * c ^ 5)) * (32 * μ ^ 2 * r ^ 4 * ω ^ 6)

def pmPower (G c m₁ m₂ r : ℝ) : ℝ :=
  (32 / 5 : ℝ) * (G ^ 4 / c ^ 5) * (m₁ ^ 2 * m₂ ^ 2 * (m₁ + m₂) / r ^ 5)

theorem peters_mathews_circular_power {G c m₁ m₂ r ω : ℝ}
    (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hr : 0 < r) (hG : 0 < G) (hc : 0 < c)
    (hω : ω ^ 2 = G * (m₁ + m₂) / r ^ 3) :
    quadrupolePower G c (m₁ * m₂ / (m₁ + m₂)) r ω = pmPower G c m₁ m₂ r := by
  have hM : 0 < m₁ + m₂ := add_pos hm₁ hm₂
  have hG0 : G ≠ 0 := hG.ne'
  rw [quadrupolePower, pmPower, show ω ^ 6 = (ω ^ 2) ^ 3 by ring, hω]
  field_simp [hM.ne', hr.ne', hc.ne', hG0]

private theorem pow_rpow (a : ℝ) (ha : 0 ≤ a) (n : ℕ) (p : ℝ) :
    (a ^ n) ^ p = a ^ ((n : ℝ) * p) := by
  rw [Real.rpow_mul ha, Real.rpow_natCast]

private theorem chirpMass_rpow_five_thirds {m₁ m₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) :
    chirpMass m₁ m₂ ^ (5 / 3 : ℝ) = m₁ * m₂ / (m₁ + m₂) ^ (1 / 3 : ℝ) := by
  unfold chirpMass
  rw [Real.div_rpow (by positivity) (by positivity),
    ← Real.rpow_mul (by positivity : 0 ≤ m₁ * m₂),
    ← Real.rpow_mul (by positivity : 0 ≤ m₁ + m₂)]
  norm_num

theorem peters_mathews_chirp_power {G c m₁ m₂ r ω : ℝ}
    (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hr : 0 < r) (hG : 0 < G) (hc : 0 < c)
    (hω : ω = Real.sqrt (G * (m₁ + m₂) / r ^ 3)) :
    quadrupolePower G c (m₁ * m₂ / (m₁ + m₂)) r ω =
      (32 / 5 : ℝ) * (c ^ 5 / G) * (G * chirpMass m₁ m₂ * ω / c ^ 3) ^ (10 / 3 : ℝ) := by
  have hM : 0 < m₁ + m₂ := add_pos hm₁ hm₂
  have hMc : 0 < chirpMass m₁ m₂ := by unfold chirpMass; positivity
  have hω2 : ω ^ 2 = G * (m₁ + m₂) / r ^ 3 := by rw [hω, Real.sq_sqrt (by positivity)]
  have hω0 : 0 ≤ ω := hω.symm ▸ Real.sqrt_nonneg _
  have hωp : (ω ^ (5 / 3 : ℝ)) ^ 2 = (G * (m₁ + m₂) / r ^ 3) ^ (5 / 3 : ℝ) := by
    rw [Real.rpow_pow_comm hω0, hω2]
  rw [peters_mathews_circular_power hm₁ hm₂ hr hG hc hω2, pmPower,
    show (10 / 3 : ℝ) = (5 / 3 : ℝ) * 2 by norm_num,
    Real.rpow_mul (by positivity), Real.rpow_two,
    Real.div_rpow (by positivity) (by positivity),
    Real.mul_rpow (by positivity) hω0,
    Real.mul_rpow hG.le hMc.le,
    chirpMass_rpow_five_thirds hm₁ hm₂,
    pow_rpow c hc.le, show (↑(3 : ℕ) : ℝ) * (5 / 3) = 5 by norm_num, Real.rpow_ofNat,
    div_pow, mul_pow, mul_pow, hωp,
    Real.div_rpow (by positivity) (by positivity), Real.mul_rpow hG.le hM.le,
    pow_rpow r hr.le, show (↑(3 : ℕ) : ℝ) * (5 / 3) = 5 by norm_num, Real.rpow_ofNat,
    div_pow, ← Real.rpow_natCast ((m₁ + m₂) ^ (1 / 3 : ℝ)) 2,
    ← Real.rpow_mul hM.le, ← Real.rpow_natCast (G ^ (5 / 3 : ℝ)) 2,
    ← Real.rpow_mul hG.le]
  rw [show (5 / 3 : ℝ) * ↑(2 : ℕ) = 10 / 3 by norm_num,
    show (1 / 3 : ℝ) * ↑(2 : ℕ) = 2 / 3 by norm_num,
    show (10 / 3 : ℝ) = 5 - 5 / 3 by norm_num,
    Real.rpow_sub hG, Real.rpow_ofNat,
    show (5 / 3 : ℝ) = (2 / 3 : ℝ) + 1 by norm_num,
    Real.rpow_add hM, Real.rpow_one]
  have hc10 : c ^ 5 ≠ 0 := pow_ne_zero _ hc.ne'
  have hr5 : r ^ 5 ≠ 0 := pow_ne_zero _ hr.ne'
  have hgpow : G ^ (5 / 3 : ℝ) ≠ 0 := ne_of_gt (by positivity)
  have hmpow : (m₁ + m₂) ^ (2 / 3 : ℝ) ≠ 0 := ne_of_gt (by positivity)
  field_simp [hG.ne', hc10, hr5, hgpow, hmpow]

theorem chirpMass_le_equal_mass {m₁ m₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) :
    chirpMass m₁ m₂ ≤ (m₁ + m₂) * (2 : ℝ) ^ (-(6 / 5 : ℝ)) ∧
      (chirpMass m₁ m₂ = (m₁ + m₂) * (2 : ℝ) ^ (-(6 / 5 : ℝ)) ↔ m₁ = m₂) := by
  have hM : 0 < m₁ + m₂ := add_pos hm₁ hm₂
  have hden : 0 < (m₁ + m₂) ^ (1 / 5 : ℝ) := by positivity
  have hhalf : 0 ≤ (m₁ + m₂) / 2 := by positivity
  have hscale : (((m₁ + m₂) / 2) ^ 2) ^ (3 / 5 : ℝ) / (m₁ + m₂) ^ (1 / 5 : ℝ) =
      (m₁ + m₂) * (2 : ℝ) ^ (-(6 / 5 : ℝ)) := by
    rw [pow_rpow _ hhalf, show (↑(2 : ℕ) : ℝ) * (3 / 5) = 6 / 5 by norm_num,
      Real.div_rpow hM.le (by norm_num : (0 : ℝ) ≤ 2), div_right_comm,
      ← Real.rpow_sub hM, show (6 / 5 : ℝ) - 1 / 5 = 1 by norm_num,
      Real.rpow_one, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_eq_mul_inv]
  have hgap : ((m₁ + m₂) / 2) ^ 2 - m₁ * m₂ = (m₁ - m₂) ^ 2 / 4 := by ring
  have hle : m₁ * m₂ ≤ ((m₁ + m₂) / 2) ^ 2 := by linarith [sq_nonneg (m₁ - m₂)]
  rw [← hscale]
  unfold chirpMass
  refine ⟨div_le_div_of_nonneg_right (Real.rpow_le_rpow (by positivity) hle (by norm_num))
    hden.le, ?_⟩
  constructor
  · intro he
    by_contra hne
    have hlt : m₁ * m₂ < ((m₁ + m₂) / 2) ^ 2 :=
      lt_of_le_of_ne hle (fun hp => (pow_ne_zero 2 (sub_ne_zero.mpr hne)) (by linarith))
    exact (ne_of_lt (div_lt_div_of_pos_right
      (Real.rpow_lt_rpow (by positivity) hlt (by norm_num : 0 < (3 / 5 : ℝ))) hden)) he
  · rintro rfl
    rw [show ((m₁ + m₁) / 2) ^ 2 = m₁ * m₁ by ring]

def orbitalEnergy (G m₁ m₂ r : ℝ) : ℝ := -(G * m₁ * m₂) / (2 * r)

def coalescenceTime (G c m₁ m₂ r₀ : ℝ) : ℝ :=
  (5 * c ^ 5 * r₀ ^ 4) / (256 * G ^ 3 * m₁ * m₂ * (m₁ + m₂))

def inspiralRadius (r₀ Tc t : ℝ) : ℝ := r₀ * (1 - t / Tc) ^ (1 / 4 : ℝ)

private theorem inspiralRadius_pos {r₀ Tc t : ℝ} (hr₀ : 0 < r₀) (hT : 0 < Tc)
    (ht : t < Tc) : 0 < inspiralRadius r₀ Tc t :=
  mul_pos hr₀ (Real.rpow_pos_of_pos (sub_pos.mpr ((div_lt_one hT).mpr ht)) _)

theorem inspiralRadius_hasDerivAt {G c m₁ m₂ r₀ Tc t : ℝ}
    (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hr₀ : 0 < r₀) (hG : 0 < G) (hc : 0 < c)
    (hTc : Tc = coalescenceTime G c m₁ m₂ r₀) (ht : t < Tc) :
    HasDerivAt (inspiralRadius r₀ Tc)
      (-(64 / 5 : ℝ) * (G ^ 3 * m₁ * m₂ * (m₁ + m₂)) /
        (c ^ 5 * inspiralRadius r₀ Tc t ^ 3)) t := by
  have hT : 0 < Tc := by rw [hTc]; unfold coalescenceTime; positivity
  have hq : 0 < 1 - t / Tc := sub_pos.mpr ((div_lt_one hT).mpr ht)
  have he := (hasDerivAt_const t (1 : ℝ)).sub ((hasDerivAt_id t).div_const Tc)
  have hd := (he.rpow_const (p := (1 / 4 : ℝ)) (Or.inl hq.ne')).const_mul r₀
  refine hd.congr_deriv ?_
  simp only [id_eq, Pi.sub_apply, zero_sub]
  rw [show (1 / 4 : ℝ) - 1 = -((1 / 4 : ℝ) * 3) by norm_num,
    Real.rpow_neg hq.le, Real.rpow_mul hq.le, Real.rpow_ofNat,
    inspiralRadius, mul_pow]
  have hqp : 0 < (1 - t / Tc) ^ (1 / 4 : ℝ) := by positivity
  have hinv : Tc⁻¹ = 256 * G ^ 3 * m₁ * m₂ * (m₁ + m₂) / (5 * c ^ 5 * r₀ ^ 4) := by
    rw [hTc, coalescenceTime, inv_div]
  rw [show -(1 / Tc) = -Tc⁻¹ by simp, hinv]
  field_simp [hc.ne', hr₀.ne', hqp.ne']
  ring

theorem inspiral_satisfies_energy_balance {G c m₁ m₂ r₀ Tc t : ℝ}
    (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hr₀ : 0 < r₀) (hG : 0 < G) (hc : 0 < c)
    (hTc : Tc = coalescenceTime G c m₁ m₂ r₀) (ht : t < Tc) :
    HasDerivAt (fun s => orbitalEnergy G m₁ m₂ (inspiralRadius r₀ Tc s))
      (-pmPower G c m₁ m₂ (inspiralRadius r₀ Tc t)) t := by
  have hT : 0 < Tc := by rw [hTc]; unfold coalescenceTime; positivity
  have hr := inspiralRadius_pos hr₀ hT ht
  have hd := inspiralRadius_hasDerivAt hm₁ hm₂ hr₀ hG hc hTc ht
  have he := (hasDerivAt_const t (-(G * m₁ * m₂))).div (hd.const_mul 2) (by positivity)
  refine he.congr_deriv ?_
  unfold pmPower
  field_simp [hr.ne', hc.ne']
  ring

theorem inspiral_coalescence_limit {r₀ Tc : ℝ} (_hr₀ : 0 < r₀) (hT : 0 < Tc) :
    inspiralRadius r₀ Tc 0 = r₀ ∧ Tendsto (inspiralRadius r₀ Tc) (𝓝[<] Tc) (𝓝 0) := by
  constructor
  · simp [inspiralRadius]
  have hf : Continuous (fun u : ℝ => r₀ * (1 - u / Tc) ^ (1 / 4 : ℝ)) :=
    continuous_const.mul <| (continuous_const.sub (continuous_id.div_const Tc)).rpow_const
      (fun _ => Or.inr (by norm_num))
  have hzero : inspiralRadius r₀ Tc Tc = 0 := by
    simp [inspiralRadius, hT.ne']
  rw [← hzero]
  exact hf.continuousAt.continuousWithinAt

def gwFreq (G m₁ m₂ r : ℝ) : ℝ := Real.sqrt (G * (m₁ + m₂) / r ^ 3) / Real.pi

private theorem gwFreq_rpow {G m₁ m₂ r : ℝ}
    (hM : 0 < G * (m₁ + m₂)) (hr : 0 < r) :
    gwFreq G m₁ m₂ r = (G * (m₁ + m₂)) ^ (1 / 2 : ℝ) / Real.pi * r ^ (-(3 / 2 : ℝ)) := by
  rw [gwFreq, Real.sqrt_eq_rpow, Real.div_rpow hM.le (by positivity),
    pow_rpow r hr.le, show (↑(3 : ℕ) : ℝ) * (1 / 2) = 3 / 2 by norm_num,
    Real.rpow_neg hr.le, div_div, div_eq_mul_inv, mul_inv_rev]
  ring

private theorem gw_chirp_coefficient {G c m₁ m₂ r : ℝ}
    (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hr : 0 < r) (hG : 0 < G) (hc : 0 < c) :
    (96 / 5 : ℝ) * ((G * (m₁ + m₂)) ^ (1 / 2 : ℝ) / Real.pi) *
      (G ^ 3 * m₁ * m₂ * (m₁ + m₂) / c ^ 5) * r ^ (-(11 / 2 : ℝ)) =
    (96 / 5 : ℝ) * Real.pi ^ (8 / 3 : ℝ) *
      (G * chirpMass m₁ m₂ / c ^ 3) ^ (5 / 3 : ℝ) * (gwFreq G m₁ m₂ r) ^ (11 / 3 : ℝ) := by
  have hM : 0 < m₁ + m₂ := add_pos hm₁ hm₂
  have hMc : 0 < chirpMass m₁ m₂ := by unfold chirpMass; positivity
  have hGexp : G ^ (5 / 3 : ℝ) * G ^ (11 / 6 : ℝ) = G ^ (1 / 2 : ℝ) * G ^ 3 := by
    rw [← Real.rpow_ofNat G 3, ← Real.rpow_add hG, ← Real.rpow_add hG]
    congr 1
    norm_num
  have hMexp : (m₁ + m₂) ^ (11 / 6 : ℝ) / (m₁ + m₂) ^ (1 / 3 : ℝ) =
      (m₁ + m₂) ^ (1 / 2 : ℝ) * (m₁ + m₂) := by
    rw [← Real.rpow_sub hM, ← Real.rpow_add_one hM.ne']
    congr 1
    norm_num
  have hpi : Real.pi ^ (8 / 3 : ℝ) / Real.pi ^ (11 / 3 : ℝ) = Real.pi⁻¹ := by
    rw [← Real.rpow_sub Real.pi_pos, show (8 / 3 : ℝ) - 11 / 3 = -1 by norm_num, Real.rpow_neg_one]
  have hf : (gwFreq G m₁ m₂ r) ^ (11 / 3 : ℝ) =
      (G * (m₁ + m₂)) ^ (11 / 6 : ℝ) / Real.pi ^ (11 / 3 : ℝ) * r ^ (-(11 / 2 : ℝ)) := by
    rw [gwFreq_rpow (by positivity) hr,
      Real.mul_rpow (x := (G * (m₁ + m₂)) ^ (1 / 2 : ℝ) / Real.pi)
        (by positivity) (by positivity),
      Real.div_rpow (by positivity) Real.pi_pos.le,
      ← Real.rpow_mul (by positivity : 0 ≤ G * (m₁ + m₂)),
      ← Real.rpow_mul hr.le, show (1 / 2 : ℝ) * (11 / 3) = 11 / 6 by norm_num,
      show -(3 / 2 : ℝ) * (11 / 3) = -(11 / 2) by norm_num]
  rw [hf, Real.div_rpow (by positivity) (by positivity), Real.mul_rpow hG.le hMc.le,
    chirpMass_rpow_five_thirds hm₁ hm₂, pow_rpow c hc.le,
    show (↑(3 : ℕ) : ℝ) * (5 / 3) = 5 by norm_num, Real.rpow_ofNat,
    Real.mul_rpow hG.le hM.le, Real.mul_rpow hG.le hM.le]
  calc
    _ = (96 / 5 : ℝ) * (Real.pi ^ (8 / 3 : ℝ) / Real.pi ^ (11 / 3 : ℝ)) *
        (G ^ (5 / 3 : ℝ) * G ^ (11 / 6 : ℝ)) *
        ((m₁ + m₂) ^ (11 / 6 : ℝ) / (m₁ + m₂) ^ (1 / 3 : ℝ)) *
        (m₁ * m₂ / c ^ 5) * r ^ (-(11 / 2 : ℝ)) := by rw [hpi, hGexp, hMexp]; ring
    _ = _ := by ring

theorem gw_chirp_frequency_ode {G c m₁ m₂ r₀ Tc t : ℝ}
    (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hr₀ : 0 < r₀) (hG : 0 < G) (hc : 0 < c)
    (hTc : Tc = coalescenceTime G c m₁ m₂ r₀) (ht : t < Tc) :
    let f := fun s => gwFreq G m₁ m₂ (inspiralRadius r₀ Tc s)
    HasDerivAt f ((96 / 5 : ℝ) * Real.pi ^ (8 / 3 : ℝ) *
      (G * chirpMass m₁ m₂ / c ^ 3) ^ (5 / 3 : ℝ) * (f t) ^ (11 / 3 : ℝ)) t := by
  have hT : 0 < Tc := by rw [hTc]; unfold coalescenceTime; positivity
  have hr := inspiralRadius_pos hr₀ hT ht
  have hM : 0 < G * (m₁ + m₂) := by positivity
  have hd := inspiralRadius_hasDerivAt hm₁ hm₂ hr₀ hG hc hTc ht
  have hf := (hd.rpow_const (p := -(3 / 2 : ℝ)) (Or.inl hr.ne')).const_mul
    ((G * (m₁ + m₂)) ^ (1 / 2 : ℝ) / Real.pi)
  refine (hf.congr_of_eventuallyEq ?_).congr_deriv ?_
  · exact (eventually_lt_nhds ht).mono fun s hs =>
      gwFreq_rpow hM (inspiralRadius_pos hr₀ hT hs)
  · rw [← gw_chirp_coefficient hm₁ hm₂ hr hG hc,
      show -(3 / 2 : ℝ) - 1 = -(5 / 2) by norm_num,
      show -(11 / 2 : ℝ) = -(5 / 2) - 3 by norm_num,
      Real.rpow_sub hr, Real.rpow_ofNat]
    ring

theorem gw_chirp_frequency_inv_power_linear {G m₁ m₂ r₀ Tc t : ℝ}
    (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hr₀ : 0 < r₀) (hG : 0 < G) (hT : 0 < Tc)
    (ht : t < Tc) :
    let f := fun s => gwFreq G m₁ m₂ (inspiralRadius r₀ Tc s)
    (f t) ^ (-(8 / 3 : ℝ)) = (f 0) ^ (-(8 / 3 : ℝ)) * (1 - t / Tc) := by
  have hM : 0 < G * (m₁ + m₂) := by positivity
  have hq : 0 < 1 - t / Tc := sub_pos.mpr ((div_lt_one hT).mpr ht)
  have hr := inspiralRadius_pos hr₀ hT ht
  have hpow (r : ℝ) (h : 0 < r) :
      (gwFreq G m₁ m₂ r) ^ (-(8 / 3 : ℝ)) =
        ((G * (m₁ + m₂)) ^ (1 / 2 : ℝ) / Real.pi) ^ (-(8 / 3 : ℝ)) * r ^ 4 := by
    rw [gwFreq_rpow hM h, Real.mul_rpow (by positivity) (by positivity),
      ← Real.rpow_mul h.le, show -(3 / 2 : ℝ) * -(8 / 3) = 4 by norm_num,
      Real.rpow_ofNat]
  have hq4 : ((1 - t / Tc) ^ (1 / 4 : ℝ)) ^ 4 = 1 - t / Tc := by
    rw [← Real.rpow_ofNat _ 4, ← Real.rpow_mul hq.le]
    norm_num
  dsimp only
  rw [hpow _ hr, (inspiral_coalescence_limit hr₀ hT).1, hpow _ hr₀, inspiralRadius, mul_pow, hq4]
  ring

end D5.S3.Geometry.Lorentz.GRLinearizedWavesQuadrupole4D
