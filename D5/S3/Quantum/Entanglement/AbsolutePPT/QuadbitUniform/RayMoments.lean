/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/RayMoments
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/RayMoments
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniformSpectralBound.three_row_scalar_bound; instance=D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/SpectrumCompression.A
   digest: Original ray labels, exact step moments and scalar certificate interpretation. -/

import D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.ScalarEnvelopes
import D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.SpectrumCompression

set_option autoImplicit false

namespace D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound
open scoped BigOperators Matrix
open Finset Matrix
open UniformSpectralBound.SharedSpectral
noncomputable section

inductive RayBranch where
  | boundary | envelope₁ | envelope₂ | bulk
  deriving DecidableEq

structure RayData where
  gap : Fin 16 → ℕ
  u : ℤ
  v : ℤ
  c : ℤ
  C : ℤ
  branch : RayBranch

/- These are exactly the coefficients of the ORIGINAL ordered positions
   (1,2,3,4,5,j,N-9,N-8,...,N). No duplicate columns are removed. -/
private def positionN : Fin 16 → ℤ := ![0,0,0,0,0,0,1,1,1,1,1,1,1,1,1,1]
private def positionJ : Fin 16 → ℤ := ![0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0]
private def positionC : Fin 16 → ℤ := ![1,2,3,4,5,0,-9,-8,-7,-6,-5,-4,-3,-2,-1,0]
def positions₁₆ (N j : ℕ) : Fin 16 → ℕ :=
  ![1,2,3,4,5,j,N-9,N-8,N-7,N-6,N-5,N-4,N-3,N-2,N-1,N]

private def massMoment (r : RayData) (p : Fin 16 → ℤ) : ℤ :=
  ∑ i, (r.gap i : ℤ)*p i
private def squareMoment (r : RayData) (p : Fin 16 → ℤ) : ℤ :=
  ∑ i, ∑ k, (r.gap i : ℤ)*(r.gap k : ℤ)*p (min i k)

def MomentWitness (r : RayData) : Prop :=
  massMoment r positionN = r.u ∧
  massMoment r positionJ = r.v ∧
  massMoment r positionC = r.c ∧
  squareMoment r positionN = r.u^2 ∧
  squareMoment r positionJ = r.v^2+2*r.u*r.v ∧
  squareMoment r positionC = r.C

def branchValid (r : RayData) : Prop :=
  match r.branch with
  | .boundary => r.v = 0 ∧ boundaryCertificate (r.u : ℝ) (r.c : ℝ) (r.C : ℝ)
  | .envelope₁ => 0 < (r.v : ℝ) ∧
      middleCertificate 25 24 (-24) (r.u : ℝ) (r.v : ℝ) (r.c : ℝ) (r.C : ℝ)
  | .envelope₂ => 0 < (r.v : ℝ) ∧
      middleCertificate 36 35 (-80) (r.u : ℝ) (r.v : ℝ) (r.c : ℝ) (r.C : ℝ)
  | .bulk => r.u = 3 ∧ r.v = 2 ∧ r.c = 0 ∧ r.C = 0

structure RayData.Valid (r : RayData) : Prop where
  u_nonneg : 0 ≤ (r.u : ℝ)
  v_nonneg : 0 ≤ (r.v : ℝ)
  mass67_pos : 0 < 67*(r.u : ℝ)+6*(r.v : ℝ)+(r.c : ℝ)
  moments : MomentWitness r
  branch_valid : branchValid r

private def rayMass (r : RayData) (N j : ℝ) : ℝ := (r.u : ℝ)*N+(r.v : ℝ)*j+(r.c : ℝ)
private def raySquare (r : RayData) (N j : ℝ) : ℝ :=
  (r.u : ℝ)^2*N+((r.v : ℝ)^2+2*(r.u : ℝ)*(r.v : ℝ))*j+(r.C : ℝ)

lemma ray_mass_positive (r : RayData) (hr : r.Valid) (N j : ℝ)
    (hN : 67 ≤ N) (hj : 6 ≤ j) : 0 < rayMass r N j := by
  have h1 := mul_nonneg hr.u_nonneg (sub_nonneg.mpr hN)
  have h2 := mul_nonneg hr.v_nonneg (sub_nonneg.mpr hj)
  dsimp [rayMass]
  nlinarith only [h1, h2, hr.mass67_pos]

private lemma ray_nonbulk_le_common (r : RayData) (hr : r.Valid) (N j : ℝ)
    (hN : 67 ≤ N) (hj : 6 ≤ j) (hne : r.branch ≠ .bulk) :
    raySquare r N j/(rayMass r N j)^2 ≤ commonEnvelope N := by
  have hM := ray_mass_positive r hr N j hN hj
  have hc := hr.branch_valid
  cases hb : r.branch with
  | boundary =>
      simp only [branchValid, hb] at hc
      obtain ⟨hv, hcert⟩ := hc
      have hM' : 0 < (r.u : ℝ)*N+(r.c : ℝ) := by simpa [rayMass, hv] using hM
      have h := boundary_ray_bound N (r.u : ℝ) (r.c : ℝ) (r.C : ℝ) hN hM' hcert
      have h' : raySquare r N j/(rayMass r N j)^2 ≤ boundaryEnvelope N := by
        simpa [raySquare, rayMass, hv] using h
      exact h'.trans (boundary_envelope_le_common N hN)
  | envelope₁ =>
      simp only [branchValid, hb] at hc
      obtain ⟨hv, hcert⟩ := hc
      have hh : 0 < 2*(r.u : ℝ)+(r.v : ℝ) := by linarith [hr.u_nonneg]
      have hD : 0 < 24*N+(-24) := by linarith
      have h := middle_ray_envelope N j 25 24 (-24) (r.u : ℝ) (r.v : ℝ)
        (r.c : ℝ) (r.C : ℝ) hN (by norm_num) hD hh hM hcert
      have h' : raySquare r N j/(rayMass r N j)^2 ≤ middleEnvelope₁ N := by
        have hden : 24*N+(-24 : ℝ) = 24*(N-1) := by ring
        rw [hden] at h
        exact h
      exact h'.trans (middle_envelope₁_le_common N hN)
  | envelope₂ =>
      simp only [branchValid, hb] at hc
      obtain ⟨hv, hcert⟩ := hc
      have hh : 0 < 2*(r.u : ℝ)+(r.v : ℝ) := by linarith [hr.u_nonneg]
      have hD : 0 < 35*N+(-80) := by linarith
      have h := middle_ray_envelope N j 36 35 (-80) (r.u : ℝ) (r.v : ℝ)
        (r.c : ℝ) (r.C : ℝ) hN (by norm_num) hD hh hM hcert
      have h' : raySquare r N j/(rayMass r N j)^2 ≤ middleEnvelope₂ N := by
        simpa only [raySquare, rayMass, middleEnvelope₂, sub_eq_add_neg] using h
      exact h'.trans (middle_envelope₂_le_common N hN)
  | bulk => exact False.elim (hne hb)

private lemma ray_scalar_bound (r : RayData) (hr : r.Valid) (N j : ℕ)
    (hN : 67 ≤ N) (hj : 6 ≤ j) :
    raySquare r (N : ℝ) (j : ℝ) ≤
      bulkValue (N : ℝ) (bulkIndex N : ℝ)*(rayMass r (N : ℝ) (j : ℝ))^2 := by
  have hn : (67 : ℝ) ≤ N := by exact_mod_cast hN
  have hjR : (6 : ℝ) ≤ j := by exact_mod_cast hj
  have hM := ray_mass_positive r hr (N : ℝ) (j : ℝ) hn hjR
  apply (div_le_iff₀ (sq_pos_of_pos hM)).1
  by_cases hb : r.branch = .bulk
  · have hc := hr.branch_valid
    simp only [branchValid, hb] at hc
    obtain ⟨hu, hv, hc, hC⟩ := hc
    have he : raySquare r (N : ℝ) (j : ℝ)/(rayMass r (N : ℝ) (j : ℝ))^2 =
        bulkValue (N : ℝ) (j : ℝ) := by
      norm_num [raySquare, rayMass, hu, hv, hc, hC, bulkValue]
    rw [he]
    exact bulk_integer_maximum N j hN
  · exact (ray_nonbulk_le_common r hr (N : ℝ) (j : ℝ) hn hjR hb).trans
      (common_le_integer_bulk N hN)

lemma positions₁₆_le (N j : ℕ) (hN : 67 ≤ N) (hj : j ≤ N-10) :
    ∀ i, positions₁₆ N j i ≤ N := by
  intro i
  fin_cases i <;> simp [positions₁₆] <;> omega

private lemma positions₁₆_monotone (N j : ℕ) (hN : 67 ≤ N) (hl : 6 ≤ j) (hu : j ≤ N-10) :
    Monotone (positions₁₆ N j) := by
  have he : positions N j = positions₁₆ N j := by
    rw [positions_literal N j hN]
    rfl
  rw [← he]
  exact (positions_strict N j hN hl hu).monotone

private lemma positions₁₆_cast (N j : ℕ) (hN : 67 ≤ N) (i : Fin 16) :
    (positions₁₆ N j i : ℝ) =
      (positionN i : ℝ)*(N : ℝ)+(positionJ i : ℝ)*(j : ℝ)+(positionC i : ℝ) := by
  fin_cases i <;> simp only [positions₁₆, positionN, positionJ, positionC,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one]
  all_goals push_cast [show 9 ≤ N from by omega, show 8 ≤ N from by omega,
    show 7 ≤ N from by omega, show 6 ≤ N from by omega, show 5 ≤ N from by omega,
    show 4 ≤ N from by omega, show 3 ≤ N from by omega, show 2 ≤ N from by omega,
    show 1 ≤ N from by omega]
  all_goals ring

private lemma mass_moment_real (r : RayData) (p : Fin 16 → ℤ) (z : ℤ)
    (h : massMoment r p = z) : ∑ i, (r.gap i : ℝ)*(p i : ℝ) = (z : ℝ) := by
  dsimp [massMoment] at h
  exact_mod_cast h

private lemma square_moment_real (r : RayData) (p : Fin 16 → ℤ) (z : ℤ)
    (h : squareMoment r p = z) :
    ∑ i, ∑ k, (r.gap i : ℝ)*(r.gap k : ℝ)*(p (min i k) : ℝ) = (z : ℝ) := by
  dsimp [squareMoment] at h
  exact_mod_cast h

lemma ray_mass_identity (r : RayData) (hr : MomentWitness r) (N j : ℕ) (hN : 67 ≤ N) :
    (∑ i, (r.gap i : ℝ)*(positions₁₆ N j i : ℝ)) = rayMass r (N : ℝ) (j : ℝ) := by
  obtain ⟨hu, hv, hc, _, _, _⟩ := hr
  have huR := mass_moment_real r positionN r.u hu
  have hvR := mass_moment_real r positionJ r.v hv
  have hcR := mass_moment_real r positionC r.c hc
  simp_rw [positions₁₆_cast N j hN]
  calc
    _ = (∑ i, (r.gap i : ℝ)*(positionN i : ℝ))*(N : ℝ) +
        (∑ i, (r.gap i : ℝ)*(positionJ i : ℝ))*(j : ℝ) +
        (∑ i, (r.gap i : ℝ)*(positionC i : ℝ)) := by
          simp only [mul_add, ← mul_assoc, Finset.sum_add_distrib, Finset.sum_mul]
    _ = _ := by rw [huR, hvR, hcR]; rfl

private lemma ray_square_identity (r : RayData) (hr : MomentWitness r) (N j : ℕ)
    (hN : 67 ≤ N) (hl : 6 ≤ j) (hu : j ≤ N-10) :
    (∑ i, ∑ k, (r.gap i : ℝ)*(r.gap k : ℝ)*
      (min (positions₁₆ N j i) (positions₁₆ N j k) : ℕ)) = raySquare r (N : ℝ) (j : ℝ) := by
  obtain ⟨_, _, _, hN₂, hj₂, hC₂⟩ := hr
  have hN₂R : ∑ i, ∑ k, (r.gap i : ℝ)*(r.gap k : ℝ)*(positionN (min i k) : ℝ) = (r.u : ℝ)^2 := by
    have h := square_moment_real r positionN (r.u^2) hN₂
    simpa using h
  have hj₂R : ∑ i, ∑ k, (r.gap i : ℝ)*(r.gap k : ℝ)*(positionJ (min i k) : ℝ) =
      (r.v : ℝ)^2+2*(r.u : ℝ)*(r.v : ℝ) := by
    have h := square_moment_real r positionJ (r.v^2+2*r.u*r.v) hj₂
    simpa using h
  have hC₂R := square_moment_real r positionC r.C hC₂
  have hmin : ∀ i k, min (positions₁₆ N j i) (positions₁₆ N j k) = positions₁₆ N j (min i k) := by
    intro i k
    rcases le_total i k with hik | hki
    · rw [min_eq_left hik, min_eq_left (positions₁₆_monotone N j hN hl hu hik)]
    · rw [min_eq_right hki, min_eq_right (positions₁₆_monotone N j hN hl hu hki)]
  simp_rw [hmin, positions₁₆_cast N j hN]
  calc
    _ = (∑ i, ∑ k, (r.gap i : ℝ)*(r.gap k : ℝ)*(positionN (min i k) : ℝ))*(N : ℝ) +
        (∑ i, ∑ k, (r.gap i : ℝ)*(r.gap k : ℝ)*(positionJ (min i k) : ℝ))*(j : ℝ) +
        (∑ i, ∑ k, (r.gap i : ℝ)*(r.gap k : ℝ)*(positionC (min i k) : ℝ)) := by
          simp only [mul_add, ← mul_assoc, Finset.sum_add_distrib, Finset.sum_mul]
    _ = _ := by rw [hN₂R, hj₂R, hC₂R]; rfl

/- This is the exact interface for the generalized ORIGINAL square_synth and
   mass_synth lemmas; it introduces no replacement norm/step implementation. -/
lemma ray_gram_bound (r : RayData) (hr : r.Valid) (N j : ℕ)
    (hN : 67 ≤ N) (hl : 6 ≤ j) (hu : j ≤ N-10) :
    (∑ i, ∑ k, (r.gap i : ℝ)*(r.gap k : ℝ)*
      (min (positions₁₆ N j i) (positions₁₆ N j k) : ℕ)) ≤
      bulkValue (N : ℝ) (bulkIndex N : ℝ)*
        (∑ i, (r.gap i : ℝ)*(positions₁₆ N j i : ℝ))^2 := by
  rw [ray_square_identity r hr.moments N j hN hl hu, ray_mass_identity r hr.moments N j hN]
  exact ray_scalar_bound r hr N j hN hl

def originalRay (i : Fin 187) : RayData :=
  match i.val with
  | 0 => { gap := ![0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0], u := 1, v := 0, c := (-2), C := (-2), branch := .boundary }
  | 1 => { gap := ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0], u := 1, v := 0, c := (-1), C := (-1), branch := .boundary }
  | 2 => { gap := ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1], u := 1, v := 0, c := 0, C := 0, branch := .boundary }
  | 3 => { gap := ![1,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0], u := 1, v := 0, c := 0, C := 2, branch := .boundary }
  | 4 => { gap := ![2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1], u := 1, v := 0, c := 2, C := 8, branch := .boundary }
  | 5 => { gap := ![0,1,0,0,0,0,0,0,0,0,0,0,0,0,1,0], u := 1, v := 0, c := 1, C := 5, branch := .boundary }
  | 6 => { gap := ![0,3,0,0,0,0,0,0,0,0,0,0,0,0,0,2], u := 2, v := 0, c := 6, C := 42, branch := .boundary }
  | 7 => { gap := ![0,0,2,0,0,0,0,0,0,0,0,0,0,0,3,0], u := 3, v := 0, c := 3, C := 39, branch := .boundary }
  | 8 => { gap := ![0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,1], u := 1, v := 0, c := 3, C := 9, branch := .boundary }
  | 9 => { gap := ![0,0,0,2,0,0,0,0,0,0,0,0,0,0,3,0], u := 3, v := 0, c := 5, C := 55, branch := .boundary }
  | 10 => { gap := ![0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,1], u := 1, v := 0, c := 4, C := 12, branch := .boundary }
  | 11 => { gap := ![0,0,0,0,3,0,0,0,0,0,0,0,0,0,5,0], u := 5, v := 0, c := 10, C := 170, branch := .boundary }
  | 12 => { gap := ![0,0,0,0,4,0,0,0,0,0,0,0,0,0,0,5], u := 5, v := 0, c := 20, C := 280, branch := .boundary }
  | 13 => { gap := ![0,0,0,0,0,1,0,0,0,0,0,0,0,0,2,0], u := 2, v := 1, c := (-2), C := (-4), branch := .envelope₁ }
  | 14 => { gap := ![0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,3], u := 3, v := 2, c := 0, C := 0, branch := .bulk }
  | 15 => { gap := ![0,0,0,0,0,0,3,0,0,0,0,0,0,0,5,0], u := 8, v := 0, c := (-32), C := (-376), branch := .boundary }
  | 16 => { gap := ![0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,5], u := 9, v := 0, c := (-36), C := (-504), branch := .boundary }
  | 17 => { gap := ![0,0,0,0,0,0,0,2,0,0,0,0,0,0,3,0], u := 5, v := 0, c := (-19), C := (-137), branch := .boundary }
  | 18 => { gap := ![0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,1], u := 2, v := 0, c := (-8), C := (-24), branch := .boundary }
  | 19 => { gap := ![0,0,0,0,0,0,0,0,2,0,0,0,0,0,3,0], u := 5, v := 0, c := (-17), C := (-121), branch := .boundary }
  | 20 => { gap := ![0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,1], u := 2, v := 0, c := (-7), C := (-21), branch := .boundary }
  | 21 => { gap := ![0,0,0,0,0,0,0,0,0,2,0,0,0,0,3,0], u := 5, v := 0, c := (-15), C := (-105), branch := .boundary }
  | 22 => { gap := ![0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,1], u := 2, v := 0, c := (-6), C := (-18), branch := .boundary }
  | 23 => { gap := ![0,0,0,0,0,0,0,0,0,0,1,0,0,0,1,0], u := 2, v := 0, c := (-6), C := (-16), branch := .boundary }
  | 24 => { gap := ![0,0,0,0,0,0,0,0,0,0,3,0,0,0,0,2], u := 5, v := 0, c := (-15), C := (-105), branch := .boundary }
  | 25 => { gap := ![0,0,0,0,0,0,0,0,0,0,0,1,0,0,1,0], u := 2, v := 0, c := (-5), C := (-13), branch := .boundary }
  | 26 => { gap := ![0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,1], u := 3, v := 0, c := (-8), C := (-32), branch := .boundary }
  | 27 => { gap := ![0,0,0,0,0,0,0,0,0,0,0,0,1,0,1,0], u := 2, v := 0, c := (-4), C := (-10), branch := .boundary }
  | 28 => { gap := ![0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,1], u := 3, v := 0, c := (-6), C := (-24), branch := .boundary }
  | 29 => { gap := ![1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,1], u := 1, v := 0, c := 3, C := 11, branch := .boundary }
  | 30 => { gap := ![1,0,1,0,0,0,0,0,0,0,0,0,0,0,2,0], u := 2, v := 0, c := 2, C := 18, branch := .boundary }
  | 31 => { gap := ![3,0,1,0,0,0,0,0,0,0,0,0,0,0,0,2], u := 2, v := 0, c := 6, C := 42, branch := .boundary }
  | 32 => { gap := ![1,0,0,1,0,0,0,0,0,0,0,0,0,0,2,0], u := 2, v := 0, c := 3, C := 23, branch := .boundary }
  | 33 => { gap := ![3,0,0,1,0,0,0,0,0,0,0,0,0,0,0,2], u := 2, v := 0, c := 7, C := 47, branch := .boundary }
  | 34 => { gap := ![1,0,0,0,1,0,0,0,0,0,0,0,0,0,2,0], u := 2, v := 0, c := 4, C := 28, branch := .boundary }
  | 35 => { gap := ![3,0,0,0,1,0,0,0,0,0,0,0,0,0,0,2], u := 2, v := 0, c := 8, C := 52, branch := .boundary }
  | 36 => { gap := ![3,0,0,0,0,2,0,0,0,0,0,0,0,0,5,0], u := 5, v := 2, c := (-2), C := 26, branch := .envelope₂ }
  | 37 => { gap := ![8,0,0,0,0,2,0,0,0,0,0,0,0,0,0,5], u := 5, v := 2, c := 8, C := 176, branch := .envelope₂ }
  | 38 => { gap := ![1,0,0,0,0,0,1,0,0,0,0,0,0,0,2,0], u := 3, v := 0, c := (-10), C := (-42), branch := .boundary }
  | 39 => { gap := ![3,0,0,0,0,0,1,0,0,0,0,0,0,0,0,2], u := 3, v := 0, c := (-6), C := (-18), branch := .boundary }
  | 40 => { gap := ![1,0,0,0,0,0,0,1,0,0,0,0,0,0,2,0], u := 3, v := 0, c := (-9), C := (-37), branch := .boundary }
  | 41 => { gap := ![3,0,0,0,0,0,0,1,0,0,0,0,0,0,0,2], u := 3, v := 0, c := (-5), C := (-13), branch := .boundary }
  | 42 => { gap := ![1,0,0,0,0,0,0,0,1,0,0,0,0,0,2,0], u := 3, v := 0, c := (-8), C := (-32), branch := .boundary }
  | 43 => { gap := ![3,0,0,0,0,0,0,0,1,0,0,0,0,0,0,2], u := 3, v := 0, c := (-4), C := (-8), branch := .boundary }
  | 44 => { gap := ![1,0,0,0,0,0,0,0,0,1,0,0,0,0,2,0], u := 3, v := 0, c := (-7), C := (-27), branch := .boundary }
  | 45 => { gap := ![3,0,0,0,0,0,0,0,0,1,0,0,0,0,0,2], u := 3, v := 0, c := (-3), C := (-3), branch := .boundary }
  | 46 => { gap := ![1,0,0,0,0,0,0,0,0,0,1,0,0,0,0,1], u := 2, v := 0, c := (-4), C := (-10), branch := .boundary }
  | 47 => { gap := ![0,1,0,0,2,0,0,0,0,0,0,0,0,0,4,0], u := 4, v := 0, c := 8, C := 110, branch := .boundary }
  | 48 => { gap := ![0,3,0,0,2,0,0,0,0,0,0,0,0,0,0,4], u := 4, v := 0, c := 16, C := 190, branch := .boundary }
  | 49 => { gap := ![0,3,0,0,0,2,0,0,0,0,0,0,0,0,6,0], u := 6, v := 2, c := 0, C := 78, branch := .envelope₂ }
  | 50 => { gap := ![0,3,0,0,0,1,0,0,0,0,0,0,0,0,0,3], u := 3, v := 1, c := 6, C := 66, branch := .envelope₂ }
  | 51 => { gap := ![0,1,0,0,0,0,2,0,0,0,0,0,0,0,4,0], u := 6, v := 0, c := (-20), C := (-170), branch := .boundary }
  | 52 => { gap := ![0,3,0,0,0,0,2,0,0,0,0,0,0,0,0,4], u := 6, v := 0, c := (-12), C := (-90), branch := .boundary }
  | 53 => { gap := ![0,1,0,0,0,0,0,0,0,0,0,1,0,0,0,1], u := 2, v := 0, c := (-2), C := (-2), branch := .boundary }
  | 54 => { gap := ![0,3,0,0,0,0,0,0,0,0,0,0,1,0,0,2], u := 3, v := 0, c := 3, C := 39, branch := .boundary }
  | 55 => { gap := ![0,2,0,0,0,0,0,0,0,0,0,0,0,1,0,1], u := 2, v := 0, c := 2, C := 18, branch := .boundary }
  | 56 => { gap := ![0,0,1,0,3,0,0,0,0,0,0,0,0,0,6,0], u := 6, v := 0, c := 12, C := 246, branch := .boundary }
  | 57 => { gap := ![0,0,1,0,1,0,0,0,0,0,0,0,0,0,0,2], u := 2, v := 0, c := 8, C := 46, branch := .boundary }
  | 58 => { gap := ![0,0,1,0,0,1,0,0,0,0,0,0,0,0,3,0], u := 3, v := 1, c := 0, C := 18, branch := .envelope₂ }
  | 59 => { gap := ![0,0,2,0,0,1,0,0,0,0,0,0,0,0,0,3], u := 3, v := 1, c := 6, C := 60, branch := .envelope₂ }
  | 60 => { gap := ![0,0,1,0,0,0,3,0,0,0,0,0,0,0,6,0], u := 9, v := 0, c := (-30), C := (-384), branch := .boundary }
  | 61 => { gap := ![0,0,1,0,0,0,1,0,0,0,0,0,0,0,0,2], u := 3, v := 0, c := (-6), C := (-24), branch := .boundary }
  | 62 => { gap := ![0,0,1,0,0,0,0,0,0,0,0,1,0,0,2,0], u := 3, v := 0, c := (-3), C := (-3), branch := .boundary }
  | 63 => { gap := ![0,0,1,0,0,0,0,0,0,0,0,3,0,0,0,2], u := 5, v := 0, c := (-9), C := (-51), branch := .boundary }
  | 64 => { gap := ![0,0,2,0,0,0,0,0,0,0,0,0,1,0,3,0], u := 4, v := 0, c := 0, C := 30, branch := .boundary }
  | 65 => { gap := ![0,0,1,0,0,0,0,0,0,0,0,0,1,0,0,1], u := 2, v := 0, c := 0, C := 6, branch := .boundary }
  | 66 => { gap := ![0,0,1,0,0,0,0,0,0,0,0,0,0,1,1,0], u := 2, v := 0, c := 0, C := 8, branch := .boundary }
  | 67 => { gap := ![0,0,2,0,0,0,0,0,0,0,0,0,0,3,0,1], u := 4, v := 0, c := 0, C := 30, branch := .boundary }
  | 68 => { gap := ![0,0,0,1,1,0,0,0,0,0,0,0,0,0,3,0], u := 3, v := 0, c := 6, C := 62, branch := .boundary }
  | 69 => { gap := ![0,0,0,3,0,1,0,0,0,0,0,0,0,0,6,0], u := 6, v := 1, c := 6, C := 168, branch := .envelope₂ }
  | 70 => { gap := ![0,0,0,1,0,0,1,0,0,0,0,0,0,0,3,0], u := 4, v := 0, c := (-8), C := (-36), branch := .boundary }
  | 71 => { gap := ![0,0,0,1,0,0,0,0,0,0,0,1,0,0,2,0], u := 3, v := 0, c := (-2), C := 4, branch := .boundary }
  | 72 => { gap := ![0,0,0,1,0,0,0,0,0,0,0,3,0,0,0,2], u := 5, v := 0, c := (-8), C := (-40), branch := .boundary }
  | 73 => { gap := ![0,0,0,2,0,0,0,0,0,0,0,0,1,0,3,0], u := 4, v := 0, c := 2, C := 50, branch := .boundary }
  | 74 => { gap := ![0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,1], u := 2, v := 0, c := 1, C := 11, branch := .boundary }
  | 75 => { gap := ![0,0,0,1,0,0,0,0,0,0,0,0,0,1,1,0], u := 2, v := 0, c := 1, C := 13, branch := .boundary }
  | 76 => { gap := ![0,0,0,2,0,0,0,0,0,0,0,0,0,3,0,1], u := 4, v := 0, c := 2, C := 50, branch := .boundary }
  | 77 => { gap := ![0,0,0,0,1,0,0,1,0,0,0,0,0,0,3,0], u := 4, v := 0, c := (-6), C := (-20), branch := .boundary }
  | 78 => { gap := ![0,0,0,0,3,0,0,0,1,0,0,0,0,0,6,0], u := 7, v := 0, c := 2, C := 128, branch := .boundary }
  | 79 => { gap := ![0,0,0,0,1,0,0,0,1,0,0,0,0,0,0,2], u := 3, v := 0, c := (-2), C := 0, branch := .boundary }
  | 80 => { gap := ![0,0,0,0,5,0,0,0,0,1,0,0,0,0,9,0], u := 10, v := 0, c := 10, C := 430, branch := .boundary }
  | 81 => { gap := ![0,0,0,0,2,0,0,0,0,1,0,0,0,0,0,3], u := 4, v := 0, c := 4, C := 58, branch := .boundary }
  | 82 => { gap := ![0,0,0,0,4,0,0,0,0,0,1,0,0,0,7,0], u := 8, v := 0, c := 8, C := 276, branch := .boundary }
  | 83 => { gap := ![0,0,0,0,5,0,0,0,0,0,3,0,0,0,0,7], u := 10, v := 0, c := 10, C := 370, branch := .boundary }
  | 84 => { gap := ![0,0,0,0,1,0,0,0,0,0,0,1,0,0,2,0], u := 3, v := 0, c := (-1), C := 11, branch := .boundary }
  | 85 => { gap := ![0,0,0,0,3,0,0,0,0,0,0,1,0,0,5,0], u := 6, v := 0, c := 6, C := 156, branch := .boundary }
  | 86 => { gap := ![0,0,0,0,1,0,0,0,0,0,0,3,0,0,0,2], u := 5, v := 0, c := (-7), C := (-29), branch := .boundary }
  | 87 => { gap := ![0,0,0,0,4,0,0,0,0,0,0,3,0,0,0,5], u := 8, v := 0, c := 8, C := 244, branch := .boundary }
  | 88 => { gap := ![0,0,0,0,2,0,0,0,0,0,0,0,1,0,3,0], u := 4, v := 0, c := 4, C := 70, branch := .boundary }
  | 89 => { gap := ![0,0,0,0,1,0,0,0,0,0,0,0,1,0,0,1], u := 2, v := 0, c := 2, C := 16, branch := .boundary }
  | 90 => { gap := ![0,0,0,0,1,0,0,0,0,0,0,0,0,1,1,0], u := 2, v := 0, c := 2, C := 18, branch := .boundary }
  | 91 => { gap := ![0,0,0,0,2,0,0,0,0,0,0,0,0,3,0,1], u := 4, v := 0, c := 4, C := 70, branch := .boundary }
  | 92 => { gap := ![0,0,0,0,0,1,0,3,0,0,0,0,0,0,6,0], u := 9, v := 1, c := (-30), C := (-396), branch := .envelope₂ }
  | 93 => { gap := ![0,0,0,0,0,1,0,0,1,0,0,0,0,0,3,0], u := 4, v := 1, c := (-10), C := (-58), branch := .envelope₂ }
  | 94 => { gap := ![0,0,0,0,0,1,0,0,2,0,0,0,0,0,0,3], u := 5, v := 1, c := (-14), C := (-112), branch := .envelope₂ }
  | 95 => { gap := ![0,0,0,0,0,5,0,0,0,3,0,0,0,0,12,0], u := 15, v := 5, c := (-30), C := (-630), branch := .envelope₂ }
  | 96 => { gap := ![0,0,0,0,0,1,0,0,0,1,0,0,0,0,0,2], u := 3, v := 1, c := (-6), C := (-30), branch := .envelope₂ }
  | 97 => { gap := ![0,0,0,0,0,4,0,0,0,0,3,0,0,0,9,0], u := 12, v := 4, c := (-24), C := (-396), branch := .envelope₂ }
  | 98 => { gap := ![0,0,0,0,0,5,0,0,0,0,6,0,0,0,0,9], u := 15, v := 5, c := (-30), C := (-720), branch := .envelope₂ }
  | 99 => { gap := ![0,0,0,0,0,1,0,0,0,0,0,1,0,0,2,0], u := 3, v := 1, c := (-6), C := (-24), branch := .envelope₂ }
  | 100 => { gap := ![0,0,0,0,0,1,0,0,0,0,0,3,0,0,0,2], u := 5, v := 1, c := (-12), C := (-84), branch := .envelope₂ }
  | 101 => { gap := ![0,0,0,0,0,2,0,0,0,0,0,3,0,0,0,3], u := 6, v := 2, c := (-12), C := (-108), branch := .envelope₂ }
  | 102 => { gap := ![0,0,0,0,0,4,0,0,0,0,0,0,3,0,7,0], u := 10, v := 4, c := (-16), C := (-202), branch := .envelope₂ }
  | 103 => { gap := ![0,0,0,0,0,6,0,0,0,0,0,0,8,0,0,7], u := 15, v := 6, c := (-24), C := (-528), branch := .envelope₂ }
  | 104 => { gap := ![0,0,0,0,0,2,0,0,0,0,0,0,0,3,2,0], u := 5, v := 2, c := (-8), C := (-46), branch := .envelope₂ }
  | 105 => { gap := ![0,0,0,0,0,2,0,0,0,0,0,0,0,4,0,1], u := 5, v := 2, c := (-8), C := (-48), branch := .envelope₂ }
  | 106 => { gap := ![0,0,0,0,0,0,1,1,0,0,0,0,0,0,3,0], u := 5, v := 0, c := (-20), C := (-146), branch := .boundary }
  | 107 => { gap := ![0,0,0,0,0,0,3,0,1,0,0,0,0,0,6,0], u := 10, v := 0, c := (-40), C := (-586), branch := .boundary }
  | 108 => { gap := ![0,0,0,0,0,0,1,0,1,0,0,0,0,0,0,2], u := 4, v := 0, c := (-16), C := (-98), branch := .boundary }
  | 109 => { gap := ![0,0,0,0,0,0,5,0,0,1,0,0,0,0,9,0], u := 15, v := 0, c := (-60), C := (-1320), branch := .boundary }
  | 110 => { gap := ![0,0,0,0,0,0,2,0,0,1,0,0,0,0,0,3], u := 6, v := 0, c := (-24), C := (-222), branch := .boundary }
  | 111 => { gap := ![0,0,0,0,0,0,4,0,0,0,1,0,0,0,7,0], u := 12, v := 0, c := (-48), C := (-844), branch := .boundary }
  | 112 => { gap := ![0,0,0,0,0,0,5,0,0,0,3,0,0,0,0,7], u := 15, v := 0, c := (-60), C := (-1380), branch := .boundary }
  | 113 => { gap := ![0,0,0,0,0,0,1,0,0,0,0,1,0,0,2,0], u := 4, v := 0, c := (-15), C := (-87), branch := .boundary }
  | 114 => { gap := ![0,0,0,0,0,0,3,0,0,0,0,1,0,0,5,0], u := 9, v := 0, c := (-36), C := (-474), branch := .boundary }
  | 115 => { gap := ![0,0,0,0,0,0,1,0,0,0,0,3,0,0,0,2], u := 6, v := 0, c := (-21), C := (-183), branch := .boundary }
  | 116 => { gap := ![0,0,0,0,0,0,4,0,0,0,0,3,0,0,0,5], u := 12, v := 0, c := (-48), C := (-876), branch := .boundary }
  | 117 => { gap := ![0,0,0,0,0,0,2,0,0,0,0,0,1,0,3,0], u := 6, v := 0, c := (-24), C := (-210), branch := .boundary }
  | 118 => { gap := ![0,0,0,0,0,0,1,0,0,0,0,0,1,0,0,1], u := 3, v := 0, c := (-12), C := (-54), branch := .boundary }
  | 119 => { gap := ![0,0,0,0,0,0,1,0,0,0,0,0,0,1,1,0], u := 3, v := 0, c := (-12), C := (-52), branch := .boundary }
  | 120 => { gap := ![0,0,0,0,0,0,2,0,0,0,0,0,0,3,0,1], u := 6, v := 0, c := (-24), C := (-210), branch := .boundary }
  | 121 => { gap := ![0,0,0,0,0,0,0,1,0,0,0,1,0,0,2,0], u := 4, v := 0, c := (-14), C := (-80), branch := .boundary }
  | 122 => { gap := ![0,0,0,0,0,0,0,1,0,0,0,3,0,0,0,2], u := 6, v := 0, c := (-20), C := (-172), branch := .boundary }
  | 123 => { gap := ![0,0,0,0,0,0,0,2,0,0,0,0,1,0,3,0], u := 6, v := 0, c := (-22), C := (-190), branch := .boundary }
  | 124 => { gap := ![0,0,0,0,0,0,0,1,0,0,0,0,1,0,0,1], u := 3, v := 0, c := (-11), C := (-49), branch := .boundary }
  | 125 => { gap := ![0,0,0,0,0,0,0,1,0,0,0,0,0,1,1,0], u := 3, v := 0, c := (-11), C := (-47), branch := .boundary }
  | 126 => { gap := ![0,0,0,0,0,0,0,2,0,0,0,0,0,3,0,1], u := 6, v := 0, c := (-22), C := (-190), branch := .boundary }
  | 127 => { gap := ![0,0,0,0,0,0,0,0,1,0,0,1,0,0,2,0], u := 4, v := 0, c := (-13), C := (-73), branch := .boundary }
  | 128 => { gap := ![0,0,0,0,0,0,0,0,1,0,0,3,0,0,0,2], u := 6, v := 0, c := (-19), C := (-161), branch := .boundary }
  | 129 => { gap := ![0,0,0,0,0,0,0,0,2,0,0,0,1,0,3,0], u := 6, v := 0, c := (-20), C := (-170), branch := .boundary }
  | 130 => { gap := ![0,0,0,0,0,0,0,0,1,0,0,0,1,0,0,1], u := 3, v := 0, c := (-10), C := (-44), branch := .boundary }
  | 131 => { gap := ![0,0,0,0,0,0,0,0,1,0,0,0,0,1,1,0], u := 3, v := 0, c := (-10), C := (-42), branch := .boundary }
  | 132 => { gap := ![0,0,0,0,0,0,0,0,2,0,0,0,0,3,0,1], u := 6, v := 0, c := (-20), C := (-170), branch := .boundary }
  | 133 => { gap := ![0,0,0,0,0,0,0,0,0,1,0,1,0,0,2,0], u := 4, v := 0, c := (-12), C := (-66), branch := .boundary }
  | 134 => { gap := ![0,0,0,0,0,0,0,0,0,1,0,3,0,0,0,2], u := 6, v := 0, c := (-18), C := (-150), branch := .boundary }
  | 135 => { gap := ![0,0,0,0,0,0,0,0,0,2,0,0,1,0,3,0], u := 6, v := 0, c := (-18), C := (-150), branch := .boundary }
  | 136 => { gap := ![0,0,0,0,0,0,0,0,0,1,0,0,1,0,0,1], u := 3, v := 0, c := (-9), C := (-39), branch := .boundary }
  | 137 => { gap := ![0,0,0,0,0,0,0,0,0,1,0,0,0,1,1,0], u := 3, v := 0, c := (-9), C := (-37), branch := .boundary }
  | 138 => { gap := ![0,0,0,0,0,0,0,0,0,2,0,0,0,3,0,1], u := 6, v := 0, c := (-18), C := (-150), branch := .boundary }
  | 139 => { gap := ![0,0,0,0,0,0,0,0,0,0,1,1,0,0,0,1], u := 3, v := 0, c := (-9), C := (-37), branch := .boundary }
  | 140 => { gap := ![0,0,0,0,0,0,0,0,0,0,3,0,1,0,0,2], u := 6, v := 0, c := (-18), C := (-150), branch := .boundary }
  | 141 => { gap := ![0,0,0,0,0,0,0,0,0,0,2,0,0,1,0,1], u := 4, v := 0, c := (-12), C := (-66), branch := .boundary }
  | 142 => { gap := ![1,1,0,0,0,1,0,0,0,0,0,0,0,0,3,0], u := 3, v := 1, c := 0, C := 20, branch := .envelope₂ }
  | 143 => { gap := ![4,1,0,0,0,1,0,0,0,0,0,0,0,0,0,3], u := 3, v := 1, c := 6, C := 74, branch := .envelope₂ }
  | 144 => { gap := ![3,0,1,0,0,2,0,0,0,0,0,0,0,0,6,0], u := 6, v := 2, c := 0, C := 78, branch := .envelope₂ }
  | 145 => { gap := ![9,0,1,0,0,2,0,0,0,0,0,0,0,0,0,6], u := 6, v := 2, c := 12, C := 294, branch := .envelope₂ }
  | 146 => { gap := ![2,0,0,1,0,1,0,0,0,0,0,0,0,0,4,0], u := 4, v := 1, c := 2, C := 56, branch := .envelope₂ }
  | 147 => { gap := ![6,0,0,1,0,1,0,0,0,0,0,0,0,0,0,4], u := 4, v := 1, c := 10, C := 152, branch := .envelope₂ }
  | 148 => { gap := ![2,0,0,0,0,1,0,1,0,0,0,0,0,0,4,0], u := 5, v := 1, c := (-10), C := (-60), branch := .envelope₂ }
  | 149 => { gap := ![6,0,0,0,0,1,0,1,0,0,0,0,0,0,0,4], u := 5, v := 1, c := (-2), C := 36, branch := .envelope₂ }
  | 150 => { gap := ![3,0,0,0,0,2,0,0,1,0,0,0,0,0,6,0], u := 7, v := 2, c := (-10), C := (-64), branch := .envelope₂ }
  | 151 => { gap := ![9,0,0,0,0,2,0,0,1,0,0,0,0,0,0,6], u := 7, v := 2, c := 2, C := 152, branch := .envelope₂ }
  | 152 => { gap := ![4,0,0,0,0,3,0,0,0,1,0,0,0,0,8,0], u := 9, v := 3, c := (-10), C := (-54), branch := .envelope₂ }
  | 153 => { gap := ![12,0,0,0,0,3,0,0,0,1,0,0,0,0,0,8], u := 9, v := 3, c := 6, C := 330, branch := .envelope₂ }
  | 154 => { gap := ![2,0,0,0,0,2,0,0,0,0,1,0,0,0,5,0], u := 6, v := 2, c := (-8), C := (-44), branch := .envelope₂ }
  | 155 => { gap := ![7,0,0,0,0,2,0,0,0,0,1,0,0,0,0,5], u := 6, v := 2, c := 2, C := 106, branch := .envelope₂ }
  | 156 => { gap := ![2,0,0,0,0,1,0,0,0,0,0,1,0,0,0,2], u := 3, v := 1, c := (-2), C := 0, branch := .envelope₂ }
  | 157 => { gap := ![0,2,0,0,0,2,0,0,0,0,0,0,1,0,5,0], u := 6, v := 2, c := (-4), C := 14, branch := .envelope₂ }
  | 158 => { gap := ![0,3,0,0,0,3,0,0,0,0,0,0,4,0,0,5], u := 9, v := 3, c := (-6), C := (-6), branch := .envelope₂ }
  | 159 => { gap := ![0,1,0,0,0,1,0,0,0,0,0,0,0,1,2,0], u := 3, v := 1, c := (-2), C := 4, branch := .envelope₂ }
  | 160 => { gap := ![0,1,0,0,0,1,0,0,0,0,0,0,0,2,0,1], u := 3, v := 1, c := (-2), C := 2, branch := .envelope₂ }
  | 161 => { gap := ![0,0,2,0,0,4,0,0,0,0,0,0,3,0,9,0], u := 12, v := 4, c := (-12), C := (-66), branch := .envelope₂ }
  | 162 => { gap := ![0,0,1,0,0,2,0,0,0,0,0,0,3,0,0,3], u := 6, v := 2, c := (-6), C := (-30), branch := .envelope₂ }
  | 163 => { gap := ![0,0,1,0,0,2,0,0,0,0,0,0,0,3,3,0], u := 6, v := 2, c := (-6), C := (-12), branch := .envelope₂ }
  | 164 => { gap := ![0,0,2,0,0,4,0,0,0,0,0,0,0,9,0,3], u := 12, v := 4, c := (-12), C := (-66), branch := .envelope₂ }
  | 165 => { gap := ![0,0,0,1,0,1,0,0,0,0,0,0,1,0,3,0], u := 4, v := 1, c := (-2), C := 14, branch := .envelope₂ }
  | 166 => { gap := ![0,0,0,1,0,1,0,0,0,0,0,0,2,0,0,2], u := 4, v := 1, c := (-2), C := 8, branch := .envelope₂ }
  | 167 => { gap := ![0,0,0,1,0,1,0,0,0,0,0,0,0,2,2,0], u := 4, v := 1, c := (-2), C := 16, branch := .envelope₂ }
  | 168 => { gap := ![0,0,0,1,0,1,0,0,0,0,0,0,0,3,0,1], u := 4, v := 1, c := (-2), C := 14, branch := .envelope₂ }
  | 169 => { gap := ![0,0,0,0,0,1,0,1,0,0,0,0,1,0,3,0], u := 5, v := 1, c := (-14), C := (-102), branch := .envelope₂ }
  | 170 => { gap := ![0,0,0,0,0,1,0,1,0,0,0,0,2,0,0,2], u := 5, v := 1, c := (-14), C := (-108), branch := .envelope₂ }
  | 171 => { gap := ![0,0,0,0,0,1,0,1,0,0,0,0,0,2,2,0], u := 5, v := 1, c := (-14), C := (-100), branch := .envelope₂ }
  | 172 => { gap := ![0,0,0,0,0,1,0,1,0,0,0,0,0,3,0,1], u := 5, v := 1, c := (-14), C := (-102), branch := .envelope₂ }
  | 173 => { gap := ![0,0,0,0,0,4,0,0,2,0,0,0,3,0,9,0], u := 14, v := 4, c := (-32), C := (-634), branch := .envelope₂ }
  | 174 => { gap := ![0,0,0,0,0,2,0,0,1,0,0,0,3,0,0,3], u := 7, v := 2, c := (-16), C := (-172), branch := .envelope₂ }
  | 175 => { gap := ![0,0,0,0,0,2,0,0,1,0,0,0,0,3,3,0], u := 7, v := 2, c := (-16), C := (-154), branch := .envelope₂ }
  | 176 => { gap := ![0,0,0,0,0,4,0,0,2,0,0,0,0,9,0,3], u := 14, v := 4, c := (-32), C := (-634), branch := .envelope₂ }
  | 177 => { gap := ![0,0,0,0,0,3,0,0,0,1,0,0,2,0,6,0], u := 9, v := 3, c := (-18), C := (-222), branch := .envelope₂ }
  | 178 => { gap := ![0,0,0,0,0,3,0,0,0,1,0,0,4,0,0,4], u := 9, v := 3, c := (-18), C := (-246), branch := .envelope₂ }
  | 179 => { gap := ![0,0,0,0,0,3,0,0,0,1,0,0,0,4,4,0], u := 9, v := 3, c := (-18), C := (-214), branch := .envelope₂ }
  | 180 => { gap := ![0,0,0,0,0,3,0,0,0,1,0,0,0,6,0,2], u := 9, v := 3, c := (-18), C := (-222), branch := .envelope₂ }
  | 181 => { gap := ![0,0,0,0,0,2,0,0,0,0,1,0,1,0,4,0], u := 6, v := 2, c := (-12), C := (-98), branch := .envelope₂ }
  | 182 => { gap := ![0,0,0,0,0,6,0,0,0,0,3,0,7,0,0,8], u := 18, v := 6, c := (-36), C := (-978), branch := .envelope₂ }
  | 183 => { gap := ![0,0,0,0,0,2,0,0,0,0,1,0,0,2,3,0], u := 6, v := 2, c := (-12), C := (-96), branch := .envelope₂ }
  | 184 => { gap := ![0,0,0,0,0,4,0,0,0,0,2,0,0,7,0,3], u := 12, v := 4, c := (-24), C := (-402), branch := .envelope₂ }
  | 185 => { gap := ![0,0,0,0,0,3,0,0,0,0,0,3,2,0,0,4], u := 9, v := 3, c := (-18), C := (-240), branch := .envelope₂ }
  | _ => { gap := ![0,0,0,0,0,1,0,0,0,0,0,1,0,1,0,1], u := 3, v := 1, c := (-6), C := (-26), branch := .envelope₂ }

end
end D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound
