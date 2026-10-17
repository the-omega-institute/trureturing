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

/-- Gaps, four integer moment coefficients, and a branch in the order
boundary, first middle envelope, second middle envelope, bulk. -/
abbrev RayData := (Fin 16 → ℕ) × ℤ × ℤ × ℤ × ℤ × Fin 4

abbrev RayData.gap (r : RayData) : Fin 16 → ℕ := r.1
abbrev RayData.u (r : RayData) : ℤ := r.2.1
abbrev RayData.v (r : RayData) : ℤ := r.2.2.1
abbrev RayData.c (r : RayData) : ℤ := r.2.2.2.1
abbrev RayData.C (r : RayData) : ℤ := r.2.2.2.2.1
abbrev RayData.branch (r : RayData) : Fin 4 := r.2.2.2.2.2

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
  if r.branch.val = 0 then
    r.v = 0 ∧ boundaryCertificate (r.u : ℝ) (r.c : ℝ) (r.C : ℝ)
  else if r.branch.val = 1 then
    0 < (r.v : ℝ) ∧
      middleCertificate 25 24 (-24) (r.u : ℝ) (r.v : ℝ) (r.c : ℝ) (r.C : ℝ)
  else if r.branch.val = 2 then
    0 < (r.v : ℝ) ∧
      middleCertificate 36 35 (-80) (r.u : ℝ) (r.v : ℝ) (r.c : ℝ) (r.C : ℝ)
  else r.u = 3 ∧ r.v = 2 ∧ r.c = 0 ∧ r.C = 0

def RayData.Valid (r : RayData) : Prop :=
  0 ≤ (r.u : ℝ) ∧
  0 ≤ (r.v : ℝ) ∧
  0 < 67*(r.u : ℝ)+6*(r.v : ℝ)+(r.c : ℝ) ∧
  MomentWitness r ∧ branchValid r

theorem RayData.Valid.u_nonneg {r : RayData} (h : r.Valid) : 0 ≤ (r.u : ℝ) := h.1

theorem RayData.Valid.v_nonneg {r : RayData} (h : r.Valid) : 0 ≤ (r.v : ℝ) := h.2.1

theorem RayData.Valid.mass67_pos {r : RayData} (h : r.Valid) :
    0 < 67*(r.u : ℝ)+6*(r.v : ℝ)+(r.c : ℝ) := h.2.2.1

theorem RayData.Valid.moments {r : RayData} (h : r.Valid) : MomentWitness r := h.2.2.2.1

theorem RayData.Valid.branch_valid {r : RayData} (h : r.Valid) : branchValid r := h.2.2.2.2

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
    (hN : 67 ≤ N) (hj : 6 ≤ j) (hne : r.branch ≠ 3) :
    raySquare r N j/(rayMass r N j)^2 ≤ commonEnvelope N := by
  have hM := ray_mass_positive r hr N j hN hj
  have hc := hr.branch_valid
  have hbranch := r.branch.isLt
  interval_cases hb : r.branch.val
  ·
    simp only [branchValid, hb] at hc
    obtain ⟨hv, hcert⟩ := hc
    have hM' : 0 < (r.u : ℝ)*N+(r.c : ℝ) := by simpa [rayMass, hv] using hM
    have h := boundary_ray_bound N (r.u : ℝ) (r.c : ℝ) (r.C : ℝ) hN hM' hcert
    have h' : raySquare r N j/(rayMass r N j)^2 ≤ boundaryEnvelope N := by
      simpa [raySquare, rayMass, hv] using h
    exact h'.trans (boundary_envelope_le_common N hN)
  ·
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
  ·
    simp only [branchValid, hb] at hc
    obtain ⟨hv, hcert⟩ := hc
    have hh : 0 < 2*(r.u : ℝ)+(r.v : ℝ) := by linarith [hr.u_nonneg]
    have hD : 0 < 35*N+(-80) := by linarith
    have h := middle_ray_envelope N j 36 35 (-80) (r.u : ℝ) (r.v : ℝ)
      (r.c : ℝ) (r.C : ℝ) hN (by norm_num) hD hh hM hcert
    have h' : raySquare r N j/(rayMass r N j)^2 ≤ middleEnvelope₂ N := by
      simpa only [raySquare, rayMass, middleEnvelope₂, sub_eq_add_neg] using h
    exact h'.trans (middle_envelope₂_le_common N hN)
  · exact False.elim (hne (Fin.ext hb))

private lemma ray_scalar_bound (r : RayData) (hr : r.Valid) (N j : ℕ)
    (hN : 67 ≤ N) (hj : 6 ≤ j) :
    raySquare r (N : ℝ) (j : ℝ) ≤
      bulkValue (N : ℝ) (bulkIndex N : ℝ)*(rayMass r (N : ℝ) (j : ℝ))^2 := by
  have hn : (67 : ℝ) ≤ N := by exact_mod_cast hN
  have hjR : (6 : ℝ) ≤ j := by exact_mod_cast hj
  have hM := ray_mass_positive r hr (N : ℝ) (j : ℝ) hn hjR
  apply (div_le_iff₀ (sq_pos_of_pos hM)).1
  by_cases hb : r.branch = 3
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
  | 0 => (![0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0], 1, 0, (-2), (-2), 0)
  | 1 => (![0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0], 1, 0, (-1), (-1), 0)
  | 2 => (![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1], 1, 0, 0, 0, 0)
  | 3 => (![1,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0], 1, 0, 0, 2, 0)
  | 4 => (![2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1], 1, 0, 2, 8, 0)
  | 5 => (![0,1,0,0,0,0,0,0,0,0,0,0,0,0,1,0], 1, 0, 1, 5, 0)
  | 6 => (![0,3,0,0,0,0,0,0,0,0,0,0,0,0,0,2], 2, 0, 6, 42, 0)
  | 7 => (![0,0,2,0,0,0,0,0,0,0,0,0,0,0,3,0], 3, 0, 3, 39, 0)
  | 8 => (![0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,1], 1, 0, 3, 9, 0)
  | 9 => (![0,0,0,2,0,0,0,0,0,0,0,0,0,0,3,0], 3, 0, 5, 55, 0)
  | 10 => (![0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,1], 1, 0, 4, 12, 0)
  | 11 => (![0,0,0,0,3,0,0,0,0,0,0,0,0,0,5,0], 5, 0, 10, 170, 0)
  | 12 => (![0,0,0,0,4,0,0,0,0,0,0,0,0,0,0,5], 5, 0, 20, 280, 0)
  | 13 => (![0,0,0,0,0,1,0,0,0,0,0,0,0,0,2,0], 2, 1, (-2), (-4), 1)
  | 14 => (![0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,3], 3, 2, 0, 0, 3)
  | 15 => (![0,0,0,0,0,0,3,0,0,0,0,0,0,0,5,0], 8, 0, (-32), (-376), 0)
  | 16 => (![0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,5], 9, 0, (-36), (-504), 0)
  | 17 => (![0,0,0,0,0,0,0,2,0,0,0,0,0,0,3,0], 5, 0, (-19), (-137), 0)
  | 18 => (![0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,1], 2, 0, (-8), (-24), 0)
  | 19 => (![0,0,0,0,0,0,0,0,2,0,0,0,0,0,3,0], 5, 0, (-17), (-121), 0)
  | 20 => (![0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,1], 2, 0, (-7), (-21), 0)
  | 21 => (![0,0,0,0,0,0,0,0,0,2,0,0,0,0,3,0], 5, 0, (-15), (-105), 0)
  | 22 => (![0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,1], 2, 0, (-6), (-18), 0)
  | 23 => (![0,0,0,0,0,0,0,0,0,0,1,0,0,0,1,0], 2, 0, (-6), (-16), 0)
  | 24 => (![0,0,0,0,0,0,0,0,0,0,3,0,0,0,0,2], 5, 0, (-15), (-105), 0)
  | 25 => (![0,0,0,0,0,0,0,0,0,0,0,1,0,0,1,0], 2, 0, (-5), (-13), 0)
  | 26 => (![0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,1], 3, 0, (-8), (-32), 0)
  | 27 => (![0,0,0,0,0,0,0,0,0,0,0,0,1,0,1,0], 2, 0, (-4), (-10), 0)
  | 28 => (![0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,1], 3, 0, (-6), (-24), 0)
  | 29 => (![1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,1], 1, 0, 3, 11, 0)
  | 30 => (![1,0,1,0,0,0,0,0,0,0,0,0,0,0,2,0], 2, 0, 2, 18, 0)
  | 31 => (![3,0,1,0,0,0,0,0,0,0,0,0,0,0,0,2], 2, 0, 6, 42, 0)
  | 32 => (![1,0,0,1,0,0,0,0,0,0,0,0,0,0,2,0], 2, 0, 3, 23, 0)
  | 33 => (![3,0,0,1,0,0,0,0,0,0,0,0,0,0,0,2], 2, 0, 7, 47, 0)
  | 34 => (![1,0,0,0,1,0,0,0,0,0,0,0,0,0,2,0], 2, 0, 4, 28, 0)
  | 35 => (![3,0,0,0,1,0,0,0,0,0,0,0,0,0,0,2], 2, 0, 8, 52, 0)
  | 36 => (![3,0,0,0,0,2,0,0,0,0,0,0,0,0,5,0], 5, 2, (-2), 26, 2)
  | 37 => (![8,0,0,0,0,2,0,0,0,0,0,0,0,0,0,5], 5, 2, 8, 176, 2)
  | 38 => (![1,0,0,0,0,0,1,0,0,0,0,0,0,0,2,0], 3, 0, (-10), (-42), 0)
  | 39 => (![3,0,0,0,0,0,1,0,0,0,0,0,0,0,0,2], 3, 0, (-6), (-18), 0)
  | 40 => (![1,0,0,0,0,0,0,1,0,0,0,0,0,0,2,0], 3, 0, (-9), (-37), 0)
  | 41 => (![3,0,0,0,0,0,0,1,0,0,0,0,0,0,0,2], 3, 0, (-5), (-13), 0)
  | 42 => (![1,0,0,0,0,0,0,0,1,0,0,0,0,0,2,0], 3, 0, (-8), (-32), 0)
  | 43 => (![3,0,0,0,0,0,0,0,1,0,0,0,0,0,0,2], 3, 0, (-4), (-8), 0)
  | 44 => (![1,0,0,0,0,0,0,0,0,1,0,0,0,0,2,0], 3, 0, (-7), (-27), 0)
  | 45 => (![3,0,0,0,0,0,0,0,0,1,0,0,0,0,0,2], 3, 0, (-3), (-3), 0)
  | 46 => (![1,0,0,0,0,0,0,0,0,0,1,0,0,0,0,1], 2, 0, (-4), (-10), 0)
  | 47 => (![0,1,0,0,2,0,0,0,0,0,0,0,0,0,4,0], 4, 0, 8, 110, 0)
  | 48 => (![0,3,0,0,2,0,0,0,0,0,0,0,0,0,0,4], 4, 0, 16, 190, 0)
  | 49 => (![0,3,0,0,0,2,0,0,0,0,0,0,0,0,6,0], 6, 2, 0, 78, 2)
  | 50 => (![0,3,0,0,0,1,0,0,0,0,0,0,0,0,0,3], 3, 1, 6, 66, 2)
  | 51 => (![0,1,0,0,0,0,2,0,0,0,0,0,0,0,4,0], 6, 0, (-20), (-170), 0)
  | 52 => (![0,3,0,0,0,0,2,0,0,0,0,0,0,0,0,4], 6, 0, (-12), (-90), 0)
  | 53 => (![0,1,0,0,0,0,0,0,0,0,0,1,0,0,0,1], 2, 0, (-2), (-2), 0)
  | 54 => (![0,3,0,0,0,0,0,0,0,0,0,0,1,0,0,2], 3, 0, 3, 39, 0)
  | 55 => (![0,2,0,0,0,0,0,0,0,0,0,0,0,1,0,1], 2, 0, 2, 18, 0)
  | 56 => (![0,0,1,0,3,0,0,0,0,0,0,0,0,0,6,0], 6, 0, 12, 246, 0)
  | 57 => (![0,0,1,0,1,0,0,0,0,0,0,0,0,0,0,2], 2, 0, 8, 46, 0)
  | 58 => (![0,0,1,0,0,1,0,0,0,0,0,0,0,0,3,0], 3, 1, 0, 18, 2)
  | 59 => (![0,0,2,0,0,1,0,0,0,0,0,0,0,0,0,3], 3, 1, 6, 60, 2)
  | 60 => (![0,0,1,0,0,0,3,0,0,0,0,0,0,0,6,0], 9, 0, (-30), (-384), 0)
  | 61 => (![0,0,1,0,0,0,1,0,0,0,0,0,0,0,0,2], 3, 0, (-6), (-24), 0)
  | 62 => (![0,0,1,0,0,0,0,0,0,0,0,1,0,0,2,0], 3, 0, (-3), (-3), 0)
  | 63 => (![0,0,1,0,0,0,0,0,0,0,0,3,0,0,0,2], 5, 0, (-9), (-51), 0)
  | 64 => (![0,0,2,0,0,0,0,0,0,0,0,0,1,0,3,0], 4, 0, 0, 30, 0)
  | 65 => (![0,0,1,0,0,0,0,0,0,0,0,0,1,0,0,1], 2, 0, 0, 6, 0)
  | 66 => (![0,0,1,0,0,0,0,0,0,0,0,0,0,1,1,0], 2, 0, 0, 8, 0)
  | 67 => (![0,0,2,0,0,0,0,0,0,0,0,0,0,3,0,1], 4, 0, 0, 30, 0)
  | 68 => (![0,0,0,1,1,0,0,0,0,0,0,0,0,0,3,0], 3, 0, 6, 62, 0)
  | 69 => (![0,0,0,3,0,1,0,0,0,0,0,0,0,0,6,0], 6, 1, 6, 168, 2)
  | 70 => (![0,0,0,1,0,0,1,0,0,0,0,0,0,0,3,0], 4, 0, (-8), (-36), 0)
  | 71 => (![0,0,0,1,0,0,0,0,0,0,0,1,0,0,2,0], 3, 0, (-2), 4, 0)
  | 72 => (![0,0,0,1,0,0,0,0,0,0,0,3,0,0,0,2], 5, 0, (-8), (-40), 0)
  | 73 => (![0,0,0,2,0,0,0,0,0,0,0,0,1,0,3,0], 4, 0, 2, 50, 0)
  | 74 => (![0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,1], 2, 0, 1, 11, 0)
  | 75 => (![0,0,0,1,0,0,0,0,0,0,0,0,0,1,1,0], 2, 0, 1, 13, 0)
  | 76 => (![0,0,0,2,0,0,0,0,0,0,0,0,0,3,0,1], 4, 0, 2, 50, 0)
  | 77 => (![0,0,0,0,1,0,0,1,0,0,0,0,0,0,3,0], 4, 0, (-6), (-20), 0)
  | 78 => (![0,0,0,0,3,0,0,0,1,0,0,0,0,0,6,0], 7, 0, 2, 128, 0)
  | 79 => (![0,0,0,0,1,0,0,0,1,0,0,0,0,0,0,2], 3, 0, (-2), 0, 0)
  | 80 => (![0,0,0,0,5,0,0,0,0,1,0,0,0,0,9,0], 10, 0, 10, 430, 0)
  | 81 => (![0,0,0,0,2,0,0,0,0,1,0,0,0,0,0,3], 4, 0, 4, 58, 0)
  | 82 => (![0,0,0,0,4,0,0,0,0,0,1,0,0,0,7,0], 8, 0, 8, 276, 0)
  | 83 => (![0,0,0,0,5,0,0,0,0,0,3,0,0,0,0,7], 10, 0, 10, 370, 0)
  | 84 => (![0,0,0,0,1,0,0,0,0,0,0,1,0,0,2,0], 3, 0, (-1), 11, 0)
  | 85 => (![0,0,0,0,3,0,0,0,0,0,0,1,0,0,5,0], 6, 0, 6, 156, 0)
  | 86 => (![0,0,0,0,1,0,0,0,0,0,0,3,0,0,0,2], 5, 0, (-7), (-29), 0)
  | 87 => (![0,0,0,0,4,0,0,0,0,0,0,3,0,0,0,5], 8, 0, 8, 244, 0)
  | 88 => (![0,0,0,0,2,0,0,0,0,0,0,0,1,0,3,0], 4, 0, 4, 70, 0)
  | 89 => (![0,0,0,0,1,0,0,0,0,0,0,0,1,0,0,1], 2, 0, 2, 16, 0)
  | 90 => (![0,0,0,0,1,0,0,0,0,0,0,0,0,1,1,0], 2, 0, 2, 18, 0)
  | 91 => (![0,0,0,0,2,0,0,0,0,0,0,0,0,3,0,1], 4, 0, 4, 70, 0)
  | 92 => (![0,0,0,0,0,1,0,3,0,0,0,0,0,0,6,0], 9, 1, (-30), (-396), 2)
  | 93 => (![0,0,0,0,0,1,0,0,1,0,0,0,0,0,3,0], 4, 1, (-10), (-58), 2)
  | 94 => (![0,0,0,0,0,1,0,0,2,0,0,0,0,0,0,3], 5, 1, (-14), (-112), 2)
  | 95 => (![0,0,0,0,0,5,0,0,0,3,0,0,0,0,12,0], 15, 5, (-30), (-630), 2)
  | 96 => (![0,0,0,0,0,1,0,0,0,1,0,0,0,0,0,2], 3, 1, (-6), (-30), 2)
  | 97 => (![0,0,0,0,0,4,0,0,0,0,3,0,0,0,9,0], 12, 4, (-24), (-396), 2)
  | 98 => (![0,0,0,0,0,5,0,0,0,0,6,0,0,0,0,9], 15, 5, (-30), (-720), 2)
  | 99 => (![0,0,0,0,0,1,0,0,0,0,0,1,0,0,2,0], 3, 1, (-6), (-24), 2)
  | 100 => (![0,0,0,0,0,1,0,0,0,0,0,3,0,0,0,2], 5, 1, (-12), (-84), 2)
  | 101 => (![0,0,0,0,0,2,0,0,0,0,0,3,0,0,0,3], 6, 2, (-12), (-108), 2)
  | 102 => (![0,0,0,0,0,4,0,0,0,0,0,0,3,0,7,0], 10, 4, (-16), (-202), 2)
  | 103 => (![0,0,0,0,0,6,0,0,0,0,0,0,8,0,0,7], 15, 6, (-24), (-528), 2)
  | 104 => (![0,0,0,0,0,2,0,0,0,0,0,0,0,3,2,0], 5, 2, (-8), (-46), 2)
  | 105 => (![0,0,0,0,0,2,0,0,0,0,0,0,0,4,0,1], 5, 2, (-8), (-48), 2)
  | 106 => (![0,0,0,0,0,0,1,1,0,0,0,0,0,0,3,0], 5, 0, (-20), (-146), 0)
  | 107 => (![0,0,0,0,0,0,3,0,1,0,0,0,0,0,6,0], 10, 0, (-40), (-586), 0)
  | 108 => (![0,0,0,0,0,0,1,0,1,0,0,0,0,0,0,2], 4, 0, (-16), (-98), 0)
  | 109 => (![0,0,0,0,0,0,5,0,0,1,0,0,0,0,9,0], 15, 0, (-60), (-1320), 0)
  | 110 => (![0,0,0,0,0,0,2,0,0,1,0,0,0,0,0,3], 6, 0, (-24), (-222), 0)
  | 111 => (![0,0,0,0,0,0,4,0,0,0,1,0,0,0,7,0], 12, 0, (-48), (-844), 0)
  | 112 => (![0,0,0,0,0,0,5,0,0,0,3,0,0,0,0,7], 15, 0, (-60), (-1380), 0)
  | 113 => (![0,0,0,0,0,0,1,0,0,0,0,1,0,0,2,0], 4, 0, (-15), (-87), 0)
  | 114 => (![0,0,0,0,0,0,3,0,0,0,0,1,0,0,5,0], 9, 0, (-36), (-474), 0)
  | 115 => (![0,0,0,0,0,0,1,0,0,0,0,3,0,0,0,2], 6, 0, (-21), (-183), 0)
  | 116 => (![0,0,0,0,0,0,4,0,0,0,0,3,0,0,0,5], 12, 0, (-48), (-876), 0)
  | 117 => (![0,0,0,0,0,0,2,0,0,0,0,0,1,0,3,0], 6, 0, (-24), (-210), 0)
  | 118 => (![0,0,0,0,0,0,1,0,0,0,0,0,1,0,0,1], 3, 0, (-12), (-54), 0)
  | 119 => (![0,0,0,0,0,0,1,0,0,0,0,0,0,1,1,0], 3, 0, (-12), (-52), 0)
  | 120 => (![0,0,0,0,0,0,2,0,0,0,0,0,0,3,0,1], 6, 0, (-24), (-210), 0)
  | 121 => (![0,0,0,0,0,0,0,1,0,0,0,1,0,0,2,0], 4, 0, (-14), (-80), 0)
  | 122 => (![0,0,0,0,0,0,0,1,0,0,0,3,0,0,0,2], 6, 0, (-20), (-172), 0)
  | 123 => (![0,0,0,0,0,0,0,2,0,0,0,0,1,0,3,0], 6, 0, (-22), (-190), 0)
  | 124 => (![0,0,0,0,0,0,0,1,0,0,0,0,1,0,0,1], 3, 0, (-11), (-49), 0)
  | 125 => (![0,0,0,0,0,0,0,1,0,0,0,0,0,1,1,0], 3, 0, (-11), (-47), 0)
  | 126 => (![0,0,0,0,0,0,0,2,0,0,0,0,0,3,0,1], 6, 0, (-22), (-190), 0)
  | 127 => (![0,0,0,0,0,0,0,0,1,0,0,1,0,0,2,0], 4, 0, (-13), (-73), 0)
  | 128 => (![0,0,0,0,0,0,0,0,1,0,0,3,0,0,0,2], 6, 0, (-19), (-161), 0)
  | 129 => (![0,0,0,0,0,0,0,0,2,0,0,0,1,0,3,0], 6, 0, (-20), (-170), 0)
  | 130 => (![0,0,0,0,0,0,0,0,1,0,0,0,1,0,0,1], 3, 0, (-10), (-44), 0)
  | 131 => (![0,0,0,0,0,0,0,0,1,0,0,0,0,1,1,0], 3, 0, (-10), (-42), 0)
  | 132 => (![0,0,0,0,0,0,0,0,2,0,0,0,0,3,0,1], 6, 0, (-20), (-170), 0)
  | 133 => (![0,0,0,0,0,0,0,0,0,1,0,1,0,0,2,0], 4, 0, (-12), (-66), 0)
  | 134 => (![0,0,0,0,0,0,0,0,0,1,0,3,0,0,0,2], 6, 0, (-18), (-150), 0)
  | 135 => (![0,0,0,0,0,0,0,0,0,2,0,0,1,0,3,0], 6, 0, (-18), (-150), 0)
  | 136 => (![0,0,0,0,0,0,0,0,0,1,0,0,1,0,0,1], 3, 0, (-9), (-39), 0)
  | 137 => (![0,0,0,0,0,0,0,0,0,1,0,0,0,1,1,0], 3, 0, (-9), (-37), 0)
  | 138 => (![0,0,0,0,0,0,0,0,0,2,0,0,0,3,0,1], 6, 0, (-18), (-150), 0)
  | 139 => (![0,0,0,0,0,0,0,0,0,0,1,1,0,0,0,1], 3, 0, (-9), (-37), 0)
  | 140 => (![0,0,0,0,0,0,0,0,0,0,3,0,1,0,0,2], 6, 0, (-18), (-150), 0)
  | 141 => (![0,0,0,0,0,0,0,0,0,0,2,0,0,1,0,1], 4, 0, (-12), (-66), 0)
  | 142 => (![1,1,0,0,0,1,0,0,0,0,0,0,0,0,3,0], 3, 1, 0, 20, 2)
  | 143 => (![4,1,0,0,0,1,0,0,0,0,0,0,0,0,0,3], 3, 1, 6, 74, 2)
  | 144 => (![3,0,1,0,0,2,0,0,0,0,0,0,0,0,6,0], 6, 2, 0, 78, 2)
  | 145 => (![9,0,1,0,0,2,0,0,0,0,0,0,0,0,0,6], 6, 2, 12, 294, 2)
  | 146 => (![2,0,0,1,0,1,0,0,0,0,0,0,0,0,4,0], 4, 1, 2, 56, 2)
  | 147 => (![6,0,0,1,0,1,0,0,0,0,0,0,0,0,0,4], 4, 1, 10, 152, 2)
  | 148 => (![2,0,0,0,0,1,0,1,0,0,0,0,0,0,4,0], 5, 1, (-10), (-60), 2)
  | 149 => (![6,0,0,0,0,1,0,1,0,0,0,0,0,0,0,4], 5, 1, (-2), 36, 2)
  | 150 => (![3,0,0,0,0,2,0,0,1,0,0,0,0,0,6,0], 7, 2, (-10), (-64), 2)
  | 151 => (![9,0,0,0,0,2,0,0,1,0,0,0,0,0,0,6], 7, 2, 2, 152, 2)
  | 152 => (![4,0,0,0,0,3,0,0,0,1,0,0,0,0,8,0], 9, 3, (-10), (-54), 2)
  | 153 => (![12,0,0,0,0,3,0,0,0,1,0,0,0,0,0,8], 9, 3, 6, 330, 2)
  | 154 => (![2,0,0,0,0,2,0,0,0,0,1,0,0,0,5,0], 6, 2, (-8), (-44), 2)
  | 155 => (![7,0,0,0,0,2,0,0,0,0,1,0,0,0,0,5], 6, 2, 2, 106, 2)
  | 156 => (![2,0,0,0,0,1,0,0,0,0,0,1,0,0,0,2], 3, 1, (-2), 0, 2)
  | 157 => (![0,2,0,0,0,2,0,0,0,0,0,0,1,0,5,0], 6, 2, (-4), 14, 2)
  | 158 => (![0,3,0,0,0,3,0,0,0,0,0,0,4,0,0,5], 9, 3, (-6), (-6), 2)
  | 159 => (![0,1,0,0,0,1,0,0,0,0,0,0,0,1,2,0], 3, 1, (-2), 4, 2)
  | 160 => (![0,1,0,0,0,1,0,0,0,0,0,0,0,2,0,1], 3, 1, (-2), 2, 2)
  | 161 => (![0,0,2,0,0,4,0,0,0,0,0,0,3,0,9,0], 12, 4, (-12), (-66), 2)
  | 162 => (![0,0,1,0,0,2,0,0,0,0,0,0,3,0,0,3], 6, 2, (-6), (-30), 2)
  | 163 => (![0,0,1,0,0,2,0,0,0,0,0,0,0,3,3,0], 6, 2, (-6), (-12), 2)
  | 164 => (![0,0,2,0,0,4,0,0,0,0,0,0,0,9,0,3], 12, 4, (-12), (-66), 2)
  | 165 => (![0,0,0,1,0,1,0,0,0,0,0,0,1,0,3,0], 4, 1, (-2), 14, 2)
  | 166 => (![0,0,0,1,0,1,0,0,0,0,0,0,2,0,0,2], 4, 1, (-2), 8, 2)
  | 167 => (![0,0,0,1,0,1,0,0,0,0,0,0,0,2,2,0], 4, 1, (-2), 16, 2)
  | 168 => (![0,0,0,1,0,1,0,0,0,0,0,0,0,3,0,1], 4, 1, (-2), 14, 2)
  | 169 => (![0,0,0,0,0,1,0,1,0,0,0,0,1,0,3,0], 5, 1, (-14), (-102), 2)
  | 170 => (![0,0,0,0,0,1,0,1,0,0,0,0,2,0,0,2], 5, 1, (-14), (-108), 2)
  | 171 => (![0,0,0,0,0,1,0,1,0,0,0,0,0,2,2,0], 5, 1, (-14), (-100), 2)
  | 172 => (![0,0,0,0,0,1,0,1,0,0,0,0,0,3,0,1], 5, 1, (-14), (-102), 2)
  | 173 => (![0,0,0,0,0,4,0,0,2,0,0,0,3,0,9,0], 14, 4, (-32), (-634), 2)
  | 174 => (![0,0,0,0,0,2,0,0,1,0,0,0,3,0,0,3], 7, 2, (-16), (-172), 2)
  | 175 => (![0,0,0,0,0,2,0,0,1,0,0,0,0,3,3,0], 7, 2, (-16), (-154), 2)
  | 176 => (![0,0,0,0,0,4,0,0,2,0,0,0,0,9,0,3], 14, 4, (-32), (-634), 2)
  | 177 => (![0,0,0,0,0,3,0,0,0,1,0,0,2,0,6,0], 9, 3, (-18), (-222), 2)
  | 178 => (![0,0,0,0,0,3,0,0,0,1,0,0,4,0,0,4], 9, 3, (-18), (-246), 2)
  | 179 => (![0,0,0,0,0,3,0,0,0,1,0,0,0,4,4,0], 9, 3, (-18), (-214), 2)
  | 180 => (![0,0,0,0,0,3,0,0,0,1,0,0,0,6,0,2], 9, 3, (-18), (-222), 2)
  | 181 => (![0,0,0,0,0,2,0,0,0,0,1,0,1,0,4,0], 6, 2, (-12), (-98), 2)
  | 182 => (![0,0,0,0,0,6,0,0,0,0,3,0,7,0,0,8], 18, 6, (-36), (-978), 2)
  | 183 => (![0,0,0,0,0,2,0,0,0,0,1,0,0,2,3,0], 6, 2, (-12), (-96), 2)
  | 184 => (![0,0,0,0,0,4,0,0,0,0,2,0,0,7,0,3], 12, 4, (-24), (-402), 2)
  | 185 => (![0,0,0,0,0,3,0,0,0,0,0,3,2,0,0,4], 9, 3, (-18), (-240), 2)
  | _ => (![0,0,0,0,0,1,0,0,0,0,0,1,0,1,0,1], 3, 1, (-6), (-26), 2)

end
end D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound
