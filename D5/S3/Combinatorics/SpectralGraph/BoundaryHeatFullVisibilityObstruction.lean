/- GID: D5/S3/Combinatorics/SpectralGraph/BoundaryHeatFullVisibilityObstruction
   generality: I
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/BoundaryHeatFullVisibilityObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Normed.Algebra.MatrixExponential, mathlib/module/Mathlib.LinearAlgebra.Vandermonde]
   utility: none
   digest: Two nonisomorphic weighted K4 Laplacians have identical one-port heat and full sampled visibility. -/

import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Tactic

/-! Two unit-mass weighted complete graphs have the same heat curve at a
cyclic boundary port. Weighted graph isomorphisms preserve the maximum edge
conductance, which separates the two graphs. -/

open scoped Matrix BigOperators
open Matrix

namespace D5.S3.Combinatorics.SpectralGraph.BoundaryHeatFullVisibilityObstruction

noncomputable section

abbrev Mat := Matrix (Fin 4) (Fin 4) ℝ

def L : Mat :=
  !![25/6, -11/6, -4/3, -1;
     -11/6, 25/6, -4/3, -1;
     -4/3, -4/3, 11/3, -1;
     -1, -1, -1, 3]

def U : Mat :=
  !![1, 0, 0, 0;
     0, 2/3, -1/3, 2/3;
     0, -1/3, 2/3, 2/3;
     0, 2/3, 2/3, -1/3]

def reflectedL : Mat := U * L * Uᵀ

/-- With unit masses the Laplacian itself generates the heat evolution. -/
def IsK4Laplacian (A : Mat) : Prop :=
  A.IsSymm ∧ (∀ i, ∑ j, A i j = 0) ∧ ∀ i j, i ≠ j → 0 < -A i j

def heatStep (A : Mat) (t : ℝ) : Mat :=
  NormedSpace.exp ((-t) • A)

def boundaryHeat (A : Mat) (t : ℝ) : ℝ :=
  heatStep A t 0 0

/-- Column j is the jth iterate of the heat step applied to the port vector. -/
def krylovFrame (A : Mat) (h : ℝ) : Mat :=
  Matrix.of fun i j => (heatStep A h ^ (j : ℕ)) i 0

def edgeConductances (A : Mat) : Multiset ℝ :=
  ([ -A 0 1, -A 0 2, -A 0 3, -A 1 2, -A 1 3, -A 2 3 ] : List ℝ)

def IsWeightedIso (A B : Mat) : Prop :=
  ∃ σ : Equiv.Perm (Fin 4), ∀ i j, i ≠ j → -A i j = -B (σ i) (σ j)

def conductanceValues (A : Mat) : Set ℝ :=
  {c | ∃ i j : Fin 4, i ≠ j ∧ c = -A i j}

private theorem greatest_eq_of_iso {A B : Mat} {a b : ℝ}
    (ha : IsGreatest (conductanceValues A) a)
    (hb : IsGreatest (conductanceValues B) b)
    (h : IsWeightedIso A B) : a = b := by
  obtain ⟨σ, hσ⟩ := h
  apply le_antisymm
  · obtain ⟨i, j, hij, hia⟩ := ha.1
    exact hb.2 ⟨σ i, σ j, fun he => hij (σ.injective he), hia.trans (hσ i j hij)⟩
  · obtain ⟨i, j, hij, hjb⟩ := hb.1
    have hne : σ.symm i ≠ σ.symm j := fun he => hij (σ.symm.injective he)
    have he : -A (σ.symm i) (σ.symm j) = -B i j := by
      simpa using hσ (σ.symm i) (σ.symm j) hne
    exact ha.2 ⟨σ.symm i, σ.symm j, hne, hjb.trans he.symm⟩

private theorem exp_similarity (P Q A : Mat) (hPQ : P * Q = 1) :
    NormedSpace.exp (P * A * Q) = P * NormedSpace.exp A * Q := by
  have hunit : IsUnit Q :=
    (Matrix.isUnit_iff_isUnit_det Q).2 (Matrix.isUnit_det_of_left_inverse hPQ)
  simpa only [Matrix.inv_eq_left_inv hPQ] using Matrix.exp_conj' Q A hunit

private theorem heatStep_similarity (P Q A : Mat) (hPQ : P * Q = 1) (t : ℝ) :
    heatStep (P * A * Q) t = P * heatStep A t * Q := by
  have hs : P * ((-t) • A) * Q = (-t) • (P * A * Q) := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
  unfold heatStep
  rw [← hs, exp_similarity P Q _ hPQ]

private theorem pow_similarity (P Q A : Mat) (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (n : ℕ) : (P * A * Q) ^ n = P * A ^ n * Q := by
  induction n with
  | zero => simp [hPQ]
  | succ n ih =>
    calc
      (P * A * Q) ^ (n + 1) = (P * A ^ n * Q) * (P * A * Q) := by
        rw [pow_succ, ih]
      _ = P * A ^ n * (Q * P) * A * Q := by simp only [mul_assoc]
      _ = P * A ^ (n + 1) * Q := by simp only [hQP, mul_one, pow_succ, mul_assoc]

private theorem mul_port (A V : Mat) (hV : ∀ i, V i 0 = (1 : Mat) i 0) (i : Fin 4) :
    (A * V) i 0 = A i 0 := by
  calc
    (A * V) i 0 = (A * 1) i 0 := by simp only [Matrix.mul_apply, hV]
    _ = A i 0 := by rw [mul_one]

private theorem boundaryHeat_conj (A V : Mat) (horth : Vᵀ * V = 1)
    (hport : ∀ i, V i 0 = (1 : Mat) i 0) (t : ℝ) :
    boundaryHeat (Vᵀ * A * V) t = boundaryHeat A t := by
  unfold boundaryHeat
  rw [heatStep_similarity _ _ _ horth, mul_port _ _ hport]
  calc
    (Vᵀ * heatStep A t) 0 0 = (1 * heatStep A t) 0 0 := by
      simp only [Matrix.mul_apply, Matrix.transpose_apply, hport]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : j = 0
      · subst j
        rfl
      · have hj' : (0 : Fin 4) ≠ j := fun he => hj he.symm
        rw [Matrix.one_apply_ne hj, Matrix.one_apply_ne hj']
    _ = heatStep A t 0 0 := by rw [one_mul]

private theorem krylovFrame_conj (A V : Mat) (horth : Vᵀ * V = 1)
    (hport : ∀ i, V i 0 = (1 : Mat) i 0) (h : ℝ) :
    krylovFrame (Vᵀ * A * V) h = Vᵀ * krylovFrame A h := by
  ext i j
  change (heatStep (Vᵀ * A * V) h ^ (j : ℕ)) i 0 = _
  rw [heatStep_similarity _ _ _ horth, pow_similarity _ _ _ horth (mul_eq_one_comm.mp horth),
    mul_port _ _ hport]
  simp only [Matrix.mul_apply, krylovFrame, Matrix.of_apply]

private theorem krylovFrame_conj_det_ne_zero (A V : Mat) (horth : Vᵀ * V = 1)
    (hport : ∀ i, V i 0 = (1 : Mat) i 0) (h : ℝ)
    (hdet : (krylovFrame A h).det ≠ 0) :
    (krylovFrame (Vᵀ * A * V) h).det ≠ 0 := by
  rw [krylovFrame_conj A V horth hport, Matrix.det_mul]
  exact mul_ne_zero (Matrix.det_ne_zero_of_right_inverse horth) hdet

private def eigenvalues : Fin 4 → ℝ := ![0, 4, 5, 6]

private def P : Mat :=
  !![1, 1, 1, 1;
     1, 1, 1, -1;
     1, 1, -2, 0;
     1, -3, 0, 0]

private def Q : Mat :=
  !![1/4, 1/4, 1/4, 1/4;
     1/12, 1/12, 1/12, -1/4;
     1/6, 1/6, -1/3, 0;
     1/2, -1/2, 0, 0]

private theorem Q_mul_P : Q * P = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Q, P, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_four, Fin.ext_iff]

private theorem P_mul_Q : P * Q = 1 := mul_eq_one_comm.mp Q_mul_P

private theorem L_spectral : L = P * Matrix.diagonal eigenvalues * Q := by
  have h : L * P = P * Matrix.diagonal eigenvalues := by
    ext i j
    rw [Matrix.mul_diagonal, Matrix.mul_apply]
    fin_cases i <;> fin_cases j <;>
      norm_num [L, P, eigenvalues, Fin.sum_univ_four]
  calc
    L = L * (P * Q) := by rw [P_mul_Q, mul_one]
    _ = P * Matrix.diagonal eigenvalues * Q := by rw [← mul_assoc, h]

private def heatEigenvalues (t : ℝ) (i : Fin 4) : ℝ :=
  Real.exp ((-t) * eigenvalues i)

private theorem heatStep_L (t : ℝ) :
    heatStep L t = P * Matrix.diagonal (heatEigenvalues t) * Q := by
  rw [L_spectral, heatStep_similarity _ _ _ P_mul_Q]
  unfold heatStep
  rw [← Matrix.diagonal_smul, Matrix.exp_diagonal, Pi.exp_def]
  have hentries : (fun i : Fin 4 => NormedSpace.exp (((-t) • eigenvalues) i)) =
      heatEigenvalues t := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, heatEigenvalues, Real.exp_eq_exp_ℝ]
  rw [hentries]

private theorem boundaryHeat_L (t : ℝ) :
    boundaryHeat L t =
      1/4 + Real.exp (-4*t)/12 + Real.exp (-5*t)/6 + Real.exp (-6*t)/2 := by
  have hentries : heatEigenvalues t =
      ![1, Real.exp (-4*t), Real.exp (-5*t), Real.exp (-6*t)] := by
    funext i
    fin_cases i <;> norm_num [heatEigenvalues, eigenvalues] <;> ring
  unfold boundaryHeat
  rw [heatStep_L, hentries, Matrix.mul_apply]
  norm_num [Matrix.mul_diagonal, Fin.sum_univ_four, P, Q] <;> ring

private theorem krylovFrame_L (h : ℝ) :
    krylovFrame L h =
      P * Matrix.diagonal (fun i => Q i 0) * Matrix.vandermonde (heatEigenvalues h) := by
  ext i j
  change (heatStep L h ^ (j : ℕ)) i 0 = _
  rw [heatStep_L, pow_similarity _ _ _ P_mul_Q Q_mul_P, Matrix.diagonal_pow]
  conv_lhs => rw [Matrix.mul_apply]
  conv_rhs => rw [mul_assoc, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.vandermonde_apply, Pi.pow_apply]
  apply Finset.sum_congr rfl
  intro k _
  ring

private theorem krylovFrame_L_det_ne_zero (h : ℝ) (hh : 0 < h) :
    (krylovFrame L h).det ≠ 0 := by
  have hrate : Function.Injective eigenvalues := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num [eigenvalues] at hij
    all_goals rfl
  have hheat : Function.Injective (heatEigenvalues h) := by
    intro i j hij
    apply hrate
    exact mul_left_cancel₀ (neg_ne_zero.mpr hh.ne') (Real.exp_injective hij)
  have hcoeff : ∀ i, Q i 0 ≠ 0 := by
    intro i
    fin_cases i <;> norm_num [Q]
  rw [krylovFrame_L, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
  exact mul_ne_zero
    (mul_ne_zero (Matrix.det_ne_zero_of_left_inverse Q_mul_P)
      (Finset.prod_ne_zero_iff.mpr fun i _ => hcoeff i))
    (Matrix.det_vandermonde_ne_zero_iff.mpr hheat)

private theorem U_symm : Uᵀ = U := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [U, Matrix.transpose_apply]

private theorem U_orth : Uᵀ * U = 1 := by
  rw [U_symm]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [U, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_four, Fin.ext_iff]

private theorem U_port (i : Fin 4) : U i 0 = (1 : Mat) i 0 := by
  fin_cases i <;> norm_num [U, Matrix.one_apply, Fin.ext_iff]

private theorem reflectedL_entries :
    reflectedL = !![25/6, -13/9, -17/18, -16/9;
            -13/9, 101/27, -43/27, -19/27;
            -17/18, -43/27, 193/54, -28/27;
            -16/9, -19/27, -28/27, 95/27] := by
  rw [reflectedL, U_symm]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [L, U, Matrix.mul_apply, Fin.sum_univ_four]

private theorem L_laplacian : IsK4Laplacian L := by
  refine ⟨?_, ?_, ?_⟩
  · apply Matrix.IsSymm.ext_iff.mpr
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num [L]
  · intro i
    fin_cases i <;> norm_num [L, Fin.sum_univ_four]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num [Fin.ext_iff] at hij
    all_goals norm_num [L]

private theorem reflectedL_laplacian : IsK4Laplacian reflectedL := by
  rw [reflectedL_entries]
  refine ⟨?_, ?_, ?_⟩
  · apply Matrix.IsSymm.ext_iff.mpr
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num
  · intro i
    fin_cases i <;> norm_num [Fin.sum_univ_four]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num [Fin.ext_iff] at hij
    all_goals norm_num

private theorem L_max : IsGreatest (conductanceValues L) (11/6) := by
  refine ⟨⟨0, 1, by decide, by norm_num [L]⟩, ?_⟩
  rintro x ⟨i, j, hij, rfl⟩
  fin_cases i <;> fin_cases j <;> norm_num [Fin.ext_iff] at hij
  all_goals norm_num [L]

private theorem reflectedL_max : IsGreatest (conductanceValues reflectedL) (16/9) := by
  refine ⟨⟨0, 3, by decide, by rw [reflectedL_entries]; norm_num⟩, ?_⟩
  rintro x ⟨i, j, hij, rfl⟩
  rw [reflectedL_entries]
  fin_cases i <;> fin_cases j <;> norm_num [Fin.ext_iff] at hij
  all_goals norm_num

private theorem conductance_multisets_ne : edgeConductances L ≠ edgeConductances reflectedL := by
  intro heq
  have ha : (11/6 : ℝ) ∈ edgeConductances L := by
    norm_num [edgeConductances, L, Multiset.mem_coe, List.mem_cons]
  have hb : (11/6 : ℝ) ∉ edgeConductances reflectedL := by
    rw [reflectedL_entries]
    norm_num [edgeConductances, Multiset.mem_coe, List.mem_cons]
  exact hb (heq ▸ ha)

/-- Two explicit unit-mass networks have identical heat at port 0 and full sampled visibility. -/
theorem boundary_heat_full_visibility_obstruction :
    IsK4Laplacian L ∧ IsK4Laplacian reflectedL ∧
    (∀ t : ℝ, boundaryHeat L t = boundaryHeat reflectedL t) ∧
    (∀ t : ℝ, boundaryHeat L t =
      1/4 + Real.exp (-4*t)/12 + Real.exp (-5*t)/6 + Real.exp (-6*t)/2) ∧
    (∀ h : ℝ, 0 < h → (krylovFrame L h).det ≠ 0 ∧ (krylovFrame reflectedL h).det ≠ 0) ∧
    IsGreatest (conductanceValues L) (11/6) ∧ IsGreatest (conductanceValues reflectedL) (16/9) ∧
    edgeConductances L ≠ edgeConductances reflectedL ∧ ¬ IsWeightedIso L reflectedL := by
  refine ⟨L_laplacian, reflectedL_laplacian, ?_, boundaryHeat_L, ?_, L_max, reflectedL_max,
    conductance_multisets_ne, ?_⟩
  · intro t
    simpa only [reflectedL, U_symm] using (boundaryHeat_conj L U U_orth U_port t).symm
  · intro h hh
    have hd := krylovFrame_L_det_ne_zero h hh
    refine ⟨hd, ?_⟩
    simpa only [reflectedL, U_symm] using krylovFrame_conj_det_ne_zero L U U_orth U_port h hd
  · intro hi
    have he := greatest_eq_of_iso L_max reflectedL_max hi
    norm_num at he

#print axioms boundary_heat_full_visibility_obstruction

end

end D5.S3.Combinatorics.SpectralGraph.BoundaryHeatFullVisibilityObstruction
