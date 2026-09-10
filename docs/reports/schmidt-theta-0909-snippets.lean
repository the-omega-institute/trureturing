import D5.S3.Quantum.Entanglement.CoherentHistorySchmidt
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.InnerProductSpace.SingularValues

/- Temporary bind-only elaboration probe. This file is not a D5 delivery. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Matrix
open D5.S3.Quantum.Entanglement
open OccupancyWordSectors CoherentHistorySchmidt

namespace SchmidtThetaProbe0909

def phase (x : ℝ) : ℂ := Complex.exp ((x : ℂ) * Complex.I)

theorem phase_star_mul (x : ℝ) : star (phase x) * phase x = 1 := by
  rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
  simp [Complex.normSq_eq_norm_sq, phase, Complex.norm_exp_ofReal_mul_I]

def phaseUnitary {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → ℝ) :
    Matrix.unitaryGroup ι ℂ :=
  ⟨Matrix.diagonal (fun i => phase (f i)), by
    rw [Matrix.mem_unitaryGroup_iff']
    simp only [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal]
    rw [← Matrix.diagonal_one]
    congr 1
    funext i
    exact phase_star_mul (f i)⟩

theorem unitary_gram_eigenvalues {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (M : Matrix m n ℂ)
    (U : Matrix.unitaryGroup m ℂ) (V : Matrix.unitaryGroup n ℂ) :
    (Matrix.isHermitian_conjTranspose_mul_self
      ((U : Matrix m m ℂ) * M * (V : Matrix n n ℂ))).eigenvalues =
      (Matrix.isHermitian_conjTranspose_mul_self M).eigenvalues := by
  apply (Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff _ _).mpr
  have hU : (U : Matrix m m ℂ)ᴴ * (U : Matrix m m ℂ) = 1 := U.prop.1
  have hGram : ((U : Matrix m m ℂ) * M * (V : Matrix n n ℂ))ᴴ *
      ((U : Matrix m m ℂ) * M * (V : Matrix n n ℂ)) =
      (V : Matrix n n ℂ)ᴴ * (Mᴴ * M) * (V : Matrix n n ℂ) := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (U : Matrix m m ℂ)ᴴ, hU, Matrix.one_mul]
  rw [hGram]
  rw [Matrix.charpoly_mul_comm, ← Matrix.mul_assoc,
    show (V : Matrix n n ℂ) * (V : Matrix n n ℂ)ᴴ = 1 from V.prop.2,
    Matrix.one_mul]

theorem unitary_rank {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (M : Matrix m n ℂ)
    (U : Matrix.unitaryGroup m ℂ) (V : Matrix.unitaryGroup n ℂ) :
    ((U : Matrix m m ℂ) * M * (V : Matrix n n ℂ)).rank = M.rank := by
  rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ (Matrix.UnitaryGroup.det_isUnit V),
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ (Matrix.UnitaryGroup.det_isUnit U)]

theorem gram_toEuclideanLin {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (M : Matrix m n ℂ) :
    (Mᴴ * M).toEuclideanLin = M.toEuclideanLin.adjoint.comp M.toEuclideanLin := by
  rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  simp only [Matrix.toEuclideanLin_eq_toLin_orthonormal]
  exact Matrix.toLin_mul (EuclideanSpace.basisFun n ℂ).toBasis
    (EuclideanSpace.basisFun m ℂ).toBasis (EuclideanSpace.basisFun n ℂ).toBasis Mᴴ M

theorem singular_values_of_gram_eigenvalues {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (M N : Matrix m n ℂ)
    (h : (Matrix.isHermitian_conjTranspose_mul_self M).eigenvalues =
      (Matrix.isHermitian_conjTranspose_mul_self N).eigenvalues) :
    M.toEuclideanLin.singularValues = N.toEuclideanLin.singularValues := by
  have hc := (Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff _ _).mp h
  have hp (A : Matrix m n ℂ) :
      (A.toEuclideanLin.adjoint.comp A.toEuclideanLin).charpoly = (Aᴴ * A).charpoly := by
    rw [← gram_toEuclideanLin, Matrix.toEuclideanLin_eq_toLin_orthonormal,
      Matrix.charpoly_toLin]
  have he := (LinearMap.IsSymmetric.eigenvalues_eq_eigenvalues_iff
    M.toEuclideanLin.isSymmetric_adjoint_comp_self rfl
    N.toEuclideanLin.isSymmetric_adjoint_comp_self rfl).mpr
      (by rw [hp, hp, hc])
  ext i
  by_cases hi : i < Module.finrank ℂ (EuclideanSpace ℂ n)
  · rw [M.toEuclideanLin.singularValues_of_lt rfl hi,
      N.toEuclideanLin.singularValues_of_lt rfl hi, he]
  · rw [M.toEuclideanLin.singularValues_of_finrank_le (Nat.le_of_not_gt hi),
      N.toEuclideanLin.singularValues_of_finrank_le (Nat.le_of_not_gt hi)]

def spectralEntropy {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (M : Matrix m n ℂ) : ℝ :=
  -∑ i ∈ M.toEuclideanLin.singularValues.support,
    M.toEuclideanLin.singularValues i ^ 2 * Real.log (M.toEuclideanLin.singularValues i ^ 2)

theorem entropy_log_argument_pos {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (M : Matrix m n ℂ) {i : ℕ} (hi : i ∈ M.toEuclideanLin.singularValues.support) :
    0 < M.toEuclideanLin.singularValues i ^ 2 := by
  exact sq_pos_of_pos ((M.toEuclideanLin.singularValues_pos_iff_ne_zero i).mpr
    (Finsupp.mem_support_iff.mp hi))

variable {α : Type*} [LinearOrder α] [Fintype α]

def area {n : ℕ} (w : Word α n) : ℕ :=
  ∑ i, ∑ j, if i < j ∧ w j < w i then 1 else 0

def crossArea (a b : Multiset α) : ℕ :=
  (a.map (fun x => (b.map (fun y => if y < x then (1 : ℕ) else 0)).sum)).sum

theorem cross_area_count_formula (a b : Multiset α) :
    crossArea a b = ∑ x, ∑ y, if y < x then a.count x * b.count y else 0 := by
  have hs (c : Multiset α) (f : α → ℕ) :
      (c.map f).sum = ∑ x, c.count x * f x := by
    rw [Finset.sum_multiset_map_count]
    simp only [nsmul_eq_mul]
    apply Finset.sum_subset (Finset.subset_univ _)
    intro x _ hx
    have hx' : x ∉ c := by simpa only [Multiset.mem_toFinset] using hx
    simp only [Multiset.count_eq_zero.mpr hx', Nat.cast_zero, zero_mul]
  simp only [crossArea, hs, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  by_cases h : y < x <;> simp [h]

theorem area_append {t s : ℕ} (u : Word α t) (v : Word α s) :
    area (Fin.append u v) = area u + area v + crossArea (occupation u) (occupation v) := by
  have hlt (i : Fin t) (j : Fin s) : i.castAdd s < j.natAdd t := by
    simp only [Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd]
    omega
  have hnlt (i : Fin t) (j : Fin s) : ¬ j.natAdd t < i.castAdd s :=
    not_lt_of_ge (hlt i j).le
  have hcast (i j : Fin t) : i.castAdd s < j.castAdd s ↔ i < j := Iff.rfl
  simp only [area, Fin.sum_univ_add, Finset.sum_add_distrib]
  simp [crossArea, occupation, List.sum_ofFn, hlt, hnlt, hcast,
    add_comm, add_left_comm, add_assoc]

theorem phase_add (x y : ℝ) : phase (x + y) = phase x * phase y := by
  simp [phase, Complex.ofReal_add, add_mul, Complex.exp_add]

def phasedSector (θ : ℝ) (n : ℕ) (a : Multiset α) (w : Word α n) : ℂ :=
  phase (θ * area w) * sectorVector n a w

def phasedMatrix (θ : ℝ) (a : Multiset α) (t s : ℕ) :
    Matrix (Word α t) (Word α s) ℂ :=
  fun u v => phase (θ * area (Fin.append u v)) * coefficientMatrix a t s u v

theorem phased_matrix_local_factors (θ : ℝ) (a : Multiset α) (t s : ℕ) :
    phasedMatrix θ a t s =
      (phaseUnitary (fun u : Word α t =>
        θ * (area u + crossArea (occupation u) (a - occupation u))) :
          Matrix (Word α t) (Word α t) ℂ) * coefficientMatrix a t s *
      (phaseUnitary (fun v : Word α s => θ * area v) :
          Matrix (Word α s) (Word α s) ℂ) := by
  ext u v
  by_cases h : occupation (Fin.append u v) = a
  · have hc : a - occupation u = occupation v := by
      rw [← h, occupation_append, add_comm, Multiset.add_sub_cancel_right]
    simp [phasedMatrix, phaseUnitary, coefficientMatrix, h, hc, area_append,
      Nat.cast_add, mul_add, phase_add, mul_comm, mul_left_comm, mul_assoc]
  · rw [occupation_append] at h
    simp [phasedMatrix, phaseUnitary, coefficientMatrix, h]

theorem phased_factorization (θ : ℝ) {a : Multiset α} {t s : ℕ}
    (h : a.card = t + s) (u : Word α t) (v : Word α s) :
    phasedMatrix θ a t s u v = ∑ b : Boundary a t,
      (schmidtCoefficient a t s b : ℂ) *
        phase (θ * crossArea b.val (a - b.val)) *
        phasedSector θ t b.val u * phasedSector θ s (a - b.val) v := by
  rw [phasedMatrix, normalized_coefficient_factorization h, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hu : occupation u = b.val <;> by_cases hv : occupation v = a - b.val
  · simp [phasedSector, area_append, hu, hv, Nat.cast_add, mul_add, phase_add,
      mul_comm, mul_left_comm, mul_assoc]
  · simp [phasedSector, sectorVector, sectorWords, hv]
  · simp [phasedSector, sectorVector, sectorWords, hu]
  · simp [phasedSector, sectorVector, sectorWords, hu]

theorem phase_preserves_gram {ι : Type*} [Fintype ι]
    (f : ι → ℝ) (x y : ι → ℂ) :
    (∑ i, star (phase (f i) * x i) * (phase (f i) * y i)) =
      ∑ i, star (x i) * y i := by
  apply Finset.sum_congr rfl
  intro i _
  rw [star_mul]
  calc
    star (x i) * star (phase (f i)) * (phase (f i) * y i) =
        (star (phase (f i)) * phase (f i)) * (star (x i) * y i) := by ring
    _ = star (x i) * y i := by rw [phase_star_mul, one_mul]

theorem phased_cut_sector_gram (θ : ℝ) {a : Multiset α} {t s : ℕ}
    (h : a.card = t + s) (b c : Boundary a t) :
    (∑ u : Word α t, star (phasedSector θ t b.val u) * phasedSector θ t c.val u =
      if b = c then 1 else 0) ∧
    (∑ v : Word α s, star (phasedSector θ s (a - b.val) v) *
      phasedSector θ s (a - c.val) v = if b = c then 1 else 0) := by
  simpa only [phasedSector, phase_preserves_gram] using cut_sector_gram h b c

theorem phased_state_normalized (θ : ℝ) {a : Multiset α} {n : ℕ} (h : a.card = n) :
    0 < (multiplicity n a : ℝ) ∧
      ∑ w : Word α n, star (phasedSector θ n a w) * phasedSector θ n a w = 1 := by
  refine ⟨by exact_mod_cast multiplicity_pos a h, ?_⟩
  simpa only [phasedSector, phase_preserves_gram, ite_true] using sector_gram a a h

theorem phased_matrix_is_state (θ : ℝ) (a : Multiset α) (t s : ℕ)
    (u : Word α t) (v : Word α s) :
    phasedMatrix θ a t s u v = phasedSector θ (t + s) a (Fin.append u v) := by
  rw [phasedMatrix, phasedSector, coefficient_eq_uniform_word]

theorem all_theta_cut_eigenvalues (θ : ℝ) (a : Multiset α) (t s : ℕ) :
    (Matrix.isHermitian_conjTranspose_mul_self (phasedMatrix θ a t s)).eigenvalues =
      (Matrix.isHermitian_conjTranspose_mul_self (coefficientMatrix a t s)).eigenvalues := by
  rw [phased_matrix_local_factors]
  exact unitary_gram_eigenvalues _ _ _

theorem all_theta_cut_singular_values (θ φ : ℝ) {a : Multiset α} {t s : ℕ}
    (h : a.card = t + s) :
    (phasedMatrix θ a t s).toEuclideanLin.singularValues =
      (phasedMatrix φ a t s).toEuclideanLin.singularValues := by
  apply singular_values_of_gram_eigenvalues
  rw [all_theta_cut_eigenvalues, all_theta_cut_eigenvalues]

theorem all_theta_cut_entropy (θ φ : ℝ) {a : Multiset α} {t s : ℕ}
    (h : a.card = t + s) :
    spectralEntropy (phasedMatrix θ a t s) = spectralEntropy (phasedMatrix φ a t s) := by
  simp only [spectralEntropy, all_theta_cut_singular_values θ φ h]

theorem all_theta_cut_rank (θ : ℝ) {a : Multiset α} {t s : ℕ}
    (h : a.card = t + s) :
    (phasedMatrix θ a t s).rank = (boundaries a t).card := by
  rw [phased_matrix_local_factors, unitary_rank, coefficient_rank h]

local instance : LinearOrder (Option (Fin 3)) :=
  inferInstanceAs (LinearOrder (WithBot (Fin 3)))

theorem all_theta_5040_rank (θ : ℝ) :
    (phasedMatrix θ occupation5040 4 4).rank = 12 := by
  rw [phased_matrix_local_factors, unitary_rank]
  exact history_5040_max_schmidt_rank.2

theorem normalization_positive {a : Multiset α} {t s : ℕ}
    (h : a.card = t + s) (b : Boundary a t) :
    0 < (multiplicity (t + s) a : ℝ) ∧
    0 < (multiplicity t b.val : ℝ) ∧ 0 < (multiplicity s (a - b.val) : ℝ) ∧
    0 < schmidtCoefficient a t s b := by
  exact ⟨by exact_mod_cast multiplicity_pos a h,
    by exact_mod_cast multiplicity_pos b.val (boundary_spec a t b).2,
    by exact_mod_cast multiplicity_pos (a - b.val) (complement_card h b),
    schmidt_coefficient_pos h b⟩

#print axioms phase_star_mul
#print axioms unitary_gram_eigenvalues
#print axioms unitary_rank
#print axioms gram_toEuclideanLin
#print axioms singular_values_of_gram_eigenvalues
#print axioms entropy_log_argument_pos
#print axioms cross_area_count_formula
#print axioms area_append
#print axioms phased_matrix_local_factors
#print axioms phased_factorization
#print axioms phased_cut_sector_gram
#print axioms phased_state_normalized
#print axioms phased_matrix_is_state
#print axioms all_theta_cut_eigenvalues
#print axioms all_theta_cut_singular_values
#print axioms all_theta_cut_entropy
#print axioms all_theta_cut_rank
#print axioms all_theta_5040_rank
#print axioms normalization_positive

end SchmidtThetaProbe0909
