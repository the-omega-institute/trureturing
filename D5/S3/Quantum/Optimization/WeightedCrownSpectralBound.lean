/- GID: D5/S3/Quantum/Optimization/WeightedCrownSpectralBound
   generality: G
   mirror-B: D5/B/S3/Quantum/Optimization/WeightedCrownSpectralBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A singlet-sector spectral bound for weighted crowns. -/

/-
admission_basis: escape-witness.
escape_witness: crown_spectral_bound.
Escape audit unfinished: issue #15610 records missing observational-dependence evidence at
n = 3, x = 0 and x = 8, plus source-selection/report-decoding evidence for the hub/leaf
registrations. No completed registration is claimed.
site_apply_of_offEq: proof_shape: bind-only; escape_witness: none; consumers: site_adjoint, site_one, site_smul.
site_apply_of_not_offEq: proof_shape: bind-only; escape_witness: none; consumers: site_adjoint, site_one, site_smul.
site_mul_same: proof_shape: bind-only; escape_witness: none; consumers: site_pair_mul_left, site_pair_mul_pair, site_pair_mul_right, site_pair_shared, site_pair_shared_rev.
site_pair_formula: proof_shape: bind-only; escape_witness: none; consumers: site_mul_ne, site_pair_formula_reverse.
site_pair_formula_reverse: proof_shape: bind-only; escape_witness: none; consumers: site_mul_ne.
site_mul_ne: proof_shape: bind-only; escape_witness: none; consumers: pair_isHermitian, singlet_swap, site_pair_mul_left, site_pair_mul_pair, site_pair_shared, site_pair_shared_rev.
pauli_sq_X: proof_shape: bind-only; escape_witness: none; consumers: pair_XX, test_anti, test_hub.
pauli_sq_Y: proof_shape: bind-only; escape_witness: none; consumers: hub_annihilation_Y, pair_YY, test_anti.
pauli_sq_Z: proof_shape: bind-only; escape_witness: none; consumers: hub_annihilation_Z, pair_ZZ, test_anti.
pauli_mul_XY: proof_shape: bind-only; escape_witness: none; consumers: hub_annihilation_Y, pair_XY, test_anti.
pauli_mul_YX: proof_shape: bind-only; escape_witness: none; consumers: pauli_mul_YX_smul.
pauli_mul_YZ: proof_shape: bind-only; escape_witness: none; consumers: hub_annihilation_Z, pair_YZ, test_anti.
pauli_mul_ZY: proof_shape: bind-only; escape_witness: none; consumers: pauli_mul_ZY_smul.
pauli_mul_ZX: proof_shape: bind-only; escape_witness: none; consumers: pair_ZX, test_anti, test_hub.
pauli_mul_XZ: proof_shape: bind-only; escape_witness: none; consumers: pauli_mul_XZ_smul.
pauli_selfAdj_X: proof_shape: bind-only; escape_witness: none; consumers: singlet_isHermitian.
pauli_selfAdj_Y: proof_shape: bind-only; escape_witness: none; consumers: singlet_isHermitian.
pauli_selfAdj_Z: proof_shape: bind-only; escape_witness: none; consumers: singlet_isHermitian.
pauli_mul_YX_smul: proof_shape: bind-only; escape_witness: none; consumers: pair_YX, test_anti, test_hub.
pauli_mul_ZY_smul: proof_shape: bind-only; escape_witness: none; consumers: hub_annihilation_Y, pair_ZY, test_anti.
pauli_mul_XZ_smul: proof_shape: bind-only; escape_witness: none; consumers: hub_annihilation_Z, pair_XZ, test_anti.
site_one: proof_shape: bind-only; escape_witness: none; consumers: hub_annihilation_Y, hub_annihilation_Z, pair_XX, pair_YY, pair_ZZ, test_anti, test_hub.
site_smul: proof_shape: bind-only; escape_witness: none; consumers: hub_annihilation_Y, hub_annihilation_Z, pair_XY, pair_XZ, pair_YX, pair_YZ, pair_ZX, pair_ZY, test_anti, test_hub.
site_pair_mul_pair: proof_shape: bind-only; escape_witness: none; consumers: pair_XX, pair_XY, pair_XZ, pair_YX, pair_YY, pair_YZ, pair_ZX, pair_ZY, pair_ZZ.
pair_XX: proof_shape: bind-only; escape_witness: none; consumers: singlet_idempotent.
pair_YY: proof_shape: bind-only; escape_witness: none; consumers: singlet_idempotent.
pair_ZZ: proof_shape: bind-only; escape_witness: none; consumers: singlet_idempotent.
pair_XY: proof_shape: bind-only; escape_witness: none; consumers: singlet_idempotent.
pair_YX: proof_shape: bind-only; escape_witness: none; consumers: singlet_idempotent.
pair_YZ: proof_shape: bind-only; escape_witness: none; consumers: singlet_idempotent.
pair_ZY: proof_shape: bind-only; escape_witness: none; consumers: singlet_idempotent.
pair_ZX: proof_shape: bind-only; escape_witness: none; consumers: singlet_idempotent.
pair_XZ: proof_shape: bind-only; escape_witness: none; consumers: singlet_idempotent.
singlet_idempotent: proof_shape: bind-only; escape_witness: none; consumers: crownH_bound_psd, crown_certificate, singlet_posSemidef, star_square.
site_adjoint: proof_shape: bind-only; escape_witness: none; consumers: pair_isHermitian.
pair_isHermitian: proof_shape: bind-only; escape_witness: none; consumers: singlet_isHermitian.
singlet_isHermitian: proof_shape: bind-only; escape_witness: none; consumers: crownK_mul_P, singlet_posSemidef.
singlet_posSemidef: proof_shape: bind-only; escape_witness: none; consumers: crownH_bound_psd, leafEdge_pos, star_pos.
site_pair_mul_left: proof_shape: bind-only; escape_witness: none; consumers: hub_annihilation_Y, hub_annihilation_Z, test_hub.
site_pair_mul_right: proof_shape: bind-only; escape_witness: none; consumers: hub_annihilation_Y, hub_annihilation_Z, test_hub.
test_hub: proof_shape: bind-only; escape_witness: none; consumers: hub_annihilation.
site_pair_shared: proof_shape: bind-only; escape_witness: none; consumers: test_anti.
site_pair_shared_rev: proof_shape: bind-only; escape_witness: none; consumers: test_anti.
matrix_div_two: proof_shape: bind-only; escape_witness: none; consumers: star_square, test_anti.
test_anti: proof_shape: bind-only; escape_witness: none; consumers: star_square.
hub_annihilation_Y: proof_shape: bind-only; escape_witness: none; consumers: hub_annihilation.
hub_annihilation_Z: proof_shape: bind-only; escape_witness: none; consumers: hub_annihilation.
hub_annihilation: proof_shape: bind-only; escape_witness: none; consumers: singlet_mul_pair_sum.
singlet_mul_pair_sum: proof_shape: bind-only; escape_witness: none; consumers: crownP_mul_K.
a_ne_leaf: proof_shape: bind-only; escape_witness: none; consumers: encode_left, leftEdge, moment_feasible, moment_objective, objective_on_active, pair_shapes, _simp_1, crownK_bound, crownK_mul_P, crownP_mul_K.
b_ne_leaf: proof_shape: bind-only; escape_witness: none; consumers: encode_right, moment_feasible, moment_objective, objective_on_active, pair_shapes, rightEdge, _simp_1, crownK_bound, crownK_mul_P, crownP_mul_K.
matrix_le_scalar_of_sq_le: proof_shape: bind-only; escape_witness: none; consumers: star_bound.
projection_certificate: proof_shape: bind-only; escape_witness: none; consumers: crown_certificate.
projection_certificate_posSemidef: proof_shape: bind-only; escape_witness: none; consumers: crownH_bound_psd.
leaf_ne_leaf: proof_shape: bind-only; escape_witness: none; consumers: leafEdge_pos, star_square.
star_square: proof_shape: bind-only; escape_witness: none; consumers: star_square_unordered.
singlet_swap: proof_shape: bind-only; escape_witness: none; consumers: leafEdgeSum_twice.
leafEdgeSum_twice: proof_shape: bind-only; escape_witness: none; consumers: star_sq_le, star_square_unordered.
star_square_unordered: proof_shape: bind-only; escape_witness: none; consumers: star_sq_le.
leafEdge_pos: proof_shape: bind-only; escape_witness: none; consumers: star_sq_le.
star_pos: proof_shape: bind-only; escape_witness: none; consumers: crownK_mul_P, star_bound.
star_sq_le: proof_shape: bind-only; escape_witness: none; consumers: star_bound.
star_bound: proof_shape: content; escape_witness: self; consumers: crownK_bound.
crownP_mul_K: proof_shape: bind-only; escape_witness: none; consumers: crownK_mul_P, crown_certificate.
crownK_mul_P: proof_shape: bind-only; escape_witness: none; consumers: crown_certificate.
crownK_bound: proof_shape: content; escape_witness: star_bound; consumers: crownH_bound_psd.
crown_certificate: proof_shape: bind-only; escape_witness: none; consumers: crownH_bound_psd.
crownH_bound_psd: proof_shape: content; escape_witness: star_bound; consumers: crown_spectral_bound.
rayleigh_le_of_posSemidef: proof_shape: bind-only; escape_witness: none; consumers: crown_spectral_bound.
crown_spectral_bound: proof_shape: content; escape_witness: self; consumers: result.
Direct frozen dependencies:
  D5/S3/Quantum/FiniteDimensional.QubitMatrix; declaration statement_id: sha256:e376bbe008ddbbc49fcf9763247304ed70ec54ac5cf49af3c6f7fb58fa626f30.
  D5/S3/Quantum/FiniteDimensional.qubitX; declaration statement_id: sha256:cfaddf4a17693b52013e93be8cd6559e7021ed57ca0305492712468b57f882f7.
  D5/S3/Quantum/FiniteDimensional.qubitZ; declaration statement_id: sha256:381a2bec567456715f58fe6c0c413d59d37882b8499fc81a486c49e7c081d78c.
  D5/S3/Quantum/FiniteDimensional.qubit_weyl_star; declaration statement_id: sha256:be07b0533dfdb8741136a43d8272fd7a664770fb9b4a851805c5db573532362d.
Utility none: uniform operator and real-parameter constructions, not finite enumeration.
-/

import D5.S3.Quantum.FiniteDimensional

noncomputable section
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace D5.S3.Quantum.Optimization.WeightedCrownSpectralBound
open D5.S3.Quantum.FiniteDimensional (qubitX qubitZ qubit_weyl_star)
attribute [local instance] Classical.propDecidable

def a (n : ℕ) : (Option (Option (Fin n))) := none

def b (n : ℕ) : (Option (Option (Fin n))) := some none

def leaf {n : ℕ} (i : Fin n) : (Option (Option (Fin n))) := some (some i)

def site {n : ℕ} (i : (Option (Option (Fin n)))) (A : Matrix (Fin 2) (Fin 2) ℂ) : (Matrix (Option (Option (Fin n)) → Fin 2) (Option (Option (Fin n)) → Fin 2) ℂ) :=
  fun s t => ∏ k, if k = i then A (s k) (t k) else if s k = t k then 1 else 0

def singlet {n : ℕ} (i j : (Option (Option (Fin n)))) : (Matrix (Option (Option (Fin n)) → Fin 2) (Option (Option (Fin n)) → Fin 2) ℂ) :=
  (1 / 4 : ℂ) • (1 - site i qubitX * site j qubitX - site i (Complex.I • (qubitX * qubitZ)) * site j (Complex.I • (qubitX * qubitZ)) - site i qubitZ * site j qubitZ)

private def offEq {n : ℕ} (i : Option (Option (Fin n))) (s t : Option (Option (Fin n)) → Fin 2) : Prop := ∀ k, k ≠ i → s k = t k

private lemma site_apply_of_offEq {n : ℕ} (i : Option (Option (Fin n))) (A : Matrix (Fin 2) (Fin 2) ℂ) (s t : Option (Option (Fin n)) → Fin 2) (h : offEq i s t) : site i A s t = A (s i) (t i) := by
  classical
  simp only [site]
  change Finset.prod (Finset.univ : Finset (Option (Option (Fin n))))
      (fun k => if k = i then A (s k) (t k) else if s k = t k then 1 else 0) = _
  have hp := Finset.prod_eq_single (s := (Finset.univ : Finset (Option (Option (Fin n)))))
    (f := fun k => if k = i then A (s k) (t k) else if s k = t k then 1 else 0) i
      (by
        intro k hk hki
        simp only [hki, ↓reduceIte]
        simp [h k hki])
      (by simp)
  simpa using hp

private lemma site_apply_of_not_offEq {n : ℕ} (i : Option (Option (Fin n))) (A : Matrix (Fin 2) (Fin 2) ℂ) (s t : Option (Option (Fin n)) → Fin 2) (h : ¬ offEq i s t) : site i A s t = 0 := by
  classical
  simp only [site]
  unfold offEq at h
  push Not at h
  obtain ⟨k, hki, hst⟩ := h
  have hz : (if k = i then A (s k) (t k) else if s k = t k then 1 else 0) = 0 := by
    simp [hki, hst]
  apply Finset.prod_eq_zero (Finset.mem_univ k)
  simp [hz]


private lemma site_mul_same {n : ℕ} (i : Option (Option (Fin n))) (A B : Matrix (Fin 2) (Fin 2) ℂ) : site i A * site i B = site i (A * B) := by
  ext s t
  simp only [site, Matrix.mul_apply]
  simp_rw [← Finset.prod_mul_distrib]
  let f : Option (Option (Fin n)) → Fin 2 → ℂ := fun k q =>
    (if k = i then A (s k) q else if s k = q then 1 else 0) *
    (if k = i then B q (t k) else if q = t k then 1 else 0)
  change (∑ x : Option (Option (Fin n)) → Fin 2, ∏ k, f k (x k)) = _
  rw [← Fintype.prod_sum f]
  apply Finset.prod_congr rfl
  intro k hk
  by_cases hki : k = i
  · simp [f, hki, Matrix.mul_apply]
  · simp [f, hki, ite_mul, Finset.sum_ite]

private def outsideEq {n : ℕ} (i j : Option (Option (Fin n)))
    (s t : Option (Option (Fin n)) → Fin 2) : Prop :=
  ∀ k, k ≠ i → k ≠ j → s k = t k
private lemma site_pair_formula {n : ℕ} {i j : Option (Option (Fin n))} (hij : i ≠ j) (A B : Matrix (Fin 2) (Fin 2) ℂ) (s t : Option (Option (Fin n)) → Fin 2) : (site i A * site j B) s t = if outsideEq i j s t then A (s i) (t i) * B (s j) (t j) else 0 := by
  simp only [site, Matrix.mul_apply]
  simp_rw [← Finset.prod_mul_distrib]
  let f : Option (Option (Fin n)) → Fin 2 → ℂ := fun k q =>
    (if k = i then A (s k) q else if s k = q then 1 else 0) *
    (if k = j then B q (t k) else if q = t k then 1 else 0)
  change (∑ x : Option (Option (Fin n)) → Fin 2, ∏ k, f k (x k)) = _
  rw [← Fintype.prod_sum f]
  have he (k : Option (Option (Fin n))) :
      (∑ q, f k q) = if k = i then A (s k) (t k) else if k = j then B (s k) (t k)
        else if s k = t k then 1 else 0 := by
    by_cases hki : k = i
    · subst k
      simp [f, hij, Finset.sum_ite]
    · by_cases hkj : k = j
      · subst k
        simp [f, hij.symm, Finset.sum_ite, ite_mul]
      · simp [f, hki, hkj, ite_mul, Finset.sum_ite]
  simp_rw [he]
  by_cases h : outsideEq i j s t
  · rw [if_pos h]
    rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ i)]
    simp only [ite_true]
    rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (show j ∈ Finset.univ \ {i} by simp [hij.symm])]
    simp only [hij.symm, ite_false, ite_true]
    have hz : ∏ k ∈ (Finset.univ \ {i}) \ {j},
      (if k = i then A (s k) (t k) else if k = j then B (s k) (t k) else if s k = t k then 1 else 0) = 1 := by
      apply Finset.prod_eq_one
      intro k hk
      simp only [Finset.mem_sdiff, Finset.mem_singleton] at hk
      simp [hk.1.2, hk.2, h k hk.1.2 hk.2]
    rw [hz, mul_one]
  · rw [if_neg h]
    unfold outsideEq at h
    push Not at h
    obtain ⟨k,hki,hkj,hst⟩ := h
    apply Finset.prod_eq_zero (Finset.mem_univ k)
    simp [hki,hkj,hst]

private lemma site_pair_formula_reverse {n : ℕ} {i j : (Option (Option (Fin n)))} (hij : i ≠ j) (A B : Matrix (Fin 2) (Fin 2) ℂ) (s t : (Option (Option (Fin n)) → Fin 2)) : (site j B * site i A) s t = if outsideEq i j s t then B (s j) (t j) * A (s i) (t i) else 0 := by
  classical
  have horder : outsideEq j i s t ↔ outsideEq i j s t := by
    constructor
    · intro h k hki hkj
      exact h k hkj hki
    · intro h k hkj hki
      exact h k hki hkj
  have h := site_pair_formula (i := j) (j := i) hij.symm B A s t
  simpa only [propext horder] using h

private lemma site_mul_ne {n : ℕ} {i j : (Option (Option (Fin n)))} (hij : i ≠ j) (A B : Matrix (Fin 2) (Fin 2) ℂ) : site i A * site j B = site j B * site i A := by
  ext s t
  rw [site_pair_formula hij A B s t, site_pair_formula_reverse hij A B s t]
  split_ifs <;> ring

private lemma pauli_sq_X : qubitX * qubitX = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  simpa only [pow_two] using qubit_weyl_star.2.2.2.1

private lemma pauli_sq_Y : (Complex.I • (qubitX * qubitZ)) * (Complex.I • (qubitX * qubitZ)) = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [qubitX, qubitZ, smul_eq_mul, Matrix.mul_apply, Fin.sum_univ_two]

private lemma pauli_sq_Z : qubitZ * qubitZ = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  simpa only [pow_two] using qubit_weyl_star.2.2.2.2

private lemma pauli_mul_XY : qubitX * (Complex.I • (qubitX * qubitZ)) = Complex.I • qubitZ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [qubitX, qubitZ, Matrix.mul_apply, Fin.sum_univ_two, smul_eq_mul]

private lemma pauli_mul_YX : (Complex.I • (qubitX * qubitZ)) * qubitX = -(Complex.I • qubitZ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [qubitX, qubitZ, Matrix.mul_apply, Fin.sum_univ_two, smul_eq_mul]

private lemma pauli_mul_YZ : (Complex.I • (qubitX * qubitZ)) * qubitZ = Complex.I • qubitX := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [qubitX, qubitZ, Matrix.mul_apply, Fin.sum_univ_two, smul_eq_mul]

private lemma pauli_mul_ZY : qubitZ * (Complex.I • (qubitX * qubitZ)) = -(Complex.I • qubitX) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [qubitX, qubitZ, Matrix.mul_apply, Fin.sum_univ_two, smul_eq_mul]

private lemma pauli_mul_ZX : qubitZ * qubitX = Complex.I • (Complex.I • (qubitX * qubitZ)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [qubitX, qubitZ, Matrix.mul_apply, Fin.sum_univ_two, smul_eq_mul]

private lemma pauli_mul_XZ : qubitX * qubitZ = -(Complex.I • (Complex.I • (qubitX * qubitZ))) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [qubitX, qubitZ, Matrix.mul_apply, Fin.sum_univ_two, smul_eq_mul]

private lemma pauli_selfAdj_X : qubitX.IsHermitian := by
  exact qubit_weyl_star.2.1

private lemma pauli_selfAdj_Y : (Complex.I • (qubitX * qubitZ)).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;> norm_num [qubitX, qubitZ, smul_eq_mul, star]

private lemma pauli_selfAdj_Z : qubitZ.IsHermitian := by
  exact qubit_weyl_star.2.2.1

private lemma pauli_mul_YX_smul : (Complex.I • (qubitX * qubitZ)) * qubitX = (-Complex.I) • qubitZ := by
  rw [pauli_mul_YX, neg_smul]

private lemma pauli_mul_ZY_smul : qubitZ * (Complex.I • (qubitX * qubitZ)) = (-Complex.I) • qubitX := by
  rw [pauli_mul_ZY, neg_smul]

private lemma pauli_mul_XZ_smul : qubitX * qubitZ = (-Complex.I) • (Complex.I • (qubitX * qubitZ)) := by
  simpa only [neg_smul] using pauli_mul_XZ

private lemma site_one {n : ℕ} (i : (Option (Option (Fin n)))) : site i (1 : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
  ext s t
  by_cases hst : offEq i s t
  · rw [site_apply_of_offEq i (1 : Matrix (Fin 2) (Fin 2) ℂ) s t hst]
    by_cases hi : s i = t i
    · have heq : s = t := by
        funext k
        by_cases hk : k = i
        · simp [hk, hi]
        · exact hst k hk
      subst t
      simp
    · have hentry : (1 : Matrix (Fin 2) (Fin 2) ℂ) (s i) (t i) = 0 := by
        simp [Matrix.one_apply, hi]
      rw [hentry]
      have hneq : s ≠ t := by
        intro h
        apply hi
        rw [h]
      simp [Matrix.one_apply, hneq]
  · rw [site_apply_of_not_offEq i (1 : Matrix (Fin 2) (Fin 2) ℂ) s t hst]
    have hneq : s ≠ t := by
      intro h
      apply hst
      subst t
      intro k hk
      rfl
    simp [Matrix.one_apply, hneq]

private lemma site_smul {n : ℕ} (i : (Option (Option (Fin n)))) (c : ℂ) (A : Matrix (Fin 2) (Fin 2) ℂ) : site i (c • A) = c • site i A := by
  ext s t
  by_cases hst : offEq i s t
  · have hA : site i A s t = A (s i) (t i) := site_apply_of_offEq i A s t hst
    rw [site_apply_of_offEq i (c • A) s t hst]
    change c * A (s i) (t i) = c * site i A s t
    rw [hA]
  · have hA : site i A s t = 0 := site_apply_of_not_offEq i A s t hst
    rw [site_apply_of_not_offEq i (c • A) s t hst]
    change 0 = c * site i A s t
    rw [hA]
    simp

private lemma site_pair_mul_pair {n : ℕ} {i j : (Option (Option (Fin n)))} (hij : i ≠ j) (A B C D : Matrix (Fin 2) (Fin 2) ℂ) : (site i A * site j B) * (site i C * site j D) = site i (A * C) * site j (B * D) := by
  calc
    (site i A * site j B) * (site i C * site j D) =
        site i A * (site j B * site i C) * site j D := by
          simp only [mul_assoc]
    _ = site i A * (site i C * site j B) * site j D := by
          rw [site_mul_ne hij.symm B C]
    _ = (site i A * site i C) * (site j B * site j D) := by
          simp only [mul_assoc]
    _ = site i (A * C) * site j (B * D) := by
          rw [site_mul_same i A C, site_mul_same j B D]

private lemma pair_XX {n : ℕ} {i j : (Option (Option (Fin n)))} (hij : i ≠ j) : (site i qubitX * site j qubitX) * (site i qubitX * site j qubitX) = 1 := by
  rw [site_pair_mul_pair hij qubitX qubitX qubitX qubitX, pauli_sq_X, site_one, site_one]
  simp

private lemma pair_YY {n : ℕ} {i j : (Option (Option (Fin n)))} (hij : i ≠ j) : (site i (Complex.I • (qubitX * qubitZ)) * site j (Complex.I • (qubitX * qubitZ))) * (site i (Complex.I • (qubitX * qubitZ)) * site j (Complex.I • (qubitX * qubitZ))) = 1 := by
  rw [site_pair_mul_pair hij (Complex.I • (qubitX * qubitZ)) (Complex.I • (qubitX * qubitZ)) (Complex.I • (qubitX * qubitZ)) (Complex.I • (qubitX * qubitZ)), pauli_sq_Y, site_one, site_one]
  simp

private lemma pair_ZZ {n : ℕ} {i j : (Option (Option (Fin n)))} (hij : i ≠ j) : (site i qubitZ * site j qubitZ) * (site i qubitZ * site j qubitZ) = 1 := by
  rw [site_pair_mul_pair hij qubitZ qubitZ qubitZ qubitZ, pauli_sq_Z, site_one, site_one]
  simp

private lemma pair_XY {n : ℕ} {i j : (Option (Option (Fin n)))} (hij : i ≠ j) : (site i qubitX * site j qubitX) * (site i (Complex.I • (qubitX * qubitZ)) * site j (Complex.I • (qubitX * qubitZ))) = -(site i qubitZ * site j qubitZ) := by
  rw [site_pair_mul_pair hij qubitX qubitX (Complex.I • (qubitX * qubitZ)) (Complex.I • (qubitX * qubitZ)), pauli_mul_XY,
    site_smul, site_smul]
  simp [Matrix.smul_mul, Matrix.mul_smul, smul_smul]

private lemma pair_YX {n : ℕ} {i j : (Option (Option (Fin n)))} (hij : i ≠ j) : (site i (Complex.I • (qubitX * qubitZ)) * site j (Complex.I • (qubitX * qubitZ))) * (site i qubitX * site j qubitX) = -(site i qubitZ * site j qubitZ) := by
  rw [site_pair_mul_pair hij (Complex.I • (qubitX * qubitZ)) (Complex.I • (qubitX * qubitZ)) qubitX qubitX, pauli_mul_YX_smul,
    site_smul, site_smul]
  simp [Matrix.smul_mul, Matrix.mul_smul, smul_smul]

private lemma pair_YZ {n : ℕ} {i j : (Option (Option (Fin n)))} (hij : i ≠ j) : (site i (Complex.I • (qubitX * qubitZ)) * site j (Complex.I • (qubitX * qubitZ))) * (site i qubitZ * site j qubitZ) = -(site i qubitX * site j qubitX) := by
  rw [site_pair_mul_pair hij (Complex.I • (qubitX * qubitZ)) (Complex.I • (qubitX * qubitZ)) qubitZ qubitZ, pauli_mul_YZ,
    site_smul, site_smul]
  simp [Matrix.smul_mul, Matrix.mul_smul, smul_smul]

private lemma pair_ZY {n : ℕ} {i j : (Option (Option (Fin n)))} (hij : i ≠ j) : (site i qubitZ * site j qubitZ) * (site i (Complex.I • (qubitX * qubitZ)) * site j (Complex.I • (qubitX * qubitZ))) = -(site i qubitX * site j qubitX) := by
  rw [site_pair_mul_pair hij qubitZ qubitZ (Complex.I • (qubitX * qubitZ)) (Complex.I • (qubitX * qubitZ)), pauli_mul_ZY_smul,
    site_smul, site_smul]
  simp [Matrix.smul_mul, Matrix.mul_smul, smul_smul]

private lemma pair_ZX {n : ℕ} {i j : (Option (Option (Fin n)))} (hij : i ≠ j) : (site i qubitZ * site j qubitZ) * (site i qubitX * site j qubitX) = -(site i (Complex.I • (qubitX * qubitZ)) * site j (Complex.I • (qubitX * qubitZ))) := by
  have hPauli := pauli_mul_ZX
  generalize (Complex.I • (qubitX * qubitZ)) = Y at hPauli ⊢
  rw [site_pair_mul_pair hij qubitZ qubitZ qubitX qubitX, hPauli,
    site_smul, site_smul]
  simp [Matrix.smul_mul, Matrix.mul_smul, smul_smul]

private lemma pair_XZ {n : ℕ} {i j : (Option (Option (Fin n)))} (hij : i ≠ j) : (site i qubitX * site j qubitX) * (site i qubitZ * site j qubitZ) = -(site i (Complex.I • (qubitX * qubitZ)) * site j (Complex.I • (qubitX * qubitZ))) := by
  have hPauli := pauli_mul_XZ_smul
  generalize (Complex.I • (qubitX * qubitZ)) = Y at hPauli ⊢
  rw [site_pair_mul_pair hij qubitX qubitX qubitZ qubitZ, hPauli,
    site_smul, site_smul]
  simp [Matrix.smul_mul, Matrix.mul_smul, smul_smul]

private lemma singlet_idempotent {n : ℕ} {i j : (Option (Option (Fin n)))} (hij : i ≠ j) : singlet i j * singlet i j = singlet i j := by
  unfold singlet
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  simp only [sub_mul, mul_sub, add_mul, mul_add]
  simp only [one_mul, mul_one]
  rw [pair_XX hij, pair_YY hij, pair_ZZ hij,
    pair_XY hij, pair_YX hij, pair_YZ hij, pair_ZY hij,
    pair_ZX hij, pair_XZ hij]
  -- scalar normalization in the remaining commutative coefficient ring
  module

private lemma site_adjoint {n : ℕ} (i : (Option (Option (Fin n)))) (A : Matrix (Fin 2) (Fin 2) ℂ) : (site i A)ᴴ = site i Aᴴ := by
  ext s t
  change star (site i A t s) = site i Aᴴ s t
  by_cases hst : offEq i t s
  · have hts : offEq i s t := by
      intro k hk
      exact (hst k hk).symm
    rw [site_apply_of_offEq i A t s hst, site_apply_of_offEq i Aᴴ s t hts]
    rfl
  · have hts : ¬offEq i s t := by
      intro h
      apply hst
      intro k hk
      exact (h k hk).symm
    rw [site_apply_of_not_offEq i A t s hst, site_apply_of_not_offEq i Aᴴ s t hts]
    simp

private lemma pair_isHermitian {n : ℕ} {i j : (Option (Option (Fin n)))} (hij : i ≠ j) (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.IsHermitian) : (site i A * site j A).IsHermitian := by
  change (site i A * site j A)ᴴ = site i A * site j A
  rw [Matrix.conjTranspose_mul, site_adjoint, site_adjoint, hA.eq]
  exact site_mul_ne hij.symm A A

private lemma singlet_isHermitian {n : ℕ} {i j : (Option (Option (Fin n)))} (hij : i ≠ j) : (singlet i j).IsHermitian := by
  unfold singlet
  apply Matrix.IsHermitian.smul
  · exact ((Matrix.isHermitian_one.sub (pair_isHermitian hij qubitX pauli_selfAdj_X)).sub
      (pair_isHermitian hij (Complex.I • (qubitX * qubitZ)) pauli_selfAdj_Y)).sub (pair_isHermitian hij qubitZ pauli_selfAdj_Z)
  · apply Complex.ext <;> norm_num [IsSelfAdjoint, star]

private lemma singlet_posSemidef {n : ℕ} {i j : (Option (Option (Fin n)))} (hij : i ≠ j) : (singlet i j).PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self (singlet i j)
  rw [(singlet_isHermitian hij).eq, singlet_idempotent hij] at h
  exact h

private lemma site_pair_mul_left {n : ℕ} {i j : (Option (Option (Fin n)))} (hij : i ≠ j) (A B C : Matrix (Fin 2) (Fin 2) ℂ) : (site i A * site j B) * site i C = site i (A * C) * site j B := by
  calc
    (site i A * site j B) * site i C = site i A * (site j B * site i C) := by simp only [mul_assoc]
    _ = site i A * (site i C * site j B) := by rw [site_mul_ne hij.symm B C]
    _ = site i (A * C) * site j B := by
      rw [← mul_assoc, site_mul_same i A C]
private lemma site_pair_mul_right {n : ℕ} {i j : (Option (Option (Fin n)))} (hij : i ≠ j) (A B C : Matrix (Fin 2) (Fin 2) ℂ) : (site i A * site j B) * site j C = site i A * site j (B * C) := by
  calc
    (site i A * site j B) * site j C = site i A * (site j B * site j C) := by simp only [mul_assoc]
    _ = site i A * site j (B * C) := by rw [site_mul_same j B C]

private lemma test_hub {n : ℕ} {i j : (Option (Option (Fin n)))} (hij : i ≠ j) : singlet i j * (site i qubitX + site j qubitX) = 0 := by
  unfold singlet
  have hPauli0 := pauli_sq_X
  have hPauli1 := pauli_mul_YX_smul
  have hPauli2 := pauli_mul_ZX
  generalize (Complex.I • (qubitX * qubitZ)) = Y at hPauli0 hPauli1 hPauli2 ⊢
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  simp only [sub_mul, mul_sub, add_mul, mul_add]
  simp only [one_mul, mul_one]
  rw [site_pair_mul_left hij qubitX qubitX qubitX, site_pair_mul_left hij Y Y qubitX,
    site_pair_mul_left hij qubitZ qubitZ qubitX, site_pair_mul_right hij qubitX qubitX qubitX,
    site_pair_mul_right hij Y Y qubitX, site_pair_mul_right hij qubitZ qubitZ qubitX]
  rw [hPauli0, hPauli1, hPauli2,
    site_smul, site_smul, site_smul, site_smul]
  simp [Matrix.smul_mul, Matrix.mul_smul, smul_smul, site_one]
  module

private lemma site_pair_shared {n : ℕ} {i j k : (Option (Option (Fin n)))} (hij : i ≠ j) (hik : i ≠ k) (A B C D : Matrix (Fin 2) (Fin 2) ℂ) : (site i A * site j B) * (site i C * site k D) = site i (A * C) * site j B * site k D := by
  calc
    (site i A * site j B) * (site i C * site k D) =
        site i A * (site j B * site i C) * site k D := by simp only [mul_assoc]
    _ = site i A * (site i C * site j B) * site k D := by
      rw [site_mul_ne hij.symm B C]
    _ = (site i A * site i C) * site j B * site k D := by
      simp only [mul_assoc]
    _ = site i (A * C) * site j B * site k D := by
      rw [site_mul_same i A C]

private lemma site_pair_shared_rev {n : ℕ} {i j k : (Option (Option (Fin n)))} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (A B C D : Matrix (Fin 2) (Fin 2) ℂ) : (site i A * site k B) * (site i C * site j D) = site i (A * C) * site j D * site k B := by
  calc
    (site i A * site k B) * (site i C * site j D) =
        site i A * (site k B * site i C) * site j D := by simp only [mul_assoc]
    _ = site i A * (site i C * site k B) * site j D := by
      rw [site_mul_ne hik.symm B C]
    _ = (site i A * site i C) * site k B * site j D := by simp only [mul_assoc]
    _ = site i (A * C) * site k B * site j D := by rw [site_mul_same i A C]
    _ = site i (A * C) * site j D * site k B := by
      rw [mul_assoc, site_mul_ne hjk.symm B D, ← mul_assoc]

private lemma matrix_div_two {m : Type*} [Fintype m] [DecidableEq m] (M : Matrix m m ℂ) : M / 2 = (1 / 2 : ℂ) • M := by
  have htwo : (2 : Matrix m m ℂ) = Matrix.diagonal (fun _ : m => (2 : ℂ)) := by
    ext s t
    change (↑(2 : ℕ) : Matrix m m ℂ) s t = _
    rw [Matrix.natCast_apply]
    simp [Matrix.diagonal]
  rw [div_eq_mul_inv, htwo, Matrix.inv_diagonal]
  ext s t
  simp [Matrix.mul_apply, Matrix.smul_apply, Matrix.diagonal, apply_ite]
  let u : (m → ℂ)ˣ := Units.mk (fun _ : m => (2 : ℂ)) (fun _ : m => (1 / 2 : ℂ))
    (by ext; norm_num) (by ext; norm_num)
  have hinv : Ring.inverse (fun _ : m => (2 : ℂ)) = (fun _ : m => (1 / 2 : ℂ)) := by
    have hu := Ring.inverse_unit u
    rw [hu]
    ext q
    change ((u⁻¹ : (m → ℂ)ˣ) : m → ℂ) q = _
    norm_num [u]
  rw [show Ring.inverse (fun _ : m => (2 : ℂ)) t = (1 / 2 : ℂ) by rw [hinv]]
  ring

private lemma test_anti {n : ℕ} {i j k : (Option (Option (Fin n)))} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) : singlet i j * singlet i k + singlet i k * singlet i j = (singlet i j + singlet i k - singlet j k) / 2 := by
  have hdiv := matrix_div_two (singlet i j + singlet i k - singlet j k)
  rw [hdiv]
  unfold singlet
  have hPauli0 := pauli_sq_X
  have hPauli1 := pauli_sq_Y
  have hPauli2 := pauli_sq_Z
  have hPauli3 := pauli_mul_XY
  have hPauli4 := pauli_mul_YX_smul
  have hPauli5 := pauli_mul_YZ
  have hPauli6 := pauli_mul_ZY_smul
  have hPauli7 := pauli_mul_ZX
  have hPauli8 := pauli_mul_XZ_smul
  generalize (Complex.I • (qubitX * qubitZ)) = Y at hPauli0 hPauli1 hPauli2 hPauli3 hPauli4 hPauli5 hPauli6 hPauli7 hPauli8 ⊢
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  simp only [sub_mul, mul_sub, add_mul, mul_add]
  simp only [one_mul, mul_one]
  rw [
    site_pair_shared hij hik qubitX qubitX qubitX qubitX, site_pair_shared hij hik Y Y Y Y,
    site_pair_shared hij hik qubitZ qubitZ qubitZ qubitZ,
    site_pair_shared hij hik qubitX qubitX Y Y, site_pair_shared hij hik qubitX qubitX qubitZ qubitZ,
    site_pair_shared hij hik Y Y qubitX qubitX, site_pair_shared hij hik Y Y qubitZ qubitZ,
    site_pair_shared hij hik qubitZ qubitZ qubitX qubitX, site_pair_shared hij hik qubitZ qubitZ Y Y,
    site_pair_shared_rev (i := i) (j := j) (k := k) hij hik hjk qubitX qubitX qubitX qubitX, site_pair_shared_rev (i := i) (j := j) (k := k) hij hik hjk Y Y Y Y,
    site_pair_shared_rev (i := i) (j := j) (k := k) hij hik hjk qubitZ qubitZ qubitZ qubitZ,
    site_pair_shared_rev (i := i) (j := j) (k := k) hij hik hjk qubitX qubitX Y Y, site_pair_shared_rev (i := i) (j := j) (k := k) hij hik hjk qubitX qubitX qubitZ qubitZ,
    site_pair_shared_rev (i := i) (j := j) (k := k) hij hik hjk Y Y qubitX qubitX, site_pair_shared_rev (i := i) (j := j) (k := k) hij hik hjk Y Y qubitZ qubitZ,
    site_pair_shared_rev (i := i) (j := j) (k := k) hij hik hjk qubitZ qubitZ qubitX qubitX, site_pair_shared_rev (i := i) (j := j) (k := k) hij hik hjk qubitZ qubitZ Y Y]
  rw [hPauli0, hPauli4, hPauli7,
    hPauli3, hPauli1, hPauli6,
    hPauli8, hPauli5, hPauli2]
  simp_rw [site_smul]
  simp [Matrix.smul_mul, Matrix.mul_smul, smul_smul, site_one]
  module

private lemma hub_annihilation_Y {n : ℕ} {i j : (Option (Option (Fin n)))} (hij : i ≠ j) : singlet i j * (site i (Complex.I • (qubitX * qubitZ)) + site j (Complex.I • (qubitX * qubitZ))) = 0 := by
  unfold singlet
  have hPauli0 := pauli_sq_Y
  have hPauli1 := pauli_mul_XY
  have hPauli2 := pauli_mul_ZY_smul
  generalize (Complex.I • (qubitX * qubitZ)) = Y at hPauli0 hPauli1 hPauli2 ⊢
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  simp only [sub_mul, mul_sub, add_mul, mul_add, one_mul, mul_one]
  rw [site_pair_mul_left hij qubitX qubitX Y, site_pair_mul_left hij Y Y Y,
    site_pair_mul_left hij qubitZ qubitZ Y, site_pair_mul_right hij qubitX qubitX Y,
    site_pair_mul_right hij Y Y Y, site_pair_mul_right hij qubitZ qubitZ Y]
  rw [hPauli1, hPauli0, hPauli2]
  simp_rw [site_smul]
  simp [Matrix.smul_mul, Matrix.mul_smul, smul_smul, site_one]
  module

private lemma hub_annihilation_Z {n : ℕ} {i j : (Option (Option (Fin n)))} (hij : i ≠ j) : singlet i j * (site i qubitZ + site j qubitZ) = 0 := by
  unfold singlet
  have hPauli0 := pauli_sq_Z
  have hPauli1 := pauli_mul_YZ
  have hPauli2 := pauli_mul_XZ_smul
  generalize (Complex.I • (qubitX * qubitZ)) = Y at hPauli0 hPauli1 hPauli2 ⊢
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  simp only [sub_mul, mul_sub, add_mul, mul_add, one_mul, mul_one]
  rw [site_pair_mul_left hij qubitX qubitX qubitZ, site_pair_mul_left hij Y Y qubitZ,
    site_pair_mul_left hij qubitZ qubitZ qubitZ, site_pair_mul_right hij qubitX qubitX qubitZ,
    site_pair_mul_right hij Y Y qubitZ, site_pair_mul_right hij qubitZ qubitZ qubitZ]
  rw [hPauli2, hPauli1, hPauli0]
  simp_rw [site_smul]
  simp [Matrix.smul_mul, Matrix.mul_smul, smul_smul, site_one]
  module

private lemma hub_annihilation {n : ℕ} {i j : (Option (Option (Fin n)))} (hij : i ≠ j) (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A = qubitX ∨ A = (Complex.I • (qubitX * qubitZ)) ∨ A = qubitZ) : singlet i j * (site i A + site j A) = 0 := by
  rcases hA with rfl | rfl | rfl
  · exact test_hub hij
  · exact hub_annihilation_Y hij
  · exact hub_annihilation_Z hij

private lemma singlet_mul_pair_sum {n : ℕ} {i j k : (Option (Option (Fin n)))} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) : singlet i j * (singlet i k + singlet j k) = (1 / 2 : ℂ) • singlet i j := by
  have hX : singlet i j * (site i qubitX * site k qubitX + site j qubitX * site k qubitX) = 0 := by
    rw [← add_mul]
    rw [← mul_assoc, hub_annihilation hij qubitX (Or.inl rfl)]
    simp
  have hY : singlet i j * (site i (Complex.I • (qubitX * qubitZ)) * site k (Complex.I • (qubitX * qubitZ)) + site j (Complex.I • (qubitX * qubitZ)) * site k (Complex.I • (qubitX * qubitZ))) = 0 := by
    rw [← add_mul]
    rw [← mul_assoc, hub_annihilation hij (Complex.I • (qubitX * qubitZ)) (Or.inr (Or.inl rfl))]
    simp
  have hZ : singlet i j * (site i qubitZ * site k qubitZ + site j qubitZ * site k qubitZ) = 0 := by
    rw [← add_mul]
    rw [← mul_assoc, hub_annihilation hij qubitZ (Or.inr (Or.inr rfl))]
    simp
  have hexpand : singlet i k + singlet j k =
      (1 / 2 : ℂ) • (1 : (Matrix (Option (Option (Fin n)) → Fin 2) (Option (Option (Fin n)) → Fin 2) ℂ)) - (1 / 4 : ℂ) •
        ((site i qubitX * site k qubitX + site j qubitX * site k qubitX) +
          (site i (Complex.I • (qubitX * qubitZ)) * site k (Complex.I • (qubitX * qubitZ)) + site j (Complex.I • (qubitX * qubitZ)) * site k (Complex.I • (qubitX * qubitZ))) +
          (site i qubitZ * site k qubitZ + site j qubitZ * site k qubitZ)) := by
    unfold singlet
    module
  rw [hexpand]
  have hsum : singlet i j *
      ((site i qubitX * site k qubitX + site j qubitX * site k qubitX) +
        (site i (Complex.I • (qubitX * qubitZ)) * site k (Complex.I • (qubitX * qubitZ)) + site j (Complex.I • (qubitX * qubitZ)) * site k (Complex.I • (qubitX * qubitZ))) +
        (site i qubitZ * site k qubitZ + site j qubitZ * site k qubitZ)) = 0 := by
    rw [mul_add, mul_add, hX, hY, hZ]
    simp
  simp only [mul_sub, Matrix.mul_smul, Matrix.mul_one]
  rw [hsum]
  module

@[simp] theorem a_ne_leaf {n : ℕ} (i : Fin n) : a n ≠ leaf i := by simp [a,leaf]
@[simp] theorem b_ne_leaf {n : ℕ} (i : Fin n) : b n ≠ leaf i := by simp [b,leaf]

def crownH (n : ℕ) (x : ℝ) : (Matrix (Option (Option (Fin n)) → Fin 2) (Option (Option (Fin n)) → Fin 2) ℂ) :=
  (x : ℂ) • singlet (a n) (b n) + ∑ i : Fin n, (singlet (a n) (leaf i) + singlet (b n) (leaf i))

def lambdaMax {ι : Type*} [Fintype ι] (H : Matrix ι ι ℂ) : ℝ :=
  sSup {r : ℝ | ∃ v : EuclideanSpace ℂ ι, v ≠ 0 ∧
    r = (∑ i, star (v i) * (H.mulVec v) i).re / ‖v‖^2}

private lemma matrix_le_scalar_of_sq_le {m : Type*} [Fintype m] [DecidableEq m] (A : Matrix m m ℂ) (hA : A.PosSemidef) (c : ℝ) (hc : 0 ≤ c) (hsq : A * A ≤ (c : ℂ) • A) : A ≤ (c : ℂ) • (1 : Matrix m m ℂ) := by
  have hnormA : 0 ≤ ‖A‖ := norm_nonneg _
  have hmulnon : 0 ≤ A * A :=
    Matrix.nonneg_iff_posSemidef.mpr (by simpa [pow_two] using hA.pow 2)
  have hnormsq : ‖A‖ ^ 2 = ‖A * A‖ := by
    exact hA.1.isSelfAdjoint.norm_mul_self.symm
  have hnormord : ‖A * A‖ ≤ ‖(c : ℂ) • A‖ :=
    CStarAlgebra.norm_le_norm_of_le_of_nonneg hsq hmulnon
  have hcabs : ‖(c : ℂ)‖ = c := by
    exact (RCLike.norm_ofReal c).trans (abs_of_nonneg hc)
  have hnormsc : ‖(c : ℂ) • A‖ = c * ‖A‖ := by
    rw [norm_smul, hcabs]
  have hnorm_le : ‖A‖ ≤ c := by
    by_cases hz : ‖A‖ = 0
    · linarith
    nlinarith [hnormord, hnormsq, hnormsc]
  have horder : A ≤ algebraMap ℝ (Matrix m m ℂ) c :=
    (CStarAlgebra.norm_le_iff_le_algebraMap A hc hA.nonneg).mp hnorm_le
  simpa [Algebra.algebraMap_eq_smul_one] using horder

private lemma projection_certificate {m : Type*} [Fintype m] [DecidableEq m] (P K : Matrix m m ℂ) (c r x : ℝ) (hP : P * P = P) (hKP : K * P = (r : ℂ) • P) (hPK : P * K = (r : ℂ) • P) : (c : ℂ) • (1 : Matrix m m ℂ) - (x : ℂ) • P - K = (1 - P) * ((c : ℂ) • (1 : Matrix m m ℂ) - K) * (1 - P) + (c - r - x : ℂ) • P := by
  have hq : (1 - P) * (1 - P) = (1 - P) := by
    simp only [sub_mul, mul_sub, Matrix.one_mul, Matrix.mul_one]
    rw [hP]
    module
  have hK : (1 - P) * K * (1 - P) = K - (r : ℂ) • P := by
    simp only [sub_mul, mul_sub, Matrix.one_mul, Matrix.mul_one]
    rw [hKP, hPK]
    rw [Matrix.smul_mul, hP]
    module
  have hC : (1 - P) * ((c : ℂ) • (1 : Matrix m m ℂ)) * (1 - P) =
      (c : ℂ) • (1 - P) := by
    calc
      (1 - P) * ((c : ℂ) • (1 : Matrix m m ℂ)) * (1 - P) =
          (1 - P) * (((c : ℂ) • (1 : Matrix m m ℂ)) * (1 - P)) := by rw [mul_assoc]
      _ = (1 - P) * ((c : ℂ) • ((1 : Matrix m m ℂ) * (1 - P))) := by
        rw [Matrix.smul_mul]
      _ = (c : ℂ) • ((1 - P) * (1 - P)) := by rw [Matrix.one_mul, Matrix.mul_smul]
      _ = (c : ℂ) • (1 - P) := by rw [hq]
  have hExpand :
      (1 - P) * ((c : ℂ) • (1 : Matrix m m ℂ) - K) * (1 - P) =
        (1 - P) * ((c : ℂ) • (1 : Matrix m m ℂ)) * (1 - P) -
          (1 - P) * K * (1 - P) := by
    calc
      (1 - P) * ((c : ℂ) • (1 : Matrix m m ℂ) - K) * (1 - P) =
          ((1 - P) * ((c : ℂ) • (1 : Matrix m m ℂ)) - (1 - P) * K) * (1 - P) := by
            exact congrArg (fun T : Matrix m m ℂ => T * (1 - P))
              (mul_sub (1 - P) ((c : ℂ) • (1 : Matrix m m ℂ)) K)
      _ = (1 - P) * ((c : ℂ) • (1 : Matrix m m ℂ)) * (1 - P) -
          (1 - P) * K * (1 - P) := by
            exact sub_mul ((1 - P) * ((c : ℂ) • (1 : Matrix m m ℂ)))
              ((1 - P) * K) (1 - P)
  rw [hExpand]
  rw [hC, hK]
  module

private lemma projection_certificate_posSemidef {m : Type*} [Fintype m] [DecidableEq m] (P Q : Matrix m m ℂ) (hP : P.PosSemidef) (hQ : Q.PosSemidef) (hP2 : P * P = P) (a : ℝ) (ha : 0 ≤ a) : ((1 - P) * Q * (1 - P) + (a : ℂ) • P).PosSemidef := by
  have hfirst0 := Matrix.PosSemidef.conjTranspose_mul_mul_same hQ (1 - P)
  have hfirst : ((1 - P) * Q * (1 - P)).PosSemidef := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hP.1] at hfirst0
    simpa [Matrix.star_eq_conjTranspose, sub_eq_add_neg] using hfirst0
  have hsecond : ((a : ℂ) • P).PosSemidef := hP.smul (by exact_mod_cast ha)
  exact hfirst.add hsecond

private def starOp (n : ℕ) (i : (Option (Option (Fin n)))) : (Matrix (Option (Option (Fin n)) → Fin 2) (Option (Option (Fin n)) → Fin 2) ℂ) := ∑ j : Fin n, singlet i (leaf j)
private def leafEdgeSum (n : ℕ) : (Matrix (Option (Option (Fin n)) → Fin 2) (Option (Option (Fin n)) → Fin 2) ℂ) :=
  ∑ i : Fin n, ∑ j : Fin n, if i = j then 0 else singlet (leaf i) (leaf j)
private lemma leaf_ne_leaf {n : ℕ} {i j : Fin n} (hij : i ≠ j) : leaf i ≠ leaf j := by
  intro h
  injection h with h'
  exact hij (Option.some.inj h')
private lemma star_square {n : ℕ} {hub : (Option (Option (Fin n)))} (hhub : ∀ i : Fin n, hub ≠ leaf i) : starOp n hub * starOp n hub = (((n + 1 : ℕ) : ℂ) / 2) • starOp n hub - (1 / 4 : ℂ) • leafEdgeSum n := by
  unfold starOp leafEdgeSum
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  let f : Fin n → (Matrix (Option (Option (Fin n)) → Fin 2) (Option (Option (Fin n)) → Fin 2) ℂ) := fun i => singlet hub (leaf i)
  let S : (Matrix (Option (Option (Fin n)) → Fin 2) (Option (Option (Fin n)) → Fin 2) ℂ) := ∑ i : Fin n, ∑ j : Fin n, if i = j then 0 else f i * f j
  let T : (Matrix (Option (Option (Fin n)) → Fin 2) (Option (Option (Fin n)) → Fin 2) ℂ) := ∑ i : Fin n, ∑ j : Fin n, if i = j then 0 else singlet (leaf i) (leaf j)
  have hdiag : (∑ i : Fin n, f i * f i) = ∑ i : Fin n, f i := by
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [f]
    rw [singlet_idempotent (hhub i)]
  have hoff (i : Fin n) :
      (∑ j : Fin n, if i = j then 0 else f i) = (n - 1 : ℕ) • f i := by
    simp [Finset.sum_ite]
    have hcard : (Finset.univ.filter (fun x : Fin n => ¬ i = x)).card = n - 1 := by
      rw [show Finset.univ.filter (fun x : Fin n => ¬ i = x) = Finset.univ.erase i by
        ext x; simp [eq_comm]]
      simp
    simpa [hcard]
  have hsplit :
      (∑ i : Fin n, ∑ j : Fin n, f i * f j) =
        (∑ i : Fin n, f i * f i) + S := by
    dsimp [S]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    have hsingle : f i * f i = ∑ j : Fin n, if i = j then f i * f j else 0 := by simp
    rw [hsingle, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hij : i = j <;> simp [hij]
  have hswap : S = ∑ i : Fin n, ∑ j : Fin n, if i = j then 0 else f j * f i := by
    dsimp [S]
    simpa [eq_comm] using
      (Finset.sum_comm (s := (Finset.univ : Finset (Fin n)))
        (t := (Finset.univ : Finset (Fin n)))
        (f := fun i j => if i = j then 0 else f i * f j))
  have hoff2 :
      (∑ i : Fin n, ∑ j : Fin n, if i = j then 0 else f j) =
        (n - 1 : ℕ) • (∑ i : Fin n, f i) := by
    calc
      (∑ i : Fin n, ∑ j : Fin n, if i = j then 0 else f j) =
          ∑ j : Fin n, ∑ i : Fin n, if i = j then 0 else f j := by
            rw [Finset.sum_comm]
      _ = ∑ j : Fin n, (n - 1 : ℕ) • f j := by
            apply Finset.sum_congr rfl
            intro j hj
            simpa [eq_comm] using hoff j
      _ = (n - 1 : ℕ) • (∑ j : Fin n, f j) := by
            rw [Finset.smul_sum]
  have hoffpair :
      (∑ i : Fin n, ∑ j : Fin n, if i = j then 0 else (f i + f j)) =
        (2 * (n - 1) : ℕ) • (∑ i : Fin n, f i) := by
    have hsplitpair :
        (∑ i : Fin n, ∑ j : Fin n, if i = j then 0 else (f i + f j)) =
          (∑ i : Fin n, ∑ j : Fin n, if i = j then 0 else f i) +
            (∑ i : Fin n, ∑ j : Fin n, if i = j then 0 else f j) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      by_cases hij : i = j <;> simp [hij]
    have hoffsum :
        (∑ i : Fin n, ∑ j : Fin n, if i = j then 0 else f i) =
          (n - 1 : ℕ) • (∑ i : Fin n, f i) := by
      calc
        (∑ i : Fin n, ∑ j : Fin n, if i = j then 0 else f i) =
            ∑ i : Fin n, (n - 1 : ℕ) • f i := by
              apply Finset.sum_congr rfl
              intro i hi
              exact hoff i
        _ = (n - 1 : ℕ) • (∑ i : Fin n, f i) := by rw [Finset.smul_sum]
    rw [hsplitpair, hoffsum, hoff2]
    module
  have hanti :
      (∑ i : Fin n, ∑ j : Fin n, if i = j then 0 else f i * f j + f j * f i) =
      ∑ i : Fin n, ∑ j : Fin n, if i = j then 0 else
        (1 / 2 : ℂ) • (f i + f j - singlet (leaf i) (leaf j)) := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hij : i = j
    · simp [hij]
    · simp only [hij, ↓reduceIte]
      dsimp [f]
      have hh := test_anti (hhub i) (hhub j) (leaf_ne_leaf hij)
      rw [matrix_div_two] at hh
      exact hh
  have hcomb :
      (∑ i : Fin n, ∑ j : Fin n, if i = j then 0 else
        (f i * f j + f j * f i)) = S + (∑ i : Fin n, ∑ j : Fin n,
          if i = j then 0 else f j * f i) := by
    dsimp [S]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hij : i = j <;> simp [hij]
  have hS : S =
      (1 / 2 : ℂ) • (∑ i : Fin n, ∑ j : Fin n,
        if i = j then 0 else (f i * f j + f j * f i)) := by
    rw [hcomb, hswap]
    module
  have hS2 : S = (1 / 4 : ℂ) •
      ((∑ i : Fin n, ∑ j : Fin n, if i = j then 0 else (f i + f j)) - T) := by
    rw [hS, hanti]
    have hdiff :
        (∑ i : Fin n, ∑ j : Fin n, if i = j then 0 else
          (f i + f j - singlet (leaf i) (leaf j))) =
          (∑ i : Fin n, ∑ j : Fin n, if i = j then 0 else (f i + f j)) - T := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      by_cases hij : i = j <;> simp [hij, T]
    have hscale :
        (∑ i : Fin n, ∑ j : Fin n, if i = j then 0 else
          (1 / 2 : ℂ) • (f i + f j - singlet (leaf i) (leaf j))) =
          (1 / 2 : ℂ) •
            (∑ i : Fin n, ∑ j : Fin n, if i = j then 0 else
              (f i + f j - singlet (leaf i) (leaf j))) := by
      calc
        _ = ∑ i : Fin n, (1 / 2 : ℂ) •
            (∑ j : Fin n, if i = j then 0 else
              (f i + f j - singlet (leaf i) (leaf j))) := by
              apply Finset.sum_congr rfl
              intro i hi
              calc
                (∑ j : Fin n, if i = j then 0 else
                    (1 / 2 : ℂ) • (f i + f j - singlet (leaf i) (leaf j))) =
                    ∑ j : Fin n, (1 / 2 : ℂ) •
                      (if i = j then 0 else f i + f j - singlet (leaf i) (leaf j)) := by
                        apply Finset.sum_congr rfl
                        intro j hj
                        by_cases hij : i = j <;> simp [hij]
                _ = (1 / 2 : ℂ) •
                    (∑ j : Fin n, if i = j then 0 else
                      (f i + f j - singlet (leaf i) (leaf j))) := by
                        rw [Finset.smul_sum]
        _ = (1 / 2 : ℂ) • _ := by rw [Finset.smul_sum]
    rw [hscale, hdiff]
    module
  change (∑ i : Fin n, ∑ j : Fin n, f i * f j) =
      (((n + 1 : ℕ) : ℂ) / 2) • (∑ i : Fin n, f i) - (1 / 4 : ℂ) • T
  rw [hsplit, hdiag, hS2, hoffpair]
  by_cases hn : n = 0
  · subst n
    simp [starOp, leafEdgeSum]
  · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    simp only [← Nat.cast_smul_eq_nsmul ℂ]
    norm_num [Nat.cast_sub hn1]
    have hcoeff : (1 : ℂ) + (1 / 4 : ℂ) * (2 * ((n : ℂ) - 1)) =
        1 / 2 + (n : ℂ) * (1 / 2) := by ring
    simp only [smul_sub, smul_add, smul_smul]
    have hleft : (∑ i : Fin n, f i) +
        (1 / 4 * (2 * ((n : ℂ) - 1))) • (∑ i : Fin n, f i) =
        (1 + 1 / 4 * (2 * ((n : ℂ) - 1))) • (∑ i : Fin n, f i) := by
      simpa only [one_smul] using
        (add_smul (1 : ℂ) (1 / 4 * (2 * ((n : ℂ) - 1))) (∑ i : Fin n, f i)).symm
    rw [← add_sub_assoc, hleft, hcoeff]
    module
private lemma singlet_swap {n : ℕ} (i j : (Option (Option (Fin n)))) : singlet i j = singlet j i := by
  by_cases hij : i = j
  · rw [hij]
  · unfold singlet
    rw [site_mul_ne hij qubitX qubitX, site_mul_ne hij (Complex.I • (qubitX * qubitZ)) (Complex.I • (qubitX * qubitZ)), site_mul_ne hij qubitZ qubitZ]
private def unorderedLeafEdgeSum (n : ℕ) : (Matrix (Option (Option (Fin n)) → Fin 2) (Option (Option (Fin n)) → Fin 2) ℂ) :=
  ∑ i : Fin n, ∑ j : Fin n, if i < j then singlet (leaf i) (leaf j) else 0
private lemma leafEdgeSum_twice (n : ℕ) : leafEdgeSum n = (2 : ℂ) • unorderedLeafEdgeSum n := by
  have hterm (i j : Fin n) :
      (if i = j then (0 : (Matrix (Option (Option (Fin n)) → Fin 2) (Option (Option (Fin n)) → Fin 2) ℂ)) else singlet (leaf i) (leaf j)) =
        (if i < j then singlet (leaf i) (leaf j) else 0) +
          (if j < i then singlet (leaf i) (leaf j) else 0) := by
    rcases lt_trichotomy i j with h | h | h
    · simp [h, ne_of_lt h, not_lt_of_gt h]
    · simp [h]
    · simp [h, (ne_of_lt h).symm, not_lt_of_gt h]
  have hswap : (∑ i : Fin n, ∑ j : Fin n,
      if j < i then singlet (leaf i) (leaf j) else 0) = unorderedLeafEdgeSum n := by
    rw [Finset.sum_comm]
    unfold unorderedLeafEdgeSum
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [singlet_swap (leaf j) (leaf i)]
  unfold leafEdgeSum
  simp_rw [hterm]
  simp only [Finset.sum_add_distrib]
  rw [hswap]
  change unorderedLeafEdgeSum n + unorderedLeafEdgeSum n = _
  module
private lemma star_square_unordered {n : ℕ} {hub : (Option (Option (Fin n)))} (hhub : ∀ i : Fin n, hub ≠ leaf i) : starOp n hub * starOp n hub = (((n + 1 : ℕ) : ℂ) / 2) • starOp n hub - (1 / 2 : ℂ) • unorderedLeafEdgeSum n := by
  rw [star_square hhub, leafEdgeSum_twice]
  module
private lemma leafEdge_pos {n : ℕ} : (leafEdgeSum n).PosSemidef := by
  unfold leafEdgeSum
  apply Matrix.posSemidef_sum (s := (Finset.univ : Finset (Fin n)))
  intro i hi
  apply Matrix.posSemidef_sum (s := (Finset.univ : Finset (Fin n)))
  intro j hj
  by_cases hij : i = j
  · simpa [hij] using (Matrix.PosSemidef.zero : (0 : Matrix ((Option (Option (Fin n)) → Fin 2)) ((Option (Option (Fin n)) → Fin 2)) ℂ).PosSemidef)
  · simp only [hij, ↓reduceIte]
    exact singlet_posSemidef (leaf_ne_leaf hij)
private lemma star_pos {n : ℕ} {hub : (Option (Option (Fin n)))} (hhub : ∀ i : Fin n, hub ≠ leaf i) : (starOp n hub).PosSemidef := by
  unfold starOp
  apply Matrix.posSemidef_sum (s := (Finset.univ : Finset (Fin n)))
  intro i hi
  exact singlet_posSemidef (hhub i)
private lemma star_sq_le {n : ℕ} {hub : (Option (Option (Fin n)))} (hhub : ∀ i : Fin n, hub ≠ leaf i) : starOp n hub * starOp n hub ≤ (((n + 1 : ℕ) : ℂ) / 2) • starOp n hub := by
  rw [star_square_unordered hhub]
  have hscale : (1 / 2 : ℂ) • unorderedLeafEdgeSum n =
      (1 / 4 : ℂ) • leafEdgeSum n := by
    rw [leafEdgeSum_twice]
    module
  rw [hscale]
  have hE : (0 : Matrix ((Option (Option (Fin n)) → Fin 2)) ((Option (Option (Fin n)) → Fin 2)) ℂ) ≤ leafEdgeSum n :=
    Matrix.nonneg_iff_posSemidef.mpr leafEdge_pos
  have hE4 : (0 : Matrix ((Option (Option (Fin n)) → Fin 2)) ((Option (Option (Fin n)) → Fin 2)) ℂ) ≤ (1 / 4 : ℂ) • leafEdgeSum n := by
    apply Matrix.nonneg_iff_posSemidef.mpr
    exact leafEdge_pos.smul (by positivity)
  exact sub_le_self _ hE4
private lemma star_bound {n : ℕ} {hub : (Option (Option (Fin n)))} (hhub : ∀ i : Fin n, hub ≠ leaf i) : starOp n hub ≤ (((n + 1 : ℝ) / 2 : ℝ) : ℂ) • (1 : Matrix ((Option (Option (Fin n)) → Fin 2)) ((Option (Option (Fin n)) → Fin 2)) ℂ) := by
  apply matrix_le_scalar_of_sq_le (starOp n hub) (star_pos hhub) ((n + 1 : ℝ) / 2)
  · positivity
  · simpa using star_sq_le hhub
private def crownK (n : ℕ) : (Matrix (Option (Option (Fin n)) → Fin 2) (Option (Option (Fin n)) → Fin 2) ℂ) := starOp n (a n) + starOp n (b n)
private lemma crownP_mul_K (n : ℕ) : (singlet (a n) (b n)) * crownK n = ((n : ℂ) / 2) • (singlet (a n) (b n)) := by
  unfold crownK starOp
  rw [mul_add, Finset.mul_sum, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  calc
    (∑ x : Fin n, (singlet (a n) (b n) * singlet (a n) (leaf x) +
        singlet (a n) (b n) * singlet (b n) (leaf x))) =
      ∑ x : Fin n, (1 / 2 : ℂ) • singlet (a n) (b n) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [← mul_add]
        exact singlet_mul_pair_sum (by simp [a, b]) (a_ne_leaf i) (b_ne_leaf i)
    _ = ((n : ℂ) / 2) • singlet (a n) (b n) := by
      rw [Finset.sum_const]
      simp only [Finset.card_univ, Fintype.card_fin]
      module
private lemma crownK_mul_P (n : ℕ) : crownK n * (singlet (a n) (b n)) = ((n : ℂ) / 2) • (singlet (a n) (b n)) := by
  have h := congrArg Matrix.conjTranspose (crownP_mul_K n)
  have hp : ((singlet (a n) (b n))).IsHermitian := singlet_isHermitian (by simp [a, b])
  have hk : (crownK n).IsHermitian :=
    (star_pos (n := n) a_ne_leaf).1.add (star_pos (n := n) b_ne_leaf).1
  simpa [Matrix.conjTranspose_mul, Matrix.conjTranspose_smul, hp.eq, hk.eq,
    starRingEnd_apply] using h
private lemma crownK_bound (n : ℕ) : crownK n ≤ ((n + 1 : ℝ) : ℂ) • (1 : (Matrix (Option (Option (Fin n)) → Fin 2) (Option (Option (Fin n)) → Fin 2) ℂ)) := by
  have h := add_le_add (star_bound (n := n) a_ne_leaf) (star_bound (n := n) b_ne_leaf)
  have hs : (((n + 1 : ℝ) / 2 : ℝ) : ℂ) • (1 : (Matrix (Option (Option (Fin n)) → Fin 2) (Option (Option (Fin n)) → Fin 2) ℂ)) +
      (((n + 1 : ℝ) / 2 : ℝ) : ℂ) • (1 : (Matrix (Option (Option (Fin n)) → Fin 2) (Option (Option (Fin n)) → Fin 2) ℂ)) =
        ((n + 1 : ℝ) : ℂ) • (1 : (Matrix (Option (Option (Fin n)) → Fin 2) (Option (Option (Fin n)) → Fin 2) ℂ)) := by module
  simpa only [crownK, hs] using h
private lemma crown_certificate (n : ℕ) (x : ℝ) : ((n + 1 : ℝ) : ℂ) • (1 : (Matrix (Option (Option (Fin n)) → Fin 2) (Option (Option (Fin n)) → Fin 2) ℂ)) - crownH n x = (1 - (singlet (a n) (b n))) * (((n + 1 : ℝ) : ℂ) • (1 : (Matrix (Option (Option (Fin n)) → Fin 2) (Option (Option (Fin n)) → Fin 2) ℂ)) - crownK n) * (1 - (singlet (a n) (b n))) + ((1 + (n : ℝ) / 2 - x : ℝ) : ℂ) • (singlet (a n) (b n)) := by
  have hp : (singlet (a n) (b n)) * (singlet (a n) (b n)) = (singlet (a n) (b n)) := singlet_idempotent (by simp [a, b])
  have hkp : crownK n * (singlet (a n) (b n)) = (((n : ℝ) / 2 : ℝ) : ℂ) • (singlet (a n) (b n)) := by
    simpa using crownK_mul_P n
  have hpk : (singlet (a n) (b n)) * crownK n = (((n : ℝ) / 2 : ℝ) : ℂ) • (singlet (a n) (b n)) := by
    simpa using crownP_mul_K n
  have hh : crownH n x = (x : ℂ) • (singlet (a n) (b n)) + crownK n := by
    simp only [crownH, crownK, starOp, Finset.sum_add_distrib]
  rw [hh, ← sub_sub]
  have hc := projection_certificate ((singlet (a n) (b n))) (crownK n) (n + 1) ((n : ℝ) / 2) x hp hkp hpk
  convert hc using 1 <;> push_cast <;> congr 2 <;> ring
private lemma crownH_bound_psd (n : ℕ) (x : ℝ) (hx : x ≤ 1 + (n : ℝ) / 2) : (((n + 1 : ℝ) : ℂ) • (1 : (Matrix (Option (Option (Fin n)) → Fin 2) (Option (Option (Fin n)) → Fin 2) ℂ)) - crownH n x).PosSemidef := by
  rw [crown_certificate]
  have hP : ((singlet (a n) (b n))).PosSemidef := singlet_posSemidef (by simp [a, b])
  have hQ : (((n + 1 : ℝ) : ℂ) • (1 : (Matrix (Option (Option (Fin n)) → Fin 2) (Option (Option (Fin n)) → Fin 2) ℂ)) - crownK n).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr (crownK_bound n))
  apply projection_certificate_posSemidef ((singlet (a n) (b n))) _ hP hQ
  · exact singlet_idempotent (by simp [a, b])
  · linarith
private lemma rayleigh_le_of_posSemidef {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (H : Matrix ι ι ℂ) (c : ℝ) (hc : 0 ≤ c) (hD : ((c : ℂ) • (1 : Matrix ι ι ℂ) - H).PosSemidef) : lambdaMax H ≤ c := by
  apply Real.sSup_le
  · intro r hr
    obtain ⟨v, hv, rfl⟩ := hr
    have hq := hD.re_dotProduct_nonneg (v : ι → ℂ)
    have hnorm : 0 < ‖v‖ ^ 2 := by positivity
    have hbound :
        (∑ i, star (v i) * (H.mulVec (v : ι → ℂ)) i).re ≤ c * ‖v‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      have hq := hD.re_dotProduct_nonneg (v : ι → ℂ)
      simp [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
        dotProduct_sub, dotProduct_smul, smul_eq_mul, dotProduct, Complex.sq_norm, Complex.normSq_apply] at hq ⊢
      have hid :
          (∑ x, ((v.ofLp x).re * (c * (v.ofLp x).re - ((H *ᵥ v.ofLp) x).re) +
            (v.ofLp x).im * (c * (v.ofLp x).im - ((H *ᵥ v.ofLp) x).im))) =
            c * (∑ x, ((v.ofLp x).re ^ 2 + (v.ofLp x).im ^ 2)) -
              ∑ x, ((v.ofLp x).re * ((H *ᵥ v.ofLp) x).re +
                (v.ofLp x).im * ((H *ᵥ v.ofLp) x).im) := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro x hx
        ring
      rw [hid] at hq
      simp only [pow_two] at hq ⊢
      linarith
    apply (div_le_iff₀ hnorm).mpr
    nlinarith
  · exact hc
theorem crown_spectral_bound (n : ℕ) (x : ℝ) (hx : x ≤ 1 + (n : ℝ) / 2) :
    lambdaMax (crownH n x) ≤ (n : ℝ) + 1 := by
  apply rayleigh_le_of_posSemidef (crownH n x) ((n : ℝ) + 1)
  · positivity
  · exact crownH_bound_psd n x hx
end D5.S3.Quantum.Optimization.WeightedCrownSpectralBound
