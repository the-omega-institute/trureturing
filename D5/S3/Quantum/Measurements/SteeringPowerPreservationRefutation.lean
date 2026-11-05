/- GID: D5/S3/Quantum/Measurements/SteeringPowerPreservationRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurements/SteeringPowerPreservationRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Measurements/SteeringPowerPreservationRefutation.claim; result=D5/S3/Quantum/Measurements/SteeringPowerPreservationRefutation.result; claim=D5/S3/Quantum/Measurements/SteeringPowerPreservationRefutation.claim
   digest: An admissible five-dimensional projective family fails steering power preservation. -/

import D5.S3.Quantum.Information.StabilizerAutocorrelationNormRefutation

/-! A five-dimensional counterexample to steering power preservation. -/

namespace D5.S3.Quantum.Measurements.SteeringPowerPreservationRefutation

open scoped BigOperators
open D5.S3.Observer.WindowRegister
open D5.S3.Quantum.Information.StabilizerAutocorrelationNormRefutation (shift clock)

noncomputable section

/-- The phase coefficients of the steering substitution. -/
def coeff (d : ℕ) (φ : Fin d → Fin d → ℝ) (n : ℕ) (y k : Fin d) : ℂ :=
  (1 / (d : ℂ)) * windowRoot d ^ (k.val * n * (n - 1) / 2) *
    ∑ l : Fin d,
      Complex.exp (-Complex.I * ((∑ m ∈ Finset.range n,
        φ ⟨(l.val + m + 1) % d, Nat.mod_lt _ (Nat.zero_lt_of_lt l.isLt)⟩ y : ℝ) : ℂ)) *
        windowRoot d ^ (k.val * n * l.val)

/-- Zero total phase and orthonormal coefficient rows at every nontrivial power. -/
def Admissible (d : ℕ) (φ : Fin d → Fin d → ℝ) : Prop :=
  (∀ y, ∑ j, φ j y = 0) ∧
    ∀ n, 1 ≤ n → n ≤ d - 1 → ∀ y y',
      ∑ k, star (coeff d φ n y' k) * coeff d φ n y k =
        if y = y' then 1 else 0

/-- A family of unitary observables of order dividing the number of outcomes. -/
def IsProjectiveFamily (d : ℕ) (B : Fin d → Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ∀ y, B y ∈ Matrix.unitaryGroup (Fin d) ℂ ∧ B y ^ d = 1

/-- The steering substitution for projective measurements. -/
def transformed (d : ℕ) (φ : Fin d → Fin d → ℝ)
    (B : Fin d → Matrix (Fin d) (Fin d) ℂ) (n : ℕ) (k : Fin d) :
    Matrix (Fin d) (Fin d) ℂ :=
  ∑ y, coeff d φ n y k • B y ^ n

/-- Power preservation for all prime dimensions and all admissible projective families. -/
def claim : Prop :=
  ∀ d, Nat.Prime d → ∀ φ, Admissible d φ → ∀ B, IsProjectiveFamily d B →
    ∀ k n, 1 ≤ n → n ≤ d - 1 →
      transformed d φ B n k = (transformed d φ B 1 k) ^ n

private def t (j y : Fin 5) : ℤ :=
  ![-6 * (y.val : ℤ), 0, (y.val : ℤ) - 1, 1 + 2 * (y.val : ℤ), 3 * (y.val : ℤ)] j

private def phases (j y : Fin 5) : ℝ := (2 * Real.pi / 5) * (t j y : ℝ)

private def R (y : Fin 5) : Matrix (Fin 5) (Fin 5) ℂ :=
  ∑ k : Fin 5, star (coeff 5 phases 1 y k) • (shift * clock ^ k.val)

private def B (y : Fin 5) : Matrix (Fin 5) (Fin 5) ℂ :=
  if y = 0 then windowRoot 5 • R y else R y

private def g : ℂ := (3 + windowRoot 5 + windowRoot 5 ^ 4) / 5

private lemma root_relations :
    windowRoot 5 ^ 5 = 1 ∧
    1 + windowRoot 5 + windowRoot 5 ^ 2 + windowRoot 5 ^ 3 + windowRoot 5 ^ 4 = 0 ∧
    star (windowRoot 5) = windowRoot 5 ^ 4 := by
  have h := windowRoot_isPrimitiveRoot 5
  refine ⟨h.pow_eq_one, ?_, ?_⟩
  · simpa [Finset.sum_range_succ] using h.geom_sum_eq_zero (by norm_num)
  · have hi : (windowRoot 5)⁻¹ = windowRoot 5 ^ 4 := by
      apply inv_eq_of_mul_eq_one_left
      simpa only [← pow_succ] using h.pow_eq_one
    exact (RCLike.inv_eq_conj (h.norm'_eq_one (by norm_num))).symm.trans hi

private lemma phases_zero (y : Fin 5) : ∑ j, phases j y = 0 := by
  simp [phases, t, Fin.sum_univ_succ]
  ring

private lemma phase_exponential (m : ℤ) :
    Complex.exp (-Complex.I * (((2 * Real.pi / 5) * (m : ℝ) : ℝ) : ℂ)) =
      windowRoot 5 ^ ((-m) % 5).toNat := by
  let u : ℂˣ := Units.mk0 (windowRoot 5) (by
    exact Complex.exp_ne_zero _)
  have hu : u ^ 5 = 1 := Units.ext root_relations.1
  have hm := congrArg (fun v : ℂˣ => (v : ℂ)) (zpow_eq_zpow_emod' (-m) hu)
  simp only [Units.val_zpow_eq_zpow_val] at hm
  change windowRoot 5 ^ (-m) = windowRoot 5 ^ ((-m) % 5 : ℤ) at hm
  rw [show -Complex.I * (((2 * Real.pi / 5) * (m : ℝ) : ℝ) : ℂ) =
      ((-m : ℤ) : ℂ) * (2 * Real.pi * Complex.I / 5) by push_cast; ring,
    Complex.exp_int_mul]
  change windowRoot 5 ^ (-m) = _
  rw [hm, ← Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num : (5 : ℤ) ≠ 0))]
  rfl

private lemma coefficient_formula (n : ℕ) (y k : Fin 5) :
    coeff 5 phases n y k =
      (1 / (5 : ℂ)) * windowRoot 5 ^ ((k.val * n * (n - 1) / 2) % 5) *
        ∑ l : Fin 5,
          windowRoot 5 ^ ((-(∑ m ∈ Finset.range n,
            t ⟨(l.val + m + 1) % 5, by omega⟩ y)) % 5).toNat *
            windowRoot 5 ^ ((k.val * n * l.val) % 5) := by
  unfold coeff
  rw [pow_eq_pow_mod (k.val * n * (n - 1) / 2) root_relations.1]
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  have hs : (∑ m ∈ Finset.range n,
      phases ⟨(l.val + m + 1) % 5, by omega⟩ y) =
      (2 * Real.pi / 5) * ((∑ m ∈ Finset.range n,
        t ⟨(l.val + m + 1) % 5, by omega⟩ y : ℤ) : ℝ) := by
    simp [phases, Finset.mul_sum]
  rw [hs, phase_exponential, pow_eq_pow_mod (k.val * n * l.val) root_relations.1]

set_option maxHeartbeats 5000000 in
-- The four powers require one hundred finite coefficient identities.
private lemma coefficient_orthogonality (n : ℕ) (hn : 1 ≤ n) (hn' : n ≤ 4)
    (y y' : Fin 5) :
    ∑ k, star (coeff 5 phases n y' k) * coeff 5 phases n y k =
      if y = y' then 1 else 0 := by
  have h4 : windowRoot 5 ^ 4 = -1 - windowRoot 5 - windowRoot 5 ^ 2 - windowRoot 5 ^ 3 := by
    simpa [Finset.sum_range_succ, sub_eq_add_neg, neg_add_rev, add_assoc, add_comm,
      add_left_comm] using
      (windowRoot_isPrimitiveRoot 5).pow_sub_one_eq (by norm_num : 1 < (5 : ℕ))
  interval_cases n <;> fin_cases y <;> fin_cases y' <;>
    norm_num [coefficient_formula, t, Fin.sum_univ_succ, Finset.sum_range_succ,
      star_mul, star_pow, root_relations.2.2] <;>
    ring_nf <;>
    simp only [pow_eq_pow_mod _ root_relations.1, Nat.reduceMod, pow_zero, pow_one] <;>
    rw [h4] <;> ring

private lemma phases_admissible : Admissible 5 phases := by
  exact ⟨phases_zero, coefficient_orthogonality⟩

private lemma shift_entry (i j : Fin 5) :
    shift i j = if i = j + 1 then 1 else 0 := by
  simpa only [Fin.val_one, pow_one] using
    D5.S3.Quantum.Information.StabilizerAutocorrelationNormRefutation.shift_power 1 i j

set_option maxHeartbeats 2000000 in
-- Fourier inversion leaves twenty-five nonzero matrix entries.
private lemma reference_entry (y i j : Fin 5) :
    R y i j = if i = j + 1 then
      windowRoot 5 ^ ((![0, 4, 1, 0, 0] j + y.val * j.val) % 5) else 0 := by
  have hz : clock = Matrix.diagonal (fun j : Fin 5 => windowRoot 5 ^ j.val) := rfl
  simp only [R, hz, Matrix.diagonal_pow, Pi.pow_apply, Matrix.mul_diagonal,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, shift_entry]
  by_cases hij : i = j + 1
  · subst i
    simp only [ite_true, one_mul]
    have h4 : windowRoot 5 ^ 4 = -1 - windowRoot 5 - windowRoot 5 ^ 2 - windowRoot 5 ^ 3 := by
      simpa [Finset.sum_range_succ, sub_eq_add_neg, neg_add_rev, add_assoc, add_comm,
        add_left_comm] using
        (windowRoot_isPrimitiveRoot 5).pow_sub_one_eq (by norm_num : 1 < (5 : ℕ))
    fin_cases y <;> fin_cases j <;>
      norm_num [coefficient_formula, t, Fin.sum_univ_succ, Finset.sum_range_succ,
        star_mul, star_pow, root_relations.2.2] <;>
      ring_nf <;>
      simp only [pow_eq_pow_mod _ root_relations.1, Nat.reduceMod, pow_zero, pow_one] <;>
      rw [h4] <;> ring
  · simp [hij]

private def U : Matrix (Fin 5) (Fin 5) ℂ :=
  Matrix.diagonal (fun j => windowRoot 5 ^ (![0, 0, 4, 0, 0] j : ℕ))

private lemma diagonal_unitary : U ∈ Matrix.unitaryGroup (Fin 5) ℂ := by
  apply Matrix.diagonal_mem_unitary.mpr
  apply Pi.mem_unitary_iff.mpr
  intro j
  apply (unitary ℂ).pow_mem
  apply Unitary.mem_iff_star_mul_self.mpr
  rw [root_relations.2.2, ← pow_succ, root_relations.1]

set_option maxHeartbeats 2000000 in
-- The diagonal conjugation is checked on the twenty-five nonzero entries.
private lemma reference_factorization (y : Fin 5) :
    R y = U * (shift * clock ^ y.val) * star U := by
  have hz : clock = Matrix.diagonal (fun j : Fin 5 => windowRoot 5 ^ j.val) := rfl
  ext i j
  simp only [reference_entry, U, Matrix.star_eq_conjTranspose,
    Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul,
    hz, Matrix.diagonal_pow, Pi.pow_apply, Pi.star_apply, shift_entry]
  by_cases hij : i = j + 1
  · subst i
    simp only [ite_true, one_mul]
    fin_cases y <;> fin_cases j <;>
      norm_num [star_pow, root_relations.2.2] <;> ring_nf <;>
      simp only [pow_eq_pow_mod _ root_relations.1, Nat.reduceMod, pow_zero, pow_one] <;>
      norm_num
  · simp [hij]

set_option maxHeartbeats 1000000 in
-- The frozen Weyl power law gives order five before diagonal conjugation.
private lemma reference_projective (y : Fin 5) :
    R y ∈ Matrix.unitaryGroup (Fin 5) ℂ ∧ R y ^ 5 = 1 := by
  have hx : shift ∈ Matrix.unitaryGroup (Fin 5) ℂ := by
    apply Matrix.mem_unitaryGroup_iff'.2
    exact (window_unitary (M := 5)).1
  have hz : clock ∈ Matrix.unitaryGroup (Fin 5) ℂ := by
    apply Matrix.mem_unitaryGroup_iff'.2
    exact (window_unitary (M := 5)).2
  have hm : shift * clock ^ y.val ∈ Matrix.unitaryGroup (Fin 5) ℂ :=
    (Matrix.unitaryGroup (Fin 5) ℂ).mul_mem hx
      ((Matrix.unitaryGroup (Fin 5) ℂ).pow_mem hz _)
  constructor
  · rw [reference_factorization]
    exact (Matrix.unitaryGroup (Fin 5) ℂ).mul_mem
      ((Matrix.unitaryGroup (Fin 5) ℂ).mul_mem diagonal_unitary hm)
      (Unitary.star_mem diagonal_unitary)
  · have hp : (shift * clock ^ y.val) ^ 5 = 1 := by
      let e := Matrix.reindexRingEquiv ℂ (ZMod.finEquiv 5).toEquiv.symm
      have hX : e (shiftMatrix 5) = shift := rfl
      have hZ : e (clockMatrix 5) = clock := rfl
      have hbase : D5.S3.Quantum.Algebra.WeylDisplacement.displacement
          5 1 ((ZMod.finEquiv 5) y) ^ 5 = 1 := by
        rw [D5.S3.Quantum.Algebra.WeylDisplacementPowers.displacement_pow]
        have h5 : ((5 : ℕ) : ZMod 5) = 0 := by decide
        have h10 : ((Nat.choose 5 2 : ℕ) : ZMod 5) = 0 := by decide
        simp only [h5, h10, zero_mul, ZMod.val_zero, pow_zero, one_smul,
          D5.S3.Quantum.Algebra.WeylDisplacement.displacement, mul_one]
      have hmap := congrArg e hbase
      rw [map_pow, map_one] at hmap
      have he : e (D5.S3.Quantum.Algebra.WeylDisplacement.displacement
          5 1 ((ZMod.finEquiv 5) y)) = shift * clock ^ y.val := by
        have h1 : (1 : ZMod 5).val = 1 := rfl
        have hy : ((ZMod.finEquiv 5) y).val = y.val := rfl
        simp only [D5.S3.Quantum.Algebra.WeylDisplacement.displacement,
          map_mul, map_pow, hX, hZ, h1, hy, pow_one]
      rw [he] at hmap
      exact hmap
    let u : (Matrix (Fin 5) (Fin 5) ℂ)ˣ :=
      Unitary.toUnits ⟨U, diagonal_unitary⟩
    rw [reference_factorization]
    change ((u : Matrix (Fin 5) (Fin 5) ℂ) * (shift * clock ^ y.val) *
      ((u⁻¹ : (Matrix (Fin 5) (Fin 5) ℂ)ˣ) : Matrix (Fin 5) (Fin 5) ℂ)) ^ 5 = 1
    rw [Units.conj_pow, hp, mul_one, Units.mul_inv]

private lemma witness_projective : IsProjectiveFamily 5 B := by
  intro y
  by_cases hy : y = 0
  · subst y
    rw [B, if_pos rfl]
    constructor
    · apply Unitary.smul_mem_of_mem _ (reference_projective 0).1
      apply Unitary.mem_iff_star_mul_self.mpr
      rw [root_relations.2.2, ← pow_succ, root_relations.1]
    · rw [smul_pow, root_relations.1, (reference_projective 0).2, one_smul]
  · simpa only [B, if_neg hy] using reference_projective y

set_option maxHeartbeats 3000000 in
-- Each reconstruction uses only twenty-five matrix-entry identities.
private lemma reconstruction :
    (∑ y, coeff 5 phases 1 y 0 • R y) = shift ∧
    (∑ y, coeff 5 phases 2 y 0 • R y ^ 2) = shift ^ 2 := by
  have h4 : windowRoot 5 ^ 4 = -1 - windowRoot 5 - windowRoot 5 ^ 2 - windowRoot 5 ^ 3 := by
    simpa [Finset.sum_range_succ, sub_eq_add_neg, neg_add_rev, add_assoc, add_comm,
      add_left_comm] using
      (windowRoot_isPrimitiveRoot 5).pow_sub_one_eq (by norm_num : 1 < (5 : ℕ))
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [coefficient_formula, t, Fin.sum_univ_succ, Finset.sum_range_succ,
      Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, pow_two, Matrix.mul_apply,
      reference_entry, shift_entry] <;>
    ring_nf <;>
    simp only [pow_eq_pow_mod _ root_relations.1, Nat.reduceMod, pow_zero, pow_one] <;>
    rw [h4] <;> ring

private lemma special_coefficients : coeff 5 phases 1 0 0 = g ∧
    coeff 5 phases 2 0 0 = g := by
  constructor <;>
    norm_num [coefficient_formula, t, g, Fin.sum_univ_succ, Finset.sum_range_succ] <;> ring

private lemma transformed_one :
    transformed 5 phases B 1 0 = shift + ((windowRoot 5 - 1) * g) • R 0 := by
  unfold transformed
  rw [← reconstruction.1]
  simp only [Fin.sum_univ_succ, B, Fin.succ_ne_zero, ite_false, ite_true, pow_one]
  rw [special_coefficients.1]
  simp only [sub_mul, one_mul, sub_smul, mul_smul]
  rw [smul_comm g (windowRoot 5)]
  abel

private lemma transformed_two :
    transformed 5 phases B 2 0 = shift ^ 2 + ((windowRoot 5 ^ 2 - 1) * g) • R 0 ^ 2 := by
  unfold transformed
  rw [← reconstruction.2]
  simp only [Fin.sum_univ_succ, B, Fin.succ_ne_zero, ite_false, ite_true]
  rw [special_coefficients.2]
  rw [show (windowRoot 5 • R 0) ^ 2 = windowRoot 5 ^ 2 • R 0 ^ 2 by
    simp only [pow_two, Matrix.smul_mul, Matrix.mul_smul, smul_smul]]
  simp only [sub_mul, one_mul, sub_smul, mul_smul]
  rw [smul_comm g (windowRoot 5 ^ 2)]
  abel

private lemma defect_entry :
    ((transformed 5 phases B 1 0) ^ 2 - transformed 5 phases B 2 0) 0 3 =
      g * (g - 1) * (windowRoot 5 - 1) ^ 2 := by
  rw [transformed_one, transformed_two]
  norm_num [pow_two, Matrix.mul_apply, Matrix.add_apply, Matrix.sub_apply,
    Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_succ, reference_entry, shift_entry]
  ring

private lemma g_nontrivial : g ≠ 0 ∧ g ≠ 1 := by
  have hs : (windowRoot 5 + windowRoot 5 ^ 4) ^ 2 +
      (windowRoot 5 + windowRoot 5 ^ 4) = 1 := by
    calc
      _ = windowRoot 5 ^ 8 + 2 * windowRoot 5 ^ 5 + windowRoot 5 ^ 4 +
          windowRoot 5 ^ 2 + windowRoot 5 := by ring
      _ = 1 := by
        rw [pow_eq_pow_mod 8 root_relations.1, root_relations.1]
        norm_num only [Nat.reduceMod]
        linear_combination root_relations.2.1
  constructor
  · intro hz
    have hg : windowRoot 5 + windowRoot 5 ^ 4 = -3 := by
      unfold g at hz
      linear_combination 5 * hz
    rw [hg] at hs
    norm_num at hs
  · intro ho
    have hg : windowRoot 5 + windowRoot 5 ^ 4 = 2 := by
      unfold g at ho
      linear_combination 5 * ho
    rw [hg] at hs
    norm_num at hs

theorem result : ¬ claim := by
  intro h
  have heq := h 5 Nat.prime_five phases phases_admissible B witness_projective 0 2
    (by norm_num) (by norm_num)
  have hz : g * (g - 1) * (windowRoot 5 - 1) ^ 2 = 0 := by
    rw [← defect_entry, ← heq, sub_self]
    rfl
  exact (mul_ne_zero (mul_ne_zero g_nontrivial.1 (sub_ne_zero.mpr g_nontrivial.2))
    (pow_ne_zero _ (sub_ne_zero.mpr ((windowRoot_isPrimitiveRoot 5).ne_one (by norm_num))))) hz

end

end D5.S3.Quantum.Measurements.SteeringPowerPreservationRefutation
