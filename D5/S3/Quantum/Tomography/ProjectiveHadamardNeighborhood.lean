/- GID: D5/S3/Quantum/Tomography/ProjectiveHadamardNeighborhood
   generality: G
   mirror-B: D5/B/S3/Quantum/Tomography/ProjectiveHadamardNeighborhood
   mirror-E: none(waiver:analytic-gauge-domain)
   anchors: []
   digest: Pairwise phase ratios give a reanchoring-invariant complex domain and a scale-independent differential envelope for the actual Hadamard Laurent residual. -/

import D5.S3.Quantum.Tomography.HolomorphicCayleyHadamard
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FinCases

/- Reuse audit: uses the existing Cayley phase and paired residual, Matrix
   mulVec/vecMul, norm, finite sums and actual complex derivative rules.
   The Laurent expression below is a coordinate change of the existing
   residual, not a second Hadamard, root, context or interval predicate.
   Projective reanchoring is division by one common NONZERO coordinate.
   Unit row phases preserve the domain; preserving the residual also requires
   the corresponding row gauge on H, and is not asserted for H fixed.
-/

open scoped BigOperators Matrix
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Tomography.ProjectiveHadamardNeighborhood

open Matrix
open D5.S3.Quantum.Tomography.HolomorphicCayleyHadamard

/-- A fixed-width neighborhood of the projective phase torus. Pairwise
ratios, rather than independent bounds relative to a chosen anchor, determine
its width. At R>1 it contains every vector of unit phases. -/
def phaseRatioDomain (R : ℝ) : Set (Fin 6 → ℂ) :=
  {w | ∀ i j, ‖w i‖ < R * ‖w j‖}

/-- The existing squared-modulus residual in nonzero phase coordinates.
Conjugation occurs only on the fixed matrix coefficients. -/
def projectiveHadamardResidual
    (H : Matrix (Fin 6) (Fin 6) ℂ) (w : Fin 6 → ℂ) : Fin 6 → ℂ :=
  fun a ↦ (Hᴴ *ᵥ w) a * ((fun i ↦ (w i)⁻¹) ᵥ* H) a - 6

private theorem coordinate_ne_zero (R : ℝ) (w : Fin 6 → ℂ)
    (hw : w ∈ phaseRatioDomain R) (i : Fin 6) : w i ≠ 0 := by
  intro hzero
  have h := hw i i
  simpa [hzero] using h

private theorem norm_ratio_lt (R : ℝ) (w : Fin 6 → ℂ)
    (hw : w ∈ phaseRatioDomain R) (i j : Fin 6) : ‖w i / w j‖ < R := by
  rw [norm_div]
  exact (div_lt_iff₀ (norm_pos_iff.mpr (coordinate_ne_zero R w hw j))).2 (hw i j)

private theorem domain_scale_iff (R : ℝ) (w : Fin 6 → ℂ)
    (c : ℂ) (hc : c ≠ 0) :
    (fun i ↦ c * w i) ∈ phaseRatioDomain R ↔ w ∈ phaseRatioDomain R := by
  have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
  change (∀ i j, ‖c * w i‖ < R * ‖c * w j‖) ↔ _
  simp only [norm_mul]
  constructor
  · intro h i j
    have hij := h i j
    rw [mul_left_comm R ‖c‖] at hij
    exact (mul_lt_mul_iff_right₀ hcpos).mp hij
  · intro h i j
    rw [mul_left_comm R ‖c‖]
    exact (mul_lt_mul_iff_right₀ hcpos).mpr (h i j)

private theorem residual_scale_invariant
    (H : Matrix (Fin 6) (Fin 6) ℂ) (w : Fin 6 → ℂ)
    (c : ℂ) (hc : c ≠ 0) :
    projectiveHadamardResidual H (fun i ↦ c * w i) =
      projectiveHadamardResidual H w := by
  ext a
  have hA : (Hᴴ *ᵥ (fun i ↦ c * w i)) a = c * (Hᴴ *ᵥ w) a := by
    simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hB : ((fun i ↦ (c * w i)⁻¹) ᵥ* H) a =
      c⁻¹ * ((fun i ↦ (w i)⁻¹) ᵥ* H) a := by
    simp only [Matrix.vecMul, dotProduct, mul_inv_rev, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp only [projectiveHadamardResidual, hA, hB]
  rw [mul_mul_mul_comm, mul_inv_cancel₀ hc, one_mul]

/-- Reanchoring any actual phase vector preserves BOTH its fixed-width
complex domain and every actual residual. No width is spent at successive
anchor changes. The normalized coordinates stay in (1/R,R), uniformly in the
chosen anchor; residual values are unchanged, not merely close. -/
theorem projective_reanchoring_preserves_domain_and_residual
    (R : ℝ) (hR : 1 < R)
    (H : Matrix (Fin 6) (Fin 6) ℂ) (w : Fin 6 → ℂ)
    (hw : w ∈ phaseRatioDomain R) (a : Fin 6) :
    let v : Fin 6 → ℂ := fun i ↦ w i / w a
    v ∈ phaseRatioDomain R ∧ v a = 1 ∧
      (∀ i, 1 / R < ‖v i‖ ∧ ‖v i‖ < R) ∧
      projectiveHadamardResidual H v = projectiveHadamardResidual H w := by
  have ha := coordinate_ne_zero R w hw a
  have hc : (w a)⁻¹ ≠ 0 := inv_ne_zero ha
  have hv : (fun i ↦ w i / w a) ∈ phaseRatioDomain R := by
    simpa only [div_eq_mul_inv, mul_comm] using
      (domain_scale_iff R w ((w a)⁻¹) hc).2 hw
  refine ⟨hv, div_self ha, ?_, ?_⟩
  · intro i
    refine ⟨?_, norm_ratio_lt R w hw i a⟩
    have hap : 0 < ‖w a‖ := norm_pos_iff.mpr ha
    have hRp : 0 < R := lt_trans zero_lt_one hR
    rw [norm_div]
    apply (div_lt_div_iff₀ hRp hap).2
    simpa only [one_mul, mul_one, mul_comm] using hw a i
  · simpa only [div_eq_mul_inv, mul_comm] using
      residual_scale_invariant H w ((w a)⁻¹) hc

/-- The pairwise-ratio domain is open, contains the complete real phase
 torus, and is unchanged by a common nonzero complex scale, a coordinate
 permutation and arbitrary fixed unit prefactors. Conjugation also preserves
 the domain. These are domain statements, not claims that H-fixed residuals
 are invariant under arbitrary row phases or coordinate permutations. -/
theorem phase_ratio_domain_open_torus_and_gauges (R : ℝ) (hR : 1 < R) :
    IsOpen (phaseRatioDomain R) ∧
      (∀ w : Fin 6 → ℂ, (∀ i, ‖w i‖ = 1) → w ∈ phaseRatioDomain R) ∧
      (∀ (w : Fin 6 → ℂ) (c : ℂ), c ≠ 0 →
        ∀ (p : Equiv.Perm (Fin 6)) (s : Fin 6 → ℂ),
          (∀ i, ‖s i‖ = 1) →
          ((fun i ↦ c * s i * w (p i)) ∈ phaseRatioDomain R ↔
            w ∈ phaseRatioDomain R)) ∧
      (∀ w : Fin 6 → ℂ,
        (fun i ↦ star (w i)) ∈ phaseRatioDomain R ↔ w ∈ phaseRatioDomain R) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hset : phaseRatioDomain R =
        ⋂ i : Fin 6, ⋂ j : Fin 6, {w : Fin 6 → ℂ | ‖w i‖ < R * ‖w j‖} := by
      ext w
      simp only [phaseRatioDomain, Set.mem_setOf_eq, Set.mem_iInter]
    rw [hset]
    apply isOpen_iInter_of_finite
    intro i
    apply isOpen_iInter_of_finite
    intro j
    exact isOpen_lt (continuous_apply i).norm
      (continuous_const.mul (continuous_apply j).norm)
  · intro w hw i j
    simpa only [hw i, hw j, mul_one] using hR
  · intro w c hc p s hs
    have hnorm : ∀ i, ‖c * s i * w (p i)‖ = ‖c‖ * ‖w (p i)‖ := by
      intro i
      rw [norm_mul, norm_mul, hs i, mul_one]
    have hcpos := norm_pos_iff.mpr hc
    constructor
    · intro h i j
      have hij := h (p.symm i) (p.symm j)
      rw [hnorm, hnorm, p.apply_symm_apply, p.apply_symm_apply,
        mul_left_comm R ‖c‖] at hij
      exact (mul_lt_mul_iff_right₀ hcpos).mp hij
    · intro h i j
      rw [hnorm, hnorm, mul_left_comm R ‖c‖]
      exact (mul_lt_mul_iff_right₀ hcpos).mpr (h (p i) (p j))
  · intro w
    simp only [phaseRatioDomain, Set.mem_setOf_eq, norm_star]

private theorem reciprocal_coordinate_hasFDerivAt
    (w : Fin 6 → ℂ) (i : Fin 6) (hi : w i ≠ 0) :
    HasFDerivAt (fun v : Fin 6 → ℂ ↦ (v i)⁻¹)
      ((-(w i ^ 2)⁻¹) •
        (ContinuousLinearMap.proj i : (Fin 6 → ℂ) →L[ℂ] ℂ)) w := by
  have h := (hasDerivAt_inv hi).hasFDerivAt.comp w
    (ContinuousLinearMap.proj i : (Fin 6 → ℂ) →L[ℂ] ℂ).hasFDerivAt
  convert! h using 1
  ext v
  simp [ContinuousLinearMap.toSpanSingleton_apply, mul_comm]

/-- The ACTUAL complex derivative in phase coordinates, together with a
projectively scale-independent envelope for its Euler-scaled entries.
At R=2 and unit Hadamard entries the entry bound is 20. The diagonal term
cancels before taking absolute values, leaving only five pairs of terms.

The bound concerns w_k times the ordinary partial derivative. Comparing it
with a Cayley Jacobian requires the chain rule; it is not automatically a
bound for the previous Newton preconditioner. No nonsingularity is asserted. -/
theorem projective_residual_hasFDerivAt_and_scaled_bound
    (R M : ℝ) (hM : 0 ≤ M)
    (H : Matrix (Fin 6) (Fin 6) ℂ) (hH : ∀ i a, ‖H i a‖ ≤ M)
    (w : Fin 6 → ℂ) (hw : w ∈ phaseRatioDomain R) :
    let J : Matrix (Fin 6) (Fin 6) ℂ := fun a k ↦
      star (H k a) * ((fun i ↦ (w i)⁻¹) ᵥ* H) a -
        (H k a / w k ^ 2) * (Hᴴ *ᵥ w) a
    HasFDerivAt (projectiveHadamardResidual H)
      (ContinuousLinearMap.pi (fun a ↦ ∑ k, J a k •
        (ContinuousLinearMap.proj k : (Fin 6 → ℂ) →L[ℂ] ℂ))) w ∧
      (∀ a k, ‖w k * J a k‖ ≤ 10 * R * M ^ 2) := by
  let J : Matrix (Fin 6) (Fin 6) ℂ := fun a k ↦
    star (H k a) * ((fun i ↦ (w i)⁻¹) ᵥ* H) a -
      (H k a / w k ^ 2) * (Hᴴ *ᵥ w) a
  have hnz := coordinate_ne_zero R w hw
  change HasFDerivAt (projectiveHadamardResidual H)
    (ContinuousLinearMap.pi (fun a ↦ ∑ k, J a k •
      (ContinuousLinearMap.proj k : (Fin 6 → ℂ) →L[ℂ] ℂ))) w ∧ _
  constructor
  · apply hasFDerivAt_pi.mpr
    intro a
    have hA := HasFDerivAt.fun_sum (u := Finset.univ) (fun k _ ↦
      ((ContinuousLinearMap.proj k : (Fin 6 → ℂ) →L[ℂ] ℂ).hasFDerivAt (x := w) |>.const_mul
        (star (H k a))))
    have hB := HasFDerivAt.fun_sum (u := Finset.univ) (fun k _ ↦
      (reciprocal_coordinate_hasFDerivAt w k (hnz k)).mul_const (H k a))
    have h := (hA.mul hB).sub_const (6 : ℂ)
    convert! h using 1
    ext v
    simp only [J, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
    conv_rhs => rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    simp only [Matrix.mulVec, Matrix.vecMul, dotProduct, Matrix.conjTranspose_apply]
    ring
  · intro a k
    let term : Fin 6 → ℂ := fun j ↦
      star (H k a) * H j a * (w k / w j) -
        star (H j a) * H k a * (w j / w k)
    have hzero : term k = 0 := by simp [term, div_self (hnz k)]
    have hfirst : w k * (star (H k a) * ((fun i ↦ (w i)⁻¹) ᵥ* H) a) =
        ∑ j, star (H k a) * H j a * (w k / w j) := by
      simp only [Matrix.vecMul, dotProduct, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      simp only [div_eq_mul_inv]
      ring
    have hsecond : w k * ((H k a / w k ^ 2) * (Hᴴ *ᵥ w) a) =
        ∑ j, star (H j a) * H k a * (w j / w k) := by
      simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply,
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      field_simp [hnz k]
    have hsum : w k * J a k = ∑ j, term j := by
      change w k * (star (H k a) * ((fun i ↦ (w i)⁻¹) ᵥ* H) a -
        (H k a / w k ^ 2) * (Hᴴ *ᵥ w) a) = _
      rw [mul_sub, hfirst, hsecond, ← Finset.sum_sub_distrib]
    have hproduct (i j : Fin 6) :
        ‖star (H i a) * H j a * (w i / w j)‖ ≤ M ^ 2 * R := by
      have hh : ‖star (H i a) * H j a‖ ≤ M ^ 2 := by
        rw [norm_mul, norm_star, pow_two]
        exact mul_le_mul (hH i a) (hH j a) (norm_nonneg _) hM
      rw [norm_mul]
      exact mul_le_mul hh (norm_ratio_lt R w hw i j).le
        (norm_nonneg _) (sq_nonneg M)
    have hterm (j : Fin 6) : ‖term j‖ ≤
        if j = k then 0 else 2 * (M ^ 2 * R) := by
      by_cases hj : j = k
      · subst j
        simp [hzero]
      · rw [if_neg hj]
        exact (norm_sub_le _ _).trans (by linarith [hproduct k j, hproduct j k])
    rw [hsum]
    calc
      ‖∑ j, term j‖ ≤ ∑ j, ‖term j‖ := norm_sum_le _ _
      _ ≤ ∑ j : Fin 6, (if j = k then 0 else 2 * (M ^ 2 * R)) :=
        Finset.sum_le_sum (fun j _ ↦ hterm j)
      _ = 10 * R * M ^ 2 := by
        classical
        fin_cases k <;> simp [Fin.sum_univ_succ] <;> ring

/-- Exact binding back to the existing holomorphic Cayley owner. This
identifies the Laurent readout with the already defined paired residual;
it does not use a numerical fit or restrict the coordinates to the real slice. -/
theorem paired_cayley_residual_eq_projective_readout
    (H : Matrix (Fin 6) (Fin 6) ℂ) (s z : Fin 6 → ℂ)
    (hs : ∀ k, Complex.normSq (s k) = 1)
    (hm : ∀ k, 1 - Complex.I * z k ≠ 0)
    (hp : ∀ k, 1 + Complex.I * z k ≠ 0) :
    pairedCayleyResidual H s z =
      projectiveHadamardResidual H (fun k ↦ cayleyPhase (s k) (z k)) := by
  have hdual (k : Fin 6) : cayleyPhase (star (s k)) (-z k) =
      (cayleyPhase (s k) (z k))⁻¹ := by
    have hss : s k * star (s k) = 1 := by
      simpa only [Complex.star_def, hs k, Complex.ofReal_one] using
        Complex.mul_conj (s k)
    have hprod : cayleyPhase (s k) (z k) *
        cayleyPhase (star (s k)) (-z k) = 1 := by
      calc
        _ = s k * star (s k) := by
          dsimp [cayleyPhase]
          simp only [mul_neg, sub_neg_eq_add]
          field_simp [hm k, hp k]
          <;> ring
        _ = 1 := hss
    have hnz : cayleyPhase (s k) (z k) ≠ 0 := by
      intro hzero
      rw [hzero, zero_mul] at hprod
      exact zero_ne_one hprod
    calc
      cayleyPhase (star (s k)) (-z k) =
          ((cayleyPhase (s k) (z k))⁻¹ * cayleyPhase (s k) (z k)) *
            cayleyPhase (star (s k)) (-z k) := by
        rw [inv_mul_cancel₀ hnz, one_mul]
      _ = (cayleyPhase (s k) (z k))⁻¹ := by
        rw [mul_assoc, hprod, mul_one]
  ext a
  change (∑ k, star (H k a) * cayleyPhase (s k) (z k)) *
      (∑ k, H k a * cayleyPhase (star (s k)) (-z k)) - 6 =
    (∑ k, star (H k a) * cayleyPhase (s k) (z k)) *
      (∑ k, (cayleyPhase (s k) (z k))⁻¹ * H k a) - 6
  simp_rw [hdual]
  simp only [mul_comm]

#print axioms projective_reanchoring_preserves_domain_and_residual
#print axioms phase_ratio_domain_open_torus_and_gauges
#print axioms projective_residual_hasFDerivAt_and_scaled_bound
#print axioms paired_cayley_residual_eq_projective_readout

end D5.S3.Quantum.Tomography.ProjectiveHadamardNeighborhood
