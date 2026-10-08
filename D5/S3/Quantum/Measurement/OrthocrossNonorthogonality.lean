/- GID: D5/S3/Quantum/Measurement/OrthocrossNonorthogonality
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/OrthocrossNonorthogonality
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Orthocross MIC elements are never orthogonal and every Gram entry decays uniformly (Conjecture 2 of arXiv:1812.08762). -/

import D5.S3.Quantum.Measurement.OrthocrossPairingPolynomial
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Measurement.OrthocrossNonorthogonality

open Matrix Complex
open scoped MatrixOrder ComplexOrder
open D5.S3.Quantum.Measurement.OrthocrossGramHalfInteger

/-- Strict positivity of distinct Gram entries and uniform decay of all entries. -/
def claim : Prop :=
  (∀ (d : ℕ) (U : unitaryGroup (Fin d) ℂ) (α β : Idx d), α ≠ β →
      0 < gram (U : Matrix (Fin d) (Fin d) ℂ) α β) ∧
  (∀ ε : ℝ, 0 < ε → ∃ d₀ : ℕ, ∀ d, d₀ ≤ d → ∀ (U : unitaryGroup (Fin d) ℂ) (α β : Idx d),
      ‖gram (U : Matrix (Fin d) (Fin d) ℂ) α β‖ < ε)

variable {d : ℕ}

/-- A Gram entry is the weighted squared modulus of an inverse-frame pairing. -/
theorem gram_eq_norm_sq (U : unitaryGroup (Fin d) ℂ) (α β : Idx d) :
    gram (U : Matrix (Fin d) (Fin d) ℂ) α β =
      weight α * weight β *
        (‖star (vec α) ⬝ᵥ ((frame (1 : Matrix (Fin d) (Fin d) ℂ))⁻¹ *ᵥ vec β)‖ ^ 2 : ℝ) := by
  let M := (frame (1 : Matrix (Fin d) (Fin d) ℂ))⁻¹
  have hM : M.IsHermitian := posDef_one.isHermitian.inv
  have hc : star (star (vec α) ⬝ᵥ (M *ᵥ vec β)) =
      star (vec β) ⬝ᵥ (M *ᵥ vec α) := by
    rw [← star_dotProduct, star_mulVec, hM.eq, ← dotProduct_mulVec]
  rw [gram_eq U]
  change (proj 1 α * M * proj 1 β * M).trace = _
  simp only [proj, one_mulVec, Matrix.smul_mul, Matrix.mul_smul, trace_smul,
    smul_eq_mul, vecMulVec_mul, trace_vecMulVec,
    dotProduct_comm (vec α), ← dotProduct_mulVec]
  simp only [vecMulVec_mulVec, mulVec_smul, dotProduct_smul, op_smul_eq_smul]
  rw [← hc]
  simp only [smul_eq_mul, Complex.star_def]
  rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  ring

#print axioms gram_eq_norm_sq

/-- A rational upper bound for the modulus of every off-diagonal frame entry. -/
private theorem cross_norm_bound (i j : Fin d) : ‖cross d i j‖ ≤ (3 / 4 : ℝ) := by
  have hm : ‖((1 - I) / 2 : ℂ)‖ ^ 2 = (1 / 2 : ℝ) := by
    rw [← Complex.normSq_eq_norm_sq]
    norm_num [Complex.normSq_div, Complex.normSq_apply]
  have hp : ‖((1 + I) / 2 : ℂ)‖ ^ 2 = (1 / 2 : ℝ) := by
    rw [← Complex.normSq_eq_norm_sq]
    norm_num [Complex.normSq_div, Complex.normSq_apply]
  simp only [cross, of_apply]
  split_ifs
  · norm_num
  · nlinarith [norm_nonneg ((1 - I) / 2 : ℂ)]
  · nlinarith [norm_nonneg ((1 + I) / 2 : ℂ)]

/-- The frame dominates one quarter of the dimension times the identity. -/
theorem frame_lower_bound :
    ((d : ℝ) / 4) • (1 : Matrix (Fin d) (Fin d) ℂ) ≤ frame 1 := by
  classical
  let A := frame (1 : Matrix (Fin d) (Fin d) ℂ) - ((d : ℝ) / 4) • 1
  have hA : A.IsHermitian :=
    posDef_one.isHermitian.sub (isHermitian_one.smul (IsSelfAdjoint.all _))
  rw [Matrix.le_iff]
  change A.PosSemidef
  rw [hA.posSemidef_iff_eigenvalues_nonneg]
  intro i
  change 0 ≤ hA.eigenvalues i
  let v : Fin d → ℂ := ⇑(hA.eigenvectorBasis i)
  have hv : v ≠ 0 := by
    intro hv
    apply hA.eigenvectorBasis.orthonormal.ne_zero i
    ext j
    exact congrFun hv j
  have hev : Module.End.HasEigenvalue (Matrix.toLin' A) (hA.eigenvalues i : ℂ) := by
    apply Module.End.hasEigenvalue_of_hasEigenvector
    refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, hv⟩
    ext j
    simpa [v, Pi.smul_apply, RCLike.real_smul_eq_coe_smul] using
      congrFun (hA.mulVec_eigenvectorBasis i) j
  obtain ⟨k, hk⟩ := eigenvalue_mem_ball hev
  have hd : A k k = (((d : ℝ) * 3 / 4 : ℝ) : ℂ) := by
    simp [A, frame_one, cross, Matrix.smul_apply]
    ring
  have ho : ∀ j ∈ Finset.univ.erase k, ‖A k j‖ ≤ (3 / 4 : ℝ) := by
    intro j hj
    have hjk : k ≠ j := (Finset.mem_erase.mp hj).1.symm
    simpa [A, frame_one, Matrix.smul_apply, one_apply, hjk] using cross_norm_bound k j
  have hs : (∑ j ∈ Finset.univ.erase k, ‖A k j‖) ≤ (d : ℝ) * 3 / 4 := by
    calc
      _ ≤ ∑ j ∈ Finset.univ.erase k, (3 / 4 : ℝ) := Finset.sum_le_sum ho
      _ ≤ ∑ _j : Fin d, (3 / 4 : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
          (fun _ _ _ => by norm_num)
      _ = _ := by simp; ring
  have hg : ‖(hA.eigenvalues i : ℂ) - A k k‖ ≤
      ∑ j ∈ Finset.univ.erase k, ‖A k j‖ := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hk
  have hr : (d : ℝ) * 3 / 4 - hA.eigenvalues i ≤
      ‖(hA.eigenvalues i : ℂ) - A k k‖ := by
    simpa only [hd, Complex.sub_re, Complex.ofReal_re, norm_sub_rev] using
      Complex.re_le_norm (A k k - (hA.eigenvalues i : ℂ))
  linarith

open scoped Matrix.Norms.L2Operator

/-- The operator norm of the inverse frame is at most 4/d in positive dimension. -/
theorem inverse_frame_norm_bound (hd : 0 < d) :
    ‖(frame (1 : Matrix (Fin d) (Fin d) ℂ))⁻¹‖ ≤ 4 / (d : ℝ) := by
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hs : 0 < (d : ℝ) / 4 := by positivity
  have hpos : IsStrictlyPositive
      (((d : ℝ) / 4) • (1 : Matrix (Fin d) (Fin d) ℂ)) :=
    (PosDef.one.smul hs).isStrictlyPositive
  have hi : (((d : ℝ) / 4) • (1 : Matrix (Fin d) (Fin d) ℂ))⁻¹ =
      (4 / (d : ℝ)) • 1 := by
    apply inv_eq_left_inv
    have hc : ((d : ℝ) / 4) * (4 / (d : ℝ)) = 1 := by field_simp
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, hc, one_smul]
  have hle := CStarAlgebra.ringInverse_le_ringInverse (frame_lower_bound (d := d)) hpos
  rw [← Matrix.nonsing_inv_eq_ringInverse, ← Matrix.nonsing_inv_eq_ringInverse, hi] at hle
  apply (CStarAlgebra.norm_le_iff_le_algebraMap _ (by positivity)
    posDef_one.inv.posSemidef.nonneg).mpr
  simpa only [Algebra.algebraMap_eq_smul_one] using hle

/-- All three types of orthocross vector have Euclidean norm at most two. -/
private theorem vec_norm_bound (α : Idx d) :
    ‖WithLp.toLp 2 (vec α)‖ ≤ (2 : ℝ) := by
  rcases α with j | p | p
  · norm_num [OrthocrossGramHalfInteger.vec]
  · change ‖(EuclideanSpace.single p.1.1 (1 : ℂ)) + EuclideanSpace.single p.1.2 1‖ ≤ _
    exact (norm_add_le _ _).trans (by norm_num)
  · change ‖(EuclideanSpace.single p.1.1 (1 : ℂ)) + EuclideanSpace.single p.1.2 I‖ ≤ _
    exact (norm_add_le _ _).trans (by norm_num)

/-- The inverse-frame pairings are uniformly bounded by 16/d. -/
private theorem pairing_norm_bound (hd : 0 < d) (α β : Idx d) :
    ‖star (vec α) ⬝ᵥ ((frame (1 : Matrix (Fin d) (Fin d) ℂ))⁻¹ *ᵥ vec β)‖ ≤
      16 / (d : ℝ) := by
  let M := (frame (1 : Matrix (Fin d) (Fin d) ℂ))⁻¹
  let a : EuclideanSpace ℂ (Fin d) := WithLp.toLp 2 (vec α)
  let b : EuclideanSpace ℂ (Fin d) := WithLp.toLp 2 (vec β)
  have he : star (vec α) ⬝ᵥ (M *ᵥ vec β) =
      inner ℂ a (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) M b) := by
    simp [PiLp.inner_apply, dotProduct, a, b, Matrix.toEuclideanCLM_toLp,
      mul_comm]
  rw [he]
  calc
    _ ≤ ‖a‖ * ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) M b‖ := norm_inner_le_norm _ _
    _ ≤ ‖a‖ * (‖M‖ * ‖b‖) :=
      mul_le_mul_of_nonneg_left
        ((Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) M).le_opNorm b) (norm_nonneg _)
    _ ≤ 2 * ((4 / (d : ℝ)) * 2) := by
      gcongr
      · exact vec_norm_bound α
      · exact inverse_frame_norm_bound hd
      · exact vec_norm_bound β
    _ = _ := by ring

/-- Every Gram entry has norm at most 256/d^2 in positive dimension. -/
theorem gram_norm_bound (hd : 0 < d) (U : unitaryGroup (Fin d) ℂ) (α β : Idx d) :
    ‖gram (U : Matrix (Fin d) (Fin d) ℂ) α β‖ ≤ 256 / (d : ℝ) ^ 2 := by
  have hw : ∀ γ : Idx d, ‖weight γ‖ ≤ 1 := by
    intro γ
    rcases γ with j | p | p <;> norm_num [weight]
  rw [gram_eq_norm_sq U, norm_mul, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  calc
    _ ≤ 1 * 1 * (16 / (d : ℝ)) ^ 2 := by
      gcongr
      · exact hw α
      · exact hw β
      · exact pairing_norm_bound hd α β
    _ = _ := by ring

/-- Clause (B): every Gram entry tends uniformly to zero with increasing dimension. -/
theorem gram_uniform_decay :
    ∀ ε : ℝ, 0 < ε → ∃ d₀ : ℕ, ∀ d, d₀ ≤ d →
      ∀ (U : unitaryGroup (Fin d) ℂ) (α β : Idx d),
        ‖gram (U : Matrix (Fin d) (Fin d) ℂ) α β‖ < ε := by
  intro ε hε
  obtain ⟨n, hn⟩ := exists_nat_gt (max 1 (256 / ε))
  refine ⟨n, fun d hd U α β => ?_⟩
  have hn1 : (1 : ℝ) < n := (le_max_left _ _).trans_lt hn
  have hdR : (n : ℝ) ≤ d := by exact_mod_cast hd
  have hd1 : (1 : ℝ) < d := hn1.trans_le hdR
  have hdN : 0 < d := by exact_mod_cast (lt_trans (by norm_num : (0 : ℝ) < 1) hd1)
  have hc : 256 / ε < (d : ℝ) := ((le_max_right _ _).trans_lt hn).trans_le hdR
  have hsq : (d : ℝ) ≤ (d : ℝ) ^ 2 := by nlinarith
  apply (gram_norm_bound hdN U α β).trans_lt
  apply (div_lt_iff₀ (by positivity : 0 < (d : ℝ) ^ 2)).mpr
  have h := (div_lt_iff₀ hε).mp hc
  nlinarith

/-- Every orthocross Gram entry is a strictly positive real number. -/
theorem gram_pos (U : unitaryGroup (Fin d) ℂ) (α β : Idx d) :
    0 < gram (U : Matrix (Fin d) (Fin d) ℂ) α β := by
  have hw (γ : Idx d) : 0 < weight γ := by
    rcases γ with j | p | p <;> norm_num [weight]
  have hn : 0 < ‖star (vec α) ⬝ᵥ
      ((frame (1 : Matrix (Fin d) (Fin d) ℂ))⁻¹ *ᵥ vec β)‖ :=
    norm_pos_iff.mpr (OrthocrossPairingPolynomial.inverse_frame_pairing_ne_zero α β)
  rw [gram_eq_norm_sq U α β]
  exact mul_pos (mul_pos (hw α) (hw β)) (Complex.zero_lt_real.mpr (sq_pos_of_pos hn))

/-- Orthocross Gram entries are positive and decay uniformly with dimension. -/
theorem result : claim :=
  ⟨fun _d U α β _hαβ => gram_pos U α β, gram_uniform_decay⟩

#print axioms gram_pos
#print axioms result

#print axioms frame_lower_bound
#print axioms inverse_frame_norm_bound
#print axioms gram_norm_bound
#print axioms gram_uniform_decay
#print axioms OrthocrossGramHalfInteger.result

end D5.S3.Quantum.Measurement.OrthocrossNonorthogonality
