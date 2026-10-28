/- GID: D5/S3/StatisticalMechanics/SteadyStateBlockMarkovFormRefutation
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/SteadyStateBlockMarkovFormRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/StatisticalMechanics/SteadyStateBlockMarkovFormRefutation.claim; result=D5/S3/StatisticalMechanics/SteadyStateBlockMarkovFormRefutation.result; claim=D5/S3/StatisticalMechanics/SteadyStateBlockMarkovFormRefutation.claim
   digest: An irreducible steady-state block of a four-state generator has no Markov form. -/

import D5.S3.TotalVariation.CycleSingleCutMinimax

set_option autoImplicit false
set_option linter.style.longLine false

namespace D5.S3.StatisticalMechanics.SteadyStateBlockMarkovFormRefutation

open scoped BigOperators Matrix
open Matrix
open D5.S3.TotalVariation.CycleSingleCutMinimax (Probability)

noncomputable section

/-- Real continuous-time generators use nonnegative off-diagonal rates and zero column sums. -/
def IsMarkovGenerator {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∀ i j, i ≠ j → 0 ≤ M i j) ∧ ∀ j, ∑ i, M i j = 0

/-- Every irreducible symmetry block containing a stationary probability has a Markov form. -/
def claim : Prop :=
  ∀ (N : ℕ) (L U : Matrix (Fin N) (Fin N) ℝ) (p : Fin N → ℝ),
    IsMarkovGenerator L → U ∈ Matrix.orthogonalGroup (Fin N) ℝ → U * L = L * U →
    Probability p → L *ᵥ p = 0 →
    ∀ (d : ℕ) (V : Matrix (Fin N) (Fin d) ℝ) (u : ℝ),
      Vᵀ * V = 1 → L * V = V * (Vᵀ * L * V) → U * V = u • V →
      (∀ x, U *ᵥ x = u • x → ∃ c, V *ᵥ c = x) →
      (∃ c, V *ᵥ c = p) →
      (∀ X : Matrix (Fin d) (Fin d) ℂ,
        X ∈ Matrix.unitaryGroup (Fin d) ℂ →
        X * (Vᵀ * L * V).map Complex.ofReal = (Vᵀ * L * V).map Complex.ofReal * X →
        ∃ μ : ℂ, X = μ • (1 : Matrix (Fin d) (Fin d) ℂ)) →
      ∃ (S : Matrix (Fin d) (Fin d) ℂ) (B : Matrix (Fin d) (Fin d) ℝ),
        IsUnit S ∧ IsMarkovGenerator B ∧
        S⁻¹ * (Vᵀ * L * V).map Complex.ofReal * S = B.map Complex.ofReal

private def L : Matrix (Fin 4) (Fin 4) ℝ :=
  !![-295/256, 25/256, 25/256, 281/256;
     273/256, -303/256, 17/256, 17/256;
     7/256, 263/256, -313/256, 7/256;
     15/256, 15/256, 271/256, -305/256]

private def p : Fin 4 → ℝ := ![17/64, 17/64, 15/64, 15/64]

private def U : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1/2, 1/2, -1/2, 1/2; 1/2, 1/2, 1/2, -1/2;
     -1/2, 1/2, 1/2, 1/2; 1/2, -1/2, 1/2, 1/2]

private def V : Matrix (Fin 4) (Fin 3) ℝ :=
  !![1/2, 1/2, -1/2; 1/2, 1/2, 1/2; 1/2, -1/2, 1/2; 1/2, -1/2, -1/2]

private def A : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, 0, 0; 5/64, -5/4, -1; -1/16, 1, -5/4]

private theorem generator : IsMarkovGenerator L := by
  constructor
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      first | exact (hij rfl).elim | norm_num [L.eq_1]
  · intro j
    fin_cases j <;> norm_num [L.eq_1, Fin.sum_univ_succ]

private theorem orthogonal : U ∈ Matrix.orthogonalGroup (Fin 4) ℝ := by
  apply (Matrix.mem_orthogonalGroup_iff (Fin 4) ℝ).mpr
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [U.eq_1, Matrix.mul_apply, Fin.sum_univ_succ]

private theorem symmetry : U * L = L * U := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [U.eq_1, L.eq_1, Matrix.mul_apply, Fin.sum_univ_succ]

private theorem probability : Probability p := by
  constructor
  · intro i
    fin_cases i <;> norm_num [p.eq_1]
  · norm_num [p.eq_1, Fin.sum_univ_succ]

private theorem stationary : L *ᵥ p = 0 := by
  ext i
  fin_cases i <;> norm_num [L.eq_1, p.eq_1, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

private theorem frame : Vᵀ * V = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [V.eq_1, Matrix.mul_apply, Fin.sum_univ_succ]

private theorem restriction : Vᵀ * L * V = A := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [V.eq_1, L.eq_1, A.eq_1, Matrix.mul_apply, Fin.sum_univ_succ]

private theorem invariant : L * V = V * A := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [L.eq_1, V.eq_1, A.eq_1, Matrix.mul_apply, Fin.sum_univ_succ]

private theorem eigenframe : U * V = V := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [U.eq_1, V.eq_1, Matrix.mul_apply, Fin.sum_univ_succ]

private theorem contains_stationary : ∃ c, V *ᵥ c = p := by
  refine ⟨![1/2, 1/32, 0], ?_⟩
  ext i
  fin_cases i <;> norm_num [V.eq_1, p.eq_1, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

private theorem projector : V * Vᵀ = (1/2 : ℝ) • (1 + U) := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [U.eq_1, V.eq_1, Matrix.mul_apply, Fin.sum_univ_succ]

private theorem eigenspace (x : Fin 4 → ℝ) (hx : U *ᵥ x = (1 : ℝ) • x) :
    ∃ c, V *ᵥ c = x := by
  refine ⟨Vᵀ *ᵥ x, ?_⟩
  rw [Matrix.mulVec_mulVec, projector, Matrix.smul_mulVec, Matrix.add_mulVec,
    Matrix.one_mulVec, hx, one_smul, ← two_smul ℝ x, smul_smul]
  norm_num

private def e : Fin 3 → ℂ := Pi.single 0 1

private def K : Matrix (Fin 3) (Fin 3) ℂ := fun i j =>
  ![e i, ((A.map Complex.ofReal) *ᵥ e) i,
    ((A.map Complex.ofReal) *ᵥ ((A.map Complex.ofReal) *ᵥ e)) i] j

private theorem cyclic_det : K.det = (41/4096 : ℂ) := by
  norm_num [K.eq_1, e.eq_1, A.eq_1, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
    Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

private theorem irreducible (X : Matrix (Fin 3) (Fin 3) ℂ)
    (hX : X ∈ Matrix.unitaryGroup (Fin 3) ℂ)
    (hcomm : X * A.map Complex.ofReal = A.map Complex.ofReal * X) :
    ∃ μ : ℂ, X = μ • (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  have hinv : Commute (star X) (A.map Complex.ofReal) :=
    Commute.units_inv_left (u := Unitary.toUnits ⟨X, hX⟩) hcomm
  have hstar : X * star (A.map Complex.ofReal) = star (A.map Complex.ofReal) * X :=
    hinv.star_right.eq
  have h10 := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => M 1 0) hstar
  have h20 := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => M 2 0) hstar
  norm_num [A.eq_1, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.star_apply,
    Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail] at h10 h20
  have hz1 : X 1 0 = 0 := by
    linear_combination (20/41 : ℂ) * h10 + (16/41 : ℂ) * h20
  have hz2 : X 2 0 = 0 := by
    linear_combination (-16/41 : ℂ) * h10 + (20/41 : ℂ) * h20
  have hXe : X *ᵥ e = (X 0 0) • e := by
    ext i
    fin_cases i <;> simp [e.eq_1, hz1, hz2]
  have hstep (z : Fin 3 → ℂ) (hz : X *ᵥ z = (X 0 0) • z) :
      X *ᵥ ((A.map Complex.ofReal) *ᵥ z) =
        (X 0 0) • ((A.map Complex.ofReal) *ᵥ z) := by
    rw [Matrix.mulVec_mulVec, hcomm, ← Matrix.mulVec_mulVec, hz, Matrix.mulVec_smul]
  have hcyclic : X * K = (X 0 0) • K := by
    ext i j
    fin_cases j
    · exact congrFun hXe i
    · exact congrFun (hstep e hXe) i
    · exact congrFun (hstep ((A.map Complex.ofReal) *ᵥ e) (hstep e hXe)) i
  have hK : IsUnit K := by
    apply (Matrix.isUnit_iff_isUnit_det K).mpr
    rw [cyclic_det]
    norm_num
  refine ⟨X 0 0, hK.mul_right_cancel ?_⟩
  rw [hcyclic, Matrix.smul_mul, Matrix.one_mul]

private theorem metzler_trace (B : Matrix (Fin 3) (Fin 3) ℝ)
    (hB : ∀ i j, i ≠ j → 0 ≤ B i j) :
    0 ≤ 3 * Matrix.trace (B * B) - (Matrix.trace B)^2 := by
  have h01 : 0 ≤ B 0 1 * B 1 0 := mul_nonneg (hB 0 1 (by decide)) (hB 1 0 (by decide))
  have h02 : 0 ≤ B 0 2 * B 2 0 := mul_nonneg (hB 0 2 (by decide)) (hB 2 0 (by decide))
  have h12 : 0 ≤ B 1 2 * B 2 1 := mul_nonneg (hB 1 2 (by decide)) (hB 2 1 (by decide))
  have identity : 3 * Matrix.trace (B * B) - (Matrix.trace B)^2 =
      (B 0 0 - B 1 1)^2 + (B 1 1 - B 2 2)^2 + (B 2 2 - B 0 0)^2 +
        6 * (B 0 1 * B 1 0 + B 0 2 * B 2 0 + B 1 2 * B 2 1) := by
    simp only [Matrix.trace_fin_three, Matrix.mul_apply, Fin.sum_univ_three]
    ring
  rw [identity]
  nlinarith [sq_nonneg (B 0 0 - B 1 1), sq_nonneg (B 1 1 - B 2 2),
    sq_nonneg (B 2 2 - B 0 0)]

private theorem obstruction (S : Matrix (Fin 3) (Fin 3) ℂ)
    (B : Matrix (Fin 3) (Fin 3) ℝ) (hS : IsUnit S) (hB : IsMarkovGenerator B)
    (hsim : S⁻¹ * A.map Complex.ofReal * S = B.map Complex.ofReal) : False := by
  have hinv : S * S⁻¹ = 1 :=
    Matrix.mul_nonsing_inv S ((Matrix.isUnit_iff_isUnit_det S).mp hS)
  have htrace : Matrix.trace (B.map Complex.ofReal) =
      Matrix.trace (A.map Complex.ofReal) := by
    rw [← hsim]
    exact Matrix.trace_conj' hS _
  have hsquare : B.map Complex.ofReal * B.map Complex.ofReal =
      S⁻¹ * (A.map Complex.ofReal * A.map Complex.ofReal) * S := by
    rw [← hsim]
    calc
      (S⁻¹ * A.map Complex.ofReal * S) * (S⁻¹ * A.map Complex.ofReal * S) =
          S⁻¹ * A.map Complex.ofReal * (S * S⁻¹) * A.map Complex.ofReal * S := by
            simp only [Matrix.mul_assoc]
      _ = S⁻¹ * (A.map Complex.ofReal * A.map Complex.ofReal) * S := by
        rw [hinv, Matrix.mul_one]
        simp only [Matrix.mul_assoc]
  have htrace2 : Matrix.trace (B.map Complex.ofReal * B.map Complex.ofReal) =
      Matrix.trace (A.map Complex.ofReal * A.map Complex.ofReal) := by
    rw [hsquare]
    exact Matrix.trace_conj' hS _
  have ht : Matrix.trace B = -5/2 := by
    have hr := congrArg Complex.re htrace
    norm_num [Matrix.trace_fin_three, A.eq_1, Matrix.cons_val_two, Matrix.vecHead,
      Matrix.vecTail] at hr ⊢
    exact hr
  have ht2 : Matrix.trace (B * B) = 9/8 := by
    have hr := congrArg Complex.re htrace2
    norm_num [Matrix.trace_fin_three, Matrix.mul_apply, Fin.sum_univ_succ, A.eq_1,
      Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail] at hr ⊢
    exact hr
  have hnonneg := metzler_trace B hB.1
  rw [ht, ht2] at hnonneg
  norm_num at hnonneg

/-- The steady-state block conjecture fails even with real orthogonal symmetry. -/
theorem result : ¬ claim := by
  intro h
  obtain ⟨S, B, hS, hB, hsim⟩ := h 4 L U p generator orthogonal symmetry probability
    stationary 3 V 1 frame (by rw [restriction]; exact invariant)
    (by simpa only [one_smul] using eigenframe) eigenspace contains_stationary
    (by rw [restriction]; exact irreducible)
  rw [restriction] at hsim
  exact obstruction S B hS hB hsim

end
end D5.S3.StatisticalMechanics.SteadyStateBlockMarkovFormRefutation
