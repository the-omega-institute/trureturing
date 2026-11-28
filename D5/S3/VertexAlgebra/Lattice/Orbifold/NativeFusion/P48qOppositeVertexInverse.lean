/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/NativeFusion/P48qOppositeVertexInverse
   generality: I
   mirror-B: none(waiver:no-B-plane-mirror-for-source-module)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite inverse BPZ transform for the actual P48q right insertion. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.NativeFusion.P48qOppositeVertex

/-! The inverse BPZ transform on the physical coefficients of the twisted module. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.NativeFusion

open scoped BigOperators DirectSum
open P48qFixedSourceBPZ (fixedGrade)
open P48qNativeConformalSector (fixedStates fixedField fixedOmega sector)
open P48qNativeFixedRightInsertion (rightInsertion)
open P48qNativeOppositeVacuum (exponent gradeProjection invertedCoeff)
open P48qNativeRestrictedDualField (GradeDual)
open P48qTwistedChargeAction (lattice)
open P48qTwistedStateEnergy (totalLZero)
open SourceBPZ.OriginalSourcePairing (sourcePairing)
open StateField.BorcherdsPermutations (dividedTranslation)
open private fixedGradeInclusion from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeOppositeEvaluation
open private dividedConformal_weight inversionTerm
  rightInsertionEval rightInsertionEval_apply from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeOppositeVacuum

noncomputable section

local notation "C" => HVertexOperator.coeff
local notation "L₁" s => C (fixedField s fixedOmega) (-3)
local notation "cutoff(" h ")" => (Int.toNat ((h - 16) / 9) + 1)
local notation "phase" h => Complex.exp ((Real.pi : ℂ) * Complex.I * ((h : ℂ) / 9))

private theorem divided_comp {V : Type*} [AddCommGroup V] [Module ℂ V]
    (L : Module.End ℂ V) (j l : ℕ) (v : V) :
    dividedTranslation L l (dividedTranslation L j v) =
      ((j + l).choose j : ℂ) • dividedTranslation L (j + l) v := by
  have hFactorial : ((j + l).choose j : ℂ) * (l.factorial : ℂ) * (j.factorial : ℂ) =
      ((j + l).factorial : ℂ) := by
    exact_mod_cast (Nat.add_comm l j ▸ Nat.add_choose_mul_factorial_mul_factorial l j)
  have hScalar : (j.factorial : ℂ)⁻¹ * (l.factorial : ℂ)⁻¹ =
      ((j + l).choose j : ℂ) * ((j + l).factorial : ℂ)⁻¹ := by
    field_simp [Nat.factorial_ne_zero]
    linear_combination -hFactorial
  simp only [dividedTranslation, LinearMap.smul_apply, map_smul, smul_smul, hScalar]
  rw [← Module.End.mul_apply, ← pow_add, add_comm l j]

private theorem signed_choose_sum (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1), (-1 : ℂ) ^ j * (n.choose j : ℂ)) =
      if n = 0 then 1 else 0 := by
  by_cases h : n = 0
  · subst n
    simp
  · rw [ite_eq_right h]
    exact_mod_cast Int.alternating_sum_range_choose_of_ne h

private theorem divided_weight (s : Fin 3) (h : ℤ) (u : sector s)
    (hu : totalLZero u.val = ((h : ℂ) / 9) • u.val) (j : ℕ) :
    totalLZero (dividedTranslation (L₁ s) j u).val =
      (((h - 9 * (j : ℤ) : ℤ) : ℂ) / 9) • (dividedTranslation (L₁ s) j u).val := by
  have hMode : C (fixedField s fixedOmega) (-(1 : ℤ) - 2) = L₁ s := rfl
  have he := dividedConformal_weight s 1 u ((h : ℂ) / 9) hu j
  rw [hMode, Int.cast_one, mul_one] at he
  rw [he]
  congr 1
  push_cast
  ring

/-- The finite transforms on the paired right modes are inverse.
The shifted coefficient indices add the two divided-power degrees, so the
signed binomial sum cancels each positive total degree. -/
theorem invertedCoeff_inverse (s : Fin 3) (h : ℤ) (u : sector s)
    (w : ℂ) (f : Module.Dual ℂ (totalLZero.eigenspace w)) (a : fixedStates) (m : ℤ) :
    (∑ j ∈ Finset.range (cutoff(h)),
      ((-1 : ℂ) ^ j * (phase (h - 9 * (j : ℤ) : ℤ))⁻¹) *
        invertedCoeff s (h - 9 * (j : ℤ)) w (dividedTranslation (L₁ s) j u)
          f a (-m - (j : ℤ))) =
      f (gradeProjection w ((rightInsertion s u a).coeff m).val) := by
  let N := cutoff(h)
  let D := dividedTranslation (L₁ s)
  let R := rightInsertionEval s w f a
  let row (j l : ℕ) := (-1 : ℂ) ^ j * ((j + l).choose j : ℂ) *
    R (m + ((j + l : ℕ) : ℤ)) (D (j + l) u)
  have hcut (j : ℕ) (hj : j < N) : cutoff(h - 9 * (j : ℤ)) = N - j := by
    rcases j with _ | j
    · simp [N]
    dsimp only [N] at hj ⊢
    omega
  have hrow (j l : ℕ) :
      (-1 : ℂ) ^ j * inversionTerm s w (D j u) f a (-m - (j : ℤ)) l = row j l := by
    unfold row inversionTerm
    change _ * f (gradeProjection w ((rightInsertion s (D l (D j u)) a).coeff _).val) = _
    rw [← rightInsertionEval_apply, divided_comp (L₁ s), map_smul, smul_eq_mul, mul_assoc,
      show (l : ℤ) - (-m - (j : ℤ)) = m + ((j + l : ℕ) : ℤ) by omega]
  calc
    _ = ∑ j ∈ Finset.range N, ∑ l ∈ Finset.range (N - j), row j l := by
      apply Finset.sum_congr rfl
      intro j hj
      have hphase := Complex.exp_ne_zero
        ((Real.pi : ℂ) * Complex.I * (((h - 9 * (j : ℤ) : ℤ) : ℂ) / 9))
      rw [invertedCoeff, ← mul_assoc, inv_mul_cancel_right₀ hphase,
        hcut j (Finset.mem_range.mp hj), Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => hrow j l
    _ = ∑ n ∈ Finset.range N, ∑ j ∈ Finset.range (n + 1), row j (n - j) :=
      (Finset.sum_range_diag_flip N row).symm
    _ = ∑ n ∈ Finset.range N, if n = 0 then R m u else 0 := by
      apply Finset.sum_congr rfl
      intro n _
      calc
        _ = (∑ j ∈ Finset.range (n + 1), (-1 : ℂ) ^ j * (n.choose j : ℂ)) *
            R (m + (n : ℤ)) (D n u) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro j hj
          simp only [row, Nat.add_sub_of_le (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))]
        _ = _ := by
          rw [signed_choose_sum]
          split <;> rename_i hn
          · subst n
            simp [D, dividedTranslation]
          · rw [zero_mul]
    _ = _ := by
      rw [Finset.sum_eq_single 0]
      · rw [ite_eq_left rfl]
        exact rightInsertionEval_apply s w f a m u
      · intro b _ hb
        exact ite_eq_right hb
      · simp [N]

/-- The finite inverse uses only physical coefficients of the actual opposite
vertex, paired against the given fixed test state. -/
theorem oppositeVertex_inverse (s : Fin 3) (h : ℤ) (u : sector s)
    (hu : totalLZero u.val = ((h : ℂ) / 9) • u.val) (w : ℝ) (f : GradeDual w)
    (d : ℤ) (a : fixedGrade d) (m : ℤ) :
    (∑ j ∈ Finset.range (cutoff(h)),
      ((-1 : ℂ) ^ j * (phase (h - 9 * (j : ℤ) : ℤ))⁻¹) *
        sourcePairing lattice
          (C (oppositeVertex s (dividedTranslation (L₁ s) j u))
            (exponent (h - 9 * (j : ℤ)) (-m - (j : ℤ)))
            (DirectSum.lof ℂ ℝ GradeDual w f)).val a.val) =
      f (gradeProjection (w : ℂ) ((rightInsertion s u (fixedGradeInclusion d a)).coeff m).val) := by
  rw [← invertedCoeff_inverse s h u (w : ℂ) f (fixedGradeInclusion d a) m]
  apply Finset.sum_congr rfl
  intro j _
  rw [oppositeVertex_coeff_pairing_on_grade s _ _ (divided_weight s h u hu j) w f _ d a]

#print axioms invertedCoeff_inverse
#print axioms oppositeVertex_inverse

end
end D5.S3.VertexAlgebra.Lattice.Orbifold.NativeFusion
