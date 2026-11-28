/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/NativeFusion/P48qOppositeVertexInverse
   generality: I
   mirror-B: none(waiver:no-B-plane-mirror-for-source-module)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite inverse BPZ transform for the actual P48q right insertion. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.NativeFusion.P48qOppositeVertex
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeCyclicInvariantSpectrum

/-! The inverse BPZ transform on the physical coefficients of the twisted module. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.NativeFusion

open scoped BigOperators DirectSum
open P48qFixedSourceBPZ (fixedGrade)
open P48qFullEnergySpectrum (totalLZero_exact_eigenvalues)
open P48qNativeConformalSector (fixedStates fixedField fixedOmega sector)
open P48qNativeFixedRightInsertion (rightInsertion sectorTranslation)
open P48qNativeGradingRotation (gradingRotation)
open P48qNativeOppositeVacuum (exponent gradeProjection invertedCoeff)
open P48qFiniteEnergyEigenspaces (totalLZero_eigenspace_finiteDimensional)
open P48qNativeRestrictedDualField (ActualGrade GradeDual RestrictedDual)
open P48qTwistedChargeAction (lattice)
open P48qTwistedStateEnergy (totalLZero)
open SourceBPZ.OriginalSourcePairing (sourcePairing)
open StateField.BorcherdsPermutations (dividedTranslation)
open private fixedGradeInclusion sectorLowering_eq_zero from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeOppositeEvaluation
open private actualGrade_eq_zero_of_lt from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeRestrictedDualField
open private gradingRotation_eigenvector from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeCyclicInvariantSpectrum
open private conformalMode_weight dividedConformal_weight dividedConformalOne_succ_translation
  gradeProjection_eq_zero gradeProjection_self inversionTerm rightInsertionEval
  rightInsertionEval_apply from
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

private def pairedRead (s : Fin 3)
    (J : sector s →ₗ[ℂ] HVertexOperator ℚ ℂ RestrictedDual fixedStates)
    (w : ℝ) (f : GradeDual w) (a : fixedStates) (x : ℚ) : sector s →ₗ[ℂ] ℂ :=
  (((sourcePairing lattice).flip a.val).comp fixedStates.subtype).comp
    ((LinearMap.applyₗ (R := ℂ) (DirectSum.lof ℂ ℝ GradeDual w f)).comp
      ((LinearMap.proj x).comp (HVertexOperator.coeff.comp J)))

/-- Inverse BPZ readout at integral power `m` for an arbitrary opposite coefficient
family. The divided-power sign cancels the weight-dependent phase shift. -/
def inversePairedCoeff (s : Fin 3)
    (J : sector s →ₗ[ℂ] HVertexOperator ℚ ℂ RestrictedDual fixedStates)
    (h : ℤ) (u : sector s) (w : ℝ) (f : GradeDual w) (a : fixedStates) (m : ℤ) : ℂ :=
  (phase h)⁻¹ * ∑ j ∈ Finset.range (cutoff(h)),
    pairedRead s J w f a (exponent h (-m) + (j : ℚ)) (dividedTranslation (L₁ s) j u)

private theorem phase_add_nine (h : ℤ) : (phase (h + 9 : ℤ)) = -(phase h) := by
  rw [show (Real.pi : ℂ) * Complex.I * (((h + 9 : ℤ) : ℂ) / 9) =
      (Real.pi : ℂ) * Complex.I * ((h : ℂ) / 9) + (Real.pi : ℂ) * Complex.I by
        push_cast
        ring, Complex.exp_add, Complex.exp_pi_mul_I, mul_neg_one]

/-- Reverse translation on the finite BPZ inverse of an arbitrary rational
opposite field. At power `m` the integral derivative reads power `m + 1`. -/
theorem inversePairedCoeff_translation (s : Fin 3)
    (J : sector s →ₗ[ℂ] HVertexOperator ℚ ℂ RestrictedDual fixedStates)
    (hJ : ∀ (v : sector s) (x : ℚ), C (J (sectorTranslation s v)) x =
      ((x + 1 : ℚ) : ℂ) • C (J v) (x + 1))
    (h : ℤ) (u : sector s) (hu : totalLZero u.val = ((h : ℂ) / 9) • u.val)
    (w : ℝ) (f : GradeDual w) (a : fixedStates) (m : ℤ) :
    inversePairedCoeff s J (h + 9) (sectorTranslation s u) w f a m =
      ((m + 1 : ℤ) : ℂ) * inversePairedCoeff s J h u w f a (m + 1) := by
  let D := dividedTranslation (L₁ s)
  let T := sectorTranslation s
  let E := pairedRead s J w f a
  let N := cutoff(h)
  let x (j : ℕ) : ℚ := exponent (h + 9) (-m) + (j : ℚ)
  let term (j : ℕ) : ℂ := E (x j + 1) (D j u)
  let translated (j : ℕ) : ℂ := E (x j) (D j (T u))
  let derivative (j : ℕ) : ℂ := ((x j + 1 : ℚ) : ℂ) * term j
  let commutator (j : ℕ) : ℂ := (2 * ((h : ℂ) / 9) - (j : ℂ)) * term j
  have hRead (k : ℚ) (v : sector s) : E k (T v) = ((k + 1 : ℚ) : ℂ) * E (k + 1) v := by
    dsimp only [E, T, pairedRead, LinearMap.comp_apply, LinearMap.applyₗ_apply_apply,
      LinearMap.proj_apply, Submodule.subtype_apply]
    rw [hJ v k, map_smul, Submodule.coe_smul, map_smul, smul_eq_mul]
  have hZero : translated 0 = derivative 0 := by
    simpa only [translated, derivative, term, D, dividedTranslation, pow_zero,
      Module.End.one_apply, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul] using
      hRead (x 0) u
  have hNext (j : ℕ) : x (j + 1) = x j + 1 := by
    simp only [x, Nat.cast_add, Nat.cast_one, add_assoc]
  have hSucc (j : ℕ) : translated (j + 1) = derivative (j + 1) + commutator j := by
    change E (x (j + 1)) (D (j + 1) (T u)) = _
    have hComm : D (j + 1) (T u) = T (D (j + 1) u) +
        (2 * ((h : ℂ) / 9) - (j : ℂ)) • D j u :=
      dividedConformalOne_succ_translation s u ((h : ℂ) / 9) hu j
    rw [hComm, map_add, map_smul, hRead, smul_eq_mul]
    change derivative (j + 1) + _ * E (x (j + 1)) (D j u) = _ + commutator j
    rw [hNext j]
  have hTop : derivative N = 0 := by
    have hz : D N u = 0 := sectorLowering_eq_zero s h u hu N le_rfl
    simp only [derivative, term, hz, map_zero, mul_zero]
  have hSum : (∑ j ∈ Finset.range (N + 1), translated j) =
      ∑ j ∈ Finset.range N, (derivative j + commutator j) := by
    rw [Finset.sum_range_succ' translated, hZero]
    simp only [hSucc, Finset.sum_add_distrib]
    have hShift := Finset.sum_range_succ' derivative N
    rw [Finset.sum_range_succ derivative N, hTop, add_zero] at hShift
    rw [hShift]
    abel
  have hWeight : totalLZero (T u).val = (((h + 9 : ℤ) : ℂ) / 9) • (T u).val := by
    have hw := conformalMode_weight s (-1) u ((h : ℂ) / 9) hu
    change totalLZero (T u).val = _ • (T u).val at hw
    convert hw using 2
    push_cast
    ring
  have hCut : cutoff(h + 9) ≤ N + 1 := by
    dsimp only [N]
    omega
  have hExtend : (∑ j ∈ Finset.range (cutoff(h + 9)), translated j) =
      ∑ j ∈ Finset.range (N + 1), translated j := by
    apply Finset.sum_subset (Finset.range_mono hCut)
    intro j _ hj
    have hj' : cutoff(h + 9) ≤ j := Nat.le_of_not_lt (hj ∘ Finset.mem_range.mpr)
    have hz : D j (T u) = 0 := sectorLowering_eq_zero s (h + 9) (T u) hWeight j hj'
    simp only [translated, hz, map_zero]
  have hCombine (j : ℕ) : derivative j + commutator j =
      -((m + 1 : ℤ) : ℂ) * term j := by
    dsimp only [derivative, commutator]
    rw [← add_mul]
    congr 1
    simp only [x, exponent, Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div,
      Rat.cast_intCast, Rat.cast_natCast, Rat.cast_ofNat, Rat.cast_one]
    push_cast
    ring
  have hPower (j : ℕ) : exponent h (-(m + 1)) + (j : ℚ) = x j + 1 := by
    dsimp only [x, exponent]
    push_cast
    ring
  unfold inversePairedCoeff
  change (phase (h + 9 : ℤ))⁻¹ * (∑ j ∈ Finset.range (cutoff(h + 9)), translated j) = _
  rw [phase_add_nine, inv_neg, hExtend, hSum]
  simp_rw [hCombine, hPower]
  rw [← Finset.mul_sum]
  change -(phase h)⁻¹ * (-((m + 1 : ℤ) : ℂ) * ∑ j ∈ Finset.range N, term j) =
    ((m + 1 : ℤ) : ℂ) * ((phase h)⁻¹ * ∑ j ∈ Finset.range N, term j)
  ring

private theorem inverse_phase (h : ℤ) (j : ℕ) :
    (-1 : ℂ) ^ j * (phase (h - 9 * (j : ℤ) : ℤ))⁻¹ = (phase h)⁻¹ := by
  induction j with
  | zero => simp
  | succ j ih =>
    have he : (h - 9 * ((j + 1 : ℕ) : ℤ) : ℤ) + 9 = h - 9 * (j : ℤ) := by omega
    have hphase := phase_add_nine (h - 9 * ((j + 1 : ℕ) : ℤ))
    rw [he] at hphase
    rw [pow_succ, mul_assoc, neg_one_mul, ← inv_neg, ← hphase, ih]

private theorem inverse_exponent (h m : ℤ) (j : ℕ) :
    exponent (h - 9 * (j : ℤ)) (-m - (j : ℤ)) = exponent h (-m) + (j : ℚ) := by
  simp only [exponent, Int.cast_sub, Int.cast_neg, Int.cast_mul, Int.cast_natCast, Int.cast_ofNat]
  ring

/-- The readout specializes to the same finite inverse on the native BPZ field. -/
theorem inversePairedCoeff_oppositeVertex (s : Fin 3) (h : ℤ) (u : sector s)
    (hu : totalLZero u.val = ((h : ℂ) / 9) • u.val) (w : ℝ) (f : GradeDual w)
    (d : ℤ) (a : fixedGrade d) (m : ℤ) :
    inversePairedCoeff s (oppositeVertex s) h u w f (fixedGradeInclusion d a) m =
      f (gradeProjection (w : ℂ) ((rightInsertion s u (fixedGradeInclusion d a)).coeff m).val) := by
  rw [← oppositeVertex_inverse s h u hu w f d a m, inversePairedCoeff, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [inverse_phase h j, inverse_exponent h m j]
  rfl

/-- The inverse on one actual output energy grade represents its paired coefficient
by a state in that finite-dimensional eigenspace. -/
def inverseGradeCoeff (s : Fin 3)
    (J : sector s →ₗ[ℂ] HVertexOperator ℚ ℂ RestrictedDual fixedStates)
    (h : ℤ) (u : sector s) (w : ℝ) (a : fixedStates) (m : ℤ) : ActualGrade w :=
  letI := totalLZero_eigenspace_finiteDimensional (w : ℂ)
  let pairing := ((sourcePairing lattice).flip a.val).comp fixedStates.subtype
  (Module.evalEquiv ℂ (ActualGrade w)).symm ((phase h)⁻¹ •
    ∑ j ∈ Finset.range (cutoff(h)),
      pairing.comp ((C (J (dividedTranslation (L₁ s) j u)) (exponent h (-m) + (j : ℚ))).comp
        (DirectSum.lof ℂ ℝ GradeDual w)))

/-- Evaluation against the actual grade dual reads the finite inverse sum. -/
theorem inverseGradeCoeff_pairing (s : Fin 3)
    (J : sector s →ₗ[ℂ] HVertexOperator ℚ ℂ RestrictedDual fixedStates)
    (h : ℤ) (u : sector s) (w : ℝ) (f : GradeDual w) (a : fixedStates) (m : ℤ) :
    f (inverseGradeCoeff s J h u w a m) = inversePairedCoeff s J h u w f a m := by
  unfold inverseGradeCoeff inversePairedCoeff
  rw [Module.apply_evalEquiv_symm_apply, LinearMap.smul_apply, LinearMap.sum_apply, smul_eq_mul]
  rfl

set_option maxHeartbeats 800000 in
-- Evaluation coerces through a finite-dimensional eigenspace and its dual.
/-- Reverse translation as an equality of actual twisted states in each output grade. -/
theorem inverseGradeCoeff_translation (s : Fin 3)
    (J : sector s →ₗ[ℂ] HVertexOperator ℚ ℂ RestrictedDual fixedStates)
    (hJ : ∀ (v : sector s) (x : ℚ), C (J (sectorTranslation s v)) x =
      ((x + 1 : ℚ) : ℂ) • C (J v) (x + 1))
    (h : ℤ) (u : sector s) (hu : totalLZero u.val = ((h : ℂ) / 9) • u.val)
    (w : ℝ) (a : fixedStates) (m : ℤ) :
    inverseGradeCoeff s J (h + 9) (sectorTranslation s u) w a m =
      ((m + 1 : ℤ) : ℂ) • inverseGradeCoeff s J h u w a (m + 1) := by
  let _ := totalLZero_eigenspace_finiteDimensional (w : ℂ)
  refine (Module.evalEquiv ℂ (ActualGrade w)).injective (LinearMap.ext fun f => ?_)
  simp only [Module.evalEquiv_apply, Module.Dual.eval_apply, map_smul, LinearMap.smul_apply,
    smul_eq_mul, inverseGradeCoeff_pairing]
  exact inversePairedCoeff_translation s J hJ h u hu w f a m

/-- Grade covariance makes the inverse of a homogeneous pair an actual right
coefficient. The state at energy `h/9 + d + m` represents all restricted-dual
reads, including those on other grades. -/
theorem inverseGradeCoeff_all_grades (s : Fin 3)
    (J : sector s →ₗ[ℂ] HVertexOperator ℚ ℂ RestrictedDual fixedStates)
    (hJ : ∀ (e : ℤ) (v : sector s), totalLZero v.val = ((e : ℂ) / 9) • v.val →
      ∀ (w : ℝ) (f : GradeDual w) (d k : ℤ) (a : fixedGrade d),
        (w : ℂ) ≠ (e : ℂ) / 9 + (d : ℂ) - (k : ℂ) →
          sourcePairing lattice
            (C (J v) (exponent e k) (DirectSum.lof ℂ ℝ GradeDual w f)).val a.val = 0)
    (h : ℤ) (u : sector s) (hu : totalLZero u.val = ((h : ℂ) / 9) • u.val)
    (d : ℤ) (a : fixedGrade d) (m : ℤ) (w : ℝ) (f : GradeDual w) :
    let W : ℝ := (h : ℝ) / 9 + (d : ℝ) + (m : ℝ)
    f (gradeProjection (w : ℂ) (inverseGradeCoeff s J h u W (fixedGradeInclusion d a) m).val) =
      inversePairedCoeff s J h u w f (fixedGradeInclusion d a) m := by
  intro W
  by_cases hw : w = W
  · subst w
    rw [gradeProjection_self, inverseGradeCoeff_pairing]
  · have hne : (w : ℂ) ≠ (W : ℂ) := fun he => hw (Complex.ofReal_injective he)
    have hW : (W : ℂ) = (h : ℂ) / 9 + (d : ℂ) + (m : ℂ) := by
      simp only [W, Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_intCast,
        Complex.ofReal_ofNat]
    let v := inverseGradeCoeff s J h u W (fixedGradeInclusion d a) m
    have hv := Module.End.mem_eigenspace_iff.mp v.property
    change f (gradeProjection (w : ℂ) v.val) = _
    rw [gradeProjection_eq_zero hv hne, map_zero, inversePairedCoeff]
    symm
    apply mul_eq_zero_of_right
    apply Finset.sum_eq_zero
    intro j _
    have hOff : (w : ℂ) ≠ ((h - 9 * (j : ℤ) : ℤ) : ℂ) / 9 + (d : ℂ) -
        ((-m - (j : ℤ) : ℤ) : ℂ) := by
      intro he
      apply hne
      rw [hW]
      push_cast at he
      linear_combination he
    change sourcePairing lattice
      (C (J (dividedTranslation (L₁ s) j u)) (exponent h (-m) + (j : ℚ))
        (DirectSum.lof ℂ ℝ GradeDual w f)).val a.val = 0
    rw [← inverse_exponent h m j]
    exact hJ _ _ (divided_weight s h u hu j) w f d _ a hOff

private theorem inverseGradeCoeff_mem_sector (s : Fin 3)
    (J : sector s →ₗ[ℂ] HVertexOperator ℚ ℂ RestrictedDual fixedStates)
    (h : ℤ) (u : sector s) (hu : totalLZero u.val = ((h : ℂ) / 9) • u.val)
    (a : fixedStates) (m l : ℤ) :
    let w : ℝ := (h : ℝ) / 9 + (l : ℝ)
    (inverseGradeCoeff s J h u w a m).val ∈ sector s := by
  intro w
  let v := inverseGradeCoeff s J h u w a m
  change v.val ∈ sector s
  by_cases hv : v.val = 0
  · rw [hv]
    exact (sector s).zero_mem
  have hu0 : u.val ≠ 0 := by
    intro hz
    have hzero : u = 0 := Subtype.ext hz
    apply hv
    have hv0 : v = 0 := by
      let _ := totalLZero_eigenspace_finiteDimensional (w : ℂ)
      refine (Module.evalEquiv ℂ (ActualGrade w)).injective (LinearMap.ext fun f => ?_)
      change f (inverseGradeCoeff s J h u w a m) = f 0
      simp only [inverseGradeCoeff_pairing, hzero, inversePairedCoeff, map_zero,
        Finset.sum_const_zero, mul_zero]
    exact congrArg Subtype.val hv0
  have hvWeight := Module.End.mem_eigenspace_iff.mp v.property
  obtain ⟨i, hi⟩ := (totalLZero_exact_eigenvalues _).mp ⟨u.val, hu0, hu⟩
  obtain ⟨j, hj⟩ := (totalLZero_exact_eigenvalues _).mp ⟨v.val, hv, hvWeight⟩
  have hw : (w : ℂ) = (h : ℂ) / 9 + (l : ℂ) := by
    simp only [w, Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_intCast,
      Complex.ofReal_ofNat]
  have hindex : (j : ℤ) = (i : ℤ) + 3 * l := by
    have hc : (j : ℂ) = (i : ℂ) + 3 * (l : ℂ) := by
      linear_combination 3 * (hi + hw - hj)
    exact_mod_cast hc
  have hmod : j % 3 = i % 3 := by omega
  let ζ : ℂ := ThirdTwistedChargeCocycle.zeta
  have hcube : ζ ^ (3 : ℕ) = 1 :=
    (IsPrimitiveRoot.coe_units_iff.mpr ThirdTwistedChargeCocycle.zeta_primitive).pow_eq_one
  have hpow : ζ ^ j = ζ ^ i := (pow_eq_pow_mod j hcube).trans
    ((congrArg (ζ ^ ·) hmod).trans (pow_eq_pow_mod i hcube).symm)
  have hu' : totalLZero u.val = (16 / 9 + (i : ℂ) / 3) • u.val := hi ▸ hu
  have hv' : totalLZero v.val = (16 / 9 + (j : ℂ) / 3) • v.val := hj ▸ hvWeight
  have hrot := gradingRotation_eigenvector u.val i hu'
  have huSector := Module.End.mem_eigenspace_iff.mp u.property
  have hphase : ζ ^ i = ζ ^ s.val := smul_left_injective ℂ hu0 (hrot.symm.trans huSector)
  apply Module.End.mem_eigenspace_iff.mpr
  change gradingRotation v.val = ζ ^ s.val • v.val
  rw [gradingRotation_eigenvector v.val j hv', hpow, hphase]

/-- The actual integral right mode on homogeneous inputs, with output in the
same rotation sector and at energy `h/9 + d - n - 1`. -/
def inverseHomogeneousRightMode (s : Fin 3)
    (J : sector s →ₗ[ℂ] HVertexOperator ℚ ℂ RestrictedDual fixedStates)
    (h : ℤ) (u : sector s) (hu : totalLZero u.val = ((h : ℂ) / 9) • u.val)
    (d : ℤ) (a : fixedGrade d) (n : ℤ) : sector s :=
  let w : ℝ := (h : ℝ) / 9 + ((d + (-n - 1) : ℤ) : ℝ)
  ⟨(inverseGradeCoeff s J h u w (fixedGradeInclusion d a) (-n - 1)).val,
    inverseGradeCoeff_mem_sector s J h u hu (fixedGradeInclusion d a) (-n - 1) _⟩

/-- Below the native ground energy the reconstructed coefficient vanishes. -/
theorem inverseGradeCoeff_eq_zero_below_ground (s : Fin 3)
    (J : sector s →ₗ[ℂ] HVertexOperator ℚ ℂ RestrictedDual fixedStates)
    (h : ℤ) (u : sector s) (a : fixedStates) (m : ℤ) (w : ℝ) (hw : w < 16 / 9) :
    inverseGradeCoeff s J h u w a m = 0 :=
  actualGrade_eq_zero_of_lt hw (inverseGradeCoeff s J h u w a m)

#print axioms invertedCoeff_inverse
#print axioms oppositeVertex_inverse
#print axioms inversePairedCoeff_translation
#print axioms inversePairedCoeff_oppositeVertex
#print axioms inverseGradeCoeff_translation
#print axioms inverseGradeCoeff_all_grades
#print axioms inverseHomogeneousRightMode
#print axioms inverseGradeCoeff_eq_zero_below_ground

end
end D5.S3.VertexAlgebra.Lattice.Orbifold.NativeFusion
