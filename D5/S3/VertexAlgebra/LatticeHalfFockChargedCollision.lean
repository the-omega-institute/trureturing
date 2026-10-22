/- GID: D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockChargedCollision
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite balance and all-order charged source coefficient comparisons. -/

import D5.S3.VertexAlgebra.LatticeHalfFockChargedCollision.Current

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeHalfFockChargedCollision

open LatticeGeneratingFieldLocality LatticeHalfFockChargedCoefficients
  LatticeHalfFockChargedTensorCoefficients LatticeHalfFockCorrectedField
open LatticeHalfFockFockNormalField LatticeHalfFockFiniteCorrection
open MvPolynomial
open scoped BigOperators TensorProduct VertexOperator

noncomputable section

/- Finite oscillator sum balance from the scalar recurrence.
   Expand collision_expansion/diagonal_as_sum, put
     L=e+Qa+2(N+1)+d0+d1, n=L-m, A=m-d0-Qs.
   All j terms have the same L, because j<=N.
   The scalar balance is
     (e+2)/2-(n-d1)/2+Qt/2 = A/2-N-B.
   If L<0 every term is zero. Otherwise interchange only the two finite
   sums j<=N and 0<=m<=L, apply scalarStep at each (d,m), distribute.
   This obligation contains neither correctedField nor singletonLinear. -/
private theorem collision_finite_balance (D : LatticeData) (sigma tau : Charge D)
    (N : ℕ) (e : ℤ) (p : Oscillator D)
    (scalarStep : ∀ (A B : ℤ) (k : ℕ),
      (k + 1 : ℂ) * collisionScalar A B (k + 1) =
        ((A : ℂ) / 2 - (k : ℂ) - (B : ℂ)) * collisionScalar A B k +
          ((B : ℂ) / 2) * ∑ j ∈ Finset.range (k + 1),
            collisionR j * collisionScalar A B (k - j)) :
    (N + 1 : ℂ) • collisionOscillator D sigma tau (N + 1) e p =
      (((e + 2 : ℤ) : ℂ) / 2) • collisionOscillator D sigma tau N (e + 2) p -
      collisionMoment D sigma tau N e p +
      ((chargeNorm D tau : ℂ) / 2) • collisionOscillator D sigma tau N (e + 2) p +
      ((bilinear D sigma tau : ℂ) / 2) •
        ∑ j ∈ Finset.range (N + 1), collisionR j •
          collisionOscillator D sigma tau (N - j) (e + 2 * ((j : ℤ) + 1)) p := by
  classical
  have addLeft (a b c : Charge D) : bilinear D (a + b) c =
      bilinear D a c + bilinear D b c := by
    simp [bilinear, add_mul, Finset.sum_add_distrib]
  have addRight (a b c : Charge D) : bilinear D a (b + c) =
      bilinear D a b + bilinear D a c := by
    simp [bilinear, mul_add, Finset.sum_add_distrib]
  have normAdd : chargeNorm D (sigma + tau) =
      chargeNorm D sigma + chargeNorm D tau + 2 * bilinear D sigma tau := by
    unfold chargeNorm
    rw [addLeft, addRight, addRight,
      LatticeFiniteNegativeGeneration.bilinear_symmetric D tau sigma]
    ring
  let T := LatticeHalfFockProductKernel.pairTranslation D sigma tau p
  let total (d : Fin 2 →₀ ℕ) : ℤ :=
    e + chargeNorm D (sigma + tau) + 2 * ((N + 1 : ℕ) : ℤ) + d 0 + d 1
  let moment (d : Fin 2 →₀ ℕ) : Oscillator D :=
    if total d < 0 then 0 else
      ∑ m ∈ Finset.range ((total d).toNat + 1),
        ((((total d - (m : ℤ) - (d 1 : ℤ)) : ℤ) : ℂ) / 2) •
          diagonalTerm D sigma tau N (total d) (d 0) m
  have nowTotal (d : Fin 2 →₀ ℕ) :
      e + 2 + chargeNorm D (sigma + tau) + 2 * (N : ℤ) + d 0 + d 1 =
        total d := by
    dsimp [total]
    push_cast
    ring
  have shiftedTotal (d : Fin 2 →₀ ℕ) (j : ℕ) (within : j ≤ N) :
      e + 2 * ((j : ℤ) + 1) + chargeNorm D (sigma + tau) +
        2 * ((N - j : ℕ) : ℤ) + d 0 + d 1 = total d := by
    dsimp [total]
    omega
  have expand (k : ℕ) (z : ℤ) : collisionOscillator D sigma tau k z p =
      ∑ d ∈ T.support, T.coeff d * collisionDiagonal D sigma tau k z d := by
    rw [collision_expansion]
    simp_rw [diagonal_as_sum]
    rfl
  have momentExpansion : collisionMoment D sigma tau N e p =
      ∑ d ∈ T.support, T.coeff d * moment d := by
    unfold collisionMoment
    apply Finset.sum_congr rfl
    intro d member
    dsimp only [moment]
    rw [nowTotal]
  have diagonalBalance (d : Fin 2 →₀ ℕ) :
      (N + 1 : ℂ) • collisionDiagonal D sigma tau (N + 1) e d =
        (((e + 2 : ℤ) : ℂ) / 2) • collisionDiagonal D sigma tau N (e + 2) d -
          moment d +
        ((chargeNorm D tau : ℂ) / 2) • collisionDiagonal D sigma tau N (e + 2) d +
        ((bilinear D sigma tau : ℂ) / 2) •
          ∑ j ∈ Finset.range (N + 1), collisionR j •
            collisionDiagonal D sigma tau (N - j) (e + 2 * ((j : ℤ) + 1)) d := by
    have now : collisionDiagonal D sigma tau N (e + 2) d =
        if total d < 0 then 0 else
          ∑ m ∈ Finset.range ((total d).toNat + 1),
            diagonalTerm D sigma tau N (total d) (d 0) m := by
      simp only [collisionDiagonal, nowTotal]
    have next : collisionDiagonal D sigma tau (N + 1) e d =
        if total d < 0 then 0 else
          ∑ m ∈ Finset.range ((total d).toNat + 1),
            diagonalTerm D sigma tau (N + 1) (total d) (d 0) m := rfl
    have shifted (j : ℕ) (member : j ∈ Finset.range (N + 1)) :
        collisionDiagonal D sigma tau (N - j) (e + 2 * ((j : ℤ) + 1)) d =
          if total d < 0 then 0 else
            ∑ m ∈ Finset.range ((total d).toNat + 1),
              diagonalTerm D sigma tau (N - j) (total d) (d 0) m := by
      simp only [collisionDiagonal, shiftedTotal d j (by
        have bound := Finset.mem_range.mp member
        omega)]
    rw [next, now]
    have shiftedSum :
        (∑ j ∈ Finset.range (N + 1), collisionR j •
          collisionDiagonal D sigma tau (N - j) (e + 2 * ((j : ℤ) + 1)) d) =
        ∑ j ∈ Finset.range (N + 1), collisionR j •
          (if total d < 0 then 0 else
            ∑ m ∈ Finset.range ((total d).toNat + 1),
              diagonalTerm D sigma tau (N - j) (total d) (d 0) m) := by
      apply Finset.sum_congr rfl
      intro j member
      rw [shifted j member]
    rw [shiftedSum]
    dsimp only [moment]
    by_cases negative : total d < 0
    · simp only [if_pos negative, smul_zero, sub_zero, add_zero,
        Finset.sum_const_zero]
    · simp only [if_neg negative]
      have swap :
          (∑ j ∈ Finset.range (N + 1), collisionR j •
            ∑ m ∈ Finset.range ((total d).toNat + 1),
              diagonalTerm D sigma tau (N - j) (total d) (d 0) m) =
          ∑ m ∈ Finset.range ((total d).toNat + 1),
            ∑ j ∈ Finset.range (N + 1), collisionR j •
              diagonalTerm D sigma tau (N - j) (total d) (d 0) m := by
        simp_rw [Finset.smul_sum]
        rw [Finset.sum_comm]
      rw [swap]
      simp_rw [Finset.smul_sum]
      rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib,
        ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro m member
      let A : ℤ := (m : ℤ) - (d 0 : ℤ) - chargeNorm D sigma
      have balance :
          (((e + 2 : ℤ) : ℂ) / 2) -
              (((total d - (m : ℤ) - (d 1 : ℤ) : ℤ) : ℂ) / 2) +
              ((chargeNorm D tau : ℂ) / 2) =
            (A : ℂ) / 2 - (N : ℂ) - (bilinear D sigma tau : ℂ) := by
        dsimp only [A, total]
        rw [normAdd]
        push_cast
        ring
      have coefficient := scalarStep A (bilinear D sigma tau) N
      rw [← balance] at coefficient
      have scalarIdentity := congrArg
        (fun c : ℂ => c • (halfCreationCoeff D sigma (m : ℤ) *
          halfCreationCoeff D tau (total d - (m : ℤ)))) coefficient
      dsimp [A, diagonalTerm] at scalarIdentity ⊢
      rw [smul_smul, smul_smul, smul_smul]
      simp_rw [smul_smul]
      rw [← Finset.sum_smul, ← sub_smul, ← add_smul, ← add_smul]
      convert scalarIdentity using 1
      congr 1
      rw [Finset.mul_sum]
      ring
  have weightedBalance (d : Fin 2 →₀ ℕ) :
      (N + 1 : ℂ) • (T.coeff d * collisionDiagonal D sigma tau (N + 1) e d) =
        (((e + 2 : ℤ) : ℂ) / 2) •
            (T.coeff d * collisionDiagonal D sigma tau N (e + 2) d) -
          T.coeff d * moment d +
        ((chargeNorm D tau : ℂ) / 2) •
          (T.coeff d * collisionDiagonal D sigma tau N (e + 2) d) +
        ((bilinear D sigma tau : ℂ) / 2) •
          ∑ j ∈ Finset.range (N + 1), collisionR j •
            (T.coeff d *
              collisionDiagonal D sigma tau (N - j) (e + 2 * ((j : ℤ) + 1)) d) := by
    have mul_smul (c : ℂ) (q : Oscillator D) :
        T.coeff d * (c • q) = c • (T.coeff d * q) :=
      Algebra.mul_smul_comm c (T.coeff d) q
    have weighted := congrArg (fun q : Oscillator D => T.coeff d * q) (diagonalBalance d)
    simp_rw [mul_smul] at weighted
    simp only [mul_add, mul_sub] at weighted
    simp only [Finset.mul_sum, mul_smul] at weighted
    simpa only [Algebra.smul_mul_assoc, mul_assoc, mul_add, Int.cast_add,
      Int.cast_one] using weighted
  simp_rw [expand]
  rw [momentExpansion]
  have swap :
      (∑ j ∈ Finset.range (N + 1), collisionR j •
        ∑ d ∈ T.support, T.coeff d *
          collisionDiagonal D sigma tau (N - j) (e + 2 * ((j : ℤ) + 1)) d) =
      ∑ d ∈ T.support, ∑ j ∈ Finset.range (N + 1), collisionR j •
        (T.coeff d *
          collisionDiagonal D sigma tau (N - j) (e + 2 * ((j : ℤ) + 1)) d) := by
    simp_rw [Finset.smul_sum]
    rw [Finset.sum_comm]
  rw [swap]
  simp_rw [Finset.smul_sum]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d member
  simpa only [Finset.smul_sum] using weightedBalance d

private theorem collision_closed_recurrence (D : LatticeData) (hu : IsUnit D.G.det)
    (sigma tau : Charge D) (N : ℕ) (e : ℤ) (x : ActualTensor D hu) :
    (N + 1 : ℂ) • collisionCoefficient D hu sigma tau (N + 1) e x =
      (((e + 2 : ℤ) : ℂ) / 2) • collisionCoefficient D hu sigma tau N (e + 2) x -
      (normalCurrent D hu tau (collisionField D hu sigma tau N)).coeff e x +
      ((chargeNorm D tau : ℂ) / 2) • collisionCoefficient D hu sigma tau N (e + 2) x +
      ((bilinear D sigma tau : ℂ) / 2) •
        ∑ j ∈ Finset.range (N + 1), collisionR j •
          collisionCoefficient D hu sigma tau (N - j) (e + 2 * ((j : ℤ) + 1)) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul p g =>
    rw [collision_normal_moment]
    have balance := congrArg
      (fun q : Oscillator D => chargeScalar D (sigma + tau) •
        (q ⊗ₜ[ℂ] groundAction D hu (sigma + tau) g))
      (collision_finite_balance D sigma tau N e p collisionScalar_recurrence)
    simp only [collisionCoefficient, LinearMap.smul_apply, TensorProduct.map_tmul,
      TensorProduct.add_tmul, TensorProduct.sub_tmul, TensorProduct.smul_tmul',
      TensorProduct.sum_tmul, smul_add, smul_sub, Finset.smul_sum,
      smul_smul, mul_comm, mul_left_comm, mul_assoc] at balance ⊢
    simpa only [smul_smul, mul_comm, mul_left_comm, mul_assoc] using balance
  | add x y hx hy =>
    simp only [map_add, smul_add, Finset.sum_add_distrib] at hx hy ⊢
    linear_combination hx + hy

private theorem collision_scalar_zero (A B : ℤ) : collisionScalar A B 0 = 1 := by
  have constantUnit :
      Units.map PowerSeries.constantCoeff.toMonoidHom collisionUnit = 1 := by
    apply Units.ext
    change PowerSeries.constantCoeff (collisionUnit : PowerSeries ℂ) = 1
    unfold collisionUnit
    rw [IsUnit.unit_spec]
    rw [PowerSeries.constantCoeff_smul, map_add,
      PowerSeries.binomialSeries_constantCoeff, map_one]
    norm_num
  have constantPower : PowerSeries.constantCoeff
      (((collisionUnit ^ (-2 * B) : (PowerSeries ℂ)ˣ)) : PowerSeries ℂ) = 1 := by
    change (((Units.map PowerSeries.constantCoeff.toMonoidHom
      (collisionUnit ^ (-2 * B))) : ℂˣ) : ℂ) = 1
    rw [MonoidHom.map_zpow, constantUnit, one_zpow]
    rfl
  unfold collisionScalar
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
  rw [map_mul, constantPower, mul_one]
  rw [PowerSeries.binomialSeries_constantCoeff]

/- Charge addition for the actual half creation series. This coefficient
   induction uses only the public differential equation and constant term.
   Each product coefficient is its finite natural antidiagonal. -/
private theorem half_creation_exponential_add (D : LatticeData) (sigma tau : Charge D) :
    halfCreationExponential D (sigma + tau) =
      halfCreationExponential D sigma * halfCreationExponential D tau := by
  classical
  have logarithms : halfCreationSeries D (sigma + tau) =
      halfCreationSeries D sigma + halfCreationSeries D tau := by
    ext n
    simp only [halfCreationSeries, PowerSeries.coeff_mk, map_add]
    split_ifs <;> simp [Pi.add_apply, Int.cast_add, add_smul,
      Finset.sum_add_distrib, smul_add]
  let product := halfCreationExponential D sigma * halfCreationExponential D tau
  let driver := PowerSeries.derivative (R := Oscillator D)
    (halfCreationSeries D (sigma + tau))
  have productEquation : PowerSeries.derivative (R := Oscillator D) product =
      product * driver := by
    dsimp only [product, driver]
    rw [(PowerSeries.derivative (R := Oscillator D)).leibniz,
      exponential_derivative, exponential_derivative, logarithms, map_add]
    ring
  have sumEquation : PowerSeries.derivative (R := Oscillator D)
      (halfCreationExponential D (sigma + tau)) =
        halfCreationExponential D (sigma + tau) * driver :=
    exponential_derivative D (sigma + tau)
  apply PowerSeries.ext
  intro n
  induction n using Nat.strong_induction_on with
  | h n previous =>
    cases n with
    | zero =>
      simp only [product, PowerSeries.coeff_mul, Finset.Nat.antidiagonal_zero,
        Finset.sum_singleton, exponential_constant, one_mul]
    | succ n =>
      have sumRecurrence := congrArg (PowerSeries.coeff n) sumEquation
      have productRecurrence := congrArg (PowerSeries.coeff n) productEquation
      change PowerSeries.coeff n
          (PowerSeries.derivative (R := Oscillator D)
            (halfCreationExponential D (sigma + tau))) = _ at sumRecurrence
      change PowerSeries.coeff n
          (PowerSeries.derivative (R := Oscillator D) product) = _ at productRecurrence
      conv_lhs at sumRecurrence => rw [PowerSeries.coeff_derivative]
      conv_rhs at sumRecurrence => rw [PowerSeries.coeff_mul]
      conv_lhs at productRecurrence => rw [PowerSeries.coeff_derivative]
      conv_rhs at productRecurrence => rw [PowerSeries.coeff_mul]
      have sameConvolution :
          (∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
            PowerSeries.coeff ij.1 (halfCreationExponential D (sigma + tau)) *
              PowerSeries.coeff ij.2 driver) =
          ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
            PowerSeries.coeff ij.1 product * PowerSeries.coeff ij.2 driver := by
        apply Finset.sum_congr rfl
        intro ij member
        rw [previous ij.1 (by
          have degree := Finset.HasAntidiagonal.mem_antidiagonal.mp member
          omega)]
      have scaled := sumRecurrence.trans (sameConvolution.trans productRecurrence.symm)
      have nonzero : (n + 1 : Oscillator D) ≠ 0 := by
        exact_mod_cast Nat.succ_ne_zero n
      exact mul_right_cancel₀ nonzero scaled

/- The finite creation diagonal is the coefficient of the product of the
   two actual half exponentials. Negative total degrees are retained. -/
private theorem collision_diagonal_zero (D : LatticeData) (sigma tau : Charge D)
    (e : ℤ) (d : Fin 2 →₀ ℕ) :
    collisionDiagonal D sigma tau 0 e d =
      halfCreationCoeff D (sigma + tau)
        (e + chargeNorm D (sigma + tau) + d 0 + d 1) := by
  classical
  let total : ℤ := e + chargeNorm D (sigma + tau) + d 0 + d 1
  simp only [collisionDiagonal, Nat.cast_zero, mul_zero, add_zero]
  change (if total < 0 then 0 else
    ∑ m ∈ Finset.range (total.toNat + 1), diagonalTerm D sigma tau 0 total (d 0) m) =
      halfCreationCoeff D (sigma + tau) total
  by_cases negative : total < 0
  · simp [negative, halfCreationCoeff]
  · rw [if_neg negative, halfCreationCoeff, if_neg negative,
      half_creation_exponential_add, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    apply Finset.sum_congr rfl
    intro m member
    have bound := Finset.mem_range.mp member
    have nonnegative : 0 ≤ total - (m : ℤ) := by omega
    have remaining : (total - (m : ℤ)).toNat = total.toNat - m := by omega
    simp only [diagonalTerm, collision_scalar_zero, one_smul,
      halfCreationCoeff, if_neg (show ¬ (m : ℤ) < 0 by omega),
      if_neg (not_lt.mpr nonnegative), Int.toNat_natCast, remaining]

/- This diagonal is an evaluation of a finite polynomial, with no global
   End-valued support claim. It holds for every target polynomial, including
   every polynomial obtained after a current or derivative transformation. -/
private theorem pair_translation_diagonal (D : LatticeData) (sigma tau : Charge D)
    (p : Oscillator D) :
    (MvPolynomial.eval₂AlgHom (Oscillator D)
      (fun _ : Fin 2 => (Polynomial.X : Polynomial (Oscillator D))))
        (LatticeHalfFockProductKernel.pairTranslation D sigma tau p) =
      halfTranslatedPolynomial D (sigma + tau) p := by
  let diagonal : PairPolynomial D →ₐ[Oscillator D] Polynomial (Oscillator D) :=
    MvPolynomial.eval₂AlgHom (Oscillator D) (fun _ : Fin 2 => Polynomial.X)
  have variableValue (i : Index D) :
      diagonal (LatticeHalfFockProductKernel.pairTranslationVariable D sigma tau i) =
        halfTranslationVariable D (sigma + tau) i := by
    have pairing : bilinear D (sigma + tau) (unitCharge D i.1) =
        bilinear D sigma (unitCharge D i.1) + bilinear D tau (unitCharge D i.1) := by
      simp [bilinear, add_mul, Finset.sum_add_distrib]
    simp [diagonal, LatticeHalfFockProductKernel.pairTranslationVariable,
      halfTranslationVariable, pairing, Int.cast_add, add_smul]
    <;> ring
  change diagonal (LatticeHalfFockProductKernel.pairTranslation D sigma tau p) = _
  induction p using MvPolynomial.induction_on with
  | C scalar =>
    simp [diagonal, LatticeHalfFockProductKernel.pairTranslation,
      halfTranslatedPolynomial]
  | add p q hp hq =>
    simp only [LatticeHalfFockProductKernel.pairTranslation,
      halfTranslatedPolynomial, map_add] at hp hq ⊢
    rw [hp, hq]
  | mul_X p i hp =>
    change diagonal (LatticeHalfFockProductKernel.pairTranslation D sigma tau
      (p * MvPolynomial.X i)) = _
    simp only [LatticeHalfFockProductKernel.pairTranslation, halfTranslatedPolynomial,
      map_mul, MvPolynomial.eval₂AlgHom_X] at hp ⊢
    rw [hp, variableValue]

private theorem collision_oscillator_zero (D : LatticeData) (sigma tau : Charge D)
    (e : ℤ) (p : Oscillator D) :
    collisionOscillator D sigma tau 0 e p =
      oscillatorCoefficient D (sigma + tau) e p := by
  classical
  let diagonal : PairPolynomial D →ₐ[Oscillator D] Polynomial (Oscillator D) :=
    MvPolynomial.eval₂AlgHom (Oscillator D) (fun _ : Fin 2 => Polynomial.X)
  let readout : Polynomial (Oscillator D) →ₗ[Oscillator D] Oscillator D :=
    LatticeActualProductKernel.coefficientConvolution
      (halfCreationCoeff D (sigma + tau)) (e + chargeNorm D (sigma + tau))
  have collapse (Q : PairPolynomial D) :
      collisionConvolution D sigma tau 0 e Q = readout (diagonal Q) := by
    induction Q using MvPolynomial.induction_on' with
    | add Q R hQ hR => simp only [map_add, hQ, hR]
    | monomial d c =>
      have monomialDiagonal : diagonal (MvPolynomial.monomial d c) =
          Polynomial.monomial (d 0 + d 1) c := by
        change MvPolynomial.eval₂ (algebraMap (Oscillator D) (Polynomial (Oscillator D)))
          (fun _ : Fin 2 => Polynomial.X) (MvPolynomial.monomial d c) = _
        rw [MvPolynomial.eval₂_monomial,
          Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_two, ← pow_add]
        change Polynomial.C c * Polynomial.X ^ (d 0 + d 1) = _
        rw [Polynomial.X_pow_eq_monomial]
        simp
      rw [monomialDiagonal]
      have convolutionMonomial :
          collisionConvolution D sigma tau 0 e (MvPolynomial.monomial d c) =
            c * collisionDiagonal D sigma tau 0 e d := by
        simp [collisionConvolution, MvPolynomial.monomial]
      rw [convolutionMonomial]
      change c * collisionDiagonal D sigma tau 0 e d =
        LatticeActualProductKernel.coefficientConvolution
          (halfCreationCoeff D (sigma + tau)) (e + chargeNorm D (sigma + tau))
            (Polynomial.monomial (d 0 + d 1) c)
      rw [LatticeActualProductKernel.coefficientConvolution_monomial,
        collision_diagonal_zero]
      congr 2
      push_cast
      ring
  change collisionConvolution D sigma tau 0 e
    (LatticeHalfFockProductKernel.pairTranslation D sigma tau p) = _
  rw [collapse]
  have diagonalTranslation : diagonal
      (LatticeHalfFockProductKernel.pairTranslation D sigma tau p) =
        halfTranslatedPolynomial D (sigma + tau) p :=
    pair_translation_diagonal D sigma tau p
  rw [diagonalTranslation]
  change LatticeActualProductKernel.coefficientConvolution
    (halfCreationCoeff D (sigma + tau)) (e + chargeNorm D (sigma + tau))
      (halfTranslatedPolynomial D (sigma + tau) p) = _
  rw [LatticeActualProductKernel.coefficientConvolution_expansion]
  change (∑ n ∈ (halfTranslatedPolynomial D (sigma + tau) p).support,
    (halfTranslatedPolynomial D (sigma + tau) p).coeff n *
      halfCreationCoeff D (sigma + tau) (e + chargeNorm D (sigma + tau) + n)) =
        ∑ᶠ n : ℕ, oscillatorTerm D (sigma + tau) e p n
  rw [finsum_eq_sum_of_support_subset _ (term_support D (sigma + tau) e p)]
  rfl

/- The source side reduces Corr(1) to shift 0/empty word, and P_0=1.
   Collision side: t_0=1, E_sigma E_tau=E_(sigma+tau), evaluate the finite
   pairTranslation diagonal X=Y. Compare actual oscillatorCoefficient on
   arbitrary p, then tensor linearity.
   No extra epsilon: groundAction(a) is on both sides. -/
private theorem collision_base (D : LatticeData) (hu : IsUnit D.G.det)
    (sigma tau : Charge D) (e : ℤ) (x : ActualTensor D hu) :
    (correctedField D hu
      (Finsupp.single (sigma + tau) (creationCoeff D sigma (0 : ℕ)))).coeff e x =
      collisionCoefficient D hu sigma tau 0 e x := by
  classical
  have creationZero : creationCoeff D sigma (0 : ℕ) = (1 : Oscillator D) := by
    simpa [creationCoeff] using LatticeSugawaraConformal.exponential_constant D sigma
  rw [creationZero]
  have corrOne : Corr D (sigma + tau) (1 : Oscillator D) =
      Finsupp.single 0 (1 : Oscillator D) := by
    have emptyEnumeration : ([] : List (Index D)).Perm
        (LatticeAllStateField.occurrences D (0 : Index D →₀ ℕ)) := by
      simp [LatticeAllStateField.occurrences]
    have correction := Corr_monomial_enumeration D (sigma + tau) 0 [] emptyEnumeration
    calc
      _ = shiftCoefficients D (1 : Polynomial (Oscillator D)) := by
        simpa only [show (MvPolynomial.monomial 0 (1 : ℂ) : Oscillator D) = 1 by simp,
          correctionWord, map_one] using correction
      _ = _ := by
        apply Finsupp.ext
        intro n
        change (1 : Polynomial (Oscillator D)).coeff n = (Finsupp.single 0 1) n
        simp [Polynomial.coeff_one, Finsupp.single_apply, eq_comm]
  have seedCoefficient :
      (correctedField D hu (Finsupp.single (sigma + tau) (1 : Oscillator D))).coeff e =
        chargedCoefficient D hu (sigma + tau) e := by
    rw [correctedField, Finsupp.lsum_single, correctedPolynomial, LinearMap.comp_apply,
      corrOne, correctedSum, Finsupp.lsum_single, LinearMap.comp_apply]
    rw [shiftField_coefficient_public]
    simp only [Nat.cast_zero, mul_zero, add_zero]
    rw [show (1 : Oscillator D) = MvPolynomial.monomial 0 (1 : ℂ) by simp,
      polynomialField_monomial_public]
    have emptyOccurrences : occurrences D (0 : Index D →₀ ℕ) = [] := by
      simp [occurrences]
    rw [emptyOccurrences]
    apply LinearMap.ext
    intro input
    rw [wordField_coefficient]
    change (∑ᶠ _ : Unit, (chargedField D hu (sigma + tau)).coeff e input) = _
    rw [finsum_eq_single _ ()]
    · simp only [chargedField, HVertexOperator.coeff_of_coeff]
    · intro modes distinct
      exact (distinct (Subsingleton.elim _ _)).elim
  rw [seedCoefficient]
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul p g =>
    simp only [chargedCoefficient, collisionCoefficient, LinearMap.smul_apply,
      TensorProduct.map_tmul, collision_oscillator_zero]
  | add x y hx hy => simp only [map_add, hx, hy]

/- Full all-N induction. Every coefficient and every actual input is
   quantified INSIDE the induction property. This transports singletonLinear
   as a whole-field operation, including its transformed inputs. -/
theorem charged_allN_draft (D : LatticeData) (hu : IsUnit D.G.det)
    (sigma tau : Charge D) (N : ℕ) :
    ∀ (e : ℤ) (x : ActualTensor D hu),
      (correctedField D hu
        (Finsupp.single (sigma + tau) (creationCoeff D sigma N))).coeff e x =
          collisionCoefficient D hu sigma tau N e x := by
  classical
  induction N using Nat.strong_induction_on with
  | h N previous =>
    cases N with
    | zero => exact collision_base D hu sigma tau
    | succ N =>
      intro e x
      have fields (k : ℕ) (within : k < N + 1) :
          correctedField D hu
            (Finsupp.single (sigma + tau) (creationCoeff D sigma k)) =
              collisionField D hu sigma tau k := by
        apply HVertexOperator.coeff_inj
        funext output
        apply LinearMap.ext
        intro input
        simpa only [collisionField, HVertexOperator.coeff_of_coeff] using
          previous k within output input
      have source := source_closed_recurrence D hu sigma tau N e x
      have collision := collision_closed_recurrence D hu sigma tau N e x
      have currentEquality :
          (normalCurrent D hu tau
            (correctedField D hu
              (Finsupp.single (sigma + tau) (creationCoeff D sigma N)))).coeff e x =
          (normalCurrent D hu tau (collisionField D hu sigma tau N)).coeff e x := by
        rw [fields N (by omega)]
      have lowerTerms :
          (∑ j ∈ Finset.range (N + 1), collisionR j •
            (correctedField D hu
              (Finsupp.single (sigma + tau) (creationCoeff D sigma (N - j)))).coeff
                (e + 2 * ((j : ℤ) + 1)) x) =
          ∑ j ∈ Finset.range (N + 1), collisionR j •
            collisionCoefficient D hu sigma tau (N - j)
              (e + 2 * ((j : ℤ) + 1)) x := by
        apply Finset.sum_congr rfl
        intro j member
        have hmember : j < N + 1 := Finset.mem_range.mp member
        have castSub : ((N - j : ℕ) : ℤ) = (N : ℤ) - (j : ℤ) := by omega
        rw [← castSub]
        rw [previous (N - j) (by omega)]
      simp only [currentEquality, lowerTerms,
        previous N (by omega) (e + 2) x] at source
      have scaled : (N + 1 : ℂ) •
          (correctedField D hu
            (Finsupp.single (sigma + tau) (creationCoeff D sigma (N + 1)))).coeff e x =
          (N + 1 : ℂ) • collisionCoefficient D hu sigma tau (N + 1) e x :=
        source.trans collision.symm
      have nonzero : (N + 1 : ℂ) ≠ 0 := by
        exact_mod_cast Nat.succ_ne_zero N
      have cancelled := congrArg
        (fun v : ActualTensor D hu => (N + 1 : ℂ)⁻¹ • v) scaled
      have castSucc : ((N + 1 : ℕ) : ℤ) = (N : ℤ) + 1 := by omega
      simpa only [castSucc, smul_smul, inv_mul_cancel₀ nonzero, one_smul] using cancelled

/- Live ordinary-source consumer. Its source type is Carrier D, and only
   its corrected realization acts on ActualTensor D hu. -/
private theorem charged_source_product_allN_draft
    (D : LatticeData) (hu : IsUnit D.G.det) (sigma tau : Charge D)
    (r e : ℤ) (x : ActualTensor D hu) :
    (correctedField D hu
      (((LatticeAllStateField.Y D (Finsupp.single sigma (1 : Oscillator D)))[[r]])
        (Finsupp.single tau (1 : Oscillator D)))).coeff e x =
      if -r - 1 - bilinear D sigma tau < 0 then 0 else
        epsilon D sigma tau • collisionCoefficient D hu sigma tau
          (-r - 1 - bilinear D sigma tau).toNat e x := by
  rw [bare_source_product, map_smul]
  change epsilon D sigma tau •
    (correctedField D hu
      (Finsupp.single (sigma + tau)
        (creationCoeff D sigma (-r - 1 - bilinear D sigma tau)))).coeff e x = _
  by_cases negative : -r - 1 - bilinear D sigma tau < 0
  · simp [negative, creationCoeff]
  · rw [if_neg negative]
    have castDegree :
        (((-r - 1 - bilinear D sigma tau).toNat : ℕ) : ℤ) =
          -r - 1 - bilinear D sigma tau := Int.toNat_of_nonneg (le_of_not_gt negative)
    have comparison := charged_allN_draft D hu sigma tau
      (-r - 1 - bilinear D sigma tau).toNat e x
    rw [castDegree] at comparison
    exact congrArg (fun v : ActualTensor D hu => epsilon D sigma tau • v) comparison

/- The ordinary two-charge normalization and the actual ground product are
   retained explicitly in this coefficient formula on every tensor input. -/
theorem charged_normalized_source_product_allN
    (D : LatticeData) (hu : IsUnit D.G.det) (sigma tau : Charge D)
    (r e : ℤ) (x : ActualTensor D hu) :
    (correctedField D hu
      (((LatticeAllStateField.Y D (Finsupp.single sigma (1 : Oscillator D)))[[r]])
        (Finsupp.single tau (1 : Oscillator D)))).coeff e x =
      if -r - 1 - bilinear D sigma tau < 0 then 0 else
        (chargeScalar D sigma * chargeScalar D tau *
          (2 : ℂ) ^ (-2 * bilinear D sigma tau)) •
          TensorProduct.map
            (collisionOscillator D sigma tau
              (-r - 1 - bilinear D sigma tau).toNat e)
            (groundAction D hu sigma * groundAction D hu tau) x := by
  have addLeft (a b c : Charge D) : bilinear D (a + b) c =
      bilinear D a c + bilinear D b c := by
    simp [bilinear, add_mul, Finset.sum_add_distrib]
  have addRight (a b c : Charge D) : bilinear D a (b + c) =
      bilinear D a b + bilinear D a c := by
    simp [bilinear, mul_add, Finset.sum_add_distrib]
  have normAdd : chargeNorm D (sigma + tau) =
      chargeNorm D sigma + chargeNorm D tau + 2 * bilinear D sigma tau := by
    unfold chargeNorm
    rw [addLeft, addRight, addRight,
      LatticeFiniteNegativeGeneration.bilinear_symmetric D tau sigma]
    ring
  have normalization : chargeScalar D sigma * chargeScalar D tau *
      (2 : ℂ) ^ (-2 * bilinear D sigma tau) = chargeScalar D (sigma + tau) := by
    unfold chargeScalar
    rw [← zpow_add₀ (by norm_num : (2 : ℂ) ≠ 0),
      ← zpow_add₀ (by norm_num : (2 : ℂ) ≠ 0)]
    congr 1
    omega
  rw [charged_source_product_allN_draft]
  by_cases negative : -r - 1 - bilinear D sigma tau < 0
  · simp only [negative, if_true]
  · simp only [negative, if_false]
    rw [normalization, LatticeHalfFockGroundProducts.ground_action_product,
      TensorProduct.map_smul_right]
    simp only [collisionCoefficient, LinearMap.smul_apply, smul_smul, mul_comm]

end
end D5.S3.VertexAlgebra.LatticeHalfFockChargedCollision
