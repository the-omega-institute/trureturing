/- GID: D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision/Current
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockChargedCollision/Current
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Closed source insertion and arbitrary-input charged current moments. -/

import D5.S3.VertexAlgebra.LatticeHalfFockChargedCollision.Kernel

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

private theorem chargeInsertion_closed (D : LatticeData) (hu : IsUnit D.G.det)
    (sigma tau : Charge D) (N : ℕ) (e : ℤ) (x : ActualTensor D hu)
    (modes : ∀ (colour : Fin D.rank) (n : ℕ),
      LatticeFiniteNegativeGeneration.neutralMode D colour (n : ℤ)
          (Finsupp.single (sigma + tau) (creationCoeff D sigma N)) =
        if n = 0 then
          (bilinear D (unitCharge D colour) (sigma + tau) : ℂ) •
            Finsupp.single (sigma + tau) (creationCoeff D sigma N)
        else
          (bilinear D (unitCharge D colour) sigma : ℂ) •
            Finsupp.single (sigma + tau)
              (creationCoeff D sigma ((N : ℤ) - (n : ℤ)))) :
    (chargeInsertion D hu tau
      (Finsupp.single (sigma + tau) (creationCoeff D sigma N))).coeff e x =
      (normalCurrent D hu tau
        (correctedField D hu
          (Finsupp.single (sigma + tau) (creationCoeff D sigma N)))).coeff e x -
      ((chargeNorm D tau : ℂ) / 2) •
        (correctedField D hu
          (Finsupp.single (sigma + tau) (creationCoeff D sigma N))).coeff (e + 2) x -
      ((bilinear D sigma tau : ℂ) / 2) •
        ∑ j ∈ Finset.range (N + 1), collisionR j •
          (correctedField D hu
            (Finsupp.single (sigma + tau) (creationCoeff D sigma (N - j)))).coeff
              (e + 2 * ((j : ℤ) + 1)) x := by
  have fieldIdentity := chargeInsertion_field_identity D hu sigma tau N modes
  have evaluated := congrArg
    (fun F : NativeField D hu => F.coeff e x) fieldIdentity
  simp only [map_sub, map_smul, Pi.sub_apply, Pi.smul_apply,
    LinearMap.sub_apply, LinearMap.smul_apply] at evaluated
  rw [map_sum] at evaluated
  rw [Finset.sum_apply] at evaluated
  rw [LinearMap.sum_apply] at evaluated
  have shifted (n : ℕ) :
      (HVertexOperator.coeff
          ((shiftField D hu (1 + n))
            (correctedField D hu
              (Finsupp.single (sigma + tau) (creationCoeff D sigma (N - n))))) e) x =
        (HVertexOperator.coeff
          (correctedField D hu
            (Finsupp.single (sigma + tau) (creationCoeff D sigma (N - n))))
          (e + 2 * ((n : ℤ) + 1))) x := by
    simpa only [Nat.cast_add, Nat.cast_one, add_comm] using
      congrArg (fun L => L x)
        (shiftField_coefficient_public D hu (1 + n)
          (correctedField D hu
            (Finsupp.single (sigma + tau) (creationCoeff D sigma (N - n)))) e)
  have shiftedOne :
      (HVertexOperator.coeff
          ((shiftField D hu 1)
            (correctedField D hu
              (Finsupp.single (sigma + tau) (creationCoeff D sigma N)))) e) x =
        (HVertexOperator.coeff
          (correctedField D hu
            (Finsupp.single (sigma + tau) (creationCoeff D sigma N)))
          (e + 2)) x := by
    exact congrArg (fun L => L x)
      (shiftField_coefficient_public D hu 1
        (correctedField D hu
          (Finsupp.single (sigma + tau) (creationCoeff D sigma N))) e)
  have sumTransport :
      (∑ j ∈ Finset.range (N + 1),
        (HVertexOperator.coeff
          (collisionR j •
            ((shiftField D hu (1 + j))
              (correctedField D hu
                (Finsupp.single (sigma + tau)
                  (creationCoeff D sigma (N - j)))))) e) x) =
        ∑ j ∈ Finset.range (N + 1), collisionR j •
          (HVertexOperator.coeff
            (correctedField D hu
              (Finsupp.single (sigma + tau)
                (creationCoeff D sigma (N - j))))
            (e + 2 * ((j : ℤ) + 1))) x := by
    apply Finset.sum_congr rfl
    intro j member
    simp only [map_smul, Pi.smul_apply, LinearMap.smul_apply]
    rw [shifted j]
  rw [sumTransport] at evaluated
  rw [shiftedOne] at evaluated
  simpa only [HVertexOperator.coeff_of_coeff, Nat.cast_add, Nat.cast_one] using evaluated

theorem source_closed_recurrence (D : LatticeData) (hu : IsUnit D.G.det)
    (sigma tau : Charge D) (N : ℕ) (e : ℤ) (x : ActualTensor D hu) :
    (N + 1 : ℂ) •
        (correctedField D hu
          (Finsupp.single (sigma + tau) (creationCoeff D sigma (N + 1)))).coeff e x =
      (((e + 2 : ℤ) : ℂ) / 2) •
        (correctedField D hu
          (Finsupp.single (sigma + tau) (creationCoeff D sigma N))).coeff (e + 2) x -
      (normalCurrent D hu tau
        (correctedField D hu
          (Finsupp.single (sigma + tau) (creationCoeff D sigma N)))).coeff e x +
      ((chargeNorm D tau : ℂ) / 2) •
        (correctedField D hu
          (Finsupp.single (sigma + tau) (creationCoeff D sigma N))).coeff (e + 2) x +
      ((bilinear D sigma tau : ℂ) / 2) •
        ∑ j ∈ Finset.range (N + 1), collisionR j •
          (correctedField D hu
            (Finsupp.single (sigma + tau) (creationCoeff D sigma (N - j)))).coeff
              (e + 2 * ((j : ℤ) + 1)) x := by
  rw [corrected_creation_step,
    chargeInsertion_closed D hu sigma tau N e x
      (source_neutral_creation D sigma tau N)]
  module

/- The finite moment readout for the normal current. -/
def collisionMoment (D : LatticeData) (sigma tau : Charge D)
    (N : ℕ) (e : ℤ) (p : Oscillator D) : Oscillator D :=
  let T := LatticeHalfFockProductKernel.pairTranslation D sigma tau p
  ∑ d ∈ T.support, T.coeff d *
    (let L : ℤ := e + 2 + chargeNorm D (sigma + tau) + 2 * N + d 0 + d 1
     if L < 0 then 0 else
       ∑ m ∈ Finset.range (L.toNat + 1),
         ((((L - (m : ℤ) - (d 1 : ℤ)) : ℤ) : ℂ) / 2) •
           diagonalTerm D sigma tau N L (d 0) m)

/- Arbitrary-input singleton calculation. Negative
   current modes j=-k-1 give n/2 by exponential_derivative;
   nonnegative j=k give -d1/2 by Y*d/dY(pairTranslation p).
   Explicit finite supports: negative branch from collision_lower_bound;
   positive branch from p.vars, with each transformed input read separately. -/
theorem collision_normal_moment (D : LatticeData) (hu : IsUnit D.G.det)
    (sigma tau : Charge D) (N : ℕ) (e : ℤ)
    (p : Oscillator D) (g : ActualGround D hu) :
    (normalCurrent D hu tau (collisionField D hu sigma tau N)).coeff e
        (p ⊗ₜ[ℂ] g) =
      chargeScalar D (sigma + tau) •
        (collisionMoment D sigma tau N e p ⊗ₜ[ℂ]
          groundAction D hu (sigma + tau) g) := by
  classical
  let F := collisionField D hu sigma tau N
  let v : ActualTensor D hu := p ⊗ₜ[ℂ] g
  let lower : ℤ := min
    (-chargeNorm D (sigma + tau) - 2 * (N : ℤ) -
      (translatedDegree D sigma tau p : ℤ) - e - 3) 0
  let support (colour : Fin D.rank) : Finset (ModeTuple D [(colour, 0)]) :=
    modeBox D [(colour, 0)] lower (LatticeHalfFock.bound D p)
  let oscillatorTerm (colour : Fin D.rank)
      (modes : ModeTuple D [(colour, 0)]) : Oscillator D :=
    if modes.1 < 0 then
      LatticeHalfFock.current D colour modes.1
        (collisionOscillator D sigma tau N (e + 2 * modes.1 + 3) p)
    else collisionOscillator D sigma tau N (e + 2 * modes.1 + 3)
      (LatticeHalfFock.current D colour modes.1 p)
  have flat (colour : Fin D.rank) (modes : ModeTuple D [(colour, 0)]) :
      flatTerm D hu F [(colour, 0)] e v modes =
        chargeScalar D (sigma + tau) •
          (oscillatorTerm colour modes ⊗ₜ[ℂ] groundAction D hu (sigma + tau) g) := by
    rcases modes with ⟨mode, tail⟩
    cases tail
    by_cases negative : mode < 0 <;>
      simp only [F, v, oscillatorTerm, flatTerm, flatCoefficient, jetCurrent,
        jetScalar, Finset.range_zero, Finset.prod_empty, Nat.factorial_zero,
        Nat.cast_one, div_one, one_smul, Nat.cast_zero, mul_zero, add_zero,
        negative, reduceIte, collisionField, HVertexOperator.coeff_of_coeff,
        collisionCoefficient, Module.End.mul_apply, LinearMap.smul_apply,
        LatticeHalfFock.tensorCurrent, LatticeHalfFock.tensorEnd,
        TensorProduct.map_tmul, LinearMap.id_apply, map_smul]
  have oscillatorBelow (q : Oscillator D) (z : ℤ)
      (low : z < -chargeNorm D (sigma + tau) - 2 * (N : ℤ) -
        (translatedDegree D sigma tau q : ℤ)) :
      collisionOscillator D sigma tau N z q = 0 := by
    rw [collision_expansion]
    apply Finset.sum_eq_zero
    intro d member
    have degree := Finset.le_sup (f := fun d : Fin 2 →₀ ℕ => d 0 + d 1) member
    have castDegree : (d 0 : ℤ) + (d 1 : ℤ) ≤ translatedDegree D sigma tau q := by
      exact_mod_cast degree
    rw [diagonal_as_sum, if_pos (by omega), mul_zero]
  have oscillatorSupport (colour : Fin D.rank) :
      Function.support (oscillatorTerm colour) ⊆ support colour := by
    rintro ⟨mode, tail⟩ nonzero
    cases tail
    have lowerBound : lower ≤ mode := by
      by_contra outside
      have negative : mode < 0 := by dsimp [lower] at outside; omega
      have low : e + 2 * mode + 3 <
          -chargeNorm D (sigma + tau) - 2 * (N : ℤ) -
            (translatedDegree D sigma tau p : ℤ) := by
        dsimp [lower] at outside
        omega
      exact nonzero (by
        simp only [oscillatorTerm, if_pos negative, oscillatorBelow p _ low, map_zero])
    have upperBound : mode ≤ (LatticeHalfFock.bound D p : ℤ) := by
      by_contra outside
      have nonnegative : 0 ≤ mode := by omega
      have zero := LatticeHalfFock.current_vanish D colour p mode (by omega)
      exact nonzero (by simp only [oscillatorTerm, if_neg (not_lt.mpr nonnegative),
        zero, map_zero])
    change (mode, ()) ∈ (Finset.Icc lower (LatticeHalfFock.bound D p : ℤ)).product {()}
    exact Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr ⟨lowerBound, upperBound⟩, Finset.mem_singleton_self ()⟩
  have finiteCoefficient :
      (normalCurrent D hu tau F).coeff e v =
        ∑ colour : Fin D.rank, (tau colour : ℂ) •
          ∑ modes ∈ support colour, flatTerm D hu F [(colour, 0)] e v modes := by
    have expanded : (normalCurrent D hu tau F).coeff e v =
        ∑ colour : Fin D.rank, (tau colour : ℂ) •
          (wordField D hu F [(colour, 0)]).coeff e v := by
      simp [normalCurrent, singletonLinear]
    rw [expanded]
    apply Finset.sum_congr rfl
    intro colour member
    congr 1
    rw [wordField_coefficient]
    apply finsum_eq_sum_of_support_subset
    intro modes supported
    apply oscillatorSupport colour
    intro zero
    exact supported (by rw [flat, zero, TensorProduct.zero_tmul, smul_zero])
  have reduction :
      (normalCurrent D hu tau F).coeff e v =
        chargeScalar D (sigma + tau) •
          ((∑ colour : Fin D.rank, (tau colour : ℂ) •
            ∑ modes ∈ support colour, oscillatorTerm colour modes) ⊗ₜ[ℂ]
              groundAction D hu (sigma + tau) g) := by
    rw [finiteCoefficient]
    simp_rw [flat, TensorProduct.smul_tmul']
    simp only [TensorProduct.sum_tmul, TensorProduct.smul_tmul',
      Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro colour member
    apply Finset.sum_congr rfl
    intro modes mode_member
    congr 1
    module
  change (normalCurrent D hu tau F).coeff e v = _
  rw [reduction]
  apply congrArg (fun q : Oscillator D => chargeScalar D (sigma + tau) •
    (q ⊗ₜ[ℂ] groundAction D hu (sigma + tau) g))
  /- Every helper below is local to this proof.  The polynomial convolution
     is used as a linear map, so its application to T(current p) reads that
     transformed polynomial's own support. -/
  let T := LatticeHalfFockProductKernel.pairTranslation D sigma tau
  let readout (z : ℤ) : PairPolynomial D →ₗ[ℂ] Oscillator D :=
    (collisionConvolution D sigma tau N z).restrictScalars ℂ
  have readout_monomial (z : ℤ) (d : Fin 2 →₀ ℕ) (c : Oscillator D) :
      readout z (MvPolynomial.monomial d c) =
        c * collisionDiagonal D sigma tau N z d := by
      change collisionConvolution D sigma tau N z (MvPolynomial.monomial d c) = _
      simp [collisionConvolution, MvPolynomial.monomial]
  have readout_second_shift (z : ℤ) (w : ℕ) (Q : PairPolynomial D) :
      readout z (MvPolynomial.X 1 ^ w * Q) = readout (z + w) Q := by
    induction Q using MvPolynomial.induction_on' with
    | add Q R hQ hR => simp only [mul_add, map_add, hQ, hR]
    | monomial d c =>
      rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul_monomial,
        readout_monomial, readout_monomial]
      simp only [one_mul]
      have diagonal_shift :
          collisionDiagonal D sigma tau N z (Finsupp.single 1 w + d) =
            collisionDiagonal D sigma tau N (z + w) d := by
        unfold collisionDiagonal
        simp only [Finsupp.add_apply, Finsupp.single_eq_same,
          Finsupp.single_eq_of_ne (by decide : (0 : Fin 2) ≠ 1), zero_add]
        have total : z + chargeNorm D (sigma + tau) + 2 * (N : ℤ) +
            (d 0 : ℤ) + ((w + d 1 : ℕ) : ℤ) =
            z + w + chargeNorm D (sigma + tau) + 2 * (N : ℤ) + d 0 + d 1 := by
          push_cast
          ring
        rw [total]
      rw [diagonal_shift]
  have euler_monomial (d : Fin 2 →₀ ℕ) (c : Oscillator D) :
      MvPolynomial.X 1 * MvPolynomial.pderiv 1 (MvPolynomial.monomial d c) =
        (d 1 : ℂ) • MvPolynomial.monomial d c := by
    have h := MvPolynomial.X_mul_pderiv_monomial
      (i := (1 : Fin 2)) (m := d) (r := c)
    convert h using 1 <;>
      simp [MvPolynomial.smul_monomial, nsmul_eq_mul, Algebra.smul_def,
        mul_comm]
  have readout_euler (z : ℤ) (Q : PairPolynomial D) :
      readout z (MvPolynomial.X 1 * MvPolynomial.pderiv 1 Q) =
        ∑ d ∈ Q.support, (d 1 : ℂ) •
          (Q.coeff d * collisionDiagonal D sigma tau N z d) := by
    conv_lhs => rw [MvPolynomial.as_sum Q]
    simp only [map_sum, Finset.mul_sum, euler_monomial, map_smul,
      readout_monomial]

  let pairEuler : PairPolynomial D →ₗ[ℂ] PairPolynomial D :=
    (LinearMap.mulLeft ℂ (MvPolynomial.X 1 : PairPolynomial D)).comp
      ((MvPolynomial.pderiv (R := Oscillator D) (1 : Fin 2)).toLinearMap.restrictScalars ℂ)
  /- This is a chain rule on the full polynomial, not a hypothesis of
     homogeneity.  The finite support is q.vars; pderiv counts every
     occurrence of a repeated variable. -/
  have pair_euler (q : Oscillator D) :
      MvPolynomial.X 1 * MvPolynomial.pderiv 1 (T q) =
        ∑ index ∈ q.vars,
          (-((omega D index : ℕ) : ℂ) *
            (bilinear D tau (unitCharge D index.1) : ℂ)) •
            (MvPolynomial.X 1 ^ omega D index * T (MvPolynomial.pderiv index q)) := by
    letI : Algebra (Oscillator D) (PairPolynomial D) := T.toRingHom.toAlgebra
    letI : Module (Oscillator D) (PairPolynomial D) :=
      (T.toRingHom.toAlgebra).toModule
    letI : IsScalarTower ℂ (Oscillator D) (PairPolynomial D) :=
      { smul_assoc := by
          intro c a b
          change T (c • a) * b = c • (T a * b)
          rw [map_smul, smul_mul_assoc] }
    let transportedPartial (index : Index D) :
        Derivation ℂ (Oscillator D) (PairPolynomial D) :=
      { toFun := fun q => T (MvPolynomial.pderiv index q)
        map_add' := by intro q r; simp only [map_add]
        map_smul' := by
          intro c q
          rw [Derivation.map_smul, map_smul]
          rfl
        map_one_eq_zero' := by
          change T (MvPolynomial.pderiv index 1) = 0
          rw [MvPolynomial.pderiv_one, map_zero]
        leibniz' := by
          intro q r
          change T (MvPolynomial.pderiv index (q * r)) =
            T q * T (MvPolynomial.pderiv index r) +
              T r * T (MvPolynomial.pderiv index q)
          rw [MvPolynomial.pderiv_mul, map_add, map_mul, map_mul]
          ring }
    let delta : Derivation ℂ (Oscillator D) (PairPolynomial D) :=
      { toFun := fun q => pairEuler (T q)
        map_add' := by intro q r; simp only [map_add]
        map_smul' := by
          intro c q
          change pairEuler (T (c • q)) = c • pairEuler (T q)
          rw [map_smul, map_smul]
        map_one_eq_zero' := by
          change pairEuler (T 1) = 0
          dsimp [pairEuler]
          simp
        leibniz' := by
          intro q r
          dsimp
          change pairEuler (T (q * r)) =
            q • pairEuler (T r) + r • pairEuler (T q)
          simp only [Algebra.smul_def]
          change MvPolynomial.X 1 * MvPolynomial.pderiv 1 (T (q * r)) =
            T q * (MvPolynomial.X 1 * MvPolynomial.pderiv 1 (T r)) +
              T r * (MvPolynomial.X 1 * MvPolynomial.pderiv 1 (T q))
          rw [map_mul, MvPolynomial.pderiv_mul]
          ring }
    have derivation_sum_apply
        (s : Finset (Index D))
        (f : Index D → Derivation ℂ (Oscillator D) (PairPolynomial D))
        (r : Oscillator D) : (∑ index ∈ s, f index) r = ∑ index ∈ s, f index r := by
      have h := congrFun (map_sum
        (Derivation.coeFnAddMonoidHom (R := ℂ) (A := Oscillator D)
          (M := PairPolynomial D)) f s) r
      simpa only [Derivation.coeFnAddMonoidHom_apply, Finset.sum_apply] using h
    have expansion : delta q =
        ∑ index ∈ q.vars, delta (MvPolynomial.X index) *
          T (MvPolynomial.pderiv index q) := by
      have h : delta q =
          (∑ index ∈ q.vars, delta (MvPolynomial.X index) • transportedPartial index) q := by
        apply MvPolynomial.derivation_eq_of_forall_mem_vars
        intro index member
        rw [derivation_sum_apply]
        simp [transportedPartial, Derivation.smul_apply,
          MvPolynomial.pderiv_X, Pi.single_apply, apply_ite, member]
      rw [derivation_sum_apply] at h
      change delta q =
        ∑ index ∈ q.vars, delta (MvPolynomial.X index) *
          T (MvPolynomial.pderiv index q) at h
      exact h
    have variableValue (index : Index D) : delta (MvPolynomial.X index) =
        (-((omega D index : ℕ) : ℂ) *
          (bilinear D tau (unitCharge D index.1) : ℂ)) •
            MvPolynomial.X 1 ^ omega D index := by
      change MvPolynomial.X 1 * MvPolynomial.pderiv 1
        (T (MvPolynomial.X index)) = _
      simp only [T, LatticeHalfFockProductKernel.pairTranslation,
        MvPolynomial.eval₂AlgHom_X]
      have coordinate (i : Fin 2) (w : ℕ) (c : Oscillator D) :
          MvPolynomial.X 1 * MvPolynomial.pderiv 1
              (MvPolynomial.C c * MvPolynomial.X i ^ w) =
            ((Finsupp.single i w) 1 : ℂ) •
              (MvPolynomial.C c * MvPolynomial.X i ^ w) := by
        simpa only [MvPolynomial.C_mul_X_pow_eq_monomial] using
          euler_monomial (Finsupp.single i w) c
      simp only [LatticeHalfFockProductKernel.pairTranslationVariable,
        map_sub, mul_sub, MvPolynomial.pderiv_C, mul_zero, mul_neg, coordinate,
        Finsupp.single_eq_same,
        Finsupp.single_eq_of_ne (by decide : (1 : Fin 2) ≠ 0),
        Finsupp.single_eq_of_ne (by decide : (0 : Fin 2) ≠ 1),
        Nat.cast_zero, zero_smul, sub_zero, zero_sub]
      simp [Algebra.smul_def, mul_assoc, mul_comm, mul_left_comm]
    change delta q = _
    rw [expansion]
    apply Finset.sum_congr rfl
    intro index member
    rw [variableValue, smul_mul_assoc]

  have positive_polynomial (q : Oscillator D) :
      (∑ colour : Fin D.rank, (tau colour : ℂ) •
        ∑ k ∈ Finset.range (LatticeHalfFock.bound D q + 1),
          MvPolynomial.X 1 ^ (2 * k + 1) *
            T (LatticeHalfFock.current D colour (k : ℤ) q)) =
        -(1 / 2 : ℂ) •
          (MvPolynomial.X 1 * MvPolynomial.pderiv 1 (T q)) := by
    have gram (other : Fin D.rank) : (∑ colour : Fin D.rank,
        (tau colour : ℂ) * (D.G colour other : ℂ)) =
        (bilinear D tau (unitCharge D other) : ℂ) := by
      have intGram : bilinear D tau (unitCharge D other) =
          ∑ colour : Fin D.rank, tau colour * D.G colour other := by
        simp [bilinear, unitCharge]
      rw [intGram]
      push_cast
      rfl
    have current_sum (k : ℕ) :
        (∑ colour : Fin D.rank, (tau colour : ℂ) •
          LatticeHalfFock.current D colour (k : ℤ) q) =
        ∑ other : Fin D.rank,
          (((k : ℂ) + 1 / 2) *
            (bilinear D tau (unitCharge D other) : ℂ)) •
              MvPolynomial.pderiv (other, k) q := by
      simp only [LatticeHalfFock.current,
        if_neg (by omega : ¬ (k : ℤ) < 0), Int.toNat_natCast,
        LinearMap.smul_apply, LatticeHalfFock.frequency, Int.cast_natCast,
        LatticeActualAnnihilation.annihilate, LatticeSugawaraCurrents.weightedPartial,
        LinearMap.sum_apply, LinearMap.smul_apply, Derivation.coeFn_coe,
        Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro other member
      rw [← Finset.sum_smul]
      congr 1
      calc
        (∑ colour : Fin D.rank,
            (tau colour : ℂ) * (((k : ℂ) + 1 / 2) * (D.G colour other : ℂ))) =
            ((k : ℂ) + 1 / 2) *
              ∑ colour : Fin D.rank, (tau colour : ℂ) * (D.G colour other : ℂ) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro colour _
          ring
        _ = _ := by rw [gram]
    have vars_box : q.vars ⊆ (Finset.univ : Finset (Fin D.rank)) ×ˢ
        Finset.range (LatticeHalfFock.bound D q + 1) := by
      intro index member
      have bound := Finset.le_sup (f := fun x : Index D => x.2 + 1) member
      exact Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_range.mpr (by
        change index.2 + 1 ≤ LatticeHalfFock.bound D q at bound
        omega)⟩
    have pad :
        (∑ index ∈ q.vars,
          (-((omega D index : ℕ) : ℂ) *
            (bilinear D tau (unitCharge D index.1) : ℂ)) •
            (MvPolynomial.X 1 ^ omega D index * T (MvPolynomial.pderiv index q))) =
        ∑ index ∈ (Finset.univ : Finset (Fin D.rank)) ×ˢ
            Finset.range (LatticeHalfFock.bound D q + 1),
          (-((omega D index : ℕ) : ℂ) *
            (bilinear D tau (unitCharge D index.1) : ℂ)) •
            (MvPolynomial.X 1 ^ omega D index * T (MvPolynomial.pderiv index q)) := by
      apply Finset.sum_subset vars_box
      intro index member absent
      rw [MvPolynomial.pderiv_eq_zero_of_notMem_vars absent, map_zero,
        mul_zero, smul_zero]
    calc
      _ = ∑ k ∈ Finset.range (LatticeHalfFock.bound D q + 1),
          MvPolynomial.X 1 ^ (2 * k + 1) *
            T (∑ colour : Fin D.rank, (tau colour : ℂ) •
              LatticeHalfFock.current D colour (k : ℤ) q) := by
        simp only [map_sum, map_smul, Finset.mul_sum, Finset.smul_sum,
          mul_smul_comm]
        rw [Finset.sum_comm]
      _ = ∑ k ∈ Finset.range (LatticeHalfFock.bound D q + 1),
          ∑ other : Fin D.rank,
            (((k : ℂ) + 1 / 2) * (bilinear D tau (unitCharge D other) : ℂ)) •
              (MvPolynomial.X 1 ^ (2 * k + 1) *
                T (MvPolynomial.pderiv (other, k) q)) := by
        simp only [current_sum, map_sum, map_smul, Finset.mul_sum, mul_smul_comm]
      _ = -(1 / 2 : ℂ) •
          (MvPolynomial.X 1 * MvPolynomial.pderiv 1 (T q)) := by
        rw [pair_euler, pad, Finset.sum_product_right]
        simp only [Finset.smul_sum, smul_smul]
        apply Finset.sum_congr rfl
        intro k member
        apply Finset.sum_congr rfl
        intro other _
        congr 1
        simp only [omega, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
        ring

  have positive_readout :
      (∑ colour : Fin D.rank, (tau colour : ℂ) •
        ∑ k ∈ Finset.range (LatticeHalfFock.bound D p + 1),
          collisionOscillator D sigma tau N (e + 2 * (k : ℤ) + 3)
            (LatticeHalfFock.current D colour (k : ℤ) p)) =
        -(1 / 2 : ℂ) • readout (e + 2)
          (MvPolynomial.X 1 * MvPolynomial.pderiv 1 (T p)) := by
    have h := congrArg (readout (e + 2)) (positive_polynomial p)
    simp only [map_sum, map_smul, readout_second_shift] at h
    have shifts (k : ℕ) : e + 2 + ((2 * k + 1 : ℕ) : ℤ) =
        e + 2 * (k : ℤ) + 3 := by omega
    simpa only [shifts, T, readout, collisionOscillator,
      AlgHom.toLinearMap_apply,
      LinearMap.comp_apply, LinearMap.restrictScalars_apply] using h

  let cutoff : ℕ := (-lower).toNat
  let U (k : ℕ) : Oscillator D :=
    ∑ colour : Fin D.rank, (tau colour : ℂ) • MvPolynomial.X (colour, k)
  let total (d : Fin 2 →₀ ℕ) : ℤ :=
    e + 2 + chargeNorm D (sigma + tau) + 2 * (N : ℤ) + d 0 + d 1
  let creatorDiagonal (d : Fin 2 →₀ ℕ) : Oscillator D :=
    if total d < 0 then 0 else
      ∑ m ∈ Finset.range ((total d).toNat + 1),
        ((((total d - (m : ℤ)) : ℤ) : ℂ) / 2) •
          diagonalTerm D sigma tau N (total d) (d 0) m
  let creatorMoment : Oscillator D :=
    ∑ d ∈ (T p).support, (T p).coeff d * creatorDiagonal d
  have lower_nonpositive : lower ≤ 0 := min_le_right _ _
  have cutoff_cast : (cutoff : ℤ) = -lower :=
    Int.toNat_of_nonneg (by omega)
  have total_bound (d : Fin 2 →₀ ℕ) (member : d ∈ (T p).support) :
      total d < (cutoff : ℤ) := by
    have degree : d 0 + d 1 ≤ translatedDegree D sigma tau p :=
      Finset.le_sup (f := fun d : Fin 2 →₀ ℕ => d 0 + d 1) member
    have degreeCast : (d 0 : ℤ) + d 1 ≤ translatedDegree D sigma tau p := by
      exact_mod_cast degree
    rw [cutoff_cast]
    dsimp [total, lower]
    omega

  /- The two finite diagonals below are compared after multiplying by the
     actual scalar/left-creator coefficient.  No separate copy or exposure
     of the protected signed creation recurrence is introduced. -/
  have negative_diagonal (d : Fin 2 →₀ ℕ) (bounded : total d < (cutoff : ℤ)) :
      (∑ k ∈ Finset.range cutoff, U k *
        collisionDiagonal D sigma tau N (e + 2 - (2 * k + 1 : ℕ)) d) =
        creatorDiagonal d := by
    let L : ℤ := total d
    have shifted_total (k : ℕ) :
        e + 2 - ((2 * k + 1 : ℕ) : ℤ) + chargeNorm D (sigma + tau) +
            2 * (N : ℤ) + (d 0 : ℤ) + d 1 = L - (2 * k + 1 : ℕ) := by
      dsimp [L, total]
      omega
    by_cases negative : L < 0
    · change (∑ k ∈ Finset.range cutoff, U k *
          collisionDiagonal D sigma tau N (e + 2 - (2 * k + 1 : ℕ)) d) =
          if L < 0 then 0 else _
      rw [if_pos negative]
      apply Finset.sum_eq_zero
      intro k member
      simp only [collisionDiagonal, shifted_total,
        if_pos (by omega : L - (2 * k + 1 : ℕ) < 0), mul_zero]
    · have nonnegative : 0 ≤ L := by omega
      have pad (k : ℕ) :
          collisionDiagonal D sigma tau N (e + 2 - (2 * k + 1 : ℕ)) d =
            ∑ m ∈ Finset.range (L.toNat + 1),
              diagonalTerm D sigma tau N (L - (2 * k + 1 : ℕ)) (d 0) m := by
        simp only [collisionDiagonal, shifted_total]
        by_cases outside : L - (2 * k + 1 : ℕ) < 0
        · rw [if_pos outside]
          symm
          apply Finset.sum_eq_zero
          intro m member
          simp [diagonalTerm, halfCreationCoeff,
            show L - (2 * k + 1 : ℕ) - (m : ℤ) < 0 by omega]
          intro hm
          omega
        · rw [if_neg outside]
          apply Finset.sum_subset (Finset.range_mono (by omega))
          intro m member absent
          have large : (L - (2 * k + 1 : ℕ)).toNat < m := by
            have h : ¬ m < (L - (2 * k + 1 : ℕ)).toNat + 1 :=
              by simpa only [Finset.mem_range] using absent
            omega
          simp [diagonalTerm, halfCreationCoeff,
            show L - (2 * k + 1 : ℕ) - (m : ℤ) < 0 by omega]
          intro hm
          omega
      change _ = if L < 0 then 0 else _
      rw [if_neg negative]
      simp_rw [pad, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro m member
      have m_bound : (m : ℤ) ≤ L := by
        have hm := Finset.mem_range.mp member
        omega
      let n : ℤ := L - m
      let prefactor : Oscillator D :=
        collisionScalar ((m : ℤ) - d 0 - chargeNorm D sigma)
          (bilinear D sigma tau) N • halfCreationCoeff D sigma m
      have term (k : ℕ) :
          U k * diagonalTerm D sigma tau N (L - (2 * k + 1 : ℕ)) (d 0) m =
            prefactor * U k * halfCreationCoeff D tau (n - (2 * k + 1 : ℕ)) := by
        dsimp [diagonalTerm, prefactor, n]
        have same : L - (2 * (k : ℤ) + 1) - (m : ℤ) =
            L - (m : ℤ) - (2 * (k : ℤ) + 1) := by ring
        rw [same]
        simp only [smul_mul_assoc, mul_smul_comm]
        congr 1
        ring
      have unshifted : diagonalTerm D sigma tau N L (d 0) m =
          prefactor * halfCreationCoeff D tau n := by
        simp only [diagonalTerm, prefactor, n, smul_mul_assoc]
      simp_rw [term]
      rw [unshifted]
      change (∑ k ∈ Finset.range cutoff,
          prefactor * U k * halfCreationCoeff D tau (n - (2 * k + 1 : ℕ))) =
        ((n : ℂ) / 2) • (prefactor * halfCreationCoeff D tau n)
      have n_nonnegative : 0 ≤ n := by dsimp [n]; omega
      have n_bound : n < (cutoff : ℤ) := by dsimp [n, L] at *; omega
      by_cases n_zero : n = 0
      · simp only [n_zero, Int.cast_zero, zero_div, zero_smul]
        apply Finset.sum_eq_zero
        intro k _
        rw [halfCreationCoeff, if_pos (by omega), mul_zero]
      · let degree : ℕ := n.toNat
        let r : ℕ := degree - 1
        have degree_cast : (degree : ℤ) = n := Int.toNat_of_nonneg n_nonnegative
        have degree_positive : 0 < degree := by omega
        have r_succ : r + 1 = degree := by dsimp [r]; omega
        have degree_le_cutoff : degree ≤ cutoff := by omega
        let driver (j : ℕ) : Oscillator D :=
          PowerSeries.coeff j (PowerSeries.derivative (R := Oscillator D)
            (halfCreationSeries D tau)) * halfCreationCoeff D tau (n - 1 - j)
        have even_driver (k : ℕ) : driver (2 * k) =
            (2 : ℂ) • (U k * halfCreationCoeff D tau (n - (2 * k + 1 : ℕ))) := by
          have even : (2 * k) % 2 = 0 := by omega
          have index : (2 * k) / 2 = k := by omega
          have shift : n - 1 - ((2 * k : ℕ) : ℤ) = n - (2 * k + 1 : ℕ) := by omega
          simp only [driver, series_derivative_coeff, if_pos even, index,
            shift, U, smul_mul_assoc]
        have odd_driver (k : ℕ) : driver (2 * k + 1) = 0 := by
          have odd : ¬ (2 * k + 1) % 2 = 0 := by omega
          simp only [driver, series_derivative_coeff, if_neg odd, zero_mul]
        have pairs (b : ℕ) :
            (∑ j ∈ Finset.range (2 * b), driver j) =
              ∑ k ∈ Finset.range b,
                (2 : ℂ) • (U k * halfCreationCoeff D tau (n - (2 * k + 1 : ℕ))) := by
          induction b with
          | zero => simp
          | succ b previous =>
            rw [show 2 * (b + 1) = (2 * b + 1) + 1 by omega,
              Finset.sum_range_succ, Finset.sum_range_succ, previous,
              Finset.sum_range_succ, even_driver, odd_driver, add_zero]
        have pad_driver : (∑ j ∈ Finset.range degree, driver j) =
            ∑ j ∈ Finset.range (2 * cutoff), driver j := by
          apply Finset.sum_subset (Finset.range_mono (by omega))
          intro j member absent
          have high : degree ≤ j := by simpa only [Finset.mem_range, not_lt] using absent
          have neg : n - 1 - (j : ℤ) < 0 := by omega
          simp only [driver, halfCreationCoeff, if_pos neg, mul_zero]
        have coefficient_product : PowerSeries.coeff r
            (halfCreationExponential D tau *
              PowerSeries.derivative (R := Oscillator D) (halfCreationSeries D tau)) =
            ∑ j ∈ Finset.range degree, driver j := by
          have r_succ' : r.succ = degree := by omega
          rw [mul_comm, PowerSeries.coeff_mul,
            Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, r_succ']
          apply Finset.sum_congr rfl
          intro j member
          have small : j < degree := Finset.mem_range.mp member
          have nonnegative_shift : 0 ≤ n - 1 - (j : ℤ) := by omega
          have index : (n - 1 - (j : ℤ)).toNat = r - j := by dsimp [r]; omega
          simp only [driver, halfCreationCoeff, if_neg (not_lt.mpr nonnegative_shift), index]
        have differentiated := congrArg
          (fun f : PowerSeries (Oscillator D) =>
            (1 / 2 : ℂ) • (prefactor * PowerSeries.coeff r f))
          (exponential_derivative D tau)
        have left_coefficient :
            (1 / 2 : ℂ) • (prefactor * PowerSeries.coeff r
              (PowerSeries.derivative (R := Oscillator D) (halfCreationExponential D tau))) =
              ((n : ℂ) / 2) • (prefactor * halfCreationCoeff D tau n) := by
          have scaled_coefficient : PowerSeries.coeff r
              (PowerSeries.derivative (R := Oscillator D) (halfCreationExponential D tau)) =
              (degree : ℂ) • PowerSeries.coeff degree (halfCreationExponential D tau) := by
            have cast_degree : (r : Oscillator D) + 1 = (degree : Oscillator D) := by
              exact_mod_cast r_succ
            rw [PowerSeries.coeff_derivative, r_succ, cast_degree]
            simp only [Algebra.smul_def, map_natCast]
            ring
          rw [scaled_coefficient, halfCreationCoeff,
            if_neg (not_lt.mpr n_nonnegative)]
          simp only [degree, mul_smul_comm, smul_smul]
          congr 1
          have complex_degree : (degree : ℂ) = (n : ℂ) := by exact_mod_cast degree_cast
          change (1 / 2 : ℂ) * (degree : ℂ) = (n : ℂ) / 2
          rw [complex_degree]
          ring
        rw [left_coefficient, coefficient_product, pad_driver, pairs] at differentiated
        simp only [Finset.mul_sum, Finset.smul_sum, mul_smul_comm,
          smul_smul, show (1 / 2 : ℂ) * 2 = 1 by norm_num, one_smul] at differentiated
        simpa only [mul_assoc] using differentiated.symm

  have readout_expansion (z : ℤ) (Q : PairPolynomial D) :
      readout z Q = ∑ d ∈ Q.support,
        Q.coeff d * collisionDiagonal D sigma tau N z d := by
    rfl
  have negative_readout :
      (∑ colour : Fin D.rank, (tau colour : ℂ) •
        ∑ k ∈ Finset.range cutoff,
          MvPolynomial.X (colour, k) *
            collisionOscillator D sigma tau N (e + 2 - (2 * k + 1 : ℕ)) p) =
        creatorMoment := by
    calc
      _ = ∑ k ∈ Finset.range cutoff,
          U k * readout (e + 2 - (2 * k + 1 : ℕ)) (T p) := by
        simp only [U, Finset.sum_mul, smul_mul_assoc, Finset.smul_sum,
          collisionOscillator, readout, T, LinearMap.comp_apply,
          LinearMap.restrictScalars_apply]
        exact Finset.sum_comm
      _ = ∑ d ∈ (T p).support, (T p).coeff d *
          ∑ k ∈ Finset.range cutoff, U k *
            collisionDiagonal D sigma tau N (e + 2 - (2 * k + 1 : ℕ)) d := by
        simp only [readout_expansion, Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro d member
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = creatorMoment := by
        apply Finset.sum_congr rfl
        intro d member
        rw [negative_diagonal d (total_bound d member)]

  have moment_decomposition : collisionMoment D sigma tau N e p =
      creatorMoment - (1 / 2 : ℂ) •
        readout (e + 2) (MvPolynomial.X 1 * MvPolynomial.pderiv 1 (T p)) := by
    rw [readout_euler]
    change (∑ d ∈ (T p).support, (T p).coeff d *
        (if total d < 0 then 0 else
          ∑ m ∈ Finset.range ((total d).toNat + 1),
            ((((total d - (m : ℤ) - (d 1 : ℤ)) : ℤ) : ℂ) / 2) •
              diagonalTerm D sigma tau N (total d) (d 0) m)) = _
    dsimp only [creatorMoment]
    rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d member
    have ordinary_diagonal : collisionDiagonal D sigma tau N (e + 2) d =
        if total d < 0 then 0 else
          ∑ m ∈ Finset.range ((total d).toNat + 1),
            diagonalTerm D sigma tau N (total d) (d 0) m := by rfl
    rw [ordinary_diagonal]
    dsimp only [creatorDiagonal]
    by_cases negative : total d < 0
    · simp only [if_pos negative, mul_zero, smul_zero, sub_zero]
    · simp only [if_neg negative, Finset.mul_sum, Finset.smul_sum,
        mul_smul_comm, smul_smul]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro m mMember
      rw [← sub_smul]
      congr 1
      push_cast
      ring

  have mode_split (colour : Fin D.rank) :
      (∑ modes ∈ support colour, oscillatorTerm colour modes) =
        (∑ k ∈ Finset.range cutoff, MvPolynomial.X (colour, k) *
          collisionOscillator D sigma tau N (e + 2 - (2 * k + 1 : ℕ)) p) +
        ∑ k ∈ Finset.range (LatticeHalfFock.bound D p + 1),
          collisionOscillator D sigma tau N (e + 2 * (k : ℤ) + 3)
            (LatticeHalfFock.current D colour (k : ℤ) p) := by
    let negativeModes : Finset ℤ := (Finset.range cutoff).image (fun k : ℕ => -(k : ℤ) - 1)
    let positiveModes : Finset ℤ :=
      (Finset.range (LatticeHalfFock.bound D p + 1)).image (fun k : ℕ => (k : ℤ))
    have cover : Finset.Icc lower (LatticeHalfFock.bound D p : ℤ) =
        negativeModes ∪ positiveModes := by
      ext j
      simp only [Finset.mem_Icc, Finset.mem_union, negativeModes, positiveModes,
        Finset.mem_image, Finset.mem_range]
      constructor
      · intro bounds
        by_cases sign : j < 0
        · left
          refine ⟨(-j - 1).toNat, ?_, ?_⟩ <;> omega
        · right
          refine ⟨j.toNat, ?_, ?_⟩ <;> omega
      · rintro (⟨k, within, rfl⟩ | ⟨k, within, rfl⟩) <;> constructor <;> omega
    have disjoint : Disjoint negativeModes positiveModes := by
      apply Finset.disjoint_left.mpr
      intro j left right
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp left
      obtain ⟨l, hl, eq⟩ := Finset.mem_image.mp right
      omega
    change (∑ modes ∈ (Finset.Icc lower (LatticeHalfFock.bound D p : ℤ)).product {()},
      oscillatorTerm colour modes) = _
    have productSum :
        (∑ modes ∈ (Finset.Icc lower (LatticeHalfFock.bound D p : ℤ)).product {()},
          oscillatorTerm colour modes) =
          ∑ mode ∈ Finset.Icc lower (LatticeHalfFock.bound D p : ℤ),
            ∑ unit ∈ ({()} : Finset Unit), oscillatorTerm colour (mode, unit) := by
      calc
        _ = ∑ modes ∈ (Finset.Icc lower (LatticeHalfFock.bound D p : ℤ)).product {()},
            oscillatorTerm colour (modes.1, modes.2) := by
          apply Finset.sum_congr rfl
          intro modes member
          cases modes
          rfl
        _ = _ := by
          exact Finset.sum_product'
            (s := Finset.Icc lower (LatticeHalfFock.bound D p : ℤ))
            (t := ({()} : Finset Unit))
            (f := fun mode unit => oscillatorTerm colour (mode, unit))
    rw [productSum]
    simp only [Finset.sum_singleton]
    rw [cover, Finset.sum_union disjoint]
    rw [Finset.sum_image (by
      intro a ha b hb equality
      have equality' : (a : ℤ) = (b : ℤ) := by linarith [equality]
      exact_mod_cast equality'),
      Finset.sum_image (by
        intro a ha b hb equality
        have equality' : (a : ℤ) = (b : ℤ) := by
          simpa only using equality
        exact_mod_cast equality')]
    congr 1
    · apply Finset.sum_congr rfl
      intro k member
      have negative : -(k : ℤ) - 1 < 0 := by omega
      have shift : e + 2 * (-(k : ℤ) - 1) + 3 =
          e + 2 - (2 * k + 1 : ℕ) := by omega
      simp only [oscillatorTerm, if_pos negative, LatticeHalfFock.current_negative,
        LinearMap.mulLeft_apply, shift]
  simp_rw [mode_split, smul_add]
  rw [Finset.sum_add_distrib, negative_readout, positive_readout, moment_decomposition]
  rw [neg_smul, sub_eq_add_neg]

end
end D5.S3.VertexAlgebra.LatticeHalfFockChargedCollision
