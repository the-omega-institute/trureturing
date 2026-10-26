/- GID: D5/S3/VertexAlgebra/ChargedResidue/Reflections
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/ChargedResidue/Reflections
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Coordinate reflections preserve actual translated support with exact coefficient characters. -/
import D5.S3.VertexAlgebra.ChargedResidue.SupportedResidue

/-! Odd coordinate reflections preserve translated supports and tensor diagonals. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

namespace D5.S3.VertexAlgebra.LatticeHalfFockChargedResidue
open LatticeGeneratingFieldLocality LatticeHalfFockChargedCoefficients
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockProductKernel
open LatticeFiniteNegativeGeneration LatticeHalfFockChargedCollision
open scoped BigOperators TensorProduct
noncomputable section

private def scalePair {R : Type*} [CommRing R] (a b : R) :
    MvPolynomial (Fin 2) R →+* MvPolynomial (Fin 2) R :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (fun i => MvPolynomial.C (if i = 0 then a else b) * MvPolynomial.X i)

private theorem scalePair_monomial {R : Type*} [CommRing R] (a b c : R)
    (d : Fin 2 →₀ ℕ) :
    scalePair a b (MvPolynomial.monomial d c) =
      MvPolynomial.monomial d ((a^(d 0)*b^(d 1))*c) := by
  rw [scalePair, MvPolynomial.eval₂Hom_monomial, MvPolynomial.monomial_eq]
  rw [Finsupp.prod_fintype _ _ (by simp), Finsupp.prod_fintype _ _ (by simp)]
  simp only [Fin.prod_univ_two, Fin.isValue, ite_true, show (1 : Fin 2) ≠ 0 by decide,
    ite_false, mul_pow, ← map_pow]
  simp only [map_mul]
  ring

private theorem scalePair_coeff {R : Type*} [CommRing R] (a b : R)
    (p : MvPolynomial (Fin 2) R) (d : Fin 2 →₀ ℕ) :
    (scalePair a b p).coeff d = (a^(d 0)*b^(d 1))*p.coeff d := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial e c =>
    rw [scalePair_monomial]
    by_cases same : e = d
    · simp [same]
    · simp [MvPolynomial.coeff_monomial, same, Ne.symm same]
  | add p q hp hq => simp only [map_add, MvPolynomial.coeff_add, hp, hq, mul_add]

private theorem scalePair_support (D : LatticeData) (a b : Oscillator D)
    (ha : a ≠ 0) (hb : b ≠ 0) (p : PairPolynomial D) :
    (scalePair a b p).support = p.support := by
  ext d
  simp only [MvPolynomial.mem_support_iff, scalePair_coeff, ne_eq,
    mul_eq_zero, pow_eq_zero_iff', ha, hb, false_and, false_or]

private theorem translation_scale_right (D : LatticeData) (left right : Charge D)
    (p : Oscillator D) :
    pairTranslation D left (-right) p = scalePair 1 (-1) (pairTranslation D left right p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [pairTranslation, scalePair]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    have odd : Odd (omega D i) := ⟨i.2, by simp [omega, two_mul]⟩
    simp only [map_mul, hp, pairTranslation, MvPolynomial.eval₂AlgHom_X]
    congr 1
    simp [pairTranslationVariable, scalePair, bilinear_neg_left, bilinear_neg_right,
      odd.neg_pow, mul_pow, sub_eq_add_neg]

private theorem translation_scale_left (D : LatticeData) (left right : Charge D)
    (p : Oscillator D) :
    pairTranslation D (-left) right p = scalePair (-1) 1 (pairTranslation D left right p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [pairTranslation, scalePair]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    have odd : Odd (omega D i) := ⟨i.2, by simp [omega, two_mul]⟩
    simp only [map_mul, hp, pairTranslation, MvPolynomial.eval₂AlgHom_X]
    congr 1
    simp [pairTranslationVariable, scalePair, bilinear_neg_left, bilinear_neg_right,
      odd.neg_pow, mul_pow, sub_eq_add_neg]

private theorem translation_right_coeff (D : LatticeData) (left right : Charge D)
    (p : Oscillator D) (d : Fin 2 →₀ ℕ) :
    (pairTranslation D left (-right) p).coeff d =
      ((-1 : ℂ)^(d 1 : ℤ)) • (pairTranslation D left right p).coeff d := by
  rw [translation_scale_right, scalePair_coeff]
  simp only [one_pow, one_mul, zpow_natCast]
  rw [← MvPolynomial.C_mul']
  congr 1
  simp

private theorem translation_left_coeff (D : LatticeData) (left right : Charge D)
    (p : Oscillator D) (d : Fin 2 →₀ ℕ) :
    (pairTranslation D (-left) right p).coeff d =
      ((-1 : ℂ)^(d 0 : ℤ)) • (pairTranslation D left right p).coeff d := by
  rw [translation_scale_left, scalePair_coeff]
  simp only [one_pow, mul_one, zpow_natCast]
  rw [← MvPolynomial.C_mul']
  congr 1
  simp

private theorem translation_right_support (D : LatticeData) (left right : Charge D)
    (p : Oscillator D) :
    (pairTranslation D left (-right) p).support = (pairTranslation D left right p).support := by
  rw [translation_scale_right]
  exact scalePair_support D 1 (-1) one_ne_zero (neg_ne_zero.mpr one_ne_zero) _

private theorem translation_left_support (D : LatticeData) (left right : Charge D)
    (p : Oscillator D) :
    (pairTranslation D (-left) right p).support = (pairTranslation D left right p).support := by
  rw [translation_scale_left]
  exact scalePair_support D (-1) 1 (neg_ne_zero.mpr one_ne_zero) one_ne_zero _

private theorem sign_congr (a b : ℤ) (h : Even (a-b)) :
    (-1 : ℂ)^a = (-1 : ℂ)^b := by
  have one := h.neg_one_zpow (α := ℂ)
  rw [zpow_sub₀ (by norm_num : (-1 : ℂ) ≠ 0)] at one
  exact (div_eq_one_iff_eq (zpow_ne_zero _ (by norm_num))).mp one

private theorem double_phase (D : LatticeData) (sigma tau : Charge D)
    (gamma delta r n : ℤ) (d : Fin 2 →₀ ℕ) :
    (-1 : ℂ)^((d 0 : ℤ)+d 1+physicalCreationTotal D sigma tau gamma delta r n d) =
      (-1 : ℂ)^(gamma+delta) := by
  apply sign_congr
  obtain ⟨a, ha⟩ := LatticeHalfFockChargedMonodromy.norm_even D sigma
  obtain ⟨b, hb⟩ := LatticeHalfFockChargedMonodromy.norm_even D tau
  refine ⟨-(r+n)-gamma-delta-2+a+b+d 0+d 1, ?_⟩
  dsimp [physicalCreationTotal]
  omega

private theorem double_diagonal (D : LatticeData) (sigma tau : Charge D)
    (gamma delta r n : ℤ) (N : ℕ) (d : Fin 2 →₀ ℕ) :
    transformedCollisionDiagonal D (-sigma) (-tau) gamma delta r n N d =
      (-1 : ℂ)^(physicalCreationTotal D sigma tau gamma delta r n d) •
        transformedCollisionDiagonal D sigma tau gamma delta r n N d := by
  classical
  have total : physicalCreationTotal D (-sigma) (-tau) gamma delta r n d =
      physicalCreationTotal D sigma tau gamma delta r n d := by
    simp only [physicalCreationTotal, LatticeHalfFockChargedMonodromy.norm_neg]
  unfold transformedCollisionDiagonal
  rw [total]
  by_cases neg : physicalCreationTotal D sigma tau gamma delta r n d < 0
  · simp only [ite_eq_left neg, smul_zero]
  · simp only [ite_eq_right neg, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    rw [LatticeHalfFockChargedMonodromy.norm_neg, bilinear_neg_left, bilinear_neg_right,
      neg_neg, LatticeHalfFockChargedMonodromy.creation_neg,
      LatticeHalfFockChargedMonodromy.creation_neg, smul_mul_assoc, mul_smul_comm,
      smul_smul]
    simp only [smul_smul]
    congr 1
    rw [mul_assoc, ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0),
      show (m : ℤ)+(physicalCreationTotal D sigma tau gamma delta r n d-m) =
        physicalCreationTotal D sigma tau gamma delta r n d by omega]
    ring

/- proof_shape: transformedCollisionKernel_double_reflection: content
   admission_basis: escape-witness
   escape_witness: Odd coordinate frequencies give support-preserving characters
   on both translated variables. Their combined character cancels the creation
   character using even lattice norms, retaining both arbitrary input degrees.
   literature_status: classical twisted-lattice coordinate monodromy. -/
theorem transformedCollisionKernel_double_reflection (D : LatticeData)
    (hu : IsUnit D.G.det) (sigma tau : Charge D) (gamma delta r n : ℤ)
    (l : ℕ) (p : Oscillator D) (g : ActualGround D hu) :
    transformedCollisionKernel D hu (-sigma) (-tau) gamma delta r n l p g =
      (-1 : ℂ)^(gamma+delta) •
        transformedCollisionKernel D hu sigma tau gamma delta r n l p g := by
  classical
  unfold transformedCollisionKernel
  simp only [bilinear_neg_left, bilinear_neg_right, neg_neg,
    chargeScalar, LatticeHalfFockChargedMonodromy.norm_neg,
    LatticeHalfFockChargedMonodromy.ground_neg]
  by_cases neg : -(r+(l : ℤ))-1-bilinear D sigma tau < 0
  · simp only [ite_eq_left neg, smul_zero]
  · simp only [ite_eq_right neg]
    rw [smul_comm ((-1 : ℂ)^(gamma+delta)), TensorProduct.smul_tmul' ((-1 : ℂ)^(gamma+delta))]
    apply congrArg (fun O : Oscillator D =>
      ((2 : ℂ)^(-chargeNorm D sigma)*(2 : ℂ)^(-chargeNorm D tau)*
        (2 : ℂ)^(-2*bilinear D sigma tau)) •
        (O ⊗ₜ[ℂ] groundAction D hu sigma (groundAction D hu tau g)))
    rw [translation_left_support, translation_right_support, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    rw [translation_left_coeff, translation_right_coeff, double_diagonal,
      smul_smul, smul_mul_assoc, mul_smul_comm, smul_smul,
      ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0),
      ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), double_phase]


private def creationAggregate (D : LatticeData) (sigma tau : Charge D)
    (gamma delta r n : ℤ) (p : Oscillator D)
    (w : (Fin 2 →₀ ℕ) → ℤ → ℂ) : Oscillator D :=
  ∑ d ∈ (pairTranslation D sigma tau p).support,
    (pairTranslation D sigma tau p).coeff d *
      (if physicalCreationTotal D sigma tau gamma delta r n d < 0 then 0 else
        ∑ m ∈ Finset.range ((physicalCreationTotal D sigma tau gamma delta r n d).toNat+1),
          w d m • (halfCreationCoeff D sigma m *
            halfCreationCoeff D tau (physicalCreationTotal D sigma tau gamma delta r n d-m)))

private def poleWeight (q B a : ℤ) : ℂ :=
  (2 : ℂ)^(-2*B) *
    (if -q-1-B < 0 then 0 else collisionScalar a B (-q-1-B).toNat)

private theorem right_phase (D : LatticeData) (sigma tau : Charge D)
    (gamma delta q z m : ℤ) (d : Fin 2 →₀ ℕ) :
    (-1 : ℂ)^delta *
        (-1 : ℂ)^((d 1 : ℤ)+physicalCreationTotal D sigma tau gamma delta q z d-m) =
      (-1 : ℂ)^(m-(-2*q-gamma-2+chargeNorm D sigma+d 0)) := by
  rw [← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
  apply sign_congr
  obtain ⟨b, hb⟩ := LatticeHalfFockChargedMonodromy.norm_even D tau
  refine ⟨-2*q-z-gamma-3+chargeNorm D sigma+b+d 0+d 1-m, ?_⟩
  dsimp [physicalCreationTotal]
  omega

private theorem kernel_as_aggregate (D : LatticeData) (hu : IsUnit D.G.det)
    (sigma tau : Charge D) (gamma delta r n : ℤ) (l : ℕ)
    (p : Oscillator D) (g : ActualGround D hu) :
    transformedCollisionKernel D hu sigma tau gamma delta r n l p g =
      (chargeScalar D sigma * chargeScalar D tau) •
        (creationAggregate D sigma tau gamma delta r n p
          (fun d m => poleWeight (r+l) (bilinear D sigma tau)
            (m-d 0-chargeNorm D sigma+gamma)) ⊗ₜ[ℂ]
          groundAction D hu sigma (groundAction D hu tau g)) := by
  classical
  unfold transformedCollisionKernel poleWeight
  by_cases neg : -(r+(l : ℤ))-1-bilinear D sigma tau < 0
  · simp only [ite_eq_left neg, creationAggregate, mul_zero, zero_smul,
      Finset.sum_const_zero, ite_self, TensorProduct.zero_tmul, smul_zero]
  · simp only [ite_eq_right neg]
    rw [mul_smul, TensorProduct.smul_tmul' ((2 : ℂ)^(-2*bilinear D sigma tau))]
    apply congrArg (fun O : Oscillator D => (chargeScalar D sigma * chargeScalar D tau) •
      (O ⊗ₜ[ℂ] groundAction D hu sigma (groundAction D hu tau g)))
    unfold creationAggregate transformedCollisionDiagonal
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    by_cases total : physicalCreationTotal D sigma tau gamma delta r n d < 0
    · simp [total]
    · simp only [ite_eq_right total]
      rw [← mul_smul_comm]
      simp only [Finset.smul_sum, smul_smul]

private theorem right_kernel_as_aggregate (D : LatticeData) (hu : IsUnit D.G.det)
    (sigma tau : Charge D) (gamma delta r n : ℤ) (l : ℕ)
    (p : Oscillator D) (g : ActualGround D hu) :
    (-1 : ℂ)^delta • transformedCollisionKernel D hu sigma (-tau) gamma delta r n l p g =
      (chargeScalar D sigma * chargeScalar D tau) •
        (creationAggregate D sigma tau gamma delta r n p
          (fun d m => (-1 : ℂ)^(m-(-2*(r+l)-gamma-2+chargeNorm D sigma+d 0)) *
            poleWeight (r+l) (-bilinear D sigma tau)
              (m-d 0-chargeNorm D sigma+gamma)) ⊗ₜ[ℂ]
          groundAction D hu sigma (groundAction D hu tau g)) := by
  classical
  rw [kernel_as_aggregate]
  simp only [chargeScalar, LatticeHalfFockChargedMonodromy.norm_neg,
    LatticeHalfFockChargedMonodromy.ground_neg]
  rw [smul_comm ((-1 : ℂ)^delta), TensorProduct.smul_tmul' ((-1 : ℂ)^delta)]
  apply congrArg (fun O : Oscillator D =>
    ((2 : ℂ)^(-chargeNorm D sigma)*(2 : ℂ)^(-chargeNorm D tau)) •
      (O ⊗ₜ[ℂ] groundAction D hu sigma (groundAction D hu tau g)))
  unfold creationAggregate
  rw [translation_right_support, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [translation_right_coeff]
  have total : physicalCreationTotal D sigma (-tau) gamma delta r n d =
      physicalCreationTotal D sigma tau gamma delta r n d := by
    simp only [physicalCreationTotal, LatticeHalfFockChargedMonodromy.norm_neg]
  rw [total]
  by_cases neg : physicalCreationTotal D sigma tau gamma delta r n d < 0
  · simp [neg]
  · simp only [ite_eq_right neg, Finset.smul_sum, mul_smul_comm, Finset.mul_sum,
      smul_mul_assoc]
    apply Finset.sum_congr rfl
    intro m hm
    rw [LatticeHalfFockChargedMonodromy.creation_neg]
    simp only [mul_smul_comm, smul_smul, bilinear_neg_right]
    have phase := right_phase D sigma tau gamma delta (r+l) (n-l) m d
    have total_eq : physicalCreationTotal D sigma tau gamma delta (r+l) (n-l) d =
        physicalCreationTotal D sigma tau gamma delta r n d := by
      unfold physicalCreationTotal
      ring
    rw [total_eq] at phase
    congr 1
    calc
      _ = ((-1 : ℂ)^delta * (-1 : ℂ)^((d 1 : ℤ)+
        physicalCreationTotal D sigma tau gamma delta r n d-m)) *
          poleWeight (r+l) (-bilinear D sigma tau)
            ((m : ℤ)-d 0-chargeNorm D sigma+gamma) := by
        rw [show (d 1 : ℤ)+physicalCreationTotal D sigma tau gamma delta r n d-m =
          (d 1 : ℤ)+(physicalCreationTotal D sigma tau gamma delta r n d-m) by ring,
          zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
        ring
      _ = _ := by rw [phase]



private theorem reflected_pair_diagonal (D : LatticeData) (hu : IsUnit D.G.det)
    (sigma tau : Charge D) (gamma delta r n : ℤ) (l : ℕ)
    (p : Oscillator D) (g : ActualGround D hu) :
    (1/2 : ℂ) • (transformedCollisionKernel D hu sigma tau gamma delta r n l p g +
      (-1 : ℂ)^delta • transformedCollisionKernel D hu sigma (-tau) gamma delta r n l p g) =
      (chargeScalar D sigma * chargeScalar D tau) •
        ((∑ d ∈ (pairTranslation D sigma tau p).support,
          (pairTranslation D sigma tau p).coeff d *
            physicalResidueCollisionDiagonal D sigma tau gamma delta (r+l) (n-l) d)
          ⊗ₜ[ℂ] groundAction D hu sigma (groundAction D hu tau g)) := by
  classical
  rw [right_kernel_as_aggregate, kernel_as_aggregate, ← smul_add,
    ← TensorProduct.add_tmul, smul_comm (1/2 : ℂ), TensorProduct.smul_tmul' (1/2 : ℂ)]
  apply congrArg (fun O : Oscillator D => (chargeScalar D sigma * chargeScalar D tau) •
    (O ⊗ₜ[ℂ] groundAction D hu sigma (groundAction D hu tau g)))
  unfold creationAggregate
  rw [← Finset.sum_add_distrib, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have total : physicalCreationTotal D sigma tau gamma delta (r+l) (n-l) d =
      physicalCreationTotal D sigma tau gamma delta r n d := by
    dsimp [physicalCreationTotal]
    congr 1 <;> ring
  unfold physicalResidueCollisionDiagonal
  rw [total]
  by_cases neg : physicalCreationTotal D sigma tau gamma delta r n d < 0
  · simp only [ite_eq_left neg, mul_zero, add_zero, smul_zero]
  · simp only [ite_eq_right neg]
    rw [← mul_add, ← mul_smul_comm, ← Finset.sum_add_distrib, Finset.smul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro m hm
    rw [← add_smul, smul_smul]
    congr 1
    have exponent : (m : ℤ)-(-2*(r+l)-gamma-2+chargeNorm D sigma+d 0)-2*(r+l)-2 =
        (m : ℤ)-d 0-chargeNorm D sigma+gamma := by ring
    simp only [twoPoleScalar, poleWeight, exponent, mul_neg, neg_neg]
    ring

/- proof_shape: charged_reflected_collision_diagonal: content
   admission_basis: escape-witness
   escape_witness: The four actual reflected kernels reduce to two local poles
   using both matching lift equations, support-preserving coordinate characters,
   even lattice norms and unchanged actual ground actions. The scalar two-pole
   weights then give precisely the complete residue creation diagonal.
   literature_status: classical twisted-lattice residue comparison. -/
theorem charged_reflected_collision_diagonal (D : LatticeData) (hu : IsUnit D.G.det)
    (sigma tau : Charge D) (epsilon eta : Bool) (gamma delta r n : ℤ)
    (hgamma : (-1 : ℂ)^gamma = projectedSign epsilon)
    (hdelta : (-1 : ℂ)^delta = projectedSign eta)
    (l : ℕ) (p : Oscillator D) (g : ActualGround D hu) :
    (1/4 : ℂ) • (transformedCollisionKernel D hu sigma tau gamma delta r n l p g +
      projectedSign eta • transformedCollisionKernel D hu sigma (-tau) gamma delta r n l p g +
      projectedSign epsilon • transformedCollisionKernel D hu (-sigma) tau gamma delta r n l p g +
      (projectedSign epsilon * projectedSign eta) •
        transformedCollisionKernel D hu (-sigma) (-tau) gamma delta r n l p g) =
      (chargeScalar D sigma * chargeScalar D tau) •
        ((∑ d ∈ (pairTranslation D sigma tau p).support,
          (pairTranslation D sigma tau p).coeff d *
            physicalResidueCollisionDiagonal D sigma tau gamma delta (r+l) (n-l) d)
          ⊗ₜ[ℂ] groundAction D hu sigma (groundAction D hu tau g)) := by
  have phase : (-1 : ℂ)^(gamma+delta) = projectedSign epsilon * projectedSign eta := by
    rw [zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), hgamma, hdelta]
  have sqE : projectedSign epsilon * projectedSign epsilon = 1 := by
    cases epsilon <;> norm_num [projectedSign]
  have sqT : projectedSign eta * projectedSign eta = 1 := by
    cases eta <;> norm_num [projectedSign]
  have sqET : (projectedSign epsilon * projectedSign eta) *
      (projectedSign epsilon * projectedSign eta) = 1 := by
    calc
      _ = (projectedSign epsilon * projectedSign epsilon) *
        (projectedSign eta * projectedSign eta) := by ring
      _ = 1 := by rw [sqE, sqT, one_mul]
  have both := transformedCollisionKernel_double_reflection D hu sigma tau gamma delta r n l p g
  have left := transformedCollisionKernel_double_reflection D hu sigma (-tau) gamma delta r n l p g
  simp only [neg_neg, phase] at left both
  rw [both, left, smul_smul, smul_smul,
    show projectedSign epsilon * (projectedSign epsilon * projectedSign eta) =
      projectedSign eta by rw [← mul_assoc, sqE, one_mul], sqET, one_smul]
  calc
    _ = (1/2 : ℂ) • (transformedCollisionKernel D hu sigma tau gamma delta r n l p g +
      projectedSign eta • transformedCollisionKernel D hu sigma (-tau) gamma delta r n l p g) := by module
    _ = _ := by rw [← hdelta]; exact reflected_pair_diagonal D hu sigma tau gamma delta r n l p g


end
end D5.S3.VertexAlgebra.LatticeHalfFockChargedResidue
