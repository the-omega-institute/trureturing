/- GID: D5/S3/VertexAlgebra/ChargedResidue/CollisionTransform
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/ChargedResidue/CollisionTransform
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The finite physical binomial transform has a common signed creation diagonal. -/

import D5.S3.VertexAlgebra.ChargedResidue.Native

/-! Supported collision diagonals for the physical binomial change of variables. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

namespace D5.S3.VertexAlgebra.LatticeHalfFockChargedResidue
open LatticeGeneratingFieldLocality LatticeHalfFockChargedTensorCoefficients
open LatticeHalfFockChargedCoefficients LatticeHalfFockChargedCollision
open scoped BigOperators TensorProduct VertexOperator
noncomputable section

private theorem scalar_binomial_shift (a B gamma : ℤ) (N : ℕ) :
    (∑ k ∈ Finset.range (N+1), Ring.choose ((gamma : ℂ)/2) k *
      collisionScalar a B (N-k)) = collisionScalar (a+gamma) B N := by
  have exponent : ((a+gamma : ℤ) : ℂ)/2 = (gamma : ℂ)/2 + (a : ℂ)/2 := by
    push_cast
    ring
  unfold collisionScalar
  rw [exponent, PowerSeries.binomialSeries_add, mul_assoc, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [PowerSeries.binomialSeries_coeff, smul_eq_mul, mul_one]

private theorem norm_add (D : LatticeData) (sigma tau : Charge D) :
    chargeNorm D (sigma+tau) = chargeNorm D sigma + chargeNorm D tau +
      2 * bilinear D sigma tau := by
  have left (a b c : Charge D) : bilinear D (a+b) c =
      bilinear D a c + bilinear D b c := by
    simp [bilinear, add_mul, Finset.sum_add_distrib]
  have right (a b c : Charge D) : bilinear D a (b+c) =
      bilinear D a b + bilinear D a c := by
    simp [bilinear, mul_add, Finset.sum_add_distrib]
  unfold chargeNorm
  rw [left, right, right, LatticeFiniteNegativeGeneration.bilinear_symmetric D tau sigma]
  ring

def physicalCreationTotal (D : LatticeData) (sigma tau : Charge D)
    (gamma delta r n : ℤ) (d : Fin 2 →₀ ℕ) : ℤ :=
  -2*(r+n)-gamma-delta-4 + chargeNorm D sigma + chargeNorm D tau + d 0 + d 1

def transformedCollisionDiagonal (D : LatticeData) (sigma tau : Charge D)
    (gamma delta r n : ℤ) (N : ℕ) (d : Fin 2 →₀ ℕ) : Oscillator D :=
  let total := physicalCreationTotal D sigma tau gamma delta r n d
  if total < 0 then 0 else
    ∑ m ∈ Finset.range (total.toNat+1),
      collisionScalar ((m : ℤ)-(d 0 : ℤ)-chargeNorm D sigma+gamma)
        (bilinear D sigma tau) N •
        (halfCreationCoeff D sigma (m : ℤ) * halfCreationCoeff D tau (total-m))

set_option maxHeartbeats 4000000 in
private theorem diagonal_binomial_shift (D : LatticeData) (sigma tau : Charge D)
    (gamma delta r n : ℤ) (l N : ℕ)
    (degree : (N : ℤ) = -(r + (l : ℤ)) - 1 - bilinear D sigma tau)
    (d : Fin 2 →₀ ℕ) :
    (∑ k ∈ Finset.range (N+1), Ring.choose ((gamma : ℂ)/2) k •
      collisionDiagonal D sigma tau (N-k)
        (chargedPhysicalOutputExponent gamma delta n ((l+k : ℕ) : ℤ)) d) =
      transformedCollisionDiagonal D sigma tau gamma delta r n N d := by
  classical
  have total (k : ℕ) (member : k ∈ Finset.range (N+1)) :
      chargedPhysicalOutputExponent gamma delta n ((l+k : ℕ) : ℤ) +
        chargeNorm D (sigma+tau) + 2*((N-k : ℕ) : ℤ) + d 0 + d 1 =
      physicalCreationTotal D sigma tau gamma delta r n d := by
    have within := Finset.mem_range.mp member
    rw [norm_add]
    dsimp [chargedPhysicalOutputExponent, physicalCreationTotal]
    omega
  have expand (k : ℕ) (member : k ∈ Finset.range (N+1)) :
      collisionDiagonal D sigma tau (N-k)
        (chargedPhysicalOutputExponent gamma delta n ((l+k : ℕ) : ℤ)) d =
      if physicalCreationTotal D sigma tau gamma delta r n d < 0 then 0 else
        ∑ m ∈ Finset.range ((physicalCreationTotal D sigma tau gamma delta r n d).toNat+1),
          diagonalTerm D sigma tau (N-k)
            (physicalCreationTotal D sigma tau gamma delta r n d) (d 0) m := by
    unfold collisionDiagonal
    rw [total k member]
  rw [Finset.sum_congr rfl (fun k hk => congrArg
    (fun z : Oscillator D => Ring.choose ((gamma : ℂ)/2) k • z) (expand k hk))]
  unfold transformedCollisionDiagonal
  by_cases negative : physicalCreationTotal D sigma tau gamma delta r n d < 0
  · simp only [ite_eq_left negative, smul_zero, Finset.sum_const_zero]
  · simp only [ite_eq_right negative]
    simp_rw [Finset.smul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro m member
    simp only [diagonalTerm, smul_smul]
    rw [← Finset.sum_smul, scalar_binomial_shift]

set_option maxHeartbeats 4000000 in
private theorem collision_tensor_normalization (D : LatticeData) (hu : IsUnit D.G.det)
    (sigma tau : Charge D) (q : Oscillator D) (g : ActualGround D hu) :
    (epsilon D sigma tau * chargeScalar D (sigma+tau)) •
        (q ⊗ₜ[ℂ] groundAction D hu (sigma+tau) g) =
      (chargeScalar D sigma * chargeScalar D tau * (2 : ℂ)^(-2*bilinear D sigma tau)) •
        (q ⊗ₜ[ℂ] groundAction D hu sigma (groundAction D hu tau g)) := by
  have scalar : chargeScalar D sigma * chargeScalar D tau *
      (2 : ℂ)^(-2*bilinear D sigma tau) = chargeScalar D (sigma+tau) := by
    unfold chargeScalar
    rw [← zpow_add₀ (by norm_num : (2 : ℂ) ≠ 0),
      ← zpow_add₀ (by norm_num : (2 : ℂ) ≠ 0), norm_add]
    congr 1
    ring
  have product := congrArg (fun T : Module.End ℂ (ActualGround D hu) => T g)
    (LatticeHalfFockGroundProducts.ground_action_product D hu sigma tau)
  change groundAction D hu sigma (groundAction D hu tau g) =
    epsilon D sigma tau • groundAction D hu (sigma+tau) g at product
  rw [scalar, product, TensorProduct.tmul_smul, smul_smul, mul_comm]

def transformedCollisionKernel (D : LatticeData) (hu : IsUnit D.G.det)
    (sigma tau : Charge D) (gamma delta r n : ℤ) (l : ℕ)
    (p : Oscillator D) (g : ActualGround D hu) : ActualTensor D hu :=
  let degree := -(r + (l : ℤ)) - 1 - bilinear D sigma tau
  if degree < 0 then 0 else
    (chargeScalar D sigma * chargeScalar D tau * (2 : ℂ)^(-2*bilinear D sigma tau)) •
      ((∑ d ∈ (LatticeHalfFockProductKernel.pairTranslation D sigma tau p).support,
        (LatticeHalfFockProductKernel.pairTranslation D sigma tau p).coeff d *
          transformedCollisionDiagonal D sigma tau gamma delta r n degree.toNat d)
        ⊗ₜ[ℂ] groundAction D hu sigma (groundAction D hu tau g))

set_option maxHeartbeats 4000000 in
private theorem term_transform (D : LatticeData) (hu : IsUnit D.G.det)
    (sigma tau : Charge D) (gamma delta r n : ℤ) (l : ℕ)
    (K : ℕ) (hK : (bilinear D sigma tau).natAbs ≤ K)
    (p : Oscillator D) (g : ActualGround D hu) :
    (∑ k ∈ Finset.range (((K : ℤ)-r).toNat-l), Ring.choose ((gamma : ℂ)/2) k •
      chargedCollisionTerm D hu sigma tau (r+(l+k : ℕ))
        (chargedPhysicalOutputExponent gamma delta n (l+k : ℕ)) (p ⊗ₜ[ℂ] g)) =
      transformedCollisionKernel D hu sigma tau gamma delta r n l p g := by
  classical
  let degree : ℤ := -(r + (l : ℤ)) - 1 - bilinear D sigma tau
  unfold transformedCollisionKernel
  change _ = if degree < 0 then 0 else _
  by_cases negative : degree < 0
  · rw [ite_eq_left negative]
    apply Finset.sum_eq_zero
    intro k member
    have zero : -(r+((l+k : ℕ) : ℤ))-1-bilinear D sigma tau < 0 := by
      dsimp [degree] at negative
      omega
    simp only [chargedCollisionTerm, ite_eq_left zero, smul_zero]
  · rw [ite_eq_right negative]
    rw [← collision_tensor_normalization]
    have padded : degree.toNat+1 ≤ ((K : ℤ)-r).toNat-l := by
      have lower : -bilinear D sigma tau ≤ ((-bilinear D sigma tau).natAbs : ℤ) :=
        Int.le_natAbs
      rw [Int.natAbs_neg] at lower
      dsimp [degree] at negative ⊢
      omega
    have truncate :
        (∑ k ∈ Finset.range (((K : ℤ)-r).toNat-l), Ring.choose ((gamma : ℂ)/2) k •
          chargedCollisionTerm D hu sigma tau (r+(l+k : ℕ))
            (chargedPhysicalOutputExponent gamma delta n (l+k : ℕ)) (p ⊗ₜ[ℂ] g)) =
        ∑ k ∈ Finset.range (degree.toNat+1), Ring.choose ((gamma : ℂ)/2) k •
          chargedCollisionTerm D hu sigma tau (r+(l+k : ℕ))
            (chargedPhysicalOutputExponent gamma delta n (l+k : ℕ)) (p ⊗ₜ[ℂ] g) := by
      symm
      apply Finset.sum_subset (Finset.range_mono padded)
      intro k member outside
      have zero : -(r+((l+k : ℕ) : ℤ))-1-bilinear D sigma tau < 0 := by
        have bound : degree.toNat+1 ≤ k := by simpa using outside
        dsimp [degree] at negative ⊢
        omega
      simp only [chargedCollisionTerm, ite_eq_left zero, smul_zero]
    rw [truncate]
    have term (k : ℕ) (member : k ∈ Finset.range (degree.toNat+1)) :
        chargedCollisionTerm D hu sigma tau (r+(l+k : ℕ))
          (chargedPhysicalOutputExponent gamma delta n (l+k : ℕ)) (p ⊗ₜ[ℂ] g) =
        (epsilon D sigma tau * chargeScalar D (sigma+tau)) •
          (collisionOscillator D sigma tau (degree.toNat-k)
            (chargedPhysicalOutputExponent gamma delta n (l+k : ℕ)) p
              ⊗ₜ[ℂ] groundAction D hu (sigma+tau) g) := by
      have within := Finset.mem_range.mp member
      have shifted : -(r+((l+k : ℕ) : ℤ))-1-bilinear D sigma tau = degree-(k : ℤ) := by
        dsimp [degree]
        omega
      have nonnegative : ¬ degree-(k : ℤ) < 0 := by omega
      have natural : (degree-(k : ℤ)).toNat = degree.toNat-k := by omega
      simp only [chargedCollisionTerm, shifted, ite_eq_right nonnegative, natural,
        collisionCoefficient, LinearMap.smul_apply, TensorProduct.map_tmul, smul_smul]
    rw [Finset.sum_congr rfl (fun k hk => congrArg
      (fun z : ActualTensor D hu => Ring.choose ((gamma : ℂ)/2) k • z) (term k hk))]
    have expand (k : ℕ) :
        collisionOscillator D sigma tau (degree.toNat-k)
          (chargedPhysicalOutputExponent gamma delta n (l+k : ℕ)) p =
        ∑ d ∈ (LatticeHalfFockProductKernel.pairTranslation D sigma tau p).support,
          (LatticeHalfFockProductKernel.pairTranslation D sigma tau p).coeff d *
            collisionDiagonal D sigma tau (degree.toNat-k)
              (chargedPhysicalOutputExponent gamma delta n (l+k : ℕ)) d := by
      rw [collision_expansion]
      simp_rw [diagonal_as_sum]
      rfl
    simp_rw [expand, smul_comm (Ring.choose ((gamma : ℂ)/2) _) (_ * _)]
    rw [← Finset.smul_sum]
    simp_rw [TensorProduct.smul_tmul']
    rw [← TensorProduct.sum_tmul]
    apply congrArg (fun z : Oscillator D =>
      (epsilon D sigma tau * chargeScalar D (sigma+tau)) •
        (z ⊗ₜ[ℂ] groundAction D hu (sigma+tau) g))
    simp_rw [Finset.smul_sum, ← Algebra.mul_smul_comm]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro d member
    rw [← Finset.mul_sum]
    congr 1
    exact diagonal_binomial_shift D sigma tau gamma delta r n l degree.toNat
      (by dsimp [degree]; omega) d

/- proof_shape: chargedPhysicalCollisionRow_transform_native: content
   admission_basis: escape-witness
   escape_witness: Every reflected signed collision degree truncates the
   physical outer range independently. The signed creation total is constant
   through that range. Finite coefficient convolution shifts the first
   collision exponent by gamma without changing either integer lift.
   literature_status: classical formal coefficient change of variables; no novelty claim. -/
set_option maxHeartbeats 4000000 in
theorem chargedPhysicalCollisionRow_transform_native (D : LatticeData)
    (hu : IsUnit D.G.det) (sigma tau : Charge D) (epsilon eta : Bool)
    (gamma delta r n : ℤ) (l K : ℕ) (hK : (bilinear D sigma tau).natAbs ≤ K)
    (p : Oscillator D) (g : ActualGround D hu) :
    (∑ k ∈ Finset.range (((K : ℤ)-r).toNat-l), Ring.choose ((gamma : ℂ)/2) k •
      chargedPhysicalCollisionRow D hu sigma tau epsilon eta gamma delta r n (l+k)
        (p ⊗ₜ[ℂ] g)) =
      (1/4 : ℂ) • (transformedCollisionKernel D hu sigma tau gamma delta r n l p g +
        projectedSign eta • transformedCollisionKernel D hu sigma (-tau) gamma delta r n l p g +
        projectedSign epsilon • transformedCollisionKernel D hu (-sigma) tau gamma delta r n l p g +
        (projectedSign epsilon * projectedSign eta) •
          transformedCollisionKernel D hu (-sigma) (-tau) gamma delta r n l p g) := by
  classical
  have gram (u v : Bool) :
      (bilinear D (reflectedCharge sigma u) (reflectedCharge tau v)).natAbs ≤ K := by
    simpa only [reflected_bilinear_natAbs] using hK
  unfold chargedPhysicalCollisionRow chargedCollisionFour
  simp only [reflectedCharge, Bool.false_eq_true, ite_false, ite_true]
  simp_rw [smul_comm (Ring.choose ((gamma : ℂ)/2) _) (1/4 : ℂ)]
  rw [← Finset.smul_sum]
  simp only [smul_add, Finset.sum_add_distrib]
  simp_rw [smul_comm (Ring.choose ((gamma : ℂ)/2) _) (projectedSign eta),
    smul_comm (Ring.choose ((gamma : ℂ)/2) _) (projectedSign epsilon),
    smul_comm (Ring.choose ((gamma : ℂ)/2) _) (projectedSign epsilon * projectedSign eta),
    ← Finset.smul_sum]
  rw [term_transform D hu sigma tau gamma delta r n l K hK,
    term_transform D hu sigma (-tau) gamma delta r n l K (gram false true),
    term_transform D hu (-sigma) tau gamma delta r n l K (gram true false),
    term_transform D hu (-sigma) (-tau) gamma delta r n l K (gram true true)]

end
end D5.S3.VertexAlgebra.LatticeHalfFockChargedResidue
