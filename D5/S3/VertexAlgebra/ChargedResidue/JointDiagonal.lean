/- GID: D5/S3/VertexAlgebra/ChargedResidue/JointDiagonal
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/ChargedResidue/JointDiagonal
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The two supported native chambers share one signed creation diagonal. -/

import D5.S3.VertexAlgebra.ChargedResidue.CollisionTransform

/-! Joint finite creation support for the two native ordered chambers. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

namespace D5.S3.VertexAlgebra.LatticeHalfFockChargedResidue
open LatticeGeneratingFieldLocality LatticeHalfFockChargedTensorCoefficients
open LatticeHalfFockChargedCoefficients LatticeHalfFockProductKernel
open scoped BigOperators TensorProduct
noncomputable section

/-- Extend a contraction series by zero to the signed creation diagonal. -/
def signedContraction (D : LatticeData) (left right : Charge D) (k : ℤ) : ℂ :=
  if k < 0 then 0 else PowerSeries.coeff k.toNat (halfContraction D left right)

private theorem creation_negative (D : LatticeData) (charge : Charge D)
    (k : ℤ) (negative : k < 0) : halfCreationCoeff D charge k = 0 := by
  exact ite_eq_left negative

private theorem creation_reindex (D : LatticeData) (left right : Charge D)
    (a b : ℤ) (cutoff : ℕ) (bound : b < cutoff) :
    (∑ k ∈ Finset.range cutoff,
      PowerSeries.coeff k (halfContraction D left right) •
        (halfCreationCoeff D left (a+k) * halfCreationCoeff D right (b-k))) =
      if a+b < 0 then 0 else
        ∑ m ∈ Finset.range ((a+b).toNat+1),
          signedContraction D left right ((m : ℤ)-a) •
            (halfCreationCoeff D left m * halfCreationCoeff D right (a+b-m)) := by
  classical
  by_cases negative : a+b < 0
  · rw [ite_eq_left negative]
    apply Finset.sum_eq_zero
    intro k member
    by_cases ha : a+k < 0
    · rw [creation_negative D left _ ha, zero_mul, smul_zero]
    · rw [creation_negative D right _ (by omega : b-k < 0), mul_zero, smul_zero]
  · rw [ite_eq_right negative]
    refine Finset.sum_bij_ne_zero (fun k _ _ => (a+k).toNat) ?_ ?_ ?_ ?_
    · intro k member nonzero
      have ha : 0 ≤ a+k := by
        by_contra h
        exact nonzero (by rw [creation_negative D left _ (by omega), zero_mul, smul_zero])
      have hb : 0 ≤ b-k := by
        by_contra h
        exact nonzero (by rw [creation_negative D right _ (by omega), mul_zero, smul_zero])
      apply Finset.mem_range.mpr
      omega
    · intro k hk nk j hj nj equality
      have ha : 0 ≤ a+k := by
        by_contra h
        exact nk (by rw [creation_negative D left _ (by omega), zero_mul, smul_zero])
      have hb : 0 ≤ a+j := by
        by_contra h
        exact nj (by rw [creation_negative D left _ (by omega), zero_mul, smul_zero])
      omega
    · intro m member nonzero
      have ma : 0 ≤ (m : ℤ)-a := by
        by_contra h
        exact nonzero (by simp only [signedContraction, ite_eq_left (by omega : (m : ℤ)-a < 0),
          zero_smul])
      have upper := Finset.mem_range.mp member
      refine ⟨((m : ℤ)-a).toNat, Finset.mem_range.mpr (by omega), ?_, ?_⟩
      · have natural : (((m : ℤ)-a).toNat : ℤ) = (m : ℤ)-a := by omega
        simpa only [natural, show a+((m : ℤ)-a) = m by omega,
          show b-((m : ℤ)-a) = a+b-m by omega,
          signedContraction, ite_eq_right (by omega : ¬ (m : ℤ)-a < 0)] using nonzero
      · omega
    · intro k member nonzero
      have ha : 0 ≤ a+k := by
        by_contra h
        exact nonzero (by rw [creation_negative D left _ (by omega), zero_mul, smul_zero])
      have natural : ((a+(k : ℤ)).toNat : ℤ) = a+k := by omega
      simp only [natural, signedContraction,
        show a+(k : ℤ)-a = k by omega,
        ite_eq_right (show ¬ (k : ℤ) < 0 by omega), Int.toNat_natCast,
        show a+b-(a+(k : ℤ)) = b-k by omega]

/-- The single common-kernel contraction is reindexed using its own translated
polynomial's right support, including negative and zero creation totals. -/
private theorem ordered_diagonal (D : LatticeData) (left right : Charge D)
    (first second : ℤ) (p : Oscillator D) :
    (∑ k ∈ Finset.range (nativeContractionCutoff D left right second p),
      PowerSeries.coeff k (halfContraction D left right) •
        commonKernel D left right (first+chargeNorm D left+k)
          (second+chargeNorm D right-k) p) =
      ∑ d ∈ (pairTranslation D left right p).support,
        (pairTranslation D left right p).coeff d *
          (if first+second+chargeNorm D left+chargeNorm D right+d 0+d 1 < 0 then 0 else
            ∑ m ∈ Finset.range
                ((first+second+chargeNorm D left+chargeNorm D right+d 0+d 1).toNat+1),
              signedContraction D left right
                ((m : ℤ)-(first+chargeNorm D left+d 0)) •
                (halfCreationCoeff D left m * halfCreationCoeff D right
                  (first+second+chargeNorm D left+chargeNorm D right+d 0+d 1-m))) := by
  classical
  simp_rw [kernel_expansion, Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d member
  have collect : (∑ k ∈ Finset.range (nativeContractionCutoff D left right second p),
      PowerSeries.coeff k (halfContraction D left right) •
        ((pairTranslation D left right p).coeff d *
          (halfCreationCoeff D left (first+chargeNorm D left+k+d 0) *
            halfCreationCoeff D right (second+chargeNorm D right-k+d 1)))) =
      (pairTranslation D left right p).coeff d *
        ∑ k ∈ Finset.range (nativeContractionCutoff D left right second p),
          PowerSeries.coeff k (halfContraction D left right) •
            (halfCreationCoeff D left (first+chargeNorm D left+k+d 0) *
              halfCreationCoeff D right (second+chargeNorm D right-k+d 1)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    exact (Algebra.mul_smul_comm _ _ _).symm
  rw [collect]
  apply congrArg ((pairTranslation D left right p).coeff d * ·)
  have supbound := Finset.le_sup (f := fun d : Fin 2 →₀ ℕ => d 1) member
  have integerbound : (d 1 : ℤ) ≤
      ((pairTranslation D left right p).support.sup (fun d => d 1) : ℕ) := by
    exact_mod_cast supbound
  have bound : second+chargeNorm D right+d 1 < nativeContractionCutoff D left right second p := by
    dsimp only [nativeContractionCutoff]
    omega
  have reindex := creation_reindex D left right
    (first+chargeNorm D left+d 0) (second+chargeNorm D right+d 1)
    (nativeContractionCutoff D left right second p) bound
  have total : first+chargeNorm D left+(d 0 : ℤ)+(second+chargeNorm D right+d 1) =
      first+second+chargeNorm D left+chargeNorm D right+d 0+d 1 := by ring
  rw [total] at reindex
  rw [← reindex]
  apply Finset.sum_congr rfl
  intro k hk
  congr 2 <;> congr 1 <;> ring

private theorem contraction_symmetric (D : LatticeData) (left right : Charge D) :
    halfContraction D right left = halfContraction D left right := by
  unfold halfContraction
  rw [LatticeFiniteNegativeGeneration.bilinear_symmetric D right left]

set_option maxHeartbeats 1000000 in
private theorem translation_swap (D : LatticeData) (left right : Charge D)
    (p : Oscillator D) :
    MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1) (pairTranslation D left right p) =
      pairTranslation D right left p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [pairTranslation]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul]
    rw [hp]
    congr 1
    simp only [pairTranslation, MvPolynomial.eval₂AlgHom_X]
    simp only [pairTranslationVariable, map_sub, map_mul, map_pow,
      MvPolynomial.rename_C, MvPolynomial.rename_X, Equiv.swap_apply_left,
      Equiv.swap_apply_right]
    ring

private theorem reverse_support_bound (D : LatticeData) (left right : Charge D)
    (first : ℤ) (p : Oscillator D) (d : Fin 2 →₀ ℕ)
    (member : d ∈ (pairTranslation D left right p).support) :
    first+chargeNorm D left+d 0 < nativeContractionCutoff D right left first p := by
  classical
  let swap := Equiv.swap (0 : Fin 2) 1
  have mem : d.mapDomain swap ∈ (pairTranslation D right left p).support := by
    rw [← translation_swap D left right p, MvPolynomial.support_rename_of_injective swap.injective]
    exact Finset.mem_image.mpr ⟨d, member, rfl⟩
  have bound := Finset.le_sup (f := fun e : Fin 2 →₀ ℕ => e 1) mem
  have coordinate : (d.mapDomain swap) 1 = d 0 := by
    rw [Finsupp.mapDomain_equiv_apply]
    rfl
  rw [coordinate] at bound
  have integerbound : (d 0 : ℤ) ≤
      ((pairTranslation D right left p).support.sup (fun d => d 1) : ℕ) := by
    exact_mod_cast bound
  dsimp only [nativeContractionCutoff]
  omega

private theorem creation_reindex_reverse (D : LatticeData) (left right : Charge D)
    (a b : ℤ) (cutoff : ℕ) (bound : a < cutoff) :
    (∑ k ∈ Finset.range cutoff,
      PowerSeries.coeff k (halfContraction D right left) •
        (halfCreationCoeff D left (a-k) * halfCreationCoeff D right (b+k))) =
      if a+b < 0 then 0 else
        ∑ m ∈ Finset.range ((a+b).toNat+1),
          signedContraction D left right (a-m) •
            (halfCreationCoeff D left m * halfCreationCoeff D right (a+b-m)) := by
  classical
  have reindex := creation_reindex D right left b a cutoff bound
  have total : b+a = a+b := by ring
  rw [total] at reindex
  simp_rw [mul_comm (halfCreationCoeff D right _)] at reindex
  rw [reindex]
  by_cases negative : a+b < 0
  · simp only [ite_eq_left negative]
  · simp only [ite_eq_right negative]
    rw [← Finset.sum_range_reflect (fun m =>
      signedContraction D right left ((m : ℤ)-b) •
        (halfCreationCoeff D left (a+b-m) * halfCreationCoeff D right m)) ((a+b).toNat+1)]
    apply Finset.sum_congr rfl
    intro m member
    have within := Finset.mem_range.mp member
    have coordinate : (((a+b).toNat+1-1-m : ℕ) : ℤ) = a+b-m := by omega
    rw [coordinate, show a+b-(a+b-(m : ℤ)) = m by ring,
      show a+b-(m : ℤ)-b = a-m by ring]
    simp only [signedContraction, contraction_symmetric]

private theorem reversed_diagonal (D : LatticeData) (left right : Charge D)
    (first second : ℤ) (p : Oscillator D) :
    (∑ k ∈ Finset.range (nativeContractionCutoff D right left first p),
      PowerSeries.coeff k (halfContraction D right left) •
        commonKernel D left right (first+chargeNorm D left-k)
          (second+chargeNorm D right+k) p) =
      ∑ d ∈ (pairTranslation D left right p).support,
        (pairTranslation D left right p).coeff d *
          (if first+second+chargeNorm D left+chargeNorm D right+d 0+d 1 < 0 then 0 else
            ∑ m ∈ Finset.range
                ((first+second+chargeNorm D left+chargeNorm D right+d 0+d 1).toNat+1),
              signedContraction D left right
                (first+chargeNorm D left+d 0-m) •
                (halfCreationCoeff D left m * halfCreationCoeff D right
                  (first+second+chargeNorm D left+chargeNorm D right+d 0+d 1-m))) := by
  classical
  simp_rw [kernel_expansion, Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d member
  have collect : (∑ k ∈ Finset.range (nativeContractionCutoff D right left first p),
      PowerSeries.coeff k (halfContraction D right left) •
        ((pairTranslation D left right p).coeff d *
          (halfCreationCoeff D left (first+chargeNorm D left-k+d 0) *
            halfCreationCoeff D right (second+chargeNorm D right+k+d 1)))) =
      (pairTranslation D left right p).coeff d *
        ∑ k ∈ Finset.range (nativeContractionCutoff D right left first p),
          PowerSeries.coeff k (halfContraction D right left) •
            (halfCreationCoeff D left (first+chargeNorm D left-k+d 0) *
              halfCreationCoeff D right (second+chargeNorm D right+k+d 1)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    exact (Algebra.mul_smul_comm _ _ _).symm
  rw [collect]
  apply congrArg ((pairTranslation D left right p).coeff d * ·)
  have reindex := creation_reindex_reverse D left right
    (first+chargeNorm D left+d 0) (second+chargeNorm D right+d 1)
    (nativeContractionCutoff D right left first p)
    (reverse_support_bound D left right first p d member)
  have total : first+chargeNorm D left+(d 0 : ℤ)+(second+chargeNorm D right+d 1) =
      first+second+chargeNorm D left+chargeNorm D right+d 0+d 1 := by ring
  rw [total] at reindex
  rw [← reindex]
  apply Finset.sum_congr rfl
  intro k hk
  congr 2 <;> congr 1 <;> ring

/-- The two actual contraction chambers, before their scalar cancellation. -/
def nativeChamberScalar (D : LatticeData) (left right : Charge D)
    (q v : ℤ) (forward reverse : ℕ) : ℂ :=
  (∑ j ∈ Finset.range forward, physicalResidueWeight q j *
    signedContraction D left right (v-2*j)) -
      ((-1 : ℂ) ^ q * paritySign (bilinear D left right)) *
        ∑ j ∈ Finset.range reverse, physicalResidueWeight q j *
          signedContraction D left right (2*q-v-2*j)

def nativeJointDiagonal (D : LatticeData) (left right : Charge D)
    (gamma delta q z : ℤ) (forward reverse : ℕ) (d : Fin 2 →₀ ℕ) : Oscillator D :=
  let total := physicalCreationTotal D left right gamma delta q z d
  if total < 0 then 0 else
    ∑ m ∈ Finset.range (total.toNat+1),
      nativeChamberScalar D left right q
        ((m : ℤ)-(-2*q-gamma-2+chargeNorm D left+d 0)) forward reverse •
        (halfCreationCoeff D left m * halfCreationCoeff D right (total-m))

private theorem collect_chamber (D : LatticeData) (p : PairPolynomial D)
    (total : (Fin 2 →₀ ℕ) → ℤ) (J : ℕ) (weight : ℕ → ℂ)
    (amplitude : ℕ → (Fin 2 →₀ ℕ) → ℕ → ℂ)
    (creation : (Fin 2 →₀ ℕ) → ℕ → Oscillator D) :
    (∑ j ∈ Finset.range J, weight j •
      ∑ d ∈ p.support, p.coeff d *
        (if total d < 0 then 0 else
          ∑ m ∈ Finset.range ((total d).toNat+1), amplitude j d m • creation d m)) =
      ∑ d ∈ p.support, p.coeff d *
        (if total d < 0 then 0 else
          ∑ m ∈ Finset.range ((total d).toNat+1),
            (∑ j ∈ Finset.range J, weight j * amplitude j d m) • creation d m) := by
  classical
  simp_rw [Finset.smul_sum, ← Algebra.mul_smul_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d member
  rw [← Finset.mul_sum]
  congr 1
  by_cases negative : total d < 0
  · simp only [ite_eq_left negative, smul_zero, Finset.sum_const_zero]
  · simp only [ite_eq_right negative]
    simp_rw [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul]

private def forwardOscillator (D : LatticeData) (left right : Charge D)
    (gamma delta q z : ℤ) (p : Oscillator D) (j : ℕ) : Oscillator D :=
  let first := -2*(q-j)-gamma-2
  let second := -2*(z+j)-delta-2
  ∑ k ∈ Finset.range (nativeContractionCutoff D left right second p),
    PowerSeries.coeff k (halfContraction D left right) •
      commonKernel D left right (first+chargeNorm D left+k)
        (second+chargeNorm D right-k) p

private def reverseOscillator (D : LatticeData) (left right : Charge D)
    (gamma delta q z : ℤ) (p : Oscillator D) (j : ℕ) : Oscillator D :=
  let first := -2*(j : ℤ)-gamma-2
  let second := -2*(q+z-j)-delta-2
  ∑ k ∈ Finset.range (nativeContractionCutoff D right left first p),
    PowerSeries.coeff k (halfContraction D right left) •
      commonKernel D left right (first+chargeNorm D left-k)
        (second+chargeNorm D right+k) p

private theorem forward_expansion (D : LatticeData) (left right : Charge D)
    (gamma delta q z : ℤ) (p : Oscillator D) (j : ℕ) :
    forwardOscillator D left right gamma delta q z p j =
      ∑ d ∈ (pairTranslation D left right p).support,
        (pairTranslation D left right p).coeff d *
          (if physicalCreationTotal D left right gamma delta q z d < 0 then 0 else
            ∑ m ∈ Finset.range
                ((physicalCreationTotal D left right gamma delta q z d).toNat+1),
              signedContraction D left right
                ((m : ℤ)-(-2*q-gamma-2+chargeNorm D left+d 0)-2*j) •
                (halfCreationCoeff D left m * halfCreationCoeff D right
                  (physicalCreationTotal D left right gamma delta q z d-m))) := by
  classical
  rw [forwardOscillator, ordered_diagonal]
  apply Finset.sum_congr rfl
  intro d member
  have total : -2*(q-(j : ℤ))-gamma-2+(-2*(z+j)-delta-2)+
      chargeNorm D left+chargeNorm D right+d 0+d 1 =
        physicalCreationTotal D left right gamma delta q z d := by
    unfold physicalCreationTotal
    ring
  rw [total]
  by_cases negative : physicalCreationTotal D left right gamma delta q z d < 0
  · simp only [ite_eq_left negative]
  · simp only [ite_eq_right negative]
    congr 1
    apply Finset.sum_congr rfl
    intro m hm
    congr 2
    ring

private theorem reverse_expansion (D : LatticeData) (left right : Charge D)
    (gamma delta q z : ℤ) (p : Oscillator D) (j : ℕ) :
    reverseOscillator D left right gamma delta q z p j =
      ∑ d ∈ (pairTranslation D left right p).support,
        (pairTranslation D left right p).coeff d *
          (if physicalCreationTotal D left right gamma delta q z d < 0 then 0 else
            ∑ m ∈ Finset.range
                ((physicalCreationTotal D left right gamma delta q z d).toNat+1),
              signedContraction D left right
                (2*q-((m : ℤ)-(-2*q-gamma-2+chargeNorm D left+d 0))-2*j) •
                (halfCreationCoeff D left m * halfCreationCoeff D right
                  (physicalCreationTotal D left right gamma delta q z d-m))) := by
  classical
  rw [reverseOscillator, reversed_diagonal]
  apply Finset.sum_congr rfl
  intro d member
  have total : -2*(j : ℤ)-gamma-2+(-2*(q+z-j)-delta-2)+
      chargeNorm D left+chargeNorm D right+d 0+d 1 =
        physicalCreationTotal D left right gamma delta q z d := by
    unfold physicalCreationTotal
    ring
  rw [total]
  by_cases negative : physicalCreationTotal D left right gamma delta q z d < 0
  · simp only [ite_eq_left negative]
  · simp only [ite_eq_right negative]
    congr 1
    apply Finset.sum_congr rfl
    intro m hm
    congr 2
    ring

private theorem joint_oscillator (D : LatticeData) (left right : Charge D)
    (gamma delta q z : ℤ) (p : Oscillator D) (forward reverse : ℕ) :
    ((∑ j ∈ Finset.range forward, physicalResidueWeight q j •
      forwardOscillator D left right gamma delta q z p j) -
      ((-1 : ℂ) ^ q * paritySign (bilinear D left right)) •
        ∑ j ∈ Finset.range reverse, physicalResidueWeight q j •
          reverseOscillator D left right gamma delta q z p j) =
      ∑ d ∈ (pairTranslation D left right p).support,
        (pairTranslation D left right p).coeff d *
          nativeJointDiagonal D left right gamma delta q z forward reverse d := by
  classical
  simp_rw [forward_expansion, reverse_expansion]
  rw [collect_chamber, collect_chamber]
  simp only [Finset.smul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d member
  rw [← Algebra.mul_smul_comm, ← mul_sub]
  congr 1
  unfold nativeJointDiagonal
  by_cases negative : physicalCreationTotal D left right gamma delta q z d < 0
  · simp only [ite_eq_left negative, smul_zero, sub_self]
  · simp only [ite_eq_right negative, Finset.smul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro m member
    simp only [nativeChamberScalar, sub_smul, mul_smul]

private theorem tensor_sum (D : LatticeData) (hu : IsUnit D.G.det) (c : ℂ)
    (G : ActualGround D hu) (J : ℕ) (w : ℕ → ℂ) (F : ℕ → Oscillator D) :
    (∑ j ∈ Finset.range J, w j • (c • (F j ⊗ₜ[ℂ] G))) =
      c • ((∑ j ∈ Finset.range J, w j • F j) ⊗ₜ[ℂ] G) := by
  simp only [TensorProduct.sum_tmul, Finset.smul_sum, TensorProduct.smul_tmul', smul_smul]
  apply Finset.sum_congr rfl
  intro j member
  rw [mul_comm]

/- proof_shape: chargedPhysicalResidueRow_joint_native: content
   admission_basis: escape-witness
   escape_witness: The actual two ordered contraction supports are each
   reindexed by a bijection onto the same finite creation diagonal, after
   retaining their own translated polynomial bounds. The reverse support is
   transported by an actual swap of the two polynomial variables. Both outer
   ranges remain those of the actual intermediate physical fields.
   literature_status: repo-derived finite reindexing of classical twisted-lattice coefficients. -/
theorem chargedPhysicalResidueRow_joint_native (D : LatticeData) (hu : IsUnit D.G.det)
    (sigma tau : Charge D) (epsilon eta : Bool) (gamma delta r n : ℤ)
    (hgamma : (-1 : ℂ) ^ gamma = projectedSign epsilon)
    (hdelta : (-1 : ℂ) ^ delta = projectedSign eta)
    (l : ℕ) (p : Oscillator D) (g : ActualGround D hu) :
    let A := LatticeHalfFockPhysicalRescaling.physicalSlice D hu (chargedField D hu sigma) gamma
    let B := LatticeHalfFockPhysicalRescaling.physicalSlice D hu (chargedField D hu tau) delta
    let forward := (-(n-l)-((HahnModule.of ℂ).symm (B (p ⊗ₜ[ℂ] g))).order).toNat
    let reverse := (-((HahnModule.of ℂ).symm (A (p ⊗ₜ[ℂ] g))).order).toNat
    chargedPhysicalResidueRow D hu sigma tau epsilon eta gamma delta r n l (p ⊗ₜ[ℂ] g) =
      (chargeScalar D sigma * chargeScalar D tau) •
        ((∑ d ∈ (pairTranslation D sigma tau p).support,
          (pairTranslation D sigma tau p).coeff d *
            nativeJointDiagonal D sigma tau gamma delta (r+l) (n-l) forward reverse d)
              ⊗ₜ[ℂ] groundAction D hu sigma (groundAction D hu tau g)) := by
  classical
  dsimp only
  rw [chargedPhysicalResidueRow_native D hu sigma tau epsilon eta gamma delta r n
    hgamma hdelta l p g]
  simp only [nativeOrderedKernel, nativeReversedKernel]
  change (∑ j ∈ Finset.range _, physicalResidueWeight (r+l) j •
      ((chargeScalar D sigma * chargeScalar D tau) •
        (forwardOscillator D sigma tau gamma delta (r+l) (n-l) p j ⊗ₜ[ℂ]
          groundAction D hu sigma (groundAction D hu tau g)))) -
    (-1 : ℂ) ^ (r+l) •
      (∑ j ∈ Finset.range _, physicalResidueWeight (r+l) j •
        ((paritySign (bilinear D sigma tau) * (chargeScalar D sigma * chargeScalar D tau)) •
          (reverseOscillator D sigma tau gamma delta (r+l) (n-l) p j ⊗ₜ[ℂ]
            groundAction D hu sigma (groundAction D hu tau g)))) = _
  rw [tensor_sum, tensor_sum, ← joint_oscillator]
  simp only [TensorProduct.sub_tmul, TensorProduct.smul_tmul', smul_sub, smul_smul]
  rw [show (-1 : ℂ) ^ (r+(l : ℤ)) *
      (paritySign (bilinear D sigma tau) * (chargeScalar D sigma * chargeScalar D tau)) =
      (chargeScalar D sigma * chargeScalar D tau) *
        ((-1 : ℂ) ^ (r+(l : ℤ)) * paritySign (bilinear D sigma tau)) by ring]

end
end D5.S3.VertexAlgebra.LatticeHalfFockChargedResidue
