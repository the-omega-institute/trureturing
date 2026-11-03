/- GID: D5/S3/VertexAlgebra/TwistedGround/MixedTranslation
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/MixedTranslation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual stress transpose and finite input-translation coefficient calculation. -/
import D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner
import D5.S3.VertexAlgebra.LatticeHalfFockCorrectedConformal
import D5.S3.VertexAlgebra.GroundRightCurrentTransport.FirstSourceClosure
import D5.S3.VertexAlgebra.LatticeActualConformalWard
import Batteries.Tactic.OpenPrivate

/-! Finite transpose and translation calculation for the normalized actual kernel. -/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators TensorProduct DirectSum VertexOperator
namespace D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner
open LatticeGeneratingFieldLocality LatticeHalfFock LatticeAllStateField
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockGradedTrace
open LatticeHalfFockCorrectedField LatticePositiveEnergy LatticeInvolution
open HalfFock.LatticeHalfFockParityField ActualChargedAdjoint
open CorrectedInversion ActualOddGradeOrthogonality
open HalfFock.ActualEnergyCovariance
open LatticeSugawaraCurrents LatticeSugawaraVirasoro
open LatticeHalfFockFiniteCorrection (sourceWeight)
open LatticeHalfFockGroundRightCurrentTransport.Calculus
open private T lowering_eigen lowering_killed theta_omega_fixed kernel
  homogeneous_coefficient ambientCoefficient liftGrade
  from D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner

private theorem conformal_polynomial_homogeneous (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) :
    MvPolynomial.IsWeightedHomogeneous (sourceWeight D)
      (LatticeActualConformalState.conformalPolynomial D H) 2 := by
  classical
  unfold LatticeActualConformalState.conformalPolynomial
  apply (MvPolynomial.weightedHomogeneousSubmodule ℂ (sourceWeight D) 2).smul_mem
  apply MvPolynomial.IsWeightedHomogeneous.sum
  intro i hi
  apply MvPolynomial.IsWeightedHomogeneous.sum
  intro j hj
  apply (MvPolynomial.weightedHomogeneousSubmodule ℂ (sourceWeight D) 2).smul_mem
  simpa [sourceWeight] using
    (MvPolynomial.isWeightedHomogeneous_X (R := ℂ) (sourceWeight D) (i, 0)).mul
      (MvPolynomial.isWeightedHomogeneous_X (R := ℂ) (sourceWeight D) (j, 0))

private theorem conformal_polynomial_lowering (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) :
    SourceMobius.sectorL1 D 0 (LatticeActualConformalState.conformalPolynomial D H) = 0 := by
  classical
  simp [LatticeActualConformalState.conformalPolynomial, map_smul, map_sum,
    Derivation.leibniz, SourceMobius.sectorL1, MvPolynomial.mkDerivation_X,
    SourceMobius.loweringVariable, bilinear]

private theorem actual_stress_transpose (D : LatticeData) (hu : IsUnit D.G.det)
    (m : ℤ) (x y : ActualTensor D hu) :
    actualForm D hu
        (tensorL D (ActualGround D hu) (HalfFockSpectralFiberSource.actualInverse D) m x) y =
      actualForm D hu x
        (tensorL D (ActualGround D hu) (HalfFockSpectralFiberSource.actualInverse D) (-m) y) := by
  classical
  let H := HalfFockSpectralFiberSource.actualInverse D
  let p := LatticeActualConformalState.conformalPolynomial D H
  let delta := (SourceMobius.sectorL1 D 0).toLinearMap
  have killed : delta p = 0 := conformal_polynomial_lowering D H
  have powers (j : ℕ) (hj : j ≠ 0) : (delta ^ j) p = 0 := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
    rw [pow_succ, Module.End.mul_apply, killed, map_zero]
  have inv := CorrectedInversion.actual_corrected_single_inversion D hu 0 p 2
    (conformal_polynomial_homogeneous D H) (-2*m-4) x y
  have collapse :
      (∑ j ∈ Finset.range (2+1),
        actualForm D hu x ((correctedField D hu (Finsupp.single 0
          ((j.factorial : ℂ)⁻¹ • ((delta ^ j) p)))).coeff
            (-(-2*m-4)-2*chargeNorm D 0-4*(2 : ℤ)+2*(j : ℤ)) y)) =
      actualForm D hu x ((correctedField D hu (Finsupp.single 0 p)).coeff (2*m-4) y) := by
    rw [Finset.sum_eq_single 0]
    · have c0 : chargeNorm D 0 = 0 := by simp [chargeNorm, bilinear]
      simp only [Nat.factorial_zero, Nat.cast_one, inv_one, one_smul, pow_zero,
        Module.End.one_apply, Nat.cast_zero, mul_zero, add_zero, c0]
      have ee : -(-2*m-4)-(0 : ℤ)-4*2 = 2*m-4 := by ring
      rw [ee]
    · intro j hj hne
      rw [powers j hne]
      simp
    · simp
  have c0 : chargeNorm D 0 = 0 := by simp [chargeNorm, bilinear]
  dsimp only [delta] at collapse
  simp only [Nat.cast_ofNat] at inv
  rw [collapse] at inv
  have sign : paritySign (chargeNorm D 0 / 2) * (-1 : ℂ)^(2 : ℕ) = 1 := by
    rw [c0]
    norm_num [paritySign]
  rw [sign, one_mul] at inv
  have field := LatticeHalfFockCorrectedConformal.correctedField_omega D hu H
    (HalfFockSpectralFiberSource.actualInverse_left D hu)
  change actualForm D hu
      ((correctedField D hu (LatticeActualConformalState.omega D H)).coeff (-2*m-4) x) y =
    actualForm D hu x
      ((correctedField D hu (LatticeActualConformalState.omega D H)).coeff (2*m-4) y) at inv
  rw [field] at inv
  simpa only [tensorStressField, HVertexOperator.coeff_of_coeff, stressCoeff, tensorL,
    if_pos,
    show (-2*m-4) % 2 = 0 by omega, show (2*m-4) % 2 = 0 by omega,
    show (-(-2*m-4)-4)/2 = m by omega,
    show (-(2*m-4)-4)/2 = -m by omega,
    H] using inv

private abbrev raising (D : LatticeData) (hu : IsUnit D.G.det) :=
  tensorL D (ActualGround D hu) (HalfFockSpectralFiberSource.actualInverse D) (-1)

private theorem zero_mode_commutator {M : Type*} [AddCommGroup M] [Module ℂ M]
    (A B : VertexOperator ℂ M) (U : ℤ → VertexOperator ℂ M)
    (law : LatticeHalfFockGroundRightCurrentTransport.Calculus.fullLaw A B U 0)
    (n : ℤ) (x : M) :
    ((U 0)[[n]]) x = (A[[0]]) ((B[[n]]) x) - (B[[n]]) ((A[[0]]) x) := by
  classical
  have h := (law 0 n 0 x).2.2.2
  have left : (∑ᶠ j : ℕ, leftTerm U 0 0 n 0 x j) = ((U 0)[[n]]) x := by
    rw [finsum_eq_single _ 0]
    · simp [leftTerm]
    · intro j hj
      simp [leftTerm, Ring.choose_zero_pos ℂ (Nat.pos_of_ne_zero hj)]
  have first : (∑ᶠ j : ℕ, firstTerm A B 0 n 0 x j) =
      (A[[0]]) ((B[[n]]) x) := by
    rw [finsum_eq_single _ 0]
    · simp [firstTerm, LatticeHalfFockGroundRightCurrentTransport.residueWeight]
    · intro j hj
      simp [firstTerm, LatticeHalfFockGroundRightCurrentTransport.residueWeight,
        Ring.choose_zero_pos ℂ (Nat.pos_of_ne_zero hj)]
  have second : (∑ᶠ j : ℕ, secondTerm A B 0 n 0 x j) =
      (B[[n]]) ((A[[0]]) x) := by
    rw [finsum_eq_single _ 0]
    · simp [secondTerm, LatticeHalfFockGroundRightCurrentTransport.residueWeight]
    · intro j hj
      simp [secondTerm, LatticeHalfFockGroundRightCurrentTransport.residueWeight,
        Ring.choose_zero_pos ℂ (Nat.pos_of_ne_zero hj)]
  rwa [left, first, second] at h

private theorem actual_translation_commutator (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Carrier D) (s : ℤ) (x : ActualTensor D hu) :
    raising D hu ((correctedField D hu a).coeff (2*s) x) -
        (correctedField D hu a).coeff (2*s) (raising D hu x) =
      ((s : ℂ)+1) • (correctedField D hu a).coeff (2*s+2) x := by
  let H := HalfFockSpectralFiberSource.actualInverse D
  let w := LatticeActualConformalState.omega D H
  have eigen : theta D w = (-1 : ℂ)^(0 : ℤ) • w := by
    simpa [w] using theta_omega_fixed D H
  have law := LatticeHalfFockGroundRightCurrentTransport.first_eigen_arbitrary_second
    D hu w 0 eigen a 0
  have h := zero_mode_commutator _ _ _ law (-s-1) x
  simp only [LatticeHalfFockPhysicalRescaling.physicalSlice_mode] at h
  have source : LatticeAllStateReconstruction.mu D w 0 a =
      LatticeSugawaraConformal.translation D a := by
    dsimp only [w]
    rw [LatticeActualConformalWard.omega_product]
    norm_num only
    rw [LatticeSugawaraConformal.sugawaraMode_minus_one_eq_translation D H
      (HalfFockSpectralFiberSource.actualInverse_left D hu)
      (HalfFockSpectralFiberSource.actualInverse_right D hu)]
  have stress : (correctedField D hu w).coeff (-2) = raising D hu := by
    dsimp only [w]
    rw [LatticeHalfFockCorrectedConformal.correctedField_omega D hu H
      (HalfFockSpectralFiberSource.actualInverse_left D hu)]
    simp only [tensorStressField, HVertexOperator.coeff_of_coeff, stressCoeff,
      show (-2 : ℤ) % 2 = 0 by decide, if_pos,
      show (-(-2 : ℤ)-4)/2 = -1 by decide, raising, tensorL, H]
  have ex : -2*(-s-1)-(0+0)-2 = 2*s := by ring
  rw [source, ex, show -2*(-s-1)-0-2 = 2*s by ring] at h
  have ee : -2*(0 : ℤ)-0-2 = -2 := by ring
  rw [ee, stress] at h
  rw [← h, LatticeHalfFockOriginalTranslation.correctedField_translation_physical]
  congr 1
  push_cast
  ring

private theorem scalar_translation_step (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Carrier D) (s : ℤ) (x y : ActualTensor D hu) :
    actualForm D hu x ((correctedField D hu a).coeff (2*s) (raising D hu y)) =
      actualForm D hu (T D hu x) ((correctedField D hu a).coeff (2*s) y) -
        ((s : ℂ)+1) * actualForm D hu x ((correctedField D hu a).coeff (2*s+2) y) := by
  have h := actual_translation_commutator D hu a s y
  have hB := congrArg (actualForm D hu x) h
  simp only [map_sub, map_smul, smul_eq_mul] at hB
  rw [← actual_stress_transpose D hu 1 x
    ((correctedField D hu a).coeff (2*s) y)] at hB
  change actualForm D hu (T D hu x) ((correctedField D hu a).coeff (2*s) y) -
    actualForm D hu x ((correctedField D hu a).coeff (2*s) (raising D hu y)) = _ at hB
  linear_combination -hB

private theorem lowering_raising_bracket (D : LatticeData) (hu : IsUnit D.G.det)
    (x : ActualTensor D hu) :
    T D hu (raising D hu x) - raising D hu (T D hu x) =
      (2 : ℂ) • actualTensorL0 D hu x := by
  have bracket : T D hu * raising D hu - raising D hu * T D hu =
      (2 : ℂ) • actualTensorL0 D hu := by
    apply TensorProduct.ext'
    intro p t
    have h := congrArg (fun A : Module.End ℂ (Oscillator D) => A p ⊗ₜ[ℂ] t)
      (L_virasoro D (HalfFockSpectralFiberSource.actualInverse D)
        (HalfFockSpectralFiberSource.actualInverse_left D hu)
        (HalfFockSpectralFiberSource.actualInverse_right D hu) 1 (-1))
    norm_num at h
    simpa only [T, raising, actualTensorL0, tensorL, tensorEnd, LinearMap.sub_apply,
      Module.End.mul_apply, LinearMap.smul_apply, TensorProduct.map_tmul,
      LinearMap.id_apply, TensorProduct.sub_tmul, TensorProduct.tmul_smul, TensorProduct.smul_tmul'] using h
  exact LinearMap.congr_fun bracket x

private theorem lowering_weight (D : LatticeData) (hu : IsUnit D.G.det)
    (h24 : D.rank = 24) (H : ℕ) (u : ActualTensor D hu)
    (huH : actualTensorL0 D hu u = (H : ℂ) • u) (q : ℕ) :
    actualTensorL0 D hu ((T D hu ^ q) u) =
      ((H : ℂ)-(q : ℂ)) • ((T D hu ^ q) u) := by
  have start : actualTensorL0 D hu u =
      ((D.rank : ℂ)/16 + ((2*(H : ℤ)-3 : ℤ) : ℂ)/2) • u := by
    rw [huH, h24]
    congr 1
    push_cast
    ring
  have h := lowering_eigen D hu (2*(H : ℤ)-3) u start q
  rw [h24] at h
  convert h using 1
  congr 1
  push_cast
  ring

private theorem lowering_power_raising (D : LatticeData) (hu : IsUnit D.G.det)
    (h24 : D.rank = 24) (H : ℕ) (u : ActualTensor D hu)
    (huH : actualTensorL0 D hu u = (H : ℂ) • u) (q : ℕ) :
    (T D hu ^ (q + 1)) (raising D hu u) =
      raising D hu ((T D hu ^ (q + 1)) u) +
        (((q+1 : ℕ) : ℂ)*(2*(H : ℂ)-(q : ℂ))) • ((T D hu ^ q) u) := by
  induction q with
  | zero =>
    have h := lowering_raising_bracket D hu u
    rw [huH, smul_smul, sub_eq_iff_eq_add] at h
    simpa only [Nat.zero_add, pow_zero, pow_one, Module.End.one_apply,
      Nat.cast_zero, sub_zero, Nat.cast_one, one_mul, add_comm] using h
  | succ q ih =>
    rw [pow_succ', Module.End.mul_apply, ih, map_add, map_smul]
    have hc := lowering_raising_bracket D hu ((T D hu ^ (q + 1)) u)
    rw [lowering_weight D hu h24 H u huH (q + 1), smul_smul,
      sub_eq_iff_eq_add] at hc
    rw [hc]
    have step (k : ℕ) : T D hu ((T D hu ^ k) u) = (T D hu ^ (k+1)) u := by
      rw [pow_succ', Module.End.mul_apply]
    rw [step q, step (q+1), ← pow_succ']
    change (2*((H : ℂ)-((q+1 : ℕ) : ℂ))) • ((T D hu ^ (q+1)) u) +
        raising D hu ((T D hu ^ (q+2)) u) +
        (((q+1 : ℕ) : ℂ)*(2*(H : ℂ)-(q : ℂ))) • ((T D hu ^ (q+1)) u) =
      raising D hu ((T D hu ^ (q+2)) u) +
        (((q+2 : ℕ) : ℂ)*(2*(H : ℂ)-((q+1 : ℕ) : ℂ))) • ((T D hu ^ (q+1)) u)
    push_cast
    module

private theorem sum_shift_boundary (f : ℕ → ℂ) (N : ℕ)
    (h0 : f 0 = 0) (hN : f N = 0) :
    (∑ j ∈ Finset.range N, f (j+1)) = ∑ j ∈ Finset.range N, f j := by
  have h := Finset.sum_range_succ' f N
  rw [Finset.sum_range_succ, h0, hN, add_zero, add_zero] at h
  exact h.symm

private theorem sum_successor_recurrence (F A B : ℕ → ℂ) (N : ℕ)
    (h0 : F 0 = A 0) (hs : ∀ q, F (q + 1) = A (q + 1) + B q) :
    (∑ q ∈ Finset.range (N+1), F q) =
      (∑ q ∈ Finset.range (N+1), A q) + ∑ q ∈ Finset.range N, B q := by
  rw [Finset.sum_range_succ', Finset.sum_range_succ' A]
  simp_rw [hs]
  rw [Finset.sum_add_distrib, h0]
  ring

private theorem finite_translation_cancellation
    (F G : ℕ → ℕ → ℂ) (N R : ℕ) (H m : ℂ)
    (hn : ∀ q, F N q = 0) (hr : ∀ p, F p R = 0)
    (g0 : ∀ p, G p 0 = -((p : ℂ)+1)*F (p+1) 0 -
      (m-(p : ℂ)-2*H)*F p 0)
    (gs : ∀ p q, G p (q + 1) = -((p : ℂ)+1)*F (p+1) (q + 1) -
      (m-(p : ℂ)-2*H+(q : ℂ)+1)*F p (q + 1) - (2*H-(q : ℂ))*F p q) :
    (∑ p ∈ Finset.range N, ∑ q ∈ Finset.range (R+1), G p q) =
      -m * ∑ p ∈ Finset.range N, ∑ q ∈ Finset.range R, F p q := by
  classical
  let A : ℕ → ℕ → ℂ := fun p q =>
    -((p : ℂ)+1)*F (p+1) q - (m-(p : ℂ)-2*H+(q : ℂ))*F p q
  let B : ℕ → ℕ → ℂ := fun p q => -(2*H-(q : ℂ))*F p q
  have split (p : ℕ) : (∑ q ∈ Finset.range (R+1), G p q) =
      (∑ q ∈ Finset.range R, A p q) + ∑ q ∈ Finset.range R, B p q := by
    rw [sum_successor_recurrence (G p) (A p) (B p) R]
    · simp only [Finset.sum_range_succ, A, hr, mul_zero, sub_self, add_zero]
    · simpa [A] using g0 p
    · intro q
      dsimp only [A, B]
      push_cast
      linear_combination gs p q
  simp_rw [split]
  rw [Finset.sum_add_distrib]
  have shift : (∑ p ∈ Finset.range N, ∑ q ∈ Finset.range R,
      -((p : ℂ)+1)*F (p+1) q) =
      ∑ p ∈ Finset.range N, ∑ q ∈ Finset.range R, -(p : ℂ)*F p q := by
    rw [Finset.sum_comm, Finset.sum_comm (s := Finset.range N)]
    apply Finset.sum_congr rfl
    intro q hq
    simpa only [Nat.cast_add, Nat.cast_one] using
      sum_shift_boundary (fun p => -(p : ℂ)*F p q) N (by simp) (by rw [hn]; simp)
  simp only [A, Finset.sum_sub_distrib] at shift ⊢
  rw [shift]
  simp only [B, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  ring


private def normalizedTerm (D : LatticeData) (hu : IsUnit D.G.det)
    (H : ℕ) (m : ℤ) (u v : ActualTensor D hu) (a : Carrier D) (p q : ℕ) : ℂ :=
  ((-1 : ℂ) ^ (m+1-(p : ℤ)-(H : ℤ)+(q : ℤ))) /
      ((p.factorial : ℂ)*(q.factorial : ℂ)) *
    actualForm D hu ((T D hu ^ p) v)
      ((correctedField D hu a).coeff (2*(m+1-(p : ℤ)-2*(H : ℤ)+(q : ℤ)))
        ((T D hu ^ q) u))

private theorem sign_step (E : ℤ) : (-1 : ℂ)^(E+1) = -(-1 : ℂ)^E := by
  rw [zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), zpow_one, mul_neg_one]

private theorem normalizedTerm_translation_zero (D : LatticeData)
    (hu : IsUnit D.G.det) (H : ℕ) (m : ℤ) (u v : ActualTensor D hu)
    (a : Carrier D) (p : ℕ) :
    normalizedTerm D hu (H+1) m (raising D hu u) v a p 0 =
      -((p : ℂ)+1)*normalizedTerm D hu H (m-1) u v a (p+1) 0 -
        ((m : ℂ)-(p : ℂ)-2*(H : ℂ))*normalizedTerm D hu H (m-1) u v a p 0 := by
  let s : ℤ := m-1-(p : ℤ)-2*(H : ℤ)
  have step := scalar_translation_step D hu a s ((T D hu ^ p) v) u
  have hp : (p.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero p
  have hps : (p : ℂ)+1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero p
  have ex1 : m+1-(p : ℤ)-((H+1 : ℕ) : ℤ)+(0 : ℤ) = m-(p : ℤ)-(H : ℤ) := by omega
  have ex2 : m-1+1-((p+1 : ℕ) : ℤ)-(H : ℤ)+(0 : ℤ) = m-(p : ℤ)-(H : ℤ)-1 := by omega
  have es1 : 2*(m+1-(p : ℤ)-2*((H+1 : ℕ) : ℤ)+(0 : ℤ)) = 2*s := by dsimp [s]; omega
  have es2 : 2*(m-1+1-((p+1 : ℕ) : ℤ)-2*(H : ℤ)+(0 : ℤ)) = 2*s := by dsimp [s]; omega
  have es3 : 2*(m-1+1-(p : ℤ)-2*(H : ℤ)+(0 : ℤ)) = 2*s+2 := by dsimp [s]; omega
  have sg : (-1 : ℂ)^(m-(p : ℤ)-(H : ℤ)) =
      -(-1 : ℂ)^(m-(p : ℤ)-(H : ℤ)-1) := by
    simpa using sign_step (m-(p : ℤ)-(H : ℤ)-1)
  simp only [normalizedTerm, Nat.cast_zero]
  simp only [ex1, ex2, es1, es2, es3,
    pow_zero, Module.End.one_apply, Nat.factorial_zero, Nat.cast_one, mul_one]
  rw [step]
  simp only [pow_succ', Module.End.mul_apply, Nat.factorial_succ,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have es : ((s : ℂ)+1) = (m : ℂ)-(p : ℂ)-2*(H : ℂ) := by
    dsimp [s]
    push_cast
    ring
  rw [es]
  simp only [show m-1+1-(p : ℤ)-(H : ℤ)+(0 : ℤ) =
      m-(p : ℤ)-(H : ℤ) by omega, sg]
  field_simp
  ring

private theorem normalizedTerm_translation_succ (D : LatticeData)
    (hu : IsUnit D.G.det) (h24 : D.rank = 24) (H : ℕ) (m : ℤ)
    (u v : ActualTensor D hu) (huH : actualTensorL0 D hu u = (H : ℂ) • u)
    (a : Carrier D) (p q : ℕ) :
    normalizedTerm D hu (H+1) m (raising D hu u) v a p (q+1) =
      -((p : ℂ)+1)*normalizedTerm D hu H (m-1) u v a (p+1) (q+1) -
        ((m : ℂ)-(p : ℂ)-2*(H : ℂ)+(q : ℂ)+1)*
          normalizedTerm D hu H (m-1) u v a p (q+1) -
        (2*(H : ℂ)-(q : ℂ))*normalizedTerm D hu H (m-1) u v a p q := by
  let s : ℤ := m-(p : ℤ)-2*(H : ℤ)+(q : ℤ)
  let E : ℤ := m-(p : ℤ)-(H : ℤ)+(q : ℤ)
  have step := scalar_translation_step D hu a s ((T D hu ^ p) v) ((T D hu ^ (q+1)) u)
  have hp : (p.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero p
  have hq : (q.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero q
  have hps : (p : ℂ)+1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero p
  have hqs : (q : ℂ)+1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero q
  have ex0 : m+1-(p : ℤ)-((H+1 : ℕ) : ℤ)+((q+1 : ℕ) : ℤ) = E+1 := by dsimp [E]; omega
  have ex1 : m-1+1-((p+1 : ℕ) : ℤ)-(H : ℤ)+((q+1 : ℕ) : ℤ) = E := by dsimp [E]; omega
  have ex2 : m-1+1-(p : ℤ)-(H : ℤ)+((q+1 : ℕ) : ℤ) = E+1 := by dsimp [E]; omega
  have ex3 : m-1+1-(p : ℤ)-(H : ℤ)+(q : ℤ) = E := by dsimp [E]; omega
  have es0 : 2*(m+1-(p : ℤ)-2*((H+1 : ℕ) : ℤ)+((q+1 : ℕ) : ℤ)) = 2*s := by dsimp [s]; omega
  have es1 : 2*(m-1+1-((p+1 : ℕ) : ℤ)-2*(H : ℤ)+((q+1 : ℕ) : ℤ)) = 2*s := by dsimp [s]; omega
  have es2 : 2*(m-1+1-(p : ℤ)-2*(H : ℤ)+((q+1 : ℕ) : ℤ)) = 2*s+2 := by dsimp [s]; omega
  have es3 : 2*(m-1+1-(p : ℤ)-2*(H : ℤ)+(q : ℤ)) = 2*s := by dsimp [s]; omega
  simp only [normalizedTerm, ex0, ex1, ex2, ex3, es0, es1, es2, es3]
  rw [lowering_power_raising D hu h24 H u huH q]
  simp only [map_add, map_smul, smul_eq_mul]
  rw [step]
  simp only [pow_succ', Module.End.mul_apply, Nat.factorial_succ,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have es : ((s : ℂ)+1) = (m : ℂ)-(p : ℂ)-2*(H : ℂ)+(q : ℂ)+1 := by
    dsimp [s]
    push_cast
    ring
  rw [es, sign_step]
  field_simp
  ring

private theorem normalized_kernel_translation (D : LatticeData) (hu : IsUnit D.G.det)
    (h24 : D.rank = 24) (H K : ℕ) (hH : 2 ≤ H) (hK : 2 ≤ K) (m : ℤ)
    (u v : ActualTensor D hu)
    (huH : actualTensorL0 D hu u = (H : ℂ) • u)
    (hvK : actualTensorL0 D hu v = (K : ℂ) • v) :
    kernel D hu (H+1) K m (raising D hu u) v =
      (-((m : ℂ))) • kernel D hu H K (m-1) u v := by
  classical
  apply LinearMap.ext
  intro a
  let F := normalizedTerm D hu H (m-1) u v a
  let G := normalizedTerm D hu (H+1) m (raising D hu u) v a
  have nilpotent (L : ℕ) (hL : 2 ≤ L) (x : ActualTensor D hu)
      (hx : actualTensorL0 D hu x = (L : ℂ) • x) : (T D hu ^ (L-1)) x = 0 := by
    apply lowering_killed D hu (2*(L : ℤ)-3) x
    · rw [hx, h24]
      congr 1
      push_cast
      ring
    · omega
  have hn (q : ℕ) : F (K-1) q = 0 := by
    dsimp [F, normalizedTerm]
    rw [nilpotent K hK v hvK]
    simp
  have hr (p : ℕ) : F p (H-1) = 0 := by
    dsimp [F, normalizedTerm]
    rw [nilpotent H hH u huH]
    simp
  have cancellation := finite_translation_cancellation F G (K-1) (H-1)
    (H : ℂ) (m : ℂ) hn hr
    (normalizedTerm_translation_zero D hu H m u v a)
    (normalizedTerm_translation_succ D hu h24 H m u v huH a)
  have bounds : H+1-1 = H ∧ H-1+1 = H := by omega
  rw [bounds.2] at cancellation
  have expand (L J : ℕ) (n : ℤ) (x y : ActualTensor D hu) :
      kernel D hu L J n x y a =
        ∑ p ∈ Finset.range (J-1), ∑ q ∈ Finset.range (L-1),
          normalizedTerm D hu L n x y a p q := by
    simp only [kernel, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro q hq
    dsimp [normalizedTerm, K_R]
    congr 2
    congr 1
    omega
  simp only [LinearMap.smul_apply, smul_eq_mul]
  rw [expand, expand, bounds.1]
  exact cancellation

private theorem raising_weight (D : LatticeData) (hu : IsUnit D.G.det)
    (H : ℕ) (u : ActualTensor D hu)
    (huH : actualTensorL0 D hu u = (H : ℂ) • u) :
    actualTensorL0 D hu (raising D hu u) = ((H+1 : ℕ) : ℂ) • raising D hu u := by
  have bracket : actualTensorL0 D hu * raising D hu -
      raising D hu * actualTensorL0 D hu = raising D hu := by
    apply TensorProduct.ext'
    intro p t
    have h := congrArg (fun A : Module.End ℂ (Oscillator D) => A p ⊗ₜ[ℂ] t)
      (L_virasoro D (HalfFockSpectralFiberSource.actualInverse D)
        (HalfFockSpectralFiberSource.actualInverse_left D hu)
        (HalfFockSpectralFiberSource.actualInverse_right D hu) 0 (-1))
    norm_num at h
    simpa only [actualTensorL0, raising, tensorL, tensorEnd, LinearMap.sub_apply,
      Module.End.mul_apply, LinearMap.neg_apply, TensorProduct.map_tmul,
      LinearMap.id_apply, TensorProduct.sub_tmul, TensorProduct.neg_tmul] using h
  have h := LinearMap.congr_fun bracket u
  change actualTensorL0 D hu (raising D hu u) -
    raising D hu (actualTensorL0 D hu u) = raising D hu u at h
  rw [huH, map_smul, sub_eq_iff_eq_add] at h
  simpa only [Nat.cast_add, Nat.cast_one, add_smul, one_smul, add_comm] using h

/-- The original stress L(-1), restricted to the actual negative parity sector. -/
def translation (D : LatticeData) (hu : IsUnit D.G.det) :
    Module.End ℂ (paritySpace D hu (-1)) :=
  (fixedParitySlice D hu (-1)
    ⟨LatticeActualConformalState.omega D (HalfFockSpectralFiberSource.actualInverse D),
      (mem_fixedSpace D _).mpr
        (theta_omega_fixed D (HalfFockSpectralFiberSource.actualInverse D))⟩)[[0]]

private theorem translation_val (D : LatticeData) (hu : IsUnit D.G.det)
    (u : paritySpace D hu (-1)) :
    (translation D hu u).val = raising D hu u.val := by
  change (correctedField D hu
      (LatticeActualConformalState.omega D (HalfFockSpectralFiberSource.actualInverse D))).coeff
        (-2) u.val = _
  rw [LatticeHalfFockCorrectedConformal.correctedField_omega D hu _
    (HalfFockSpectralFiberSource.actualInverse_left D hu)]
  simp only [tensorStressField, HVertexOperator.coeff_of_coeff, stressCoeff,
    show (-2 : ℤ) % 2 = 0 by decide, ite_eq_left,
    show (-(-2 : ℤ)-4)/2 = -1 by decide, raising, tensorL]

private theorem basis_parity (D : LatticeData) (hu : IsUnit D.G.det)
    (i : OddMonomial D × LatticeTwistedGroundRealization.Half (groundRank D hu)) :
    LatticeHalfFockParityT.actualParity D hu (actualAmbientBasis D hu i) =
      ((-1 : ℂ)^oddWeight D i.1) • actualAmbientBasis D hu i := by
  have hi : actualAmbientBasis D hu i ∈ actualGrade D hu (oddWeight D i.1) := by
    simp only [actualGrade, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
    exact actual_basis_eigenvalue D hu i.1 i.2
  exact LatticeHalfFockParityT.actualParity_on_actualGrade D hu _ ⟨_,hi⟩

private theorem parity_repr (D : LatticeData) (hu : IsUnit D.G.det)
    (u : ActualTensor D hu)
    (i : OddMonomial D × LatticeTwistedGroundRealization.Half (groundRank D hu)) :
    (actualAmbientBasis D hu).repr (LatticeHalfFockParityT.actualParity D hu u) i =
      ((-1 : ℂ)^oddWeight D i.1) * (actualAmbientBasis D hu).repr u i := by
  classical
  let b := actualAmbientBasis D hu
  have heigen (j) : LatticeHalfFockParityT.actualParity D hu (b j) =
      ((-1 : ℂ)^oddWeight D j.1) • b j := basis_parity D hu j
  change b.repr (LatticeHalfFockParityT.actualParity D hu u) i =
    ((-1 : ℂ)^oddWeight D i.1) * b.repr u i
  conv_lhs => rw [← b.linearCombination_repr u]
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul,
    heigen, b.repr_self, Finsupp.smul_apply, smul_eq_mul]
  simp only [Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single i]
  · simp [mul_comm]
  · intro j hj hne
    simp [Finsupp.single_apply, hne]
  · intro hn
    have hz := Finsupp.notMem_support_iff.mp hn
    simp [hz]

private theorem negative_support (D : LatticeData) (hu : IsUnit D.G.det)
    (u : paritySpace D hu (-1))
    (i : OddMonomial D × LatticeTwistedGroundRealization.Half (groundRank D hu))
    (hi : i ∈ ((actualAmbientBasis D hu).repr u.val).support) :
    oddWeight D i.1 % 2 = 1 := by
  have hp := u.property
  simp only [paritySpace, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at hp
  have hc := congrArg (fun x => (actualAmbientBasis D hu).repr x i) hp
  rw [parity_repr] at hc
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul] at hc
  by_contra hn
  have he : oddWeight D i.1 % 2 = 0 := by omega
  rw [neg_one_pow_eq_pow_mod_two, he] at hc
  have hz : (actualAmbientBasis D hu).repr u.val i = 0 := by linear_combination hc / 2
  exact Finsupp.mem_support_iff.mp hi hz

/- proof_shape: normalizedCoefficient_translation: content
   admission_basis: escape-witness
   escape_witness: normalizedTerm_translation_zero and normalizedTerm_translation_succ
   derive the two weighted recurrences from actual stress transposition and the
   Virasoro bracket. finite_translation_cancellation consumes their literal
   successor shifts and the two actual nilpotent boundaries. -/
/-- All-vector input translation in standard modes, on the actual integer sector. -/
theorem normalizedCoefficient_translation (D : LatticeData) (hu : IsUnit D.G.det)
    (h24 : D.rank = 24) (m : ℤ) (u v : paritySpace D hu (-1)) :
    normalizedCoefficient D hu m (translation D hu u) v =
      (-((m : ℂ))) • normalizedCoefficient D hu (m-1) u v := by
  classical
  change ambientCoefficient D hu m (translation D hu u).val v.val =
    (-((m : ℂ))) • ambientCoefficient D hu (m-1) u.val v.val
  rw [translation_val]
  let b := actualAmbientBasis D hu
  rw [← b.linearCombination_repr u.val, ← b.linearCombination_repr v.val]
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum,
    LinearMap.sum_apply, map_smul, LinearMap.smul_apply, Finset.smul_sum,
    smul_smul, mul_left_comm (-((m : ℂ)))]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro i hi
  suffices heq : ambientCoefficient D hu m (raising D hu (b i)) (b j) =
      (-((m : ℂ))) • ambientCoefficient D hu (m-1) (b i) (b j) by
    rw [heq]
    module
  have hiOdd := negative_support D hu u i hi
  have hjOdd := negative_support D hu v j hj
  let H := (oddWeight D i.1+3)/2
  let K := (oddWeight D j.1+3)/2
  have hH : 2 ≤ H := by dsimp [H]; omega
  have hK : 2 ≤ K := by dsimp [K]; omega
  have hiH : actualTensorL0 D hu (b i) = (H : ℂ) • b i := by
    rw [actual_basis_eigenvalue, h24]
    have he : oddWeight D i.1+3 = 2*H := by dsimp [H]; omega
    congr 1
    have hc : (oddWeight D i.1 : ℂ)+3 = 2*(H : ℂ) := by exact_mod_cast he
    linear_combination hc / 2
  have hjK : actualTensorL0 D hu (b j) = (K : ℂ) • b j := by
    rw [actual_basis_eigenvalue, h24]
    have he : oddWeight D j.1+3 = 2*K := by dsimp [K]; omega
    congr 1
    have hc : (oddWeight D j.1 : ℂ)+3 = 2*(K : ℂ) := by exact_mod_cast he
    linear_combination hc / 2
  rw [homogeneous_coefficient D hu h24 (H+1) K m _ _
      (raising_weight D hu H _ hiH) hjK,
    homogeneous_coefficient D hu h24 H K (m-1) _ _ hiH hjK,
    normalized_kernel_translation D hu h24 H K hH hK m _ _ hiH hjK]
  have grade_eq : ((H+1 : ℕ) : ℤ)+(K : ℤ)-m-1 =
      (H : ℤ)+(K : ℤ)-(m-1)-1 := by omega
  rw [grade_eq]
  simp only [liftGrade, map_smul]

#print axioms normalizedCoefficient_translation

end D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner
