/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformCommonSpectralRotation
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformCommonSpectralRotation
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: []
   utility: none
   digest: The native rotation columns agree with the literal witness derivatives. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformCommonSpectralRows
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.UniformNativeCriticalMatrix

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformCommonSpectralRankTransport

open Matrix MvPolynomial TrivSqZeroExt
open scoped BigOperators Kronecker
open PeriodicMPSCommonSpectralJets
open PeriodicMPSUniformSpecialSpectralDomains (witnessK balancedWitnessCore)
open PeriodicMPSUniformNativeSliceReadout (rawSlicePolynomial)
open SevenSiteCriticalCertificate (sliceBlock observedRow rotationIndex)
open SevenSitePhysicalRankBridge (pauli_commutator_eq_rotationIndex)
open UniformNativeRotation (rotationPolynomial)

open private frameTangent from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSitePhysicalRankBridge
open private pauliFrame from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reflection.TwoQubitMarginalReflection
open private pauli from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteCriticalCertificate
open private certificate_pauli from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteReadoutDerivative
open private dual fst_dual snd_dual fstRing map_literalGram from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformCommonSpectralRankTransport

noncomputable section

private abbrev ComplexCore := Fin 2 → Core ℂ

private def physicalJet (A : ComplexCore) (g : Core ℂ) (i : Fin 2) : Core (DualNumber ℂ) :=
  fun a b => dual (A i a b) (∑ j, g i j * A j a b)

private theorem fst_physicalJet (A : ComplexCore) (g : Core ℂ) (i : Fin 2) :
    (physicalJet A g i).map (fstRing ℂ) = A i := by
  ext a b
  rfl

private def rotateInvariant (K B : ComplexCore) (g : Core ℂ) (a : Coordinate) : ℂ :=
  (coordinates (physicalJet K g) (physicalJet B (-gᵀ)) a).snd

private theorem rotateInvariant_jet (K B : ComplexCore) (g : Core ℂ) :
    (fun a => dual (coordinates K B a) (rotateInvariant K B g a)) =
      coordinates (physicalJet K g) (physicalJet B (-gᵀ)) := by
  funext a
  apply TrivSqZeroExt.ext
  · have h := congrFun (map_coordinates (fstRing ℂ)
      (physicalJet K g) (physicalJet B (-gᵀ))) a
    change (coordinates (physicalJet K g) (physicalJet B (-gᵀ)) a).fst =
      coordinates (fun i => (physicalJet K g i).map (fstRing ℂ))
        (fun i => (physicalJet B (-gᵀ) i).map (fstRing ℂ)) a at h
    simpa only [fst_dual, fst_physicalJet] using h.symm
  · rfl

private def liftMat {α β : Type*} (M : Matrix α β ℂ) : Matrix α β (DualNumber ℂ) :=
  M.map (inlHom ℂ ℂ)

private theorem transfer_physicalJet (K B : ComplexCore) (g : Core ℂ) :
    transfer (physicalJet K g) (physicalJet B (-gᵀ)) = liftMat (transfer K B) := by
  apply Matrix.ext
  intro a b
  apply TrivSqZeroExt.ext
  · simp [transfer, liftMat, Matrix.kroneckerMap_apply, physicalJet]
  · simp [transfer, liftMat, Matrix.kroneckerMap_apply, physicalJet, Fin.sum_univ_two]
    ring

private def pairGenerator (g : Core ℂ) : Matrix Bits Bits ℂ :=
  g ⊗ₖ (1 : Core ℂ) + (1 : Core ℂ) ⊗ₖ g

private def gramMatrix {R : Type*} [CommRing R] (m : ℕ) (K B : Fin 2 → Core R) :
    Matrix Bits Bits R := fun p q => literalGram K B m (p, q)

set_option maxHeartbeats 1800000 in
private theorem insertion_physicalJet (K B : ComplexCore) (g : Core ℂ) (p q : Bits) :
    insertion (physicalJet K g) (physicalJet B (-gᵀ)) (p, q) =
      liftMat (insertion K B (p, q)) +
        ∑ a : Bits, (DualNumber.eps : DualNumber ℂ) • liftMat
          ((pairGenerator g p a) • insertion K B (a, q) -
            (pairGenerator g a q) • insertion K B (p, a)) := by
  apply Matrix.ext
  rintro ⟨a, b⟩ ⟨c, d⟩
  apply TrivSqZeroExt.ext
  · simp [insertion, Matrix.kroneckerMap_apply, Matrix.mul_apply, liftMat, physicalJet,
      Matrix.smul_apply, Matrix.sum_apply, fst_sum]
  · have diag (i j : Fin 2) : (1 : Core ℂ) i j = if i = j then 1 else 0 := by simp [Matrix.one_apply]
    rcases p with ⟨p₁, p₂⟩
    rcases q with ⟨q₁, q₂⟩
    fin_cases p₁ <;> fin_cases p₂ <;> fin_cases q₁ <;> fin_cases q₂ <;>
      simp [insertion, pairGenerator, Matrix.kroneckerMap_apply, Matrix.mul_apply,
        liftMat, physicalJet, Matrix.smul_apply,
        Fintype.sum_prod_type, Fin.sum_univ_two, diag] <;> ring

private theorem snd_trace_lift (M N : Transfer ℂ) :
    (((DualNumber.eps : DualNumber ℂ) • liftMat M) * liftMat N).trace.snd =
      (M * N).trace := by
  rw [Matrix.smul_mul (DualNumber.eps : DualNumber ℂ) (liftMat M) (liftMat N)]
  have h : liftMat M * liftMat N = liftMat (M * N) :=
    ((RingHom.mapMatrix (inlHom ℂ ℂ)).map_mul M N).symm
  rw [h, Matrix.trace_smul]
  change (DualNumber.eps * ((M * N).map (inlHom ℂ ℂ)).trace).snd = _
  rw [← AddMonoidHom.map_trace]
  simp

/-- The independent complex ket/bra jet gives a commutator on the exposed
pair. Its residual transfer has zero first-order variation. -/
theorem gramDifferential_rotateInvariant (m : ℕ) (K B : ComplexCore) (g : Core ℂ) (p q : Bits) :
    gramDifferential m (coordinates K B) (rotateInvariant K B g) (p, q) =
      (pairGenerator g * gramMatrix m K B - gramMatrix m K B * pairGenerator g) p q := by
  rw [gramDifferential_apply, rotateInvariant_jet, ← literalGram_eq_chart, literalGram_eq_contraction]
  unfold contraction
  rw [transfer_physicalJet, insertion_physicalJet, add_mul, Matrix.sum_mul, Matrix.trace_add,
    Matrix.trace_sum, snd_add, snd_sum, Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply]
  have hp : liftMat (transfer K B) ^ m = liftMat (transfer K B ^ m) :=
    ((RingHom.mapMatrix (inlHom ℂ ℂ)).map_pow (transfer K B) m).symm
  rw [hp]
  have hz : (liftMat (insertion K B (p, q)) * liftMat (transfer K B ^ m)).trace.snd = 0 := by
    change (((RingHom.mapMatrix (inlHom ℂ ℂ)) (insertion K B (p, q)) *
      (RingHom.mapMatrix (inlHom ℂ ℂ)) (transfer K B ^ m)).trace).snd = 0
    rw [← map_mul]
    change (((insertion K B (p, q) * transfer K B ^ m).map (inlHom ℂ ℂ)).trace).snd = 0
    rw [← AddMonoidHom.map_trace]
    rfl
  rw [hz, zero_add, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [snd_trace_lift, sub_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.trace_sub,
    Matrix.trace_smul, Matrix.trace_smul, smul_eq_mul, smul_eq_mul]
  simp only [gramMatrix, literalGram_eq_contraction, contraction]
  rw [mul_comm (pairGenerator g a q)]

private theorem pauliGram_eq_trace (G : Matrix Bits Bits ℂ) (ab : Fin 4 × Fin 4) :
    pauliGram Complex.I (fun p => G p.1 p.2) ab =
      ((pauli Complex.I ab.1 ⊗ₖ pauli Complex.I ab.2) * G).trace := by
  simp only [pauliGram, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]

private theorem frameTangent_commutator (j : Fin 3) (a : Fin 4) :
    pauli Complex.I a * frameTangent j - frameTangent j * pauli Complex.I a =
      ((rotationIndex j a).1 : ℂ) • pauli Complex.I (rotationIndex j a).2 := by
  simp only [certificate_pauli]
  rw [← pauli_commutator_eq_rotationIndex]
  simp only [frameTangent, mul_add, add_mul]
  have hscalar (c : ℂ) : pauliFrame a * (c • (1 : Core ℂ)) =
      (c • (1 : Core ℂ)) * pauliFrame a := by simp
  split <;> simp only [hscalar, mul_zero, zero_mul, add_zero, add_sub_add_right_eq_sub, smul_sub]
  all_goals
    rw [Matrix.mul_smul (pauliFrame a) (-Complex.I / 2) (pauliFrame j.succ),
      Matrix.smul_mul (-Complex.I / 2) (pauliFrame j.succ) (pauliFrame a)]
    simp only [neg_div, neg_smul]
    abel

private theorem kronecker_sub_left (A B C : Core ℂ) :
    (A - B) ⊗ₖ C = A ⊗ₖ C - B ⊗ₖ C := by
  ext i j
  simp [Matrix.kroneckerMap_apply, sub_mul]

private theorem kronecker_sub_right (A B C : Core ℂ) :
    A ⊗ₖ (B - C) = A ⊗ₖ B - A ⊗ₖ C := by
  ext i j
  simp [Matrix.kroneckerMap_apply, mul_sub]

private theorem pairCommutator (A B g : Core ℂ) :
    (A ⊗ₖ B) * pairGenerator g - pairGenerator g * (A ⊗ₖ B) =
      (A * g - g * A) ⊗ₖ B + A ⊗ₖ (B * g - g * B) := by
  simp only [pairGenerator, mul_add, add_mul, ← Matrix.mul_kronecker_mul, mul_one, one_mul,
    kronecker_sub_left, kronecker_sub_right]
  abel

theorem pauliGram_rotateInvariant (m : ℕ) (K B : ComplexCore) (j : Fin 3) (ab : Fin 4 × Fin 4) :
    pauliGram Complex.I (gramDifferential m (coordinates K B)
      (rotateInvariant K B (frameTangent j))) ab =
        ((rotationIndex j ab.1).1 : ℂ) *
          pauliGram Complex.I (gramChart m (coordinates K B)) ((rotationIndex j ab.1).2, ab.2) +
        ((rotationIndex j ab.2).1 : ℂ) *
          pauliGram Complex.I (gramChart m (coordinates K B)) (ab.1, (rotationIndex j ab.2).2) := by
  let G := gramMatrix m K B
  let P := pairGenerator (frameTangent j)
  have hD : gramDifferential m (coordinates K B) (rotateInvariant K B (frameTangent j)) =
      fun p => (P * G - G * P) p.1 p.2 := by
    funext ab
    rcases ab with ⟨p, q⟩
    exact gramDifferential_rotateInvariant m K B (frameTangent j) p q
  have hG : gramChart m (coordinates K B) = fun p => G p.1 p.2 := by
    funext ab
    exact (literalGram_eq_chart K B m ab).symm
  rw [hD, hG, pauliGram_eq_trace, pauliGram_eq_trace, pauliGram_eq_trace]
  let O : Matrix Bits Bits ℂ := pauli Complex.I ab.1 ⊗ₖ pauli Complex.I ab.2
  change (O * (P * G - G * P)).trace = _
  have htr : (O * (P * G - G * P)).trace = ((O * P - P * O) * G).trace := by
    simp only [mul_sub, sub_mul, Matrix.trace_sub, ← mul_assoc O P, ← mul_assoc O G]
    rw [Matrix.trace_mul_cycle O G P, mul_assoc P O]
  rw [htr]
  dsimp only [O, P]
  rw [pairCommutator, frameTangent_commutator, frameTangent_commutator, smul_kronecker,
    kronecker_smul, add_mul, Matrix.trace_add, smul_mul_assoc, smul_mul_assoc,
    Matrix.trace_smul, Matrix.trace_smul, smul_eq_mul, smul_eq_mul]

theorem eval_rotationPolynomial_eq_invariant (m : ℕ) (x : Fin 5 → ℂ) (K B : ComplexCore)
    (h : coordinates K B = sliceCoordinates Complex.I x) (j : Fin 3) (ab : Fin 4 × Fin 4) :
    eval x (rotationPolynomial m j ab) = pauliGram Complex.I
      (gramDifferential m (coordinates K B) (rotateInvariant K B (frameTangent j))) ab := by
  rw [pauliGram_rotateInvariant, h]
  simp only [rotationPolynomial, map_add, map_mul, map_intCast, eval_rawSlicePolynomial_eq_pauliGram]

end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformCommonSpectralRankTransport
