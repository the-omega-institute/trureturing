/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformMovingFrameColumns
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformMovingFrameColumns
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: []
   utility: none
   digest: Native columns on the paired section. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformMovingFrameChart
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformMovingFrameRows

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformMovingFrame

open Matrix MvPolynomial TrivSqZeroExt
open scoped Matrix Kronecker
open PeriodicMPSUniformAntisymmetricTransfer (BondMatrix TransferMatrix mixedRaw)
open PeriodicMPSUniformHardCoreTransferRecurrence (TwoBits)
open PeriodicMPSUniformVerticalSectionRank (transverseKet)
open SevenSiteCriticalCertificate (observedRow)
open UniformNativeCriticalMatrix (criticalMatrix)
open UniformNativeRotation (rotationPolynomial)
open PeriodicMPSUniformNativeSliceReadout (rawSlicePolynomial)
open private sectionKet_trace sectionBra_trace from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformMovingFrameSection
open private trace_scaleCore from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformMovingFrameDivisor
open private balance_inverse from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformMovingFrame
open private rowOf from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformMovingFrameRows
open private sectionBra from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformVerticalSectionRank
open private pauliReadLinear rotation_eq_eval from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformMovingFrameNative
open private value_mul from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformMovingFrame

noncomputable section

variable {E : Type*} [Field E] [Algebra ℂ E]

/-- Native columns in order: five coordinate speeds, radial speed and
three rotations. -/
def nativeColumn (v : Fin 5 → E) (a : E) (c : Fin 3 → E) : Fin 9 → E :=
  ![v 0, v 1, v 2, v 3, v 4, a, c 0, c 1, c 2]

omit [Algebra ℂ E] in
private theorem nativeColumn_mulVec (N : Matrix (Fin 10) (Fin 9) E)
    (v : Fin 5 → E) (a : E) (c : Fin 3 → E) (i : Fin 10) :
    (N *ᵥ nativeColumn v a c) i =
      (∑ j : Fin 5, v j * N i (Fin.castLE (by decide) j)) + a * N i 5 +
        (∑ j : Fin 3, c j * N i (Fin.natAdd 6 j)) := by
  simp [Matrix.mulVec, dotProduct, nativeColumn, Fin.sum_univ_succ]
  ring

def sectionPauliColumn (x : Fin 5 → E) (τ : E) (W : TransferMatrix E) : Fin 10 → E :=
  fun i => pauliRead (pairFrame (sectionBalancedKetFrame x τ) * W *
    pairFrame (sectionBalancedBraInverse x τ)) (observedRow i)

omit [Algebra ℂ E] in
theorem sectionFrame_inverse (x : Fin 5 → E) (hs : sectionTraceSum x ≠ 0)
    (τ : E) (ht : τ ≠ 0) :
    let g := sectionBalancedKetFrame x τ
    let h := sectionBalancedBraInverse x τ
    h * g = 1 ∧ g * h = 1 := by
  dsimp only
  let A := transverseKet (0 : E)
  let B := scaleCore (sectionTraceSum x)⁻¹ (sectionBra x)
  have hsum : traces A 0 * traces B 0 + traces A 1 * traces B 1 = 1 := by
    rw [sectionKet_trace, trace_scaleCore, trace_scaleCore, sectionBra_trace]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_mul, ← mul_add]
    exact inv_mul_cancel₀ hs
  obtain ⟨h₁, h₂⟩ := traceFrame_inverse (traces A) (traces B) hsum
  have hg := balance_inverse (mul_inv_cancel₀ ht)
  have hh := balance_inverse (inv_mul_cancel₀ ht)
  change (_ * balance τ⁻¹) * (balance τ * _) = 1 ∧
    (balance τ * _) * (_ * balance τ⁻¹) = 1
  exact ⟨by rw [mul_assoc, ← mul_assoc (balance τ⁻¹), hh, one_mul, h₁],
    by rw [mul_assoc, ← mul_assoc (traceFrame (traces A) (traces B)), h₂, one_mul, hg]⟩

theorem native_section_raw_column (m : ℕ) (x dx : Fin 5 → E) (dμ : E)
    (hs : sectionTraceSum x ≠ 0) (ha : sectionImbalance x ≠ 0)
    {τ : E} (ht : τ ≠ 0)
    (hτ : τ ^ 2 * ((sectionTraceSum x)⁻¹ * sectionImbalance x) =
      (sectionTraceSum x)⁻¹ ^ 3 * sectionInitialBraMixedTrace x) :
    let W := mixedRaw (transverseKet (inr dμ : DualNumber E)) (sectionBraJet x dx) m
    let N := (criticalMatrix m).map (aeval (sectionChart x τ))
    ∃ v : Fin 9 → E, sectionPauliColumn x τ (jetTangent W) = N *ᵥ v := by
  obtain ⟨g, h, _, _, _, _, z, _, hz⟩ :=
    native_section_unnormalized_jet m x dx dμ hs ha ht hτ
  let y : Fin 5 → DualNumber E := fun j => ⟨x j, dx j⟩
  let a : DualNumber E := sectionTraceSum y ^ (m + 2)
  let c := rotationCoefficients (jetTangent g * jetValue h)
  refine ⟨nativeColumn (fun j => a.fst * (z j).snd) a.snd (fun j => -(a.fst * c j)), ?_⟩
  funext i
  rw [nativeColumn_mulVec]
  have hzi := (hz i).2
  change sectionPauliColumn x τ
    (jetTangent (mixedRaw (transverseKet (inr dμ : DualNumber E)) (sectionBraJet x dx) m)) i =
    _ at hzi
  rw [hzi]
  let N := (criticalMatrix m).map (aeval (sectionChart x τ))
  change a.fst * ((∑ j : Fin 5, (z j).snd * N i (Fin.castLE (by decide) j)) -
      ∑ j : Fin 3, c j * N i (Fin.natAdd 6 j)) + a.snd * N i 5 =
    (∑ j : Fin 5, (a.fst * (z j).snd) * N i (Fin.castLE (by decide) j)) + a.snd * N i 5 +
      ∑ j : Fin 3, -(a.fst * c j) * N i (Fin.natAdd 6 j)
  simp only [mul_sub, Finset.mul_sum, ← mul_assoc, neg_mul, Finset.sum_neg_distrib]
  ring

omit [Algebra ℂ E] in
private theorem pairGenerator_conjugate (g h H : BondMatrix E) (hgh : g * h = 1) :
    pairGenerator (g * H * h) = pairFrame g * pairGenerator H * pairFrame h := by
  simp only [pairGenerator, pairFrame, mul_add, add_mul, ← Matrix.mul_kronecker_mul,
    mul_one, hgh]

omit [Algebra ℂ E] in
private theorem physicalTangent_frame (g h H : BondMatrix E) (hhg : h * g = 1) (hgh : g * h = 1)
    (W : TransferMatrix E) :
    pairFrame g * physicalTangent H W * pairFrame h =
      physicalTangent (g * H * h) (pairFrame g * W * pairFrame h) := by
  have h₀ : pairFrame h * pairFrame g = 1 := by rw [← pairFrame_mul, hhg, pairFrame_one]
  rw [physicalTangent, physicalTangent, pairGenerator_conjugate g h H hgh]
  simp only [mul_sub, sub_mul, Matrix.mul_assoc]
  have e (X : TransferMatrix E) : pairFrame h * (pairFrame g * X) = X := by
    rw [← mul_assoc, h₀, one_mul]
  rw [e, e]

private theorem aligned_section_radial (m : ℕ) (x : Fin 5 → E) (τ : E)
    (hs : sectionTraceSum x ≠ 0)
    (ha : traces (mix (sectionBalancedKetFrame x τ) (transverseKet 0)) = ![1,0])
    (hb : traces (mix (sectionBalancedBraInverse x τ)ᵀ
      (scaleCore (sectionTraceSum x)⁻¹ (sectionBra x))) = ![1,0])
    (hk : mixedTrace (mix (sectionBalancedKetFrame x τ) (transverseKet 0)) =
      mixedTrace (mix (sectionBalancedBraInverse x τ)ᵀ
        (scaleCore (sectionTraceSum x)⁻¹ (sectionBra x))))
    (ht : τ ≠ 0) (ab : Fin 4 × Fin 4) :
    pauliRead (pairFrame (sectionBalancedKetFrame x τ) *
      mixedRaw (transverseKet 0) (sectionBra x) m * pairFrame (sectionBalancedBraInverse x τ)) ab =
        sectionTraceSum x ^ (m + 2) * aeval (sectionChart x τ) (rawSlicePolynomial m ab) := by
  let g := sectionBalancedKetFrame x τ
  let h := sectionBalancedBraInverse x τ
  let A : Core E := transverseKet 0
  let B := sectionBra x
  let s := sectionTraceSum x
  let C := scaleCore s⁻¹ B
  have hB : scaleCore s C = B := by
    funext j
    change s • (s⁻¹ • B j) = B j
    rw [smul_smul, mul_inv_cancel₀ hs, one_smul]
  have hW : mixedRaw A B m = s ^ (m + 2) • mixedRaw A C m :=
    hB ▸ mixedRaw_scaleBra A C s m
  have hAlign := rawSlice_eq_pauliRead m (mix g A) (mix hᵀ C) ha hb hk ab
  change aeval (sectionChart x τ) _ = _ at hAlign
  rw [mixedRaw_mix g h (sectionFrame_inverse x hs τ ht).1] at hAlign
  change pauliRead (pairFrame g * mixedRaw A B m * pairFrame h) ab = _
  rw [hW, Matrix.mul_smul, Matrix.smul_mul]
  exact ((pauliReadLinear ab).map_smul _ _).trans (congrArg ((s ^ (m + 2)) * ·) hAlign.symm)

theorem native_section_rotation_column (m : ℕ) (x : Fin 5 → E)
    (H : BondMatrix E) (hs : sectionTraceSum x ≠ 0) {τ : E} (ht : τ ≠ 0)
    (ha : traces (mix (sectionBalancedKetFrame x τ) (transverseKet 0)) = ![1,0])
    (hb : traces (mix (sectionBalancedBraInverse x τ)ᵀ
      (scaleCore (sectionTraceSum x)⁻¹ (sectionBra x))) = ![1,0])
    (hk : mixedTrace (mix (sectionBalancedKetFrame x τ) (transverseKet 0)) =
      mixedTrace (mix (sectionBalancedBraInverse x τ)ᵀ
        (scaleCore (sectionTraceSum x)⁻¹ (sectionBra x)))) :
    let N := (criticalMatrix m).map (aeval (sectionChart x τ))
    ∃ v : Fin 9 → E,
      sectionPauliColumn x τ (physicalTangent H (mixedRaw (transverseKet 0) (sectionBra x) m)) =
        N *ᵥ v := by
  dsimp only
  let g := sectionBalancedKetFrame x τ
  let h := sectionBalancedBraInverse x τ
  let c := rotationCoefficients (g * H * h)
  let s := sectionTraceSum x
  let W := pairFrame g * mixedRaw (transverseKet 0) (sectionBra x) m * pairFrame h
  refine ⟨nativeColumn 0 0 (fun j => s ^ (m + 2) * c j), ?_⟩
  funext i
  rw [nativeColumn_mulVec]
  change pauliRead (pairFrame g * physicalTangent H _ * pairFrame h) _ = _
  obtain ⟨h₁, h₂⟩ := sectionFrame_inverse x hs τ ht
  rw [physicalTangent_frame g h H h₁ h₂]
  change pauliRead (physicalTangent (g * H * h) W) (observedRow i) = _
  rw [pauliRead_physicalTangent]
  have hW := aligned_section_radial m x τ hs ha hb hk ht
  have hrot (j : Fin 3) : ((criticalMatrix m).map (aeval (sectionChart x τ))) i (Fin.natAdd 6 j) =
      aeval (sectionChart x τ) (rotationPolynomial m j (observedRow i)) := by
    fin_cases j <;> rfl
  let N := (criticalMatrix m).map (aeval (sectionChart x τ))
  change (∑ j, c j * pauliRead (physicalTangent (rotationGenerator j) W) (observedRow i)) =
    (∑ j : Fin 5, (0 : E) * N i (Fin.castLE (by decide) j)) + 0 * N i 5 +
      ∑ j : Fin 3, s ^ (m + 2) * c j * N i (Fin.natAdd 6 j)
  have e (ab : Fin 4 × Fin 4) : pauliRead W ab =
      s ^ (m + 2) * aeval (sectionChart x τ) (rawSlicePolynomial m ab) := hW ab
  have hr (j : Fin 3) : N i (Fin.natAdd 6 j) =
      aeval (sectionChart x τ) (rotationPolynomial m j (observedRow i)) := hrot j
  simp_rw [pauliRead_rotation, e, hr]
  simp only [zero_mul, Finset.sum_const_zero, add_zero, zero_add]
  apply Finset.sum_congr rfl
  intro j _
  simp [rotationPolynomial]
  ring

end
end D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformMovingFrame
