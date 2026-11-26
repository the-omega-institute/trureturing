/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteReadoutDerivative
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteReadoutDerivative
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: []
   utility: none
   digest: Normalized readout rank and the radial column. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteCompactReadout
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteCriticalCertificate

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.SevenSiteReadoutDerivative

open Matrix Function Filter
open scoped Matrix Kronecker Topology Matrix.Norms.Elementwise
open TwoQubitMarginalReflection (Density)
open PeriodicMPSCompactReadout (Readout pauliIndices readout_apply)
open PeriodicMPSUniformHardCoreLocalization (normalizedMarginal normalizedMarginal_eq_rawTwo)
open SevenSiteCriticalCertificate (alignedInvariants observation observedRow)

open private pauliFrame pauli_explicit from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reflection.TwoQubitMarginalReflection
open private pauli readout from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteCriticalCertificate

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The certificate prepends the norm to the nine Pauli observations. -/
theorem observedRow_succ (i : Fin 9) : observedRow i.succ = pauliIndices i := by
  fin_cases i <;> rfl

private theorem certificate_pauli (i : Fin 4) : pauli Complex.I i = pauliFrame i := by
  refine Fin.cases rfl (fun j => ?_) i
  change pauli Complex.I j.succ = PeriodicMPSUniformChirality.pauli j
  rw [pauli_explicit]
  fin_cases j <;> rfl

/-- Specializing the two formal trace blocks to conjugate actual invariants gives
the literal unnormalized norm and nine Pauli readouts in the certificate's row order. -/
theorem observedRows_eq_rawReadout (A : Fin 2 → PeriodicMPSParentIntersection.Bond)
    (hA₀ : (A 0).trace = 1) (hA₁ : (A 1).trace = 0) :
    (fun j => (observation Complex.I (alignedInvariants A) (star ∘ alignedInvariants A)
      (observedRow j)).re) =
      Fin.cons (PeriodicMPSTwoSiteAmbiguity.rawTwo A 3).trace.re
        (PeriodicMPSCompactReadout.readout (PeriodicMPSTwoSiteAmbiguity.rawTwo A 3)) := by
  let M := PeriodicMPSTwoSiteAmbiguity.rawTwo A 3
  have contraction (a b : Fin 4) :
      observation Complex.I (alignedInvariants A) (star ∘ alignedInvariants A) (a, b) =
        ((pauliFrame a ⊗ₖ pauliFrame b) * M).trace := by
    simp only [observation, readout, certificate_pauli,
      SevenSiteCriticalCertificate.rawGram_eq_rawTwo A hA₀ hA₁, M,
      Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.kroneckerMap_apply]
    rw [Finset.sum_comm]
  funext j
  refine Fin.cases ?_ (fun i => ?_) j
  · change (observation Complex.I _ _ (0, 0)).re = M.trace.re
    rw [contraction, show pauliFrame 0 = 1 from rfl, one_kronecker_one, Matrix.one_mul]
  · rw [observedRow_succ]
    change (observation Complex.I _ _ _).re = PeriodicMPSCompactReadout.readout M i
    rw [readout_apply, ← contraction]

/-- The normalized literal readings divide the Pauli rows by the norm row. -/
theorem normalizedReadout_eq_smul (A : Fin 2 → PeriodicMPSParentIntersection.Bond) :
    PeriodicMPSCompactReadout.readout (normalizedMarginal 5 A) =
      (PeriodicMPSTwoSiteAmbiguity.rawTwo A 3).trace.re⁻¹ •
        PeriodicMPSCompactReadout.readout (PeriodicMPSTwoSiteAmbiguity.rawTwo A 3) := by
  rw [show (5 : ℕ) = 3 + 2 from rfl, normalizedMarginal_eq_rawTwo, map_smul]

/-- The derivative of the nine normalized rows is injective exactly when the
derivative of the ten raw rows, augmented by their radial column, is injective.
The domain of the augmented map is the parameter tangent space times the radial line. -/
theorem injective_fderiv_normalized_iff (n : E → ℝ) (v : E → Readout) (x : E)
    (hn : DifferentiableAt ℝ n x) (hv : DifferentiableAt ℝ v x) (hx : n x ≠ 0) :
    Injective (fderiv ℝ (fun y => (n y)⁻¹ • v y) x) ↔
      Injective (fun w : E × ℝ =>
        (fderiv ℝ n x w.1 + w.2 * n x, fderiv ℝ v x w.1 + w.2 • v x)) := by
  let g := fun y => (n y)⁻¹ • v y
  have hg : DifferentiableAt ℝ g x := (hn.inv hx).smul hv
  have hval (y : E) (hy : n y ≠ 0) : n y • g y = v y := by
    simp [g, smul_smul, mul_inv_cancel₀ hy]
  have hrad (s : ℝ) : s • v x = (s * n x) • g x :=
    (congrArg (s • ·) (hval x hx).symm).trans (smul_smul _ _ _)
  have hderiv : fderiv ℝ (fun y => n y • g y) x = fderiv ℝ v x := by
    exact Filter.EventuallyEq.fderiv_eq ((hn.continuousAt.eventually_ne hx).mono hval)
  have hprod (a : E) : n x • fderiv ℝ g x a + fderiv ℝ n x a • g x =
      fderiv ℝ v x a := by
    rw [← hderiv]
    change _ = fderiv ℝ (n • g) x a
    rw [fderiv_smul hn hg]
    rfl
  let D : E × ℝ →ₗ[ℝ] ℝ × Readout :=
    ((fderiv ℝ n x).toLinearMap.prod (fderiv ℝ v x).toLinearMap).comp
      (LinearMap.fst ℝ E ℝ) +
      (LinearMap.toSpanSingleton ℝ (ℝ × Readout) (n x, v x)).comp (LinearMap.snd ℝ E ℝ)
  change Injective (fderiv ℝ g x).toLinearMap ↔ Injective D
  rw [← (fderiv ℝ g x).toLinearMap.ker_eq_bot, ← D.ker_eq_bot]
  simp only [LinearMap.ker_eq_bot', ContinuousLinearMap.coe_coe]
  have hDn (a : E) (s : ℝ) : (D (a, s)).1 = fderiv ℝ n x a + s * n x := rfl
  have hDv (a : E) (s : ℝ) : (D (a, s)).2 = fderiv ℝ v x a + s • v x := rfl
  constructor
  · intro h w hw
    obtain ⟨a, s⟩ := w
    have hd₁ : fderiv ℝ n x a + s * n x = 0 :=
      (hDn a s).symm.trans (congrArg Prod.fst hw)
    have hd₂ : fderiv ℝ v x a + s • v x = 0 :=
      (hDv a s).symm.trans (congrArg Prod.snd hw)
    rw [hrad, ← hprod a, add_assoc, ← add_smul, hd₁, zero_smul, add_zero]
      at hd₂
    have ha : a = 0 := h a ((smul_eq_zero.mp hd₂).resolve_left hx)
    subst a
    rw [map_zero, zero_add] at hd₁
    exact Prod.ext rfl ((mul_eq_zero.mp hd₁).resolve_right hx)
  · intro h a ha
    let s := -(fderiv ℝ n x a) / n x
    have hs : fderiv ℝ n x a + s * n x = 0 := by
      rw [show s * n x = -(fderiv ℝ n x a) from div_mul_cancel₀ _ hx, add_neg_cancel]
    have hd : D (a, s) = 0 := by
      apply Prod.ext
      · exact (hDn a s).trans hs
      · rw [hDv, hrad, ← hprod a, ha, smul_zero, zero_add,
          ← add_smul, hs, zero_smul]
        rfl
    exact congrArg Prod.fst (h (a, s) hd)

#print axioms observedRows_eq_rawReadout
#print axioms injective_fderiv_normalized_iff

end

end D5.S3.Quantum.TensorNetworks.SevenSiteReadoutDerivative
