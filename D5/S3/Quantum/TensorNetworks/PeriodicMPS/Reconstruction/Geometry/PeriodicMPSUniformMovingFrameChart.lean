/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformMovingFrameChart
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformMovingFrameChart
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: []
   utility: none
   digest: Algebraic charts on generic paired sections. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformMovingFrameDivisor

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformMovingFrame

open Matrix MvPolynomial
open scoped Matrix
open PeriodicMPSUniformAntisymmetricTransfer (BondMatrix mixedRaw)
open PeriodicMPSUniformVerticalSectionRank (transverseKet DivisorRing divisorRoots genericSection)
open PeriodicMPSUniformVerticalPrimeExclusion (Roots pairing rootSum obstruction)
open UniformNativeCriticalMatrix (criticalMatrix)

open private sectionBra divisorRoots_eq_zero affine_ne_zero from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformVerticalSectionRank
open private trace_scaleCore aligned_scaleBra
  from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformMovingFrameDivisor
open private sectionKet_trace sectionBra_trace
  from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformMovingFrameSection
open private imbalance from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformVerticalPrimeExclusion
open private balance_mix balance_inverse from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformMovingFrame

noncomputable section

abbrev SectionPolynomial (f : Roots) := Polynomial (FractionRing (DivisorRing f))
abbrev SectionField (f : Roots) [IsDomain (DivisorRing f)] := AlgebraicClosure (FractionRing (SectionPolynomial f))


instance (f : Roots) [IsDomain (DivisorRing f)] : Algebra ℂ (SectionField f) :=
  ((algebraMap (FractionRing (SectionPolynomial f)) (SectionField f)).comp
    (algebraMap (SectionPolynomial f) (FractionRing (SectionPolynomial f)))).comp
      (algebraMap ℂ (SectionPolynomial f)) |>.toAlgebra

def sectionFieldMap (f : Roots) [IsDomain (DivisorRing f)] :
    SectionPolynomial f →+* SectionField f :=
  (algebraMap (FractionRing (SectionPolynomial f)) (SectionField f)).comp
    (algebraMap (SectionPolynomial f) (FractionRing (SectionPolynomial f)))

theorem sectionFieldMap_injective (f : Roots) [IsDomain (DivisorRing f)] :
    Function.Injective (sectionFieldMap f) :=
  (algebraMap (FractionRing (SectionPolynomial f)) (SectionField f)).injective.comp
    (IsFractionRing.injective (SectionPolynomial f) _)

private theorem sectionInitialBraMixedTrace_polynomial {F : Type*} [Field F]
    (r s t u : F) :
    sectionInitialBraMixedTrace (![Polynomial.C r, Polynomial.C s,
      Polynomial.C t, Polynomial.C u, Polynomial.X] : Fin 5 → Polynomial F) =
        Polynomial.C (((t+u) - (r+s)) * (r-s) * (t-u)) * Polynomial.X +
          Polynomial.C ((t+u) * (r^2+s^2) + ((t+u)-(r+s)) * (r*u+s*t) -
            (r+s) * (t^2+u^2)) := by
  unfold sectionInitialBraMixedTrace
  rw [section_bra_mixedTrace]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
    map_add, map_sub, map_pow, map_mul]
  ring

/-- The generic section has all three nonzero quantities needed for
normalization and separable balancing on every unobstructed pairing. -/
theorem genericSection_frames_defined {f : Roots} [IsDomain (DivisorRing f)]
    (htrace : ¬ f ∣ rootSum) (m : ℕ) (j : Fin 3) (hj : ¬ f ∣ obstruction m j) :
    let x := genericSection (divisorRoots f) j
    sectionTraceSum x ≠ 0 ∧ sectionImbalance x ≠ 0 ∧ sectionInitialBraMixedTrace x ≠ 0 := by
  let φ := divisorRoots f
  let r := φ (X (pairing j 0))
  let s := φ (X (pairing j 1))
  let t := φ (X (pairing j 2))
  let u := φ (X (pairing j 3))
  change sectionTraceSum ![Polynomial.C r, Polynomial.C s, Polynomial.C t, Polynomial.C u,
      Polynomial.X] ≠ 0 ∧ sectionImbalance ![Polynomial.C r, Polynomial.C s, Polynomial.C t,
      Polynomial.C u, Polynomial.X] ≠ 0 ∧ _
  have hobs : φ (obstruction m j) ≠ 0 := fun hz => hj ((divisorRoots_eq_zero f _).mp hz)
  have hobs' : (r+s) * (t+u) * ((r+s)-(t+u)) * (r^m-s^m) * (t^m-u^m) ≠ 0 := by
    simpa only [obstruction, imbalance, map_add, map_sub, map_mul, map_pow] using hobs
  rcases mul_ne_zero_iff.mp hobs' with ⟨h₀, h₁⟩
  rcases mul_ne_zero_iff.mp h₀ with ⟨h₂, h₃⟩
  rcases mul_ne_zero_iff.mp h₂ with ⟨_, h₄⟩
  have hrs : r - s ≠ 0 := sub_ne_zero.mpr fun h => h₃ (by rw [h, sub_self])
  have htu : t - u ≠ 0 := sub_ne_zero.mpr fun h => h₁ (by rw [h, sub_self])
  have hsum : r + s + (t + u) ≠ 0 := by
    have h0 : φ rootSum ≠ 0 := fun hz => htrace ((divisorRoots_eq_zero f _).mp hz)
    have he : r + s + (t + u) = φ rootSum := by
      unfold rootSum
      rw [map_sum, ← Equiv.sum_comp (pairing j) (fun i : Fin 4 => φ (X i))]
      simp [Fin.sum_univ_four, r, s, t, u, add_assoc]
    exact he.trans_ne h0
  refine ⟨?_, ?_, ?_⟩
  · change (Polynomial.C r + Polynomial.C s + (Polynomial.C t + Polynomial.C u)) ≠ 0
    have he : Polynomial.C (r + s + (t + u)) =
        Polynomial.C r + Polynomial.C s + (Polynomial.C t + Polynomial.C u) := by
      exact ((Polynomial.C.map_add (r+s) (t+u)).trans
        (congrArg₂ (· + ·) (Polynomial.C.map_add r s) (Polynomial.C.map_add t u)))
    exact he ▸ Polynomial.C_ne_zero.mpr hsum
  · change (Polynomial.C r + Polynomial.C s - (Polynomial.C t + Polynomial.C u)) ≠ 0
    have he : Polynomial.C (r + s - (t + u)) =
        Polynomial.C r + Polynomial.C s - (Polynomial.C t + Polynomial.C u) := by
      exact ((Polynomial.C.map_sub (r+s) (t+u)).trans
        (congrArg₂ (· - ·) (Polynomial.C.map_add r s) (Polynomial.C.map_add t u)))
    exact he ▸ Polynomial.C_ne_zero.mpr h₄
  · change sectionInitialBraMixedTrace ![Polynomial.C r, Polynomial.C s, Polynomial.C t,
      Polynomial.C u, Polynomial.X] ≠ 0
    rw [sectionInitialBraMixedTrace_polynomial]
    exact affine_ne_zero (mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr
      (sub_ne_zero.mp h₄).symm) hrs) htu)

variable {E : Type*} [Field E] [IsAlgClosed E]

/-- A balanced algebraic chart point for a section at nonzero trace and
nonzero mixed traces. The square root lives in the algebraically closed
extension of the section function field. -/
theorem exists_section_chart (x : Fin 5 → E)
    (hs : sectionTraceSum x ≠ 0) (ha : sectionImbalance x ≠ 0)
    (hb : sectionInitialBraMixedTrace x ≠ 0) :
    let s := (sectionTraceSum x)⁻¹
    let A := transverseKet (0 : E)
    let B := scaleCore s (sectionBra x)
    ∃ τ : E, τ ≠ 0 ∧ τ ^ 2 * (s * sectionImbalance x) =
      s ^ 3 * sectionInitialBraMixedTrace x ∧
      let g := balance τ * traceFrame (traces A) (traces B)
      let h := traceFrameInverse (traces A) (traces B) * balance τ⁻¹
      traces (mix g A) = ![1, 0] ∧ traces (mix hᵀ B) = ![1, 0] ∧
      mixedTrace (mix g A) = mixedTrace (mix hᵀ B) := by
  dsimp only
  let s := (sectionTraceSum x)⁻¹
  let A := transverseKet (0 : E)
  let B := scaleCore s (sectionBra x)
  let a := s * sectionImbalance x
  let b := s ^ 3 * sectionInitialBraMixedTrace x
  have ha' : a ≠ 0 := mul_ne_zero (inv_ne_zero hs) ha
  have hb' : b ≠ 0 := mul_ne_zero (pow_ne_zero _ (inv_ne_zero hs)) hb
  obtain ⟨τ, hτ⟩ := IsAlgClosed.exists_pow_nat_eq (b / a) (n := 2) (by decide)
  have hτ' := (eq_div_iff ha').mp hτ
  have hτ0 : τ ≠ 0 := by
    intro h
    apply hb'
    simpa [h] using hτ'.symm
  have htrace : traces A 0 * traces B 0 + traces A 1 * traces B 1 = 1 := by
    rw [sectionKet_trace, trace_scaleCore, trace_scaleCore, sectionBra_trace]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_mul, ← mul_add]
    exact inv_mul_cancel₀ hs
  have ⟨hA, hB⟩ := traceFrame_aligns A B htrace
  have htr (w : E) (C : Core E) (hc : traces C = ![1, 0]) :
      traces (mix (balance w) C) = ![1, 0] := by
    funext i
    fin_cases i
    · exact (congrArg Matrix.trace (balance_mix w C).1).trans (congrFun hc 0)
    · change (mix (balance w) C 1).trace = 0
      rw [(balance_mix w C).2, Matrix.trace_smul]
      exact mul_zero w ▸ congrArg (w * ·) (congrFun hc 1)
  have hmt (w : E) (C : Core E) : mixedTrace (mix (balance w) C) = w * mixedTrace C := by
    rw [mixedTrace, (balance_mix w C).1, (balance_mix w C).2]
    change (C 0 * w • C 1).trace = w * (C 0 * C 1).trace
    rw [Matrix.mul_smul (C 0) w (C 1), Matrix.trace_smul]
    rfl
  have htrans : (balance τ⁻¹)ᵀ = balance τ⁻¹ := by
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> rfl
  refine ⟨τ, hτ0, hτ', ?_, ?_, ?_⟩
  · rw [mix_mul]
    exact htr _ _ hA
  · rw [Matrix.transpose_mul, htrans, mix_mul]
    exact htr _ _ hB
  · rw [Matrix.transpose_mul, htrans, mix_mul, mix_mul, hmt, hmt]
    rw [(aligned_scaleBra A (sectionBra x) s).1,
      (aligned_scaleBra A (sectionBra x) s).2, section_ket_mixedTrace]
    change τ * a = τ⁻¹ * b
    rw [← hτ', pow_two]
    field_simp

/-- The generic section has an actual point of the five-coordinate
algebraic slice, over a field containing the section function field. -/
theorem genericSection_has_algebraicChart {f : Roots} [IsDomain (DivisorRing f)]
    (htrace : ¬ f ∣ rootSum) (m : ℕ) (j : Fin 3) (hj : ¬ f ∣ obstruction m j) :
    let x := sectionFieldMap f ∘ genericSection (divisorRoots f) j
    let s := (sectionTraceSum x)⁻¹
    let A := transverseKet (0 : SectionField f)
    let B := scaleCore s (sectionBra x)
    ∃ τ : SectionField f, τ ≠ 0 ∧
      τ ^ 2 * (s * sectionImbalance x) = s ^ 3 * sectionInitialBraMixedTrace x ∧
      let g := sectionBalancedKetFrame x τ
      let h := sectionBalancedBraInverse x τ
      traces (mix g A) = ![1, 0] ∧ traces (mix hᵀ B) = ![1, 0] ∧
      mixedTrace (mix g A) = mixedTrace (mix hᵀ B) := by
  dsimp only
  let x := genericSection (divisorRoots f) j
  let σ := sectionFieldMap f
  have ⟨hs, ha, hb⟩ := genericSection_frames_defined htrace m j hj
  have H : Function.Injective σ := sectionFieldMap_injective f
  have hs' : sectionTraceSum (σ ∘ x) ≠ 0 := by
    simpa only [sectionTraceSum, Function.comp_apply, map_add] using
      ((map_eq_zero_iff σ H).not.mpr hs)
  have ha' : sectionImbalance (σ ∘ x) ≠ 0 := by
    simpa only [sectionImbalance, Function.comp_apply, map_add, map_sub] using
      ((map_eq_zero_iff σ H).not.mpr ha)
  have hb' : sectionInitialBraMixedTrace (σ ∘ x) ≠ 0 := by
    have he : σ (sectionInitialBraMixedTrace x) =
        sectionInitialBraMixedTrace (σ ∘ x) := by
      unfold sectionInitialBraMixedTrace
      rw [section_bra_mixedTrace, section_bra_mixedTrace]
      simp only [Function.comp_apply, map_add, map_sub, map_mul, map_pow]
    exact he ▸ (map_eq_zero_iff σ H).not.mpr hb
  exact exists_section_chart (σ ∘ x) hs' ha' hb'

end
end D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformMovingFrame
