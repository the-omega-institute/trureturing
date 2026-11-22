/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformMovingFrameSection
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformMovingFrameSection
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: []
   utility: none
   digest: Normalized paired section jets. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformMovingFrameNative
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformVerticalNativeTransport
import Mathlib.FieldTheory.AlgebraicClosure

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformMovingFrame

open Matrix MvPolynomial TrivSqZeroExt
open scoped Matrix Kronecker
open PeriodicMPSUniformAntisymmetricTransfer (BondMatrix TransferMatrix mixedRaw mixedTransfer)
open PeriodicMPSUniformHardCoreTransferRecurrence (TwoBits binaryInsertion binaryTransfer)
open PeriodicMPSUniformVerticalMiddle (sectionB0 sectionB1)
open PeriodicMPSUniformVerticalSectionRank
  (transverseKet DivisorRing divisorRoots genericSection)
open SevenSiteCriticalCertificate (observedRow)
open UniformNativeCriticalMatrix (criticalMatrix)

open private pairedBra from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformVerticalSectionTrace
open private sectionBra divisorRoots_eq_zero from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformVerticalSectionRank

noncomputable section

private theorem map_kronecker {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (A B : BondMatrix R) :
    f.mapMatrix (A ⊗ₖ B) = f.mapMatrix A ⊗ₖ f.mapMatrix B := by
  apply Matrix.ext
  intro i j
  exact f.map_mul (A i.1 j.1) (B i.2 j.2)

private theorem map_trace' {R S : Type*} [CommRing R] [CommRing S] {n : Type*} [Fintype n] [DecidableEq n]
    (f : R →+* S) (M : Matrix n n R) : f M.trace = (f.mapMatrix M).trace :=
  AddMonoidHom.map_trace f M

private def mapCore {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (A : Core R) :
    Core S := fun i => f.mapMatrix (A i)

private theorem map_mixedTransfer {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (A B : Core R) :
    f.mapMatrix (mixedTransfer A B) = mixedTransfer (mapCore f A) (mapCore f B) := by
  simp only [mixedTransfer, binaryTransfer, map_add, map_kronecker, mapCore]

private theorem map_mixedRaw {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (A B : Core R) (m : ℕ) :
    f.mapMatrix (mixedRaw A B m) = mixedRaw (mapCore f A) (mapCore f B) m := by
  apply Matrix.ext
  intro p q
  change f (binaryInsertion B A q p * mixedTransfer A B ^ m).trace = _
  rw [map_trace', map_mul, map_pow, map_mixedTransfer]
  simp only [mixedRaw, binaryInsertion, map_kronecker, map_mul, mapCore]

private theorem map_mix {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (g : BondMatrix R) (A : Core R) :
    mapCore f (mix g A) = mix (f.mapMatrix g) (mapCore f A) := by
  funext i
  apply Matrix.ext
  intro p q
  simp [mapCore, mix, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]

private theorem map_aligned_mixedTrace {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (A B : Core R) :
    f (mixedTrace (mix (traceFrame (traces A) (traces B)) A)) =
      mixedTrace (mix (traceFrame (traces (mapCore f A)) (traces (mapCore f B))) (mapCore f A)) ∧
    f (mixedTrace (mix (traceFrameInverse (traces A) (traces B))ᵀ B)) =
      mixedTrace (mix (traceFrameInverse
        (traces (mapCore f A)) (traces (mapCore f B)))ᵀ (mapCore f B)) := by
  have hg : f.mapMatrix (traceFrame (traces A) (traces B)) =
      traceFrame (traces (mapCore f A)) (traces (mapCore f B)) := by
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [traceFrame, traces, mapCore, map_trace']
  have hh : f.mapMatrix (traceFrameInverse (traces A) (traces B))ᵀ =
      (traceFrameInverse (traces (mapCore f A)) (traces (mapCore f B)))ᵀ := by
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [traceFrameInverse, traces, mapCore, map_trace', Matrix.transpose_apply]
  have h (C : Core R) : f (mixedTrace C) = mixedTrace (mapCore f C) := by
    rw [mixedTrace, map_trace', map_mul]
    rfl
  exact ⟨by rw [h, map_mix, hg], by rw [h, map_mix, hh]⟩

variable {E : Type*} [Field E] [Algebra ℂ E]

local notation "D" => DualNumber E
local notation "π" => AlgHom.toRingHom (fstHom E E E)

private theorem sectionKet_trace {R : Type*} [CommRing R] (μ : R) :
    traces (transverseKet μ) = ![1, 1] := by
  funext i
  fin_cases i <;> simp [traces, transverseKet]

private theorem sectionBra_trace {R : Type*} [CommRing R] (x : Fin 5 → R) :
    traces (sectionBra x) = ![x 0 + x 1, x 2 + x 3] := by
  funext i
  fin_cases i <;>
    simp [traces, sectionBra, pairedBra,
      sectionB0, sectionB1]

private theorem map_sectionKet {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (μ : R) :
    mapCore f (transverseKet μ) = transverseKet (f μ) := by
  funext i
  apply Matrix.ext
  intro a b
  fin_cases i <;> fin_cases a <;> fin_cases b <;>
    simp [mapCore, transverseKet]


private theorem map_sectionBra {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (x : Fin 5 → R) :
    mapCore f (sectionBra x) = sectionBra (f ∘ x) := by
  funext i
  apply Matrix.ext
  intro a b
  fin_cases i <;> fin_cases a <;> fin_cases b <;>
    simp [mapCore, sectionBra, pairedBra, sectionB0, sectionB1, Function.comp_apply]

/-- Mixed trace of the ket after trace alignment at the triangular section. -/
theorem section_ket_mixedTrace {R : Type*} [CommRing R] (x : Fin 5 → R) :
    let A := transverseKet (0 : R)
    let B := sectionBra x
    mixedTrace (mix (traceFrame (traces A) (traces B)) A) =
      (x 0 + x 1) - (x 2 + x 3) := by
  dsimp only
  rw [sectionKet_trace, sectionBra_trace]
  simp [mixedTrace, mix, traceFrame, transverseKet,
    Matrix.trace, Fin.sum_univ_two, smul_eq_mul]
  abel

/-- The bra mixed trace is affine in the actual entry `p` of the second
section matrix. This uses the polynomial trace alignment over the base ring. -/
theorem section_bra_mixedTrace {R : Type*} [CommRing R] (x : Fin 5 → R) :
    let A := transverseKet (0 : R)
    let B := sectionBra x
    let α := x 0 + x 1
    let β := x 2 + x 3
    let p := x 3 + (x 2 - x 3) * x 4
    mixedTrace (mix (traceFrameInverse (traces A) (traces B))ᵀ B) =
      β * (x 0 ^ 2 + x 1 ^ 2) + (β - α) * (x 0 * p + x 1 * (β - p)) -
        α * (x 2 ^ 2 + x 3 ^ 2) := by
  dsimp only
  rw [sectionKet_trace, sectionBra_trace]
  simp [mixedTrace, mix, traceFrameInverse, sectionBra,
    pairedBra, sectionB0, sectionB1, Matrix.trace, Fin.sum_univ_two, smul_eq_mul]
  ring

def sectionBraJet (x dx : Fin 5 → E) : Core D :=
  sectionBra (fun j => (⟨x j, dx j⟩ : D))

omit [Algebra ℂ E] in
private theorem section_dot (x dx : Fin 5 → E) (dμ : E)
    (hsum : x 0 + x 1 + (x 2 + x 3) = 1) (hdsum : dx 0 + dx 1 + (dx 2 + dx 3) = 0) :
    let a := traces (transverseKet (inr dμ : D))
    let b := traces (sectionBraJet x dx)
    a 0 * b 0 + a 1 * b 1 = 1 := by
  dsimp only
  let y : Fin 5 → D := fun j => ⟨x j, dx j⟩
  change traces (transverseKet (inr dμ : D)) 0 * traces (sectionBra y) 0 +
    traces (transverseKet (inr dμ : D)) 1 * traces (sectionBra y) 1 = 1
  rw [sectionKet_trace, sectionBra_trace y]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_mul]
  apply TrivSqZeroExt.ext
  · exact hsum
  · exact hdsum

omit [Algebra ℂ E] in
private theorem section_base_traces (x dx : Fin 5 → E) (dμ : E) :
    let A := transverseKet (inr dμ : D)
    let B := sectionBraJet x dx
    let A₀ := transverseKet (0 : E)
    let B₀ := sectionBra x
    (mixedTrace (mix (traceFrame (traces A) (traces B)) A)).fst =
      (x 0 + x 1) - (x 2 + x 3) ∧
    (mixedTrace (mix (traceFrameInverse (traces A) (traces B))ᵀ B)).fst =
      mixedTrace (mix (traceFrameInverse (traces A₀) (traces B₀))ᵀ B₀) := by
  dsimp only
  have hA : mapCore π (transverseKet (inr dμ : D)) = transverseKet (0 : E) :=
    map_sectionKet π (inr dμ)
  have hB : mapCore π (sectionBraJet x dx) = sectionBra x := by
    let y : Fin 5 → D := fun j => ⟨x j, dx j⟩
    change mapCore π (sectionBra y) = sectionBra x
    exact (map_sectionBra π y).trans (congrArg sectionBra (funext fun _ => rfl))
  have h := map_aligned_mixedTrace π (transverseKet (inr dμ : D)) (sectionBraJet x dx)
  rw [hA, hB] at h
  exact ⟨h.1.trans (section_ket_mixedTrace x), h.2⟩

private theorem section_has_frame (x dx : Fin 5 → E) (dμ : E)
    (hsum : x 0 + x 1 + (x 2 + x 3) = 1) (hdsum : dx 0 + dx 1 + (dx 2 + dx 3) = 0)
    (hA : (x 0 + x 1) - (x 2 + x 3) ≠ 0)
    {τ : E} (ht : τ ≠ 0)
    (hτ : τ ^ 2 * ((x 0 + x 1) - (x 2 + x 3)) =
      mixedTrace (mix (traceFrameInverse (traces (transverseKet 0))
        (traces (sectionBra x)))ᵀ (sectionBra x))) :
    let A := transverseKet (inr dμ : D)
    let B := sectionBraJet x dx
    ∃ g h : BondMatrix D, h * g = 1 ∧ g * h = 1 ∧
      traces (mix g A) = ![1, 0] ∧ traces (mix hᵀ B) = ![1, 0] ∧
      mixedTrace (mix g A) = mixedTrace (mix hᵀ B) := by
  let _ : CharZero E := charZero_of_injective_algebraMap (algebraMap ℂ E).injective
  obtain ⟨hA', hB'⟩ := section_base_traces x dx dμ
  exact exists_balancedFrame _ _ (section_dot x dx dμ hsum hdsum) τ
    (hA'.trans_ne hA) ht ((congrArg (τ ^ 2 * ·) hA').trans (hτ.trans hB'.symm))

/-- Every trace-one section tangent, with independent root, section
parameter and transverse ket speeds, has a literal native comparison
after the explicit trace frame and separable balancing lift. -/
theorem native_section_movingFrame_jet (m : ℕ) (x dx : Fin 5 → E) (dμ : E)
    (hsum : x 0 + x 1 + (x 2 + x 3) = 1) (hdsum : dx 0 + dx 1 + (dx 2 + dx 3) = 0)
    (hA : (x 0 + x 1) - (x 2 + x 3) ≠ 0)
    {τ : E} (ht : τ ≠ 0)
    (hτ : τ ^ 2 * ((x 0 + x 1) - (x 2 + x 3)) =
      mixedTrace (mix (traceFrameInverse (traces (transverseKet 0))
        (traces (sectionBra x)))ᵀ (sectionBra x))) :
    let A := transverseKet (inr dμ : D)
    let B := sectionBraJet x dx
    ∃ g h : BondMatrix D, h * g = 1 ∧ g * h = 1 ∧
      let z := chartOf (mix g A) (mix hᵀ B)
      let N := (criticalMatrix m).map (aeval fun i => (z i).fst)
      let W := mixedRaw A B m
      let L := pairFrame (jetValue g)
      let R := pairFrame (jetValue h)
      let c := rotationCoefficients (jetTangent g * jetValue h)
      ∀ i : Fin 10,
        pauliRead (L * jetValue W * R) (observedRow i) = N i 5 ∧
        pauliRead (L * jetTangent W * R) (observedRow i) =
          ∑ j : Fin 5, (z j).snd * N i (Fin.castLE (by decide) j) -
          ∑ j : Fin 3, c j * N i (Fin.natAdd 6 j) := by
  obtain ⟨g, h, hhg, hgh, ha, hb, hk⟩ :=
    section_has_frame x dx dμ hsum hdsum hA ht hτ
  refine ⟨g, h, hhg, hgh, ?_⟩
  exact native_movingFrame_comparison m _ _ g h hhg hgh ha hb hk

end
end D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformMovingFrame
