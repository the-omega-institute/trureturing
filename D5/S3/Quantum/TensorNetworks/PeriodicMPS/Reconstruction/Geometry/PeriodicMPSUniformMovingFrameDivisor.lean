/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformMovingFrameDivisor
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformMovingFrameDivisor
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: []
   utility: none
   digest: Unnormalized paired section in the native frame. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformMovingFrameSection

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformMovingFrame

open Matrix MvPolynomial TrivSqZeroExt
open scoped Matrix Kronecker
open PeriodicMPSUniformAntisymmetricTransfer (BondMatrix TransferMatrix mixedRaw mixedTransfer)
open PeriodicMPSUniformHardCoreTransferRecurrence (TwoBits binaryInsertion binaryTransfer)
open PeriodicMPSUniformVerticalSectionRank (transverseKet DivisorRing divisorRoots genericSection)
open PeriodicMPSUniformVerticalPrimeExclusion (Roots pairing rootSum obstruction)
open SevenSiteCriticalCertificate (observedRow)
open UniformNativeCriticalMatrix (criticalMatrix)

open private sectionBra divisorRoots_eq_zero affine_ne_zero from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformVerticalSectionRank
open private map_trace' mapCore map_aligned_mixedTrace map_sectionBra map_sectionKet
  sectionKet_trace sectionBra_trace map_mix from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformMovingFrameSection
open private pauliReadLinear from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformMovingFrameNative

noncomputable section

def scaleCore {R : Type*} [CommRing R] (s : R) (B : Core R) : Core R :=
  fun j => s • B j

private theorem trace_scaleCore {R : Type*} [CommRing R] (s : R) (B : Core R) (j : Fin 2) :
    traces (scaleCore s B) j = s * traces B j := Matrix.trace_smul _ _

private theorem map_scaleCore {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (s : R) (B : Core R) :
    mapCore f (scaleCore s B) = scaleCore (f s) (mapCore f B) := by
  funext j
  apply Matrix.ext
  intro p q
  exact f.map_mul s (B j p q)

private theorem mix_scaleCore {R : Type*} [CommRing R] (g : BondMatrix R) (s : R) (B : Core R) :
    mix g (scaleCore s B) = scaleCore s (mix g B) := by
  funext j
  apply Matrix.ext
  intro p q
  simp [mix, scaleCore, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  ring

private theorem mixedTrace_scaleCore {R : Type*} [CommRing R] (s : R) (B : Core R) :
    mixedTrace (scaleCore s B) = s ^ 2 * mixedTrace B := by
  simp [mixedTrace, scaleCore, Matrix.trace_smul, pow_two, mul_assoc]

/-- Scaling one core changes the literal raw marginal by degree `m + 2`. -/
theorem mixedRaw_scaleBra {R : Type*} [CommRing R] (A B : Core R) (s : R) (m : ℕ) :
    mixedRaw A (scaleCore s B) m = s ^ (m + 2) • mixedRaw A B m := by
  have hT : mixedTransfer A (scaleCore s B) = s • mixedTransfer A B := by
    simp [mixedTransfer, binaryTransfer, scaleCore, smul_kronecker, smul_add]
  have hI (p q : TwoBits) : binaryInsertion (scaleCore s B) A p q =
      s ^ 2 • binaryInsertion B A p q := by
    simp [binaryInsertion, scaleCore, smul_smul,
      smul_kronecker, pow_two]
  apply Matrix.ext
  intro p q
  change (binaryInsertion (scaleCore s B) A q p * mixedTransfer A (scaleCore s B) ^ m).trace =
    s ^ (m + 2) * (binaryInsertion B A q p * mixedTransfer A B ^ m).trace
  rw [hI, hT, smul_pow, smul_mul_assoc, mul_smul_comm, smul_smul, Matrix.trace_smul, smul_eq_mul,
    ← pow_add, Nat.add_comm 2 m]

private theorem aligned_scaleBra {R : Type*} [CommRing R] (A B : Core R) (s : R) :
    mixedTrace (mix (traceFrame (traces A) (traces (scaleCore s B))) A) =
        s * mixedTrace (mix (traceFrame (traces A) (traces B)) A) ∧
    mixedTrace (mix (traceFrameInverse (traces A) (traces (scaleCore s B)))ᵀ (scaleCore s B)) =
        s ^ 3 * mixedTrace (mix (traceFrameInverse (traces A) (traces B))ᵀ B) := by
  have hA₀ : mix (traceFrame (traces A) (traces (scaleCore s B))) A 0 =
      s • mix (traceFrame (traces A) (traces B)) A 0 := by
    apply Matrix.ext
    intro i j
    simp [mix, traceFrame, trace_scaleCore, Fin.sum_univ_two, Matrix.smul_apply,
      smul_eq_mul, mul_add, mul_assoc]
  have hB₁ : mix (traceFrameInverse (traces A) (traces (scaleCore s B)))ᵀ B 1 =
      s • mix (traceFrameInverse (traces A) (traces B))ᵀ B 1 := by
    apply Matrix.ext
    intro i j
    simp [mix, traceFrameInverse, trace_scaleCore, Fin.sum_univ_two, Matrix.smul_apply,
      smul_eq_mul, mul_add, mul_assoc]
  constructor
  · unfold mixedTrace
    rw [hA₀]
    have hA₁ : mix (traceFrame (traces A) (traces (scaleCore s B))) A 1 =
        mix (traceFrame (traces A) (traces B)) A 1 := by
      simp [mix, traceFrame]
    rw [hA₁, smul_mul_assoc, Matrix.trace_smul]
    rfl
  · rw [mix_scaleCore, mixedTrace_scaleCore]
    unfold mixedTrace
    have hB₀ : mix (traceFrameInverse (traces A) (traces (scaleCore s B)))ᵀ B 0 =
        mix (traceFrameInverse (traces A) (traces B))ᵀ B 0 := by
      simp [mix, traceFrameInverse]
    rw [hB₀, hB₁, mul_smul_comm, Matrix.trace_smul, smul_eq_mul, ← mul_assoc,
      ← pow_succ]

def sectionTraceSum {R : Type*} [CommRing R] (x : Fin 5 → R) : R :=
  x 0 + x 1 + (x 2 + x 3)

def sectionImbalance {R : Type*} [CommRing R] (x : Fin 5 → R) : R :=
  (x 0 + x 1) - (x 2 + x 3)

def sectionInitialBraMixedTrace {R : Type*} [CommRing R] (x : Fin 5 → R) : R :=
  mixedTrace (mix (traceFrameInverse (traces (transverseKet 0))
    (traces (sectionBra x)))ᵀ (sectionBra x))

variable {E : Type*} [Field E] [Algebra ℂ E]

local notation "D" => DualNumber E
local notation "π" => AlgHom.toRingHom (fstHom E E E)

omit [Algebra ℂ E] in
private theorem raw_scale_jet (c : D) (W : TransferMatrix D) :
    jetValue (c • W) = c.fst • jetValue W ∧
      jetTangent (c • W) = c.fst • jetTangent W + c.snd • jetValue W := by
  constructor <;>
    apply Matrix.ext <;> intro p q <;> rfl

private theorem map_chartOf (A B : Core D) :
    (fun j => (chartOf A B j).fst) = chartOf (mapCore π A) (mapCore π B) := by
  have hd (C : Core D) (i : Fin 2) : ((C i).det).fst = ((mapCore π C) i).det :=
    RingHom.map_det π (C i)
  have hk : (mixedTrace A).fst = mixedTrace (mapCore π A) := by
    change π ((A 0 * A 1).trace) = ((RingHom.mapMatrix π (A 0)) * RingHom.mapMatrix π (A 1)).trace
    rw [map_trace', map_mul]
  have hh : (half D).fst = half E := by
    change π (algebraMap ℂ D (1 / 2)) = algebraMap ℂ E (1 / 2)
    rw [IsScalarTower.algebraMap_apply ℂ E D]
    rfl
  have hi : (imaginary D).fst = imaginary E := by
    change π (algebraMap ℂ D Complex.I) = algebraMap ℂ E Complex.I
    rw [IsScalarTower.algebraMap_apply ℂ E D]
    rfl
  funext j
  fin_cases j <;> simp [chartOf, hd, hk, hh, hi]

def sectionBalancedKetFrame (x : Fin 5 → E) (τ : E) : BondMatrix E :=
  balance τ * traceFrame (traces (transverseKet 0))
    (traces (scaleCore (sectionTraceSum x)⁻¹ (sectionBra x)))

def sectionBalancedBraInverse (x : Fin 5 → E) (τ : E) : BondMatrix E :=
  traceFrameInverse (traces (transverseKet 0))
    (traces (scaleCore (sectionTraceSum x)⁻¹ (sectionBra x))) * balance τ⁻¹

/-- The chart is fixed by the section point and the balancing square root. -/
def sectionChart (x : Fin 5 → E) (τ : E) : Fin 5 → E :=
  chartOf (mix (sectionBalancedKetFrame x τ) (transverseKet 0))
    (mix (sectionBalancedBraInverse x τ)ᵀ (scaleCore (sectionTraceSum x)⁻¹ (sectionBra x)))

/-- Every section tangent with a nonzero trace sum can be compared directly
to the native augmented matrix. The derivative of the trace normalization
contributes precisely a multiple of the transported radial column. -/
theorem native_section_unnormalized_jet (m : ℕ) (x dx : Fin 5 → E) (dμ : E)
    (hs : sectionTraceSum x ≠ 0) (ha : sectionImbalance x ≠ 0)
    {τ : E} (ht : τ ≠ 0)
    (hτ : τ ^ 2 * ((sectionTraceSum x)⁻¹ * sectionImbalance x) =
      (sectionTraceSum x)⁻¹ ^ 3 * sectionInitialBraMixedTrace x) :
    let y : Fin 5 → D := fun j => ⟨x j, dx j⟩
    let W := mixedRaw (transverseKet (inr dμ : D)) (sectionBra y) m
    ∃ g h : BondMatrix D, h * g = 1 ∧ g * h = 1 ∧
      jetValue g = sectionBalancedKetFrame x τ ∧
      jetValue h = sectionBalancedBraInverse x τ ∧
      ∃ z : Fin 5 → D, (fun j => (z j).fst) = sectionChart x τ ∧
      let N := (criticalMatrix m).map (aeval (sectionChart x τ))
      let L := pairFrame (sectionBalancedKetFrame x τ)
      let R := pairFrame (sectionBalancedBraInverse x τ)
      let c := rotationCoefficients (jetTangent g * jetValue h)
      let a := sectionTraceSum y ^ (m + 2)
      ∀ i : Fin 10,
        pauliRead (L * jetValue W * R) (observedRow i) = a.fst * N i 5 ∧
        pauliRead (L * jetTangent W * R) (observedRow i) =
          a.fst * ((∑ j : Fin 5, (z j).snd * N i (Fin.castLE (by decide) j)) -
            ∑ j : Fin 3, c j * N i (Fin.natAdd 6 j)) + a.snd * N i 5 := by
  dsimp only
  let y : Fin 5 → D := fun j => ⟨x j, dx j⟩
  let s : D := sectionTraceSum y
  let A : Core D := transverseKet (inr dμ)
  let B : Core D := sectionBra y
  have hu : IsUnit s := isUnit_iff_isUnit_fst.mpr (isUnit_iff_ne_zero.mpr hs)
  obtain ⟨u, hu⟩ := hu
  let C := scaleCore (↑u⁻¹ : D) B
  have hsu : (↑u⁻¹ : D) * s = 1 := by rw [← hu]; exact u.inv_mul
  have htrace : traces A 0 * traces C 0 + traces A 1 * traces C 1 = 1 := by
    rw [sectionKet_trace, trace_scaleCore, trace_scaleCore, sectionBra_trace]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_mul, ← mul_add]
    exact hsu
  have hinv : π (↑u⁻¹ : D) = (sectionTraceSum x)⁻¹ := by
    have hh := congrArg π hsu
    change (π ↑u⁻¹) * sectionTraceSum x = 1 at hh
    exact eq_inv_of_mul_eq_one_left hh
  have hbaseA : mapCore π A = transverseKet (0 : E) := map_sectionKet π _
  have hbaseC : mapCore π C = scaleCore (sectionTraceSum x)⁻¹ (sectionBra x) := by
    change mapCore π (scaleCore (↑u⁻¹ : D) (sectionBra y)) = _
    rw [map_scaleCore, hinv, map_sectionBra]
    rfl
  have hbase := map_aligned_mixedTrace π A C
  rw [hbaseA, hbaseC] at hbase
  have hscale := aligned_scaleBra (transverseKet (0 : E)) (sectionBra x) (sectionTraceSum x)⁻¹
  let kA := mixedTrace (mix (traceFrame (traces A) (traces C)) A)
  let kB := mixedTrace (mix (traceFrameInverse (traces A) (traces C))ᵀ C)
  have hA₀ : kA.fst = (sectionTraceSum x)⁻¹ * sectionImbalance x :=
    hbase.1.trans (hscale.1.trans (congrArg ((sectionTraceSum x)⁻¹ * ·)
      (section_ket_mixedTrace x)))
  have hB₀ : kB.fst = (sectionTraceSum x)⁻¹ ^ 3 * sectionInitialBraMixedTrace x :=
    hbase.2.trans hscale.2
  let _ : CharZero E := charZero_of_injective_algebraMap (algebraMap ℂ E).injective
  have hτ₀ : τ ^ 2 * kA.fst = kB.fst :=
    (congrArg (τ ^ 2 * ·) hA₀).trans (hτ.trans hB₀.symm)
  obtain ⟨g, h, hhg, hgh, hA, hC, hk, hg₀, hh₀⟩ := exists_balancedFrame_fixedValue A C htrace τ
    (hA₀.trans_ne (mul_ne_zero (inv_ne_zero hs) ha)) ht hτ₀
  have htr (M : Core D) (i : Fin 2) :
      (traces M i).fst = traces (mapCore π M) i := map_trace' π (M i)
  have htraceA : (fun i => (traces A i).fst) = traces (transverseKet (0 : E)) :=
    (funext (htr A)).trans (congrArg traces hbaseA)
  have htraceC : (fun i => (traces C i).fst) =
      traces (scaleCore (sectionTraceSum x)⁻¹ (sectionBra x)) :=
    (funext (htr C)).trans (congrArg traces hbaseC)
  rw [htraceA, htraceC] at hg₀ hh₀
  change jetValue g = sectionBalancedKetFrame x τ at hg₀
  change jetValue h = sectionBalancedBraInverse x τ at hh₀
  let z := chartOf (mix g A) (mix hᵀ C)
  have hz : (fun j => (z j).fst) = sectionChart x τ := by
    change (fun j => (chartOf (mix g A) (mix hᵀ C) j).fst) = _
    rw [map_chartOf, map_mix, map_mix, hbaseA, hbaseC]
    change chartOf (mix (jetValue g) (transverseKet 0))
      (mix (jetValue h)ᵀ (scaleCore (sectionTraceSum x)⁻¹ (sectionBra x))) = _
    rw [hg₀, hh₀]
    rfl
  let W₀ := mixedRaw A C m
  have hBC : scaleCore s C = B := by
    funext j
    change s • (↑u⁻¹ : D) • B j = B j
    rw [smul_smul, mul_comm s, hsu, one_smul]
  have hW : mixedRaw A B m = s ^ (m + 2) • W₀ :=
    hBC ▸ mixedRaw_scaleBra A C s m
  have hc := native_movingFrame_comparison m A C g h hhg hgh hA hC hk
  refine ⟨g, h, hhg, hgh, hg₀, hh₀, z, hz, ?_⟩
  intro i
  have hci := hc i
  change _ = ((criticalMatrix m).map (aeval fun j => (z j).fst)) i 5 ∧
    pauliRead (pairFrame (jetValue g) * jetTangent W₀ * pairFrame (jetValue h)) (observedRow i) =
      (∑ j : Fin 5, (z j).snd * ((criticalMatrix m).map (aeval fun j => (z j).fst)) i
        (Fin.castLE (by decide) j)) -
      (∑ j : Fin 3, rotationCoefficients (jetTangent g * jetValue h) j *
        ((criticalMatrix m).map (aeval fun j => (z j).fst)) i (Fin.natAdd 6 j)) at hci
  rw [hg₀, hh₀, hz] at hci
  obtain ⟨hV, hD⟩ := hci

  change pauliRead (_ * jetValue (mixedRaw A B m) * _) _ = _ ∧
    pauliRead (_ * jetTangent (mixedRaw A B m) * _) _ = _
  rw [hh₀, hW, (raw_scale_jet _ _).1, (raw_scale_jet _ _).2]
  let P := pauliReadLinear (E := E) (observedRow i)
  change P (_ * (_ • _) * _) = _ ∧ P (_ * (_ + _) * _) = _
  simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, map_add, map_smul, smul_eq_mul]
  exact ⟨congrArg ((s ^ (m + 2)).fst * ·) hV,
    congrArg₂ (fun v w => (s ^ (m + 2)).fst * v + (s ^ (m + 2)).snd * w) hD hV⟩

end
end D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformMovingFrame
