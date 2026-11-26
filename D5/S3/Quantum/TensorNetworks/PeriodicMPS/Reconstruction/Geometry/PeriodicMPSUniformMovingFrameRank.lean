/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformMovingFrameRank
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformMovingFrameRank
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: []
   utility: none
   digest: Noncoordinate prime exclusion from native criticality. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformMovingFrameFactor
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformMovingFrameMinorJets
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformMovingFrameMinorMap

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformMovingFrame

open Matrix MvPolynomial TrivSqZeroExt
open scoped Matrix
open PeriodicMPSUniformAntisymmetricTransfer (BondMatrix TransferMatrix mixedRaw)
open PeriodicMPSUniformVerticalSectionRank (transverseKet sectionTripletMinor sectionSingletMinor
  TripletIndex SingletIndex DivisorRing divisorRoots genericSection)
open PeriodicMPSUniformVerticalPrimeExclusion (Roots rootSum obstruction SectionRankImplication
  no_noncoordinate_prime_of_sectionRankImplication)
open UniformNativeCriticalMatrix (criticalMatrix)
open private outerEntry from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformVerticalSectionTrace
open private sectionBra endpoint from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformVerticalSectionRank
open private tripletIndexEquiv singletIndexEquiv from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformVerticalNativeTransport
open private tripletContract_eq sectionRaw parameterTangent transverseTangent
  from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformMovingFrameMinorRows
open private sectionRawColumns_parameter from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformMovingFrameMinorJets

noncomputable section

variable {E : Type*} [Field E] [Algebra ℂ E]

private def tripletEntryLinear (i j : Fin 3) : TransferMatrix E →ₗ[E] E where
  toFun W := tripletContract (half E) W i j
  map_add' U V := by
    simp only [tripletContract_eq, Matrix.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c W := by
    simp only [tripletContract_eq, Matrix.smul_apply, smul_eq_mul, RingHom.id_apply,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun p _ => ?_
    ring

private def singletEntryLinear : TransferMatrix E →ₗ[E] E where
  toFun := singletContract (half E)
  map_add' U V := by simp only [singletContract, Matrix.add_apply]; ring
  map_smul' c W := by simp only [singletContract, Matrix.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

private def outerEntryLinear (i : Fin 6) : TransferMatrix E →ₗ[E] E :=
  tripletEntryLinear (if i.val < 3 then 0 else 2) (Fin.ofNat 3 i.val)

private def tripletRowLinear : TripletIndex → TransferMatrix E →ₗ[E] E :=
  Sum.elim outerEntryLinear (tripletEntryLinear 1)

private def singletRowLinear : SingletIndex → TransferMatrix E →ₗ[E] E :=
  Sum.elim outerEntryLinear
    (Sum.elim (fun j => tripletEntryLinear 1 (endpoint j)) (fun _ => singletEntryLinear))

private theorem tripletRowLinear_apply (W : TransferMatrix E) (i : TripletIndex) :
    tripletRowLinear i W = tripletContractRow W i := by
  cases i <;> rfl

private theorem singletRowLinear_apply (W : TransferMatrix E) (i : SingletIndex) :
    singletRowLinear i W = singletContractRow W i := by
  rcases i with i | (i | i) <;> rfl

omit [Algebra ℂ E] in
private theorem sectionRawColumns_symmetric (x : Fin 5 → E) (m : ℕ) (j : TripletIndex) :
    SwapSymmetric (sectionRawColumns x m j) := by
  have hbase : SwapSymmetric (sectionRaw x m) := mixedRaw_swapSymmetric _ _ _
  rcases j with j | j
  · refine Fin.lastCases ?_ (fun k => ?_) j
    · exact swapSymmetric_rotation _ hbase
    · rw [sectionRawColumns_parameter]
      exact swapSymmetric_tangent (mixedRaw_swapSymmetric _ _ _)
  · fin_cases j
    · exact swapSymmetric_rotation _ hbase
    · exact swapSymmetric_rotation _ hbase
    · exact swapSymmetric_tangent (mixedRaw_swapSymmetric _ _ _)

private theorem sectionRawColumns_native (x : Fin 5 → E) (m : ℕ)
    (hs : sectionTraceSum x ≠ 0) (ha : sectionImbalance x ≠ 0)
    {τ : E} (ht : τ ≠ 0)
    (hτ : τ ^ 2 * ((sectionTraceSum x)⁻¹ * sectionImbalance x) =
      (sectionTraceSum x)⁻¹ ^ 3 * sectionInitialBraMixedTrace x)
    (hA : traces (mix (sectionBalancedKetFrame x τ) (transverseKet 0)) = ![1,0])
    (hB : traces (mix (sectionBalancedBraInverse x τ)ᵀ
      (scaleCore (sectionTraceSum x)⁻¹ (sectionBra x))) = ![1,0])
    (hk : mixedTrace (mix (sectionBalancedKetFrame x τ) (transverseKet 0)) =
      mixedTrace (mix (sectionBalancedBraInverse x τ)ᵀ
        (scaleCore (sectionTraceSum x)⁻¹ (sectionBra x))))
    (j : TripletIndex) :
    let N := (criticalMatrix m).map (aeval (sectionChart x τ))
    ∃ v, sectionPauliColumn x τ (sectionRawColumns x m j) = N *ᵥ v := by
  rcases j with j | j
  · refine Fin.lastCases ?_ (fun k => ?_) j
    · exact native_section_rotation_column m x diagonalShear hs ht hA hB hk
    · rw [sectionRawColumns_parameter]
      exact native_section_raw_column m x (Pi.single k 1) 0 hs ha ht hτ
  · fin_cases j
    · exact native_section_rotation_column m x lowerShear hs ht hA hB hk
    · exact native_section_rotation_column m x upperShear hs ht hA hB hk
    · exact native_section_raw_column m x 0 1 hs ha ht hτ

omit [Algebra ℂ E] in
private theorem factor_reindex {ι : Type*} [Fintype ι] (e : ι ≃ Fin 9)
    (L : Matrix ι (Fin 10) E) (N : Matrix (Fin 10) (Fin 9) E) (C : Matrix (Fin 9) ι E) :
    L * N * C = L * (N.submatrix id e) * C.submatrix e id := by
  rw [Matrix.mul_assoc, Matrix.mul_assoc]
  congr 1
  apply Matrix.ext
  intro i j
  exact (e.sum_comp (fun k => N i k * C k j)).symm

private def sectionFieldAlgMap (f : Roots) [IsDomain (DivisorRing f)] :
    SectionPolynomial f →ₐ[ℂ] SectionField f where
  toRingHom := sectionFieldMap f
  commutes' _ := rfl

/-- Vanishing native maximal minors at the balanced generic section for
each unobstructed pairing. -/
def GenericSectionNativeCritical (m : ℕ) (f : Roots) [IsDomain (DivisorRing f)] : Prop :=
  ∀ j : Fin 3, ¬ f ∣ obstruction m j →
    let x := sectionFieldMap f ∘ genericSection (divisorRoots f) j
    ∀ τ : SectionField f, τ ≠ 0 →
      τ ^ 2 * ((sectionTraceSum x)⁻¹ * sectionImbalance x) =
        (sectionTraceSum x)⁻¹ ^ 3 * sectionInitialBraMixedTrace x →
      ∀ d : Fin 10, (((criticalMatrix m).map (aeval (sectionChart x τ))).submatrix
        d.succAbove id).det = 0

/-- At each unobstructed pairing, vanishing native maximal minors at the
constructed algebraic section point implies the checked section rank
condition. Both row and column matrix products are constructed. -/
theorem sectionRankImplication_of_genericNativeCriticalMatrix
    {m : ℕ} (hm : 3 ≤ m) {f : Roots} [IsDomain (DivisorRing f)]
    (htrace : ¬ f ∣ rootSum) (htorus : ∀ i : Fin 4, ¬ f ∣ (X i : Roots))
    (hcritical : GenericSectionNativeCritical m f) :
    SectionRankImplication m f := by
  let σ := sectionFieldAlgMap f
  apply PeriodicMPSUniformVerticalSectionRank.sectionRankImplication_of_nativeCriticalMatrix
    hm htrace htorus σ.toRingHom (sectionFieldMap_injective f)
  intro j hj
  let y := genericSection (divisorRoots f) j
  let x := σ ∘ y
  obtain ⟨τ, ht, hτ, hA, hB, hk⟩ := genericSection_has_algebraicChart htrace m j hj
  obtain ⟨hs₀, ha₀, _⟩ := genericSection_frames_defined htrace m j hj
  have hσ := sectionFieldMap_injective f
  have hs : sectionTraceSum x ≠ 0 := by
    change sectionTraceSum (sectionFieldMap f ∘ y) ≠ 0
    simpa only [sectionTraceSum, Function.comp_apply, map_add] using
      (map_eq_zero_iff (sectionFieldMap f) hσ).not.mpr hs₀
  have ha : sectionImbalance x ≠ 0 := by
    change sectionImbalance (sectionFieldMap f ∘ y) ≠ 0
    simpa only [sectionImbalance, Function.comp_apply, map_add, map_sub] using
      (map_eq_zero_iff (sectionFieldMap f) hσ).not.mpr ha₀
  let z := sectionChart x τ
  let N := (criticalMatrix m).map (aeval z)
  have hc (k : TripletIndex) : ∃ v, sectionPauliColumn x τ (sectionRawColumns x m k) = N *ᵥ v :=
    sectionRawColumns_native x m hs ha ht hτ hA hB hk k
  obtain ⟨LT, CT, hT⟩ := sectionColumns_factor x τ hs ht N tripletRowLinear
    (sectionRawColumns x m) (sectionRawColumns_symmetric x m) hc
  obtain ⟨LS, CS, hS⟩ := sectionColumns_factor x τ hs ht N singletRowLinear
    (sectionRawColumns x m ∘ singletColumnIndex)
    (fun k => sectionRawColumns_symmetric x m (singletColumnIndex k))
    (fun k => hc (singletColumnIndex k))
  refine ⟨z, hcritical j hj τ ht hτ, ⟨LS, CS.submatrix singletIndexEquiv id, ?_⟩,
    ⟨LT, CT.submatrix tripletIndexEquiv id, ?_⟩⟩
  · change (sectionSingletMinor (1 / 2 : ℂ) m y).map σ = _
    rw [sectionSingletMinor_map, sectionSingletMinor_rawColumns]
    simp only [← singletRowLinear_apply]
    exact hS.trans (factor_reindex singletIndexEquiv LS N CS)
  · change (sectionTripletMinor (1 / 2 : ℂ) m y).map σ = _
    rw [sectionTripletMinor_map, sectionTripletMinor_rawColumns]
    simp only [← tripletRowLinear_apply]
    exact hT.trans (factor_reindex tripletIndexEquiv LT N CT)

/-- There is no irreducible noncoordinate divisor satisfying the native
criticality hypothesis at the generic section points. -/
theorem no_noncoordinate_prime_of_genericNativeCriticalMatrix
    {m : ℕ} (hm : 3 ≤ m) {f : Roots} (hf : Irreducible f) [IsDomain (DivisorRing f)]
    (htrace : ¬ f ∣ rootSum) (htorus : ∀ i : Fin 4, ¬ f ∣ (X i : Roots))
    (hcritical : GenericSectionNativeCritical m f) : False :=
  no_noncoordinate_prime_of_sectionRankImplication hm hf htrace
    (fun i h => htorus i h.dvd)
    (sectionRankImplication_of_genericNativeCriticalMatrix hm htrace htorus hcritical)


end
end D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformMovingFrame
