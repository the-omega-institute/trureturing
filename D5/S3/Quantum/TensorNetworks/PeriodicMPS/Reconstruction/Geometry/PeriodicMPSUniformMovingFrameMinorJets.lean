/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformMovingFrameMinorJets
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformMovingFrameMinorJets
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: []
   utility: none
   digest: Section minors as contractions of raw jets. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformMovingFrameMinorRows

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformMovingFrame

open Matrix MvPolynomial TrivSqZeroExt
open scoped Matrix Kronecker
open PeriodicMPSUniformAntisymmetricTransfer (BondMatrix TransferMatrix mixedRaw mixedTransfer coreCommutator)
open PeriodicMPSUniformHardCoreTransferRecurrence (TwoBits)
open PeriodicMPSUniformVerticalSectionRank (transverseKet tripletReadout tripletReadout_section
  tripletRow tripletRotation singletTrace singletTrace_eq_native sectionTripletMinor sectionSingletMinor
  TripletIndex SingletIndex)
open private pairedBra liftCore outerEntry trace_kronecker_transfer from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformVerticalSectionTrace
open private sectionBra literalOuterColumn endpoint from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformVerticalSectionRank
open private mapCore map_sectionKet map_sectionBra map_mixedRaw from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformMovingFrameSection
open private tripletContract_eq tripletContract_raw tripletConj tripletConj_diag
  sectionRaw parameterTangent transverseTangent from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformMovingFrameMinorRows

noncomputable section

variable {E : Type*} [Field E] [Algebra ℂ E]
local notation "D" => DualNumber E

private theorem map_tripletRow {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (h : R) (i : Fin 3) (p : TwoBits) :
    f (tripletRow h i p) = tripletRow (f h) i p := by
  rcases p with ⟨a,b⟩
  fin_cases i <;> fin_cases a <;> fin_cases b <;> simp [tripletRow]

omit [Algebra ℂ E] in
private theorem snd_triplet (h : E) (W : TransferMatrix D) (i j : Fin 3) :
    (tripletContract (inl h) W i j).snd = tripletContract h (jetTangent W) i j := by
  rw [tripletContract_eq, tripletContract_eq]
  have hconst (k : Fin 3) (p : TwoBits) :
      tripletRow (inl h) k p = inl (tripletRow h k p) :=
    (map_tripletRow (inlHom E E) h k p).symm
  simp only [snd_sum, hconst, DualNumber.snd_mul, fst_inl, snd_inl, zero_mul, add_zero,
    jetTangent, Matrix.map_apply]

omit [Algebra ℂ E] in
private theorem snd_singlet (h : E) (W : TransferMatrix D) :
    (singletContract (inl h) W).snd = singletContract h (jetTangent W) := by
  simp only [singletContract, DualNumber.snd_mul, fst_inl, snd_inl,
    snd_sub, snd_add, zero_mul, add_zero, jetTangent, Matrix.map_apply]

private theorem map_tripletContract {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (h : R) (W : TransferMatrix R) (i j : Fin 3) :
    f (tripletContract h W i j) = tripletContract (f h) (f.mapMatrix W) i j := by
  rw [tripletContract_eq, tripletContract_eq]
  simp only [map_sum, map_mul, map_tripletRow]
  rfl

private theorem section_eval (z : Fin 5 → D) (m : ℕ) (i j : Fin 3) :
    aeval z (tripletReadout (C (1 / 2 : ℂ)) (transverseKet 0) (sectionBra X) m i j) =
      tripletReadout (inl (half E)) (transverseKet 0) (sectionBra z) m i j := by
  let f : MvPolynomial (Fin 5) ℂ →+* D := (aeval z).toRingHom
  change f _ = _
  rw [← tripletContract_raw, map_tripletContract, map_mixedRaw, map_sectionKet, map_sectionBra,
    map_zero, tripletContract_raw]
  have hf : f ∘ X = z := funext fun k => aeval_X z k
  have hh : f (C (1 / 2 : ℂ)) = inl (half E) :=
    (aeval_C z (1 / 2 : ℂ)).trans (IsScalarTower.algebraMap_apply ℂ E D _)
  rw [hf, hh]

private theorem triplet_parameter (x : Fin 5 → E) (m : ℕ) (k : Fin 5) (i j : Fin 3) :
    tripletContract (half E) (parameterTangent x m k) i j =
      aeval x (pderiv k (tripletReadout (C (1 / 2 : ℂ)) (transverseKet 0) (sectionBra X) m i j)) := by
  let z : Fin 5 → D := fun q => ⟨x q, (Pi.single k 1 : Fin 5 → E) q⟩
  let W := mixedRaw (transverseKet (0 : D)) (sectionBra z) m
  change tripletContract (half E) (jetTangent W) i j = _
  rw [← snd_triplet, tripletContract_raw, ← section_eval z, snd_aeval]
  rw [Finset.sum_eq_single k]
  · simp [z]
  · intro u _ hu
    simp [z, Pi.single_eq_of_ne hu]
  · simp

private theorem middle_section {R : Type*} [CommRing R] (h : R) (x : Fin 5 → R)
    (m : ℕ) (j : Fin 3) :
    tripletReadout h (transverseKet 0) (sectionBra x) m 1 j = 0 := by
  exact tripletReadout_section h _ _ m 1 j

private theorem middle_parameter (x : Fin 5 → E) (m : ℕ) (k : Fin 5) (j : Fin 3) :
    tripletContract (half E) (parameterTangent x m k) 1 j = 0 := by
  rw [triplet_parameter, middle_section, map_zero, map_zero]

omit [Algebra ℂ E] in
private theorem section_lift (x : Fin 5 → E) :
    sectionBraJet x 0 = fun i => liftCore (sectionBra x i) := by
  exact (map_sectionBra (inlHom E E) x).symm

private theorem triplet_transverse (x : Fin 5 → E) (m : ℕ) (i j : Fin 3) :
    tripletContract (half E) (transverseTangent x m) i j =
      (tripletReadout (inl (half E)) (transverseKet (inr 1))
        (fun k => liftCore (sectionBra x k)) m i j).snd := by
  rw [transverseTangent, ← snd_triplet, section_lift, tripletContract_raw]

private theorem zero_singlet_section {R : Type*} [CommRing R] (h : R) (x : Fin 5 → R)
    (m : ℕ) :
    singletTrace h (transverseKet 0) (sectionBra x) m = 0 := by
  unfold singletTrace sectionBra
  rw [trace_kronecker_transfer]
  simp [coreCommutator, transverseKet]

private theorem singlet_parameter (x : Fin 5 → E) (m : ℕ) (k : Fin 5) :
    singletContract (half E) (parameterTangent x m k) = 0 := by
  let z : Fin 5 → D := fun q => ⟨x q, (Pi.single k 1 : Fin 5 → E) q⟩
  let W := mixedRaw (transverseKet (0 : D)) (sectionBra z) m
  change singletContract (half E) (jetTangent W) = 0
  rw [← snd_singlet]
  have h := singletTrace_eq_native (inl (half E)) (transverseKet 0) (sectionBra z) m
  change singletTrace (inl (half E)) (transverseKet 0) (sectionBra z) m =
    singletContract (inl (half E)) W at h
  rw [← h, zero_singlet_section, snd_zero]

private theorem singlet_transverse (x : Fin 5 → E) (m : ℕ) :
    singletContract (half E) (transverseTangent x m) =
      (singletTrace (inl (half E)) (transverseKet (inr 1))
        (fun k => liftCore (sectionBra x k)) m).snd := by
  rw [transverseTangent, ← snd_singlet, section_lift]
  congr 1
  exact (singletTrace_eq_native _ _ _ _).symm

private theorem singlet_rotation (W : TransferMatrix E) (H : BondMatrix E) :
    singletContract (half E) (physicalTangent H W) = 0 := by
  simp [singletContract, physicalTangent, pairGenerator, Matrix.mul_apply,
    Matrix.kroneckerMap_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
  right; ring

private theorem diagonal_section (x : Fin 5 → E) (m : ℕ) (j : Fin 3) :
    tripletContract (half E) (physicalTangent diagonalShear (sectionRaw x m)) 1 j = 0 := by
  rw [tripletConj_diag, sectionRaw, tripletContract_raw]
  fin_cases j <;>
    simp [diagonalTriplet, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three, middle_section]

private theorem diagonal_outer (x : Fin 5 → E) (m : ℕ) (i : Fin 6) :
    outerEntry (tripletContract (half E) (physicalTangent diagonalShear (sectionRaw x m))) i =
      ((![0, 2, 4, -4, -2, 0] : Fin 6 → ℤ) i : E) *
        outerEntry (tripletReadout (half E) (transverseKet 0) (sectionBra x) m) i := by
  rw [tripletConj_diag, sectionRaw, tripletContract_raw]
  fin_cases i <;>
    simp [outerEntry, diagonalTriplet, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three]
  case «1» =>
    let F := tripletReadout (half E) (transverseKet 0) (sectionBra x) m
    change F 0 0 * 0 + F 0 1 * 0 + F 0 2 * 0 = 0
    simp
  all_goals ring

private theorem raw_outer_eval (x : Fin 5 → E) (m : ℕ) (i : Fin 6) :
    aeval x (outerEntry (tripletReadout (C (1 / 2 : ℂ)) (transverseKet 0) (sectionBra X) m) i) =
      outerEntry (tripletReadout (half E) (transverseKet 0) (sectionBra x) m) i := by
  let f : MvPolynomial (Fin 5) ℂ →+* E := (aeval x).toRingHom
  change f _ = _
  unfold outerEntry
  rw [← tripletContract_raw, map_tripletContract, map_mixedRaw, map_sectionKet, map_sectionBra,
    map_zero, tripletContract_raw]
  rw [show f ∘ X = x from funext fun k => aeval_X x k]
  rw [show f (C (1 / 2 : ℂ)) = half E from aeval_C x _]

private theorem outer_parameter (x : Fin 5 → E) (m : ℕ) (i : Fin 6) (j : Fin 5) :
    sectionTripletMinor (1 / 2 : ℂ) m x (.inl i) (.inl j.castSucc) =
      outerEntry (tripletContract (half E) (parameterTangent x m j)) i := by
  have h : sectionTripletMinor (1 / 2 : ℂ) m x (.inl i) (.inl j.castSucc) =
      aeval x (pderiv j (outerEntry
        (tripletReadout (C (1 / 2 : ℂ)) (transverseKet 0) (sectionBra X) m) i)) := by
    fin_cases j <;> rfl
  rw [h]
  unfold outerEntry
  exact (triplet_parameter x m j _ _).symm

private theorem outer_diagonal (x : Fin 5 → E) (m : ℕ) (i : Fin 6) :
    sectionTripletMinor (1 / 2 : ℂ) m x (.inl i) (.inl 5) =
      outerEntry (tripletContract (half E) (physicalTangent diagonalShear (sectionRaw x m))) i := by
  change aeval x
    (C ((![0, 2, 4, -4, -2, 0] : Fin 6 → ℤ) i : ℂ) *
      outerEntry (tripletReadout (C (1 / 2 : ℂ)) (transverseKet 0) (sectionBra X) m) i) = _
  rw [diagonal_outer, map_mul, aeval_C, raw_outer_eval, map_intCast]

omit [Algebra ℂ E] in
private theorem sectionRawColumns_parameter (x : Fin 5 → E) (m : ℕ) (j : Fin 5) :
    sectionRawColumns x m (.inl j.castSucc) = parameterTangent x m j := by
  fin_cases j <;> rfl

private theorem sectionTripletMinor_apply (x : Fin 5 → E) (m : ℕ) (i j : TripletIndex) :
    sectionTripletMinor (1 / 2 : ℂ) m x i j = tripletContractRow (sectionRawColumns x m j) i := by
  rcases j with j | j
  · refine Fin.lastCases ?_ (fun k => ?_) j
    · rcases i with i | i
      · exact outer_diagonal x m i
      · exact (diagonal_section x m i).symm
    · rw [sectionRawColumns_parameter]
      rcases i with i | i
      · exact outer_parameter x m i k
      · exact (middle_parameter x m k i).symm
  · let F := tripletReadout (half E) (transverseKet 0) (sectionBra x) m
    have h (upper : Bool) :
        tripletContract (half E) (physicalTangent (physicalShear upper) (sectionRaw x m)) =
          tripletRotation upper F := by
      rw [tripletConj, sectionRaw, tripletContract_raw]
    fin_cases j
    · have hh : tripletContract (half E) (physicalTangent lowerShear (sectionRaw x m)) =
          tripletRotation false F := h false
      rcases i with i | i
      · exact congrArg (fun W => outerEntry W i) hh.symm
      · exact congrArg (fun W => W 1 i) hh.symm
    · have hh : tripletContract (half E) (physicalTangent upperShear (sectionRaw x m)) =
          tripletRotation true F := h true
      rcases i with i | i
      · exact congrArg (fun W => outerEntry W i) hh.symm
      · exact congrArg (fun W => W 1 i) hh.symm
    · rcases i with i | i
      · unfold tripletContractRow outerEntry
        exact (triplet_transverse x m _ _).symm
      · exact (triplet_transverse x m 1 i).symm

theorem sectionTripletMinor_rawColumns (x : Fin 5 → E) (m : ℕ) :
    sectionTripletMinor (1 / 2 : ℂ) m x =
      Matrix.of (fun i j => tripletContractRow (sectionRawColumns x m j) i) := by
  apply Matrix.ext
  exact sectionTripletMinor_apply x m

def singletColumnIndex : SingletIndex → TripletIndex :=
  Sum.elim Sum.inl (Sum.elim (fun j => Sum.inr j.castSucc) (fun _ => Sum.inr 2))

private theorem sectionSingletMinor_apply (x : Fin 5 → E) (m : ℕ) (i j : SingletIndex) :
    sectionSingletMinor (1 / 2 : ℂ) m x i j =
      singletContractRow (sectionRawColumns x m (singletColumnIndex j)) i := by
  rcases i with i | (i | i)
  · rcases j with j | (j | j)
    · exact sectionTripletMinor_apply x m (.inl i) (.inl j)
    · exact sectionTripletMinor_apply x m (.inl i) (.inr j.castSucc)
    · exact sectionTripletMinor_apply x m (.inl i) (.inr 2)
  · rcases j with j | (j | j)
    · exact sectionTripletMinor_apply x m (.inr (endpoint i)) (.inl j)
    · exact sectionTripletMinor_apply x m (.inr (endpoint i)) (.inr j.castSucc)
    · exact sectionTripletMinor_apply x m (.inr (endpoint i)) (.inr 2)
  · rcases j with j | (j | j)
    · fin_cases j <;>
        simp only [sectionSingletMinor, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply,
          singletContractRow, singletColumnIndex, Sum.elim_inl, Sum.elim_inr, sectionRawColumns]
      all_goals first
        | exact (singlet_parameter x m _).symm
        | exact (singlet_rotation (sectionRaw x m) diagonalShear).symm
    · fin_cases j <;>
        simp only [sectionSingletMinor, Matrix.fromBlocks_apply₂₂, Matrix.fromBlocks_apply₂₁,
          Matrix.zero_apply, singletContractRow, singletColumnIndex, Sum.elim_inl, Sum.elim_inr,
          sectionRawColumns]
      all_goals exact (singlet_rotation (sectionRaw x m) _).symm
    · exact (singlet_transverse x m).symm

theorem sectionSingletMinor_rawColumns (x : Fin 5 → E) (m : ℕ) :
    sectionSingletMinor (1 / 2 : ℂ) m x =
      Matrix.of (fun i j => singletContractRow (sectionRawColumns x m (singletColumnIndex j)) i) := by
  apply Matrix.ext
  exact sectionSingletMinor_apply x m

end
end D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformMovingFrame
