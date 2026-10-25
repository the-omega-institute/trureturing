import CFMPActualPositiveVolume285Transient
import D5.S3.Geometry.Hyperideal.OriginalCosineDeterminantInterface

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped BigOperators Topology
open CFMPOriginalCovolumeNeighborhood251Transient (Lengths RealizationFamily physicalCovolume)
open CFMPOriginalPhysicalEdge237Transient (sourceAngle)
open CFMPOriginalCovolumeC1253Transient (sourceDifferential sourceDifferential_apply)
open CFMPGenuineLengthNeighborhood435Transient (genuine sourceCosine sourceCosine_continuousAt)
open CFMPGlobalGenuineCovolume256Transient (realizedFamily)
open CFMPActualExtendedAngle268Transient
open CFMPActualAnalyticDiscriminant280Transient
open CFMPActualPositiveVolume285Transient
open CFMPActualNativeMass435Transient (referenceMass)
open D5.S3.Geometry.Hyperideal.LengthGramBody
open D5.S3.Geometry.Hyperideal.TwoLengthAngleSum (rawNum leftRad rightRad)
open D5.S3.Geometry.Hyperideal.FourCycleEnvelopes (rad numerator)
open D5.S3.Geometry.Hyperideal.FourCycleCurvature (frame)
open D5.S3.Geometry.Hyperideal.PositiveFlatClassification (Sector)
open D5.S3.Geometry.Hyperideal.OriginalCosineDeterminantInterface
  (D1 D2 N gram original_cosine_interface)
open private delta square_gap from D5.S3.Geometry.Hyperideal.PositiveFlatClassification

namespace CFMPActualFlatVolume286Transient

/-- The two existing original identities identify the discriminant, including its zero set. -/
theorem lengthGram_det_eq_discriminant (a : Lengths) (ha : a ∈ positiveLengths) :
    (lengthGram a).det = discriminant a := by
  let x : Fin 6 → ℝ := fun q => Real.cosh (a q)
  have hx (q : Fin 6) : 1 < x q := Real.one_lt_cosh.mpr (ha q).ne'
  have hfactor : x 0 ^ 2 - 1 ≠ 0 := by nlinarith [hx 0]
  have hi := (original_cosine_interface (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)
    (hx 0) (hx 1) (hx 2) (hx 3) (hx 4) (hx 5)).2.1
  have hg : gram (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) = lengthGram a := rfl
  rw [hg] at hi
  have hs :
      N (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) ^ 2 -
        D1 (x 0) (x 1) (x 5) * D2 (x 0) (x 2) (x 4) =
      (x 0 ^ 2 - 1) * discriminant a := by
    have hs := square_gap x 0
    simp only [rawNum,leftRad,rightRad,frame,Matrix.cons_val_zero,Matrix.cons_val_succ] at hs
    convert hs using 1 <;> dsimp [N,D1,D2,numerator,rad,discriminant,x] <;> ring
  apply mul_left_cancel₀ hfactor
  nlinarith only [hi,hs]

def anglePairing (a : Lengths) : ℝ := ∑ q : Fin 6, a q * sourceAngle a q

def referenceCovolume (a : Lengths) : ℝ := 2 * referenceMass a + anglePairing a

theorem anglePairing_continuousAt (a : Lengths) (ha : a ∈ positiveLengths) :
    ContinuousAt anglePairing a := by
  apply tendsto_finsetSum
  intro q _
  have hangle : ContinuousAt (fun b : Lengths => sourceAngle b q) a :=
    Real.continuous_arccos.continuousAt.comp (sourceCosine_continuousAt a ha q)
  exact (continuous_apply q).continuousAt.mul hangle

theorem referenceCovolume_continuousAt (a : Lengths) (ha : a ∈ positiveLengths) :
    ContinuousAt referenceCovolume a :=
  ((referenceMass_continuousAt a ha).const_mul 2).add (anglePairing_continuousAt a ha)

theorem referenceCovolume_eq_actual (G : RealizationFamily) (hG : realizedFamily G)
    (a : Lengths) (ha : genuine a) : referenceCovolume a = physicalCovolume G a := by
  simp only [referenceCovolume,physicalCovolume,anglePairing,
    physicalVolume_eq_reference G hG a ha]

theorem referenceCovolume_eq_flat (a : Lengths) (ha : a ∈ positiveLengths)
    (k : Fin 3) (hk : Sector (fun q => Real.cosh (a q)) k) :
    referenceCovolume a = flatPrimitive k a := by
  have hnonneg : 0 ≤ discriminant a := by
    apply le_of_not_gt
    intro hn
    exact (not_le_of_gt (((genuine_iff_discriminant_neg a ha).mpr hn).2
      (k.castAdd 3)).1) hk
  have hmass : referenceMass a = 0 := referenceMass_eq_zero_of_det_nonneg a
    (by rwa [lengthGram_det_eq_discriminant a ha])
  simp only [referenceCovolume,hmass,mul_zero,zero_add,anglePairing,
    flat_sourceAngle a ha k hk]
  fin_cases k <;> simp [flatPrimitive,Fin.sum_univ_succ] <;> ring

theorem referenceCovolume_eq_covector_at_nonnegative_discriminant
    (a : Lengths) (ha : a ∈ positiveLengths) (hd : 0 ≤ discriminant a) :
    referenceCovolume a = sourceDifferential a a := by
  have hm := referenceMass_eq_zero_of_det_nonneg a
    (show 0 ≤ (lengthGram a).det by rwa [lengthGram_det_eq_discriminant a ha])
  simp only [referenceCovolume,hm,mul_zero,zero_add,anglePairing,sourceDifferential_apply]
  exact Finset.sum_congr rfl (fun q _ => mul_comm _ _)

theorem physicalVolume_tendsto_zero_discriminant
    {ι : Type*} {L : Filter ι} (a : ι → Lengths) (p : Lengths)
    (hp : p ∈ positiveLengths) (hd : discriminant p = 0)
    (ha : Tendsto a L (𝓝 p)) (hg : ∀ᶠ i in L, genuine (a i))
    (G : RealizationFamily) (hG : realizedFamily G) :
    Tendsto (fun i => CFMPOriginalCovolumeNeighborhood251Transient.physicalVolume G (a i))
      L (𝓝 0) :=
  physicalVolume_tendsto_zero a p hp
    ((lengthGram_det_eq_discriminant p hp).trans hd) ha hg G hG

theorem physicalCovolume_tendsto_flat
    {ι : Type*} {L : Filter ι} (a : ι → Lengths) (p : Lengths)
    (hp : p ∈ positiveLengths) (k : Fin 3)
    (hk : Sector (fun q => Real.cosh (p q)) k)
    (ha : Tendsto a L (𝓝 p)) (hg : ∀ᶠ i in L, genuine (a i))
    (G : RealizationFamily) (hG : realizedFamily G) :
    Tendsto (fun i => physicalCovolume G (a i)) L (𝓝 (flatPrimitive k p)) := by
  have h := (referenceCovolume_continuousAt p hp).tendsto.comp ha
  rw [referenceCovolume_eq_flat p hp k hk] at h
  exact h.congr' (hg.mono (fun i hi => referenceCovolume_eq_actual G hG (a i) hi))

end CFMPActualFlatVolume286Transient

run_cmd do
  let env := (← Lean.getEnv).setExporting false
  for name in [``CFMPActualFlatVolume286Transient.lengthGram_det_eq_discriminant,
      ``CFMPActualFlatVolume286Transient.referenceCovolume_continuousAt,
      ``CFMPActualFlatVolume286Transient.referenceCovolume_eq_flat,
      ``CFMPActualFlatVolume286Transient.physicalVolume_tendsto_zero_discriminant,
      ``CFMPActualFlatVolume286Transient.physicalCovolume_tendsto_flat] do
    unless (env.checked.get.find? name).isSome do
      Lean.throwError m!"CFMP286 original actual flat-volume identification absent: {name}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        Lean.throwError m!"CFMP286 disallowed axiom {ax}"
    Lean.logInfo m!"CFMP286 CHECKED {name} axioms={axioms}"
