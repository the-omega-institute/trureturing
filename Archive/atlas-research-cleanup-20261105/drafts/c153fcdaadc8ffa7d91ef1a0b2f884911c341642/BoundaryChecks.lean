import D5.S3.Topology.Measures.FiniteObservationVariation
import Mathlib.MeasureTheory.Measure.Dirac.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Set MeasureTheory
open D5.S3.ConceptDynamics.CanonicalImage.FiniteObservationQuotientRange

-- No finite coordinate budget works for all regular signed measures on the
-- same compact zero-dimensional carrier. Both Dirac Jordan parts are regular.
-- No named declaration is retained in D5.
example (J : Finset ℕ) :
    let K := ℕ → Bool
    letI : MeasurableSpace K := borel K
    ∃ s : SignedMeasure K,
      s.toJordanDecomposition.posPart.Regular ∧
      s.toJordanDecomposition.negPart.Regular ∧
      s.totalVariation.real univ = 2 ∧
      s.map (finiteObservationReadout (fun i (x : K) => x i) J) = 0 := by
  classical
  dsimp only
  let K := ℕ → Bool
  letI : MeasurableSpace K := borel K
  letI : BorelSpace K := ⟨rfl⟩
  obtain ⟨n, hn⟩ := J.exists_notMem
  let x : K := fun _ => false
  let y : K := fun m => if m = n then true else false
  have hxy : x ≠ y := by
    intro h
    have h' := congrFun h n
    simpa [x, y] using h'
  let p := finiteObservationReadout (fun i (z : K) => z i) J
  have hp : Continuous p := continuous_pi (fun j => continuous_apply j.val)
  have hread : p x = p y := by
    funext j
    have hj : j.val ≠ n := by
      intro h
      exact hn (h ▸ j.property)
    change x j.val = y j.val
    simp [x, y, hj]
  let d : JordanDecomposition K := {
    posPart := Measure.dirac x
    negPart := Measure.dirac y
    mutuallySingular := by
      refine ⟨{x}ᶜ, (MeasurableSet.singleton x).compl, ?_, ?_⟩
      · simp
      · simp [hxy, Ne.symm hxy] }
  let s := d.toSignedMeasure
  have htv : s.totalVariation.real univ = 2 := by
    norm_num [s, SignedMeasure.totalVariation, d, Measure.real, ENNReal.toReal_add]
  have hmap : s.map p = 0 := by
    ext B hB
    rw [VectorMeasure.map_apply s hp.measurable hB]
    change d.toSignedMeasure (p ⁻¹' B) = 0
    rw [JordanDecomposition.toSignedMeasure,
      Measure.toSignedMeasure_sub_apply (hp.measurable hB)]
    change (Measure.dirac x).real (p ⁻¹' B) - (Measure.dirac y).real (p ⁻¹' B) = 0
    have hmem : x ∈ p ⁻¹' B ↔ y ∈ p ⁻¹' B := by
      change p x ∈ B ↔ p y ∈ B
      rw [hread]
    simp [Measure.real, Measure.dirac_apply' _ (hp.measurable hB), Set.indicator_apply, hmem]
  refine ⟨s, ?_, ?_, htv, hmap⟩
  · change d.toSignedMeasure.toJordanDecomposition.posPart.Regular
    simp only [JordanDecomposition.toJordanDecomposition_toSignedMeasure]
    change (Measure.dirac x).Regular
    infer_instance
  · change d.toSignedMeasure.toJordanDecomposition.negPart.Regular
    simp only [JordanDecomposition.toJordanDecomposition_toSignedMeasure]
    change (Measure.dirac y).Regular
    infer_instance
