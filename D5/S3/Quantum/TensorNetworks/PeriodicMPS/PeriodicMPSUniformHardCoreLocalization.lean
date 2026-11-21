/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformHardCoreLocalization
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformHardCoreLocalization
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformHardCoreMarginalWitness, lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSUniformHardCorePencilDecoder, lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPSProjectiveCoordinates, lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPSCompactFiber]
   utility: none
   digest: The witness marginal has a singleton fiber in the compact closure, which forces nearby actual competitors into the ordinary trace chart. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformHardCoreMarginalWitness
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSUniformHardCorePencilDecoder
import D5.S3.Quantum.TensorNetworks.PeriodicMPSProjectiveCoordinates
import D5.S3.Quantum.TensorNetworks.PeriodicMPSCompactFiber

/-! The hard-core witness has a singleton marginal fiber in the compact closure
of actual tensor projectors. The determinant-pencil decoder then confines
nearby actual competitors to the ordinary invariant chart. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformHardCoreLocalization

open PeriodicMPSParentIntersection (Bond Word)
open PeriodicMPSUniformDeterminantPencil (witnessCore)
open PeriodicMPSUniformHardCoreMarginalWitness
open PeriodicMPSProjectiveCoordinates
  (outer projector projective isCompact_projective projector_mem projector_scale
    projector_ratio projector_diag_ne_zero_iff eq_smul_of_projector_eq)
open PeriodicMPSUniformHardCorePencilDecoder
  (witnessTensor ordinaryInvariants ordinaryDecoder exists_open_ordinaryDecoder)
open UniformMPSExpectedDimensionRefutation (traceWord)
open Set Filter
open scoped BigOperators ComplexConjugate Topology

noncomputable section

variable {m : ℕ}

abbrev StateMatrix (m : ℕ) := Matrix (Word (2 + m)) (Word (2 + m)) ℂ

/-- The literal partial trace over the sites after the first two. -/
def twoSiteObservation (m : ℕ) : StateMatrix m →ₗ[ℂ] Matrix Pair Pair ℂ where
  toFun P p q := ∑ b : Word m, P (Fin.append ![p.1, p.2] b) (Fin.append ![q.1, q.2] b)
  map_add' P Q := by
    ext p q
    exact Finset.sum_add_distrib
  map_smul' z P := by
    ext p q
    change (∑ b : Word m, z • P (Fin.append ![p.1, p.2] b) (Fin.append ![q.1, q.2] b)) =
      z • ∑ b : Word m, P (Fin.append ![p.1, p.2] b) (Fin.append ![q.1, q.2] b)
    exact Finset.smul_sum.symm

private theorem continuous_entry (u v : Word (2 + m)) :
    Continuous (fun P : StateMatrix m => P u v) :=
  (continuous_apply v).comp (continuous_apply u)

theorem continuous_twoSiteObservation (m : ℕ) : Continuous (twoSiteObservation m) := by
  refine continuous_pi fun p => continuous_pi fun q => ?_
  exact continuous_finsetSum _ fun _ _ => continuous_entry _ _

theorem twoSiteObservation_outer (ψ : Amplitudes m) :
    twoSiteObservation m (outer ψ) = pairGram ψ := rfl

theorem twoSiteObservation_projector (ψ : Amplitudes m) :
    twoSiteObservation m (projector ψ) = (PeriodicMPSProjectiveCoordinates.mass ψ)⁻¹ • pairGram ψ := by
  ext p q
  change (∑ b : Word m, (PeriodicMPSProjectiveCoordinates.mass ψ)⁻¹ •
    outer ψ (Fin.append ![p.1, p.2] b) (Fin.append ![q.1, q.2] b)) =
      (PeriodicMPSProjectiveCoordinates.mass ψ)⁻¹ •
        ∑ b : Word m, outer ψ (Fin.append ![p.1, p.2] b) (Fin.append ![q.1, q.2] b)
  exact Finset.smul_sum.symm

/-- The density of an actual periodic tensor, divided by its total squared mass. -/
def normalizedMarginal (m : ℕ) (A : Fin 2 → Bond) : Matrix Pair Pair ℂ :=
  let G := pairGram (traceWord 2 2 (2 + m) A)
  (G.trace.re)⁻¹ • G

theorem twoSiteObservation_traceWord (A : Fin 2 → Bond) :
    twoSiteObservation m (projector (traceWord 2 2 (2 + m) A)) =
      normalizedMarginal m A := by
  rw [twoSiteObservation_projector]
  change (mass (traceWord 2 2 (2 + m) A))⁻¹ • pairGram _ = normalizedMarginal m A
  rw [mass_eq_trace, normalizedMarginal]

theorem normalizedMarginal_eq_rawTwo (A : Fin 2 → Bond) (r : ℕ) :
    normalizedMarginal (r + 2) A =
      ((PeriodicMPSTwoSiteAmbiguity.rawTwo A r).trace.re)⁻¹ •
        PeriodicMPSTwoSiteAmbiguity.rawTwo A r := by
  rw [normalizedMarginal, pairGram_traceWord]

/-- Projectors of all nonzero tensors given by an actual bond-two core pair. -/
def actualProjectors (m : ℕ) : Set (StateMatrix m) :=
  (fun A : Fin 2 → Bond => projector (traceWord 2 2 (2 + m) A)) ''
    {A | traceWord 2 2 (2 + m) A ≠ 0}

theorem closure_actualProjectors_subset_projective (m : ℕ) :
    closure (actualProjectors m) ⊆ projective := by
  apply closure_minimal _ isCompact_projective.isClosed
  rintro _ ⟨A, hA, rfl⟩
  exact projector_mem _ hA

theorem isCompact_closure_actualProjectors (m : ℕ) :
    IsCompact (closure (actualProjectors m)) :=
  isCompact_projective.of_isClosed_subset isClosed_closure
    (closure_actualProjectors_subset_projective m)

def witnessProjector (m : ℕ) : StateMatrix m := projector (witnessTensor (2 + m))

private def vacuum (m : ℕ) : Word (2 + m) := fun _ => 0

private theorem witnessTensor_eq_indicator (hn : 7 ≤ 2 + m) :
    witnessTensor (2 + m) = independentIndicator m :=
  funext (PeriodicMPSUniformHardCoreWitnessAmplitude.traceWord_witnessCore_eq_indicator hn)

private theorem witnessTensor_vacuum (hn : 7 ≤ 2 + m) :
    witnessTensor (2 + m) (vacuum m) = 1 := by
  rw [witnessTensor_eq_indicator hn]
  apply ite_eq_left
  exact (PeriodicMPSUniformHardCoreCounts.occupied_independent_iff hn (vacuum m)).2
    (by simp [vacuum])

theorem witnessProjector_mem_actualProjectors (hn : 7 ≤ 2 + m) :
    witnessProjector m ∈ actualProjectors m :=
  ⟨witnessCore, fun h => one_ne_zero ((witnessTensor_vacuum hn).symm.trans
    (congrFun h (vacuum m))), rfl⟩

private theorem cyclic_column_of_mem_closure {P : StateMatrix m}
    (hP : P ∈ closure (actualProjectors m)) (i : Fin (2 + m)) (u v : Word (2 + m)) :
    P (rotateWord i u) v = P u v := by
  refine closure_minimal ?_ (isClosed_eq (continuous_entry (rotateWord i u) v)
    (continuous_entry u v)) hP
  rintro _ ⟨A, _, rfl⟩
  change projector _ (rotateWord i u) v = projector _ u v
  simp only [projector, Matrix.smul_apply, outer, cyclic_traceWord A i u]

/-- The hard-core density identifies its projector among all cyclic rays. -/
theorem eq_witnessProjector_of_cyclic_columns (hn : 7 ≤ 2 + m) {P : StateMatrix m}
    (hP : P ∈ projective)
    (hcyc : ∀ (i : Fin (2 + m)) (u v : Word (2 + m)), P (rotateWord i u) v = P u v)
    (hobs : twoSiteObservation m P = twoSiteObservation m (witnessProjector m)) :
    P = witnessProjector m := by
  obtain ⟨ψ, hψ, rfl⟩ := hP
  change PeriodicMPSProjectiveCoordinates.mass ψ = 1 at hψ
  have hψne : ψ ≠ 0 := by
    intro he
    simp [he, PeriodicMPSProjectiveCoordinates.mass] at hψ
  obtain ⟨v, hv⟩ : ∃ v, ψ v ≠ 0 := by
    by_contra! h
    exact hψne (funext h)
  have hψcyc : Cyclic ψ := fun i u =>
    mul_right_cancel₀ ((map_ne_zero (starRingEnd ℂ)).2 hv) (hcyc i u v)
  have hw : witnessTensor (2 + m) ≠ 0 :=
    fun he => one_ne_zero ((witnessTensor_vacuum hn).symm.trans (congrFun he (vacuum m)))
  obtain ⟨χ, hχ, hout⟩ := projector_mem _ hw
  change PeriodicMPSProjectiveCoordinates.mass χ = 1 at hχ
  change outer χ = witnessProjector m at hout
  have hχproj : projector χ = witnessProjector m := by
    rw [projector, hχ, inv_one, one_smul, hout]
  obtain ⟨a, ha, hχa⟩ := eq_smul_of_projector_eq hw hχproj.symm
  rw [← hout, twoSiteObservation_outer, twoSiteObservation_outer, hχa,
    witnessTensor_eq_indicator hn] at hobs
  obtain ⟨c, hc, hψc⟩ := eq_constant_same_norm_of_pairGram_eq_indicator hn hψcyc a hobs
  have hcne : c ≠ 0 := by
    intro he
    exact ha (Complex.normSq_eq_zero.mp (by simpa [he] using hc.symm))
  have hrep : ψ = c • witnessTensor (2 + m) := by
    rw [witnessTensor_eq_indicator hn]
    exact funext hψc
  have hψproj : projector ψ = outer ψ := by
    simp [projector, hψ]
  rw [← hψproj, hrep, projector_scale _ hcne]
  rfl

theorem eq_witnessProjector_of_mem_closure (hn : 7 ≤ 2 + m) {P : StateMatrix m}
    (hP : P ∈ closure (actualProjectors m))
    (hobs : twoSiteObservation m P = normalizedMarginal m witnessCore) :
    P = witnessProjector m := by
  apply eq_witnessProjector_of_cyclic_columns hn
    (closure_actualProjectors_subset_projective m hP) (cyclic_column_of_mem_closure hP)
  exact hobs.trans (twoSiteObservation_traceWord witnessCore).symm

/-- The witness's normalized density has exactly one preimage in the compact closure. -/
theorem closure_actualProjectors_witness_fiber (hn : 7 ≤ 2 + m) :
    closure (actualProjectors m) ∩ twoSiteObservation m ⁻¹' {normalizedMarginal m witnessCore} =
      {witnessProjector m} := by
  ext P
  constructor
  · rintro ⟨hP, hobs⟩
    exact eq_witnessProjector_of_mem_closure hn hP hobs
  · rintro (rfl : P = witnessProjector m)
    exact ⟨subset_closure (witnessProjector_mem_actualProjectors hn),
      twoSiteObservation_traceWord witnessCore⟩

private def vacuumChart (P : StateMatrix m) : Amplitudes m :=
  fun u => P u (vacuum m) / P (vacuum m) (vacuum m)

private theorem continuousAt_vacuumChart {P : StateMatrix m}
    (hP : P (vacuum m) (vacuum m) ≠ 0) : ContinuousAt vacuumChart P := by
  apply continuousAt_pi.mpr
  intro u
  exact (continuous_entry u (vacuum m)).continuousAt.div
    (continuous_entry (vacuum m) (vacuum m)).continuousAt hP

private theorem vacuumChart_projector (ψ : Amplitudes m) (hψ : ψ (vacuum m) ≠ 0) :
    vacuumChart (projector ψ) = (ψ (vacuum m))⁻¹ • ψ := by
  funext u
  change projector ψ u (vacuum m) / projector ψ (vacuum m) (vacuum m) =
    (ψ (vacuum m))⁻¹ * ψ u
  rw [projector_ratio _ _ _ hψ, div_eq_mul_inv, mul_comm]

/-- Every actual competitor over an open neighborhood of the hard-core density
has nonzero first trace and ordinary invariants in the prescribed neighborhood. -/
theorem exists_open_normalizedMarginal_localization (hn : 7 ≤ 2 + m)
    {U : Set (ℂ × ℂ × ℂ × ℂ)} (hU : U ∈ 𝓝 (ordinaryInvariants witnessCore)) :
    ∃ W : Set (Matrix Pair Pair ℂ), IsOpen W ∧ normalizedMarginal m witnessCore ∈ W ∧
      ∀ A : Fin 2 → Bond, traceWord 2 2 (2 + m) A ≠ 0 → normalizedMarginal m A ∈ W →
        (A 0).trace ≠ 0 ∧ ordinaryInvariants A ∈ U := by
  obtain ⟨V, hV, hwV, hdec, hread⟩ := exists_open_ordinaryDecoder (2 + m) hn
  have hdiag : witnessProjector m (vacuum m) (vacuum m) ≠ 0 := by
    apply (projector_diag_ne_zero_iff _ _).2
    rw [witnessTensor_vacuum hn]
    exact one_ne_zero
  have hchart : vacuumChart (witnessProjector m) = witnessTensor (2 + m) := by
    rw [witnessProjector, vacuumChart_projector _ ((witnessTensor_vacuum hn).trans_ne one_ne_zero),
      witnessTensor_vacuum hn, inv_one, one_smul]
  have hchartContinuous := continuousAt_vacuumChart hdiag
  have hchartV : vacuumChart (witnessProjector m) ∈ V := hchart ▸ hwV
  have hdecoderAt := (hdec _ hwV).continuousAt (hV.mem_nhds hwV)
  have hdecoderValue : ordinaryDecoder (2 + m) hn (witnessTensor (2 + m)) =
      ordinaryInvariants witnessCore :=
    (hread _ hwV witnessCore 1 (by simp [witnessTensor])).2
  have hdecoderTendsto :
      Tendsto (ordinaryDecoder (2 + m) hn ∘ vacuumChart) (𝓝 (witnessProjector m))
        (𝓝 (ordinaryInvariants witnessCore)) := by
    rw [← hdecoderValue, ← hchart]
    exact hdecoderAt.comp_of_eq hchartContinuous hchart
  have hnear : ∀ᶠ P in 𝓝 (witnessProjector m),
      P (vacuum m) (vacuum m) ≠ 0 ∧ vacuumChart P ∈ V ∧
        ordinaryDecoder (2 + m) hn (vacuumChart P) ∈ U := by
    exact ((continuous_entry (vacuum m) (vacuum m)).continuousAt.eventually_ne hdiag).and
      ((hchartContinuous.eventually (hV.mem_nhds hchartV)).and (hdecoderTendsto.eventually hU))
  obtain ⟨G, hGsub, hGopen, hwG⟩ := mem_nhds_iff.mp hnear
  let X := ↥(closure (actualProjectors m))
  let : CompactSpace X := isCompact_iff_compactSpace.mp (isCompact_closure_actualProjectors m)
  let f : X → Matrix Pair Pair ℂ := fun P => twoSiteObservation m P.val
  have hf : Continuous f := (continuous_twoSiteObservation m).comp continuous_subtype_val
  have hcover : f ⁻¹' {normalizedMarginal m witnessCore} ⊆ Subtype.val ⁻¹' G := by
    intro P hP
    change P.val ∈ G
    rwa [eq_witnessProjector_of_mem_closure hn P.property hP]
  obtain ⟨W, hWopen, hwW, hWsub⟩ := PeriodicMPSCompactFiber.nearby_fibers_subset hf
    (hGopen.preimage continuous_subtype_val) hcover
  refine ⟨W, hWopen, hwW, ?_⟩
  intro A hA hAW
  let ψ := traceWord 2 2 (2 + m) A
  let P : X := ⟨projector ψ, subset_closure ⟨A, hA, rfl⟩⟩
  have hPW : f P ∈ W := by
    change twoSiteObservation m (projector ψ) ∈ W
    rwa [twoSiteObservation_traceWord]
  obtain ⟨hPdiag, hPV, hPU⟩ := hGsub (hWsub hPW : P.val ∈ G)
  have hψ : ψ (vacuum m) ≠ 0 := (projector_diag_ne_zero_iff _ _).1 hPdiag
  obtain ⟨hAtrace, hinv⟩ := hread _ hPV A (ψ (vacuum m))⁻¹ (vacuumChart_projector ψ hψ)
  exact ⟨hAtrace, hinv ▸ hPU⟩

end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformHardCoreLocalization
