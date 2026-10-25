import CFMPActualLocalAnglePrimitive275Transient

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology ContDiff
open CFMPOriginalCovolumeNeighborhood251Transient (Lengths physicalCovolume)
open CFMPOriginalCovolumeC1253Transient (sourceDifferential)
open CFMPGlobalGenuineCovolume256Transient
open CFMPGenuineLengthNeighborhood435Transient (genuine genuine_open)
open CFMPActualExtendedAngle268Transient
open CFMPActualFlatCoordinates271Transient
open CFMPActualFlatGraph269Transient (fiveCoordinates source_sector_graph)
open D5.S3.Geometry.Hyperideal.PositiveFlatClassification (Sector positive_classification)

namespace CFMPActualEverywhereLocalPrimitive276Transient

/-- Every positive original length point has a C1 local primitive of the
original extended six-angle covector, including every flat-sector boundary.
This is local exactness, without a global path-independence assertion. -/
theorem exists_local_angle_primitive (a : Lengths) (ha : a ∈ positiveLengths) :
    ∃ V : Set Lengths, a ∈ V ∧ IsOpen V ∧ V ⊆ positiveLengths ∧
      ∃ H : Lengths → ℝ, ContDiffOn ℝ 1 H V ∧
        ∀ b ∈ V, HasFDerivAt H (sourceDifferential b) b := by
  by_cases hg : genuine a
  · exact ⟨{b | genuine b},hg,genuine_open,(fun _ hb => hb.1),
      physicalCovolume wholeFamily,
      (physicalCovolume_contDiffOn_genuine wholeFamily wholeFamily_realized).1,
      fun b hb => (physicalCovolume_contDiffOn_genuine wholeFamily wholeFamily_realized).2 b hb⟩
  · have hng : ¬ D5.S3.Geometry.Hyperideal.PositiveFlatClassification.Genuine
        (fun q => Real.cosh (a q)) := fun h => hg ⟨ha,h⟩
    obtain ⟨k,hk,_⟩ :=
      (positive_classification (fun q => Real.cosh (a q))
        (fun q => Real.one_lt_cosh.mpr (ha q).ne')).2.1.resolve_left hng
    have hh : 0 ≤ (flatten (k.castAdd 3) a).2 := by
      simpa only [flatten,sub_nonneg] using (source_sector_graph a ha k).mp hk
    rcases eq_or_lt_of_le hh with hzero | hstrict
    · have hu : ∀ j, 0 < fiveCoordinates a (k.castAdd 3) j := by
        intro j
        fin_cases j <;> exact ha _
      obtain ⟨V,h0,hV,hpos,H,hH,hD,_⟩ :=
        CFMPActualLocalAnglePrimitive275Transient.exists_original_local_angle_primitive
          k (fiveCoordinates a (k.castAdd 3)) hu
      have hchart : flatten (k.castAdd 3) a = (fiveCoordinates a (k.castAdd 3),0) := by
        apply Prod.ext
        · rfl
        · exact hzero.symm
      have ha0 : unflatten (k.castAdd 3) (fiveCoordinates a (k.castAdd 3),0) = a := by
        rw [← hchart,unflatten_flatten]
      rw [ha0] at h0
      exact ⟨V,h0,hV,hpos,H,hH,hD⟩
    · let V : Set Lengths := positiveLengths ∩
        {b | 0 < (flatten (k.castAdd 3) b).2}
      have hV : IsOpen V := by
        apply isOpen_iff_mem_nhds.mpr
        intro b hb
        have hc := ((flatten_contDiffAt (k.castAdd 3) b hb.1).continuousAt).snd
        exact inter_mem (positiveLengths_open.mem_nhds hb.1)
          (hc.eventually (Ioi_mem_nhds hb.2))
      have hD (b : Lengths) (hb : b ∈ V) :
          HasFDerivAt (flatPrimitive k) (sourceDifferential b) b := by
        apply flatPrimitive_actual_derivative b hb.1 k
        apply (source_sector_graph b hb.1 k).mpr
        have hb' : 0 ≤ (flatten (k.castAdd 3) b).2 := hb.2.le
        simpa only [flatten,sub_nonneg] using hb'
      have hC1 : ContDiffOn ℝ 1 (flatPrimitive k) V := by
        have hc : ContDiffOn ℝ (0 + 1) (flatPrimitive k) V :=
          (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn (n := 0)
            hV.uniqueDiffOn).2
            ⟨by simp,sourceDifferential,
              contDiffOn_zero.mpr
                (sourceDifferential_continuousOn_positive.mono inter_subset_left),
              fun b hb => (hD b hb).hasFDerivWithinAt⟩
        simpa only [zero_add] using hc
      exact ⟨V,⟨ha,hstrict⟩,hV,inter_subset_left,flatPrimitive k,hC1,hD⟩

end CFMPActualEverywhereLocalPrimitive276Transient

run_cmd do
  let env := (← Lean.getEnv).setExporting false
  let name := ``CFMPActualEverywhereLocalPrimitive276Transient.exists_local_angle_primitive
  unless (env.checked.get.find? name).isSome do
    Lean.throwError m!"CFMP276 positive-domain local exactness absent: {name}"
  let axioms ← Lean.collectAxioms name
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      Lean.throwError m!"CFMP276 disallowed axiom {ax}"
  Lean.logInfo m!"CFMP276 CHECKED {name} axioms={axioms}"
