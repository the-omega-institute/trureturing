import CFMPActualLocalFlatPrimitive274Transient

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter Metric
open scoped Topology ContDiff
open CFMPOriginalCovolumeNeighborhood251Transient (Lengths)
open CFMPOriginalCovolumeC1253Transient (sourceDifferential)
open CFMPActualExtendedAngle268Transient
open CFMPActualFlatCoordinates271Transient
open CFMPActualResidualPullback273Transient (residual basePositive)
open CFMPActualLocalFlatPrimitive274Transient

namespace CFMPActualLocalAnglePrimitive275Transient

/-- A local primitive of the original six-angle covector in original length
coordinates around each positive point of a native flat graph. On that
sector it agrees with the original flat affine covolume expression. -/
theorem exists_original_local_angle_primitive (k : Fin 3) (u : Fin 5 → ℝ)
    (hu : ∀ j, 0 < u j) :
    ∃ V : Set Lengths,
      unflatten (k.castAdd 3) (u,0) ∈ V ∧ IsOpen V ∧
      (∀ a ∈ V, a ∈ positiveLengths) ∧ ∃ H : Lengths → ℝ,
      ContDiffOn ℝ 1 H V ∧
      (∀ a ∈ V, HasFDerivAt H (sourceDifferential a) a) ∧
      (∀ a ∈ V,
        D5.S3.Geometry.Hyperideal.PositiveFlatClassification.Sector
          (fun q => Real.cosh (a q)) k → H a = flatPrimitive k a) := by
  obtain ⟨r,hr,F,hF,hD,hZ,hvalid⟩ := exists_actual_local_residual_primitive k u hu
  let U : Set Chart := ball u r ×ˢ Ioo (-r) r
  let V : Set Lengths := positiveLengths ∩ (flatten (k.castAdd 3)) ⁻¹' U
  let H : Lengths → ℝ := fun a => F (flatten (k.castAdd 3) a) + flatPrimitive k a
  have hU : IsOpen U := isOpen_ball.prod isOpen_Ioo
  have hV : IsOpen V := by
    apply isOpen_iff_mem_nhds.mpr
    intro a ha
    have hc := (flatten_contDiffAt (k.castAdd 3) a ha.1).continuousAt
    exact inter_mem (positiveLengths_open.mem_nhds ha.1) (hc.eventually (hU.mem_nhds ha.2))
  have hV0 : unflatten (k.castAdd 3) (u,0) ∈ V := by
    refine ⟨unflatten_positive _ (u,0) hu ?_,?_⟩
    · simpa only [zero_add] using CFMPActualFlatGraph269Transient.lengthThreshold_pos u hu
    · change flatten (k.castAdd 3) (unflatten (k.castAdd 3) (u,0)) ∈ U
      rw [flatten_unflatten]
      exact ⟨mem_ball_self hr,by constructor <;> linarith⟩
  have hfull (a : Lengths) (ha : a ∈ V) : HasFDerivAt H (sourceDifferential a) a := by
    have hψ := (flatten_contDiffAt (k.castAdd 3) a ha.1).differentiableAt (by simp)
    have hp : (flatten (k.castAdd 3) a) ∈ basePositive := by
      intro j
      fin_cases j <;> exact ha.1 _
    have hφ := (unflatten_contDiffAt (k.castAdd 3)
      (flatten (k.castAdd 3) a) hp).differentiableAt (by simp)
    have hid := hφ.hasFDerivAt.comp a hψ.hasFDerivAt
    have heq : (fun b : Lengths => unflatten (k.castAdd 3) (flatten (k.castAdd 3) b)) =
        (fun b : Lengths => b) := funext (unflatten_flatten (k.castAdd 3))
    simp only [Function.comp_def] at hid
    rw [heq] at hid
    have hlinear := hid.unique (hasFDerivAt_id a)
    have hidv (v : Lengths) :
        fderiv ℝ (unflatten (k.castAdd 3)) (flatten (k.castAdd 3) a)
          (fderiv ℝ (flatten (k.castAdd 3)) a v) = v := by
      simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply] using
        congrArg (fun L : Lengths →L[ℝ] Lengths => L v) hlinear
    have hd := ((hD (flatten (k.castAdd 3) a) ha.2).comp a hψ.hasFDerivAt).add
      (flatPrimitive_hasFDerivAt k a)
    apply hd.congr_fderiv
    ext v
    change (sourceDifferential (unflatten (k.castAdd 3) (flatten (k.castAdd 3) a)) -
      flatDifferential k)
      (fderiv ℝ (unflatten (k.castAdd 3)) (flatten (k.castAdd 3) a)
        (fderiv ℝ (flatten (k.castAdd 3)) a v)) + flatDifferential k v =
      sourceDifferential a v
    rw [unflatten_flatten,hidv]
    simp only [ContinuousLinearMap.sub_apply,sub_add_cancel]
  have hHC1 : ContDiffOn ℝ 1 H V := by
    have hc : ContDiffOn ℝ (0 + 1) H V :=
      (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn (n := 0) hV.uniqueDiffOn).2
        ⟨by simp,sourceDifferential,
          contDiffOn_zero.mpr (sourceDifferential_continuousOn_positive.mono inter_subset_left),
          fun a ha => (hfull a ha).hasFDerivWithinAt⟩
    simpa only [zero_add] using hc
  refine ⟨V,hV0,hV,(fun _ ha => ha.1),H,hHC1,hfull,?_⟩
  intro a ha hk
  have hnonneg : 0 ≤ (flatten (k.castAdd 3) a).2 := by
    simpa only [flatten,sub_nonneg] using
      (CFMPActualFlatGraph269Transient.source_sector_graph a ha.1 k).mp hk
  have hupper : flatten (k.castAdd 3) a ∈ closedBall u r ×ˢ Icc 0 r :=
    ⟨ball_subset_closedBall ha.2.1,hnonneg,ha.2.2.2.le⟩
  change F (flatten (k.castAdd 3) a) + flatPrimitive k a = flatPrimitive k a
  simp only [hZ hupper,Pi.zero_apply,zero_add]

end CFMPActualLocalAnglePrimitive275Transient

run_cmd do
  let env := (← Lean.getEnv).setExporting false
  let name := ``CFMPActualLocalAnglePrimitive275Transient.exists_original_local_angle_primitive
  unless (env.checked.get.find? name).isSome do
    Lean.throwError m!"CFMP275 original-coordinate local angle primitive absent: {name}"
  let axioms ← Lean.collectAxioms name
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      Lean.throwError m!"CFMP275 disallowed axiom {ax}"
  Lean.logInfo m!"CFMP275 CHECKED {name} axioms={axioms}"
