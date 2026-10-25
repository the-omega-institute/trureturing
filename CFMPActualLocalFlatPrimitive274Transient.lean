import CFMPActualResidualPullback273Transient
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Analysis.Normed.Module.RCLike.Real

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter Metric
open scoped Topology ContDiff
open CFMPActualFlatGraph269Transient (lengthThreshold)
open CFMPActualFlatCoordinates271Transient
open CFMPActualFlatNeighborhood272Transient
open CFMPActualResidualPullback273Transient
open CFMPGenuineLengthNeighborhood435Transient (genuine)

namespace CFMPActualLocalFlatPrimitive274Transient

/-- Every positive point of the original flat graph has a local C1 primitive
for the actual residual pullback. All convex-side and boundedness hypotheses
of the gluing construction are discharged from the original angle formulas. -/
theorem exists_actual_local_residual_primitive (k : Fin 3) (u : Fin 5 → ℝ)
    (hu : ∀ j, 0 < u j) :
    ∃ r : ℝ, 0 < r ∧ ∃ F : Chart → ℝ,
      ContDiffOn ℝ 1 F (ball u r ×ˢ Ioo (-r) r) ∧
      (∀ p ∈ ball u r ×ˢ Ioo (-r) r, HasFDerivAt F (residual k p) p) ∧
      Set.EqOn F 0 (closedBall u r ×ˢ Icc 0 r) ∧
      (∀ p ∈ closedBall u r ×ˢ Icc (-r) r,
        p ∈ basePositive ∧ 0 < p.2 + lengthThreshold p.1 ∧
        (genuine (unflatten (k.castAdd 3) p) ↔ p.2 < 0)) := by
  let p0 : Chart := (u,0)
  let a0 := unflatten (k.castAdd 3) p0
  have hh0 : 0 < p0.2 + lengthThreshold p0.1 := by
    simpa only [p0, zero_add] using CFMPActualFlatGraph269Transient.lengthThreshold_pos u hu
  have ha0 : ∀ j, 0 < a0 j := unflatten_positive _ p0 hu hh0
  have hk0 : D5.S3.Geometry.Hyperideal.PositiveFlatClassification.Sector
      (fun q => Real.cosh (a0 q)) k :=
    (native_sector_iff_nonneg k p0 hu hh0).mpr (le_refl 0)
  have hgen : ∀ᶠ p in 𝓝 p0,
      genuine (unflatten (k.castAdd 3) p) ↔ p.2 < 0 := by
    simpa only [a0, flatten_unflatten] using chart_genuine_eventually a0 ha0 k hk0
  have hthreshold : ContinuousAt (fun p : Chart => lengthThreshold p.1) p0 := by
    convert! ((CFMPActualFlatGraph269Transient.lengthThreshold_contDiffAt u hu).continuousAt.comp
      (show ContinuousAt (fun p : Chart => p.1) p0 from continuousAt_fst)) using 1
  have hheight : ContinuousAt (fun p : Chart => p.2 + lengthThreshold p.1) p0 :=
    continuousAt_snd.add hthreshold
  have hvalid : ∀ᶠ p in 𝓝 p0,
      p ∈ basePositive ∧ 0 < p.2 + lengthThreshold p.1 ∧
      (genuine (unflatten (k.castAdd 3) p) ↔ p.2 < 0) := by
    filter_upwards [basePositive_open.mem_nhds (show p0 ∈ basePositive from hu),
      hheight.eventually (Ioi_mem_nhds hh0), hgen] with p hp hh hg
    exact ⟨hp,hh,hg⟩
  obtain ⟨r,hr,hvalid⟩ := (Metric.nhds_basis_closedBall (x := p0)).mem_iff.mp hvalid
  let s : Set Chart := ball u r ×ˢ Ioo (-r) 0
  let t : Set Chart := closedBall u r ×ˢ Icc 0 r
  let U : Set Chart := ball u r ×ˢ Ioo (-r) r
  let K : Set Chart := closedBall p0 r
  have hKprod : K = closedBall u r ×ˢ Icc (-r) r := by
    simp only [K,p0,← closedBall_prod_same,Real.closedBall_eq_Icc,zero_sub,zero_add]
  have hclosure : closure s = closedBall u r ×ˢ Icc (-r) 0 := by
    rw [show s = ball u r ×ˢ Ioo (-r) 0 from rfl,closure_prod_eq,
      closure_ball u hr.ne',closure_Ioo (by linarith : -r ≠ (0 : ℝ))]
  have hSTK : closure s ∪ t ⊆ K := by
    intro p hp
    rw [hKprod]
    rcases hp with hp | hp
    · rw [hclosure] at hp
      exact ⟨hp.1,hp.2.1,hp.2.2.trans hr.le⟩
    · exact ⟨hp.1,(neg_nonpos.mpr hr.le).trans hp.2.1,hp.2.2⟩
  have hsK : s ⊆ K := fun p hp => hSTK (Or.inl (subset_closure hp))
  have hcont : ContinuousOn (residual k) K := by
    intro p hp
    exact (residual_continuousAt k p (hvalid hp).1 (hvalid hp).2.1).continuousWithinAt
  obtain ⟨C,hC⟩ := (isCompact_closedBall p0 r).bddAbove_image hcont.nnnorm
  have hbound : ∀ p ∈ s, ‖residual k p‖₊ ≤ C := by
    intro p hp
    exact hC (mem_image_of_mem (fun p => ‖residual k p‖₊) (hsK hp))
  have hs : Convex ℝ s := (convex_ball u r).prod (convex_Ioo (-r) 0)
  have hso : IsOpen s := isOpen_ball.prod isOpen_Ioo
  have ht : Convex ℝ t := (convex_closedBall u r).prod (convex_Icc 0 r)
  have htc : IsClosed t := isClosed_closedBall.prod isClosed_Icc
  have hcontact : (closure s ∩ t).Nonempty := by
    refine ⟨p0,?_,?_⟩
    · rw [hclosure]
      exact ⟨mem_closedBall_self hr.le,by dsimp [p0]; constructor <;> linarith⟩
    · exact ⟨mem_closedBall_self hr.le,le_refl 0,hr.le⟩
  have hU : IsOpen U := isOpen_ball.prod isOpen_Ioo
  have hcover : U ⊆ closure s ∪ t := by
    intro p hp
    by_cases hh : p.2 ≤ 0
    · left
      rw [hclosure]
      exact ⟨ball_subset_closedBall hp.1,hp.2.1.le,hh⟩
    · right
      exact ⟨ball_subset_closedBall hp.1,(lt_of_not_ge hh).le,hp.2.2.le⟩
  have hder : ∀ p ∈ s,
      HasFDerivAt (residual k) (fderiv ℝ (residual k) p) p := by
    intro p hp
    have hv := hvalid (hsK hp)
    exact residual_hasFDerivAt_genuine k p hv.1 (hv.2.2.mpr hp.2.2)
  have hsym : ∀ p ∈ s, ∀ v w : Chart,
      fderiv ℝ (residual k) p v w = fderiv ℝ (residual k) p w v := by
    intro p hp v w
    have hv := hvalid (hsK hp)
    exact residual_derivative_symmetric k p hv.1 (hv.2.2.mpr hp.2.2) v w
  have hzero : ∀ p ∈ t, residual k p = 0 := by
    intro p hp
    have hv := hvalid (hSTK (Or.inr hp))
    exact residual_zero_nonneg k p hv.1 hv.2.1 hp.2.1
  obtain ⟨F,hF,hD,hZ⟩ :=
    CFMPConvexFlatPrimitive270Transient.exists_primitive_across_flat_side
      s t U hs hso ht htc hcontact hU hcover (residual k)
      (fderiv ℝ (residual k)) (hcont.mono hSTK) hder hsym C hbound hzero
  refine ⟨r,hr,F,hF,hD,hZ,?_⟩
  intro p hp
  exact hvalid (by change p ∈ K; rwa [hKprod])

end CFMPActualLocalFlatPrimitive274Transient

run_cmd do
  let env := (← Lean.getEnv).setExporting false
  let name := ``CFMPActualLocalFlatPrimitive274Transient.exists_actual_local_residual_primitive
  unless (env.checked.get.find? name).isSome do
    Lean.throwError m!"CFMP274 actual local flat residual primitive absent: {name}"
  let axioms ← Lean.collectAxioms name
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      Lean.throwError m!"CFMP274 disallowed axiom {ax}"
  Lean.logInfo m!"CFMP274 CHECKED {name} axioms={axioms}"
