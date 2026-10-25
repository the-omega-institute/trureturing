import CFMPActualZeroAngle288Transient
import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Analysis.Convex.Topology

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology ContDiff NNReal
open CFMPOriginalCovolumeNeighborhood251Transient (Lengths)
open CFMPOriginalCovolumeC1253Transient (sourceDifferential)
open CFMPActualExtendedAngle268Transient (positiveLengths positiveLengths_open)
open CFMPActualPositivePrimitive279Transient (positiveLengths_convex)
open CFMPActualFlatVolume286Transient (referenceCovolume)
open CFMPActualNormalizedFlat287Transient (actual_zero_flat_C1_convex_extension)
open CFMPActualZeroAngle288Transient (sourceDifferential_continuous sourceDifferential_norm_le)
open CFMPGenuineLengthNeighborhood435Transient (genuine)

namespace CFMPActualClosedOrthant289Transient

def nonnegativeLengths : Set Lengths := {a | ∀ q, 0 ≤ a q}

theorem closure_positiveLengths : closure positiveLengths = nonnegativeLengths := by
  have hp : positiveLengths = Set.univ.pi (fun _ : Fin 6 => Ioi (0 : ℝ)) := by
    ext a
    simp [positiveLengths,Set.mem_pi]
  rw [hp,closure_pi_set]
  ext a
  simp [nonnegativeLengths,Set.mem_pi,closure_Ioi,Pi.le_def]

theorem nonnegativeLengths_convex : Convex ℝ nonnegativeLengths := by
  rw [← closure_positiveLengths]
  exact positiveLengths_convex.closure

/-- Continuous inequalities extend from pairs of interior points to pairs in the closure. -/
theorem convexOn_closure_of_continuous
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Set E} {g : E → ℝ} (hc : Continuous g) (hg : ConvexOn ℝ s g) :
    ConvexOn ℝ (closure s) g := by
  refine ⟨hg.1.closure,?_⟩
  intro x hx y hy c d hc0 hd0 hcd
  let T : Set (E × E) :=
    {p | g (c • p.1 + d • p.2) ≤ c • g p.1 + d • g p.2}
  have hT : IsClosed T := by
    apply isClosed_le
    · exact hc.comp ((continuous_fst.const_smul c).add (continuous_snd.const_smul d))
    · exact ((hc.comp continuous_fst).const_smul c).add
        ((hc.comp continuous_snd).const_smul d)
  have hsub : s ×ˢ s ⊆ T := fun p hp => hg.2 hp.1 hp.2 hc0 hd0 hcd
  have hcl : closure (s ×ˢ s) ⊆ T := closure_minimal hsub hT
  rw [closure_prod_eq] at hcl
  exact hcl (show (x,y) ∈ closure s ×ˢ closure s from ⟨hx,hy⟩)

/-- The extension is unique on the nonnegative cone, even though its values
outside that cone need not be unique. -/
theorem continuous_extension_unique
    (g h : Lengths → ℝ) (hg : Continuous g) (hh : Continuous h)
    (heq : Set.EqOn g h positiveLengths) : Set.EqOn g h nonnegativeLengths := by
  rw [← closure_positiveLengths]
  exact heq.closure hg hh

/-- A genuine basepoint calibrates the original positive covolume. Its bounded
angle gradient gives a continuous extension with the same boundary covector. -/
theorem exists_actual_closed_orthant_extension (a0 : Lengths) (ha0 : genuine a0) :
    ∃ g : Lengths → ℝ,
      LipschitzWith ⟨6*Real.pi,by positivity⟩ g ∧
      Set.EqOn g referenceCovolume positiveLengths ∧
      ConvexOn ℝ nonnegativeLengths g ∧
      ∀ a ∈ nonnegativeLengths,
        HasFDerivWithinAt g (sourceDifferential a) nonnegativeLengths a := by
  have hF := actual_zero_flat_C1_convex_extension a0 ha0
  have hLip : LipschitzOnWith ⟨6*Real.pi,by positivity⟩ referenceCovolume positiveLengths := by
    apply positiveLengths_convex.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
      (fun a ha => (hF.2.2.1 a ha).hasFDerivWithinAt)
    intro a _
    exact show ‖sourceDifferential a‖₊ ≤ (⟨6*Real.pi,by positivity⟩ : ℝ≥0) from
      sourceDifferential_norm_le a
  obtain ⟨g,hg,hFg⟩ := hLip.extend_real
  have heq : Set.EqOn g referenceCovolume positiveLengths := fun a ha => (hFg ha).symm
  have hd (a : Lengths) (ha : a ∈ positiveLengths) :
      HasFDerivAt g (sourceDifferential a) a := by
    apply (hF.2.2.1 a ha).congr_of_eventuallyEq
    filter_upwards [positiveLengths_open.mem_nhds ha] with b hb
    exact heq hb
  have hgc : ConvexOn ℝ positiveLengths g := hF.2.1.congr (fun a ha => (heq ha).symm)
  refine ⟨g,hg,heq,?_,?_⟩
  · rw [← closure_positiveLengths]
    exact convexOn_closure_of_continuous hg.continuous hgc
  · intro a _
    rw [← closure_positiveLengths]
    apply hasFDerivWithinAt_closure_of_tendsto_fderiv
      (fun b hb => (hd b hb).differentiableAt.differentiableWithinAt)
      positiveLengths_convex positiveLengths_open
      (fun b _ => hg.continuous.continuousAt.continuousWithinAt)
    have hEq : Set.EqOn (fderiv ℝ g) sourceDifferential positiveLengths :=
      fun b hb => (hd b hb).fderiv
    exact (tendsto_congr' hEq.eventuallyEq_nhdsWithin).2
      (sourceDifferential_continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)

end CFMPActualClosedOrthant289Transient

run_cmd do
  let env := (← Lean.getEnv).setExporting false
  for name in [``CFMPActualClosedOrthant289Transient.closure_positiveLengths,
      ``CFMPActualClosedOrthant289Transient.continuous_extension_unique,
      ``CFMPActualClosedOrthant289Transient.exists_actual_closed_orthant_extension] do
    unless (env.checked.get.find? name).isSome do
      Lean.throwError m!"CFMP289 actual closed-orthant extension absent: {name}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        Lean.throwError m!"CFMP289 disallowed axiom {ax}"
    Lean.logInfo m!"CFMP289 CHECKED {name} axioms={axioms}"
