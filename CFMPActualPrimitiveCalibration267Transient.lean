import CFMPFourCyclePhysicalUnique266Transient
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Function

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped BigOperators Topology ContDiff
open CFMPGenuineLengthNeighborhood435Transient (genuine genuine_open)
open CFMPOriginalCovolumeNeighborhood251Transient
open CFMPOriginalCovolumeC1253Transient (sourceDifferential)
open CFMPGlobalGenuineCovolume256Transient

namespace CFMPActualPrimitiveCalibration267Transient

def normalizedPrimitive (F : Lengths → ℝ) (a0 a : Lengths) : ℝ :=
  F a + (physicalCovolume wholeFamily a0 - F a0)

theorem normalized_primitive_matches_actual
    (F : Lengths → ℝ)
    (hprimitive : ∀ a : Lengths, genuine a → HasFDerivAt F (sourceDifferential a) a)
    (a0 : Lengths) (ha0 : genuine a0)
    (G : RealizationFamily) (hG : realizedFamily G) :
    Set.EqOn (normalizedPrimitive F a0) (physicalCovolume G) {a | genuine a} := by
  letI : ConnectedSpace CFMPGenuineConnected146.GenuineLengths :=
    CFMPGenuineConnected146.connected148
  have hconn : IsPreconnected {a : Lengths | genuine a} := by
    have hpre : PreconnectedSpace CFMPGenuineConnected146.GenuineLengths := inferInstance
    convert! (isPreconnected_iff_preconnectedSpace.mpr hpre) using 1
  have hn (a : Lengths) (ha : genuine a) :
      HasFDerivAt (normalizedPrimitive F a0) (sourceDifferential a) a :=
    (hprimitive a ha).add_const (physicalCovolume wholeFamily a0 - F a0)
  have hg := (physicalCovolume_contDiffOn_genuine G hG).2
  apply genuine_open.eqOn_of_fderiv_eq hconn
    (fun a ha => (hn a ha).differentiableAt.differentiableWithinAt)
    (fun a ha => (hg a ha).differentiableAt.differentiableWithinAt)
    (fun a ha => (hn a ha).fderiv.trans (hg a ha).fderiv.symm) ha0
  unfold normalizedPrimitive
  rw [physicalCovolume_choice_independent wholeFamily G wholeFamily_realized hG a0 ha0]
  ring

theorem calibrated_C1_convex_extension
    (F : Lengths → ℝ)
    (hprimitive : ∀ a : Lengths, genuine a → HasFDerivAt F (sourceDifferential a) a)
    (hC1 : ContDiff ℝ 1 F) (hconvex : ConvexOn ℝ Set.univ F)
    (a0 : Lengths) (ha0 : genuine a0) :
    ContDiff ℝ 1 (normalizedPrimitive F a0) ∧
      ConvexOn ℝ Set.univ (normalizedPrimitive F a0) ∧
      ∀ G : RealizationFamily, realizedFamily G →
        Set.EqOn (normalizedPrimitive F a0) (physicalCovolume G) {a | genuine a} := by
  refine ⟨hC1.add contDiff_const,
    hconvex.add_const (physicalCovolume wholeFamily a0 - F a0),?_⟩
  intro G hG
  exact normalized_primitive_matches_actual F hprimitive a0 ha0 G hG

end CFMPActualPrimitiveCalibration267Transient

run_cmd do
  let env := (← Lean.getEnv).setExporting false
  for name in [``CFMPActualPrimitiveCalibration267Transient.normalized_primitive_matches_actual,
      ``CFMPActualPrimitiveCalibration267Transient.calibrated_C1_convex_extension] do
    unless (env.checked.get.find? name).isSome do
      Lean.throwError m!"CFMP267 physical primitive calibration absent from checked environment: {name}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        Lean.throwError m!"CFMP267 disallowed axiom {ax}"
    Lean.logInfo m!"CFMP267 CHECKED {name} axioms={axioms}"
