import CFMPGenuineCovolumeC1254Transient
import CFMPOriginalVolumeChoice255Transient
import Mathlib.Analysis.Calculus.FDeriv.Congr

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Matrix BigOperators Topology ContDiff ENNReal
open D5.S3.Geometry.Hyperideal.LengthGramBody
open D5.S3.Geometry.HyperbolicUpperHalfSpace
open CFMPAnchoredSmoothFrame435Transient
open CFMPOriginalCovolumeNeighborhood251Transient
open CFMPOriginalCovolumeC1253Transient
open CFMPGenuineCovolumeC1254Transient
open CFMPOriginalVolumeChoice255Transient

namespace CFMPGlobalGenuineCovolume256Transient

def realizedFamily (G : RealizationFamily) : Prop :=
  ∀ a, CFMPGenuineLengthNeighborhood435Transient.genuine a →
    ∃ M : Matrix (Fin 4) (Fin 4) ℝ,
      (∀ i j, lorentz (M i) (M j) = lengthGram a i j) ∧
      Function.Injective (G a) ∧ originalContract a M (G a)

def chosenFrame (a : Lengths) (ha : CFMPGenuineLengthNeighborhood435Transient.genuine a) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  Classical.choose (CFMPGenuineLengthNeighborhood435Transient.genuine_realization_exists a ha)

def chosenRealization (a : Lengths) (ha : CFMPGenuineLengthNeighborhood435Transient.genuine a) :
    cutBody a → HyperbolicThreeSpace :=
  Classical.choose (Classical.choose_spec
    (CFMPGenuineLengthNeighborhood435Transient.genuine_realization_exists a ha))

def origin : HyperbolicThreeSpace :=
  ⟨⟨WithLp.toLp 2 ((0 : ℂ),(1 : ℝ)),by norm_num⟩⟩

def wholeFamily : RealizationFamily := by
  classical
  exact fun a =>
    if ha : CFMPGenuineLengthNeighborhood435Transient.genuine a then chosenRealization a ha
    else fun _ => origin

theorem wholeFamily_realized : realizedFamily wholeFamily := by
  classical
  intro a ha
  have h := Classical.choose_spec (Classical.choose_spec
    (CFMPGenuineLengthNeighborhood435Transient.genuine_realization_exists a ha))
  have hchoice : wholeFamily a = chosenRealization a ha := by
    dsimp only [wholeFamily]
    rw [dif_pos ha]
  refine ⟨chosenFrame a ha,?_,?_,?_⟩
  · exact h.1
  · rw [hchoice]
    exact h.2.2.1
  · rw [hchoice]
    exact h.2.2.2.2

theorem physicalCovolume_choice_independent
    (F G : RealizationFamily) (hF : realizedFamily F) (hG : realizedFamily G)
    (a : Lengths) (ha : CFMPGenuineLengthNeighborhood435Transient.genuine a) :
    physicalCovolume F a = physicalCovolume G a := by
  obtain ⟨M,hM,hFi,hFc⟩ := hF a ha
  obtain ⟨N,hN,_,hGc⟩ := hG a ha
  exact physicalCovolume_eq_of_original_realizations a M N hM hN F G hFi hFc hGc

theorem physicalCovolume_contDiffOn_genuine
    (G : RealizationFamily) (hG : realizedFamily G) :
    ContDiffOn ℝ 1 (physicalCovolume G)
      {a | CFMPGenuineLengthNeighborhood435Transient.genuine a} ∧
      ∀ a, CFMPGenuineLengthNeighborhood435Transient.genuine a →
        HasFDerivAt (physicalCovolume G) (sourceDifferential a) a := by
  have hd (a : Lengths) (ha : CFMPGenuineLengthNeighborhood435Transient.genuine a) :
      HasFDerivAt (physicalCovolume G) (sourceDifferential a) a := by
    obtain ⟨M,U,H,_,h0,hU,hgenU,_,_,hgeom,_,hD⟩ :=
      exists_genuine_physical_covolume_C1 a ha
    have heq : physicalCovolume G =ᶠ[𝓝 a] physicalCovolume H := by
      filter_upwards [hU.mem_nhds h0] with b hb
      obtain ⟨N,hN,hGi,hGc⟩ := hG b (hgenU b hb)
      have hH := hgeom b hb
      exact physicalCovolume_eq_of_original_realizations b N (frame M b)
        hN hH.2.2.1 G H hGi hGc hH.2.2.2.2.2.2
    exact (hD a h0).congr_of_eventuallyEq heq
  refine ⟨?_,hd⟩
  have hc : ContDiffOn ℝ (0 + 1) (physicalCovolume G)
      {a | CFMPGenuineLengthNeighborhood435Transient.genuine a} :=
    (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn (n := 0)
      CFMPGenuineLengthNeighborhood435Transient.genuine_open.uniqueDiffOn).2
      ⟨by simp,sourceDifferential,
        contDiffOn_zero.mpr (sourceDifferential_continuousOn _ (fun _ ha => ha)),
        fun a ha => (hd a ha).hasFDerivWithinAt⟩
  simpa only [zero_add] using hc

theorem exists_actual_physical_covolume_C1 :
    ∃ G : RealizationFamily, realizedFamily G ∧
      ContDiffOn ℝ 1 (physicalCovolume G)
        {a | CFMPGenuineLengthNeighborhood435Transient.genuine a} ∧
      (∀ a, CFMPGenuineLengthNeighborhood435Transient.genuine a →
        HasFDerivAt (physicalCovolume G) (sourceDifferential a) a) ∧
      (∀ F : RealizationFamily, realizedFamily F →
        ∀ a, CFMPGenuineLengthNeighborhood435Transient.genuine a →
          physicalCovolume F a = physicalCovolume G a) := by
  have h := physicalCovolume_contDiffOn_genuine wholeFamily wholeFamily_realized
  exact ⟨wholeFamily,wholeFamily_realized,h.1,h.2,
    fun F hF a ha => physicalCovolume_choice_independent F wholeFamily
      hF wholeFamily_realized a ha⟩

end CFMPGlobalGenuineCovolume256Transient

run_cmd do
  let env := (← Lean.getEnv).setExporting false
  for name in [``CFMPGlobalGenuineCovolume256Transient.physicalCovolume_choice_independent,
      ``CFMPGlobalGenuineCovolume256Transient.physicalCovolume_contDiffOn_genuine,
      ``CFMPGlobalGenuineCovolume256Transient.exists_actual_physical_covolume_C1] do
    unless (env.checked.get.find? name).isSome do
      Lean.throwError m!"CFMP256 actual physical source theorem absent from checked environment: {name}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        Lean.throwError m!"CFMP256 disallowed axiom {ax}"
    Lean.logInfo m!"CFMP256 CHECKED {name} axioms={axioms}"
