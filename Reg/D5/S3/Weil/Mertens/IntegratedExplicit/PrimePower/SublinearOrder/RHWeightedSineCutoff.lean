import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.RHWeightedSineCutoff
import Reg.Support.DependentFamily

/-! The exact conditional source law with the weighted sine value as its observation. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Set
open scoped Topology

namespace Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.RHWeightedSineCutoff

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder
  (harmonicMass weightedSine)
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.RHWeightedSineCutoff

abbrev signature : Signature where
  Params := PLift RiemannHypothesis × ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p v => weightedSine p.1.down p.2 v) (fun e => nomatch e)

private def zeroSine : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ (hRH : RiemannHypothesis) (_ : EffectiveLI hRH) {r β ε : ℝ},
    0 < r → 0 < β → 2 * (1 - (min β 1)^2) < ε →
    ∀ᶠ T : ℝ in atTop, 0 < harmonicMass hRH T ∧
      ∀ a : ℝ, ∃ u ∈ Icc a (a + Real.exp (T ^ β)),
        1 - V.readout () (⟨hRH⟩, T) (u / r) / harmonicMass hRH T < ε

theorem source_bridge :
    (type_of% @eventual_weighted_sine_cutoff_tradeoff) ↔ arena.Law actual :=
  Iff.rfl

private theorem actual_law : arena.Law actual :=
  source_bridge.mp @eventual_weighted_sine_cutoff_tradeoff

/-- Rejection of the complete law requires a witness for both source hypotheses. -/
theorem rejection_requires_eli (V : Realization signature) (h : ¬ arena.Law V) :
    ∃ hRH : RiemannHypothesis, EffectiveLI hRH := by
  classical
  by_contra! hnone
  exact h (fun hRH hELI => (hnone hRH hELI).elim)

private theorem half_loss (V : Realization signature) (h : arena.Law V)
    (hRH : RiemannHypothesis) (hELI : EffectiveLI hRH) :
    ∃ T u : ℝ, 0 < harmonicMass hRH T ∧
      1 - V.readout () (⟨hRH⟩, T) u / harmonicMass hRH T < 1 / 2 := by
  have he := h hRH hELI (r := 1) (β := 1) (ε := 1 / 2)
    (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨T, hT, hwindow⟩ := he.exists
  obtain ⟨u, _, hu⟩ := hwindow 0
  exact ⟨T, u, hT, by simpa only [div_one] using hu⟩

private theorem zero_sine_rejected (hRH : RiemannHypothesis) (hELI : EffectiveLI hRH) :
    ¬ arena.Law zeroSine := by
  intro h
  obtain ⟨_, _, _, hu⟩ := half_loss zeroSine h hRH hELI
  norm_num [zeroSine, realize] at hu

private theorem actual_dependence (hRH : RiemannHypothesis) (hELI : EffectiveLI hRH) :
    ObservationalDependence signature actual := by
  rintro ⟨⟩
  obtain ⟨T, u, hT, hu⟩ := half_loss actual actual_law hRH hELI
  have hpos : 0 < weightedSine hRH T u := by
    change 1 - weightedSine hRH T u / harmonicMass hRH T < 1 / 2 at hu
    exact pos_of_div_pos_left (by linarith only [hu]) hT.le
  refine ⟨(⟨hRH⟩, T), u, 0, ?_⟩
  change weightedSine hRH T u ≠ weightedSine hRH T 0
  simpa [weightedSine] using hpos.ne'

/-- The kernel-side registration exists exactly when the source hypotheses are inhabited. -/
theorem registration_iff_eli :
    Nonempty (Registration arena (type_of% @eventual_weighted_sine_cutoff_tradeoff)) ↔
      ∃ hRH : RiemannHypothesis, EffectiveLI hRH := by
  constructor
  · rintro ⟨reg⟩
    obtain ⟨V, hV⟩ := reg.variation.2
    exact rejection_requires_eli V hV
  · rintro ⟨hRH, hELI⟩
    have hbad := zero_sine_rejected hRH hELI
    refine ⟨{
      actual := actual
      bridge := source_bridge
      variation := ⟨actual_law, zeroSine, hbad⟩
      sensitivity := ⟨?_, fun e => nomatch e⟩
      dependence := actual_dependence hRH hELI
    }⟩
    intro i
    refine ⟨zeroSine, ?_, ?_, hbad⟩
    · intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · funext e
      exact nomatch e

end Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.RHWeightedSineCutoff
