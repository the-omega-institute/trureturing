import D5.S3.Weil.Mertens.IntegratedExplicit.RHPrimeWindowRemainder
import Reg.Support.SingleDependentReadout

/-! Changing the discrepancy on windows with left cutoff two isolates the fixed-cutoff
interval law. Rejection of the full source law entails its Riemann hypothesis premise. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Set
open scoped Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePhaseCluster (phaseOrbit)
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.RHPrimeWindowRemainder

namespace Reg.D5.S3.Weil.Mertens.IntegratedExplicit.RHPrimeWindowRemainder

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ × ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ cuts => windowDiscrepancy cuts.1 cuts.2) (fun e => nomatch e)

def uniformLaw (V : Realization signature) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ X : ℝ, 2 ≤ X ∧ ∀ a B : ℝ, X ≤ a → a ≤ B →
    |V.readout () () (a, B) - spectralPrimitive (phaseOrbit (Real.log B)) +
      spectralPrimitive (phaseOrbit (Real.log a))| < ε

def clusterLaw (V : Realization signature) : Prop :=
  ∀ a : ℝ, 2 ≤ a →
    {y | MapClusterPt y atTop (fun B => V.readout () () (a, B))} =
      (fun h => fixedCutoffConstant a + spectralPrimitive h) '' closure (range phaseOrbit) ∧
    ∃ lower upper : ℝ, lower < upper ∧
      {y | MapClusterPt y atTop (fun B => V.readout () () (a, B))} = Icc lower upper

abbrev arena : Arena where
  signature := signature
  Law V := RiemannHypothesis → uniformLaw V ∧ clusterLaw V

theorem source_bridge : (type_of% @prime_window_remainder_of_rh) ↔ arena.Law actual := Iff.rfl

def atTwoIntervention : Realization signature := by
  classical
  exact realize signature
    (fun _ _ cuts => if cuts.1 = 2 then 0 else windowDiscrepancy cuts.1 cuts.2)
    (fun e => nomatch e)

theorem intervention_preserves_uniform (h : uniformLaw actual) :
    uniformLaw atTwoIntervention := by
  intro ε hε
  obtain ⟨X, hX, hcut⟩ := h ε hε
  refine ⟨max 3 X, hX.trans (le_max_right _ _), fun a B ha hB => ?_⟩
  have ha_ne : a ≠ 2 := by linarith [(le_max_left 3 X).trans ha]
  simpa [atTwoIntervention, realize, actual, ha_ne] using
    hcut a B ((le_max_right 3 X).trans ha) hB

theorem intervention_rejects_cluster : ¬ clusterLaw atTwoIntervention := by
  intro h
  obtain ⟨lower, upper, hlt, heq⟩ := (h 2 le_rfl).2
  have hzero (x : ℝ) (hx : x ∈ Icc lower upper) : x = 0 := by
    have hcluster : MapClusterPt x atTop (fun B => atTwoIntervention.readout () () (2, B)) :=
      (heq ▸ hx :)
    have hconstant : MapClusterPt x atTop (fun _ : ℝ => (0 : ℝ)) := by
      simpa [atTwoIntervention, realize] using hcluster
    exact isClosed_singleton.mem_of_mapClusterPt hconstant (Eventually.of_forall fun _ => rfl)
  have hlow := hzero lower ⟨le_rfl, hlt.le⟩
  have hupp := hzero upper ⟨hlt.le, le_rfl⟩
  linarith

theorem rejected_law_implies_rh (V : Realization signature) (h : ¬ arena.Law V) :
    RiemannHypothesis := by
  by_contra hRH
  exact h (fun hrh => (hRH hrh).elim)

theorem sensitivity_iff_rh : Sensitivity arena actual ↔ RiemannHypothesis := by
  constructor
  · intro h
    obtain ⟨bad, _, _, hbad⟩ := h.1 ()
    exact rejected_law_implies_rh bad hbad
  · intro hRH
    exact _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual atTwoIntervention
      (fun h => intervention_rejects_cluster (h hRH).2)

end Reg.D5.S3.Weil.Mertens.IntegratedExplicit.RHPrimeWindowRemainder
