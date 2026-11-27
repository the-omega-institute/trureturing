import D5.S3.Combinatorics.Graph.Chordal.ChordalBanachSharpFour

import D5.S3.Combinatorics.Graph.Chordal.UniformGainPotential
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

/-! Strict obstruction thresholds obtained from the sharp chordal lower bound. -/

namespace Reg.D5.S3.Combinatorics.Graph.Chordal.ChordalBanachSharpFour

open SimpleGraph LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Reg.Support

noncomputable section

private theorem upper_four_additive {V E : Type} [Fintype V] [NormedAddCommGroup E]
    {G : SimpleGraph V} (hc : G.IsChordal) (g : V → V → E)
    (hg : ∀ u v, g v u = -g u v)
    (hflat : ∀ u v z, G.Adj u v → G.Adj v z → G.Adj u z →
      ‖g u v + g v z - g u z‖ ≤ 1) :
    ∃ φ : V → E, ∀ u v, G.Adj u v → ‖g u v - (φ v - φ u)‖ ≤ 4 := by
  let gain (u v : V) : Multiplicative E := Multiplicative.ofAdd (g u v)
  have hrev (u v : V) (_ : G.Adj u v) : gain v u = (gain u v)⁻¹ := hg u v
  have htri (u v z : V) (huv : G.Adj u v) (hvz : G.Adj v z) (huz : G.Adj u z) :
      Dist.dist (gain u v * gain v z) (gain u z) ≤ 1 := by
    change dist (g u v + g v z) (g u z) ≤ 1
    rw [dist_eq_norm]
    exact hflat u v z huv hvz huz
  obtain ⟨φ,hφ⟩ := hc.exists_uniform_approximate_gain_potential gain 1 zero_le_one hrev htri
  refine ⟨fun x => (φ x).toAdd, fun u v huv => ?_⟩
  have h := hφ u v huv
  change dist (g u v) (-((φ u).toAdd) + (φ v).toAdd) ≤ 4 * 1 at h
  rw [dist_eq_norm, mul_one, neg_add_eq_sub] at h
  exact h

private def StrictWitness (R : ℝ) : Prop :=
  ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V), G.IsChordal ∧ G.Connected ∧
    ∃ (E : Type) (N : NormedAddCommGroup E) (S : @NormedSpace ℝ E _ N.toSeminormedAddCommGroup),
      letI := N
      letI := S
      ∃ (_ : CompleteSpace E) (_ : FiniteDimensional ℝ E) (g : V → V → E),
        (∀ u v, g v u = -g u v) ∧
        (∀ u v z, G.Adj u v → G.Adj v z → G.Adj u z → ‖g u v + g v z - g u z‖ ≤ 1) ∧
        ∀ φ : V → E, ∃ u v, G.Adj u v ∧ R < ‖g u v - (φ v - φ u)‖

private theorem strict_of_le (R δ : ℝ) (hδ : 0 < δ) (hR : R < 4 - δ) :
    StrictWitness R := by
  obtain ⟨V, FV, G, hG, hconn, E, norm, space, complete, finite, g, skew, flat, obs⟩ :=
    SimpleGraph.exists_chordal_banach_gain_lower_four δ hδ
  exact ⟨V, FV, G, hG, hconn, E, norm, space, complete, finite, g, skew, flat, fun φ => by
    obtain ⟨u,v,adj,lb⟩ := obs φ
    exact ⟨u,v,adj,hR.trans_le lb⟩⟩

example : StrictWitness 3 := strict_of_le _ (1/2) (by norm_num) (by norm_num)
example : StrictWitness (7/2) := strict_of_le _ (1/4) (by norm_num) (by norm_num)
example : StrictWitness (399/100) := strict_of_le _ (1/200) (by norm_num) (by norm_num)
abbrev signature := SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ ε => 4 - ε) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 5) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law O := ∀ (ε : ℝ), 0 < ε →
    ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V), G.IsChordal ∧ G.Connected ∧
      ∃ (E : Type) (N : NormedAddCommGroup E) (S : @NormedSpace ℝ E _ N.toSeminormedAddCommGroup),
        letI := N
        letI := S
        ∃ (_ : CompleteSpace E) (_ : FiniteDimensional ℝ E) (g : V → V → E),
          (∀ u v, g v u = -g u v) ∧
          (∀ u v z, G.Adj u v → G.Adj v z → G.Adj u z → ‖g u v + g v z - g u z‖ ≤ 1) ∧
          ∀ φ : V → E, ∃ u v, G.Adj u v ∧ O.readout () () ε ≤ ‖g u v - (φ v - φ u)‖

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  obtain ⟨V, FV, G, hc, _, E, norm, space, _, _, g, hg, hf, hL⟩ :=
    law 1 zero_lt_one
  letI := FV
  letI := norm
  letI := space
  obtain ⟨φ,hφ⟩ := upper_four_additive hc g hg hf
  obtain ⟨u,v,hAdj,hR⟩ := hL φ
  change (5 : ℝ) ≤ ‖g u v - (φ v - φ u)‖ at hR
  linarith [hφ u v hAdj]

def family : Registration arena (type_of% (@SimpleGraph.exists_chordal_banach_gain_lower_four)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨SimpleGraph.exists_chordal_banach_gain_lower_four, rejected, rejected_law⟩
  sensitivity := SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro _
    refine ⟨(), 1, 2, ?_⟩
    norm_num [actual, realize]

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@SimpleGraph.exists_chordal_banach_gain_lower_four) (Realization signature) Unit Unit where
  unitName := `SimpleGraph.exists_chordal_banach_gain_lower_four.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Chordal.ChordalBanachSharpFour.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Chordal.ChordalBanachSharpFour
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "body", "arg", "body", "arg", "body", "arg", "arg",
        "arg", "body", "arg", "body", "arg", "body", "arg", "body", "arg", "body",
        "arg", "body", "arg", "arg", "body", "arg", "body", "arg", "body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Combinatorics.Graph.Chordal.ChordalBanachSharpFour
