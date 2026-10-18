import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SeedLaw
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SeedLaw

open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

open MeasureTheory
universe u

noncomputable section

namespace RawLawSections

abbrev signature : Signature where
  Params := Bias
  State p := Set SourcePoint
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ β E => (sourceLaw β).real E) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {U : Type u} [MeasurableSpace U] (β : Bias) (j : Bool) (ν : Measure U) [IsProbabilityMeasure ν] (Q : RawRule U) (hQ : Q.CompletionLawful ν) (k : ℕ) (hc : Q.TotalCap k) (w : SourcePoint → Observation) (hw : Measurable w)
    (hlaw : Q.fullLaw β j ν = ((sourceLaw β).prod ν).map (fun p : SourcePoint × U => (p.2, w p.1))),
    ∀ᵐ u ∂ν, ∀ z : Observation, fullMass β (lawWindow (Q.normalize k u)) j (Q.normalize k u) z = R.readout () β (w ⁻¹' {z})

private theorem actual_law : arena.{u}.Law actual := by
  exact @full_same_seed_law_forces_sections.{u}

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let β : Bias := ⟨1 / 3, by norm_num, by norm_num, by norm_num⟩
  let ν : Measure (ULift.{u} Unit) := Measure.dirac (ULift.up ())
  haveI : IsProbabilityMeasure ν := by dsimp [ν]; infer_instance
  let T : ULift.{u} Unit → ReadTree := fun _ => .leaf none
  let Q : RawRule (ULift.{u} Unit) := RawRule.realize T
  have hc : Q.TotalCap 0 := RawRule.realize_cap T 0 (fun _ => by rfl)
  have hQ : Q.CompletionLawful ν := by
    constructor
    · intro r
      change Measurable (fun _ : NullMeasurableSpace (ULift.{u} Unit) ν => (ReadTree.leaf none).eventAfter r)
      exact measurable_const
    · intro r
      change Measurable (fun _ : NullMeasurableSpace (ULift.{u} Unit) ν => (0 : NNReal))
      exact measurable_const
  let w : SourcePoint → Observation := fun s => observation false s.1 (.leaf none) s.2
  have hw : Measurable w := measurable_observation false (.leaf none)
  have hj : Q.joint false = fun p : SourcePoint × ULift.{u} Unit => (p.2, w p.1) := by
    funext p
    have hs := Q.normalization_pointwise 0 hc p.1.1 p.1.2 p.2
    have hd := Q.normalization_return_indicator 0 hc p.1.1 p.1.2 p.2
    dsimp only [RawRule.joint, RawRule.rawObservation, w, observation]
    rw [hs.2.1, hd, hs.2.2]
    rfl
  have hlaw : Q.fullLaw β false ν = ((sourceLaw β).prod ν).map (fun p : SourcePoint × ULift.{u} Unit => (p.2, w p.1)) := by
    unfold RawRule.fullLaw
    rw [hj]
  have hb := h β false ν Q hQ 0 hc w hw hlaw
  obtain ⟨u, hu⟩ := hb.exists
  let z : Observation := ⟨.a false, none, false, 0⟩
  have hx := hu z
  have hs := sourceLaw_observation β false (Q.normalize 0 u) z
  have hbnd : fullMass β (lawWindow (Q.normalize 0 u)) false (Q.normalize 0 u) z ≤ 1 := by
    rw [← hs]
    exact measureReal_le_one
  norm_num [rejected, realize] at hx
  linarith

def evidence : Registration arena.{u} (type_of% (@full_same_seed_law_forces_sections.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    dsimp only [Sensitivity, arena, signature]
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (Subsingleton.elim j i))
    · intro i
      exact nomatch i
  dependence := by
    dsimp only [ObservationalDependence, arena, signature]
    intro i
    cases i
    let β : Bias := ⟨1 / 3, by norm_num, by norm_num, by norm_num⟩
    refine ⟨β, ∅, Set.univ, ?_⟩
    simp [actual, realize]

end RawLawSections

namespace CompletedLawSections

abbrev signature : Signature where
  Params := Bias
  State p := Set SourcePoint
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ β E => (sourceLaw β).real E) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {U : Type u} [MeasurableSpace U] (β : Bias) (j : Bool) (ν : Measure U) [IsProbabilityMeasure ν] (Q : CompletedRule U) (hQ : Q.Lawful ((sourceLaw β).prod ν)) (k : ℕ) (hc : Q.TotalCap k) (w : SourcePoint → Observation) (hw : Measurable w)
    (hlaw : Q.fullLaw β j ν = ((sourceLaw β).prod ν).map (fun p : SourcePoint × U => (p.2, w p.1))),
    ∃ T : U → {t : ReadTree // t.height ≤ k}, Measurable T ∧
      (Q.normalize k =ᵐ[(sourceLaw β).prod ν] fun p => (T p.2).val) ∧
      (∀ᵐ u ∂ν, (∀ᵐ s ∂sourceLaw β, Q.normalize k (s,u) = (T u).val) ∧
        ∀ z, fullMass β (lawWindow (T u).val) j (T u).val z = R.readout () β (w ⁻¹' {z}))

private theorem actual_law : arena.{u}.Law actual := by
  exact @CompletedRule.full_law_sections.{u}

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let β : Bias := ⟨1 / 3, by norm_num, by norm_num, by norm_num⟩
  let ν : Measure (ULift.{u} Unit) := Measure.dirac (ULift.up ())
  haveI : IsProbabilityMeasure ν := by dsimp [ν]; infer_instance
  let T : ULift.{u} Unit → ReadTree := fun _ => .leaf none
  let Q : RawRule (ULift.{u} Unit) := RawRule.realize T
  have hc : Q.TotalCap 0 := RawRule.realize_cap T 0 (fun _ => by rfl)
  have hQ : Q.CompletionLawful ν := by
    constructor
    · intro r
      change Measurable (fun _ : NullMeasurableSpace (ULift.{u} Unit) ν => (ReadTree.leaf none).eventAfter r)
      exact measurable_const
    · intro r
      change Measurable (fun _ : NullMeasurableSpace (ULift.{u} Unit) ν => (0 : NNReal))
      exact measurable_const
  let w : SourcePoint → Observation := fun s => observation false s.1 (.leaf none) s.2
  have hw : Measurable w := measurable_observation false (.leaf none)
  have hj : Q.joint false = fun p : SourcePoint × ULift.{u} Unit => (p.2, w p.1) := by
    funext p
    have hs := Q.normalization_pointwise 0 hc p.1.1 p.1.2 p.2
    have hd := Q.normalization_return_indicator 0 hc p.1.1 p.1.2 p.2
    dsimp only [RawRule.joint, RawRule.rawObservation, w, observation]
    rw [hs.2.1, hd, hs.2.2]
    rfl
  have hlaw : Q.fullLaw β false ν = ((sourceLaw β).prod ν).map (fun p : SourcePoint × ULift.{u} Unit => (p.2, w p.1)) := by
    unfold RawRule.fullLaw
    rw [hj]
  let C : CompletedRule (ULift.{u} Unit) := CompletedRule.fromRaw Q
  have hC : C.Lawful ((sourceLaw β).prod ν) := CompletedRule.fromRaw_completion_lawful Q ν hQ _ Measure.quasiMeasurePreserving_snd
  have hcap : C.TotalCap 0 := by intro s u; exact hc s.1 s.2 u
  have hclaw : C.fullLaw β false ν = ((sourceLaw β).prod ν).map (fun p : SourcePoint × ULift.{u} Unit => (p.2, w p.1)) := hlaw
  obtain ⟨F, _, _, hf⟩ := h β false ν C hC 0 hcap w hw hclaw
  obtain ⟨u, hu⟩ := hf.exists
  let z : Observation := ⟨.a false, none, false, 0⟩
  have hx := hu.2 z
  have hs := sourceLaw_observation β false (F u).val z
  have hbnd : fullMass β (lawWindow (F u).val) false (F u).val z ≤ 1 := by
    rw [← hs]
    exact measureReal_le_one
  norm_num [rejected, realize] at hx
  linarith

def evidence : Registration arena.{u} (type_of% (@CompletedRule.full_law_sections.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    dsimp only [Sensitivity, arena, signature]
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (Subsingleton.elim j i))
    · intro i
      exact nomatch i
  dependence := by
    dsimp only [ObservationalDependence, arena, signature]
    intro i
    cases i
    let β : Bias := ⟨1 / 3, by norm_num, by norm_num, by norm_num⟩
    refine ⟨β, ∅, Set.univ, ?_⟩
    simp [actual, realize]

end CompletedLawSections

end
end Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SeedLaw
