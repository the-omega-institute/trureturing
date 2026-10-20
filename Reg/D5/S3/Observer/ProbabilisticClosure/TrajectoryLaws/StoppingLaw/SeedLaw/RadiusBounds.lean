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

abbrev signature : Signature where
  Params := Bool
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := List ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ j k => (witnessEdges j k).map (fun e => 2 * e + (!j).toInt)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => []) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (j : Bool) (k : ℕ), R.readout () j k =
    (List.range k).map (fun i : ℕ => j.toInt + 2 * ((i : ℤ) + 1) + 1)

private theorem actual_law : arena.Law actual := by
  exact witness_read_addresses

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h false 1
  simpa [rejected, realize] using hbad

def evidence : Registration arena (type_of% (@witness_read_addresses)) where
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
    refine ⟨false, 0, 1, ?_⟩
    simp [actual, realize, witnessEdges]

namespace RawMinimum

abbrev signature : Signature where
  Params := Unit
  State p := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ k => 2 * k + 1) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {U : Type u} [MeasurableSpace U] (β : Bias) (j : Bool) (k : ℕ) (hk : 1 ≤ k) (ν : Measure U) [IsProbabilityMeasure ν], IsLeast {R : ℕ | ∃ Q : RawRule U, Q.CompletionLawful ν ∧ Q.TotalCap k ∧ Q.SameFullLaw (stoppingRule j k) β j ν ∧ Q.WithinActualRadius j R} (R.readout () () k)

private theorem actual_law : arena.{u}.Law actual := by
  exact @stopping_witness_exact_radius.{u}

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let β : Bias := ⟨1 / 3, by norm_num, by norm_num, by norm_num⟩
  let ν : Measure (ULift.{u} Unit) := Measure.dirac (ULift.up ())
  haveI : IsProbabilityMeasure ν := by dsimp [ν]; infer_instance
  have hb := h (U := ULift.{u} Unit) β false 1 (by omega) ν
  have hs := stopping_witness_exact_radius β false 1 (by omega) ν
  have hc := hs.2 hb.1
  norm_num [rejected, realize] at hc

def evidence : Registration arena.{u} (type_of% (@stopping_witness_exact_radius.{u})) where
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
    refine ⟨(), 1, 2, ?_⟩
    norm_num [actual, realize]

end RawMinimum

namespace CompletedMinimum

abbrev signature : Signature where
  Params := Unit
  State p := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ k => 2 * k + 1) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {U : Type u} [MeasurableSpace U] (β : Bias) (j : Bool) (k : ℕ) (hk : 1 ≤ k) (ν : Measure U) [IsProbabilityMeasure ν], IsLeast {R : ℕ | ∃ Q : CompletedRule U, Q.Lawful ((sourceLaw β).prod ν) ∧ Q.TotalCap k ∧ Q.fullLaw β j ν = (stoppingRule j k).fullLaw β j ν ∧ Q.CompletedWithinActualRadius j R} (R.readout () () k)

private theorem actual_law : arena.{u}.Law actual := by
  exact @CompletedRule.completed_stopping_witness_exact_radius.{u}

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let β : Bias := ⟨1 / 3, by norm_num, by norm_num, by norm_num⟩
  let ν : Measure (ULift.{u} Unit) := Measure.dirac (ULift.up ())
  haveI : IsProbabilityMeasure ν := by dsimp [ν]; infer_instance
  have hb := h (U := ULift.{u} Unit) β false 1 (by omega) ν
  have hs := CompletedRule.completed_stopping_witness_exact_radius β false 1 (by omega) ν
  have hc := hs.2 hb.1
  norm_num [rejected, realize] at hc

def evidence : Registration arena.{u} (type_of% (@CompletedRule.completed_stopping_witness_exact_radius.{u})) where
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
    refine ⟨(), 1, 2, ?_⟩
    norm_num [actual, realize]

end CompletedMinimum

namespace RadiusLower

abbrev signature : Signature where
  Params := Unit
  State p := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ k => 2 * k + 1) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ k => 2 * k + 2) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {U : Type u} [MeasurableSpace U] (β : Bias) (j : Bool) (k : ℕ) (hk : 1 ≤ k) (ν : Measure U) [IsProbabilityMeasure ν] (Q : RawRule U) (hQ : Q.CompletionLawful ν) (hc : Q.TotalCap k) (hlaw : Q.SameFullLaw (stoppingRule j k) β j ν) (r : ℕ) (hr : Q.WithinActualRadius j r), R.readout () () k ≤ r

private theorem actual_law : arena.{u}.Law actual := by
  exact @original_rule_radius_lower.{u}

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let β : Bias := ⟨1 / 3, by norm_num, by norm_num, by norm_num⟩
  let ν : Measure (ULift.{u} Unit) := Measure.dirac (ULift.up ())
  haveI : IsProbabilityMeasure ν := by dsimp [ν]; infer_instance
  obtain ⟨Q, hQ, hc, hl, hr⟩ := (stopping_witness_exact_radius β false 1 (by omega) ν).1
  have hb := h β false 1 (by omega) ν Q hQ hc hl 3 hr
  norm_num [rejected, realize] at hb

def evidence : Registration arena.{u} (type_of% (@original_rule_radius_lower.{u})) where
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
    refine ⟨(), 1, 2, ?_⟩
    norm_num [actual, realize]

end RadiusLower

end
end Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SeedLaw
