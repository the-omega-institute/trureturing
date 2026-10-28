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

namespace FullWitnessMass

abbrev signature : Signature where
  Params := Σ _ : Bias, ℕ
  State p := Observation
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p z => stoppingMass p.1 p.2 z) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {U : Type u} [MeasurableSpace U] (β : Bias) (j : Bool) (k : ℕ) (hk : 1 ≤ k) (ν : Measure U) [IsProbabilityMeasure ν] (B : Set U) (hB : MeasurableSet B) (z : Observation), ((stoppingRule j k).fullLaw β j ν).real (B ×ˢ {z}) = ν.real B * R.readout () ⟨β, k⟩ z

private theorem actual_law : arena.{u}.Law actual := by
  exact @stopping_witness_full_law.{u}

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let β : Bias := ⟨1 / 3, by norm_num, by norm_num, by norm_num⟩
  let ν : Measure (ULift.{u} Unit) := Measure.dirac (ULift.up ())
  haveI : IsProbabilityMeasure ν := by dsimp [ν]; infer_instance
  have hb := h β false 1 (by omega) ν Set.univ MeasurableSet.univ ⟨.a false, none, false, 0⟩
  have hs := stopping_witness_full_law β false 1 (by omega) ν Set.univ MeasurableSet.univ ⟨.a false, none, false, 0⟩
  norm_num [rejected, realize, stoppingMass] at hb hs
  linarith

def evidence : Registration arena.{u} (type_of% (@stopping_witness_full_law.{u})) where
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
    refine ⟨⟨β, 1⟩, ⟨.a false, none, false, 0⟩, ⟨.a false, some (.a false), true, 1⟩, ?_⟩
    norm_num [actual, realize, stoppingMass, Bias.π, β]

end FullWitnessMass

namespace OriginalWitnessContract

abbrev signature : Signature where
  Params := Σ _ : Bias, ℕ
  State p := Observation
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p z => stoppingMass p.1 p.2 z) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {U : Type u} [MeasurableSpace U] (β : Bias) (j : Bool) (k : ℕ) (hk : 1 ≤ k) (ν : Measure U) [IsProbabilityMeasure ν], (stoppingRule (U := U) j k).Lawful ∧ (stoppingRule (U := U) j k).TotalCap k ∧
      (∀ v ∈ (witnessTree j k).formalRuns,
        v.returned = true ∧ 1 ≤ v.paid ∧ v.paid ≤ k) ∧
      (∀ B : Set U, MeasurableSet B → ∀ z : Observation,
        ((stoppingRule j k).fullLaw β j ν).real (B ×ˢ {z}) =
          ν.real B * R.readout () ⟨β, k⟩ z) ∧
      (stoppingRule (U := U) j k).WithinActualRadius j (2 * k + 1)

private theorem actual_law : arena.{u}.Law actual := by
  exact @stopping_witness_original_contract.{u}

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let β : Bias := ⟨1 / 3, by norm_num, by norm_num, by norm_num⟩
  let ν : Measure (ULift.{u} Unit) := Measure.dirac (ULift.up ())
  haveI : IsProbabilityMeasure ν := by dsimp [ν]; infer_instance
  have hb := (h β false 1 (by omega) ν).2.2.2.1 Set.univ MeasurableSet.univ ⟨.a false, none, false, 0⟩
  have hs := stopping_witness_full_law β false 1 (by omega) ν Set.univ MeasurableSet.univ ⟨.a false, none, false, 0⟩
  norm_num [rejected, realize, stoppingMass] at hb hs
  linarith

def evidence : Registration arena.{u} (type_of% (@stopping_witness_original_contract.{u})) where
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
    refine ⟨⟨β, 1⟩, ⟨.a false, none, false, 0⟩, ⟨.a false, some (.a false), true, 1⟩, ?_⟩
    norm_num [actual, realize, stoppingMass, Bias.π, β]

end OriginalWitnessContract

namespace OriginalSharpProbability

abbrev signature : Signature where
  Params := Bias
  State p := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ β k => β.T k) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 3) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {U : Type u} [MeasurableSpace U] (β : Bias) (j : Bool) (k : ℕ) (hk : 1 ≤ k) (ν : Measure U) [IsProbabilityMeasure ν] (Q : RawRule U) (hQ : Q.CompletionLawful ν) (hc : Q.TotalCap k) (hlaw : Q.SameFullLaw (stoppingRule j k) β j ν),
    ((1 + R.readout () β k) / 2 ≤ ((sourceLaw β).prod ν).real (Q.remote j (2 * k + 1)) ∧
      ((sourceLaw β).prod ν).real ((stoppingRule (U := U) j k).remote j (2 * k + 1)) =
        (1 + β.T k) / 2) ∧
      (k = 1 → ((sourceLaw β).prod ν).real (Q.remote j (2 * k + 1)) = 1)

private theorem actual_law : arena.{u}.Law actual := by
  exact @original_rule_sharp_remote_probability.{u}

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let β : Bias := ⟨1 / 3, by norm_num, by norm_num, by norm_num⟩
  let ν : Measure (ULift.{u} Unit) := Measure.dirac (ULift.up ())
  haveI : IsProbabilityMeasure ν := by dsimp [ν]; infer_instance
  obtain ⟨Q, hQ, hc, hl, hr⟩ := (stopping_witness_exact_radius β false 1 (by omega) ν).1
  have hb := (h β false 1 (by omega) ν Q hQ hc hl).1.1
  have hs := (original_rule_sharp_remote_probability β false 1 (by omega) ν Q hQ hc hl).2 rfl
  rw [hs] at hb
  norm_num [rejected, realize] at hb

def evidence : Registration arena.{u} (type_of% (@original_rule_sharp_remote_probability.{u})) where
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
    refine ⟨β, 1, 2, ?_⟩
    exact ne_of_gt (β.T_succ_lt 1)

end OriginalSharpProbability

namespace CompletedSharpProbability

abbrev signature : Signature where
  Params := Bias
  State p := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ β k => β.T k) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 3) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {U : Type u} [MeasurableSpace U] (β : Bias) (j : Bool) (k : ℕ) (hk : 1 ≤ k) (ν : Measure U) [IsProbabilityMeasure ν] (Q : CompletedRule U) (hQ : Q.Lawful ((sourceLaw β).prod ν)) (hc : Q.TotalCap k) (hlaw : Q.fullLaw β j ν = (stoppingRule j k).fullLaw β j ν),
    (∃ T : U → {t : ReadTree // t.height ≤ k}, Measurable T ∧
      (∀ᵐ u ∂ν, (∀ᵐ s ∂sourceLaw β, Q.normalize k (s,u) = (T u).val) ∧
        ∃ es : List ℤ, es.length = k ∧ es.Nodup ∧ ∃ L : ℤ,
          (T u).val = ReadTree.stopComb (es.map (fun e => 2 * e + (!j).toInt)) ∧
          es.toFinset = pathEdges L k ∧ j.toInt ∉ pathVertices L k)) ∧
      ((1 + R.readout () β k) / 2 ≤ ((sourceLaw β).prod ν).real (Q.remote j (2 * k + 1))) ∧
      (((sourceLaw β).prod ν).real
        ((stoppingRule (U := U) j k).remote j (2 * k + 1)) = (1 + β.T k) / 2) ∧
      (k = 1 → ((sourceLaw β).prod ν).real (Q.remote j (2 * k + 1)) = 1)

private theorem actual_law : arena.{u}.Law actual := by
  exact @CompletedRule.original_rule_stopping_results.{u}

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let β : Bias := ⟨1 / 3, by norm_num, by norm_num, by norm_num⟩
  let ν : Measure (ULift.{u} Unit) := Measure.dirac (ULift.up ())
  haveI : IsProbabilityMeasure ν := by dsimp [ν]; infer_instance
  obtain ⟨Q, hQ, hc, hl, hr⟩ := (CompletedRule.completed_stopping_witness_exact_radius β false 1 (by omega) ν).1
  have hb := (h β false 1 (by omega) ν Q hQ hc hl).2.1
  have hs := (CompletedRule.original_rule_stopping_results β false 1 (by omega) ν Q hQ hc hl).2.2.2 rfl
  rw [hs] at hb
  norm_num [rejected, realize] at hb

def evidence : Registration arena.{u} (type_of% (@CompletedRule.original_rule_stopping_results.{u})) where
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
    refine ⟨β, 1, 2, ?_⟩
    exact ne_of_gt (β.T_succ_lt 1)

end CompletedSharpProbability

namespace OriginalRigidity

abbrev signature : Signature where
  Params := Unit
  State p := List ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ReadTree
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ ts => ReadTree.stopComb ts) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => .leaf none) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {U : Type u} [MeasurableSpace U] (β : Bias) (j : Bool) (k : ℕ) (hk : 1 ≤ k) (ν : Measure U) [IsProbabilityMeasure ν] (Q : RawRule U) (hQ : Q.CompletionLawful ν) (hc : Q.TotalCap k) (hlaw : Q.SameFullLaw (stoppingRule j k) β j ν), ∀ᵐ u ∂ν, ∃ es : List ℤ, es.length = k ∧ es.Nodup ∧ ∃ L : ℤ,
      Q.normalize k u = R.readout () () (es.map (fun e => 2 * e + (!j).toInt)) ∧
      es.toFinset = pathEdges L k ∧ j.toInt ∉ pathVertices L k

private theorem actual_law : arena.{u}.Law actual := by
  exact @original_rule_stopping_rigidity.{u}

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let β : Bias := ⟨1 / 3, by norm_num, by norm_num, by norm_num⟩
  let ν : Measure (ULift.{u} Unit) := Measure.dirac (ULift.up ())
  haveI : IsProbabilityMeasure ν := by dsimp [ν]; infer_instance
  obtain ⟨Q, hQ, hc, hl, hr⟩ := (stopping_witness_exact_radius β false 1 (by omega) ν).1
  have hs := original_rule_stopping_rigidity β false 1 (by omega) ν Q hQ hc hl
  have hb := h β false 1 (by omega) ν Q hQ hc hl
  obtain ⟨u, hu, hv⟩ := (hs.and hb).exists
  obtain ⟨es, hlen, _, L, he, _, _⟩ := hu
  obtain ⟨es₀, _, _, L₀, he₀, _, _⟩ := hv
  change Q.normalize 1 u = ReadTree.leaf none at he₀
  rw [he₀] at he
  cases es with
  | nil => simp at hlen
  | cons e es => cases he

def evidence : Registration arena.{u} (type_of% (@original_rule_stopping_rigidity.{u})) where
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
    refine ⟨(), [], [0], ?_⟩
    decide

end OriginalRigidity

namespace CanonicalWitness

abbrev signature : Signature where
  Params := Bool
  State p := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ReadTree
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ j k => witnessTree j k) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => .leaf none) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (β : Bias) (j : Bool) (k : ℕ) (hk : 1 ≤ k), HasStoppingLaw β (lawWindow (witnessTree j k)) j k (R.readout () j k)

private theorem actual_law : arena.Law actual := by
  exact @witness_canonical_law

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let β : Bias := ⟨1 / 3, by norm_num, by norm_num, by norm_num⟩
  let V := lawWindow (witnessTree false 1)
  let z : Observation := ⟨.a false, none, false, 0⟩
  have hb := (h β false 1 (by decide)) z
  change fullMass β V false (.leaf none) z = 0 at hb
  have hm := ReadTree.fullMass_a β V false false (.leaf none) none 0
  have he : {S : Spins | S (targetIndex false false) = false ∧ ((ReadTree.leaf none).run (visible false S)).output = none ∧ ((ReadTree.leaf none).run (visible false S)).paid = 0} = {S | S (targetIndex false false) = false} := by
    ext S
    simp [ReadTree.run, Execution.paid]
  rw [he, SpinWindow.spin_prob β V (targetIndex false false) (by simp [V, lawWindow, targetIndex]) false] at hm
  norm_num [Bias.π, β] at hm
  change fullMass β V false (.leaf none) z = 1 / 3 at hm
  rw [hb] at hm
  norm_num at hm

def evidence : Registration arena (type_of% (@witness_canonical_law)) where
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
    refine ⟨false, 1, 2, ?_⟩
    decide

end CanonicalWitness

end
end Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SeedLaw
