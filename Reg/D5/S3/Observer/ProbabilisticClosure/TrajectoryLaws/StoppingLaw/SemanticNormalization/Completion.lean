import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SemanticNormalization
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SemanticNormalization

open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

open MeasureTheory
universe u

noncomputable section

namespace ReturnIndicator

abbrev signature : Signature where
  Params := Unit
  State p := Execution
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ v => v.returned) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {U : Type u} [MeasurableSpace U] (Q : RawRule U) (k : ℕ) (hc : Q.TotalCap k) (φ : Bool) (S : Spins) (u : U), decide (Q.returnTime u (visible φ S) < ⊤) = R.readout () () ((Q.normalize k u).run (visible φ S))

private theorem actual_law : arena.{u}.Law actual := by
  exact @RawRule.normalization_return_indicator.{u}

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let T : ULift.{u} Unit → ReadTree := fun _ => .leaf (some (.a false))
  let Q : RawRule (ULift.{u} Unit) := RawRule.realize T
  have hc : Q.TotalCap 0 := RawRule.realize_cap T 0 (fun _ => by rfl)
  have hs := Q.normalization_pointwise 0 hc false (fun _ => false) (ULift.up ())
  have ho := hs.2.1
  change Q.output (ULift.up ()) (visible false (fun _ => false)) = some (.a false) at ho
  have hr := Q.normalization_return_indicator 0 hc false (fun _ => false) (ULift.up ())
  have hb := h Q 0 hc false (fun _ => false) (ULift.up ())
  change decide (Q.returnTime (ULift.up ()) (visible false (fun _ => false)) < ⊤) = true at hr
  rw [hr] at hb
  simpa [rejected, realize] using hb

def evidence : Registration arena.{u} (type_of% (@RawRule.normalization_return_indicator.{u})) where
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
    refine ⟨(), ⟨none, []⟩, ⟨some (.a false), []⟩, ?_⟩
    decide

end ReturnIndicator

namespace CompletedOutput

abbrev signature : Signature where
  Params := Unit
  State p := Execution
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Option Hidden
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ v => v.output) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => none) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {U : Type u} [MeasurableSpace U] (Q : CompletedRule U) (k : ℕ) (hc : Q.TotalCap k) (p : SourcePoint × U),
    let v := (Q.normalize k p).run (visible p.1.1 p.1.2)
    (Q.atSource p.1).Completes p.2 (visible p.1.1 p.1.2) v ∧
      (Q.atSource p.1).output p.2 (visible p.1.1 p.1.2) = R.readout () () v ∧
      (Q.atSource p.1).paidCount p.2 (visible p.1.1 p.1.2) = v.paid

private theorem actual_law : arena.{u}.Law actual := by
  exact @CompletedRule.completed_normalization_execution.{u}

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let T : ULift.{u} Unit → ReadTree := fun _ => .leaf (some (.a false))
  let Q : CompletedRule (ULift.{u} Unit) := CompletedRule.fromRaw (RawRule.realize T)
  have hc : Q.TotalCap 0 := by
    intro s u
    exact RawRule.realize_cap T 0 (fun _ => by rfl) s.1 s.2 u
  let p : SourcePoint × ULift.{u} Unit := ((false, fun _ => false), ULift.up ())
  have hs := (Q.completed_normalization_execution 0 hc p).2.1
  have hb := (h Q 0 hc p).2.1
  change (Q.atSource p.1).output p.2 (visible p.1.1 p.1.2) = some (.a false) at hs
  rw [hs] at hb
  simpa [rejected, realize] using hb

def evidence : Registration arena.{u} (type_of% (@CompletedRule.completed_normalization_execution.{u})) where
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
    refine ⟨(), ⟨none, []⟩, ⟨some (.a false), []⟩, ?_⟩
    decide

end CompletedOutput

namespace FormalCombRuns

abbrev signature : Signature where
  Params := Unit
  State p := ReadTree
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := List Execution
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ T => T.formalRuns) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => [⟨none, []⟩]) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (ts : List ℤ), ∀ v ∈ R.readout () () (ReadTree.stopComb ts),
      v.output = some (.a false) ∧ v.paid = ts.length ∨
      v.output = some (.a true) ∧ 1 ≤ v.paid ∧ v.paid ≤ ts.length

private theorem actual_law : arena.Law actual := by
  exact @ReadTree.stopComb_formal_outcomes

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h [] ⟨none, []⟩ (by simp [rejected, realize])
  simpa using hb

def evidence : Registration arena (type_of% (@ReadTree.stopComb_formal_outcomes)) where
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
    refine ⟨(), .leaf none, .leaf (some (.a false)), ?_⟩
    decide

end FormalCombRuns

namespace FiniteReturn

abbrev signature : Signature where
  Params := Unit
  State p := Option Hidden
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ o => o.isSome) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {U : Type u} [MeasurableSpace U] (Q : RawRule U) (u : U) (x : ℤ → Bool), Q.returnTime u x < ⊤ ↔ R.readout () () (Q.output u x) = true

private theorem actual_law : arena.{u}.Law actual := by
  exact @RawRule.finite_return_iff.{u}

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let T : ULift.{u} Unit → ReadTree := fun _ => .leaf (some (.a false))
  let Q : RawRule (ULift.{u} Unit) := RawRule.realize T
  have hc : Q.TotalCap 0 := RawRule.realize_cap T 0 (fun _ => by rfl)
  have hs := Q.normalization_pointwise 0 hc false (fun _ => false) (ULift.up ())
  have ho := hs.2.1
  change Q.output (ULift.up ()) (visible false (fun _ => false)) = some (.a false) at ho
  have hr : Q.returnTime (ULift.up ()) (visible false (fun _ => false)) < ⊤ := (Q.finite_return_iff _ _).2 (by rw [ho]; rfl)
  have hb := (h Q (ULift.up ()) (visible false (fun _ => false))).1 hr
  simpa [rejected, realize] using hb

def evidence : Registration arena.{u} (type_of% (@RawRule.finite_return_iff.{u})) where
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
    refine ⟨(), none, some (.a false), ?_⟩
    decide

end FiniteReturn

namespace CompletedRecord

abbrev signature : Signature where
  Params := Unit
  State p := Execution
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Record
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ v => v.record) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => []) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {U : Type u} [MeasurableSpace U] (Q : RawRule U) (u : U) (x : ℤ → Bool) {v : Execution} (hv : Q.Completes u x v) {n : ℕ} {r : Record}
    (hr : Q.readPrefix u x n = some r), ∀ a ∈ r, a ∈ R.readout () () v

private theorem actual_law : arena.{u}.Law actual := by
  exact @RawRule.completes_record_subset.{u}

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let T : ULift.{u} Unit → ReadTree := fun _ => .read 0 (.leaf none) (.leaf none)
  let Q : RawRule (ULift.{u} Unit) := RawRule.realize T
  let x : ℤ → Bool := fun _ => false
  let v : Execution := ⟨none, [(0, false)]⟩
  have hv : Q.Completes (ULift.up ()) x v := by constructor <;> rfl
  have hb := h Q (ULift.up ()) x (v := v) hv (n := 1) (r := [(0, false)]) rfl (0, false) (by simp)
  simpa [rejected, realize] using hb

def evidence : Registration arena.{u} (type_of% (@RawRule.completes_record_subset.{u})) where
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
    refine ⟨(), ⟨none, []⟩, ⟨none, [(0, false)]⟩, ?_⟩
    decide

end CompletedRecord

namespace CompletionVersion

abbrev signature : Signature where
  Params := Σ V : Type u, V
  State p := p.1 → ReadTree
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ReadTree
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature.{u} (fun _ p f => f p.2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature.{u} (fun _ _ _ => .read 0 (.leaf none) (.leaf none)) (fun e => nomatch e)

def arena : Arena where
  signature := signature.{u}
  Law R := ∀ {U : Type u} [MeasurableSpace U] (Q : RawRule U) (ν : Measure U) (hQ : Q.CompletionLawful ν) (k : ℕ), ∃ F : U → {T : ReadTree // T.height ≤ k}, Measurable F ∧ ∀ᵐ u ∂ν, R.readout () ⟨U, u⟩ (Q.normalize k) = (F u).val

private theorem actual_law : arena.{u}.Law actual := by
  exact @RawRule.completion_normalization_version.{u}

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
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
  obtain ⟨F, _, he⟩ := h Q ν hQ 0
  obtain ⟨u, hu⟩ := he.exists
  have hh := (F u).property
  have heq : ReadTree.read 0 (.leaf none) (.leaf none) = (F u).val := by simpa [rejected, realize] using hu
  rw [← heq] at hh
  norm_num [ReadTree.height] at hh

def evidence : Registration arena.{u} (type_of% (@RawRule.completion_normalization_version.{u})) where
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
    refine ⟨⟨ULift.{u} Unit, ULift.up ()⟩, (fun _ => ReadTree.leaf none), (fun _ => ReadTree.leaf (some (.a false))), ?_⟩
    decide

end CompletionVersion

namespace CompletionBridge

abbrev signature : Signature where
  Params := Σ V : Type u, V
  State p := p.1 → ReadTree
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ReadTree
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature.{u} (fun _ p f => f p.2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature.{u} (fun _ _ _ => .read 0 (.leaf none) (.leaf none)) (fun e => nomatch e)

def arena : Arena where
  signature := signature.{u}
  Law R := ∀ {U : Type u} [MeasurableSpace U] (Q : RawRule U) (ν : Measure U) (hQ : Q.CompletionLawful ν) (k : ℕ) (hc : Q.TotalCap k), ∃ F : U → {T : ReadTree // T.height ≤ k}, Measurable F ∧
      (∀ᵐ u ∂ν, R.readout () ⟨U, u⟩ (Q.normalize k) = (F u).val) ∧
      ∀ᵐ u ∂ν, ∀ (φ : Bool) (S : Spins), let v := (F u).val.run (visible φ S)
        Q.Completes u (visible φ S) v ∧ Q.output u (visible φ S) = v.output ∧ Q.paidCount u (visible φ S) = v.paid

private theorem actual_law : arena.{u}.Law actual := by
  exact @RawRule.completion_normalization_bridge.{u}

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
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
  obtain ⟨F, _, he, _⟩ := h Q ν hQ 0 hc
  obtain ⟨u, hu⟩ := he.exists
  have hh := (F u).property
  have heq : ReadTree.read 0 (.leaf none) (.leaf none) = (F u).val := by simpa [rejected, realize] using hu
  rw [← heq] at hh
  norm_num [ReadTree.height] at hh

def evidence : Registration arena.{u} (type_of% (@RawRule.completion_normalization_bridge.{u})) where
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
    refine ⟨⟨ULift.{u} Unit, ULift.up ()⟩, (fun _ => ReadTree.leaf none), (fun _ => ReadTree.leaf (some (.a false))), ?_⟩
    decide

end CompletionBridge

end
end Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SemanticNormalization
