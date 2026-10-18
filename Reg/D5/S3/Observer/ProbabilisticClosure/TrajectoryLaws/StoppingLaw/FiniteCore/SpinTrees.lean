import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.FiniteCore
import Reg.Support.DependentFamily
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SeedLaw

open MeasureTheory

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.FiniteCore

open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

namespace SpinMass

abbrev signature : Signature where
  Params := Σ _ : Bias, Finset ℤ
  State p := Set Spins
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p E => SpinWindow.prob p.1 p.2 E) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (β : Bias) (V : Finset ℤ) (q : ℤ) (hq : q ∈ V) (s : Bool), R.readout () ⟨β, V⟩ {S | S q = s} = β.π s

private theorem actual_law : arena.Law actual := by
  exact @SpinWindow.spin_prob

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let β : Bias := ⟨1 / 3, by norm_num, by norm_num, by norm_num⟩
  have hb := h β {0} 0 (by simp) false
  norm_num [rejected, realize, Bias.π, β] at hb

def evidence : Registration arena (type_of% (@SpinWindow.spin_prob)) where
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
    refine ⟨⟨β, ∅⟩, ∅, Set.univ, ?_⟩
    change SpinWindow.prob β ∅ ∅ ≠ SpinWindow.prob β ∅ Set.univ
    rw [SpinWindow.prob_univ]
    simp [SpinWindow.prob, FiniteSpinLaw.mass]

end SpinMass

namespace CombOutput

abbrev signature : Signature where
  Params := List ℤ
  State p := ℤ → Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Execution
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ ts x => (ReadTree.stopComb ts).run x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => ⟨none, []⟩) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (ts : List ℤ) (x : ℤ → Bool),
    (R.readout () ts x).output = some (.a false) ∧
      ((ReadTree.stopComb ts).run x).paid = ts.length ∨
    ((ReadTree.stopComb ts).run x).output = some (.a true) ∧
      1 ≤ ((ReadTree.stopComb ts).run x).paid ∧ ((ReadTree.stopComb ts).run x).paid ≤ ts.length

private theorem actual_law : arena.Law actual := by
  exact @ReadTree.stopComb_outcomes

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h [] (fun _ => false)
  simpa [rejected, realize, ReadTree.stopComb, ReadTree.run] using hb

def evidence : Registration arena (type_of% (@ReadTree.stopComb_outcomes)) where
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
    refine ⟨[0], (fun _ => false), (fun _ => true), ?_⟩
    intro h
    have hb := congrArg Execution.output h
    simpa [actual, realize, ReadTree.stopComb, ReadTree.run, Execution.prepend] using hb

end CombOutput

namespace ZeroFinal

abbrev signature : Signature where
  Params := List ℤ
  State p := ℤ → Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Execution
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ ts x => (ReadTree.stopComb ts).run x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => ⟨none, []⟩) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (ts : List ℤ) (x : ℤ → Bool), ReadTree.ZeroReplies ts ts.length x ↔ (R.readout () ts x).output = some (.a false) ∧ ((ReadTree.stopComb ts).run x).paid = ts.length

private theorem actual_law : arena.Law actual := by
  exact @ReadTree.zero_prefix_final

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := (h [] (fun _ => false)).1 (by simp [ReadTree.ZeroReplies])
  simpa [rejected, realize] using hb

def evidence : Registration arena (type_of% (@ReadTree.zero_prefix_final)) where
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
    refine ⟨[0], (fun _ => false), (fun _ => true), ?_⟩
    intro h
    have hb := congrArg Execution.output h
    simpa [actual, realize, ReadTree.stopComb, ReadTree.run, Execution.prepend] using hb

end ZeroFinal

namespace EdgeZeroReplies

abbrev signature : Signature where
  Params := Bool
  State p := Spins
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ → Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ φ S => visible φ S) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => true) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (es : List ℤ) (φ : Bool) (S : Spins) (r : ℕ), ReadTree.ZeroReplies (es.map (fun e => 2 * e + φ.toInt)) r (R.readout () φ S) ↔ ∀ e ∈ (es.take r).toFinset, S e = S (e + 1)

private theorem actual_law : arena.Law actual := by
  exact @ReadTree.edge_zero_prefix

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := (h [0] false (fun _ => false) 1).2 (by simp)
  simpa [ReadTree.ZeroReplies, rejected, realize] using hb

def evidence : Registration arena (type_of% (@ReadTree.edge_zero_prefix)) where
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
    refine ⟨false, (fun _ => false), (fun e => decide (e = 0)), ?_⟩
    intro h
    have hb := congrFun h 0
    norm_num [actual, realize, visible] at hb

end EdgeZeroReplies

namespace CombSupport

abbrev signature : Signature where
  Params := Unit
  State p := ReadTree
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Finset ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ T => T.support) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => ∅) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (es : List ℤ) (φ : Bool), ∀ e ∈ es, e ∈ R.readout () () (ReadTree.edgeComb es φ) ∧ e + 1 ∈ (ReadTree.edgeComb es φ).support

private theorem actual_law : arena.Law actual := by
  exact @ReadTree.edgeComb_support

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := (h [0] false 0 (by simp)).1
  simpa [rejected, realize] using hb

def evidence : Registration arena (type_of% (@ReadTree.edgeComb_support)) where
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
    refine ⟨(), .leaf none, .read 0 (.leaf none) (.leaf none), ?_⟩
    decide

end CombSupport

end
end Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.FiniteCore
