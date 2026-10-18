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

abbrev signature : Signature where
  Params := Σ _ : Bool, ℤ
  State _ := Spins
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p S => visible p.1 S (2 * p.2 + p.1.toInt)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => true) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (φ : Bool) (S : Spins) (e : ℤ),
    R.readout () ⟨φ, e⟩ S = Bool.xor (S e) (S (e + 1))

private theorem actual_law : arena.Law actual := by
  exact active_visible

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h false (fun _ => false) 0
  simpa [rejected, realize] using hbad

def evidence : Registration arena (type_of% (@active_visible)) where
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
    refine ⟨⟨false, 0⟩, (fun _ => false), (fun e => decide (e = 0)), ?_⟩
    simp [actual, realize, visible]

namespace ActualEndpoint

abbrev signature : Signature where
  Params := Σ _ : Bool, Bool
  State p := Spins
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Hidden
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p S => hidden p.2 S p.1.toInt) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => Hidden.a false) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (j φ : Bool) (S : Spins), R.readout () ⟨j, φ⟩ S = targetClass j φ (S (targetIndex j φ))

private theorem actual_law : arena.Law actual := by
  exact @actual_endpoint

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h false false (fun _ => true)
  simpa [rejected, realize, targetClass, targetIndex] using hb

def evidence : Registration arena (type_of% (@actual_endpoint)) where
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
    refine ⟨⟨false, false⟩, (fun _ => false), (fun _ => true), ?_⟩
    simp [actual, realize, _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.hidden]

end ActualEndpoint

namespace OppositePhase

abbrev signature : Signature where
  Params := Σ _ : Bool, ℤ
  State p := Spins
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p S => visible (!p.1) S p.2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => true) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (φ : Bool) (S : Spins) (t : ℤ), (t - φ.toInt) % 2 = 0 → R.readout () ⟨φ, t⟩ S = false

private theorem actual_law : arena.Law actual := by
  exact @opposite_phase_visible

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h false (fun _ => false) 0 (by decide)
  simpa [rejected, realize] using hb

def evidence : Registration arena (type_of% (@opposite_phase_visible)) where
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
    refine ⟨⟨false, 1⟩, (fun _ => false), (fun e => decide (e = 0)), ?_⟩
    simp [actual, realize, visible]

end OppositePhase

namespace ConstantSource

abbrev signature : Signature where
  Params := Bool
  State p := Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Spins
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ s => fun _ => s) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ e => decide (e = 0)) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (φ s : Bool) (t : ℤ), visible φ (R.readout () φ s) t = false

private theorem actual_law : arena.Law actual := by
  exact @constant_visible

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h false false 0
  simpa [rejected, realize, visible] using hb

def evidence : Registration arena (type_of% (@constant_visible)) where
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
    refine ⟨false, false, true, ?_⟩
    intro h
    have hb := congrFun h 0
    simpa [actual, realize] using hb

end ConstantSource

namespace ZeroComb

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
  Law R := ∀ (ts : List ℤ) (x : ℤ → Bool) (h : ∀ t ∈ ts, x t = false), R.readout () ts x = ⟨some (.a false), ts.map (fun t => (t, false))⟩

private theorem actual_law : arena.Law actual := by
  exact @ReadTree.stopComb_all_zero

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h [] (fun _ => false) (by simp)
  simpa [rejected, realize] using hb

def evidence : Registration arena (type_of% (@ReadTree.stopComb_all_zero)) where
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

end ZeroComb

namespace Agreement

abbrev signature : Signature where
  Params := Σ _ : ReadTree, Bool
  State p := Spins
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Execution
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p S => p.1.run (visible p.2 S)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => ⟨none, []⟩) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (T : ReadTree) (φ : Bool) (S S₀ : Spins) (h : ∀ i ∈ T.support, S i = S₀ i), R.readout () ⟨T, φ⟩ S = T.run (visible φ S₀)

private theorem actual_law : arena.Law actual := by
  exact @ReadTree.source_run_eq_of_agree

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h (.leaf (some (.a false))) false (fun _ => false) (fun _ => false) (by simp)
  simpa [rejected, realize, ReadTree.run] using hb

def evidence : Registration arena (type_of% (@ReadTree.source_run_eq_of_agree)) where
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
    refine ⟨⟨.read 0 (.leaf (some (.a false))) (.leaf (some (.a true))), false⟩, (fun _ => false), (fun e => decide (e = 0)), ?_⟩
    intro h
    have hb := congrArg Execution.output h
    simpa [actual, realize, ReadTree.run, visible, Execution.prepend] using hb

end Agreement

namespace PaidPrepend

abbrev signature : Signature where
  Params := Unit
  State p := Execution
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ v => v.paid) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (t : ℤ) (b : Bool) (v : Execution), R.readout () () (v.prepend t b) = v.paid + 1

private theorem actual_law : arena.Law actual := by
  exact @Execution.paid_prepend

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 0 false ⟨none, []⟩
  norm_num [rejected, realize, Execution.paid] at hb

def evidence : Registration arena (type_of% (@Execution.paid_prepend)) where
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
    norm_num [actual, realize, Execution.paid]

end PaidPrepend

end
end Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SemanticNormalization
