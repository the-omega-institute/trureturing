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

namespace PaidCap

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
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (T : ReadTree) {k : ℕ} (h : T.height ≤ k) (x : ℤ → Bool), R.readout () () (T.run x) ≤ k

private theorem actual_law : arena.Law actual := by
  exact @ReadTree.paid_cap

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h (.leaf none) (k := 0) (by decide) (fun _ => false)
  norm_num [rejected, realize] at hb

def evidence : Registration arena (type_of% (@ReadTree.paid_cap)) where
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

end PaidCap

namespace RecordAddresses

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
  realize signature (fun _ _ T => T.addresses) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => ∅) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (T : ReadTree) (x : ℤ → Bool), ∀ a ∈ (T.run x).record, a.1 ∈ R.readout () () T

private theorem actual_law : arena.Law actual := by
  exact @ReadTree.record_addresses

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h (.read 0 (.leaf none) (.leaf none)) (fun _ => false) (0, false) (by simp [ReadTree.run, Execution.prepend])
  simpa [rejected, realize] using hb

def evidence : Registration arena (type_of% (@ReadTree.record_addresses)) where
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
    simp [actual, realize, ReadTree.addresses]

end RecordAddresses

namespace LeafFromZero

abbrev signature : Signature where
  Params := Unit
  State p := Option Hidden
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ReadTree
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ o => .leaf o) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => .read 0 (.leaf none) (.leaf none)) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (T : ReadTree) (x : ℤ → Bool) (h : (T.run x).paid = 0), T = R.readout () () (T.run x).output

private theorem actual_law : arena.Law actual := by
  exact @ReadTree.leaf_of_paid_zero

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h (.leaf none) (fun _ => false) (by decide)
  simpa [rejected, realize] using hb

def evidence : Registration arena (type_of% (@ReadTree.leaf_of_paid_zero)) where
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
    simp [actual, realize]

end LeafFromZero

namespace UnfoldHeight

abbrev signature : Signature where
  Params := Unit
  State p := ReadTree
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ T => T.height) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {U : Type u} [MeasurableSpace U] (Q : RawRule U) (k : ℕ) (u : U) (r : Record), R.readout () () (Q.unfold k u r) ≤ k

private theorem actual_law : arena.{u}.Law actual := by
  exact @RawRule.unfold_height.{u}

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let T : ULift.{u} Unit → ReadTree := fun _ => .leaf none
  have hb := h (RawRule.realize T) 0 (ULift.up ()) []
  norm_num [rejected, realize] at hb

def evidence : Registration arena.{u} (type_of% (@RawRule.unfold_height.{u})) where
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

end UnfoldHeight

namespace NormalizeRealized

abbrev signature : Signature where
  Params := Unit
  State p := ReadTree
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ T => T.height) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {U : Type u} [MeasurableSpace U] (T : U → ReadTree) (k : ℕ) (u : U) (hT : R.readout () () (T u) ≤ k), (RawRule.realize T).normalize k u = T u

private theorem actual_law : arena.{u}.Law actual := by
  exact @RawRule.normalize_realize.{u}

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let T : ULift.{u} Unit → ReadTree := fun _ => .read 0 (.leaf none) (.leaf none)
  have hb := h T 0 (ULift.up ()) (by change 0 ≤ 0; decide)
  change ReadTree.leaf none = ReadTree.read 0 (.leaf none) (.leaf none) at hb
  cases hb

def evidence : Registration arena.{u} (type_of% (@RawRule.normalize_realize.{u})) where
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

end NormalizeRealized

namespace RealizedCap

abbrev signature : Signature where
  Params := Unit
  State p := ReadTree
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ T => T.height) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {U : Type u} [MeasurableSpace U] (T : U → ReadTree) (k : ℕ) (hT : ∀ u, R.readout () () (T u) ≤ k), (RawRule.realize T).TotalCap k

private theorem actual_law : arena.{u}.Law actual := by
  exact @RawRule.realize_cap.{u}

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let T : ULift.{u} Unit → ReadTree := fun _ => .read 0 (.leaf none) (.leaf none)
  have hb := h T 0 (fun _ => by change 0 ≤ 0; decide)
  have ht := ((RawRule.realize T).normalization_pointwise 0 hb false (fun _ => false) (ULift.up ())).1.2
  change EventKind.read 0 = EventKind.terminal none at ht
  cases ht

def evidence : Registration arena.{u} (type_of% (@RawRule.realize_cap.{u})) where
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

end RealizedCap

namespace PointwiseOutput

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
  Law R := ∀ {U : Type u} [MeasurableSpace U] (Q : RawRule U) (k : ℕ) (hc : Q.TotalCap k) (φ : Bool) (S : Spins) (u : U), let v := (Q.normalize k u).run (visible φ S)
    Q.Completes u (visible φ S) v ∧ Q.output u (visible φ S) = R.readout () () v ∧ Q.paidCount u (visible φ S) = v.paid

private theorem actual_law : arena.{u}.Law actual := by
  exact @RawRule.normalization_pointwise.{u}

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let T : ULift.{u} Unit → ReadTree := fun _ => .leaf (some (.a false))
  let Q : RawRule (ULift.{u} Unit) := RawRule.realize T
  have hc : Q.TotalCap 0 := RawRule.realize_cap T 0 (fun _ => by rfl)
  have hs := Q.normalization_pointwise 0 hc false (fun _ => false) (ULift.up ())
  have ho := hs.2.1
  change Q.output (ULift.up ()) (visible false (fun _ => false)) = some (.a false) at ho
  have hb := (h Q 0 hc false (fun _ => false) (ULift.up ())).2.1
  rw [ho] at hb
  simpa [rejected, realize] using hb

def evidence : Registration arena.{u} (type_of% (@RawRule.normalization_pointwise.{u})) where
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

end PointwiseOutput

namespace UnfoldTerminal

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
  Law R := ∀ {U : Type u} [MeasurableSpace U] (Q : RawRule U) (u : U) (x : ℤ → Bool) (k n : ℕ) (r : Record)
    (hr : Q.readPrefix u x n = some r)
    (hc : ∀ m s, Q.readPrefix u x m = some s → m ≤ n + k),
    let v := (Q.unfold k u r).run x
    Q.readPrefix u x (n + v.paid) = some (r ++ v.record) ∧
      Q.next u (r ++ v.record) = .terminal (R.readout () () v)

private theorem actual_law : arena.{u}.Law actual := by
  exact @RawRule.unfold_correct.{u}

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let Q : RawRule (ULift.{u} Unit) := ⟨(fun _ _ => .terminal (some (.a false))), (fun _ _ => 0)⟩
  have hc : ∀ m s, Q.readPrefix (ULift.up ()) (fun _ => false) m = some s → m ≤ 0 + 0 := by
    intro m s hs
    cases m with
    | zero => omega
    | succ m => simp [RawRule.readPrefix, Q] at hs
  have hb := (h Q (ULift.up ()) (fun _ => false) 0 0 [] rfl hc).2
  simpa [rejected, realize, Q] using hb

def evidence : Registration arena.{u} (type_of% (@RawRule.unfold_correct.{u})) where
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

end UnfoldTerminal

end
end Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SemanticNormalization
