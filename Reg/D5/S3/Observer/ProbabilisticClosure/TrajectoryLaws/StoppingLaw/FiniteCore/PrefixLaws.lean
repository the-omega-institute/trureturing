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

namespace RemoteSourceMass

abbrev signature : Signature where
  Params := Σ _ : Bias, Σ _ : Bool, ReadTree
  State p := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p r => remoteMass p.1 (lawWindow p.2.2) p.2.1 r p.2.2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (β : Bias) (j : Bool) (r : ℕ) (T : ReadTree), (sourceLaw β).real {s | ∃ a ∈ (T.run (visible s.1 s.2)).record, Far j r a.1} = R.readout () ⟨β, j, T⟩ r

private theorem actual_law : arena.Law actual := by
  exact @sourceLaw_remote

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let β : Bias := ⟨1 / 3, by norm_num, by norm_num, by norm_num⟩
  have hb := h β false 0 (.leaf none)
  norm_num [rejected, realize, ReadTree.run] at hb

def evidence : Registration arena (type_of% (@sourceLaw_remote)) where
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
    let T : ReadTree := .read 0 (.leaf none) (.leaf none)
    have he0 (φ : Bool) : remoteEvent T false 0 φ = Set.univ := by
      ext S
      cases hv : visible φ S 0 <;> simp [remoteEvent, T, ReadTree.run, hv, Execution.prepend, Far]
    have he1 (φ : Bool) : remoteEvent T false 1 φ = ∅ := by
      ext S
      cases hv : visible φ S 0 <;> simp [remoteEvent, T, ReadTree.run, hv, Execution.prepend, Far]
    refine ⟨⟨β, false, T⟩, 0, 1, ?_⟩
    change remoteMass β (lawWindow T) false 0 T ≠ remoteMass β (lawWindow T) false 1 T
    have hz : SpinWindow.prob β (lawWindow T) ∅ = 0 := by simp [SpinWindow.prob, FiniteSpinLaw.mass]
    simp [remoteMass, he0, he1, hz]

end RemoteSourceMass

namespace MassPhaseA

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
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (β : Bias) (V : Finset ℤ) (j s : Bool) (T : ReadTree) (o : Option Hidden) (n : ℕ), fullMass β V j T ⟨.a s, o, o.isSome, n⟩ = R.readout () ⟨β, V⟩ {S | S (targetIndex j j) = s ∧ (T.run (visible j S)).output = o ∧ (T.run (visible j S)).paid = n} / 2

private theorem actual_law : arena.Law actual := by
  exact @ReadTree.fullMass_a

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let β : Bias := ⟨1 / 3, by norm_num, by norm_num, by norm_num⟩
  have hb := h β ∅ false false (.leaf none) (some (.a false)) 0
  have hs := ReadTree.fullMass_a β ∅ false false (.leaf none) (some (.a false)) 0
  norm_num [ReadTree.run, SpinWindow.prob, FiniteSpinLaw.mass] at hs
  norm_num [rejected, realize] at hb
  rw [hs] at hb
  norm_num at hb

def evidence : Registration arena (type_of% (@ReadTree.fullMass_a)) where
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

end MassPhaseA

namespace MassPhaseB

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
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (β : Bias) (V : Finset ℤ) (j s : Bool) (T : ReadTree) (o : Option Hidden) (n : ℕ), fullMass β V j T ⟨.b s, o, o.isSome, n⟩ = R.readout () ⟨β, V⟩ {S | S j.toInt = s ∧ (T.run (visible (!j) S)).output = o ∧ (T.run (visible (!j) S)).paid = n} / 2

private theorem actual_law : arena.Law actual := by
  exact @ReadTree.fullMass_b

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let β : Bias := ⟨1 / 3, by norm_num, by norm_num, by norm_num⟩
  have hb := h β ∅ false false (.leaf none) (some (.a false)) 0
  have hs := ReadTree.fullMass_b β ∅ false false (.leaf none) (some (.a false)) 0
  norm_num [ReadTree.run, SpinWindow.prob, FiniteSpinLaw.mass] at hs
  norm_num [rejected, realize] at hb
  rw [hs] at hb
  norm_num at hb

def evidence : Registration arena (type_of% (@ReadTree.fullMass_b)) where
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

end MassPhaseB

namespace PrefixAntitone

abbrev signature : Signature where
  Params := Unit
  State p := Finset ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Set Spins
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ E => SpinWindow.zeroEdges E) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => Set.univ) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (es : List ℤ) {r t : ℕ} (hrt : r ≤ t), R.readout () () (es.take t).toFinset ⊆ SpinWindow.zeroEdges (es.take r).toFinset

private theorem actual_law : arena.Law actual := by
  exact @SpinWindow.zero_prefix_antitone

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let S : Spins := fun e => decide (e = 0)
  have hb := h [0] (r := 1) (t := 1) (by decide) (by trivial : S ∈ rejected.readout () () (([0] : List ℤ).take 1).toFinset)
  have hc := hb 0 (by simp)
  norm_num [S] at hc

def evidence : Registration arena (type_of% (@SpinWindow.zero_prefix_antitone)) where
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
    refine ⟨(), (∅ : Finset ℤ), {0}, ?_⟩
    let S : Spins := fun e => decide (e = 0)
    intro he
    have hm : S ∈ actual.readout () () ∅ := by simp [actual, realize, SpinWindow.zeroEdges]
    rw [he] at hm
    have hc := hm 0 (by simp)
    norm_num [S] at hc

end PrefixAntitone

namespace EdgeDifference

abbrev signature : Signature where
  Params := Unit
  State p := Finset ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Set Spins
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ E => SpinWindow.zeroEdges E) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => ∅) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (es : List ℤ) (φ : Bool) (r : ℕ) (hr : r < es.length),
    R.readout () () (es.take r).toFinset \ SpinWindow.zeroEdges (es.take (r + 1)).toFinset =
      {S | ((ReadTree.edgeComb es φ).run (visible φ S)).output = some (.a true) ∧
        ((ReadTree.edgeComb es φ).run (visible φ S)).paid = r + 1}

private theorem actual_law : arena.Law actual := by
  exact @SpinWindow.zero_edge_difference

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let S : Spins := fun e => decide (e = 0)
  have hb := h [0] false 0 (by decide)
  have hm : S ∈ {S | ((ReadTree.edgeComb [0] false).run (visible false S)).output = some (.a true) ∧ ((ReadTree.edgeComb [0] false).run (visible false S)).paid = 0 + 1} := by
    norm_num [S, ReadTree.edgeComb, ReadTree.stopComb, ReadTree.run, visible, Execution.prepend, Execution.paid]
  rw [← hb] at hm
  simpa [rejected, realize] using hm

def evidence : Registration arena (type_of% (@SpinWindow.zero_edge_difference)) where
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
    refine ⟨(), (∅ : Finset ℤ), {0}, ?_⟩
    let S : Spins := fun e => decide (e = 0)
    intro he
    have hm : S ∈ actual.readout () () ∅ := by simp [actual, realize, SpinWindow.zeroEdges]
    rw [he] at hm
    have hc := hm 0 (by simp)
    norm_num [S] at hc

end EdgeDifference

namespace RemotePrefix

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
  Law R := ∀ (j : Bool) (r : ℕ) (pre : List ℤ) (t : ℤ) (post : List ℤ)
    (hn : ∀ a ∈ pre, ¬Far j r a) (hf : Far j r t) (x : ℤ → Bool),
    (∃ a ∈ ((R.readout () () (pre ++ t :: post)).run x).record, Far j r a.1) ↔ ReadTree.ZeroReplies pre pre.length x

private theorem actual_law : arena.Law actual := by
  exact @ReadTree.remote_iff_first_prefix

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h false 0 [] 0 [] (by simp) (by norm_num [Far]) (fun _ => false)
  simpa [rejected, realize, ReadTree.run, ReadTree.ZeroReplies] using hb

def evidence : Registration arena (type_of% (@ReadTree.remote_iff_first_prefix)) where
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

end RemotePrefix

namespace OppositeRemote

abbrev signature : Signature where
  Params := Σ _ : Bool, ℕ
  State p := ReadTree
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Set Spins
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p T => remoteEvent T p.1 p.2 p.1) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => ∅) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (es : List ℤ) (j : Bool) (r : ℕ) (hf : ∃ t ∈ es.map (fun e => 2 * e + (!j).toInt), Far j r t), R.readout () ⟨j, r⟩ (ReadTree.edgeComb es (!j)) = Set.univ

private theorem actual_law : arena.Law actual := by
  exact @ReadTree.edgeComb_opposite_remote

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h [0] false 0 ⟨1, by simp, by norm_num [Far]⟩
  have he : (∅ : Set Spins) = Set.univ := by simpa [rejected, realize] using hb
  have hc := congrArg (fun E : Set Spins => (fun _ => false) ∈ E) he
  simpa using hc


def evidence : Registration arena (type_of% (@ReadTree.edgeComb_opposite_remote)) where
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
    refine ⟨⟨false, 0⟩, .leaf none, .read 0 (.leaf none) (.leaf none), ?_⟩
    intro he
    have hm : (fun _ => false) ∈ actual.readout () ⟨false, 0⟩ (.read 0 (.leaf none) (.leaf none)) := by
      change ∃ a ∈ ((ReadTree.read 0 (.leaf none) (.leaf none)).run (visible false (fun _ => false))).record, Far false 0 a.1
      refine ⟨(0, false), ?_, by norm_num [Far]⟩
      simp [ReadTree.run, Execution.prepend, visible]
    rw [← he] at hm
    simpa [actual, realize, remoteEvent, ReadTree.run] using hm

end OppositeRemote

end
end Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.FiniteCore
