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

namespace SourceObservationMass

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
  Law R := ∀ (β : Bias) (j : Bool) (T : ReadTree) (z : Observation), R.readout () β {s | observation j s.1 T s.2 = z} = fullMass β (lawWindow T) j T z

private theorem actual_law : arena.Law actual := by
  exact @sourceLaw_observation

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let β : Bias := ⟨1 / 3, by norm_num, by norm_num, by norm_num⟩
  let z : Observation := ⟨.a false, some (.a false), true, 0⟩
  have hb := h β false (.leaf none) z
  have hs := sourceLaw_observation β false (.leaf none) z
  have he : {s : SourcePoint | observation false s.1 (.leaf none) s.2 = z} = ∅ := by
    ext s
    simp [observation, ReadTree.run, Execution.returned, z]
  rw [he, measureReal_empty] at hs
  rw [← hs] at hb
  norm_num [rejected, realize] at hb

def evidence : Registration arena (type_of% (@sourceLaw_observation)) where
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

end SourceObservationMass

namespace FiniteRigidity

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
  Law R := ∀ (β : Bias) (j : Bool) (k : ℕ) (hk : 1 ≤ k) (T : ReadTree) (hh : T.height ≤ k) (hlaw : HasStoppingLaw β (lawWindow T) j k T),
    ∃ es : List ℤ, es.length = k ∧ es.Nodup ∧ ∃ L : ℤ,
      T = R.readout () () (es.map (fun e => 2 * e + (!j).toInt)) ∧ es.toFinset = pathEdges L k ∧ j.toInt ∉ pathVertices L k

private theorem actual_law : arena.Law actual := by
  exact @finite_full_law_forces_stopping_path

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let β : Bias := ⟨1 / 3, by norm_num, by norm_num, by norm_num⟩
  let T := witnessTree false 1
  have hh : T.height ≤ 1 := by simp [T, witnessTree, ReadTree.edgeComb, witnessEdges]
  have hlaw : HasStoppingLaw β (lawWindow T) false 1 T := witness_canonical_law β false 1 (by decide)
  obtain ⟨es, _, _, L, he, _, _⟩ := h β false 1 (by decide) T hh hlaw
  change ReadTree.read 3 (.leaf (some (.a false))) (.leaf (some (.a true))) = ReadTree.leaf none at he
  cases he

def evidence : Registration arena (type_of% (@finite_full_law_forces_stopping_path)) where
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

end FiniteRigidity

namespace ZeroPrefixMass

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
  Law R := ∀ (β : Bias) (V : Finset ℤ) (j : Bool) (es : List ℤ) (hq : j.toInt ∈ V) (hlaw : HasStoppingLaw β V j es.length (ReadTree.edgeComb es (!j))) (r : ℕ) (hr : r ≤ es.length), R.readout () ⟨β, V⟩ (SpinWindow.zeroEdges (es.take r).toFinset) = β.T (r + 1)

private theorem actual_law : arena.Law actual := by
  exact @SpinWindow.zero_prefix_mass

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let β : Bias := ⟨1 / 3, by norm_num, by norm_num, by norm_num⟩
  let T := witnessTree false 1
  have hh : T.height ≤ 1 := by simp [T, witnessTree, ReadTree.edgeComb, witnessEdges]
  have hlaw : HasStoppingLaw β (lawWindow T) false 1 T := witness_canonical_law β false 1 (by decide)
  have hq : false.toInt ∈ lawWindow T := by simp [lawWindow]
  have he : (witnessEdges false 1).length = 1 := by simp [witnessEdges]
  have hl : HasStoppingLaw β (lawWindow T) false (witnessEdges false 1).length (ReadTree.edgeComb (witnessEdges false 1) (!false)) := by simpa [he, T, witnessTree] using hlaw
  have hb := h β (lawWindow T) false (witnessEdges false 1) hq hl 0 (by omega)
  norm_num [rejected, realize, Bias.T] at hb

def evidence : Registration arena (type_of% (@SpinWindow.zero_prefix_mass)) where
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

end ZeroPrefixMass

namespace FiniteRemote

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
  Law R := ∀ (β : Bias) (j : Bool) (k : ℕ) (hk : 1 ≤ k) (T : ReadTree) (hh : T.height ≤ k) (hlaw : HasStoppingLaw β (lawWindow T) j k T),
    ∃ m : ℕ, 1 ≤ m ∧ m ≤ k ∧ R.readout () ⟨β, j, T⟩ (2 * k + 1) = (1 + β.T m) / 2 ∧
      (1 + β.T k) / 2 ≤ remoteMass β (lawWindow T) j (2 * k + 1) T

private theorem actual_law : arena.Law actual := by
  exact @finite_remote_read_section

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let β : Bias := ⟨1 / 3, by norm_num, by norm_num, by norm_num⟩
  let T := witnessTree false 1
  have hh : T.height ≤ 1 := by simp [T, witnessTree, ReadTree.edgeComb, witnessEdges]
  have hlaw : HasStoppingLaw β (lawWindow T) false 1 T := witness_canonical_law β false 1 (by decide)
  obtain ⟨m, hm, hm₁, he, _⟩ := h β false 1 (by decide) T hh hlaw
  have hm : m = 1 := by omega
  subst m
  rw [β.T_one] at he
  norm_num [rejected, realize] at he

def evidence : Registration arena (type_of% (@finite_remote_read_section)) where
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

end FiniteRemote

namespace CappedLaw

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
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (β : Bias) (V : Finset ℤ) (j : Bool) (k : ℕ) (T : ReadTree) (hh : T.height ≤ k), HasStoppingLaw β V j k T ↔ ∀ z : CappedObservation k, fullMass β V j T z.val = R.readout () ⟨β, k⟩ z.val

private theorem actual_law : arena.Law actual := by
  exact @hasStoppingLaw_iff_capped

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let β : Bias := ⟨1 / 3, by norm_num, by norm_num, by norm_num⟩
  let T := witnessTree false 1
  have hh : T.height ≤ 1 := by simp [T, witnessTree, ReadTree.edgeComb, witnessEdges]
  have hlaw : HasStoppingLaw β (lawWindow T) false 1 T := witness_canonical_law β false 1 (by decide)
  let z : CappedObservation 1 := ⟨⟨.a false, none, false, 0⟩, by decide, rfl⟩
  have hb := ((h β (lawWindow T) false 1 T hh).1 hlaw) z
  have hs := sourceLaw_observation β false T z.val
  have hbnd : fullMass β (lawWindow T) false T z.val ≤ 1 := by rw [← hs]; exact measureReal_le_one
  norm_num [rejected, realize] at hb
  linarith

def evidence : Registration arena (type_of% (@hasStoppingLaw_iff_capped)) where
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

end CappedLaw

end
end Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.FiniteCore
