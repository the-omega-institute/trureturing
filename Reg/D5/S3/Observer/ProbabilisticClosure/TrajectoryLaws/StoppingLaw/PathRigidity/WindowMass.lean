import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.PathRigidity
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.PathRigidity

open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

namespace VertexCount

abbrev signature : Signature where
  Params := ℤ
  State p := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ L n => (pathVertices L n).card) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (L : ℤ) (n : ℕ), R.readout () L n = n + 1

private theorem actual_law : arena.Law actual := by
  exact @vertices_card

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 0 0
  simpa [rejected, realize] using hb

def evidence : Registration arena (type_of% (@vertices_card)) where
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
    refine ⟨0, 0, 1, ?_⟩
    change (pathVertices 0 0).card ≠ (pathVertices 0 1).card
    rw [vertices_card, vertices_card]
    omega

end VertexCount

namespace WholeWindow

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
  Law R := ∀ (β : Bias) (V : Finset ℤ), R.readout () ⟨β, V⟩ Set.univ = 1

private theorem actual_law : arena.Law actual := by
  exact @SpinWindow.prob_univ

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let β : Bias := ⟨1 / 3, by norm_num, by norm_num, by norm_num⟩
  have hb := h β ∅
  simpa [rejected, realize] using hb

def evidence : Registration arena (type_of% (@SpinWindow.prob_univ)) where
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

end WholeWindow

namespace UnionMass

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
  Law R := ∀ (β : Bias) (V : Finset ℤ) {E F : Set Spins} (h : Disjoint E F), R.readout () ⟨β, V⟩ (E ∪ F) = SpinWindow.prob β V E + SpinWindow.prob β V F

private theorem actual_law : arena.Law actual := by
  exact @SpinWindow.prob_union

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let β : Bias := ⟨1 / 3, by norm_num, by norm_num, by norm_num⟩
  have hb := h β ∅ (E := Set.univ) (F := ∅) (by simp)
  rw [SpinWindow.prob_univ] at hb
  simpa [rejected, realize, SpinWindow.prob, FiniteSpinLaw.mass] using hb

def evidence : Registration arena (type_of% (@SpinWindow.prob_union)) where
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

end UnionMass

namespace DifferenceMass

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
  Law R := ∀ (β : Bias) (V : Finset ℤ) {E F : Set Spins} (h : F ⊆ E), R.readout () ⟨β, V⟩ (E \ F) = SpinWindow.prob β V E - SpinWindow.prob β V F

private theorem actual_law : arena.Law actual := by
  exact @SpinWindow.prob_diff

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let β : Bias := ⟨1 / 3, by norm_num, by norm_num, by norm_num⟩
  have hb := h β ∅ (E := Set.univ) (F := ∅) (by simp)
  rw [SpinWindow.prob_univ] at hb
  simpa [rejected, realize, SpinWindow.prob, FiniteSpinLaw.mass] using hb

def evidence : Registration arena (type_of% (@SpinWindow.prob_diff)) where
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

end DifferenceMass

namespace PositiveMass

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
  Law R := ∀ (β : Bias) (V : Finset ℤ) (E : Set Spins), 0 < R.readout () ⟨β, V⟩ E ↔ ∃ σ : V → Bool, SpinWindow.extend V σ ∈ E

private theorem actual_law : arena.Law actual := by
  exact @SpinWindow.prob_pos_iff

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let β : Bias := ⟨1 / 3, by norm_num, by norm_num, by norm_num⟩
  have hb := (h β ∅ Set.univ).2 ⟨(fun _ => false), trivial⟩
  norm_num [rejected, realize] at hb

def evidence : Registration arena (type_of% (@SpinWindow.prob_pos_iff)) where
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

end PositiveMass

namespace FullMass

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
  Law R := ∀ (β : Bias) (V : Finset ℤ) (E : Set Spins), R.readout () ⟨β, V⟩ E = 1 ↔ ∀ σ : V → Bool, SpinWindow.extend V σ ∈ E

private theorem actual_law : arena.Law actual := by
  exact @SpinWindow.prob_one_iff

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let β : Bias := ⟨1 / 3, by norm_num, by norm_num, by norm_num⟩
  have hb := (h β ∅ Set.univ).2 (fun _ => trivial)
  norm_num [rejected, realize] at hb

def evidence : Registration arena (type_of% (@SpinWindow.prob_one_iff)) where
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

end FullMass

namespace ConstantMass

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
  Law R := ∀ (β : Bias) (V A : Finset ℤ) (hA : A ⊆ V) (s : Bool), R.readout () ⟨β, V⟩ (SpinWindow.constant A s) = (β.π s)^A.card

private theorem actual_law : arena.Law actual := by
  exact @SpinWindow.constant_prob

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let β : Bias := ⟨1 / 3, by norm_num, by norm_num, by norm_num⟩
  have hb := h β ∅ ∅ (by simp) false
  norm_num [rejected, realize] at hb

def evidence : Registration arena (type_of% (@SpinWindow.constant_prob)) where
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

end ConstantMass

namespace BlockMass

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
  Law R := ∀ (β : Bias) (V A B : Finset ℤ) (hA : A ⊆ V) (hB : B ⊆ V) (hd : Disjoint A B) (hne : A.Nonempty) (s : Bool), R.readout () ⟨β, V⟩ (SpinWindow.monoBlock A ∩ SpinWindow.constant B s) = β.T A.card * (β.π s)^B.card

private theorem actual_law : arena.Law actual := by
  exact @SpinWindow.block_constant_prob

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let β : Bias := ⟨1 / 3, by norm_num, by norm_num, by norm_num⟩
  have hb := h β {0} {0} ∅ (by simp) (by simp) (by simp) (by simp) false
  norm_num [rejected, realize, Bias.T] at hb

def evidence : Registration arena (type_of% (@SpinWindow.block_constant_prob)) where
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

end BlockMass

end
end Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.PathRigidity
