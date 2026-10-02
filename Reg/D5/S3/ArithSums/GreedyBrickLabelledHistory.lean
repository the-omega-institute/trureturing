import D5.S3.ArithSums.GreedyBrickLabelledHistory
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.ArithSums.GreedyBrickCapacityTotality
open _root_.D5.S3.ArithSums.GreedyBrickLabelledHistory

namespace Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory

namespace Continuous

abbrev signature : Signature where
  Params := ℕ
  State := fun _ => List ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => List ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ n ws => sourceRowStep n ws) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ), 0 < n → ∀ (ws : List ℕ), ws.Pairwise (· ≤ ·) →
    ∃ x y : ℕ, PlacementSite n ws x y ∧
      sourceOptimal n ws (x : ℝ) (y : ℝ) ∧
      ∀ t z, wall (R.readout () n ws) t z ↔
        wall ws t z ∨ rectangle n (x : ℝ) (y : ℝ) t z

def rejected : Realization signature := realize signature
  (fun _ _ _ => []) (fun e => nomatch e)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨x, y, hs, _, hu⟩ := h 1 (by omega) [] (by simp)
  have hxy : x = 0 ∧ y = 0 := by simpa [PlacementSite, AppendSite] using hs
  rcases hxy with ⟨rfl, rfl⟩
  have hw := (hu 0 0).mpr (Or.inr (by norm_num [rectangle]))
  rcases hw with ⟨k, _, _, ht, hk⟩
  simp [rejected, realize, rowEnd] at hk

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨continuous_row_geometry, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    cases i
    exact ⟨1, [], [2], by decide⟩

def selection : LeanInformationAudit.SourceSelection := {
  owner := `D5.S3.ArithSums.GreedyBrickLabelledHistory
  coordinates := #[0]
  readouts := #[{
    path := #["body", "body", "body", "body", "arg", "body", "arg", "body",
      "arg", "arg", "body", "body", "fn", "arg", "fn", "fn", "arg"]
    stateBinder := 2 }] }

register_information_theorem continuous_row_geometry in arena
  readout via (realize signature (fun _ n ws => sourceRowStep n ws) (fun e => nomatch e))
  realizes registration
  escape from source (selection)
  escape continues (open)

#print axioms registration

end Continuous

namespace History

abbrev signature : Signature where
  Params := Unit
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => List ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ N => widths (trajectory N)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∃ pos : ℕ → ℕ × ℕ,
    (∀ N t z, wall (R.readout () () N) t z ↔ labelledWall pos N t z) ∧
    (∀ n, 0 < n → historyOptimal pos (n - 1) n (pos n).1 (pos n).2) ∧
    (∀ n, 0 < n → closedSupport pos (n - 1) n (pos n).1 (pos n).2) ∧
    (∀ i j, 0 < i → i < j → ∀ t z,
      rectangle i (pos i).1 (pos i).2 t z →
      ¬ rectangle j (pos j).1 (pos j).2 t z)

def rejected : Realization signature := realize signature
  (fun _ _ _ => []) (fun e => nomatch e)

theorem rejected_law : ¬ arena.Law rejected := by
  rintro ⟨pos, hu, _⟩
  have hr : rectangle 1 (pos 1).1 (pos 1).2 (pos 1).1 (pos 1).2 := by
    simp [rectangle]
  have hw := (hu 1 (pos 1).1 (pos 1).2).mpr ⟨1, by omega, le_rfl, hr⟩
  rcases hw with ⟨k, _, _, ht, hk⟩
  simp [rejected, realize, rowEnd] at hk
  have ht0 : (0 : ℝ) ≤ (pos 1).1 := Nat.cast_nonneg _
  linarith

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_labelled_history, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    cases i
    exact ⟨(), 0, 1, by decide⟩

def selection : LeanInformationAudit.SourceSelection := {
  owner := `D5.S3.ArithSums.GreedyBrickLabelledHistory
  coordinates := #[]
  readouts := #[{
    path := #["arg", "body", "fn", "arg", "body", "body", "body",
      "fn", "arg", "fn", "fn", "arg"]
    stateBinder := 1 }] }

register_information_theorem actual_labelled_history in arena
  readout via (realize signature
    (fun _ _ N => widths (trajectory N)) (fun e => nomatch e))
  realizes registration
  escape from source (selection)
  escape continues (open)

#print axioms registration

end History

end Reg.D5.S3.ArithSums.GreedyBrickLabelledHistory
