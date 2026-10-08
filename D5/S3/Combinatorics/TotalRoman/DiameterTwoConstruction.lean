/- GID: D5/S3/Combinatorics/TotalRoman/DiameterTwoConstruction
   generality: G
   mirror-B: D5/B/S3/Combinatorics/TotalRoman/DiameterTwoConstruction
   mirror-E: none(waiver:explicit-clique-expansion)
   anchors: []
   utility: none
   digest: Clique expansions with domination obstructions and edge-repair certificates. -/

import D5.S3.Combinatorics.TotalRoman.DiameterTwoDefs
import D5.S3.Combinatorics.TotalRoman.SupercriticalBasics

set_option autoImplicit false
set_option maxRecDepth 4096

namespace D5.S3.Combinatorics.TotalRoman.DiameterTwoConstruction

open SupercriticalDefs SupercriticalBasics

/-- The seed's twenty absent unordered edges. -/
def missing : Finset (ℕ × ℕ) :=
  {(0, 1), (0, 2), (0, 4), (0, 6), (0, 7), (0, 8), (1, 5), (1, 6),
   (2, 4), (2, 7), (3, 4), (3, 5), (3, 7), (3, 9), (4, 5), (5, 6),
   (6, 8), (6, 9), (7, 9), (8, 9)}

/-- The ten-vertex seed, specified without graph-isomorphism choices. -/
def seed : SimpleGraph (Fin 10) where
  Adj i j := i ≠ j ∧ (i.val, j.val) ∉ missing ∧ (j.val, i.val) ∉ missing
  symm := ⟨by intro i j h; exact ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨by intro i h; exact h.1 rfl⟩

instance seedDecidable : DecidableRel seed.Adj := fun i j =>
  inferInstanceAs (Decidable (i ≠ j ∧ (i.val, j.val) ∉ missing ∧ (j.val, i.val) ∉ missing))

/-- Every extra vertex belongs to the clique replacing vertex 1. -/
def project {n : ℕ} (x : Fin n) : Fin 10 :=
  if h : x.val < 10 then ⟨x.val, h⟩ else 1

/-- Adjacent twins over vertex 1, with the other nine fibres unchanged. -/
def family (n : ℕ) : SimpleGraph (Fin n) where
  Adj x y := x ≠ y ∧ (project x = project y ∨ seed.Adj (project x) (project y))
  symm := ⟨by
    intro x y h
    exact ⟨h.1.symm, h.2.elim (fun e => Or.inl e.symm) (fun e => Or.inr e.symm)⟩⟩
  loopless := ⟨by intro x h; exact h.1 rfl⟩

theorem project_rep {n : ℕ} (hn : 10 ≤ n) (i : Fin 10) :
    project (Fin.castLE hn i) = i := by
  simp [project, Fin.val_castLE, i.isLt]

theorem singleton {n : ℕ} (hn : 10 ≤ n) (x : Fin n) (i : Fin 10)
    (hi : i ≠ 1) (hx : project x = i) : x = Fin.castLE hn i := by
  unfold project at hx
  split_ifs at hx with h
  · apply Fin.ext
    change x.val = i.val
    exact congrArg Fin.val hx
  · exact False.elim (hi hx.symm)

theorem lift_adj {n : ℕ} {x y : Fin n} (h : seed.Adj (project x) (project y)) :
    (family n).Adj x y := by
  refine ⟨?_, Or.inr h⟩
  intro e
  subst y
  exact seed.irrefl h

/-- A total dominating set yields the function assigning two exactly on that set. -/
theorem doubled_bound {V : Type*} [Fintype V]
    (G : SimpleGraph V) (D : Finset V) (hD : ∀ v, ∃ u ∈ D, G.Adj v u) :
    gammaTR G ≤ 2 * D.card := by
  classical
  let f : V → ℕ := fun v => if v ∈ D then 2 else 0
  have hf : IsTRDF G f := by
    refine ⟨?_, ?_, ?_⟩
    · intro v; simp only [f]; split_ifs <;> omega
    · intro v _
      obtain ⟨u, hu, hvu⟩ := hD v
      exact ⟨u, hvu, by simp [f, hu]⟩
    · intro v _
      obtain ⟨u, hu, hvu⟩ := hD v
      exact ⟨u, hvu, by simp [f, hu]⟩
  have hs : (∑ v, f v) = 2 * D.card := by
    simp [f, Nat.mul_comm]
  exact hs ▸ le_weight hf

/-- No ordinary pair dominates any member of the family. -/
theorem obstruction {n : ℕ} (hn : 10 ≤ n) (a b : Fin n) :
    ∃ w, w ≠ a ∧ w ≠ b ∧ ¬ (family n).Adj w a ∧ ¬ (family n).Adj w b := by
  have hc : ∀ i j : Fin 10, ∃ k : Fin 10,
      k ≠ i ∧ k ≠ j ∧ ¬ seed.Adj k i ∧ ¬ seed.Adj k j := by decide
  obtain ⟨k, hki, hkj, hka, hkb⟩ := hc (project a) (project b)
  have hp := project_rep hn k
  refine ⟨Fin.castLE hn k, ?_, ?_, ?_, ?_⟩
  · intro e; exact hki (by rw [← hp, e])
  · intro e; exact hkj (by rw [← hp, e])
  · rintro ⟨_, h | h⟩
    · exact hki (hp ▸ h)
    · exact hka (hp ▸ h)
  · rintro ⟨_, h | h⟩
    · exact hkj (hp ▸ h)
    · exact hkb (hp ▸ h)

/-- The unchanged vertices 0, 3 and 6 totally dominate every expansion. -/
theorem total_domination {n : ℕ} (hn : 10 ≤ n) :
    ∀ x : Fin n, ∃ u ∈ ({Fin.castLE hn 0, Fin.castLE hn 3, Fin.castLE hn 6} : Finset (Fin n)),
      (family n).Adj x u := by
  have hc : ∀ i : Fin 10, seed.Adj i 0 ∨ seed.Adj i 3 ∨ seed.Adj i 6 := by decide
  intro x
  rcases hc (project x) with h | h | h
  · exact ⟨Fin.castLE hn 0, by simp, lift_adj (by simpa [project_rep] using h)⟩
  · exact ⟨Fin.castLE hn 3, by simp, lift_adj (by simpa [project_rep] using h)⟩
  · exact ⟨Fin.castLE hn 6, by simp, lift_adj (by simpa [project_rep] using h)⟩

end D5.S3.Combinatorics.TotalRoman.DiameterTwoConstruction
