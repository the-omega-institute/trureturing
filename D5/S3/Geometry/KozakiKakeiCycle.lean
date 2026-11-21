/- GID: D5/S3/Geometry/KozakiKakeiCycle
   generality: G
   mirror-B: D5/B/S3/Geometry/KozakiKakeiCycle
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The even cycle is the union of the two oriented matchings and its automorphisms are the cyclic rotations and reflections. -/
import D5.S3.Geometry.KozakiKakeiMatching
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Tactic.Abel

namespace D5.S3.Geometry.KozakiKakei

def step {m : ℕ} (hm : 2 ≤ m) (i : Col m) : Col m := i + second hm

def Adjacent {m : ℕ} (hm : 2 ≤ m) (i j : Col m) : Prop :=
  j = step hm i ∨ i = step hm j

def SameEdge {m : ℕ} (M : Fin m × Bool ≃ Col m) (i j : Col m) : Prop :=
  (M.symm i).1 = (M.symm j).1

theorem step_val {m : ℕ} (hm : 2 ≤ m) (i : Col m) :
    (step hm i).val = if i.val + 1 < 2 * m then i.val + 1 else 0 := by
  have h := i.isLt
  simp only [step, Fin.val_add_eq_ite, second]
  split <;> split <;> omega

theorem step_ne {m : ℕ} (hm : 2 ≤ m) (i : Col m) : step hm i ≠ i := by
  intro h
  have h' := congrArg Fin.val h
  rw [step_val] at h'
  split at h' <;> omega

theorem adjacent_ne {m : ℕ} (hm : 2 ≤ m) {i j : Col m} (h : Adjacent hm i j) : i ≠ j := by
  rintro rfl
  exact (step_ne hm i) (h.elim Eq.symm Eq.symm)

theorem odd_forward {m : ℕ} (hm : 2 ≤ m) (e : Fin m) :
    step hm (oddVertex (e, false)) = oddVertex (e, true) := by
  have h := e.isLt
  apply Fin.ext
  rw [step_val]
  simp only [oddVertex, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
  rw [ite_eq_left (by omega)]

theorem even_forward {m : ℕ} (hm : 2 ≤ m) (e : Fin m) (h : e.val ≠ 0) :
    step hm (evenVertex (e, false)) = evenVertex (e, true) := by
  have he := e.isLt
  apply Fin.ext
  rw [step_val]
  simp [evenVertex, h]
  rw [ite_eq_left (by omega)]
  omega

theorem even_closing {m : ℕ} (hm : 2 ≤ m) (e : Fin m) (h : e.val = 0) :
    step hm (evenVertex (e, true)) = evenVertex (e, false) := by
  apply Fin.ext
  rw [step_val]
  simp [evenVertex, h, show ¬ (2 * m - 1 + 1 < 2 * m) by omega]

theorem sameEdge_iff {m : ℕ} {M : Fin m × Bool ≃ Col m}
    {i j : Col m} (hne : i ≠ j) :
    SameEdge M i j ↔ ∃ e : Fin m,
      (i = M (e, false) ∧ j = M (e, true)) ∨
      (i = M (e, true) ∧ j = M (e, false)) := by
  constructor
  · intro h
    obtain ⟨⟨e, b⟩, rfl⟩ := M.surjective i
    obtain ⟨⟨f, c⟩, rfl⟩ := M.surjective j
    have hef : e = f := by simpa [SameEdge] using h
    subst f
    cases b <;> cases c <;> simp_all
  · rintro ⟨e, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩ <;> simp [SameEdge]

private theorem step_sameEdge {m : ℕ} (hm : 2 ≤ m) (i : Col m) :
    SameEdge (oddMatching m) i (step hm i) ∨ SameEdge (evenMatching m) i (step hm i) := by
  have hi := i.isLt
  by_cases hp : i.val % 2 = 0
  · let e : Fin m := ⟨i.val / 2, by omega⟩
    have he : i = oddVertex (e, false) := by apply Fin.ext; simp [oddVertex, e]; omega
    exact Or.inl ((sameEdge_iff (step_ne hm i).symm).mpr
      ⟨e, Or.inl ⟨he, by rw [he, odd_forward]; rfl⟩⟩)
  · by_cases hend : i.val + 1 < 2 * m
    · let e : Fin m := ⟨(i.val+1) / 2, by omega⟩
      have h₀ : e.val ≠ 0 := by dsimp [e]; omega
      have he : i = evenVertex (e, false) := by
        apply Fin.ext
        simp [evenVertex, h₀, e]
        omega
      exact Or.inr ((sameEdge_iff (step_ne hm i).symm).mpr
        ⟨e, Or.inl ⟨he, by rw [he, even_forward hm e h₀]; rfl⟩⟩)
    · let e : Fin m := ⟨0, by omega⟩
      have he : i = evenVertex (e, true) := by apply Fin.ext; simp [evenVertex, e]; omega
      exact Or.inr ((sameEdge_iff (step_ne hm i).symm).mpr
        ⟨e, Or.inr ⟨he, by rw [he, even_closing hm e rfl]; rfl⟩⟩)

theorem edges_cover {m : ℕ} (hm : 2 ≤ m) {i j : Col m} (hne : i ≠ j) :
    Adjacent hm i j ↔ SameEdge (oddMatching m) i j ∨ SameEdge (evenMatching m) i j := by
  constructor
  · rintro (rfl | rfl)
    · exact step_sameEdge hm i
    · simpa only [SameEdge, eq_comm] using step_sameEdge hm j
  · intro h
    rcases h with h | h
    · obtain ⟨e, hh | hh⟩ := (sameEdge_iff hne).mp h
      · exact Or.inl (hh.2.trans (by rw [hh.1]; exact (odd_forward hm e).symm))
      · exact Or.inr (hh.1.trans (by rw [hh.2]; exact (odd_forward hm e).symm))
    · obtain ⟨e, hh⟩ := (sameEdge_iff hne).mp h
      by_cases hz : e.val = 0
      · rcases hh with hh | hh
        · exact Or.inr (hh.1.trans (by rw [hh.2]; exact (even_closing hm e hz).symm))
        · exact Or.inl (hh.2.trans (by rw [hh.1]; exact (even_closing hm e hz).symm))
      · rcases hh with hh | hh
        · exact Or.inl (hh.2.trans (by rw [hh.1]; exact (even_forward hm e hz).symm))
        · exact Or.inr (hh.1.trans (by rw [hh.2]; exact (even_forward hm e hz).symm))

theorem edges_disjoint {m : ℕ} (hm : 2 ≤ m) {i j : Col m} (hne : i ≠ j)
    (ho : SameEdge (oddMatching m) i j) (he : SameEdge (evenMatching m) i j) : False := by
  obtain ⟨e, ho⟩ := (sameEdge_iff hne).mp ho
  obtain ⟨f, he⟩ := (sameEdge_iff hne).mp he
  have hE := e.isLt
  have hF := f.isLt
  rcases ho with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    rcases he with ⟨he₁, he₂⟩ | ⟨he₁, he₂⟩ <;>
    have h₁ := congrArg Fin.val he₁ <;> have h₂ := congrArg Fin.val he₂ <;>
    by_cases hz : f.val = 0 <;>
    simp [evenMatching, oddMatching, evenVertex, oddVertex, hz] at h₁ h₂ <;> omega

theorem dihedral_of_preserves_adjacency {m : ℕ} (hm : 2 ≤ m) (σ : Equiv.Perm (Col m))
    (h : ∀ i j, Adjacent hm i j → Adjacent hm (σ i) (σ j)) : Dihedral σ := by
  have : NeZero (2 * m) := ⟨by omega⟩
  let u := second hm
  have hu : u + u ≠ (0 : Col m) := by
    intro he
    have hf := congrArg Fin.val he
    simp only [u, second, Fin.val_add_eq_ite, Fin.val_zero] at hf
    split at hf <;> omega
  have local_step (i : Col m) : σ (i + u) = σ i + u ∨ σ (i + u) = σ i - u := by
    rcases h i (i + u) (Or.inl rfl) with hi | hi
    · exact Or.inl hi
    · exact Or.inr (eq_sub_of_add_eq hi.symm)
  have local_orientation (d : Col m) (hd : d = u ∨ d = -u) (i : Col m)
      (hi : σ (i + u) = σ i + d) :
      σ (i + u + u) = σ (i + u) + d := by
    have hnot : σ (i + u + u) ≠ σ i := by
      intro hEq
      have hEq' := σ.injective hEq
      apply hu
      exact add_left_cancel (a := i) (by simpa only [← add_assoc, add_zero] using hEq')
    rcases hd with rfl | rfl
    · rcases local_step (i + u) with hh | hh
      · exact hh
      · exact (hnot (by rw [hh, hi, add_sub_cancel_right])).elim
    · rcases local_step (i + u) with hh | hh
      · exact (hnot (by rw [hh, hi]; abel)).elim
      · simpa [sub_eq_add_neg] using hh
  have extend (d : Col m) (hd : d = u ∨ d = -u)
      (hs : σ (0 + u) = σ 0 + d) :
      ∀ i : Col m, σ (i + u) = σ i + d := by
    have hn : ∀ (k : ℕ) (hk : k < 2*m),
        σ ((⟨k, hk⟩ : Col m) + u) = σ ⟨k, hk⟩ + d := by
      intro k
      induction k with
      | zero =>
        intro hk
        exact hs
      | succ k ih =>
        intro hk
        have he : (⟨k, by omega⟩ : Col m) + u = ⟨k + 1, hk⟩ := by
          apply Fin.ext
          change (step hm ⟨k, by omega⟩).val = k + 1
          rw [step_val, ite_eq_left hk]
        simpa only [he] using local_orientation d hd ⟨k, by omega⟩ (ih (by omega))
    exact fun i => hn i.val i.isLt
  have add_case (ha : ∀ i : Col m, σ (i + u) = σ i + u) :
      ∀ i : Col m, σ i = σ 0 + i := by
    have hn : ∀ (k : ℕ) (hk : k < 2*m), σ ⟨k, hk⟩ = σ 0 + ⟨k, hk⟩ := by
      intro k
      induction k with
      | zero =>
        intro hk
        exact (add_zero _).symm
      | succ k ih =>
        intro hk
        have he : (⟨k, by omega⟩ : Col m) + u = ⟨k + 1, hk⟩ := by
          apply Fin.ext
          change (step hm ⟨k, by omega⟩).val = k + 1
          rw [step_val, ite_eq_left hk]
        rw [← he, ha, ih, add_assoc]
    exact fun i => hn i.val i.isLt
  have sub_case (ha : ∀ i : Col m, σ (i + u) = σ i + (-u)) :
      ∀ i : Col m, σ i = σ 0 - i := by
    have hn : ∀ (k : ℕ) (hk : k < 2*m), σ ⟨k, hk⟩ = σ 0 - ⟨k, hk⟩ := by
      intro k
      induction k with
      | zero =>
        intro hk
        exact (sub_zero _).symm
      | succ k ih =>
        intro hk
        have he : (⟨k, by omega⟩ : Col m) + u = ⟨k + 1, hk⟩ := by
          apply Fin.ext
          change (step hm ⟨k, by omega⟩).val = k + 1
          rw [step_val, ite_eq_left hk]
        rw [← he, ha, ih]
        abel
    exact fun i => hn i.val i.isLt
  refine ⟨σ 0, ?_⟩
  rcases local_step 0 with hs | hs
  · exact Or.inl (add_case (extend u (Or.inl rfl) hs))
  · exact Or.inr (sub_case (extend (-u) (Or.inr rfl) (by simpa [sub_eq_add_neg] using hs)))

#print axioms dihedral_of_preserves_adjacency

end D5.S3.Geometry.KozakiKakei
