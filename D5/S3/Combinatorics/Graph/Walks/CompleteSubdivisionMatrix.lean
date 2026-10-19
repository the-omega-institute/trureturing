/- GID: D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionMatrix
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Walks/CompleteSubdivisionMatrix
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Algebra.BigOperators.Fin]
   utility: none
   digest: Diagonal-aware binary symmetric matrices with ranked row sums are staircases. -/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.Walks.CompleteSubdivisionMatrix

/-- The diagonal is an ordinary binary entry and is not constrained to vanish. -/
theorem ranked_staircase (n : ℕ) (C : Fin n → Fin n → ℕ)
    (symm : ∀ i j, C i j = C j i) (binary : ∀ i j, C i j ≤ 1)
    (rows : ∀ i, ∑ j, C i j = i.val) :
    ∀ i j, C i j = if n ≤ i.val + j.val then 1 else 0 := by
  classical
  induction n using Nat.twoStepInduction with
  | zero => exact fun i => Fin.elim0 i
  | one =>
    intro i j
    have hi : i = 0 := Subsingleton.elim _ _
    have hj : j = 0 := Subsingleton.elim _ _
    subst i; subst j
    simpa using rows 0
  | more n ih _ =>
    have row0 (j : Fin (n + 2)) : C 0 j = 0 := by
      have hle := Finset.single_le_sum (f := C 0) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
      have hr := rows 0
      simp only [Fin.val_zero] at hr
      omega
    have col0 (i : Fin (n + 2)) : C i 0 = 0 := by rw [symm, row0]
    have last (j : Fin (n + 2)) :
        C (Fin.last (n + 1)) j = if j = 0 then 0 else 1 := by
      have bound (j : Fin (n + 2)) :
          C (Fin.last (n + 1)) j ≤ if j = 0 then 0 else 1 := by
        split_ifs with hj
        · subst j; rw [col0]
        · exact binary _ _
      have total : (∑ j : Fin (n + 2), if j = 0 then (0 : ℕ) else 1) = n + 1 := by
        rw [Fin.sum_univ_succ]
        simp
      have heq : (∑ j, C (Fin.last (n + 1)) j) =
          ∑ j : Fin (n + 2), if j = 0 then (0 : ℕ) else 1 := by
        rw [rows, total]; rfl
      exact (Finset.sum_eq_sum_iff_of_le (fun j _ => bound j)).mp heq j (Finset.mem_univ j)
    have lastcol (i : Fin (n + 2)) :
        C i (Fin.last (n + 1)) = if i = 0 then 0 else 1 := by rw [symm, last]
    let emb : Fin n → Fin (n + 2) := fun i => i.castSucc.succ
    let D : Fin n → Fin n → ℕ := fun i j => C (emb i) (emb j)
    have drows (i : Fin n) : ∑ j, D i j = i.val := by
      have hr := rows (emb i)
      rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc] at hr
      have hlast : (Fin.last n).succ = Fin.last (n + 1) := rfl
      rw [col0, hlast, lastcol, if_neg (Fin.succ_ne_zero _)] at hr
      dsimp [D, emb] at *
      omega
    have core := ih D (fun i j => symm (emb i) (emb j))
      (fun i j => binary (emb i) (emb j)) drows
    intro i j
    by_cases hi0 : i = 0
    · subst i; rw [row0]; simp
    by_cases hj0 : j = 0
    · subst j; rw [col0]; simp
    by_cases hil : i = Fin.last (n + 1)
    · subst i
      rw [last, if_neg hj0, if_pos]
      have : j.val ≠ 0 := fun h => hj0 (Fin.ext h)
      simp only [Fin.val_last]
      omega
    by_cases hjl : j = Fin.last (n + 1)
    · subst j
      rw [lastcol, if_neg hi0, if_pos]
      have : i.val ≠ 0 := fun h => hi0 (Fin.ext h)
      simp only [Fin.val_last]
      omega
    have hib : i.val - 1 < n := by
      have := i.isLt
      have : i.val ≠ n + 1 := fun h => hil (Fin.ext h)
      have : i.val ≠ 0 := fun h => hi0 (Fin.ext h)
      omega
    have hjb : j.val - 1 < n := by
      have := j.isLt
      have : j.val ≠ n + 1 := fun h => hjl (Fin.ext h)
      have : j.val ≠ 0 := fun h => hj0 (Fin.ext h)
      omega
    let a : Fin n := ⟨i.val - 1, hib⟩
    let b : Fin n := ⟨j.val - 1, hjb⟩
    have hia : emb a = i := by
      apply Fin.ext
      dsimp [emb, a]
      have : i.val ≠ 0 := fun h => hi0 (Fin.ext h)
      omega
    have hjb' : emb b = j := by
      apply Fin.ext
      dsimp [emb, b]
      have : j.val ≠ 0 := fun h => hj0 (Fin.ext h)
      omega
    have hc := core a b
    change C (emb a) (emb b) = _ at hc
    rw [hia, hjb'] at hc
    have threshold : n ≤ a.val + b.val ↔ n + 2 ≤ i.val + j.val := by
      dsimp [a, b]
      have : i.val ≠ 0 := fun h => hi0 (Fin.ext h)
      have : j.val ≠ 0 := fun h => hj0 (Fin.ext h)
      omega
    simpa only [threshold] using hc

theorem row_sum_le (n : ℕ) (C : Fin n → Fin n → ℕ)
    (binary : ∀ i j, C i j ≤ 1) (i : Fin n) : ∑ j, C i j ≤ n := by
  calc
    _ ≤ ∑ _j : Fin n, 1 := Finset.sum_le_sum (fun j _ => binary i j)
    _ = n := by simp

theorem zero_full_incompatible (n : ℕ) (C : Fin n → Fin n → ℕ)
    (symm : ∀ i j, C i j = C j i) (binary : ∀ i j, C i j ≤ 1)
    (u x : Fin n) (hz : ∑ j, C u j = 0) (hf : ∑ j, C x j = n) : False := by
  have zero : C u x = 0 := by
    have := Finset.single_le_sum (f := C u) (fun _ _ => Nat.zero_le _) (Finset.mem_univ x)
    omega
  have full : C x u = 1 := by
    have total : (∑ j, C x j) = ∑ _j : Fin n, 1 := by simpa using hf
    exact (Finset.sum_eq_sum_iff_of_le (fun j _ => binary x j)).mp total u (Finset.mem_univ u)
  rw [symm] at zero
  omega

theorem distinct_rows_extreme (n : ℕ) (hn : 0 < n) (C : Fin n → Fin n → ℕ)
    (binary : ∀ i j, C i j ≤ 1) (hinj : Function.Injective (fun i => ∑ j, C i j)) :
    (∃ u, ∑ j, C u j = 0) ∨ (∃ u, ∑ j, C u j = n) := by
  classical
  by_cases hz : ∃ u, ∑ j, C u j = 0
  · exact Or.inl hz
  · right
    have pos (i : Fin n) : 0 < ∑ j, C i j := by
      have : (∑ j, C i j) ≠ 0 := fun h => hz ⟨i, h⟩
      omega
    let rank : Fin n → Fin n := fun i =>
      ⟨(∑ j, C i j) - 1, by have := row_sum_le n C binary i; have := pos i; omega⟩
    have injective : Function.Injective rank := by
      intro i j hij
      apply hinj
      change (∑ k, C i k) = ∑ k, C j k
      have h := congrArg Fin.val hij
      have := pos i
      have := pos j
      change (∑ k, C i k) - 1 = (∑ k, C j k) - 1 at h
      omega
    have surj := Finite.surjective_of_injective injective
    obtain ⟨u, hu⟩ := surj ⟨n - 1, by omega⟩
    refine ⟨u, ?_⟩
    have h := congrArg Fin.val hu
    have := pos u
    dsimp [rank] at h
    omega

/-- Rank relabeling is a proved permutation of the entire original vertex set. -/
theorem zero_row_normal_form (n : ℕ) (C : Fin n → Fin n → ℕ)
    (symm : ∀ i j, C i j = C j i) (binary : ∀ i j, C i j ≤ 1)
    (hinj : Function.Injective (fun i => ∑ j, C i j))
    (hz : ∃ u, ∑ j, C u j = 0) :
    ∃ e : Fin n ≃ Fin n, (∀ i, ∑ j, C (e i) j = i.val) ∧
      ∀ i j, C (e i) (e j) = if n ≤ i.val + j.val then 1 else 0 := by
  classical
  obtain ⟨u, hu⟩ := hz
  have bound (i : Fin n) : (∑ j, C i j) < n := by
    have := row_sum_le n C binary i
    have : (∑ j, C i j) ≠ n := fun hf => zero_full_incompatible n C symm binary u i hu hf
    omega
  let rank : Fin n → Fin n := fun i => ⟨∑ j, C i j, bound i⟩
  have injective : Function.Injective rank := fun i j h => hinj (congrArg Fin.val h)
  let r : Fin n ≃ Fin n := Equiv.ofBijective rank
    ⟨injective, Finite.surjective_of_injective injective⟩
  have ranks (i : Fin n) : (∑ j, C (r.symm i) j) = i.val :=
    congrArg Fin.val (r.apply_symm_apply i)
  refine ⟨r.symm, ranks, ?_⟩
  apply ranked_staircase n (fun i j => C (r.symm i) (r.symm j))
    (fun i j => symm _ _) (fun i j => binary _ _)
  intro i
  rw [Equiv.sum_comp r.symm]
  exact ranks i

end D5.S3.Combinatorics.Graph.Walks.CompleteSubdivisionMatrix
