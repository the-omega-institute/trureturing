/- GID: D5/S3/Combinatorics/Posets/GradedGamma/SaturatedRuns
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Posets/GradedGamma/SaturatedRuns
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Order.Atoms.Finite]
   utility: none
   digest: Consecutive grade-parity runs of an extension are antichains. -/

import D5.S3.Combinatorics.Posets.GradedGamma.RankParityRuns
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Order.Interval.Finset.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Posets.GradedGamma

open D5.S3.Combinatorics.Posets.PPartitions
noncomputable section

variable {α : Type*} [Fintype α] [PartialOrder α] [GradeOrder ℕ α]

def parityBoundary (e : EnumeratingExtension α)
    (k : Fin (Fintype.card α - 1)) : Prop :=
  grade ℕ (e ⟨k.val, by omega⟩) % 2 ≠
    grade ℕ (e ⟨k.val + 1, by omega⟩) % 2

/-- The number of grade-parity changes before a position in an extension. -/
def runIndex (e : EnumeratingExtension α) (i : Fin (Fintype.card α)) : ℕ := by
  classical
  exact (Finset.univ.filter fun k : Fin (Fintype.card α - 1) =>
    k.val < i.val ∧ parityBoundary e k).card

open Classical in
theorem runIndex_succ (e : EnumeratingExtension α)
    (k : Fin (Fintype.card α - 1)) :
    runIndex e ⟨k.val + 1, by omega⟩ =
      runIndex e ⟨k.val, by omega⟩ +
        if parityBoundary e k then 1 else 0 := by
  classical
  let A := Finset.univ.filter fun t : Fin (Fintype.card α - 1) =>
    t.val < k.val ∧ parityBoundary e t
  let B := Finset.univ.filter fun t : Fin (Fintype.card α - 1) =>
    t.val < k.val + 1 ∧ parityBoundary e t
  have hnot : k ∉ A := by simp [A]
  have hleft : runIndex e ⟨k.val + 1, by omega⟩ = B.card := by
    simp [runIndex, B]
  have hright : runIndex e ⟨k.val, by omega⟩ = A.card := by
    simp [runIndex, A]
  by_cases hk : parityBoundary e k
  · have hset : B = insert k A := by
      ext t
      simp only [B, A, Finset.mem_filter, Finset.mem_univ,
        true_and, Finset.mem_insert]
      by_cases htk : t = k
      · subst t
        simp [hk]
      · constructor
        · intro h
          right
          have ht : t.val ≠ k.val := by
            intro heq
            exact htk (Fin.ext heq)
          exact ⟨by omega, h.2⟩
        · rintro (h | ⟨hlt, hpar⟩)
          · exact False.elim (htk h)
          · exact ⟨by omega, hpar⟩
    rw [hleft, hright, if_pos hk, hset, Finset.card_insert_of_notMem hnot]
  · have hset : B = A := by
      ext t
      simp only [B, A, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h
        have ht : t.val ≠ k.val := by
          intro heq
          have : t = k := Fin.ext heq
          exact hk (this ▸ h.2)
        exact ⟨by omega, h.2⟩
      · intro h
        exact ⟨by omega, h.2⟩
    rw [hleft, hright, if_neg hk, hset, add_zero]

/-- The parity of the run number is the grade parity when the first
extension position has even grade. -/
theorem runIndex_parity (e : EnumeratingExtension α)
    (hfirst : ∀ h : 0 < Fintype.card α,
      grade ℕ (e ⟨0, h⟩) % 2 = 0)
    (i : Fin (Fintype.card α)) :
    runIndex e i % 2 = grade ℕ (e i) % 2 := by
  have hstep : ∀ t : ℕ, (ht : t < Fintype.card α) →
      runIndex e ⟨t, ht⟩ % 2 = grade ℕ (e ⟨t, ht⟩) % 2 := by
    intro t
    induction t with
    | zero =>
        intro ht
        simp [runIndex, hfirst ht]
    | succ t ih =>
        intro ht
        let k : Fin (Fintype.card α - 1) := ⟨t, by omega⟩
        have hprev := ih (by omega : t < Fintype.card α)
        have hnext := runIndex_succ e k
        have hbound0 : grade ℕ (e ⟨t, by omega⟩) % 2 < 2 :=
          Nat.mod_lt _ (by omega)
        have hbound1 : grade ℕ (e ⟨t + 1, ht⟩) % 2 < 2 :=
          Nat.mod_lt _ (by omega)
        by_cases hb : parityBoundary e k
        · simp only [if_pos hb] at hnext
          unfold parityBoundary at hb
          change grade ℕ (e ⟨t, by omega⟩) % 2 ≠
            grade ℕ (e ⟨t + 1, ht⟩) % 2 at hb
          change runIndex e ⟨t + 1, ht⟩ =
            runIndex e ⟨t, by omega⟩ + 1 at hnext
          omega
        · simp only [if_neg hb, add_zero] at hnext
          unfold parityBoundary at hb
          change ¬ grade ℕ (e ⟨t, by omega⟩) % 2 ≠
            grade ℕ (e ⟨t + 1, ht⟩) % 2 at hb
          change runIndex e ⟨t + 1, ht⟩ =
            runIndex e ⟨t, by omega⟩ at hnext
          omega
  exact hstep i.val i.isLt

private theorem runIndex_eq_no_boundary (e : EnumeratingExtension α)
    (i j : Fin (Fintype.card α)) (hij : i ≤ j)
    (heq : runIndex e i = runIndex e j)
    (k : Fin (Fintype.card α - 1))
    (hik : i.val ≤ k.val) (hkj : k.val < j.val) :
    ¬ parityBoundary e k := by
  classical
  intro hboundary
  let A := Finset.univ.filter fun t : Fin (Fintype.card α - 1) =>
    t.val < i.val ∧ parityBoundary e t
  let B := Finset.univ.filter fun t : Fin (Fintype.card α - 1) =>
    t.val < j.val ∧ parityBoundary e t
  have hsub : A ⊆ B := by
    intro t ht
    simp only [A, B, Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
    exact ⟨lt_of_lt_of_le ht.1 (Fin.le_iff_val_le_val.mp hij), ht.2⟩
  have hka : k ∉ A := by
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and, not_and]
    intro hlt
    omega
  have hkb : k ∈ B := by
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hkj, hboundary⟩
  have hneq : A ≠ B := by
    intro hab
    exact hka (hab ▸ hkb)
  have hlt := Finset.card_lt_card ((Finset.ssubset_iff_subset_ne).2 ⟨hsub, hneq⟩)
  exact (Nat.ne_of_lt hlt) (by simpa [A, B, runIndex] using heq)

theorem run_interval_constant_parity (e : EnumeratingExtension α)
    (i j : Fin (Fintype.card α)) (hij : i ≤ j)
    (heq : runIndex e i = runIndex e j) :
    ∀ k : Fin (Fintype.card α), i ≤ k → k ≤ j →
      grade ℕ (e k) % 2 = grade ℕ (e i) % 2 := by
  intro k hik hkj
  have hsame : ∀ (t : ℕ) (hit : i.val ≤ t) (htk : t ≤ k.val),
      grade ℕ (e ⟨t, by omega⟩) % 2 = grade ℕ (e i) % 2 := by
    intro t
    induction t with
    | zero =>
        intro hit htk
        have hi0 : i.val = 0 := by omega
        have hfin : (⟨0, by omega⟩ : Fin (Fintype.card α)) = i :=
          Fin.ext hi0.symm
        simp [hfin]
    | succ t ih =>
        intro hit htk
        by_cases heqi : i.val = t + 1
        · have hfin : (⟨t + 1, by omega⟩ : Fin (Fintype.card α)) = i :=
            Fin.ext heqi.symm
          simp [hfin]
        · have hit' : i.val ≤ t := by omega
          have hprev := ih hit' (by omega)
          have hnobound := runIndex_eq_no_boundary e i j hij heq
            ⟨t, by omega⟩ hit' (by change t < j.val; omega)
          have hstep : grade ℕ (e ⟨t, by omega⟩) % 2 =
              grade ℕ (e ⟨t + 1, by omega⟩) % 2 := by
            exact Classical.not_not.mp hnobound
          exact hstep.symm.trans hprev
  have hk := hsame k.val hik (by omega)
  simpa using hk

/-- Vertices assigned to one parity run cannot be comparable. -/
theorem run_fiber_incomparable (e : EnumeratingExtension α)
    (i j : Fin (Fintype.card α)) (hij : i ≤ j)
    (heq : runIndex e i = runIndex e j) :
    ¬ e i < e j := by
  exact parity_run_incomparable e i j
    (run_interval_constant_parity e i j hij heq)

/-- Ordering every earlier parity run below every later run saturates an
extension while retaining the original order. -/
def runLE (e : EnumeratingExtension α) (x y : α) : Prop :=
  x = y ∨ runIndex e (e.1.symm x) < runIndex e (e.1.symm y)

theorem runLE_saturated (e : EnumeratingExtension α) {x y : α}
    (hparity : grade ℕ x % 2 ≠ grade ℕ y % 2) :
    runLE e x y ∨ runLE e y x := by
  let ix := e.1.symm x
  let iy := e.1.symm y
  have hne : runIndex e ix ≠ runIndex e iy := by
    intro heq
    rcases le_total ix iy with hpos | hpos
    · have h := run_interval_constant_parity e ix iy hpos heq iy hpos le_rfl
      exact hparity (by simpa [ix, iy] using h.symm)
    · have h := run_interval_constant_parity e iy ix hpos heq.symm ix hpos le_rfl
      exact hparity (by simpa [ix, iy] using h)
  rcases lt_or_gt_of_ne hne with h | h
  · exact Or.inl (Or.inr h)
  · exact Or.inr (Or.inr h)

theorem runLE_extends (e : EnumeratingExtension α) {x y : α}
    (hxy : x < y) : runLE e x y := by
  have hpos : e.1.symm x < e.1.symm y := e.2 hxy
  have hmono : runIndex e (e.1.symm x) ≤ runIndex e (e.1.symm y) := by
    unfold runIndex
    apply Finset.card_le_card
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    exact ⟨lt_of_lt_of_le hk.1 hpos.le, hk.2⟩
  have hne : runIndex e (e.1.symm x) ≠ runIndex e (e.1.symm y) := by
    intro heq
    have hi := run_fiber_incomparable e (e.1.symm x) (e.1.symm y) hpos.le heq
    exact hi (by simpa only [Equiv.apply_symm_apply] using hxy)
  exact Or.inr (lt_of_le_of_ne hmono hne)

/-- Respecting the order between runs preserves the run number at every
position, even when each antichain run is permuted. -/
theorem compatible_run_word (e e' : EnumeratingExtension α)
    (hcompat : ∀ x y : α,
      runIndex e (e.1.symm x) < runIndex e (e.1.symm y) →
        e'.1.symm x < e'.1.symm y) :
    ∀ i : Fin (Fintype.card α),
      runIndex e (e.1.symm (e' i)) = runIndex e i := by
  classical
  have hf : Monotone (runIndex e) := by
    intro i j hij
    unfold runIndex
    apply Finset.card_le_card
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    exact ⟨lt_of_lt_of_le hk.1 hij, hk.2⟩
  have hg : Monotone (fun i => runIndex e (e.1.symm (e' i))) := by
    intro i j hij
    rcases hij.eq_or_lt with rfl | hij
    · exact le_rfl
    · by_contra hn
      have hrev : runIndex e (e.1.symm (e' j)) <
          runIndex e (e.1.symm (e' i)) := lt_of_not_ge hn
      have hpos := hcompat (e' j) (e' i) hrev
      simp only [Equiv.symm_apply_apply] at hpos
      exact (not_lt_of_ge hij.le) hpos
  let σ : Equiv.Perm (Fin (Fintype.card α)) := e'.1.trans e.1.symm
  have hunique : (runIndex e) ∘ σ = runIndex e := by
    have hs := Tuple.unique_monotone (f := runIndex e) (σ := σ)
      (τ := Equiv.refl _) (by simpa [σ, Function.comp_def] using hg)
      (by simpa using hf)
    simpa using hs
  intro i
  have hi := congrArg (fun f : Fin (Fintype.card α) → ℕ => f i) hunique
  simpa [σ, Function.comp_def] using hi

/-- Compatible extensions have the same run index at each position, although
the vertices within a run may be permuted. -/
theorem compatible_run_index (e e' : EnumeratingExtension α)
    (hcompat : ∀ x y : α,
      runIndex e (e.1.symm x) < runIndex e (e.1.symm y) →
        e'.1.symm x < e'.1.symm y) :
    (∀ i : Fin (Fintype.card α), runIndex e' i = runIndex e i) ∧
      (∀ i : Fin (Fintype.card α),
        grade ℕ (e' i) % 2 = grade ℕ (e i) % 2) := by
  classical
  have hword := compatible_run_word e e' hcompat
  have hparity (i : Fin (Fintype.card α)) :
      grade ℕ (e' i) % 2 = grade ℕ (e i) % 2 := by
    by_contra hne
    have hsat := runLE_saturated e (x := e' i) (y := e i) hne
    have hi : runIndex e (e.1.symm (e' i)) =
        runIndex e (e.1.symm (e i)) := by simpa using hword i
    rcases hsat with (h | h) | (h | h)
    · exact hne (by rw [h])
    · exact (Nat.ne_of_lt h) hi
    · exact hne (by rw [h])
    · exact (Nat.ne_of_gt h) hi
  have hboundary (k : Fin (Fintype.card α - 1)) :
      parityBoundary e' k ↔ parityBoundary e k := by
    unfold parityBoundary
    rw [hparity ⟨k.val, by omega⟩, hparity ⟨k.val + 1, by omega⟩]
  refine ⟨?_, hparity⟩
  intro i
  unfold runIndex
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hboundary k]

def runOrder (e : EnumeratingExtension α) : PartialOrder α where
  le := runLE e
  lt x y := runIndex e (e.1.symm x) < runIndex e (e.1.symm y)
  lt_iff_le_not_ge := by
    intro x y
    constructor
    · intro h
      exact ⟨Or.inr h, by
        intro hyx
        rcases hyx with hyx | hyx
        · subst y
          exact (Nat.lt_irrefl _) h
        · exact (Nat.lt_asymm h hyx)⟩
    · rintro ⟨hxy, hnot⟩
      rcases hxy with hxy | hxy
      · subst y
        exact False.elim (hnot (Or.inl rfl))
      · exact hxy
  le_refl := fun x => Or.inl rfl
  le_trans := by
    intro x y z hxy hyz
    rcases hxy with hxy | hxy
    · subst y
      exact hyz
    · rcases hyz with hyz | hyz
      · subst z
        exact Or.inr hxy
      · exact Or.inr (hxy.trans hyz)
  le_antisymm := by
    intro x y hxy hyx
    rcases hxy with hxy | hxy
    · exact hxy
    · rcases hyx with hyx | hyx
      · exact hyx.symm
      · exact False.elim (Nat.lt_asymm hxy hyx)

end
end D5.S3.Combinatorics.Posets.GradedGamma
