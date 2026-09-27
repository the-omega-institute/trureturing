/- GID: D5/S1/Words/Patterns/Separable/CutFactorization
   generality: G
   mirror-B: D5/B/S1/Words/Patterns/Separable/CutFactorization
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Actual fixed-cut factors of classical separable permutations. -/

import D5.S1.Words.Patterns.Separable.ProperCut
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
Actual block sums supporting the classical decomposition in Fu--Lin--Zeng,
arXiv:1507.05184v2, Proposition 2.1. This does not settle the real-rootedness
problem. The two factors keep their internal orders in both orientations.
-/

namespace D5.S1.Words.Patterns.Separable.CutFactorization

open D5.S1.Words.Patterns.DerangementRatioNonconvergence (Contains)
open D5.S1.Words.Patterns.Separable.ProperCut (pattern2413 pattern3142)

/-- The actual classical avoidance predicate. -/
def Avoids {n : ℕ} (π : Equiv.Perm (Fin n)) : Prop :=
  ¬Contains pattern2413 π ∧ ¬Contains pattern3142 π

/-- Actual permutations, without a recursive replacement class. -/
abbrev Avoider (n : ℕ) := {π : Equiv.Perm (Fin n) // Avoids π}

/-- False is direct sum; true is skew sum. -/
def blockSum {m k : ℕ} (skew : Bool)
    (α : Equiv.Perm (Fin m)) (β : Equiv.Perm (Fin k)) : Equiv.Perm (Fin (m + k)) :=
  finSumFinEquiv.symm.trans ((Equiv.sumCongr α β).trans
    (if skew then (Equiv.sumComm _ _).trans
      (finSumFinEquiv.trans (finCongr (Nat.add_comm k m))) else finSumFinEquiv))

/-- The crossing comparison at an actual position cut. -/
def Cut {n : ℕ} (skew : Bool) (π : Equiv.Perm (Fin n)) (m : ℕ) : Prop :=
  ∀ i j : Fin n, i.val < m → m ≤ j.val →
    if skew then π j < π i else π i < π j

/-- A forbidden literal occurrence in a block sum lies wholly in one factor. -/
theorem avoids_block_sum_iff {m k : ℕ} (skew : Bool)
    (α : Equiv.Perm (Fin m)) (β : Equiv.Perm (Fin k)) :
    Avoids (blockSum skew α β) ↔ Avoids α ∧ Avoids β := by
  have leftval (i : Fin m) :
      (blockSum skew α β (Fin.castAdd k i)).val =
        (if skew then k else 0) + (α i).val := by
    cases skew <;> simp [blockSum, Equiv.sumCongr, Equiv.sumComm, Nat.add_comm]
  have rightval (i : Fin k) :
      (blockSum skew α β (Fin.natAdd m i)).val =
        (if skew then 0 else m) + (β i).val := by
    cases skew <;> simp [blockSum, Equiv.sumCongr, Equiv.sumComm]
  have cross : Cut skew (blockSum skew α β) m := by
    intro i j hi hj
    have ei : i = Fin.castAdd k ⟨i.val, hi⟩ := Fin.ext rfl
    have ej : j = Fin.natAdd m ⟨j.val - m, by omega⟩ := Fin.ext (by simp; omega)
    rw [ei, ej]
    cases skew <;> change _ < _
    all_goals simp only [Fin.lt_def, leftval, rightval]; simp; omega
  have transfer (σ : Equiv.Perm (Fin 4))
      (hσ : σ = pattern2413 ∨ σ = pattern3142) :
      Contains σ (blockSum skew α β) ↔ Contains σ α ∨ Contains σ β := by
    constructor
    · rintro ⟨f, hf⟩
      have mono := f.strictMono
      have h01 := mono (show (0 : Fin 4) < 1 by decide)
      have h12 := mono (show (1 : Fin 4) < 2 by decide)
      have h23 := mono (show (2 : Fin 4) < 3 by decide)
      have allside : (∀ i, (f i).val < m) ∨ (∀ i, m ≤ (f i).val) := by
        by_cases h0 : m ≤ (f 0).val
        · right
          intro i
          fin_cases i <;> dsimp <;> omega
        by_cases h3 : (f 3).val < m
        · left
          intro i
          fin_cases i <;> dsimp <;> omega
        have hc (i j : Fin 4) (hi : (f i).val < m) (hj : m ≤ (f j).val) :
            if skew then σ j < σ i else σ i < σ j := by
          have hh := cross (f i) (f j) hi hj
          cases skew
          · exact (hf i j).mpr hh
          · exact (hf j i).mpr hh
        by_cases h1 : (f 1).val < m
        · by_cases h2 : (f 2).val < m
          · have c03 := hc 0 3 (by omega) (by omega)
            have c13 := hc 1 3 h1 (by omega)
            have c23 := hc 2 3 h2 (by omega)
            rcases hσ with rfl | rfl <;> cases skew <;>
              simp_all [pattern2413, pattern3142]
          · have c02 := hc 0 2 (by omega) (by omega)
            have c03 := hc 0 3 (by omega) (by omega)
            have c12 := hc 1 2 h1 (by omega)
            have c13 := hc 1 3 h1 (by omega)
            rcases hσ with rfl | rfl <;> cases skew <;>
              simp_all [pattern2413, pattern3142]
        · have c01 := hc 0 1 (by omega) (by omega)
          have c02 := hc 0 2 (by omega) (by omega)
          rcases hσ with rfl | rfl <;> cases skew <;>
            simp_all [pattern2413, pattern3142]
      rcases allside with hl | hr
      · left
        let g : Fin 4 ↪o Fin m := OrderEmbedding.ofStrictMono
          (fun i => ⟨(f i).val, hl i⟩) (by intro i j hij; exact mono hij)
        refine ⟨g, fun i j => ?_⟩
        have ei (i : Fin 4) : f i = Fin.castAdd k (g i) := Fin.ext rfl
        rw [hf, ei i, ei j, Fin.lt_def, leftval, leftval]
        simp
      · right
        let g : Fin 4 ↪o Fin k := OrderEmbedding.ofStrictMono
          (fun i => ⟨(f i).val - m, by have := (f i).isLt; have := hr i; omega⟩)
          (by intro i j hij; have := mono hij; have := hr i; have := hr j
              change (f i).val - m < (f j).val - m; omega)
        refine ⟨g, fun i j => ?_⟩
        have ei (i : Fin 4) : f i = Fin.natAdd m (g i) := by
          apply Fin.ext
          have := hr i
          simp [g, OrderEmbedding.ofStrictMono]
          omega
        rw [hf, ei i, ei j, Fin.lt_def, rightval, rightval]
        simp
    · rintro (⟨f, hf⟩ | ⟨f, hf⟩)
      · let g : Fin 4 ↪o Fin (m + k) := OrderEmbedding.ofStrictMono
          (fun i => Fin.castAdd k (f i)) (by intro i j hij; exact f.strictMono hij)
        refine ⟨g, fun i j => ?_⟩
        change σ i < σ j ↔ blockSum skew α β (Fin.castAdd k (f i)) <
          blockSum skew α β (Fin.castAdd k (f j))
        rw [hf]
        simp only [Fin.lt_def, leftval]
        simp
      · let g : Fin 4 ↪o Fin (m + k) := OrderEmbedding.ofStrictMono
          (fun i => Fin.natAdd m (f i)) (by intro i j hij; simpa using f.strictMono hij)
        refine ⟨g, fun i j => ?_⟩
        change σ i < σ j ↔ blockSum skew α β (Fin.natAdd m (f i)) <
          blockSum skew α β (Fin.natAdd m (f j))
        rw [hf]
        simp only [Fin.lt_def, rightval]
        simp
  unfold Avoids
  rw [transfer pattern2413 (Or.inl rfl), transfer pattern3142 (Or.inr rfl)]
  tauto

/-- A fixed nonempty cut has unique actual avoiding factors, with literal reconstruction. -/
theorem fixed_cut_factorization {m k : ℕ} (_hm : 0 < m) (_hk : 0 < k)
    (skew : Bool) (π : Avoider (m + k)) :
    Cut skew π.val m ↔
      ∃! factors : Avoider m × Avoider k,
        blockSum skew factors.1.val factors.2.val = π.val := by
  classical
  have leftval (a : Equiv.Perm (Fin m)) (b : Equiv.Perm (Fin k)) (i : Fin m) :
      (blockSum skew a b (Fin.castAdd k i)).val =
        (if skew then k else 0) + (a i).val := by
    cases skew <;> simp [blockSum, Equiv.sumCongr, Equiv.sumComm, Nat.add_comm]
  have rightval (a : Equiv.Perm (Fin m)) (b : Equiv.Perm (Fin k)) (i : Fin k) :
      (blockSum skew a b (Fin.natAdd m i)).val =
        (if skew then 0 else m) + (b i).val := by
    cases skew <;> simp [blockSum, Equiv.sumCongr, Equiv.sumComm]
  constructor
  · intro hc
    let l : Fin m → Fin (m + k) := fun i => π.val (Fin.castAdd k i)
    let r : Fin k → Fin (m + k) := fun i => π.val (Fin.natAdd m i)
    let α := (Tuple.sort l).symm
    let β := (Tuple.sort r).symm
    have hl : StrictMono (l ∘ Tuple.sort l) :=
      (Tuple.monotone_sort l).strictMono_of_injective
        ((π.val.injective.comp (Fin.castAdd_injective m k)).comp (Tuple.sort l).injective)
    have hr : StrictMono (r ∘ Tuple.sort r) :=
      (Tuple.monotone_sort r).strictMono_of_injective
        ((π.val.injective.comp (Fin.natAdd_injective k m)).comp (Tuple.sort r).injective)
    have ha (i j : Fin m) : α i < α j ↔ l i < l j := by
      simpa [α, Function.comp_def] using (hl.lt_iff_lt (a := α i) (b := α j)).symm
    have hb (i j : Fin k) : β i < β j ↔ r i < r j := by
      simpa [β, Function.comp_def] using (hr.lt_iff_lt (a := β i) (b := β j)).symm
    let ρ := blockSum skew α β
    have same_order (i j : Fin (m + k)) : ρ i < ρ j ↔ π.val i < π.val j := by
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
        refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · change blockSum skew α β (Fin.castAdd k i) <
          blockSum skew α β (Fin.castAdd k j) ↔ l i < l j
        rw [← ha]
        simp only [Fin.lt_def, leftval, Nat.add_lt_add_iff_left]
      · have h := hc (Fin.castAdd k i) (Fin.natAdd m j) (by simp) (by simp)
        change blockSum skew α β (Fin.castAdd k i) <
          blockSum skew α β (Fin.natAdd m j) ↔ _
        simp only [Fin.lt_def, leftval, rightval]
        cases skew <;> simp_all only [Bool.false_eq_true, ↓reduceIte] <;> omega
      · have h := hc (Fin.castAdd k j) (Fin.natAdd m i) (by simp) (by simp)
        change blockSum skew α β (Fin.natAdd m i) <
          blockSum skew α β (Fin.castAdd k j) ↔ _
        simp only [Fin.lt_def, leftval, rightval]
        cases skew <;> simp_all only [Bool.false_eq_true, ↓reduceIte] <;> omega
      · change blockSum skew α β (Fin.natAdd m i) <
          blockSum skew α β (Fin.natAdd m j) ↔ r i < r j
        rw [← hb]
        simp only [Fin.lt_def, rightval, Nat.add_lt_add_iff_left]
    have heq : ρ = π.val := by
      have hs : StrictMono (ρ.symm.trans π.val) := by
        intro i j hij
        apply (same_order (ρ.symm i) (ρ.symm j)).mp
        simpa using hij
      have hid := (Equiv.Perm.monotone_iff (ρ.symm.trans π.val)).mp hs.monotone
      apply Equiv.ext
      intro i
      have hh := Equiv.congr_fun hid (ρ i)
      simpa using hh.symm
    have hav : Avoids α ∧ Avoids β :=
      (avoids_block_sum_iff skew α β).mp (by change Avoids ρ; rw [heq]; exact π.property)
    refine ⟨(⟨α, hav.1⟩, ⟨β, hav.2⟩), heq, ?_⟩
    intro q hq
    apply Prod.ext
    · apply Subtype.ext
      apply Equiv.ext
      intro i
      apply Fin.ext
      have hh := congrArg (fun p : Equiv.Perm (Fin (m + k)) =>
        (p (Fin.castAdd k i)).val) (hq.trans heq.symm)
      change (blockSum skew q.1.val q.2.val (Fin.castAdd k i)).val =
        (blockSum skew α β (Fin.castAdd k i)).val at hh
      rw [leftval, leftval] at hh
      exact Nat.add_left_cancel hh
    · apply Subtype.ext
      apply Equiv.ext
      intro i
      apply Fin.ext
      have hh := congrArg (fun p : Equiv.Perm (Fin (m + k)) =>
        (p (Fin.natAdd m i)).val) (hq.trans heq.symm)
      change (blockSum skew q.1.val q.2.val (Fin.natAdd m i)).val =
        (blockSum skew α β (Fin.natAdd m i)).val at hh
      rw [rightval, rightval] at hh
      exact Nat.add_left_cancel hh
  · rintro ⟨q, hq, _⟩
    rw [← hq]
    intro i j hi hj
    have ei : i = Fin.castAdd k ⟨i.val, hi⟩ := Fin.ext rfl
    have ej : j = Fin.natAdd m ⟨j.val - m, by omega⟩ := Fin.ext (by simp; omega)
    rw [ei, ej]
    cases skew <;> change _ < _
    all_goals simp only [Fin.lt_def, leftval, rightval]; simp; omega

/-- The ordinary adjacent-descent indicator, zero at the final position. -/
def descentAt {n : ℕ} (π : Equiv.Perm (Fin n)) (i : Fin n) : ℕ :=
  if h : i.val + 1 < n then if π ⟨i.val + 1, h⟩ < π i then 1 else 0 else 0

/-- Number of ordinary adjacent descents. -/
def descents {n : ℕ} (π : Equiv.Perm (Fin n)) : ℕ := ∑ i, descentAt π i

#check avoids_block_sum_iff
#check fixed_cut_factorization
#print axioms avoids_block_sum_iff
#print axioms fixed_cut_factorization

end D5.S1.Words.Patterns.Separable.CutFactorization
