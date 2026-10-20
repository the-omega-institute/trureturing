/- GID: D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionSelection
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Walks/CompleteSubdivisionSelection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Algebra.BigOperators.Group.Finset.Basic]
   utility: none
   digest: Extract the full diagonal-aware selection matrix from arbitrary subdivision landmarks. -/
import D5.S3.Combinatorics.Graph.Walks.CompleteSubdivisionCounting
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.Walks.CompleteSubdivisionSelection

open D5.S3.Combinatorics.Graph.Walks.CompleteSubdivisionMetric
open D5.S3.Combinatorics.Graph.Walks.CompleteSubdivisionProfiles
open D5.S3.Combinatorics.Graph.Walks.CompleteSubdivisionCounting

variable {n : ℕ}

noncomputable def pairBit (S : Finset (Vertex n)) (u v : Fin n) : ℤ :=
  if h : u = v then 0 else midpointBit S (subdivisionVertex u v h)

private noncomputable def hit (u v : Fin n) (s : Vertex n) : ℤ :=
  if h : u = v then 0 else if s = .inr (subdivisionVertex u v h) then 1 else 0

private theorem sum_hit (u : Fin n) (s : Vertex n) :
    (∑ v, hit u v s) = match s with
      | .inl _ => (0 : ℤ) | .inr f => if u ∈ f.val then 1 else 0 := by
  classical
  cases s with
  | inl w => simp [hit]
  | inr f =>
    dsimp only
    by_cases hu : u ∈ f.val
    · let v := Sym2.Mem.other hu
      have huv : u ≠ v := (Sym2.other_ne f.property hu).symm
      have hfv : f = subdivisionVertex u v huv :=
        Subtype.ext (Sym2.other_spec hu).symm
      rw [if_pos hu]
      rw [Finset.sum_eq_single v]
      · simp [hit, huv, hfv]
      · intro w _ hwv
        by_cases huw : u = w
        · simp [hit, huw]
        · have hfw : f ≠ subdivisionVertex u w huw := by
            intro hfw
            have hi : incidence u v huv = incidence u w huw :=
              congrArg (fun z : Midpoint n => s(Sum.inl u, Sum.inr z)) (hfv.symm.trans hfw)
            exact hwv ((incidence_eq_iff u v u w huv huw).mp hi).2.symm
          simp [hit, huw, hfw]
      · simp
    · rw [if_neg hu]
      apply Finset.sum_eq_zero
      intro v _
      by_cases huv : u = v
      · simp [hit, huv]
      · have hf : f ≠ subdivisionVertex u v huv := by
          intro hf
          apply hu
          rw [hf]
          exact Sym2.mem_mk_left u v
        simp [hit, huv, hf]

theorem selectedDegree_eq_sum_pairBit (S : Finset (Vertex n)) (u : Fin n) :
    selectedDegree S u = ∑ v, pairBit S u v := by
  classical
  calc
    selectedDegree S u = ∑ s ∈ S, ∑ v, hit u v s := by
      apply Finset.sum_congr rfl
      intro s _
      exact (sum_hit u s).symm
    _ = ∑ v, ∑ s ∈ S, hit u v s := Finset.sum_comm
    _ = ∑ v, pairBit S u v := by
      apply Finset.sum_congr rfl
      intro v _
      by_cases h : u = v <;> simp [pairBit, hit, h, midpointBit]

theorem pairBit_symm (S : Finset (Vertex n)) (u v : Fin n) :
    pairBit S u v = pairBit S v u := by
  classical
  by_cases h : u = v
  · subst v; rfl
  · simp only [pairBit, dif_neg h, dif_neg (Ne.symm h)]
    exact midpointBit_swap S u v h

theorem pairBit_binary (S : Finset (Vertex n)) (u v : Fin n) :
    pairBit S u v = 0 ∨ pairBit S u v = 1 := by
  classical
  unfold pairBit midpointBit
  split_ifs <;> simp

/-- Original selections occupy the genuinely free diagonal. -/
noncomputable def selection (S : Finset (Vertex n)) (u v : Fin n) : ℕ :=
  if u = v then (originalBit S u).toNat else (pairBit S u v).toNat

theorem selection_symm (S : Finset (Vertex n)) (u v : Fin n) :
    selection S u v = selection S v u := by
  classical
  by_cases h : u = v
  · subst v; rfl
  · simp [selection, h, Ne.symm h, pairBit_symm]

theorem selection_binary (S : Finset (Vertex n)) (u v : Fin n) :
    selection S u v ≤ 1 := by
  classical
  unfold selection originalBit
  have := pairBit_binary S u v
  split_ifs <;> rcases this with h | h <;> simp [h]

theorem selection_diagonal (S : Finset (Vertex n)) (u : Fin n) :
    (selection S u u : ℤ) = originalBit S u := by
  classical
  simp only [selection, if_pos rfl]
  unfold originalBit
  split_ifs <;> norm_num

theorem selection_offDiagonal (S : Finset (Vertex n)) (u v : Fin n) (h : u ≠ v) :
    (selection S u v : ℤ) = midpointBit S (subdivisionVertex u v h) := by
  classical
  simp only [selection, if_neg h, pairBit, dif_neg h]
  unfold midpointBit
  split_ifs <;> norm_num

theorem selection_row (S : Finset (Vertex n)) (u : Fin n) :
    (∑ v, (selection S u v : ℤ)) = selectedDegree S u + originalBit S u := by
  classical
  rw [selectedDegree_eq_sum_pairBit]
  have pointwise (v : Fin n) : (selection S u v : ℤ) =
      pairBit S u v + if u = v then originalBit S u else 0 := by
    have hp := pairBit_binary S u v
    by_cases h : u = v
    · subst v
      simp only [selection, if_pos rfl, pairBit, dif_pos rfl, zero_add]
      unfold originalBit
      split_ifs <;> norm_num
    · simp only [selection, if_neg h, add_zero]
      rcases hp with hp | hp <;> simp [hp]
  simp_rw [pointwise, Finset.sum_add_distrib]
  simp

end D5.S3.Combinatorics.Graph.Walks.CompleteSubdivisionSelection
