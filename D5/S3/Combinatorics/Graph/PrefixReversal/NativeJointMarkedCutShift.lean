/- GID: D5/S3/Combinatorics/Graph/PrefixReversal/NativeJointMarkedCutShift
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/PrefixReversal/NativeJointMarkedCutShift
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Every next marked cut group is its prior group together with its actual new zero edge. -/
/- exact native cut-set bridge for the actual J update.
   Literal shifted native ports identify every positive next cut with an
   old P cut. The remaining two edges are precisely the two Q zero cuts.
   Both next marked orders exchange the previous orders as in Phi. -/
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeMarkedStepCoordinates

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.PrefixReversal.NativeJointMarkedCutShift

open D5.S3.Combinatorics.Graph.PrefixReversalZeroStarComplement
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveSupply
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeMarkedStepCoordinates

noncomputable def markedCut {m k : ℕ} (F : SupplyFrame m k) (i : ℕ) : Sym2 (Configuration m) :=
  s(rightPort F i, leftPort F i)

noncomputable def markedCuts {m k : ℕ} (F : SupplyFrame m k) :
    Finset (Sym2 (Configuration m)) := by
  classical
  exact Finset.univ.image (fun i : Fin (k + 1) => markedCut F i.val)

/-- Exact native tuple shift accounts for every next cut, including its
zero edge; there are no other cut indices. -/
theorem native_frame_marked_cuts_shift {m k : ℕ} (hm : 3 ≤ m)
    (F : SupplyFrame m k) (A : List (Fin (m + 1))) (u : Fin (m + 1))
    (hbase : F.base = A ++ [u]) :
    markedCuts (nextFrame F A u hbase) =
      insert (markedCut (nextFrame F A u hbase) 0) (markedCuts F) := by
  classical
  ext e
  simp only [markedCuts, Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert]
  constructor
  · rintro ⟨i, hi⟩
    by_cases hi0 : i.val = 0
    · left
      exact (by simpa only [hi0] using hi.symm)
    · right
      let j : Fin (k + 1) := ⟨i.val - 1, by have h := i.isLt; omega⟩
      have hj : j.val + 1 = i.val := by dsimp only [j]; omega
      have hs := native_marked_index_shift hm F A u hbase j.val
      rw [hj] at hs
      refine ⟨j, ?_⟩
      unfold markedCut at hi ⊢
      rw [hs.1, hs.2] at hi
      exact hi
  · rintro (he | ⟨i, hi⟩)
    · exact ⟨0, he.symm⟩
    · refine ⟨i.succ, ?_⟩
      have hs := native_marked_index_shift hm F A u hbase i.val
      unfold markedCut at hi ⊢
      simp only [Fin.val_succ]
      rw [hs.1, hs.2]
      exact hi

/-- The actual next joint deletion set is the two Q zero cuts and all
old P cuts, with the previous marked orders exchanged. -/
theorem native_joint_marked_cuts_shift {m k : ℕ} (hm : 3 ≤ m)
    (F₀ F₁ : SupplyFrame m k) (A : List (Fin (m + 1))) (u : Fin (m + 1))
    (hbase₀ : F₀.base = A ++ [u]) (hbase₁ : F₁.base = A ++ [u]) :
    markedCuts (nextFrame F₁ A u hbase₁) ∪ markedCuts (nextFrame F₀ A u hbase₀) =
      {markedCut (nextFrame F₁ A u hbase₁) 0,
        markedCut (nextFrame F₀ A u hbase₀) 0} ∪ (markedCuts F₀ ∪ markedCuts F₁) := by
  classical
  rw [native_frame_marked_cuts_shift hm F₀ A u hbase₀,
    native_frame_marked_cuts_shift hm F₁ A u hbase₁]
  ext e
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
  tauto

#print axioms native_frame_marked_cuts_shift
#print axioms native_joint_marked_cuts_shift

end D5.S3.Combinatorics.Graph.PrefixReversal.NativeJointMarkedCutShift
