/- GID: D5/S3/Combinatorics/PathAlignedPacking/CFiveDP
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PathAlignedPacking/CFiveDP
   mirror-E: none(waiver:path-aligned-packing-transfer)
   anchors: []
   utility: none
   digest: Sparse transfer membership propagates along chains of arbitrary length. -/

import D5.S3.Combinatorics.PathAlignedPacking.CFiveData

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PathAlignedPacking.CFiveDP

set_option maxRecDepth 100000
set_option maxHeartbeats 0

open Defs
open D5.S3.Combinatorics.PathAlignedPacking.Metric

open CFiveData

/-- State layers after the initial adjacent pair. -/
def reachable : ℕ → List State
  | 0 => layerTwo
  | n + 1 => extend (reachable n)

/-- Adjacent and next-nearest constraints propagate through any finite chain. -/
theorem propagate (f : ℕ → Fin 240) (n : ℕ)
    (hone : ∀ i, i ≤ n → PairOK 1 (candidate (f i)) (candidate (f (i + 1))))
    (htwo : ∀ i, i < n → PairOK 2 (candidate (f i)) (candidate (f (i + 2)))) :
    (f n, f (n + 1)) ∈ reachable n := by
  have mem_layerTwo
      (hrow : ∀ i j : Fin 240, PairOK 1 (candidate i) (candidate j) → j ∈ oneNext i)
      (i j : Fin 240) (h : PairOK 1 (candidate i) (candidate j)) :
      (i, j) ∈ layerTwo := by
    unfold layerTwo
    apply List.mem_flatMap.mpr
    refine ⟨i, by simp, List.mem_map.mpr ⟨j, hrow i j h, rfl⟩⟩

  have mem_extend
      (hrow : ∀ i j : Fin 240, PairOK 1 (candidate i) (candidate j) → j ∈ oneNext i)
      (states : List State) (i j k : Fin 240) (hij : (i, j) ∈ states)
      (hjk : PairOK 1 (candidate j) (candidate k))
      (hik : PairOK 2 (candidate i) (candidate k)) : (j, k) ∈ extend states := by
    unfold extend
    rw [List.mem_eraseDups]
    apply List.mem_flatMap.mpr
    refine ⟨(i, j), hij, List.mem_map.mpr ⟨k, ?_, rfl⟩⟩
    exact List.mem_filter.mpr ⟨hrow j k hjk, by simp [hik]⟩
  have one_complete : ∀ i j : Fin 240,
      PairOK 1 (candidate i) (candidate j) → j ∈ oneNext i := by
    let join (a : Fin 24) (b : Fin 10) : Fin 240 :=
      ⟨10 * a.val + b.val, by have := a.isLt; have := b.isLt; omega⟩
    have checks : ∀ a : Fin 24, ∀ b : Fin 10, ∀ j : Fin 240,
        PairOK 1 (candidate (join a b)) (candidate j) → j ∈ oneNext (join a b) := by
      intro a
      fin_cases a <;> decide +kernel
    intro i j hij
    let a : Fin 24 := ⟨i.val / 10, by have := i.isLt; omega⟩
    let b : Fin 10 := ⟨i.val % 10, Nat.mod_lt _ (by omega)⟩
    have heq : join a b = i := by
      apply Fin.ext
      dsimp [join, a, b]
      omega
    simpa only [heq] using checks a b j (by simpa only [heq] using hij)
  
  induction n with
  | zero => exact mem_layerTwo one_complete _ _ (hone 0 (by omega))
  | succ n ih =>
    apply mem_extend one_complete (reachable n) (f n) (f (n + 1)) (f (n + 2))
    · exact ih (fun i hi => hone i (by omega)) (fun i hi => htwo i (by omega))
    · exact hone (n + 1) (by omega)
    · exact htwo n (by omega)

end D5.S3.Combinatorics.PathAlignedPacking.CFiveDP
