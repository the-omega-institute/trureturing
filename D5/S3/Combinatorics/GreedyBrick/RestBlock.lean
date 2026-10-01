/- GID: D5/S3/Combinatorics/GreedyBrick/RestBlock
   generality: G
   mirror-B: D5/B/S3/Combinatorics/GreedyBrick/RestBlock
   mirror-E: none(waiver:unbounded-relay-induction)
   anchors: [mathlib/module/Mathlib.Data.List.Basic]
   utility: none
   digest: Literal capacity placements realize first-zero rest blocks. -/

import D5.S3.Combinatorics.GreedyBrick.SuccessorBand
import D5.S3.ArithSums.GreedyBrickCapacityTotality

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.GreedyBrick.RestBlock

open SuccessorBand
open D5.S3.ArithSums.GreedyBrickCapacityTotality

/-- One-based least zero bin, or the next bin when every old bin is positive.
The input is ordered from bottom to top. -/
def firstZeroBin : List ℕ → ℕ
  | [] => 1
  | c :: cs => if c = 0 then 1 else firstZeroBin cs + 1

/-- Execute the accepted top-to-bottom capacity step at successive widths
N+1,...,N+k. No rest-event relation is used in this definition. -/
def placeBricks (N : ℕ) (cs : List ℕ) : ℕ → List ℕ
  | 0 => cs
  | k + 1 => placeBricks (N + 1) (step (N + 1) cs) k

/-- Candidate bottom-to-top rest capacities: decrement the positive prefix,
reset its first zero, and preserve the remaining suffix; append at the top
when the old list has no zero. The theorem identifies this candidate with
the independently defined literal placements. -/
def restCapacity (N : ℕ) : List ℕ → List ℕ
  | [] => [N + 1]
  | c :: cs => if c = 0 then (N + 1) :: cs else (c - 1) :: restCapacity (N + 1) cs

/-- Every bounded rest state realizes its first-zero event by exactly that
many consecutive applications of the actual capacity step. Capacities of
the rest interface are bottom-to-top, so both algorithm boundaries reverse
the list. This supplies no geometric row correspondence or event history. -/
theorem literal_rest_block (s : RestState) :
    ∃ t : RestState, RestEventStep s t (firstZeroBin s.capacity) ∧
      placeBricks s.endpoint s.capacity.reverse (firstZeroBin s.capacity) =
        t.capacity.reverse := by
  have pass (n : ℕ) (us ds : List ℕ)
      (hu : ∀ c ∈ us, c < n) (hf : (transfer n ds).2 = false) :
      transfer n (us ++ ds) = (us ++ (transfer n ds).1, false) := by
    induction us with
    | nil => apply Prod.ext <;> simp [hf]
    | cons c us ih =>
      have hc : ¬ n ≤ c := by have := hu c (by simp); omega
      have ht := ih (fun d hd => hu d (by simp [hd]))
      simp [transfer, hc, ht]
  have relay : ∀ (cs : List ℕ) (N a : ℕ) (lower : List ℕ),
      0 < a → (∀ c ∈ cs, c ≤ N) →
      placeBricks N (cs.reverse ++ (N + a) :: lower) (firstZeroBin cs) =
        (restCapacity N cs).reverse ++ (a - 1) :: lower := by
    intro cs
    induction cs with
    | nil =>
      intro N a lower ha _
      have he : N + 1 ≤ N + a := by omega
      have hd : N + a - (N + 1) = a - 1 := by omega
      simp [firstZeroBin, restCapacity, placeBricks, step, transfer, he, hd]
    | cons c cs ih =>
      intro N a lower ha hb
      have hc := hb c (by simp)
      have hn : ¬ N + 1 ≤ c := by omega
      have he : N + 1 ≤ N + a := by omega
      have hd : N + a - (N + 1) = a - 1 := by omega
      have hbase : transfer (N + 1) (c :: (N + a) :: lower) =
          ((c + (N + 1)) :: (a - 1) :: lower, false) := by
        simp [transfer, hn, he, hd]
      have hp := pass (N + 1) cs.reverse (c :: (N + a) :: lower)
        (by intro d hd'; have := hb d (by simp only [List.mem_reverse] at hd'; simp [hd']); omega)
        (by rw [hbase])
      have hs : step (N + 1) (cs.reverse ++ c :: (N + a) :: lower) =
          cs.reverse ++ (c + (N + 1)) :: (a - 1) :: lower := by
        unfold step
        rw [hp, hbase]
        simp
      by_cases hz : c = 0
      · subst c
        simpa [firstZeroBin, restCapacity, placeBricks, List.reverse_cons,
          List.append_assoc] using hs
      · have hi := ih (N + 1) c ((a - 1) :: lower) (by omega)
          (by intro d hd'; have := hb d (by simp [hd']); omega)
        simp only [firstZeroBin, if_neg hz, restCapacity, placeBricks,
          List.reverse_cons, List.append_assoc, List.singleton_append]
        rw [hs]
        simpa [Nat.add_comm] using hi
  have realization : ∀ (cs : List ℕ) (N : ℕ),
      (∀ c ∈ cs, c ≤ N) →
      placeBricks N cs.reverse (firstZeroBin cs) = (restCapacity N cs).reverse := by
    intro cs N hb
    cases cs with
    | nil => simp [firstZeroBin, restCapacity, placeBricks, step, transfer]
    | cons c cs =>
      have hc := hb c (by simp)
      have hn : ¬ N + 1 ≤ c := by omega
      have hbase : transfer (N + 1) [c] = ([c + (N + 1)], false) := by
        simp [transfer, hn]
      have hp := pass (N + 1) cs.reverse [c]
        (by intro d hd; have := hb d (by simp only [List.mem_reverse] at hd; simp [hd]); omega)
        (by rw [hbase])
      have hs : step (N + 1) (cs.reverse ++ [c]) =
          cs.reverse ++ [c + (N + 1)] := by
        unfold step
        rw [hp, hbase]
        simp
      by_cases hz : c = 0
      · subst c
        simpa [firstZeroBin, restCapacity, placeBricks] using hs
      · have hi := relay cs (N + 1) c [] (by omega)
          (by intro d hd; have := hb d (by simp [hd]); omega)
        simp only [firstZeroBin, if_neg hz, restCapacity, placeBricks,
          List.reverse_cons]
        rw [hs]
        simpa [Nat.add_comm] using hi
  have facts : ∀ (cs : List ℕ) (N : ℕ), (∀ c ∈ cs, c ≤ N) →
      0 < firstZeroBin cs ∧ firstZeroBin cs ≤ cs.length + 1 ∧
      (∀ c ∈ restCapacity N cs, c ≤ N + firstZeroBin cs) ∧
      (restCapacity N cs).length = max cs.length (firstZeroBin cs) ∧
      (∀ i (hi : i < cs.length), i + 1 < firstZeroBin cs → 0 < cs[i]'hi) ∧
      (firstZeroBin cs ≤ cs.length → cs[firstZeroBin cs - 1]? = some 0) ∧
      (∀ i (hi : i < cs.length), i + 1 < firstZeroBin cs →
        (restCapacity N cs)[i]? = some (cs[i]'hi - 1)) ∧
      (restCapacity N cs)[firstZeroBin cs - 1]? = some (N + firstZeroBin cs) ∧
      (∀ i (hi : i < cs.length), firstZeroBin cs < i + 1 →
        (restCapacity N cs)[i]? = some (cs[i]'hi)) := by
    intro cs
    induction cs with
    | nil => intro N hb; simp [firstZeroBin, restCapacity]
    | cons c cs ih =>
      intro N hb
      have hc := hb c (by simp)
      have hb' : ∀ d ∈ cs, d ≤ N + 1 := by
        intro d hd
        have := hb d (by simp [hd])
        omega
      obtain ⟨hpos, hle, hbound, hlength, hprefix, hzero, hdec, hreset, hsuffix⟩ := ih (N + 1) hb'
      by_cases hz : c = 0
      · subst c
        simp only [firstZeroBin, restCapacity, ↓reduceIte, List.length_cons]
        refine ⟨by omega, by omega, ?_, by simp, ?_, by simp, ?_, by simp, ?_⟩
        · intro d hd
          rcases List.mem_cons.mp hd with rfl | hd
          · omega
          · have := hb d (by simp [hd]); omega
        · intro i hi hik; omega
        · intro i hi hik; omega
        · intro i hi hik
          cases i with
          | zero => omega
          | succ i => simp
      · simp only [firstZeroBin, if_neg hz, restCapacity, List.length_cons]
        refine ⟨by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro d hd
          rcases List.mem_cons.mp hd with rfl | hd
          · omega
          · have := hbound d hd; omega
        · rw [hlength]
          omega
        · intro i hi hik
          cases i with
          | zero => simp; omega
          | succ i => simpa using hprefix i (by omega) (by omega)
        · intro hk
          have := hzero (by omega)
          have heq : firstZeroBin cs + 1 - 1 = (firstZeroBin cs - 1) + 1 := by omega
          rw [heq]
          simpa using this
        · intro i hi hik
          cases i with
          | zero => simp
          | succ i => simpa using hdec i (by omega) (by omega)
        · have heq : firstZeroBin cs + 1 - 1 = (firstZeroBin cs - 1) + 1 := by omega
          rw [heq]
          simpa only [List.getElem?_cons_succ, Nat.add_assoc,
            Nat.add_comm 1 (firstZeroBin cs)] using hreset
        · intro i hi hik
          cases i with
          | zero => omega
          | succ i => simpa using hsuffix i (by omega) (by omega)
  obtain ⟨hpos, hle, hbound, hlength, hprefix, hzero, hdec, hreset, hsuffix⟩ :=
    facts s.capacity s.endpoint s.bounded
  let t : RestState := ⟨s.endpoint + firstZeroBin s.capacity,
    restCapacity s.endpoint s.capacity, hbound⟩
  refine ⟨t, ?_, realization s.capacity s.endpoint s.bounded⟩
  refine ⟨hpos, hle, rfl, hlength, ?_, hzero, ?_, hreset, ?_⟩
  · intro j hj
    exact hprefix j.val j.isLt hj
  · intro j hj
    simpa using hdec j.val j.isLt hj
  · intro j hj
    simpa using hsuffix j.val j.isLt hj

#print axioms literal_rest_block

end D5.S3.Combinatorics.GreedyBrick.RestBlock
