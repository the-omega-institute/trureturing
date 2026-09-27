/- GID: D5/S1/Words/Permutations/MamedeAdjacentWords
   generality: G
   mirror-B: D5/B/S1/Words/Permutations/MamedeAdjacentWords
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Adjacent-swap words, broad-monotone oscillations and conditional source shapes. -/

import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Tactic

namespace D5.S1.Words.Permutations.MamedeAdjacentWords

/-- The one-based generator `k` swaps positions `k` and `k+1`. -/
def adjacent (n k : Nat) : Equiv.Perm (Fin (n + 1)) :=
  Equiv.swap (Fin.ofNat (n + 1) (k - 1)) (Fin.ofNat (n + 1) k)

/-- Product of an adjacent-swap word, in list order. -/
def wordProduct (n : Nat) (w : List Nat) : Equiv.Perm (Fin (n + 1)) :=
  (w.map (adjacent n)).prod

def validWord (n : Nat) (w : List Nat) : Prop :=
  ∀ k ∈ w, 1 ≤ k ∧ k ≤ n

/-- Minimal length among valid words representing the same permutation. -/
def reducedWord (n : Nat) (w : List Nat) : Prop :=
  validWord n w ∧
    ∀ v, validWord n v → wordProduct n v = wordProduct n w → w.length ≤ v.length

def consecutive : List Nat → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => (a + 1 = b ∨ b + 1 = a) ∧ consecutive (b :: rest)

def descending (hi lo : Nat) : List Nat :=
  (List.range (hi - lo + 1)).map (hi - ·)

def ascending (lo hi : Nat) : List Nat :=
  (List.range (hi - lo + 1)).map (lo + ·)

def internalSpikes : List Nat → List Nat
  | a :: b :: c :: rest =>
    if (a < b ∧ c < b) ∨ (b < a ∧ b < c) then
      b :: internalSpikes (b :: c :: rest)
    else internalSpikes (b :: c :: rest)
  | _ => []

def spikes : List Nat → List Nat
  | [] => []
  | [a] => [a]
  | a :: b :: rest => a :: internalSpikes (a :: b :: rest) ++ [(a :: b :: rest).getLast!]

def segmentLengths : List Nat → List Nat
  | a :: b :: rest => ((a - b) + (b - a)) :: segmentLengths (b :: rest)
  | _ => []

def weakIncreasing : List Nat → Prop
  | a :: b :: rest => a ≤ b ∧ weakIncreasing (b :: rest)
  | _ => True

def oscillation (w : List Nat) : Prop :=
  let lengths := segmentLengths (spikes w)
  weakIncreasing lengths ∨ weakIncreasing lengths.reverse

def singletonWord (n : Nat) (σ : Equiv.Perm (Fin (n + 1))) (w : List Nat) : Prop :=
  reducedWord n w ∧ consecutive w ∧ wordProduct n w = σ

def fullExcursion (m M i j : Nat) : List Nat :=
  descending j m ++ ascending (m + 1) M ++ descending (M - 1) i

def deletedExcursion (m M i : Nat) : List Nat :=
  descending (i - 1) m ++ ascending (m + 1) M ++ descending (M - 1) i

def imageWord (i j : Nat) (p q : List Nat) : List Nat :=
  p ++ descending j i ++ q

/-- The first orientation of Mamede--Santos--Soares Lemma 3.6. -/
def sourceShape (m M i j : Nat) (a p q : List Nat) : Prop :=
  a = p ++ fullExcursion m M i j ++ q ∧
    (∀ k ∈ p, m < k ∧ k < j) ∧
    (∀ k ∈ q, i < k ∧ k < M)

def position (n k : Nat) : Fin (n + 1) :=
  Fin.ofNat (n + 1) (k - 1)

def exactSourceHypotheses (n m M i j : Nat)
    (σ : Equiv.Perm (Fin (n + 1))) : Prop :=
  1 ≤ m ∧ m < i ∧ i ≤ j ∧ j < M ∧ M ≤ n ∧
    σ (position n (M + 1)) = position n m ∧
    σ (position n m) = position n (j + 1) ∧
    σ (position n i) = position n (M + 1) ∧
    σ (position n m) ≠ position n m ∧
    σ (position n (M + 1)) ≠ position n (M + 1) ∧
    (∀ k : Fin (n + 1),
      k.val + 1 < m ∨ M + 1 < k.val + 1 → σ k = k) ∧
    (∃ a, singletonWord n σ a ∧ ¬ oscillation a)

end D5.S1.Words.Permutations.MamedeAdjacentWords
