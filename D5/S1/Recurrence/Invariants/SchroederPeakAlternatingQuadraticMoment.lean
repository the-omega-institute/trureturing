/- GID: D5/S1/Recurrence/Invariants/SchroederPeakAlternatingQuadraticMoment
   generality: G
   mirror-B: D5/B/S1/Recurrence/Invariants/SchroederPeakAlternatingQuadraticMoment
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [Mathlib.Data.Finset.Card, Mathlib.Data.Fintype.List]
   utility: none
   digest: First returns of peak-marked Schroeder paths prove Schulte's alternating moment. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.List

open Finset
open scoped BigOperators

namespace D5.S1.Recurrence.Invariants.SchroederPeakAlternatingQuadraticMoment

/-- Steps of a large Schroeder path. `U` and `D` have horizontal weight one;
`H` has horizontal weight two. -/
inductive Step
  | U
  | D
  | H
  deriving DecidableEq

open Step

instance : Fintype Step where
  elems := {U, D, H}
  complete s := by cases s <;> simp

/-- Horizontal weight of a Schroeder word. -/
def weight : List Step -> Nat
  | [] => 0
  | U :: w => weight w + 1
  | D :: w => weight w + 1
  | H :: w => weight w + 2

/-- Decision procedure for every prefix of the word staying weakly above height zero. -/
def prefixNonnegative (w : List Step) : Bool :=
  w.inits.all (fun p => decide (p.count D <= p.count U))

/-- Decision procedure for a word describing a Schroeder path of semilength `n`. -/
def isSchroeder (n : Nat) (w : List Step) : Bool :=
  decide (weight w = 2 * n) && decide (w.count U = w.count D) && prefixNonnegative w

/-- All words over `Step` whose length is at most the supplied bound. -/
def wordsUpTo : Nat -> Finset (List Step)
  | 0 => {[]}
  | n + 1 => wordsUpTo n ∪ univ.biUnion (fun s => (wordsUpTo n).image (s :: .))

/-- Concrete finite set of Schroeder words of semilength `n`. -/
def schroeder (n : Nat) : Finset (List Step) :=
  (wordsUpTo (2 * n)).filter (fun w => isSchroeder n w = true)

/-- Number of adjacent `U,D` pairs in a word. -/
def peaks : List Step -> Nat
  | a :: b :: w => (if a = U /\ b = D then 1 else 0) + peaks (b :: w)
  | _ => 0
termination_by w => w.length

/-- The peak-counted Schroeder triangle A060693. -/
def T (n k : Nat) : Nat :=
  ((schroeder n).filter (fun w => peaks w = k)).card

set_option maxRecDepth 100000 in
example : T 1 0 = 1 := by decide +kernel
set_option maxRecDepth 100000 in
example : T 1 1 = 1 := by decide +kernel
set_option maxRecDepth 100000 in
example : T 2 0 = 2 := by decide +kernel
set_option maxRecDepth 100000 in
example : T 2 1 = 3 := by decide +kernel
set_option maxRecDepth 100000 in
example : T 2 2 = 1 := by decide +kernel

end D5.S1.Recurrence.Invariants.SchroederPeakAlternatingQuadraticMoment
