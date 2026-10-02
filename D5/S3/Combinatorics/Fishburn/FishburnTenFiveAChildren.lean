/- GID: D5/S3/Combinatorics/Fishburn/FishburnTenFiveAChildren
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Fishburn/FishburnTenFiveAChildren
   mirror-E: none(waiver:ordered-a-insertion-children)
   anchors: []
   utility: none
   digest: A labels distinguish active-gap shapes and retain both ranked P children of Q. -/

import D5.S3.Combinatorics.Fishburn.FishburnTenFiveAInvariant
import D5.S3.Combinatorics.Fishburn.FishburnTenFiveATree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Fishburn.FishburnTenFiveAChildren

open D5.S3.Combinatorics.Fishburn FishburnDefs FishburnTenFiveATree
open FishburnTenFiveASites FishburnTenFiveAInvariant FishburnTenFivePrepend

def State (n : ℕ) (p : List ℕ) (label : Label) : Prop :=
  ∃ start : ℕ, 1 ≤ start ∧ start ≤ p.length ∧
    (∀ gap, gap ≤ p.length →
      (p.insertIdx gap (n + 1) ∈ avoiders (n + 1) [[1, 3, 2, 4], [1, 4, 2, 3]] ↔
        gap = 0 ∨ gap = start ∨ (label = .P ∨ label = .Q) ∧ gap = start + 1)) ∧
    ((label = .P ∨ label = .Q) → start < p.length ∧
      p.getD (start - 1) 0 < p.getD start 0) ∧
    ∃ position : ℕ, position < p.length ∧ p.getD position 0 = n ∧
      match label with
      | .D | .Q => position < start
      | .E => start ≤ position
      | .P => position = start

def edgeLabel : (label : Label) → Paths 1 label → Label
  | .D, .inl _ => .D
  | .D, .inr _ => .P
  | .E, .inl _ => .D
  | .E, .inr _ => .E
  | .P, .inl _ => .Q
  | .P, .inr (.inl _) => .E
  | .P, .inr (.inr _) => .P
  | .Q, .inl _ => .Q
  | .Q, .inr (.inl _) => .P
  | .Q, .inr (.inr _) => .P

def edgeIndex : (label : Label) → Paths 1 label → ℕ
  | .D, .inl _ => 0
  | .D, .inr _ => 1
  | .E, .inl _ => 0
  | .E, .inr _ => 1
  | .P, .inl _ => 0
  | .P, .inr (.inl _) => 1
  | .P, .inr (.inr _) => 2
  | .Q, .inl _ => 0
  | .Q, .inr (.inl _) => 1
  | .Q, .inr (.inr _) => 2


end D5.S3.Combinatorics.Fishburn.FishburnTenFiveAChildren
