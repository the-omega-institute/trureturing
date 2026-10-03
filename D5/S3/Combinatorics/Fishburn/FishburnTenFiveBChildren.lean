/- GID: D5/S3/Combinatorics/Fishburn/FishburnTenFiveBChildren
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Fishburn/FishburnTenFiveBChildren
   mirror-E: none(waiver:ordered-b-insertion-children)
   anchors: []
   utility: none
   digest: B labels retain interval size and the distinct ranks of their ordered child families. -/

import D5.S3.Combinatorics.Fishburn.FishburnTenFiveBInvariant
import D5.S3.Combinatorics.Fishburn.FishburnTenFiveBTree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Fishburn.FishburnTenFiveBChildren

open D5.S3.Combinatorics.Fishburn FishburnDefs FishburnTenFiveBTree
open FishburnTenFiveBSites FishburnTenFiveBInvariant FishburnTenFivePrepend

def State (n : ℕ) (p : List ℕ) (label : Label) : Prop :=
  ∃ start finish : ℕ, 1 ≤ start ∧ start ≤ finish ∧ finish ≤ p.length ∧
    (∀ gap, gap ≤ p.length →
      (p.insertIdx gap (n + 1) ∈ avoiders (n + 1) [[1, 3, 2, 4], [3, 1, 2, 4]] ↔
        gap = 0 ∨ start ≤ gap ∧ gap ≤ finish)) ∧
    (∀ first second, first < second → second < start →
      p.getD second 0 < p.getD first 0) ∧
    (∀ edge, start ≤ edge → edge < finish → p.getD (edge - 1) 0 < p.getD edge 0) ∧
    ∃ position : ℕ, position < p.length ∧ p.getD position 0 = n ∧
      match label with
      | .L => position < start ∧ start = finish
      | .M sites => 3 ≤ sites ∧ finish - start + 2 = sites ∧
          start ≤ position ∧ position + 1 = finish
      | .R sites => 2 ≤ sites ∧ finish - start + 2 = sites ∧ finish ≤ position

def edgeLabel : (label : Label) → Paths 1 label → Label
  | .L, .inl _ => .L
  | .L, .inr _ => .M 3
  | .M _, .inl (.inl _) => .L
  | .M _, .inl (.inr ⟨edge, _⟩) => .R (edge.val + 2)
  | .M sites, .inr _ => .M (sites + 1)
  | .R _, .inl _ => .L
  | .R _, .inr ⟨edge, _⟩ => .R (edge.val + 2)

def edgeIndex : (label : Label) → Paths 1 label → ℕ
  | .L, .inl _ => 0
  | .L, .inr _ => 1
  | .M _, .inl (.inl _) => 0
  | .M _, .inl (.inr ⟨edge, _⟩) => edge.val + 1
  | .M sites, .inr _ => sites - 1
  | .R _, .inl _ => 0
  | .R _, .inr ⟨edge, _⟩ => edge.val + 1


end D5.S3.Combinatorics.Fishburn.FishburnTenFiveBChildren
