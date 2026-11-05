/-
  Uncompiled source candidate for the arbitrary finite parity-block collision.

  This file is a formalization boundary, not a compilation or verification claim.
  The concrete block constructor is the pair/triple table in Research.md.
-/
import D5.S3.Combinatorics.CircularWords.CircularDeletionTransport
import D5.S3.Combinatorics.CircularWords.DisjointBlockContraction
import Mathlib.Data.Finsupp.Basic

set_option autoImplicit false
namespace D5.S3.Combinatorics.CircularWords.ArbitraryBlockParityCollision

open D5.S3.Combinatorics.CircularWords.CircularDeletionTransport
open D5.S3.Combinatorics.CircularWords.DisjointBlockContraction
open scoped Classical

universe u
variable {α : Type u} [DecidableEq α]
noncomputable section

/-- A state-indexed family of actual cycles with one deletion-erasing bit per label.
The concrete instance concatenates the pair blocks and the four three-block words
listed in Research.md. -/
structure BlockEncoding (A : Finset α) (d : Nat) where
  cycle : (Fin d → Bool) → Cycle α
  nodup : ∀ s, (cycle s).Nodup
  support : ∀ s, (cycle s).toFinset = A
  injective : Function.Injective cycle
  erase : ∀ i ∈ A, ∃ j : Fin d, ∀ s,
    delete i (cycle s) = delete i (Function.update s j (Bool.not (s j)))

/-- Parity of a Boolean state. -/
def parity {d : Nat} (s : Fin d → Bool) : Bool :=
  decide ((∑ j : Fin d, if s j then 1 else 0) % 2 = 1)

/-- The even/odd Finsupp law attached to a block encoding. -/
def parityLaw {A : Finset α} {d : Nat} (E : BlockEncoding A d)
    (target : Bool) : Cycle α →₀ ℚ :=
  ∑ s in (Finset.univ.filter (fun s : Fin d → Bool => parity s = target)),
    Finsupp.single (E.cycle s) ((2 : ℚ) ^ (d - 1))⁻¹

/-- Generic parity pairing: once the block encoding exists, all required facts
follow from the fixed-coordinate involution and Finsupp fiber counting.
The proof is intentionally left open in this uncompiled candidate. -/
theorem parityLaw_collision {A : Finset α} {d : Nat} (E : BlockEncoding A d)
    (hd : 2 ≤ d) :
    (∀ C ∈ (parityLaw E false).support ∪ (parityLaw E true).support,
      C.Nodup ∧ C.toFinset = A) ∧
    (∀ C, 0 ≤ parityLaw E false C ∧ 0 ≤ parityLaw E true C) ∧
    (Finsupp.mapDomain (fun _ : Cycle α => ()) (parityLaw E false)) () = 1 ∧
    (Finsupp.mapDomain (fun _ : Cycle α => ()) (parityLaw E true)) () = 1 ∧
    Disjoint (parityLaw E false).support (parityLaw E true).support ∧
    (∀ i ∈ A,
      Finsupp.mapDomain (delete i) (parityLaw E false) =
        Finsupp.mapDomain (delete i) (parityLaw E true)) := by
  sorry

/-- The concrete pair/triple block constructor.  For even |A| it uses only
2-block reversals; for odd |A| it starts with the four three-block words
`abc`, `acb`, `bca`, `cba` and then uses 2-block reversals. -/
theorem exists_blockEncoding (A : Finset α) (hA : 4 ≤ A.card) :
    ∃ d, 2 ≤ d ∧ Nonempty (BlockEncoding A d) := by
  sorry

/-- Final arbitrary-size collision theorem in the existing Cycle/Finsupp API. -/
theorem arbitrary_block_parity_collision (A : Finset α) (hA : 4 ≤ A.card) :
    ∃ μ ν : Cycle α →₀ ℚ,
      (∀ C ∈ μ.support ∪ ν.support, C.Nodup ∧ C.toFinset = A) ∧
      (∀ C, 0 ≤ μ C ∧ 0 ≤ ν C) ∧
      (Finsupp.mapDomain (fun _ : Cycle α => ()) μ) () = 1 ∧
      (Finsupp.mapDomain (fun _ : Cycle α => ()) ν) () = 1 ∧
      Disjoint μ.support ν.support ∧
      (∀ i ∈ A,
        Finsupp.mapDomain (delete i) μ = Finsupp.mapDomain (delete i) ν) := by
  sorry

end
end D5.S3.Combinatorics.CircularWords.ArbitraryBlockParityCollision
