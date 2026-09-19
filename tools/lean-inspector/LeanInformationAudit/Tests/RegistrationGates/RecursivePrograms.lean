import Mathlib.Data.List.Permutation
import Mathlib.Data.List.Range

/-!
Source-faithful engineering fixtures for #8847. Definitions and universal proofs
adapted from CyclicStackPreimagesCore/Candidates, consumer #8660, PR #8705
head 1e472756a3369712c74c7051c5e0b57ea301db86. These fixtures own their native
source evidence and do not import the unmerged consumer. The source's unused
finite-word provenance let is omitted; both complete universal laws are retained.
-/

namespace LeanInformationAudit.Tests.RecursivePrograms

def forbidden (x a b : Nat) : Bool :=
  decide (x < a ∧ a < b ∨ b < x ∧ x < a ∨ a < b ∧ b < x)

def drain (x : Nat) : List Nat → List Nat × List Nat
  | a :: b :: stack =>
      if forbidden x a b then
        let rest := drain x (b :: stack)
        (a :: rest.1, rest.2)
      else ([], a :: b :: stack)
  | stack => ([], stack)

def process : List Nat → List Nat → List Nat
  | [], stack => stack
  | x :: input, stack =>
      let step := drain x stack
      step.1 ++ process input (x :: step.2)

def run : List Nat → List Nat → List Nat × List Nat
  | [], stack => ([], stack)
  | x :: input, stack =>
      let step := drain x stack
      let rest := run input (x :: step.2)
      (step.1 ++ rest.1, rest.2)

theorem process_eq_run (input stack : List Nat) :
    process input stack = (run input stack).1 ++ (run input stack).2 := by
  induction input generalizing stack with
  | nil => rfl
  | cons x input ih =>
      simp only [process, run]
      let step := drain x stack
      rw [ih]
      simp only [List.append_assoc]

def target (n : Nat) : List Nat :=
  List.range' 1 (n / 2) ++ (List.range' (n / 2 + 1) (n - n / 2)).reverse

theorem target_perm_range (n : Nat) : (target n).Perm (List.range' 1 n) := by
  let m := n / 2
  have hm : m ≤ n := Nat.div_le_self n 2
  have hreverse : (List.range' (m + 1) (n - m)).reverse.Perm
      (List.range' (m + 1) (n - m)) := List.reverse_perm _
  have happ := hreverse.append_left (List.range' 1 m)
  have hrange : List.range' 1 m ++ List.range' (m + 1) (n - m) =
      List.range' 1 n := by
    rw [show m + 1 = 1 + m by omega, List.range'_append_1]
    congr 1
    omega
  simpa only [target, m] using happ.trans (List.Perm.of_eq hrange)

end LeanInformationAudit.Tests.RecursivePrograms

