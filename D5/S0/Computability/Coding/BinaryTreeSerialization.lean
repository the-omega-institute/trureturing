/- GID: D5/S0/Computability/Coding/BinaryTreeSerialization
   generality: G
   mirror-B: D5/B/S0/Computability/Coding/BinaryTreeSerialization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A recursive binary parser recovers the tagged FreeMagma tree and its unused suffix. -/

import Mathlib.Algebra.Free

set_option autoImplicit false

namespace D5.S0.Computability.Coding.BinaryTreeSerialization

/-- Binary trees with the two source atoms as their leaf labels. -/
abbrev BinaryTree := FreeMagma Bool

/-- The source serialization uses `false` as the leaf marker and `true` as the branch marker. -/
def code : BinaryTree → List Bool
  | .of false => [false, false]
  | .of true => [false, true]
  | .mul s t => true :: (code s ++ code t)

/-- A fuel-bounded parser; the fuel is consumed once per parser call. -/
def parseFuel : Nat → List Bool → Option (BinaryTree × List Bool)
  | 0, _ => none
  | _n + 1, false :: false :: rest => some (.of false, rest)
  | _n + 1, false :: true :: rest => some (.of true, rest)
  | n + 1, true :: rest =>
      match parseFuel n rest with
      | some (s, rest') =>
          match parseFuel n rest' with
          | some (t, rest'') => some (.mul s t, rest'')
          | none => none
      | none => none
  | _, _ => none

def parse (xs : List Bool) : Option (BinaryTree × List Bool) :=
  parseFuel xs.length xs

/-- Recursive parsing preserves arbitrary suffixes. Injectivity, prefix freedom, and
the empty-suffix round trip are residual corollaries of this recovery theorem. -/
theorem serialization_spec :
    (∀ (t : BinaryTree) (rest : List Bool),
      parse (code t ++ rest) = some (t, rest)) := by
  have hmain : ∀ (n : Nat) (u : BinaryTree) (r : List Bool),
      (code u).length ≤ n → parseFuel n (code u ++ r) = some (u, r) := by
    intro n
    induction n with
    | zero =>
        intro u r hn
        cases u with
        | of b => cases b <;> simp [code] at hn
        | mul s t => simp [code] at hn
    | succ n ih =>
        intro u r hn
        cases u with
        | of b =>
            cases b <;> simp [code, parseFuel]
        | mul s t =>
            simp only [code, List.length_cons, Nat.succ_le_iff] at hn
            have hcode' : (code s).length + (code t).length < n + 1 := by
              simpa [List.length_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hn
            have hcode : (code s).length + (code t).length ≤ n := by
              omega
            have hs : (code s).length ≤ n := by omega
            have ht : (code t).length ≤ n := by omega
            change parseFuel (Nat.succ n) (true :: ((code s ++ code t) ++ r)) = _
            simp only [parseFuel]
            rw [List.append_assoc, ih s (code t ++ r) hs]
            simp only [ih t r ht]
  have hparse (t : BinaryTree) (rest : List Bool) :
      parse (code t ++ rest) = some (t, rest) := by
    apply hmain (code t ++ rest).length t rest
    simp
  exact hparse

#print axioms serialization_spec

end D5.S0.Computability.Coding.BinaryTreeSerialization
