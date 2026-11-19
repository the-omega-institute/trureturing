import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SeventyTwoSignedSearch
import Batteries.Tactic.OpenPrivate

/-! The signed path test reconstructs the midpoint of each compressed edge. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SeventyTwoSignedCompletion

open BalancedCriticalSpectrum (Q)
open Q9SeventyTwoSignedSearch (signed_middle_unique)
open private middle_of_signed_path from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SeventyTwoSignedSearch
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)

local notation "flip" => BalancedCriticalSpectrum.flip

private def tests (x y : Q 9) (product : ℤ) (i j : Fin 9) : Bool :=
  decide (flip (flip x i) j = y) &&
    decide (truePrefixSign x i * truePrefixSign (flip x i) j = product)

private theorem tests_iff (x y : Q 9) (product : ℤ) (i j : Fin 9) :
    tests x y product i j = true ↔
      flip (flip x i) j = y ∧ truePrefixSign x i * truePrefixSign (flip x i) j = product := by
  simp [tests]

private def firstFlip (x y : Q 9) (product : ℤ) : Option (Fin 9) :=
  (List.finRange 9).find? fun i => (List.finRange 9).any (tests x y product i)

private theorem firstFlip_eq {x y : Q 9} (hxy : x ≠ y) {product : ℤ}
    {i j : Fin 9} (h : tests x y product i j = true) : firstFlip x y product = some i := by
  unfold firstFlip
  cases hfind : (List.finRange 9).find? (fun k => (List.finRange 9).any (tests x y product k)) with
  | none =>
    exact (List.find?_eq_none.mp hfind i (List.mem_finRange i)
      (List.any_eq_true.mpr ⟨j, List.mem_finRange j, h⟩)).elim
  | some k =>
    have hk : (List.finRange 9).any (tests x y product k) = true :=
      List.find?_some (p := fun a => (List.finRange 9).any (tests x y product a)) hfind
    obtain ⟨l, _, hl⟩ := List.any_eq_true.mp hk
    obtain ⟨hy, hs⟩ := (tests_iff x y product i j).mp h
    obtain ⟨hy', hs'⟩ := (tests_iff x y product k l).mp hl
    exact congrArg some (signed_middle_unique hxy hy hy' (hs.trans hs'.symm)).symm

/-- The midpoint and its signing value are computed from the two high
vertices and their signed values. -/
def signedMiddle (x y : Q 9) (a b : ℤ) : Option (Q 9 × ℤ) :=
  (firstFlip x y (a * b)).map fun i => (flip x i, a * truePrefixSign x i)

/-- Every realized two-step path with distinct endpoints and unit values
is recovered by the signed midpoint computation. -/
theorem signedMiddle_of_path {x y m : Q 9} {z : Q 9 → ℤ} (hxy : x ≠ y)
    (hxm : (hypercube 9).Adj x m) (hmy : (hypercube 9).Adj m y)
    (hx : z x = 1 ∨ z x = -1) (hm : z m = 1 ∨ z m = -1)
    (h : ∀ u (i : Fin 9), (u = x ∧ flip u i = m) ∨ (u = m ∧ flip u i = y) →
      truePrefixSign u i = z u * z (flip u i)) :
    signedMiddle x y (z x) (z y) = some (m, z m) := by
  obtain ⟨i, j, hi, hj, hs, hz⟩ := middle_of_signed_path hxm hmy hx hm h
  have htest : tests x y (z x * z y) i j = true := by
    apply (tests_iff ..).mpr
    rw [← hi]
    exact ⟨hj.symm, hs⟩
  simp only [signedMiddle, firstFlip_eq hxy htest, Option.map_some, ← hi, ← hz]

#print axioms signedMiddle_of_path

end D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SeventyTwoSignedCompletion
