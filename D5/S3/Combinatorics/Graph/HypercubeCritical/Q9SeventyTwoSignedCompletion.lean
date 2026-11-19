import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SeventyTwoSignedSearch
import Batteries.Tactic.OpenPrivate
import Mathlib.Data.List.OfFn

/-! The signed path test reconstructs the midpoint of each compressed edge. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SeventyTwoSignedCompletion

open BalancedCriticalSpectrum (Q)
open Q9SeventyTwoSignedSearch (modelEdges signed_middle_unique)
open Q9EightCubicGraphCertificate (modelAdj)
open BalancedCubeLowerBound (coordinateSlice)
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

private def signedRecords (wagner : Bool) (p : Fin 8 → Q 9) (s : Fin 8 → ℤ) :
    List (Q 9 × ℤ) :=
  List.ofFn (fun i => (p i, s i)) ++
    (List.finRange 8).flatMap fun i => (List.finRange 8).filterMap fun j =>
      if i < j ∧ modelAdj wagner i j = true then signedMiddle (p i) (p j) (s i) (s j)
      else none

private def valueIn (entries : List (Q 9 × ℤ)) (x : Q 9) : ℤ :=
  ((entries.find? fun e => decide (e.1 = x)).map Prod.snd).getD 0

/-- Form the full signed vector by computing the high and middle records in
the first half and applying the eigenvector row to obtain the second half. -/
def complete (wagner : Bool) (p : Fin 8 → Q 9) (s : Fin 8 → ℤ) (x : Q 9) : ℤ :=
  let value := valueIn (signedRecords wagner p s)
  if x 0 = false then value x
  else
    let y := flip x 0
    3 * value y -
      ∑ i ∈ Finset.univ.erase (0 : Fin 9), truePrefixSign y i * value (flip y i)

/-- Every normalized signed support with its realized model incidences is
recovered exactly by the finite computation on the high vertices. -/
theorem complete_eq_of_actual {U : Finset (Q 9)} {wagner : Bool}
    (p : Fin 8 ↪ Q 9)
    (m : (modelEdges wagner : Set (Fin 8 × Fin 8)) ↪ Q 9)
    (z : Q 9 → ℤ)
    (hU : coordinateSlice U false = Finset.univ.map p ∪ Finset.univ.map m)
    (hm : ∀ e k, (hypercube 9).Adj (m e) (p k) ↔ k = e.val.1 ∨ k = e.val.2)
    (hunit : ∀ x ∈ U, z x = 1 ∨ z x = -1) (hzero : ∀ x ∉ U, z x = 0)
    (hsign : ∀ x ∈ U, ∀ i : Fin 9, flip x i ∈ U →
      truePrefixSign x i = z x * z (flip x i))
    (hrow : ∀ y, z (flip y 0) =
      3 * z y - ∑ i ∈ Finset.univ.erase (0 : Fin 9), truePrefixSign y i * z (flip y i)) :
    complete wagner p (fun k => z (p k)) = z := by
  let entries := signedRecords wagner p (fun k => z (p k))
  have highMem (k : Fin 8) : p k ∈ Finset.univ.map p :=
    Finset.mem_map.mpr ⟨k, Finset.mem_univ k, rfl⟩
  have midMem (e : (modelEdges wagner : Set (Fin 8 × Fin 8))) :
      m e ∈ Finset.univ.map m := Finset.mem_map.mpr ⟨e, Finset.mem_univ e, rfl⟩
  have memU {x : Q 9} (hx : x ∈ Finset.univ.map p ∪ Finset.univ.map m) : x ∈ U :=
    (Finset.mem_filter.mp (hU.symm ▸ hx)).1
  have actualMid (e : (modelEdges wagner : Set (Fin 8 × Fin 8))) :
      signedMiddle (p e.val.1) (p e.val.2) (z (p e.val.1)) (z (p e.val.2)) =
        some (m e, z (m e)) := by
    have hx := memU (Finset.mem_union_left _ (highMem e.val.1))
    have hy := memU (Finset.mem_union_left _ (highMem e.val.2))
    have hv := memU (Finset.mem_union_right _ (midMem e))
    apply signedMiddle_of_path
      (fun he => (Finset.mem_filter.mp e.property).2.1.ne (p.injective he))
      ((hm e e.val.1).mpr (Or.inl rfl)).symm ((hm e e.val.2).mpr (Or.inr rfl))
      (hunit _ hx) (hunit _ hv)
    rintro u i (⟨rfl, hi⟩ | ⟨rfl, hi⟩)
    · exact hsign _ hx _ (hi.symm ▸ hv)
    · exact hsign _ hv _ (hi.symm ▸ hy)
  have midRecord (i j : Fin 8) (hij : i < j ∧ modelAdj wagner i j = true) :
      ∃ val : Q 9 × ℤ,
        signedMiddle (p i) (p j) (z (p i)) (z (p j)) = some val ∧ val.2 = z val.1 := by
    let e : (modelEdges wagner : Set (Fin 8 × Fin 8)) :=
      ⟨(i, j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩⟩
    exact ⟨(m e, z (m e)), actualMid e, rfl⟩
  have recordCorrect (v : Q 9 × ℤ) (hv : v ∈ entries) : v.2 = z v.1 := by
    change v ∈ signedRecords wagner p (fun k => z (p k)) at hv
    rw [signedRecords, List.mem_append] at hv
    rcases hv with hv | hv
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hv
      rfl
    · obtain ⟨i, _, hv⟩ := List.mem_flatMap.mp hv
      obtain ⟨j, _, hj⟩ := List.mem_filterMap.mp hv
      split at hj
      · rename_i he
        obtain ⟨v', hs, hval⟩ := midRecord i j he
        rw [hs, Option.some.injEq] at hj
        exact hj ▸ hval
      · simp at hj
  have recordsCover (x : Q 9) (hx : x ∈ coordinateSlice U false) : (x, z x) ∈ entries := by
    rw [hU] at hx
    change (x, z x) ∈ signedRecords wagner p (fun k => z (p k))
    rw [signedRecords, List.mem_append]
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hx
      exact Or.inl (List.mem_ofFn.mpr ⟨i, rfl⟩)
    · obtain ⟨e, _, rfl⟩ := Finset.mem_map.mp hx
      apply Or.inr
      refine List.mem_flatMap.mpr ⟨e.val.1, List.mem_finRange _, ?_⟩
      refine List.mem_filterMap.mpr ⟨e.val.2, List.mem_finRange _, ?_⟩
      rw [ite_eq_left (Finset.mem_filter.mp e.property).2]
      exact actualMid e
  have valueEq (x : Q 9) (hx : x 0 = false) : valueIn entries x = z x := by
    unfold valueIn
    cases hfind : entries.find? (fun v => decide (v.1 = x)) with
    | none =>
      have hnot : x ∉ U := by
        intro hxU
        exact List.find?_eq_none.mp hfind (x, z x)
          (recordsCover x (Finset.mem_filter.mpr ⟨hxU, hx⟩)) (by simp)
      exact (hzero x hnot).symm
    | some v =>
      have hv : v.1 = x :=
        of_decide_eq_true (List.find?_some (p := fun a : Q 9 × ℤ => decide (a.1 = x)) hfind)
      exact (recordCorrect v (List.mem_of_find?_eq_some hfind)).trans (congrArg z hv)
  funext x
  change (if x 0 = false then valueIn entries x
    else let y := flip x 0
         3 * valueIn entries y -
           ∑ i ∈ Finset.univ.erase (0 : Fin 9), truePrefixSign y i * valueIn entries (flip y i))
      = z x
  by_cases hx : x 0 = false
  · rw [ite_eq_left hx, valueEq x hx]
  · rw [ite_eq_right hx]
    let y := flip x 0
    have hy : y 0 = false := by
      cases hb : x 0
      · exact (hx hb).elim
      · simp [y, hb]
    have hs :
        (∑ i ∈ Finset.univ.erase (0 : Fin 9), truePrefixSign y i * valueIn entries (flip y i)) =
          ∑ i ∈ Finset.univ.erase (0 : Fin 9), truePrefixSign y i * z (flip y i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [valueEq]
      exact (Function.update_of_ne (Finset.mem_erase.mp hi).1.symm _ _).trans hy
    change 3 * valueIn entries y - _ = z x
    rw [valueEq y hy, hs, ← hrow, BalancedCriticalSpectrum.flip_flip]

#print axioms complete_eq_of_actual

end D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SeventyTwoSignedCompletion
