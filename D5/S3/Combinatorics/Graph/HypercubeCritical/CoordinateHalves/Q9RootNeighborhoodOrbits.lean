import Mathlib.Data.Fintype.Defs
import Mathlib.Data.List.Sort

/-! Orbit representatives for the first two layers around a cubic vertex.
A column records which of the three branches use a specified free cube axis. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9RootNeighborhoodOrbits

abbrev Columns := List (Fin 8)

/-- Number of free axes used by a branch. -/
def branchSize (columns : Columns) (branch : Fin 3) : Nat :=
  columns.countP fun c => c.val.testBit branch.val

/-- Relabel the branches by precomposing the three bits of an axis column. -/
def relabel (σ : Equiv.Perm (Fin 3)) (c : Fin 8) : Fin 8 :=
  let bit (i : Fin 3) := (c.val.testBit (σ i).val).toNat
  Fin.ofNat 8 (bit 0 + 2 * bit 1 + 4 * bit 2)

/-- Permutations of branches of equal size. -/
def branchPermutations (short : Bool) : List (Equiv.Perm (Fin 3)) :=
  let identity := Equiv.refl (Fin 3)
  let a := Equiv.swap (0 : Fin 3) 1
  let b := Equiv.swap (1 : Fin 3) 2
  if short then [identity, a]
  else [identity, a, b, Equiv.swap 0 2, a.trans b, b.trans a]

/-- Axis lists after relabeling the equal branches and the five free axes. -/
def representatives (short : Bool) : List Columns :=
  if short then [
    [0, 0, 0, 3, 7], [0, 0, 1, 2, 7], [0, 0, 1, 3, 6], [0, 0, 3, 3, 4],
    [0, 1, 1, 2, 6], [0, 1, 2, 3, 4], [1, 1, 2, 2, 4]]
  else [
    [0, 0, 0, 7, 7], [0, 0, 1, 6, 7], [0, 0, 3, 5, 6], [0, 1, 1, 6, 6],
    [0, 1, 2, 4, 7], [0, 1, 2, 5, 6], [1, 1, 2, 4, 6]]

private def sorted (columns : Columns) : Columns := columns.mergeSort (· ≤ ·)

private def covered (short : Bool) (columns : Columns) : Bool :=
  (branchPermutations short).any fun σ =>
    (representatives short).any fun prototype => (columns.map (relabel σ)).isPerm prototype

private theorem length_five {α : Type*} {l : List α} (h : l.length = 5) :
    ∃ a b c d e, [a, b, c, d, e] = l := by
  obtain ⟨a, t, ha, ht⟩ := (List.length_eq_succ_iff (n := 4)).mp h
  obtain ⟨b, u, hb, hu⟩ := (List.length_eq_succ_iff (l := t) (n := 3)).mp ht
  obtain ⟨c, v, hc, hv⟩ := (List.length_eq_succ_iff (l := u) (n := 2)).mp hu
  obtain ⟨d, w, hd, hw⟩ := (List.length_eq_succ_iff (l := v) (n := 1)).mp hv
  obtain ⟨e, z, he, hz⟩ := (List.length_eq_succ_iff (l := w) (n := 0)).mp hw
  exact ⟨a, b, c, d, e, by rw [← ha, ← hb, ← hc, ← hd, ← he, List.length_eq_zero_iff.mp hz]⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 12000000 in
-- The kernel checks all ordered lists of five columns.
private theorem checked (short : Bool) (a b c d e : Fin 8) :
    let cols : Columns := [a, b, c, d, e]
    cols.Pairwise (· ≤ ·) →
      branchSize cols 0 = 2 → branchSize cols 1 = 2 →
      branchSize cols 2 = (if short then 1 else 2) → covered short cols = true := by
  revert short a b c d e
  decide +kernel

/-- Every two-layer pattern with branch counts (2,2,1) or (2,2,2) is
represented by a listed orbit under branch and free-axis permutations. -/
theorem covered_by_representatives (short : Bool) (columns : Columns)
    (hlen : columns.length = 5) (h0 : branchSize columns 0 = 2)
    (h1 : branchSize columns 1 = 2) (h2 : branchSize columns 2 = (if short then 1 else 2)) :
    ∃ σ ∈ branchPermutations short, ∃ prototype ∈ representatives short,
      (columns.map (relabel σ)).Perm prototype := by
  let ordered := sorted columns
  have hp : ordered.Perm columns := List.mergeSort_perm _ _
  have hs : ordered.Pairwise (· ≤ ·) := List.pairwise_mergeSort' (· ≤ ·) _
  have hsize (i : Fin 3) : branchSize ordered i = branchSize columns i :=
    hp.countP_eq _
  obtain ⟨a, b, c, d, e, he⟩ := length_five (hp.length_eq.trans hlen)
  have hc : covered short ordered = true := by
    rw [← he] at hs hsize ⊢
    exact checked short a b c d e hs ((hsize 0).trans h0) ((hsize 1).trans h1)
      ((hsize 2).trans h2)
  obtain ⟨σ, hσ, hm⟩ := List.any_eq_true.mp hc
  obtain ⟨prototype, hprototype, hp'⟩ := List.any_eq_true.mp hm
  exact ⟨σ, hσ, prototype, hprototype, (hp.map _).symm.trans (List.isPerm_iff.mp hp')⟩

#print axioms covered_by_representatives

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9RootNeighborhoodOrbits
