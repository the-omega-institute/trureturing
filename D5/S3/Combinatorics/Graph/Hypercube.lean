/- GID: D5/S3/Combinatorics/Graph/Hypercube
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Hypercube
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.DegreeSum, mathlib/module/Mathlib.InformationTheory.Hamming]
   utility: none
   digest: The Boolean hypercube is regular of degree its dimension and has the corresponding edge count. -/

import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.InformationTheory.Hamming

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.Hypercube

open scoped Classical

/-- The Boolean hypercube joins vertices whose Hamming distance is exactly one. -/
def hypercube (n : ℕ) : SimpleGraph (Fin n → Bool) where
  Adj x y := hammingDist x y = 1
  symm := ⟨fun x y h => (hammingDist_comm y x).trans h⟩
  loopless := ⟨fun x => by simp⟩

/-- Every vertex of the `n`-dimensional Boolean hypercube has exactly `n` neighbours. -/
theorem hypercube_regular (n : ℕ) : (hypercube n).IsRegularOfDegree n := by
  intro x
  rw [← SimpleGraph.card_neighborSet_eq_degree]
  let flip (i : Fin n) : Fin n → Bool := Function.update x i (!x i)
  have flip_adj (i : Fin n) : (hypercube n).Adj x (flip i) := by
    change (Finset.univ.filter (fun j => x j ≠ flip i j)).card = 1
    have hs : Finset.univ.filter (fun j => x j ≠ flip i j) = {i} := by
      ext j
      by_cases h : j = i
      · subst j
        simp [flip]
      · simp [flip, h]
    rw [hs, Finset.card_singleton]
  let f : Fin n → (hypercube n).neighborSet x := fun i => ⟨flip i, flip_adj i⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j h
      by_contra hij
      have he := congrArg (fun y : (hypercube n).neighborSet x => y.val i) h
      simp [f, flip, Function.update_of_ne hij] at he
    · intro y
      have hy : (Finset.univ.filter (fun i => x i ≠ y.val i)).card = 1 := y.property
      obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hy
      refine ⟨i, Subtype.ext ?_⟩
      change flip i = y.val
      funext j
      have hmem (k : Fin n) : x k ≠ y.val k ↔ k = i := by
        have := Finset.ext_iff.mp hi k
        simpa using this
      by_cases hji : j = i
      · subst j
        have hne := (hmem i).mpr rfl
        simp only [flip, Function.update_self]
        cases hx : x i <;> cases hyi : y.val i <;> simp_all
      · have heq : x j = y.val j := by
          by_contra hne
          exact hji ((hmem j).mp hne)
        simpa [flip, Function.update_of_ne hji] using heq
  exact (Fintype.card_congr (Equiv.ofBijective f hf)).symm.trans (Fintype.card_fin n)

/-- The `n`-dimensional Boolean hypercube has `n * 2 ^ (n - 1)` edges, also for `n = 0`. -/
theorem hypercube_edge_count (n : ℕ) :
    (hypercube n).edgeFinset.card = n * 2 ^ (n - 1) := by
  have h := (hypercube n).sum_degrees_eq_twice_card_edges
  simp only [(hypercube_regular n).degree_eq, Finset.sum_const, Finset.card_univ,
    Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, smul_eq_mul] at h
  cases n with
  | zero =>
      simp only [pow_zero, mul_zero, zero_mul] at *
      omega
  | succ n =>
      simp only [Nat.add_sub_cancel, pow_succ] at *
      apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2)
      calc
        2 * (hypercube (n + 1)).edgeFinset.card = 2 ^ n * 2 * (n + 1) := h.symm
        _ = 2 * ((n + 1) * 2 ^ n) := by ac_rfl

end D5.S3.Combinatorics.Graph.Hypercube
