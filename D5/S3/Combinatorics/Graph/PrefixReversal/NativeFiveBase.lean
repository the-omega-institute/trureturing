/- GID: D5/S3/Combinatorics/Graph/PrefixReversal/NativeFiveBase
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/PrefixReversal/NativeFiveBase
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Hamiltonian]
   utility: none
   digest: The actual complete F2 cycle spans all 120 permutations at size five. -/

import D5.S3.Combinatorics.Graph.PrefixReversal.NativeF2Coverage

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.PrefixReversal.NativeFiveBase

open D5.S3.Combinatorics.Graph.PrefixReversalZeroStarComplement
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeStarGrafting
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeContactIteration
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeF2Coverage
open D5.S3.Combinatorics.Graph.PrefixReversal.InsertionLayerPartition

private theorem triple_orientations {α : Type} [DecidableEq α]
    {a b c : α} {l : List α} (hp : l.Perm [a, b, c]) :
    (l : Cycle α) = ([a, b, c] : List α) ∨
      (l : Cycle α) = ([a, b, c] : Cycle α).reverse := by
  have ha : a ∈ l := hp.mem_iff.mpr (by simp)
  have hh : (l.rotate (l.idxOf a)).head? = some a := by
    rw [List.head?_rotate (List.idxOf_lt_length_iff.mpr ha)]
    exact List.getElem?_idxOf ha
  have hr : (l : Cycle α) = (l.rotate (l.idxOf a) : List α) :=
    Cycle.coe_eq_coe.mpr ⟨l.idxOf a, rfl⟩
  have hpr : (l.rotate (l.idxOf a)).Perm [a, b, c] := (List.rotate_perm l _).trans hp
  cases e : l.rotate (l.idxOf a) with
  | nil => simp [e] at hh
  | cons d tail =>
    have hd : d = a := by simpa [e] using hh
    subst d
    rw [e] at hpr hr
    have ht : tail.Perm [b, c] := hpr.cons_inv
    rcases List.perm_pair.mp ht with h | h
    · left
      simpa [h] using hr
    · right
      have hs : ([a, c, b] : Cycle α) = ([a, b, c] : Cycle α).reverse := by
        rw [Cycle.reverse_coe]
        exact Cycle.coe_eq_coe.mpr ⟨1, rfl⟩
      have hr' : (l : Cycle α) = ([a, c, b] : Cycle α) := by
        simpa [h] using hr
      exact hr'.trans hs

/-- After deleting labels zero and four, the three remaining labels have one bracelet.
Thus every actual permutation belongs to the independently defined F2 domain. -/
theorem native_five_domain (v : Configuration 4) : F2Domain 4 v := by
  apply (native_f2_layer_iff (by omega : 4 ≤ 4) v).mpr
  let l := (List.ofFn v).filter
    (fun x => decide (x ∉ ({0, Fin.last 4} : Finset (Fin 5))))
  have hp := (v.ofFn_comp_perm (fun x : Fin 5 => x)).filter
    (fun x => decide (x ∉ ({0, Fin.last 4} : Finset (Fin 5))))
  change l.Perm ([1, 2, 3] : List (Fin 5)) at hp
  change (l : Cycle (Fin 5)) = (([1, 2, 3] : List (Fin 5)) : Cycle (Fin 5)) ∨
    (l : Cycle (Fin 5)) = (([1, 2, 3] : List (Fin 5)) : Cycle (Fin 5)).reverse
  exact triple_orientations hp

/-- The existing actual F2 construction is a Hamilton cycle for the reversals
of lengths five, four and three on the full group of 120 permutations. -/
theorem native_five_hamiltonian_cycle :
    ∃ base : Configuration 4,
      ∃ w : (SimpleGraph.mulCayley ({a 4, b 4, c 4} : Set (Configuration 4))).Walk
        base base, w.IsHamiltonianCycle := by
  classical
  obtain ⟨base, w, hw⟩ := native_f2_hamiltonian_cycle (by omega : 4 ≤ 4)
  let f : domainGraph (F2Domain 4) →g
      SimpleGraph.mulCayley ({a 4, b 4, c 4} : Set (Configuration 4)) :=
    { toFun := Subtype.val
      map_rel' := fun h => h }
  have hf : Function.Bijective f :=
    ⟨Subtype.val_injective, fun v => ⟨⟨v, native_five_domain v⟩, rfl⟩⟩
  exact ⟨base.val, w.map f, hw.map hf⟩

#print axioms native_five_domain
#print axioms native_five_hamiltonian_cycle

end D5.S3.Combinatorics.Graph.PrefixReversal.NativeFiveBase
