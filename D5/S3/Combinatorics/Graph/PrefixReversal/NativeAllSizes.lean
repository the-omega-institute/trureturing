/- GID: D5/S3/Combinatorics/Graph/PrefixReversal/NativeAllSizes
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/PrefixReversal/NativeAllSizes
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The canonical final supply frame has a literal three-label base. -/
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeThreeLabelFullDomain
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeFourBase
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeFiveBase
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2ParentCycle

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.PrefixReversal.NativeAllSizes

open D5.S3.Combinatorics.Graph.PrefixReversalZeroStarComplement
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveSupply
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeStarGrafting
open D5.S3.Combinatorics.Graph.PrefixReversal.InsertionLayerPartition
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeThreeLabelFullDomain
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveExpansion
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2ParentCycle

private def finalPrefix (m : ℕ) : List (Fin (m + 1)) :=
  List.ofFn (Fin.castSucc : Fin m → Fin (m + 1))

private theorem final_tuple (m : ℕ) :
    (finalPrefix m).take (m - 3) ++ (finalPrefix m).drop (m - 3) ++ [Fin.last m] =
      List.ofFn (id : Fin (m + 1) → Fin (m + 1)) := by
  rw [List.take_append_drop]
  simpa only [finalPrefix, Function.comp_def, id_eq, List.concat_eq_append] using
    (List.ofFn_succ' (id : Fin (m + 1) → Fin (m + 1))).symm

private def finalFrame (m : ℕ) : SupplyFrame m (m - 3) where
  selected := (finalPrefix m).take (m - 3)
  base := (finalPrefix m).drop (m - 3)
  terminal := Fin.last m
  selected_length := by
    simp only [List.length_take, finalPrefix, List.length_ofFn]
    exact Nat.min_eq_left (Nat.sub_le m 3)
  prefix_length := by
    rw [List.take_append_drop]
    exact List.length_ofFn
  full_nodup := by
    rw [final_tuple]
    exact List.nodup_ofFn.mpr Function.injective_id
  full_labels := by
    intro x
    rw [final_tuple]
    exact List.mem_ofFn.mpr ⟨x, rfl⟩

private theorem final_base_length {m : ℕ} (hm : 3 ≤ m) :
    (finalFrame m).base.length = 3 := by
  simp only [finalFrame, List.length_drop, finalPrefix, List.length_ofFn]
  omega

private noncomputable def finalParentIso {m : ℕ} (hm : 3 ≤ m) :
    domainGraph (Layer (insert (finalFrame m).terminal (finalFrame m).selected.toFinset)
      ((finalFrame m).base : Cycle (Fin (m + 1)))) ≃g
      SimpleGraph.mulCayley ({a m, b m, c m} : Set (Configuration m)) :=
  fullParentDomainIso (finalFrame m) (final_base_length hm)

/- UNCOMPILED new boundary consumer of the unconditional J2 construction.
   No all-size result is claimed until the all-k induction is earned. -/
private theorem native_six_hamiltonian_cycle :
    ∃ base : Configuration 5,
      ∃ c : (SimpleGraph.mulCayley ({a 5, b 5, c 5} : Set (Configuration 5))).Walk base base,
        c.IsHamiltonianCycle := by
  let F : SupplyFrame 5 2 := finalFrame 5
  have hB : 3 ≤ F.base.length := le_of_eq
    (show 3 = F.base.length from (final_base_length (by omega : 3 ≤ 5)).symm)
  obtain ⟨base, w, _, hw⟩ := native_j2_parent_hamiltonian_cycle (by omega : 5 ≤ 5) F hB
  let iso : domainGraph (ParentDomain F) ≃g
      SimpleGraph.mulCayley ({a 5, b 5, c 5} : Set (Configuration 5)) :=
    finalParentIso (by omega : 3 ≤ 5)
  exact ⟨iso base, w.map iso.toHom,
    SimpleGraph.Walk.IsHamiltonianCycle.map iso.toEquiv.bijective hw⟩

#print axioms native_six_hamiltonian_cycle

end D5.S3.Combinatorics.Graph.PrefixReversal.NativeAllSizes
