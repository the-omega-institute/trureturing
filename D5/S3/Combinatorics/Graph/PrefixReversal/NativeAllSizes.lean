/- GID: D5/S3/Combinatorics/Graph/PrefixReversal/NativeAllSizes
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/PrefixReversal/NativeAllSizes
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native Hamilton cycles exist at every label count at least four. -/
import Batteries.Tactic.OpenPrivate
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeThreeLabelFullDomain
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeFourBase
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeFiveBase
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2ParentCycle
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeActualStateExistence

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.PrefixReversal.NativeAllSizes

open D5.S3.Combinatorics.Graph.PrefixReversalZeroStarComplement
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveSupply
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeStarGrafting
open D5.S3.Combinatorics.Graph.PrefixReversal.InsertionLayerPartition
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeThreeLabelFullDomain
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveExpansion
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2ParentCycle
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeActualInductionState
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeActualStateExistence
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeMarkedFrameDomains
open NativeActualStateSuppliers
open private special_path_from_state ordinary_from_state from
  D5.S3.Combinatorics.Graph.PrefixReversal.NativeActualStateSuppliers

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

/- The six-label boundary consumer uses the unconditional J2 construction. -/
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

/-- Final parent assembly only needs a genuine three-label base. It uses
the special state and each rotated ordinary state at this same order;
it does not invoke the step that removes a label from the base. -/
private theorem parent_from_state_family {m k : ℕ} (hm : 3 ≤ m) (hk : 2 ≤ k)
    (supplies : ∀ (G : SupplyFrame m k) (hG : 3 ≤ G.base.length),
      ∃ S : StateFor G hk hG, S.primaryOdd = decide (k % 2 = 1))
    (F : SupplyFrame m k) (hB : 3 ≤ F.base.length) :
    ∃ base : {x : Configuration m // ParentDomain F x},
      ∃ w : (domainGraph (ParentDomain F)).Walk base base,
        base.val = rightPort F 0 ∧ w.IsHamiltonianCycle := by
  classical
  obtain ⟨S, hodd⟩ := supplies F hB
  obtain ⟨special⟩ := special_path_from_state hm F hk hB S hodd
  have hchildren (j : Fin F.base.length) (hj : 0 < j.val) :
      Nonempty (SpecifiedOrdinaryCycle hm F hB j hj) := by
    have hG : 3 ≤ (nativeChildFrame F j).base.length := by
      simpa only [nativeChildFrame, List.length_rotate] using hB
    obtain ⟨T, _⟩ := supplies (nativeChildFrame F j) hG
    obtain ⟨ordinary⟩ := ordinary_from_state hm F hk hB j hj T
    exact ⟨ordinary.cycle⟩
  let children (j : Fin F.base.length) (hj : 0 < j.val) :
      SpecifiedOrdinaryCycle hm F hB j hj := Classical.choice (hchildren j hj)
  obtain ⟨_, _, _, _, base, w, _, hb, hw, _, _⟩ :=
    recursive_cycle_from_specified_children_with_inventory hm F hB
      special.path special.hamiltonian children
  exact ⟨base, w, hb, hw⟩

/-- The canonical final frame has base length exactly three, so its
parent domain is the full permutation graph, at every larger order. -/
private theorem native_larger_hamiltonian_cycle {m : ℕ} (hm : 6 ≤ m) :
    ∃ base : Configuration m,
      ∃ w : (SimpleGraph.mulCayley ({a m, b m, c m} : Set (Configuration m))).Walk
        base base, w.IsHamiltonianCycle := by
  have hm3 : 3 ≤ m := by omega
  have hk3 : 3 ≤ m - 3 := by omega
  have hk2 : 2 ≤ m - 3 := by omega
  let F := finalFrame m
  have hB : 3 ≤ F.base.length := le_of_eq
    (show 3 = F.base.length from (final_base_length hm3).symm)
  have supplies (G : SupplyFrame m (m - 3)) (hG : 3 ≤ G.base.length) :
      ∃ S : StateFor G hk2 hG, S.primaryOdd = decide ((m - 3) % 2 = 1) := by
    obtain ⟨S, hodd, _, _⟩ := native_actual_state_exists hk3 G hG
    exact ⟨S, hodd⟩
  obtain ⟨base, w, _, hw⟩ := parent_from_state_family hm3 hk2
    supplies F hB
  let iso : domainGraph (ParentDomain F) ≃g
      SimpleGraph.mulCayley ({a m, b m, c m} : Set (Configuration m)) :=
    finalParentIso hm3
  exact ⟨iso base, w.map iso.toHom,
    SimpleGraph.Walk.IsHamiltonianCycle.map iso.toEquiv.bijective hw⟩

/-- Every native prefix-reversal graph on at least four labels has a
Hamilton cycle using the three literal generators a, b and c. -/
theorem native_all_sizes_hamiltonian_cycle {m : ℕ} (hm : 3 ≤ m) :
    ∃ base : Configuration m,
      ∃ w : (SimpleGraph.mulCayley ({a m, b m, c m} : Set (Configuration m))).Walk
        base base, w.IsHamiltonianCycle := by
  rcases (by omega : m = 3 ∨ m = 4 ∨ m = 5 ∨ 6 ≤ m) with rfl | rfl | rfl | hlarge
  · exact NativeFourBase.native_four_hamiltonian_cycle
  · exact NativeFiveBase.native_five_hamiltonian_cycle
  · exact native_six_hamiltonian_cycle
  · exact native_larger_hamiltonian_cycle hlarge

#print axioms native_all_sizes_hamiltonian_cycle

end D5.S3.Combinatorics.Graph.PrefixReversal.NativeAllSizes
