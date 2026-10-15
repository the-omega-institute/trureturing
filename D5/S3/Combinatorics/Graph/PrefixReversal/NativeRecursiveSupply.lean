/- GID: D5/S3/Combinatorics/Graph/PrefixReversal/NativeRecursiveSupply
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/PrefixReversal/NativeRecursiveSupply
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Explicit full label tuples encode every recursive supply port and its actual c-generator seams. -/
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeCircleOwnership
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeSwitches
import Mathlib.Data.List.NodupEquivFin

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveSupply

open D5.S3.Combinatorics.Graph.PrefixReversalZeroStarComplement
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeCircleOwnership
open Equiv

/-- The supplied lists, not a recursive path state, specify the actual tuple.
All labels occur once. The selected list may be either required p/q order;
no reversal of the base list is implicit in this representation. -/
structure SupplyFrame (m k : Nat) where
  selected : List (Fin (m + 1))
  base : List (Fin (m + 1))
  terminal : Fin (m + 1)
  selected_length : selected.length = k
  prefix_length : (selected ++ base).length = m
  full_nodup : (selected ++ base ++ [terminal]).Nodup
  full_labels : ∀ x : Fin (m + 1), x ∈ selected ++ base ++ [terminal]

private theorem SupplyFrame.full_length {m k : Nat} (F : SupplyFrame m k) :
    (F.selected ++ F.base ++ [F.terminal]).length = m + 1 := by
  have h := F.prefix_length
  simp only [List.length_append, List.length_singleton] at h ⊢
  omega

/-- The actual permutation whose literal list is (S,B,u). -/
noncomputable def anchor {m k : Nat} (F : SupplyFrame m k) : Configuration m :=
  (finCongr F.full_length.symm).trans
    (List.Nodup.getEquivOfForallMemList
      (F.selected ++ F.base ++ [F.terminal]) F.full_nodup F.full_labels)

private theorem anchor_tuple {m k : Nat} (F : SupplyFrame m k) :
    List.ofFn (anchor F) = F.selected ++ F.base ++ [F.terminal] := by
  apply List.ext_getElem
  · simp only [List.length_ofFn, F.full_length]
  · intro i hi hj
    simp only [List.getElem_ofFn]
    rfl

private theorem tuple_decompose {m : Nat} (z : Configuration m) :
    List.ofFn z = residualList z ++ [z (Fin.last m)] := by
  simpa only [residualList, List.concat_eq_append] using List.ofFn_succ' z

private theorem anchor_coordinates {m k : Nat} (F : SupplyFrame m k) :
    residualList (anchor F) = F.selected ++ F.base ∧
      anchor F (Fin.last m) = F.terminal := by
  have h := anchor_tuple F
  rw [tuple_decompose] at h
  have hl : (residualList (anchor F)).length = (F.selected ++ F.base).length := by
    simp only [residualList, List.length_ofFn, F.prefix_length]
  obtain ⟨hp, ht⟩ := List.append_inj h hl
  exact ⟨hp, by simpa using ht⟩

private theorem bc_prefix_tuple {m : Nat} (hm : 2 ≤ m)
    (z : Configuration m) (i : Nat) :
    residualList (z * (b m * c m) ^ i) = (residualList z).rotate i := by
  apply List.ext_getElem
  · simp only [residualList, List.length_ofFn, List.length_rotate]
  · intro j hj hj'
    simp only [residualList, List.getElem_ofFn, List.getElem_rotate,
      List.length_ofFn, Equiv.Perm.mul_apply]
    apply congrArg z
    apply Fin.ext
    simp only [native_bc_pow_val hm, Fin.val_castSucc,
      if_pos (show j < m by simpa only [residualList, List.length_ofFn] using hj)]

private theorem bc_terminal {m : Nat} (hm : 2 ≤ m)
    (z : Configuration m) (i : Nat) :
    (z * (b m * c m) ^ i) (Fin.last m) = z (Fin.last m) := by
  apply congrArg z
  apply Fin.ext
  simp only [native_bc_pow_val hm, Fin.val_last, lt_self_iff_false, if_false]

private theorem b_prefix_tuple {m : Nat} (z : Configuration m) :
    residualList (z * b m) = (residualList z).reverse := by
  apply List.ext_getElem
  · simp only [residualList, List.length_ofFn, List.length_reverse]
  · intro i hi hj
    simp only [residualList, List.getElem_ofFn, List.getElem_reverse,
      List.length_ofFn, Equiv.Perm.mul_apply]
    apply congrArg z
    apply Fin.ext
    rw [b_apply]
    simp only [Fin.val_castSucc,
      if_pos (show i < m by simpa only [residualList, List.length_ofFn] using hi)]

/-- The right port (rotate(S ++ B,i),u), at every actual supply position. -/
noncomputable def rightPort {m k : Nat} (F : SupplyFrame m k) (i : Nat) :
    Configuration m := anchor F * (b m * c m) ^ i

/-- The left port reverses the prefix and keeps the terminal label u. -/
noncomputable def leftPort {m k : Nat} (F : SupplyFrame m k) (i : Nat) :
    Configuration m := rightPort F i * b m

/-- The k+1 distinguished port pairs used by the independently proved E/O
boundary template. Side 0 is R and side 1 is L. -/
noncomputable def specialPort {m k : Nat} (F : SupplyFrame m k)
    (p : Fin (k + 1) × Fin 2) : Configuration m :=
  if p.2.val = 0 then rightPort F p.1.val else leftPort F p.1.val

private theorem c_ne_one {m : Nat} (hm : 3 ≤ m) : c m ≠ 1 := by
  intro h
  have he : (c m (0 : Fin (m + 1))).val = m - 2 := by
    rw [c_apply]
    change (if 0 < m - 1 then m - 2 else 0) = m - 2
    exact if_pos (by omega : 0 < m - 1)
  have hz : (c m (0 : Fin (m + 1))).val = 0 := by rw [h]; rfl
  omega

private theorem c_adj {m : Nat} (hm : 3 ≤ m) (x y : Configuration m)
    (hxy : x * c m = y) :
    (SimpleGraph.mulCayley ({a m, b m, c m} : Set (Configuration m))).Adj x y := by
  rw [SimpleGraph.mulCayley_adj']
  refine ⟨?_, c m, by simp, Or.inl hxy⟩
  intro he
  apply c_ne_one hm
  exact mul_left_cancel (hxy.trans (he.symm.trans (mul_one x).symm))

private theorem supply_step {m k : Nat} (F : SupplyFrame m k) (i : Nat) :
    leftPort F i * c m = rightPort F (i + 1) := by
  simp only [leftPort, rightPort, pow_succ, mul_assoc]

private theorem supply_closes {m k : Nat} (hm : 3 ≤ m) (F : SupplyFrame m k) :
    leftPort F (m - 1) * c m = rightPort F 0 := by
  rw [supply_step, show m - 1 + 1 = m by omega]
  have horder : (b m * c m) ^ m = 1 := by
    apply Equiv.ext
    intro i
    apply Fin.ext
    rw [native_bc_pow_val (by omega : 2 ≤ m)]
    by_cases hi : i.val < m
    · simp only [if_pos hi, Nat.add_mod_right, Nat.mod_eq_of_lt hi,
        Equiv.Perm.one_apply]
    · simp only [if_neg hi, Equiv.Perm.one_apply]
  simp only [rightPort, horder, pow_zero, mul_one]

/-- Every supplied recursive port is an explicit native permutation tuple.
The internal connectors are actual c-generator edges, including the final
return of the full supplier. There is no premise about a formal port graph.
For a special boundary with i<k, use the unwrapped step at i; a base of length
at least three ensures these positions lie strictly inside the full supplier. -/
theorem native_anchored_supply_coordinates {m k : Nat} (hm : 3 ≤ m)
    (F : SupplyFrame m k) :
    (∀ i : Nat,
      List.ofFn (rightPort F i) =
        (F.selected ++ F.base).rotate i ++ [F.terminal] ∧
      List.ofFn (leftPort F i) =
        ((F.selected ++ F.base).rotate i).reverse ++ [F.terminal] ∧
      leftPort F i * c m = rightPort F (i + 1) ∧
      (SimpleGraph.mulCayley ({a m, b m, c m} : Set (Configuration m))).Adj
        (leftPort F i) (rightPort F (i + 1))) ∧
    leftPort F (m - 1) * c m = rightPort F 0 ∧
    (SimpleGraph.mulCayley ({a m, b m, c m} : Set (Configuration m))).Adj
      (leftPort F (m - 1)) (rightPort F 0) := by
  obtain ⟨hprefix, hlast⟩ := anchor_coordinates F
  refine ⟨?_, supply_closes hm F, c_adj hm _ _ (supply_closes hm F)⟩
  intro i
  have hr : residualList (rightPort F i) = (F.selected ++ F.base).rotate i := by
    rw [rightPort, bc_prefix_tuple (by omega : 2 ≤ m), hprefix]
  have ht : rightPort F i (Fin.last m) = F.terminal := by
    rw [rightPort, bc_terminal (by omega : 2 ≤ m), hlast]
  refine ⟨?_, ?_, supply_step F i, c_adj hm _ _ (supply_step F i)⟩
  · rw [tuple_decompose, hr, ht]
  · rw [tuple_decompose]
    simp only [leftPort, b_prefix_tuple, hr, Equiv.Perm.mul_apply, b_last, ht]

/-- The k+1 special port pairs are actual distinct configurations when k<m.
This condition is essential: at k=m, R_m=R_0. The proof embeds the ports into
the existing independently earned native supplier coordinate equivalence. -/
theorem native_special_port_injective {m k : Nat} (hm : 3 ≤ m)
    (F : SupplyFrame m k) (hkm : k < m) : Function.Injective (specialPort F) := by
  let index (p : Fin (k + 1) × Fin 2) : Fin m × Fin (m + 1) × Bool :=
    (⟨p.1.val, by have hp := p.1.isLt; omega⟩,
      if p.2.val = 0 then 0 else -1,
      if p.2.val = 0 then false else true)
  have hcoord (p : Fin (k + 1) × Fin 2) :
      coordinate (anchor F) (index p) = specialPort F p := by
    rcases p with ⟨i, s⟩
    fin_cases s <;>
      simp [index, specialPort, coordinate, rightPort, leftPort, gapAnchor,
        b_eq_cycle_a, cycle_zero, mul_assoc]
  intro p q he
  have hsub : coordinateEquiv hm (anchor F) (index p) =
      coordinateEquiv hm (anchor F) (index q) := by
    apply Subtype.ext
    change coordinate (anchor F) (index p) = coordinate (anchor F) (index q)
    rw [hcoord, hcoord]
    exact he
  have hi := (coordinateEquiv hm (anchor F)).injective hsub
  apply Prod.ext
  · apply Fin.ext
    exact congrArg (fun r : Fin m × Fin (m + 1) × Bool => r.1.val) hi
  · have hside : Function.Injective (fun s : Fin 2 =>
        if s.val = 0 then false else true) := by
      intro s t hst
      fin_cases s <;> fin_cases t <;> simp_all
    exact hside (congrArg (fun r : Fin m × Fin (m + 1) × Bool => r.2.2) hi)

#print axioms native_anchored_supply_coordinates
#print axioms native_special_port_injective

end D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveSupply
