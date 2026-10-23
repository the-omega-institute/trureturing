/- GID: D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2FrameTransport
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/PrefixReversal/NativeJ2FrameTransport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Arbitrary two-label supply frames earn the complete native F2 domain and literal indexed port identification by actual label relabelling. -/
/- This earns the arbitrary-frame identification used by the k=2 recursive
   base case from actual independent label tuples. It assumes no target domain
   equivalence, endpoint certificate, prior-cycle inventory, or changed barred
   numbering. -/
import Batteries.Tactic.OpenPrivate
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveSupply
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeF2Coverage
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2MarkedPorts

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2FrameTransport

open Equiv Fin.NatCast

open D5.S3.Combinatorics.Graph.PrefixReversalZeroStarComplement
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeCircleComplement
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeStarGrafting
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeContactIteration
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeCircleOwnership
open D5.S3.Combinatorics.Graph.PrefixReversal.InsertionLayerPartition
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveSupply
open private anchor_tuple from
  D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveSupply
open private rotate_val from
  D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2Words
open private swap_val from
  D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2MarkedPorts

private theorem cycle_map_reverse {α β : Type*} (f : α → β) (C : Cycle α) :
    Cycle.map f C.reverse = (Cycle.map f C).reverse := by
  induction C using Quotient.inductionOn with
  | _ l =>
    change ((l.reverse.map f : List β) : Cycle β) = (l.map f).reverse
    rw [List.map_reverse]

private theorem cycle_map_left_inverse {α β : Type*} (ρ : α ≃ β) (C : Cycle α) :
    Cycle.map ρ.symm (Cycle.map ρ C) = C := by
  induction C using Quotient.inductionOn with
  | _ l =>
    simp [List.map_map, Function.comp_def]

private theorem cycle_map_injective {α β : Type*} (ρ : α ≃ β) :
    Function.Injective (Cycle.map ρ) := by
  intro C D he
  have h := congrArg (Cycle.map ρ.symm) he
  simpa only [cycle_map_left_inverse] using h

private theorem cycle_erase_map {α β : Type*} [DecidableEq α] [DecidableEq β]
    (ρ : α ≃ β) (S : Finset α) (C : Cycle α) :
    erase (S.image ρ) (Cycle.map ρ C) = Cycle.map ρ (erase S C) := by
  induction C using Quotient.inductionOn with
  | _ l =>
    change (((l.map ρ).filter (fun y => decide (y ∉ S.image ρ))) : Cycle β) =
      ((l.filter (fun x => decide (x ∉ S))).map ρ : Cycle β)
    simp [List.filter_map, Function.comp_def, ρ.injective.eq_iff]

private theorem configuration_cycle_left_mul {m : ℕ} (ρ x : Configuration m) :
    configurationCycle (ρ * x) = Cycle.map ρ (configurationCycle x) := by
  change ((List.ofFn (fun i => ρ (x i))) : Cycle (Fin (m + 1))) =
    ((List.ofFn x).map ρ : Cycle (Fin (m + 1)))
  rw [List.ofFn_comp']

private theorem layer_left_relabel {m : ℕ} (ρ : Configuration m)
    (S : Finset (Fin (m + 1))) (P : Cycle (Fin (m + 1))) (x : Configuration m) :
    Layer (S.image ρ) (Cycle.map ρ P) (ρ * x) ↔ Layer S P x := by
  simp only [Layer, configuration_cycle_left_mul, cycle_erase_map,
    ← cycle_map_reverse, (cycle_map_injective ρ).eq_iff]

/-- The label relabelling is left multiplication, so it preserves every
native generator and every actual edge; no generator is conjugated. -/
noncomputable def relabel {m : ℕ} (F : SupplyFrame m 2) : Configuration m :=
  anchor F * (NativeJ2Words.rightPort m 0)⁻¹

private theorem relabel_anchor {m : ℕ} (F : SupplyFrame m 2) :
    relabel F * NativeJ2Words.rightPort m 0 = anchor F := by
  simp only [relabel, mul_assoc, inv_mul_cancel, mul_one]

private theorem frame_selected_coordinates {m : ℕ} (hm : 5 ≤ m)
    (F : SupplyFrame m 2) :
    F.selected = [anchor F 0, anchor F ⟨1, by omega⟩] := by
  obtain ⟨p, q, hs⟩ := List.length_eq_two.mp F.selected_length
  have ht := anchor_tuple F
  have hp := congrArg (fun l : List (Fin (m + 1)) => l[0]?) ht
  have hq := congrArg (fun l : List (Fin (m + 1)) => l[1]?) ht
  have hp' : anchor F 0 = p := by
    have hp'' : anchor F ⟨0, by omega⟩ = p := by
      simpa only [List.getElem?_ofFn, dif_pos (by omega : 0 < m + 1),
        hs, List.cons_append, List.nil_append, List.getElem?_cons_zero,
        Option.some.injEq] using hp
    have hz : (⟨0, by omega⟩ : Fin (m + 1)) = 0 := by
      apply Fin.ext
      simp
    simpa only [hz] using hp''
  have hq' : anchor F ⟨1, by omega⟩ = q := by
    simpa only [List.getElem?_ofFn, dif_pos (by omega : 1 < m + 1),
      hs, List.cons_append, List.nil_append, List.getElem?_cons_succ,
      List.getElem?_cons_zero, Option.some.injEq] using hq
  rw [hs, hp', hq']

private theorem raw_zero_coordinates {m : ℕ} (hm : 5 ≤ m) :
    NativeJ2Words.rightPort m 0 0 = Fin.last m ∧
    NativeJ2Words.rightPort m 0 ⟨1, by omega⟩ = 0 := by
  constructor <;> apply Fin.ext
  · simp only [NativeJ2Words.rightPort, Fin.val_zero, rotate_val, Nat.zero_add,
      Nat.mod_eq_of_lt (by omega : m < m + 1), Fin.val_last]
  · simp only [NativeJ2Words.rightPort, Fin.val_zero, Fin.val_mk, rotate_val]
    rw [show 1 + m = m + 1 by omega, Nat.mod_self]

private theorem relabel_selected {m : ℕ} (hm : 5 ≤ m) (F : SupplyFrame m 2) :
    ({0, Fin.last m} : Finset (Fin (m + 1))).image (relabel F) =
      F.selected.toFinset := by
  have hraw (i : Fin (m + 1)) :
      relabel F (NativeJ2Words.rightPort m 0 i) = anchor F i := by
    change (relabel F * NativeJ2Words.rightPort m 0) i = _
    rw [relabel_anchor]
  have hz := hraw 0
  have ho := hraw ⟨1, by omega⟩
  rw [(raw_zero_coordinates hm).1] at hz
  rw [(raw_zero_coordinates hm).2] at ho
  rw [frame_selected_coordinates hm F]
  ext x
  simp only [Finset.mem_image, Finset.mem_insert, Finset.mem_singleton,
    List.toFinset_cons, List.toFinset_nil, Finset.notMem_empty, or_false]
  constructor
  · rintro ⟨y, rfl | rfl, rfl⟩ <;> simp [hz, ho]
  · rintro (rfl | rfl)
    · exact ⟨Fin.last m, Or.inr rfl, hz⟩
    · exact ⟨0, Or.inl rfl, ho⟩

private theorem erased_anchor {m : ℕ} (F : SupplyFrame m 2) :
    erase F.selected.toFinset (configurationCycle (anchor F)) =
      (F.terminal :: F.base : Cycle (Fin (m + 1))) := by
  have hprefix := (List.nodup_append'.mp F.full_nodup).1
  have hdis := (List.nodup_append'.mp hprefix).2.2
  have ht : F.terminal ∉ F.selected := by
    intro ht
    exact List.disjoint_left.mp (List.nodup_append'.mp F.full_nodup).2.2
      (List.mem_append.mpr (Or.inl ht)) (by simp)
  have hs : F.selected.filter (fun x => decide (x ∉ F.selected.toFinset)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro x hx
    simp [hx]
  have hb : F.base.filter (fun x => decide (x ∉ F.selected.toFinset)) = F.base := by
    apply List.filter_eq_self.mpr
    intro x hx
    exact decide_eq_true (by
      simpa only [List.mem_toFinset] using
        (fun hs => List.disjoint_left.mp hdis hs hx))
  change (((List.ofFn (anchor F)).filter
    (fun x => decide (x ∉ F.selected.toFinset))) : Cycle (Fin (m + 1))) = _
  rw [anchor_tuple, List.filter_append, List.filter_append, hs, hb]
  simp only [List.nil_append, List.filter_cons, List.mem_toFinset,
    if_pos (show decide (F.terminal ∉ F.selected) = true from decide_eq_true ht),
    List.filter_nil]
  exact Cycle.coe_eq_coe.mpr (List.isRotated_append (l := F.base) (l' := [F.terminal]))

private theorem raw_zero_cycle {m : ℕ} :
    configurationCycle (NativeJ2Words.rightPort m 0) =
      configurationCycle (1 : Configuration m) := by
  simpa only [NativeJ2Words.rightPort, Fin.val_zero, rotate_pow_eq_cycle, one_mul] using
    native_configurationCycle_rotation (1 : Configuration m) (m : Fin (m + 1))

private theorem relabel_residual {m : ℕ} (hm : 5 ≤ m) (F : SupplyFrame m 2) :
    Cycle.map (relabel F)
      (erase {0, Fin.last m} (configurationCycle (1 : Configuration m))) =
      (F.terminal :: F.base : Cycle (Fin (m + 1))) := by
  rw [← raw_zero_cycle, ← cycle_erase_map, relabel_selected hm,
    ← configuration_cycle_left_mul, relabel_anchor, erased_anchor]

/-- Every actual native vertex, not merely each supplier or a chosen walk,
belongs to the arbitrary frame's independent gap-zero domain exactly when
its inverse relabelling belongs to the fixed complete F2 layer. -/
theorem native_j2_frame_domain_iff {m : ℕ} (hm : 5 ≤ m)
    (F : SupplyFrame m 2) (x : Configuration m) :
    Layer F.selected.toFinset (F.terminal :: F.base : Cycle (Fin (m + 1)))
      (relabel F * x) ↔ F2Domain m x := by
  rw [← relabel_selected hm F, ← relabel_residual hm F,
    layer_left_relabel, ← NativeF2Coverage.native_f2_layer_iff (by omega : 4 ≤ m)]

private theorem raw_right_supply {m : ℕ} (hm : 5 ≤ m) (i : Fin 3) :
    NativeJ2Words.rightPort m i = NativeJ2Words.rightPort m 0 * (b m * c m)^i.val := by
  have hstep : NativeJ2Words.rightPort m 0 * (b m * c m) =
      Equiv.swap (⟨m - 1, by omega⟩ : Fin (m + 1)) (Fin.last m) := by
    apply Equiv.ext
    intro j
    apply Fin.ext
    change (((finRotate (m + 1))^m) ((b m * c m) j)).val =
      ((Equiv.swap (⟨m - 1, by omega⟩ : Fin (m + 1)) (Fin.last m)) j).val
    rw [rotate_val, bc_apply (by omega : 2 ≤ m)]
    simp only [swap_val, Fin.val_last, Fin.val_mk]
    by_cases hj : j.val < m
    · simp only [dif_pos hj, Fin.val_mk]
      by_cases hlast : j.val = m - 1
      · simp only [if_pos hlast]
        rw [hlast]
        simp only [show m - 1 + 1 = m by omega, Nat.mod_self, Nat.zero_add,
          Nat.mod_eq_of_lt (by omega : m < m + 1)]
      · have hi : j.val + 1 < m := by omega
        simp only [Nat.mod_eq_of_lt hi, if_neg hlast,
          if_neg (by omega : j.val ≠ m)]
        rw [show j.val + 1 + m = j.val + (m + 1) by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt j.isLt]
    · have he : j.val = m := by have h := j.isLt; omega
      rw [dif_neg hj]
      simp only [he, if_neg (by omega : m ≠ m - 1), if_true]
      rw [show m + m = m - 1 + (m + 1) by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : m - 1 < m + 1)]
  fin_cases i
  · simp
  · change Equiv.swap (⟨m - 1, by omega⟩ : Fin (m + 1)) (Fin.last m) =
      NativeJ2Words.rightPort m 0 * (b m * c m)
    exact hstep.symm
  · change Equiv.swap (⟨m - 1, by omega⟩ : Fin (m + 1)) (Fin.last m) * (b m * c m) =
      NativeJ2Words.rightPort m 0 * (b m * c m)^2
    rw [← hstep, pow_succ, pow_one, mul_assoc]

/-- The original R0,R1,R2/L0,L1,L2 indices are preserved under the same
left relabelling that earned the complete independent domain equivalence. -/
theorem native_j2_frame_ports {m : ℕ} (hm : 5 ≤ m)
    (F : SupplyFrame m 2) (i : Fin 3) :
    relabel F * NativeJ2Words.rightPort m i = rightPort F i.val ∧
    relabel F * NativeJ2Words.leftPort m i = leftPort F i.val := by
  have hr : relabel F * NativeJ2Words.rightPort m i = rightPort F i.val := by
    rw [raw_right_supply hm i, ← mul_assoc, relabel_anchor]
    rfl
  exact ⟨hr, by rw [NativeJ2Words.leftPort, ← mul_assoc, hr]; rfl⟩

/-- Only the two selected labels reverse. The base list and terminal are
literally unchanged, so the exceptional barred endpoint table keeps its
original R0,R1,R2 indexing. -/
def reverseSelected {m : ℕ} (F : SupplyFrame m 2) : SupplyFrame m 2 where
  selected := F.selected.reverse
  base := F.base
  terminal := F.terminal
  selected_length := by simpa only [List.length_reverse] using F.selected_length
  prefix_length := by
    simpa only [List.length_append, List.length_reverse] using F.prefix_length
  full_nodup := by
    have hp := ((List.reverse_perm F.selected).append_right F.base).append_right [F.terminal]
    exact hp.nodup_iff.mpr F.full_nodup
  full_labels := by
    intro x
    simpa only [List.mem_append, List.mem_reverse] using F.full_labels x

private theorem swap_prefix_tuple {α : Type*} [DecidableEq α]
    (p q : α) (tail : List α) (hn : (p :: q :: tail).Nodup) :
    (p :: q :: tail).map (Equiv.swap q p) = q :: p :: tail := by
  have hp := (List.nodup_cons.mp hn).1
  have hq := (List.nodup_cons.mp (List.nodup_cons.mp hn).2).1
  have htail : tail.map (Equiv.swap q p) = tail := by
    have hfix : ∀ x ∈ tail, Equiv.swap q p x = id x := by
      intro x hx
      exact Equiv.swap_apply_of_ne_of_ne
        (fun he => hq (he ▸ hx)) (fun he => hp (List.mem_cons_of_mem q (he ▸ hx)))
    simpa only [List.map_id] using List.map_congr_left hfix
  simp only [List.map_cons, Equiv.swap_apply_right, Equiv.swap_apply_left, htail]

private theorem barred_anchor {m : ℕ} (hm : 5 ≤ m) (F : SupplyFrame m 2) :
    relabel F * NativeJ2Words.bar (NativeJ2Words.rightPort m 0) =
      anchor (reverseSelected F) := by
  have hraw (i : Fin (m + 1)) :
      relabel F (NativeJ2Words.rightPort m 0 i) = anchor F i := by
    change (relabel F * NativeJ2Words.rightPort m 0) i = _
    rw [relabel_anchor]
  have hz := hraw 0
  have ho := hraw ⟨1, by omega⟩
  rw [(raw_zero_coordinates hm).1] at hz
  rw [(raw_zero_coordinates hm).2] at ho
  rw [NativeJ2Words.bar, ← mul_assoc, Equiv.mul_swap_eq_swap_mul,
    mul_assoc, relabel_anchor, ho, hz]
  apply Equiv.ext
  apply congrFun
  apply List.ofFn_injective
  change List.ofFn (fun i =>
    Equiv.swap (anchor F ⟨1, by omega⟩) (anchor F 0) (anchor F i)) = _
  rw [List.ofFn_comp', anchor_tuple, anchor_tuple]
  change (F.selected ++ F.base ++ [F.terminal]).map
    (Equiv.swap (anchor F ⟨1, by omega⟩) (anchor F 0)) =
      F.selected.reverse ++ F.base ++ [F.terminal]
  have hn := F.full_nodup
  rw [frame_selected_coordinates hm F] at hn ⊢
  simpa only [List.cons_append, List.nil_append, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.singleton_append] using
    swap_prefix_tuple (anchor F 0) (anchor F ⟨1, by omega⟩)
      (F.base ++ [F.terminal]) hn

/-- The barred ports are the literal ports of the reversed selected frame.
The proof preserves each index i; it never swaps 1 and 2 or flips the base. -/
theorem native_j2_frame_barred_ports {m : ℕ} (hm : 5 ≤ m)
    (F : SupplyFrame m 2) (i : Fin 3) :
    relabel F * NativeJ2Words.bar (NativeJ2Words.rightPort m i) =
      rightPort (reverseSelected F) i.val ∧
    relabel F * NativeJ2Words.bar (NativeJ2Words.leftPort m i) =
      leftPort (reverseSelected F) i.val := by
  have hr : relabel F * NativeJ2Words.bar (NativeJ2Words.rightPort m i) =
      rightPort (reverseSelected F) i.val := by
    rw [raw_right_supply hm i]
    change relabel F * (Equiv.swap 0 (Fin.last m) *
      (NativeJ2Words.rightPort m 0 * (b m * c m)^i.val)) = _
    rw [← mul_assoc (Equiv.swap 0 (Fin.last m)), ← mul_assoc (relabel F)]
    change (relabel F * NativeJ2Words.bar (NativeJ2Words.rightPort m 0)) *
      (b m * c m)^i.val = _
    rw [barred_anchor hm F]
    rfl
  exact ⟨hr, by
    simp only [NativeJ2Words.leftPort, NativeJ2Words.bar, ← mul_assoc] at hr ⊢
    rw [hr]
    rfl⟩

/-- The graph isomorphism uses the earned complete layer identification.
Its graph proof is Mathlib's left-translation invariance of a Cayley graph. -/
noncomputable def frameDomainIso {m : ℕ} (hm : 5 ≤ m) (F : SupplyFrame m 2) :
    domainGraph (F2Domain m) ≃g
      domainGraph (Layer F.selected.toFinset
        (F.terminal :: F.base : Cycle (Fin (m + 1)))) where
  toEquiv := Equiv.subtypeEquiv (Equiv.mulLeft (relabel F))
    (fun x => (native_j2_frame_domain_iff hm F x).symm)
  map_rel_iff' := by
    intro x y
    change (SimpleGraph.mulCayley ({a m, b m, c m} : Set (Configuration m))).Adj
      (relabel F * x.val) (relabel F * y.val) ↔ _
    exact SimpleGraph.mulCayley_adj_mul_iff_right

#print axioms native_j2_frame_domain_iff
#print axioms native_j2_frame_ports
#print axioms native_j2_frame_barred_ports

end D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2FrameTransport
