/- GID: D5/S3/Combinatorics/Graph/PrefixReversal/NativeOppositeMarkedPorts
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/PrefixReversal/NativeOppositeMarkedPorts
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The canonical protected-label exchange separates both complete native marked-port tables and their actual deletion sets. -/
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeOppositeSelectedOrders
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeJointMarkedCutShift
import Mathlib.Data.Nat.ModEq

set_option autoImplicit false
namespace D5.S3.Combinatorics.Graph.PrefixReversal.NativeOppositeMarkedPorts
open D5.S3.Combinatorics.Graph.PrefixReversalZeroStarComplement
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveSupply
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeProtectedLabels
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeOppositeSelectedOrders
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeCircleOwnership

private theorem anchor_list {m k : ℕ} (hm : 3 ≤ m) (F : SupplyFrame m k) :
    List.ofFn (anchor F) = F.selected ++ F.base ++ [F.terminal] := by
  simpa [rightPort] using ((native_anchored_supply_coordinates hm F).1 0).1

private theorem opposite_anchor {m k : ℕ} (hm : 3 ≤ m) (F : SupplyFrame m k)
    (hk : 2 ≤ k) :
    anchor (oppositeSelectedFrame F hk) =
      Equiv.swap (protectedP F hk) (protectedQ F hk) * anchor F := by
  apply Equiv.coe_fn_injective
  apply List.ofFn_injective
  rw [anchor_list hm, show List.ofFn (fun x =>
      (Equiv.swap (protectedP F hk) (protectedQ F hk) * anchor F) x) =
      (List.ofFn (anchor F)).map (Equiv.swap (protectedP F hk) (protectedQ F hk)) by
        simp only [Equiv.Perm.mul_apply, List.map_ofFn, Function.comp_def], anchor_list hm]
  obtain ⟨_, _, _, hpB, hqB, hpT, hqT⟩ := native_protected_labels F hk
  have hb : F.base.map (Equiv.swap (protectedP F hk) (protectedQ F hk)) = F.base := by
    calc
      F.base.map (Equiv.swap (protectedP F hk) (protectedQ F hk)) = F.base.map id := by
        apply List.map_congr_left
        intro x hx
        exact Equiv.swap_apply_of_ne_of_ne
          (fun he => hpB (he ▸ hx)) (fun he => hqB (he ▸ hx))
      _ = F.base := List.map_id _
  simp only [oppositeSelectedFrame, List.map_append, hb, List.map_singleton,
    Equiv.swap_apply_of_ne_of_ne (Ne.symm hpT) (Ne.symm hqT)]

private theorem anchor_base {m k : ℕ} (hm : 3 ≤ m) (F : SupplyFrame m k)
    (i : ℕ) (hi : i < F.base.length) :
    anchor F ⟨k + i, by
      have hp := F.prefix_length
      simp only [List.length_append, F.selected_length] at hp
      omega⟩ = F.base[i] := by
  have hp := F.prefix_length
  simp only [List.length_append, F.selected_length] at hp
  have ht : k+i < (F.selected ++ F.base ++ [F.terminal]).length := by
    simp only [List.length_append, List.length_singleton, F.selected_length]
    omega
  have h := congrArg (fun L : List (Fin (m+1)) => L[k+i]?) (anchor_list hm F)
  rw [List.getElem?_eq_getElem (by simp only [List.length_ofFn]; omega),
    List.getElem?_eq_getElem ht] at h
  simp only [List.getElem_ofFn] at h
  rw [List.getElem_append_left (by simp only [List.length_append, F.selected_length]; omega),
    List.getElem_append_right (by rw [F.selected_length]; omega)] at h
  simpa only [F.selected_length, Nat.add_sub_cancel_left, Option.some.injEq] using h

private theorem rotation_separation {m : ℕ} (hm : 3 ≤ m)
    (A τ : Configuration m) (hτ : τ ≠ 1)
    (l : Fin (m+1)) (hl : l.val < m) (hfix : τ (A l) = A l)
    (i j : ℕ) : τ * A * (b m * c m)^j ≠ A * (b m * c m)^i := by
  intro he
  let q : Fin (m+1) := ((b m * c m)^j)⁻¹ l
  have hq : ((b m * c m)^j) q = l := by simp [q]
  have hqi : ((b m * c m)^i) q = l := by
    apply A.injective
    have hv := congrArg (fun z : Configuration m => z q) he
    simpa only [Equiv.Perm.mul_apply, hq, hfix] using hv.symm
  have hqm : q.val < m := by
    have hv := congrArg Fin.val hq
    rw [native_bc_pow_val (by omega : 2 ≤ m)] at hv
    split_ifs at hv with h
    · exact h
    · omega
  have hj : (q.val+j)%m = l.val := by
    simpa only [native_bc_pow_val (by omega : 2 ≤ m), if_pos hqm] using congrArg Fin.val hq
  have hi : (q.val+i)%m = l.val := by
    simpa only [native_bc_pow_val (by omega : 2 ≤ m), if_pos hqm] using congrArg Fin.val hqi
  have hij : i ≡ j [MOD m] := Nat.ModEq.add_left_cancel' q.val (hi.trans hj.symm)
  have hr : (b m*c m)^i = (b m*c m)^j := by
    apply Equiv.ext
    intro x
    apply Fin.ext
    simp only [native_bc_pow_val (by omega : 2 ≤ m)]
    split_ifs
    · exact Nat.ModEq.add_left x.val hij
    · rfl
  rw [hr] at he
  have ha : τ * A = A := mul_right_cancel he
  apply hτ
  exact mul_right_cancel (ha.trans (one_mul A).symm)

private theorem reflection_separation {m : ℕ} (hm : 5 ≤ m)
    (A τ : Configuration m) (k : ℕ) (hkm : k+2 < m)
    (hfix : ∀ l : Fin (m+1), l.val = k ∨ l.val = k+1 → τ (A l) = A l)
    (i j : ℕ) : τ * A * (b m*c m)^j ≠ A * (b m*c m)^i * b m := by
  intro he
  have equations (l : Fin (m+1)) (hl : l.val = k ∨ l.val = k+1) :
      m-1+(i+j) ≡ l.val+l.val [MOD m] := by
    have hlm : l.val < m := by rcases hl with hl | hl <;> omega
    let q : Fin (m+1) := ((b m*c m)^j)⁻¹ l
    have hq : ((b m*c m)^j) q = l := by simp [q]
    have hqi : ((b m*c m)^i) (b m q) = l := by
      apply A.injective
      have hv := congrArg (fun z : Configuration m => z q) he
      simpa only [Equiv.Perm.mul_apply, hq, hfix l hl] using hv.symm
    have hqm : q.val < m := by
      have hv := congrArg Fin.val hq
      rw [native_bc_pow_val (by omega : 2 ≤ m)] at hv
      split_ifs at hv with h
      · exact h
      · omega
    have hbm : (b m q).val = m-1-q.val := by simp only [b_apply, if_pos hqm]
    have hbmlt : (b m q).val < m := by rw [hbm]; omega
    have hj : q.val+j ≡ l.val [MOD m] := by
      change (q.val+j)%m = l.val%m
      rw [Nat.mod_eq_of_lt hlm]
      simpa only [native_bc_pow_val (by omega : 2 ≤ m), if_pos hqm] using congrArg Fin.val hq
    have hi : m-1-q.val+i ≡ l.val [MOD m] := by
      change (m-1-q.val+i)%m = l.val%m
      rw [Nat.mod_eq_of_lt hlm]
      have hv := congrArg Fin.val hqi
      rw [native_bc_pow_val (by omega : 2 ≤ m), if_pos hbmlt, hbm] at hv
      exact hv
    have hadd := hj.add hi
    have hsum : q.val+j+(m-1-q.val+i) = m-1+(i+j) := by omega
    rw [hsum] at hadd
    exact hadd
  have h0 : m-1+(i+j) ≡ k+k [MOD m] := equations ⟨k, by omega⟩ (Or.inl rfl)
  have h1 : m-1+(i+j) ≡ (k+1)+(k+1) [MOD m] :=
    equations ⟨k+1, by omega⟩ (Or.inr rfl)
  have hh : k+k+0 ≡ k+k+2 [MOD m] := by
    convert h0.symm.trans h1 using 1 <;> omega
  have hz : 0 ≡ 2 [MOD m] := Nat.ModEq.add_left_cancel' (k+k) hh
  have : (0 : ℕ) = 2 := by
    simpa only [Nat.ModEq, Nat.zero_mod, Nat.mod_eq_of_lt (by omega : 2 < m)] using hz
  omega

/-- All rotation and reversal ports from the canonical protected-label
exchange are disjoint from the ports in the original order. This uses two
adjacent unselected base positions, not an assumed port inequality. -/
theorem native_opposite_ports_disjoint {m k : ℕ} (F : SupplyFrame m k)
    (hk : 2 ≤ k) (hB : 3 ≤ F.base.length) (i j : ℕ) :
    rightPort (oppositeSelectedFrame F hk) j ≠ rightPort F i ∧
    rightPort (oppositeSelectedFrame F hk) j ≠ leftPort F i ∧
    leftPort (oppositeSelectedFrame F hk) j ≠ rightPort F i ∧
    leftPort (oppositeSelectedFrame F hk) j ≠ leftPort F i := by
  have hp := F.prefix_length
  simp only [List.length_append, F.selected_length] at hp
  have hm : 5 ≤ m := by omega
  let τ : Configuration m := Equiv.swap (protectedP F hk) (protectedQ F hk)
  have hτ : τ ≠ 1 := by
    intro he
    have hv := congrArg (fun z : Configuration m => z (protectedP F hk)) he
    have hn := (native_protected_labels F hk).1
    exact hn (by simpa only [τ, Equiv.swap_apply_left, Equiv.Perm.one_apply] using hv.symm)
  have hfix (l : Fin (m+1)) (hl : l.val = k ∨ l.val = k+1) : τ (anchor F l) = anchor F l := by
    obtain ⟨_, _, _, hpB, hqB, _, _⟩ := native_protected_labels F hk
    have hb : anchor F l ∈ F.base := by
      rcases hl with hl | hl
      · have he : l = ⟨k+0, by omega⟩ := Fin.ext (by simpa using hl)
        rw [he, anchor_base (by omega) F 0 (by omega)]
        exact List.getElem_mem _
      · have he : l = ⟨k+1, by omega⟩ := Fin.ext hl
        rw [he, anchor_base (by omega) F 1 (by omega)]
        exact List.getElem_mem _
    exact Equiv.swap_apply_of_ne_of_ne (fun he => hpB (he ▸ hb)) (fun he => hqB (he ▸ hb))
  have rr (i j : ℕ) : rightPort (oppositeSelectedFrame F hk) j ≠ rightPort F i := by
    rw [rightPort, rightPort, opposite_anchor (by omega)]
    exact rotation_separation (by omega) (anchor F) τ hτ ⟨k, by omega⟩
      (by change k < m; omega) (hfix _ (Or.inl rfl)) i j
  have rl (i j : ℕ) : rightPort (oppositeSelectedFrame F hk) j ≠ leftPort F i := by
    rw [rightPort, leftPort, rightPort, opposite_anchor (by omega)]
    exact reflection_separation hm (anchor F) τ k (by omega) hfix i j
  refine ⟨rr i j, rl i j, ?_, ?_⟩
  · intro he
    have hv := congrArg (fun z : Configuration m => τ * z) he
    have hi : τ * anchor (oppositeSelectedFrame F hk) = anchor F := by
      rw [opposite_anchor (by omega)]
      simp only [τ, ← mul_assoc, Equiv.swap_mul_self, one_mul]
    have hj : τ * anchor F = anchor (oppositeSelectedFrame F hk) :=
      (opposite_anchor (by omega) F hk).symm
    apply rl j i
    simpa only [leftPort, rightPort, ← mul_assoc, hi, hj] using hv.symm
  · intro he
    apply rr i j
    exact mul_right_cancel he


private theorem opposite_special_ne {m k : ℕ} (F : SupplyFrame m k)
    (hk : 2 ≤ k) (hB : 3 ≤ F.base.length)
    (p q : Fin (k+1) × Fin 2) :
    specialPort (oppositeSelectedFrame F hk) p ≠ specialPort F q := by
  have h := native_opposite_ports_disjoint F hk hB q.1.val p.1.val
  unfold specialPort
  split_ifs with hp hq
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1
  · exact h.2.2.2

/-- Both literal marked-port tables jointly have unique native vertices.
The Boolean tag records the actual protected-label exchange. -/
theorem native_opposite_marked_port_injective {m k : ℕ} (F : SupplyFrame m k)
    (hk : 2 ≤ k) (hB : 3 ≤ F.base.length) :
    Function.Injective (fun p : Bool × (Fin (k+1) × Fin 2) =>
      specialPort (if p.1 then oppositeSelectedFrame F hk else F) p.2) := by
  have hp := F.prefix_length
  simp only [List.length_append, F.selected_length] at hp
  have hm : 3 ≤ m := by omega
  have hkm : k < m := by omega
  rintro ⟨a,p⟩ ⟨b,q⟩ he
  cases a <;> cases b
  · exact Prod.ext rfl (native_special_port_injective hm F hkm he)
  · exact False.elim (opposite_special_ne F hk hB q p he.symm)
  · exact False.elim (opposite_special_ne F hk hB p q he)
  · exact Prod.ext rfl (native_special_port_injective hm (oppositeSelectedFrame F hk) hkm he)

/-- The two actual marked deletion sets have no common undirected edge. -/
theorem native_opposite_marked_cuts_disjoint {m k : ℕ} (F : SupplyFrame m k)
    (hk : 2 ≤ k) (hB : 3 ≤ F.base.length) :
    Disjoint (NativeJointMarkedCutShift.markedCuts F)
      (NativeJointMarkedCutShift.markedCuts (oppositeSelectedFrame F hk)) := by
  classical
  rw [Finset.disjoint_left]
  intro e he hbar
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp he
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hbar
  have heq := hj.trans hi.symm
  change s(rightPort (oppositeSelectedFrame F hk) j.val,
      leftPort (oppositeSelectedFrame F hk) j.val) =
    s(rightPort F i.val, leftPort F i.val) at heq
  have h := native_opposite_ports_disjoint F hk hB i.val j.val
  rcases Sym2.eq_iff.mp heq with hsame | hswap
  · exact h.1 hsame.1
  · exact h.2.1 hswap.1

#print axioms native_opposite_marked_port_injective
#print axioms native_opposite_marked_cuts_disjoint

#print axioms native_opposite_ports_disjoint
end D5.S3.Combinatorics.Graph.PrefixReversal.NativeOppositeMarkedPorts
