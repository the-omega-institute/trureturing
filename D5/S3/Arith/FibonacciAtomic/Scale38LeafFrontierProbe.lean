import D5.S3.Arith.FibonacciAtomic.Scale38LeafFrontierResponse

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Scale38LeafFrontierResponse
open GenealogicalFiberTransport (Source)
open ActualTreeReadoutAcquisition (Address Reply readout)
open ActualImageSevenLeafSeparation (A C E leafLabel)
open FourExitRawEndpointSpectrum (comb comb_slot_readout comb_tail_readout)
open Scale38NestedCompensation (family)
local notation "Index" => fun k : Nat => Unit ⊕ (Fin k ⊕ Fin k)
local notation "B" => FourExitRawEndpointSpectrum.B
local notation "H" => fun r : Nat => comb r (fun _ => A) C
local notation "G" => fun k : Nat => fun j : Fin k => comb k (fun l => ite (l = j) B A) C
local notation "label" => fun b : Bool => Bool.rec Reply.beta Reply.alpha b

/-- Complete disjoint frontiers and the response at every leaf against every competitor. -/
theorem result (k : Nat) (hk : 1 ≤ k) :
    labelledFrontier A = {([false,false],false),([false,true],true),([true],false)} ∧
    labelledFrontier E = {([false],false),([true],true)} ∧
    (∀ r : Nat,
      labelledFrontier (H r) = ⋃ t : Fin (r+2), combBlock (r+1) (fun _ => A) E t ∧
      Pairwise (fun t u => Disjoint (combBlock (r+1) (fun _ => A) E t)
        (combBlock (r+1) (fun _ => A) E u))) ∧
    (labelledFrontier B = prefixed [false,false] (labelledFrontier A) ∪
      prefixed [false,true] (labelledFrontier E) ∪ prefixed [true] (labelledFrontier A) ∧
      Pairwise (fun t u : Fin 3 => Disjoint
        (![prefixed [false,false] (labelledFrontier A),prefixed [false,true] (labelledFrontier E),
          prefixed [true] (labelledFrontier A)] t)
        (![prefixed [false,false] (labelledFrontier A),prefixed [false,true] (labelledFrontier E),
          prefixed [true] (labelledFrontier A)] u))) ∧
    (∀ j : Fin k,
      labelledFrontier (G k j) = ⋃ t : Fin (k+1), combBlock k (fun l => ite (l=j) B A) C t ∧
      Pairwise (fun t u => Disjoint (combBlock k (fun l => ite (l=j) B A) C t)
        (combBlock k (fun l => ite (l=j) B A) C u))) ∧
    (labelledFrontier (family k (.inl ())) =
      prefixed [false] (labelledFrontier (H k)) ∪ prefixed [true] (labelledFrontier B) ∧
      Disjoint (prefixed [false] (labelledFrontier (H k)))
        (prefixed [true] (labelledFrontier B))) ∧
    (∀ j : Fin k,
      labelledFrontier (family k (.inr (.inl j))) =
        prefixed [false] (labelledFrontier (G k j)) ∪ prefixed [true] (labelledFrontier A) ∧
      Disjoint (prefixed [false] (labelledFrontier (G k j)))
        (prefixed [true] (labelledFrontier A))) ∧
    (∀ i : Fin k,
      labelledFrontier (family k (.inr (.inr i))) = prefixed [false] (labelledFrontier (H i.val)) ∪
        prefixed [true,false] (labelledFrontier (H (k-i.val))) ∪
        prefixed [true,true] (labelledFrontier A) ∧
      Pairwise (fun t u : Fin 3 => Disjoint
        (![prefixed [false] (labelledFrontier (H i.val)),
          prefixed [true,false] (labelledFrontier (H (k-i.val))),prefixed [true,true] (labelledFrontier A)] t)
        (![prefixed [false] (labelledFrontier (H i.val)),
          prefixed [true,false] (labelledFrontier (H (k-i.val))),prefixed [true,true] (labelledFrontier A)] u))) ∧
    (∀ (n t : Nat) (a : Address) (b : Bool), (a,b) ∈ labelledFrontier A →
      readout (List.replicate t true ++ false :: a) (H n) =
        if n < t then .absent else label b) ∧
    (∀ (r n : Nat) (a : Address) (b : Bool), (a,b) ∈ labelledFrontier E →
      readout (List.replicate (r+1) true ++ a) (H n) =
        if r < n then .branch else if n < r then .absent else label b) ∧
    (∀ (a : Address) (b : Bool), (a,b) ∈ labelledFrontier A → readout a B = .branch) ∧
    (∀ (a : Address) (b : Bool), (a,b) ∈ labelledFrontier B → readout a A = .absent) ∧
    (∀ (Z : Index k) (a : Address) (b : Bool), (a,b) ∈ labelledFrontier (family k Z) →
      ∃ r : LeafRow k, r.target = Z ∧ (a,b) ∈ r.block) ∧
    (∀ (r : LeafRow k) (U : Index k), U ≠ r.target →
      ∀ (a : Address) (b : Bool), (a,b) ∈ r.block →
      readout a (family k U) = r.reply U b) := by
  classical
  have mem_front (T : Source) (u : Address) (b : Bool) :
      (u,b) ∈ labelledFrontier T ↔ readout u T = label b := by
    cases h : readout u T <;> cases b <;> simp [labelledFrontier, leafLabel, h]
  have pre_mem (w u : Address) (b : Bool) (F : Set (Address × Bool)) :
      (u,b) ∈ prefixed w F ↔ ∃ v, (v,b) ∈ F ∧ u = w++v := by
    constructor
    · rintro ⟨⟨v,c⟩,hv,he⟩
      have hp : w++v = u ∧ c = b := Prod.mk.inj he
      rcases hp with ⟨haddr,hlabel⟩
      subst c
      exact ⟨v,hv,haddr.symm⟩
    · rintro ⟨v,hv,rfl⟩
      exact ⟨(v,b),hv,rfl⟩
  have pair_front (S T : Source) : labelledFrontier (.mul S T) =
      prefixed [false] (labelledFrontier S) ∪ prefixed [true] (labelledFrontier T) := by
    ext ⟨u,b⟩
    cases u with
    | nil => cases b <;> simp [mem_front, readout, prefixed]
    | cons d u => cases d <;> simp [mem_front, readout, prefixed, Prod.exists]
  have leaf_front (b : Bool) : labelledFrontier (.of b) = {([],b)} := by
    ext ⟨u,c⟩
    cases u <;> cases b <;> cases c <;> simp [mem_front, readout]
  have pre_comp (u v : Address) (F : Set (Address × Bool)) :
      prefixed u (prefixed v F) = prefixed (u++v) F := by
    simp only [prefixed, Set.image_image]
    congr 1
    funext ⟨a,b⟩
    simp [List.append_assoc]
  have pre_union (u : Address) (F J : Set (Address × Bool)) :
      prefixed u (F ∪ J) = prefixed u F ∪ prefixed u J := Set.image_union _ _ _
  have pre_iUnion {I : Type} (u : Address) (F : I → Set (Address × Bool)) :
      prefixed u (⋃ i, F i) = ⋃ i, prefixed u (F i) := Set.image_iUnion
  have fold_front : ∀ (n : Nat) (f : Fin n → Source) (q : Source),
      labelledFrontier (comb n f q) =
      (⋃ i : Fin n, prefixed (List.replicate i.val true ++ [false]) (labelledFrontier (f i))) ∪
      prefixed (List.replicate n true) (labelledFrontier q) := by
    intro n
    induction n with
    | zero => intro f q; simp [comb, prefixed]
    | succ n ih =>
      intro f q
      rw [comb, pair_front, ih, pre_union, pre_iUnion]
      rw [Set.iUnion_fin_add_one_eq_iUnion_succ]
      simp only [Fin.val_zero, List.replicate_zero, List.nil_append, Fin.val_succ,
        List.replicate_succ, List.cons_append, pre_comp, Function.comp_def]
      exact (Set.union_assoc _ _ _).symm
  have pair_mem (S T : Source) (u : Address) (b : Bool) :
      (u,b) ∈ labelledFrontier (.mul S T) ↔
      (∃ v, (v,b) ∈ labelledFrontier S ∧ u = false :: v) ∨
      (∃ v, (v,b) ∈ labelledFrontier T ∧ u = true :: v) := by
    simp only [pair_front,Set.mem_union,pre_mem,List.singleton_append]
  have fold_mem (n : Nat) (f : Fin n → Source) (q : Source) (u : Address) (b : Bool) :
      (u,b) ∈ labelledFrontier (comb n f q) ↔
      (∃ i : Fin n, ∃ v, (v,b) ∈ labelledFrontier (f i) ∧
        u = List.replicate i.val true ++ false :: v) ∨
      (∃ v, (v,b) ∈ labelledFrontier q ∧ u = List.replicate n true ++ v) := by
    simp only [fold_front,Set.mem_union,Set.mem_iUnion,pre_mem,
      List.append_assoc,List.singleton_append]
  have pre_inj (w : Address) : Function.Injective
      (fun p : Address × Bool => (w++p.1,p.2)) := by
    intro p q h
    change (w++p.1,p.2) = (w++q.1,q.2) at h
    exact Prod.ext (List.append_right_injective w (Prod.mk.inj h).1) (Prod.mk.inj h).2
  have left_right (F J : Set (Address × Bool)) :
      Disjoint (prefixed [false] F) (prefixed [true] J) := by
    apply Set.disjoint_left.mpr
    rintro p ⟨⟨u,b⟩,hu,rfl⟩ ⟨⟨v,c⟩,hv,he⟩
    simp at he
  have block_succ (n : Nat) (f : Fin (n+1) → Source) (q : Source) (i : Fin (n+1)) :
      combBlock (n+1) f q i.succ =
        prefixed [true] (combBlock n (fun j => f j.succ) q i) := by
    by_cases hi : i.val < n
    · simp [combBlock, hi, pre_comp, List.replicate_succ, List.cons_append]
    · simp [combBlock, hi, pre_comp, List.replicate_succ, List.cons_append]
  have block_zero (n : Nat) (f : Fin (n+1) → Source) (q : Source) :
      combBlock (n+1) f q 0 = prefixed [false] (labelledFrontier (f 0)) := by
    simp [combBlock]
  have block_disjoint : ∀ (n : Nat) (f : Fin n → Source) (q : Source),
      Pairwise (fun i j => Disjoint (combBlock n f q i) (combBlock n f q j)) := by
    intro n
    induction n with
    | zero =>
      intro f q i j h
      exact (h (Fin.ext (by omega))).elim
    | succ n ih =>
      intro f q
      rw [pairwise_fin_succ_iff]
      refine ⟨?_,?_,?_⟩
      · intro i; rw [block_succ, block_zero]; exact (left_right _ _).symm
      · intro j; rw [block_zero, block_succ]; exact left_right _ _
      · intro i j hij
        rw [block_succ, block_succ]
        exact Set.disjoint_image_of_injective (pre_inj [true]) (ih _ _ hij)
  have A_front : labelledFrontier A =
      {([false,false],false), ([false,true],true), ([true],false)} := by
    simp only [A,E,pair_front,leaf_front,prefixed,Set.image_union,Set.image_singleton]
    ext p; simp [or_assoc,or_left_comm,or_comm]
  have E_front : labelledFrontier E = {([false],false),([true],true)} := by
    simp only [E,pair_front,leaf_front,prefixed,Set.image_union,Set.image_singleton]
    ext p; simp [or_assoc,or_left_comm,or_comm]
  have C_front : labelledFrontier C =
      {([false,false,false],false),([false,false,true],true),([false,true],false),
        ([true,false],false),([true,true],true)} := by
    simp only [C,A,E,pair_front,leaf_front,prefixed,Set.image_union,Set.image_singleton]
    ext p; simp [or_assoc,or_left_comm,or_comm]
  have B_front : labelledFrontier B =
      {([false,false,false,false],false),([false,false,false,true],true),
        ([false,false,true],false),([false,true,false],false),([false,true,true],true),
        ([true,false,false],false),([true,false,true],true),([true,true],false)} := by
    change labelledFrontier (.mul C A) = _
    simp only [C,A,E,pair_front,leaf_front,prefixed,Set.image_union,Set.image_singleton]
    ext p; simp [or_assoc,or_left_comm,or_comm]
  have H_extend : ∀ r : Nat, H r = comb (r+1) (fun _ => A) E := by
    intro r
    induction r with
    | zero => rfl
    | succ r ih => simpa only [comb] using congrArg (FreeMagma.mul A) ih
  have root_comb : ∀ (n : Nat) (f : Fin n → Source) (q : Source) (t : Nat),
      t ≤ n → readout [] q = .branch →
      readout (List.replicate t true) (comb n f q) = .branch := by
    intro n
    induction n with
    | zero =>
      intro f q t ht hq
      have he : t = 0 := by omega
      subst t
      exact hq
    | succ n ih =>
      intro f q t ht hq
      cases t with
      | zero => rfl
      | succ t =>
        simpa only [List.replicate_succ,comb,readout] using
          (ih (fun i => f i.succ) q t (by omega) hq)
  have E_past (d : Nat) (hd : 0 < d) (u : Address) :
      readout (List.replicate d true ++ false :: u) E = .absent := by
    cases d with
    | zero => omega
    | succ d => cases d <;> rfl
  have E_right_past (d : Nat) (hd : 0 < d) (u : Address) (b : Bool)
      (hu : (u,b) ∈ labelledFrontier E) :
      readout (List.replicate d true ++ u) E = .absent := by
    rw [E_front] at hu
    rcases (by simpa only [Set.mem_insert_iff,Set.mem_singleton_iff,Prod.mk.injEq] using hu :
      (u=[false] ∧ b=false) ∨ (u=[true] ∧ b=true)) with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    all_goals cases d with
    | zero => omega
    | succ d => cases d <;> rfl
  have H_slot (n t : Nat) (u : Address) (b : Bool) (hu : (u,b) ∈ labelledFrontier A) :
      readout (List.replicate t true ++ false :: u) (H n) =
        if n < t then .absent else label b := by
    rw [H_extend]
    by_cases ht : t ≤ n
    · rw [if_neg (by omega)]
      exact (comb_slot_readout (n+1) (fun _ => A) E ⟨t,by omega⟩ u).trans
        ((mem_front A u b).mp hu)
    · rw [if_pos (by omega)]
      have he : t = n+1+(t-(n+1)) := by omega
      rw [he,List.replicate_add,List.append_assoc,comb_tail_readout]
      cases hd : t-(n+1) with
      | zero =>
        rw [List.replicate_zero,List.nil_append]
        rw [A_front] at hu
        rcases (by simpa only [Set.mem_insert_iff,Set.mem_singleton_iff,Prod.mk.injEq] using hu :
          (u=[false,false] ∧ b=false) ∨ (u=[false,true] ∧ b=true) ∨ (u=[true] ∧ b=false))
          with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> rfl
      | succ d => exact E_past (d+1) (by omega) u
  have H_tail (r n : Nat) (u : Address) (b : Bool) (hu : (u,b) ∈ labelledFrontier E) :
      readout (List.replicate (r+1) true ++ u) (H n) =
        if r < n then .branch else if n < r then .absent else label b := by
    rw [H_extend]
    by_cases hlt : r < n
    · rw [if_pos hlt]
      rw [E_front] at hu
      rcases (by simpa only [Set.mem_insert_iff,Set.mem_singleton_iff,Prod.mk.injEq] using hu :
        (u=[false] ∧ b=false) ∨ (u=[true] ∧ b=true)) with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact comb_slot_readout (n+1) (fun _ => A) E ⟨r+1,by omega⟩ []
      · have he : List.replicate (r+1) true ++ [true] = List.replicate (r+2) true := by
          simp only [show r+2=(r+1)+1 from rfl,List.replicate_succ']
        rw [he]
        exact root_comb (n+1) (fun _ => A) E (r+2) (by omega) rfl
    · rw [if_neg hlt]
      by_cases hgt : n < r
      · rw [if_pos hgt]
        have he : r+1 = n+1+(r-n) := by omega
        rw [he,List.replicate_add,List.append_assoc,comb_tail_readout]
        exact E_right_past (r-n) (by omega) u b hu
      · have he : r = n := by omega
        subst r
        rw [if_neg (by omega),comb_tail_readout]
        exact (mem_front E u b).mp hu
  have A_B (u : Address) (b : Bool) (hu : (u,b) ∈ labelledFrontier A) :
      readout u B = .branch := by
    rw [A_front] at hu
    rcases (by simpa only [Set.mem_insert_iff,Set.mem_singleton_iff,Prod.mk.injEq] using hu :
      (u=[false,false] ∧ b=false) ∨ (u=[false,true] ∧ b=true) ∨ (u=[true] ∧ b=false))
      with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> rfl
  have B_A (u : Address) (b : Bool) (hu : (u,b) ∈ labelledFrontier B) :
      readout u A = .absent := by
    rw [B_front] at hu
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff,Prod.mk.injEq] at hu
    rcases hu with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ |
      ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> rfl
  have A_nonempty (u : Address) (b : Bool) (hu : (u,b) ∈ labelledFrontier A) : u ≠ [] := by
    rw [A_front] at hu
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff,Prod.mk.injEq] at hu
    rcases hu with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp
  have B_nonempty (u : Address) (b : Bool) (hu : (u,b) ∈ labelledFrontier B) : u ≠ [] := by
    intro he; subst u
    have hx : readout [] B = .branch := rfl
    cases b <;> simpa [mem_front,hx] using hu
  have H_bad (n t : Nat) (u : Address) (b : Bool) (hu : (u,b) ∈ labelledFrontier B) :
      readout (List.replicate t true ++ false :: u) (H n) = .absent := by
    rw [H_extend]
    by_cases ht : t ≤ n
    · exact (comb_slot_readout (n+1) (fun _ => A) E ⟨t,by omega⟩ u).trans (B_A u b hu)
    · have he : t = n+1+(t-(n+1)) := by omega
      rw [he,List.replicate_add,List.append_assoc,comb_tail_readout]
      cases hd : t-(n+1) with
      | zero =>
        simp only [List.replicate_zero,List.nil_append,E,readout]
        cases u with
        | nil => exact (B_nonempty [] b hu rfl).elim
        | cons d u => rfl
      | succ d => exact E_past (d+1) (by omega) u
  have C_far (n t : Nat) (hnt : n < t) (u : Address) (b : Bool)
      (hu : (u,b) ∈ labelledFrontier C) :
      readout (List.replicate t true ++ u) (H n) = .absent := by
    rw [C,pair_front] at hu
    rcases hu with ⟨⟨v,c⟩,hv,he⟩ | ⟨⟨v,c⟩,hv,he⟩
    · have hp : u = false :: v ∧ b = c := by simpa using he.symm
      rcases hp with ⟨rfl,rfl⟩
      rw [H_slot n t v b hv,if_pos hnt]
    · have hp : u = true :: v ∧ b = c := by simpa using he.symm
      rcases hp with ⟨rfl,rfl⟩
      have he : List.replicate t true ++ true :: v = List.replicate (t+1) true ++ v := by
        rw [List.replicate_add]; simp
      rw [he,H_tail t n v b hv,if_neg (by omega),if_pos hnt]
  have A_left_slot (t : Nat) (u : Address) (b : Bool) (hu : (u,b) ∈ labelledFrontier A) :
      readout (false :: (List.replicate t true ++ false :: u)) A = .absent := by
    cases t with
    | zero => cases u with
      | nil => exact (A_nonempty [] b hu rfl).elim
      | cons d u => rfl
    | succ t => cases t <;> rfl
  have A_left_tail (t : Nat) (u : Address) (b : Bool) (hu : (u,b) ∈ labelledFrontier E) :
      readout (false :: (List.replicate (t+1) true ++ u)) A = .absent := by
    rw [E_front] at hu
    rcases (by simpa only [Set.mem_insert_iff,Set.mem_singleton_iff,Prod.mk.injEq] using hu :
      (u=[false] ∧ b=false) ∨ (u=[true] ∧ b=true)) with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    all_goals cases t <;> rfl
  have A_right (u : Address) (b : Bool) (hu : (u,b) ∈ labelledFrontier A) :
      readout (true :: u) A = .absent := by
    cases u with
    | nil => exact (A_nonempty [] b hu rfl).elim
    | cons d u => rfl
  have A_Y (n : Nat) (u : Address) (b : Bool) (hu : (u,b) ∈ labelledFrontier A) :
      readout u (.mul (H n) A) = .branch := by
    rw [A_front] at hu
    rcases (by simpa only [Set.mem_insert_iff,Set.mem_singleton_iff,Prod.mk.injEq] using hu :
      (u=[false,false] ∧ b=false) ∨ (u=[false,true] ∧ b=true) ∨ (u=[true] ∧ b=false))
      with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · cases n <;> rfl
    · change readout [true] (H n) = .branch
      rw [H_extend]
      exact root_comb (n+1) (fun _ => A) E 1 (by omega) rfl
    · rfl
  have G_slot (k : Nat) (j t : Fin k) (u : Address) (b : Bool)
      (hu : (u,b) ∈ labelledFrontier A) :
      readout (List.replicate t.val true ++ false :: u) (G k j) =
        if j.val = t.val then .branch else label b := by
    rw [comb_slot_readout]
    by_cases he : t = j
    · subst t; rw [if_pos rfl,if_pos rfl]; exact A_B u b hu
    · rw [if_neg he,if_neg (by intro h; exact he (Fin.ext h.symm))]
      exact (mem_front A u b).mp hu
  have G_tail_E (k : Nat) (j i : Fin k) (u : Address) (b : Bool)
      (hu : (u,b) ∈ labelledFrontier E) :
      readout (List.replicate (i.val+1) true ++ u) (G k j) = .branch := by
    rw [E_front] at hu
    rcases (by simpa only [Set.mem_insert_iff,Set.mem_singleton_iff,Prod.mk.injEq] using hu :
      (u=[false] ∧ b=false) ∨ (u=[true] ∧ b=true)) with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · by_cases hi : i.val+1 < k
      · rw [comb_slot_readout k (fun l => ite (l=j) B A) C ⟨i.val+1,hi⟩ []]
        split_ifs <;> rfl
      · have he : i.val+1 = k := by omega
        rw [he,comb_tail_readout]; rfl
    · have he : List.replicate (i.val+1) true ++ [true] =
          List.replicate (i.val+2) true := by simp only [show i.val+2=(i.val+1)+1 from rfl,List.replicate_succ']
      rw [he]
      by_cases hi : i.val+2 ≤ k
      · exact root_comb k (fun l => ite (l=j) B A) C (i.val+2) hi rfl
      · have he : i.val+2 = k+1 := by omega
        rw [he,List.replicate_add]
        exact comb_tail_readout k (fun l => ite (l=j) B A) C [true]
  have block_front (n : Nat) (f : Fin n → Source) (q : Source) :
      labelledFrontier (comb n f q) = ⋃ i : Fin (n+1), combBlock n f q i := by
    rw [Set.iUnion_fin_add_one_eq_iUnion_castSucc]
    simp only [combBlock,Fin.val_castSucc,Fin.isLt,Fin.val_last,lt_self_iff_false,
      dite_false,dite_true,Function.comp_def]
    exact fold_front n f q
  have cover_rows (k : Nat) : ∀ (Z : Index k) (a : Address) (b : Bool),
      (a,b) ∈ labelledFrontier (family k Z) →
      ∃ r : LeafRow k, r.target = Z ∧ (a,b) ∈ r.block := by
    intro Z a b ha
    cases Z with
    | inl v =>
      cases v
      rcases (pair_mem _ _ _ _).mp ha with ⟨u,hu,rfl⟩ | ⟨u,hu,rfl⟩
      · rcases (fold_mem k (fun _ => A) C u b).mp hu with
          ⟨t,w,hw,rfl⟩ | ⟨w,hw,rfl⟩
        · exact ⟨.pSlot t,rfl,(pre_mem _ _ _ _).mpr ⟨w,hw,by simp⟩⟩
        · exact ⟨.pTail,rfl,(pre_mem _ _ _ _).mpr ⟨w,hw,rfl⟩⟩
      · change (u,b) ∈ labelledFrontier (.mul C A) at hu
        rcases (pair_mem _ _ _ _).mp hu with ⟨v,hv,rfl⟩ | ⟨v,hv,rfl⟩
        · rcases (pair_mem A E v b).mp hv with ⟨w,hw,rfl⟩ | ⟨w,hw,rfl⟩
          · exact ⟨.pOuter false,rfl,(pre_mem _ _ _ _).mpr ⟨w,hw,rfl⟩⟩
          · exact ⟨.pInner,rfl,(pre_mem _ _ _ _).mpr ⟨w,hw,rfl⟩⟩
        · exact ⟨.pOuter true,rfl,(pre_mem _ _ _ _).mpr ⟨v,hv,rfl⟩⟩
    | inr Z => cases Z with
      | inl j =>
        rcases (pair_mem _ _ _ _).mp ha with ⟨u,hu,rfl⟩ | ⟨u,hu,rfl⟩
        · rcases (fold_mem k (fun l => ite (l=j) B A) C u b).mp hu with
            ⟨t,w,hw,rfl⟩ | ⟨w,hw,rfl⟩
          · by_cases ht : t = j
            · subst t
              rw [if_pos rfl] at hw
              exact ⟨.xExceptional j,rfl,(pre_mem _ _ _ _).mpr ⟨w,hw,by simp⟩⟩
            · rw [if_neg ht] at hw
              exact ⟨.xSlot j t ht,rfl,(pre_mem _ _ _ _).mpr ⟨w,hw,by simp⟩⟩
          · exact ⟨.xTail j,rfl,(pre_mem _ _ _ _).mpr ⟨w,hw,rfl⟩⟩
        · exact ⟨.xRight j,rfl,(pre_mem _ _ _ _).mpr ⟨u,hu,rfl⟩⟩
      | inr i =>
        rcases (pair_mem _ _ _ _).mp ha with ⟨u,hu,rfl⟩ | ⟨u,hu,rfl⟩
        · rw [H_extend] at hu
          rcases (fold_mem (i.val+1) (fun _ => A) E u b).mp hu with
              ⟨t,w,hw,rfl⟩ | ⟨w,hw,rfl⟩
          · exact ⟨.ySlot i t,rfl,(pre_mem _ _ _ _).mpr ⟨w,hw,by simp⟩⟩
          · exact ⟨.yLeftTail i,rfl,(pre_mem _ _ _ _).mpr ⟨w,hw,rfl⟩⟩
        · rcases (pair_mem _ _ _ _).mp hu with ⟨v,hv,rfl⟩ | ⟨v,hv,rfl⟩
          · rw [H_extend] at hv
            rcases (fold_mem (k-i.val+1) (fun _ => A) E v b).mp hv with
                ⟨h,w,hw,rfl⟩ | ⟨w,hw,rfl⟩
            · exact ⟨.yRightSlot i h,rfl,(pre_mem _ _ _ _).mpr ⟨w,hw,by simp⟩⟩
            · exact ⟨.yRightTail i,rfl,(pre_mem _ _ _ _).mpr ⟨w,hw,rfl⟩⟩
          · exact ⟨.yRightA i,rfl,(pre_mem _ _ _ _).mpr ⟨v,hv,rfl⟩⟩
  have left_three (F J K : Set (Address × Bool)) :
      Pairwise (fun i j : Fin 3 => Disjoint
        (![prefixed [false,false] F,prefixed [false,true] J,prefixed [true] K] i)
        (![prefixed [false,false] F,prefixed [false,true] J,prefixed [true] K] j)) := by
    have d01 : Disjoint (prefixed [false,false] F) (prefixed [false,true] J) := by
      simpa only [pre_comp,List.singleton_append] using
        (show Disjoint (prefixed [false] (prefixed [false] F))
          (prefixed [false] (prefixed [true] J)) from
          Set.disjoint_image_of_injective (pre_inj [false]) (left_right F J))
    have d02 : Disjoint (prefixed [false,false] F) (prefixed [true] K) := by
      simpa only [pre_comp,List.singleton_append] using left_right (prefixed [false] F) K
    have d12 : Disjoint (prefixed [false,true] J) (prefixed [true] K) := by
      simpa only [pre_comp,List.singleton_append] using left_right (prefixed [true] J) K
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij
    all_goals first
      | exact d01
      | exact d01.symm
      | exact d02
      | exact d02.symm
      | exact d12
      | exact d12.symm
  have right_three (F J K : Set (Address × Bool)) :
      Pairwise (fun i j : Fin 3 => Disjoint
        (![prefixed [false] F,prefixed [true,false] J,prefixed [true,true] K] i)
        (![prefixed [false] F,prefixed [true,false] J,prefixed [true,true] K] j)) := by
    have d01 : Disjoint (prefixed [false] F) (prefixed [true,false] J) := by
      simpa only [pre_comp,List.singleton_append] using left_right F (prefixed [false] J)
    have d02 : Disjoint (prefixed [false] F) (prefixed [true,true] K) := by
      simpa only [pre_comp,List.singleton_append] using left_right F (prefixed [true] K)
    have d12 : Disjoint (prefixed [true,false] J) (prefixed [true,true] K) := by
      simpa only [pre_comp,List.singleton_append] using
        (show Disjoint (prefixed [true] (prefixed [false] J))
          (prefixed [true] (prefixed [true] K)) from
          Set.disjoint_image_of_injective (pre_inj [true]) (left_right J K))
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij
    all_goals first
      | exact d01
      | exact d01.symm
      | exact d02
      | exact d02.symm
      | exact d12
      | exact d12.symm
  have responses (k : Nat) (hk : 1 ≤ k) :
      ∀ (r : LeafRow k) (U : Index k), U ≠ r.target →
      ∀ (a : Address) (b : Bool), (a,b) ∈ r.block →
        readout a (family k U) = r.reply U b := by
    intro r U hne a b hab
    cases r with
    | pSlot t =>
      rcases (pre_mem _ _ _ _).mp hab with ⟨u,hu,rfl⟩
      cases U with
      | inl v => cases v; exact (hne rfl).elim
      | inr U => cases U with
        | inl j => simpa [List.append_assoc,List.singleton_append,List.replicate_one,
            (show B = .mul C A from rfl),comb,List.cons_append, family,readout,LeafRow.reply] using G_slot k j t u b hu
        | inr i => simpa [List.append_assoc,List.singleton_append,List.replicate_one,
            (show B = .mul C A from rfl),comb,List.cons_append,family,readout,LeafRow.reply]
            using H_slot i.val t.val u b hu
    | pTail =>
      rcases (pre_mem _ _ _ _).mp hab with ⟨u,hu,rfl⟩
      cases U with
      | inl v => cases v; exact (hne rfl).elim
      | inr U => cases U with
        | inl j => simpa [List.append_assoc,List.singleton_append,List.replicate_one,
            (show B = .mul C A from rfl),comb,List.cons_append,family,readout,LeafRow.reply] using
            (comb_tail_readout k (fun l => ite (l=j) B A) C u).trans ((mem_front C u b).mp hu)
        | inr i => simpa [List.append_assoc,List.singleton_append,List.replicate_one,
            (show B = .mul C A from rfl),comb,List.cons_append,family,readout,LeafRow.reply] using C_far i.val k i.isLt u b hu
    | pOuter right =>
      cases right <;> rcases (pre_mem _ _ _ _).mp hab with ⟨u,hu,rfl⟩
      all_goals cases U with
      | inl v => cases v; exact (hne rfl).elim
      | inr U => cases U with
        | inl j =>
          first
          | simpa [List.append_assoc,List.singleton_append,List.replicate_one,
            (show B = .mul C A from rfl),comb,List.cons_append,List.nil_append,family,readout,LeafRow.reply] using A_left_slot 0 u b hu
          | simpa [List.append_assoc,List.singleton_append,List.replicate_one,
            (show B = .mul C A from rfl),comb,List.cons_append,List.nil_append,family,readout,LeafRow.reply] using A_right u b hu
        | inr i =>
          first
          | simpa [List.append_assoc,List.singleton_append,List.replicate_one,
            (show B = .mul C A from rfl),comb,List.cons_append,List.nil_append,family,readout,LeafRow.reply,(show ¬ k-i.val < 0 from by omega)]
              using H_slot (k-i.val) 0 u b hu
          | exact (mem_front A u b).mp hu
    | pInner =>
      rcases (pre_mem _ _ _ _).mp hab with ⟨u,hu,rfl⟩
      cases U with
      | inl v => cases v; exact (hne rfl).elim
      | inr U => cases U with
        | inl j => simpa [List.append_assoc,List.singleton_append,List.replicate_one,
            (show B = .mul C A from rfl),comb,List.cons_append,List.nil_append,family,readout,LeafRow.reply]
            using A_left_tail 0 u b hu
        | inr i =>
          simpa [List.append_assoc,List.singleton_append,List.replicate_one,
            (show B = .mul C A from rfl),comb,List.cons_append,List.nil_append,family,readout,LeafRow.reply,(show 0 < k-i.val from by omega)]
            using H_tail 0 (k-i.val) u b hu
    | xSlot j t ht =>
      rcases (pre_mem _ _ _ _).mp hab with ⟨u,hu,rfl⟩
      cases U with
      | inl v => simpa [List.append_assoc,List.singleton_append,List.replicate_one,
            (show B = .mul C A from rfl),comb,List.cons_append,family,readout,LeafRow.reply,(show ¬ k < t.val from by omega)]
          using H_slot k t.val u b hu
      | inr U => cases U with
        | inl l => simpa [List.append_assoc,List.singleton_append,List.replicate_one,
            (show B = .mul C A from rfl),comb,List.cons_append,family,readout,LeafRow.reply] using G_slot k l t u b hu
        | inr i => simpa [List.append_assoc,List.singleton_append,List.replicate_one,
            (show B = .mul C A from rfl),comb,List.cons_append,family,readout,LeafRow.reply]
            using H_slot i.val t.val u b hu
    | xExceptional j =>
      rcases (pre_mem _ _ _ _).mp hab with ⟨u,hu,rfl⟩
      cases U with
      | inl v => simpa [List.append_assoc,List.singleton_append,List.replicate_one,
            (show B = .mul C A from rfl),comb,List.cons_append,family,readout,LeafRow.reply] using H_bad k j.val u b hu
      | inr U => cases U with
        | inl l =>
          have hjl : j ≠ l := by intro he; subst l; exact hne rfl
          simp only [List.cons_append,List.append_assoc,List.singleton_append,family,readout,LeafRow.reply]
          change readout (List.replicate j.val true ++ false :: u) (G k l) = .absent
          rw [comb_slot_readout,if_neg hjl]
          exact B_A u b hu
        | inr i => simpa [List.append_assoc,List.singleton_append,List.replicate_one,
            (show B = .mul C A from rfl),comb,List.cons_append,family,readout,LeafRow.reply] using H_bad i.val j.val u b hu
    | xTail j =>
      rcases (pre_mem _ _ _ _).mp hab with ⟨u,hu,rfl⟩
      cases U with
      | inl v => simpa [List.append_assoc,List.singleton_append,List.replicate_one,
            (show B = .mul C A from rfl),comb,List.cons_append,family,readout,LeafRow.reply] using
          (comb_tail_readout k (fun _ => A) C u).trans ((mem_front C u b).mp hu)
      | inr U => cases U with
        | inl l => simpa [List.append_assoc,List.singleton_append,List.replicate_one,
            (show B = .mul C A from rfl),comb,List.cons_append,family,readout,LeafRow.reply] using
            (comb_tail_readout k (fun m => ite (m=l) B A) C u).trans ((mem_front C u b).mp hu)
        | inr i => simpa [List.append_assoc,List.singleton_append,List.replicate_one,
            (show B = .mul C A from rfl),comb,List.cons_append,family,readout,LeafRow.reply] using C_far i.val k i.isLt u b hu
    | xRight j =>
      rcases (pre_mem _ _ _ _).mp hab with ⟨u,hu,rfl⟩
      cases U with
      | inl v => simpa [List.append_assoc,List.singleton_append,List.replicate_one,
            (show B = .mul C A from rfl),comb,List.singleton_append,family,readout,LeafRow.reply] using A_B u b hu
      | inr U => cases U with
        | inl l => exact (mem_front A u b).mp hu
        | inr i => simpa [List.append_assoc,List.singleton_append,List.replicate_one,
            (show B = .mul C A from rfl),comb,List.singleton_append,family,readout,LeafRow.reply] using A_Y (k-i.val) u b hu
    | ySlot i t =>
      rcases (pre_mem _ _ _ _).mp hab with ⟨u,hu,rfl⟩
      have ht : t.val < k := by omega
      cases U with
      | inl v => simpa [List.append_assoc,List.singleton_append,List.replicate_one,
            (show B = .mul C A from rfl),comb,List.cons_append,family,readout,LeafRow.reply,(show ¬ k < t.val from by omega)]
          using H_slot k t.val u b hu
      | inr U => cases U with
        | inl j => simpa [List.append_assoc,List.singleton_append,List.replicate_one,
            (show B = .mul C A from rfl),comb,List.cons_append,family,readout,LeafRow.reply] using G_slot k j ⟨t.val,ht⟩ u b hu
        | inr j => simpa [List.append_assoc,List.singleton_append,List.replicate_one,
            (show B = .mul C A from rfl),comb,List.cons_append,family,readout,LeafRow.reply]
            using H_slot j.val t.val u b hu
    | yLeftTail i =>
      rcases (pre_mem _ _ _ _).mp hab with ⟨u,hu,rfl⟩
      cases U with
      | inl v => simpa [List.append_assoc,List.singleton_append,List.replicate_one,
            (show B = .mul C A from rfl),comb,List.cons_append,family,readout,LeafRow.reply,i.isLt]
          using H_tail i.val k u b hu
      | inr U => cases U with
        | inl j => simpa [List.append_assoc,List.singleton_append,List.replicate_one,
            (show B = .mul C A from rfl),comb,List.cons_append,family,readout,LeafRow.reply] using G_tail_E k j i u b hu
        | inr j => simpa [List.append_assoc,List.singleton_append,List.replicate_one,
            (show B = .mul C A from rfl),comb,List.cons_append,family,readout,LeafRow.reply] using H_tail i.val j.val u b hu
    | yRightSlot i h =>
      rcases (pre_mem _ _ _ _).mp hab with ⟨u,hu,rfl⟩
      cases U with
      | inl v => simpa [List.append_assoc,List.singleton_append,List.replicate_one,
            (show B = .mul C A from rfl),comb,List.cons_append,family,readout,LeafRow.reply]
          using H_slot 0 h.val u b hu
      | inr U => cases U with
        | inl j => simpa [List.append_assoc,List.singleton_append,List.replicate_one,
            (show B = .mul C A from rfl),comb,List.cons_append,family,readout,LeafRow.reply] using A_left_slot h.val u b hu
        | inr j => simpa [List.append_assoc,List.singleton_append,List.replicate_one,
            (show B = .mul C A from rfl),comb,List.cons_append,family,readout,LeafRow.reply]
            using H_slot (k-j.val) h.val u b hu
    | yRightTail i =>
      rcases (pre_mem _ _ _ _).mp hab with ⟨u,hu,rfl⟩
      cases U with
      | inl v => simpa [List.append_assoc,List.singleton_append,List.replicate_one,
            (show B = .mul C A from rfl),comb,List.cons_append,family,readout,LeafRow.reply,
          (show ¬ k-i.val < 0 from by omega),(show 0 < k-i.val from by omega)]
          using H_tail (k-i.val) 0 u b hu
      | inr U => cases U with
        | inl j => simpa [List.append_assoc,List.singleton_append,List.replicate_one,
            (show B = .mul C A from rfl),comb,List.cons_append,family,readout,LeafRow.reply] using A_left_tail (k-i.val) u b hu
        | inr j =>
          have e1 : k-i.val < k-j.val ↔ j.val < i.val := by omega
          have e2 : k-j.val < k-i.val ↔ i.val < j.val := by omega
          simpa [List.append_assoc,List.singleton_append,List.replicate_one,
            (show B = .mul C A from rfl),comb,List.cons_append,family,readout,LeafRow.reply,e1,e2] using H_tail (k-i.val) (k-j.val) u b hu
    | yRightA i =>
      rcases (pre_mem _ _ _ _).mp hab with ⟨u,hu,rfl⟩
      cases U with
      | inl v => exact (mem_front A u b).mp hu
      | inr U => cases U with
        | inl j => simpa [List.append_assoc,List.singleton_append,List.replicate_one,
            (show B = .mul C A from rfl),comb,List.cons_append,List.nil_append,family,readout,LeafRow.reply] using A_right u b hu
        | inr j => exact (mem_front A u b).mp hu
  refine ⟨A_front,E_front,?_,?_,?_,?_,?_,?_,H_slot,H_tail,A_B,B_A,cover_rows k,responses k hk⟩
  · intro r
    refine ⟨?_,block_disjoint (r+1) (fun _ => A) E⟩
    rw [H_extend]
    exact block_front (r+1) (fun _ => A) E
  · refine ⟨?_,left_three (labelledFrontier A) (labelledFrontier E) (labelledFrontier A)⟩
    change labelledFrontier (.mul C A) = _
    rw [pair_front,C,pair_front,pre_union,pre_comp,pre_comp]
  · intro j
    exact ⟨block_front k (fun l => ite (l=j) B A) C,block_disjoint k (fun l => ite (l=j) B A) C⟩
  · exact ⟨pair_front _ _,left_right _ _⟩
  · intro j
    exact ⟨pair_front _ _,left_right _ _⟩
  · intro i
    refine ⟨?_,right_three (labelledFrontier (H i.val))
      (labelledFrontier (H (k-i.val))) (labelledFrontier A)⟩
    change labelledFrontier (.mul (H i.val) (.mul (H (k-i.val)) A)) = _
    rw [pair_front,pair_front,pre_union,pre_comp,pre_comp]
    exact (Set.union_assoc _ _ _).symm
end D5.S3.Arith.FibonacciAtomic.Scale38LeafFrontierResponse
