/- GID: D5/S3/Combinatorics/PriorityLattice/TestartTraversal
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PriorityLattice/TestartTraversal
   mirror-E: none(waiver:structural-traversal)
   anchors: []
   utility: none
   digest: Decreasing-child preorder and cycle words for native increasing trees. -/

import D5.S3.Combinatorics.PriorityLattice.TestartTreeCode

/-! Literal component words and the defining depth-first traversal equation. -/

namespace D5.S3.Combinatorics.PriorityLattice.TestartTraversal

open Equiv TestartTreeCode

/-- Insert after each occurrence. On the distinct-label words used here this
inserts at the unique occurrence, and absent labels leave the word unchanged. -/
def splice (p x : ℕ) : List ℕ → List ℕ
  | [] => []
  | y :: ys => if y = p then y :: x :: splice p x ys else y :: splice p x ys

private theorem splice_append (p x : ℕ) (u v : List ℕ) :
    splice p x (u ++ v) = splice p x u ++ splice p x v := by
  induction u with
  | nil => rfl
  | cons y ys ih => simp [splice, ih, List.cons_append]; split <;> rfl

private theorem splice_flatMap (p x : ℕ) (l : List ℕ) (f : ℕ → List ℕ) :
    splice p x (l.flatMap f) = l.flatMap (fun y => splice p x (f y)) := by
  induction l with
  | nil => rfl
  | cons y ys ih => simp [splice_append, ih]

private theorem splice_of_not_mem (p x : ℕ) (l : List ℕ) (h : p ∉ l) :
    splice p x l = l := by
  induction l with
  | nil => rfl
  | cons y ys ih =>
    simp only [List.mem_cons, not_or] at h
    simp [splice, (Ne.symm h.1), ih h.2]

private theorem mem_splice {p x z : ℕ} {l : List ℕ} :
    z ∈ splice p x l ↔ z ∈ l ∨ (z = x ∧ p ∈ l) := by
  induction l with
  | nil => simp [splice]
  | cons y ys ih => by_cases h : y = p <;> simp [splice, h, ih] <;> tauto

private theorem splice_perm {p x : ℕ} {l : List ℕ} (hl : l.Nodup) (hp : p ∈ l) :
    (splice p x l).Perm (x :: l) := by
  induction l with
  | nil => simp at hp
  | cons y ys ih =>
    have hn := List.nodup_cons.mp hl
    by_cases h : y = p
    · subst y
      rw [splice, ite_eq_left rfl, splice_of_not_mem p x ys hn.1]
      exact List.Perm.swap _ _ _
    · have hm : p ∈ ys := (List.mem_cons.mp hp).resolve_left (Ne.symm h)
      rw [splice, ite_eq_right h]
      exact ((ih hn.2 hm).cons y).trans (List.Perm.swap _ _ _)

/-- Children enumerated in strictly decreasing label order. -/
def children : (n : ℕ) → ParentCode n → ℕ → List ℕ
  | 0, _, _ => []
  | n+1, t, r => if (t (Fin.last n)).val = r then
      (n+1) :: children n (fun v => t v.castSucc) r
    else children n (fun v => t v.castSucc) r

/-- Maximum-label insertion implementation of preorder. Its recursive DFS
unfolding is proved below; it has no plane-order input. -/
def preorder : (n : ℕ) → ParentCode n → ℕ → List ℕ
  | 0, _, r => [r]
  | n+1, t, r => if r = n+1 then [r] else
      splice (t (Fin.last n)).val (n+1) (preorder n (fun v => t v.castSucc) r)

private theorem children_bounds (n : ℕ) (t : ParentCode n) (r c : ℕ)
    (hc : c ∈ children n t r) : r < c ∧ c ≤ n := by
  induction n with
  | zero => simp [children] at hc
  | succ n ih =>
    simp only [children] at hc
    split at hc
    · rename_i hp
      rcases List.mem_cons.mp hc with h | h
      · have := by simpa only [Fin.val_last] using (t (Fin.last n)).isLt
        omega
      · exact (ih _ h).imp_right (by omega)
    · exact (ih _ hc).imp_right (by omega)

private theorem children_decreasing (n : ℕ) (t : ParentCode n) (r : ℕ) :
    (children n t r).Pairwise (fun x y => y < x) := by
  induction n with
  | zero => simp [children]
  | succ n ih =>
    simp only [children]
    split
    · simp only [List.pairwise_cons]
      exact ⟨fun c hc => by have := (children_bounds n _ r c hc).2; omega, ih _⟩
    · exact ih _

private theorem children_incidence (n : ℕ) (t : ParentCode n) (r c : ℕ) :
    c ∈ children n t r ↔ ∃ v : Fin n, v.val + 1 = c ∧ (t v).val = r := by
  induction n with
  | zero => simp [children]
  | succ n ih =>
    simp only [children]
    constructor
    · intro h
      split at h
      · rename_i hp
        rcases List.mem_cons.mp h with h | h
        · exact ⟨Fin.last n, by simpa using h.symm, hp⟩
        · obtain ⟨v,hv,hp⟩ := (ih _).mp h
          exact ⟨v.castSucc,hv,hp⟩
      · obtain ⟨v,hv,hp⟩ := (ih _).mp h
        exact ⟨v.castSucc,hv,hp⟩
    · rintro ⟨v,hv,hp⟩
      revert hv hp
      refine Fin.lastCases ?_ (fun j => ?_) v
      · intro hv hp
        simp only [Fin.val_last] at hv
        simp [hp, ← hv]
      · intro hv hp
        have hc := (ih (fun w => t w.castSucc)).mpr ⟨j,hv,hp⟩
        split <;> simp_all

/-- The defining root-first depth-first equation, with decreasing child roots.
It also covers leaves, whose child list is empty. -/
private theorem preorder_dfs (n : ℕ) (t : ParentCode n) (r : ℕ) (hr : r ≤ n) :
    preorder n t r = r :: (children n t r).flatMap (preorder n t) := by
  induction n generalizing r with
  | zero => simp [preorder, children]
  | succ n ih =>
    by_cases h : r = n+1
    · subst r
      have hc : children (n+1) t (n+1) = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro c hc
        have := children_bounds (n+1) t (n+1) c hc
        omega
      simp [preorder, hc]
    · have hrn : r ≤ n := by omega
      rw [preorder, ite_eq_right h, ih _ r hrn, splice]
      have he : (children n (fun v => t v.castSucc) r).flatMap (preorder (n+1) t) =
          (children n (fun v => t v.castSucc) r).flatMap
            (fun c => splice (t (Fin.last n)).val (n+1)
              (preorder n (fun v => t v.castSucc) c)) := by
        apply List.flatMap_congr
        intro c hc
        have hb := (children_bounds n _ r c hc).2
        simp [preorder, show c ≠ n+1 by omega]
      rw [splice_flatMap, children]
      split <;> simp_all [preorder, eq_comm]

private theorem preorder_bounds (n : ℕ) (t : ParentCode n) (r z : ℕ) (hr : r ≤ n)
    (hz : z ∈ preorder n t r) : r ≤ z ∧ z ≤ n := by
  induction n generalizing r with
  | zero => simp [preorder] at hz; omega
  | succ n ih =>
    by_cases h : r = n+1
    · simp [preorder,h] at hz; omega
    · rw [preorder, ite_eq_right h, mem_splice] at hz
      rcases hz with hz | ⟨rfl,_⟩
      · exact (ih _ r (by omega) hz).imp_right (by omega)
      · omega

private theorem preorder_nodup (n : ℕ) (t : ParentCode n) (r : ℕ) (hr : r ≤ n) :
    (preorder n t r).Nodup := by
  induction n generalizing r with
  | zero => simp [preorder]
  | succ n ih =>
    by_cases h : r = n+1
    · simp [preorder,h]
    · rw [preorder, ite_eq_right h]
      have hd := ih (fun v => t v.castSucc) r (by omega)
      by_cases hp : (t (Fin.last n)).val ∈ preorder n (fun v => t v.castSucc) r
      · apply (splice_perm hd hp).nodup_iff.mpr
        rw [List.nodup_cons]
        exact ⟨fun hx => by have := (preorder_bounds n _ r (n+1) (by omega) hx).2; omega, hd⟩
      · rw [splice_of_not_mem _ _ _ hp]
        exact hd

private theorem preorder_root_perm (n : ℕ) (t : ParentCode n) :
    (preorder n t 0).Perm (List.range (n+1)) := by
  induction n with
  | zero => simp [preorder]
  | succ n ih =>
    have ht := ih (fun v => t v.castSucc)
    have hp : (t (Fin.last n)).val ∈ preorder n (fun v => t v.castSucc) 0 := by
      rw [ht.mem_iff]
      simpa using (t (Fin.last n)).isLt
    have hh := (splice_perm (preorder_nodup n _ 0 (by omega)) hp).trans (ht.cons (n+1))
    simp only [preorder, show ¬ (0 : ℕ) = n+1 by omega, ite_false]
    exact hh.trans (by simpa [List.range_succ] using List.perm_append_comm (l₁ := [n+1]) (l₂ := List.range (n+1)))

/-- Root deletion followed by the prescribed component preorders. -/
def componentWords (n : ℕ) (t : ParentCode n) : List (List ℕ) :=
  (children n t 0).map (preorder n t)

private theorem components_perm (n : ℕ) (t : ParentCode n) :
    (componentWords n t).flatten.Perm (List.range' 1 n) := by
  have h := preorder_root_perm n t
  rw [preorder_dfs n t 0 (by omega)] at h
  change (0 :: (componentWords n t).flatten).Perm _ at h
  apply List.Perm.cons_inv (a := 0)
  simpa only [List.range_eq_range', List.range'_succ] using h

private theorem splice_formPerm {p x : ℕ} {l : List ℕ} (hl : l.Nodup)
    (hx : x ∉ l) (hp : p ∈ l) :
    (splice p x l).formPerm = l.formPerm * Equiv.swap p x := by
  induction l with
  | nil => simp at hp
  | cons y ys ih =>
    have hn := List.nodup_cons.mp hl
    have hxn : x ≠ y ∧ x ∉ ys := by simpa using hx
    by_cases h : y = p
    · subst y
      rw [splice, ite_eq_left rfl, splice_of_not_mem p x ys hn.1]
      cases ys with
      | nil => simp
      | cons z zs =>
        have hpz : z ≠ p := fun hz => hn.1 (by simp [hz])
        have hxz : z ≠ x := fun hz => hxn.2 (by simp [hz])
        have hcomm : (z :: zs).formPerm * Equiv.swap p x =
            Equiv.swap p x * (z :: zs).formPerm := by
          rw [Equiv.mul_swap_eq_swap_mul,
            List.formPerm_apply_of_notMem hn.1,
            List.formPerm_apply_of_notMem hxn.2]
        have hbraid : Equiv.swap p x * Equiv.swap x z =
            Equiv.swap p z * Equiv.swap p x := by
          rw [Equiv.mul_swap_eq_swap_mul]
          simp [Equiv.swap_apply_of_ne_of_ne, hpz, hxz]
        simp only [List.formPerm_cons_cons]
        rw [← mul_assoc, hbraid, mul_assoc, ← hcomm, ← mul_assoc]
    · have hp' : p ∈ ys := (List.mem_cons.mp hp).resolve_left (Ne.symm h)
      have hi := ih hn.2 hxn.2 hp'
      cases ys with
      | nil => simp at hp'
      | cons z zs =>
        have hs : (y :: splice p x (z :: zs)).formPerm =
            Equiv.swap y z * (splice p x (z :: zs)).formPerm := by
          by_cases hz : z = p <;> simp [splice, hz]
        rw [splice, ite_eq_right h, hs, hi]
        simp [mul_assoc]

/-- Make each component word a cycle, in its original direction. -/
def cycleProduct (ws : List (List ℕ)) : Perm ℕ := (ws.map List.formPerm).prod

private theorem cycleProduct_fix (ws : List (List ℕ)) (v : ℕ) (h : v ∉ ws.flatten) :
    cycleProduct ws v = v := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    have hw : v ∉ w := by intro hv; exact h (by simp [hv])
    have hs : v ∉ ws.flatten := by intro hv; exact h (by simp [hv])
    change w.formPerm (cycleProduct ws v) = v
    rw [ih hs, List.formPerm_apply_of_notMem hw]

private theorem cycleProduct_splice (ws : List (List ℕ)) (p x : ℕ)
    (hd : ws.flatten.Nodup) (hp : p ∈ ws.flatten) (hx : x ∉ ws.flatten) :
    cycleProduct (ws.map (splice p x)) = cycleProduct ws * Equiv.swap p x := by
  induction ws with
  | nil => simp at hp
  | cons w ws ih =>
    have hn : (w ++ ws.flatten).Nodup := hd
    have hw : w.Nodup := (List.nodup_append'.mp hn).1
    have hs : ws.flatten.Nodup := (List.nodup_append'.mp hn).2.1
    have hxw : x ∉ w := fun h => hx (by simp [h])
    have hxs : x ∉ ws.flatten := fun h => hx (by simp [h])
    by_cases hpw : p ∈ w
    · have hps : p ∉ ws.flatten := fun h => (List.nodup_append'.mp hn).2.2 hpw h
      have hm : ws.map (splice p x) = ws := by
        conv_rhs => rw [← List.map_id ws]
        apply List.map_congr_left
        intro u hu
        exact splice_of_not_mem p x u (by
          intro h; exact hps (List.mem_flatten.mpr ⟨u,hu,h⟩))
      have hc : cycleProduct ws * Equiv.swap p x = Equiv.swap p x * cycleProduct ws := by
        rw [Equiv.mul_swap_eq_swap_mul,
          cycleProduct_fix ws p hps, cycleProduct_fix ws x hxs]
      simp only [List.map_cons, cycleProduct, List.map_cons, List.prod_cons] at hm ⊢
      rw [splice_formPerm hw hxw hpw]
      change (w.formPerm * Equiv.swap p x) * cycleProduct (ws.map (splice p x)) = _
      rw [hm, mul_assoc, ← hc, ← mul_assoc]
      rfl
    · have hps : p ∈ ws.flatten := by simpa [hpw] using hp
      have hi := ih hs hps hxs
      simp only [List.map_cons, cycleProduct, List.map_cons, List.prod_cons]
      rw [splice_of_not_mem p x w hpw]
      change w.formPerm * cycleProduct (ws.map (splice p x)) = _
      rw [hi, ← mul_assoc]
      rfl

private theorem components_succ (n : ℕ) (t : ParentCode (n+1)) :
    componentWords (n+1) t =
      if (t (Fin.last n)).val = 0 then [n+1] :: componentWords n (fun v => t v.castSucc)
      else (componentWords n (fun v => t v.castSucc)).map
        (splice (t (Fin.last n)).val (n+1)) := by
  have hm : (children n (fun v => t v.castSucc) 0).map (preorder (n+1) t) =
      (componentWords n (fun v => t v.castSucc)).map
        (splice (t (Fin.last n)).val (n+1)) := by
    simp only [componentWords, List.map_map]
    apply List.map_congr_left
    intro c hc
    have h := (children_bounds n _ 0 c hc).2
    simp [preorder, show c ≠ n+1 by omega]
  change (if (t (Fin.last n)).val = 0 then
    (n+1) :: children n (fun v => t v.castSucc) 0
    else children n (fun v => t v.castSucc) 0).map (preorder (n+1) t) = _
  split
  · rename_i hp
    rw [List.map_cons, show preorder (n+1) t (n+1) = [n+1] by simp [preorder], hm]
    congr 1
    conv_rhs => rw [← List.map_id (componentWords n (fun v => t v.castSucc))]
    apply List.map_congr_left
    intro w hw
    apply splice_of_not_mem
    intro hz
    have hpos := List.left_le_of_mem_range' ((components_perm n _).mem_iff.mp
      (List.mem_flatten.mpr ⟨w,hw,hz⟩))
    omega
  · exact hm

private theorem cycles_succ (n : ℕ) (t : ParentCode (n+1)) :
    cycleProduct (componentWords (n+1) t) =
      if (t (Fin.last n)).val = 0 then cycleProduct (componentWords n (fun v => t v.castSucc))
      else cycleProduct (componentWords n (fun v => t v.castSucc)) *
        Equiv.swap (t (Fin.last n)).val (n+1) := by
  rw [components_succ]
  split
  · simp [cycleProduct]
  · rename_i hp
    apply cycleProduct_splice
    · exact (components_perm n _).nodup_iff.mpr List.nodup_range'
    · rw [(components_perm n _).mem_iff]
      have ht : (t (Fin.last n)).val < n+1 := by simpa only [Fin.val_last] using (t (Fin.last n)).isLt
      simp only [List.mem_range']
      simp only [Fin.val_last] at *
      exact ⟨(t (Fin.last n)).val-1, by omega, by omega⟩
    · rw [(components_perm n _).mem_iff]
      simp; omega

/-- Literal DFS cycles on positive labels agree with insertion on Fin n.
Singleton words are included in the cycle product. -/
private theorem cycles_code (n : ℕ) (t : ParentCode n) (v : Fin n) :
    cycleProduct (componentWords n t) (v.val+1) = (codeEquiv n t v).val+1 := by
  induction n with
  | zero => exact Fin.elim0 v
  | succ n ih =>
    have hx : cycleProduct (componentWords n (fun v => t v.castSucc)) (n+1) = n+1 := by
      apply cycleProduct_fix
      rw [(components_perm n _).mem_iff]
      simp; omega
    rw [cycles_succ]
    change _ = (insertEquiv n (t (Fin.last n), codeEquiv n (fun v => t v.castSucc)) v).val+1
    refine Fin.cases ?_ (fun p => ?_) (t (Fin.last n))
    · simp only [Fin.val_zero, ite_eq_left rfl]
      refine Fin.lastCases ?_ (fun j => ?_) v
      · simpa [insert_apply] using hx
      · simpa [insert_apply] using ih _ j
    · have hp0 : (p.succ).val ≠ 0 := by simp
      simp only [hp0, ite_false]
      refine Fin.lastCases ?_ (fun j => ?_) v
      · simpa [Equiv.Perm.mul_apply, insert_apply] using ih _ p
      · by_cases hj : j = p
        · subst j
          simp [Equiv.Perm.mul_apply, insert_apply, hx]
        · have hne : j.val+1 ≠ p.val+1 := by intro h; exact hj (Fin.ext (by omega))
          have hn : j.val+1 ≠ n+1 := by have := j.isLt; omega
          have hs : Equiv.swap (p.val+1) (n+1) (j.val+1) = j.val+1 :=
            Equiv.swap_apply_of_ne_of_ne hne hn
          simpa [Equiv.Perm.mul_apply, insert_apply, hs, Equiv.swap_apply_of_ne_of_ne, hj, Fin.val_succ, Fin.val_castSucc]
            using ih (fun v => t v.castSucc) j


/-- A literal directed cycle decomposition, including singleton cycles.
Each word starts at its unique minimum, partitions the positive labels, and
sends every letter to the next letter with the final letter returning first. -/
def CycleWords (n : ℕ) (s : Perm (Fin n)) (ws : List (List ℕ)) : Prop :=
  ws.flatten.Perm (List.range' 1 n) ∧
  (∀ w ∈ ws, ∃ r tail, w = r :: tail ∧ ∀ x ∈ tail, r < x) ∧
  ∀ w ∈ ws, ∀ v : Fin n, ∀ hv : v.val+1 ∈ w,
    (s v).val+1 = w.next (v.val+1) hv

private theorem cycleProduct_member (ws : List (List ℕ)) (hd : ws.flatten.Nodup)
    (w : List ℕ) (hw : w ∈ ws) (v : ℕ) (hv : v ∈ w) :
    cycleProduct ws v = w.formPerm v := by
  induction ws with
  | nil => simp at hw
  | cons u us ih =>
    have hn : (u ++ us.flatten).Nodup := hd
    have hs := (List.nodup_append'.mp hn).2.1
    have hdis := (List.nodup_append'.mp hn).2.2
    rcases List.mem_cons.mp hw with rfl | hw
    · have hx : v ∉ us.flatten := fun h => hdis hv h
      change w.formPerm (cycleProduct us v) = _
      rw [cycleProduct_fix us v hx]
    · change u.formPerm (cycleProduct us v) = _
      rw [ih hs hw]
      apply List.formPerm_apply_of_notMem
      intro h
      exact hdis h (List.mem_flatten.mpr ⟨w,hw,List.formPerm_apply_mem_of_mem hv⟩)

private theorem components_minimum (n : ℕ) (t : ParentCode n)
    (w : List ℕ) (hw : w ∈ componentWords n t) :
    ∃ r tail, w = r :: tail ∧ ∀ x ∈ tail, r < x := by
  obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hw
  have hb := children_bounds n t 0 r hr
  refine ⟨r, (children n t r).flatMap (preorder n t), preorder_dfs n t r hb.2, ?_⟩
  intro x hx
  have hnd := preorder_nodup n t r hb.2
  rw [preorder_dfs n t r hb.2, List.nodup_cons] at hnd
  have hne : x ≠ r := fun h => hnd.1 (h ▸ hx)
  have hm : x ∈ preorder n t r := by rw [preorder_dfs n t r hb.2]; simp [hx]
  have hle := (preorder_bounds n t r x hb.2 hm).1
  omega

private theorem components_cycles (n : ℕ) (t : ParentCode n) :
    CycleWords n (codeEquiv n t) (componentWords n t) := by
  have hp := components_perm n t
  have hd := hp.nodup_iff.mpr List.nodup_range'
  refine ⟨hp, components_minimum n t, ?_⟩
  intro w hw v hv
  rw [← cycles_code n t v, cycleProduct_member _ hd w hw _ hv]
  exact List.formPerm_apply_mem_eq_next ((List.nodup_flatten.mp hd).1 w hw) _ hv

/-- Last entry smaller than v, with 0 for an empty admissible prefix. -/
def previousSmaller (v : ℕ) (letters : List ℕ) (initial : ℕ := 0) : ℕ :=
  letters.foldl (fun a y => if y < v then y else a) initial

/-- The rightmost smaller letter strictly before v in a word. -/
def wordParent (w : List ℕ) (v : ℕ) : ℕ :=
  previousSmaller v (w.takeWhile (fun y => y ≠ v))

/-- Locate v's cycle word and reconstruct its parent; cycle minima receive 0. -/
def parentLookup : List (List ℕ) → ℕ → ℕ
  | [], _ => 0
  | w :: ws, v => if v ∈ w then wordParent w v else parentLookup ws v

private theorem previousSmaller_bound (v : ℕ) (l : List ℕ) (a : ℕ) (ha : a < v) :
    previousSmaller v l a < v := by
  induction l generalizing a with
  | nil => exact ha
  | cons y ys ih =>
    simp only [previousSmaller, List.foldl_cons]
    apply ih
    split <;> assumption

private theorem parentLookup_bound (ws : List (List ℕ)) (v : ℕ) (hv : 0 < v) :
    parentLookup ws v < v := by
  induction ws with
  | nil => exact hv
  | cons w ws ih =>
    simp only [parentLookup]
    split
    · exact previousSmaller_bound v _ 0 hv
    · exact ih

private theorem takeWhile_splice (p x v : ℕ) (l : List ℕ) (h : x ≠ v) :
    (splice p x l).takeWhile (fun y => y ≠ v) =
      splice p x (l.takeWhile (fun y => y ≠ v)) := by
  induction l with
  | nil => rfl
  | cons y ys ih =>
    by_cases hyp : y = p
    · subst y
      by_cases hpv : p = v
      · subst p
        simp [splice]
      · simp only [splice, ite_eq_left rfl, List.takeWhile_cons,
          decide_eq_true_eq, hpv, h, not_false_eq_true, ite_true, ih]
        simp [splice,hpv,h]
    · by_cases hyv : y = v
      · subst y
        simp [splice,hyp]
      · simp only [splice, ite_eq_right hyp, List.takeWhile_cons,
          decide_eq_true_eq, hyv, not_false_eq_true, ite_true, ih]
        simp [splice,hyp,hyv]


private theorem previousSmaller_splice (p x v : ℕ) (l : List ℕ) (a : ℕ) (hv : v ≤ x) :
    previousSmaller v (splice p x l) a = previousSmaller v l a := by
  induction l generalizing a with
  | nil => rfl
  | cons y ys ih =>
    by_cases h : y = p
    · rw [splice, ite_eq_left h]
      change previousSmaller v (splice p x ys) (if x < v then x else (if y < v then y else a)) = _
      rw [ite_eq_right (by omega : ¬ x < v)]
      exact ih _
    · rw [splice, ite_eq_right h]
      exact ih (if y < v then y else a)

private theorem wordParent_splice_old (p x v : ℕ) (l : List ℕ) (hv : v < x) :
    wordParent (splice p x l) v = wordParent l v := by
  unfold wordParent
  rw [takeWhile_splice p x v l (by omega), previousSmaller_splice p x v _ _ hv.le]

private theorem lookup_splice_old (p x v : ℕ) (ws : List (List ℕ)) (hv : v < x) :
    parentLookup (ws.map (splice p x)) v = parentLookup ws v := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [List.map_cons, parentLookup, mem_splice, show v ≠ x by omega,
      false_and, or_false]
    split
    · exact wordParent_splice_old p x v w hv
    · exact ih

private theorem previousSmaller_splice_new (p x : ℕ) (l : List ℕ)
    (hp : p ∈ l) (hx : ∀ y ∈ l, y < x) (a : ℕ) :
    previousSmaller x ((splice p x l).takeWhile (fun y => y ≠ x)) a = p := by
  induction l generalizing a with
  | nil => simp at hp
  | cons y ys ih =>
    have hy : y < x := hx y (by simp)
    have hys : ∀ z ∈ ys, z < x := fun z hz => hx z (by simp [hz])
    by_cases h : y = p
    · subst y
      simp [splice,previousSmaller,hy,show p ≠ x by omega]
    · have hpt : p ∈ ys := (List.mem_cons.mp hp).resolve_left (Ne.symm h)
      simpa [splice,h,previousSmaller,hy,show y ≠ x by omega] using ih hpt hys y

private theorem lookup_splice_new (p x : ℕ) (ws : List (List ℕ))
    (hp : p ∈ ws.flatten) (hx : ∀ y ∈ ws.flatten, y < x) :
    parentLookup (ws.map (splice p x)) x = p := by
  induction ws with
  | nil => simp at hp
  | cons w ws ih =>
    have hxw : ∀ y ∈ w, y < x := fun y hy => hx y (by simp [hy])
    have hxs : ∀ y ∈ ws.flatten, y < x := fun y hy => hx y (by simp [hy])
    have hxn : x ∉ w := fun h => (hxw x h).false
    simp only [List.map_cons, parentLookup, mem_splice, true_and, true_or]
    by_cases hpw : p ∈ w
    · rw [ite_eq_left (by simpa [hxn] using hpw)]
      exact previousSmaller_splice_new p x w hpw hxw 0
    · have hps : p ∈ ws.flatten := by simpa [hpw] using hp
      rw [ite_eq_right (by simpa [hxn] using hpw)]
      exact ih hps hxs

private theorem lookup_components (n : ℕ) (t : ParentCode n) (v : Fin n) :
    parentLookup (componentWords n t) (v.val+1) = (t v).val := by
  induction n with
  | zero => exact Fin.elim0 v
  | succ n ih =>
    rw [components_succ]
    have hbounds : ∀ y ∈ (componentWords n (fun v => t v.castSucc)).flatten, y < n+1 := by
      intro y hy
      obtain ⟨i,hi,heq⟩ := List.mem_range'.mp ((components_perm n _).mem_iff.mp hy)
      omega
    refine Fin.lastCases ?_ (fun j => ?_) v
    · simp only [Fin.val_last]
      split
      · rename_i hp
        simp [parentLookup,wordParent,previousSmaller,hp]
      · rename_i hp
        apply lookup_splice_new
        · rw [(components_perm n _).mem_iff]
          have ht : (t (Fin.last n)).val < n+1 := by simpa only [Fin.val_last] using (t (Fin.last n)).isLt
          simp only [List.mem_range']
          simp only [Fin.val_last] at *
          exact ⟨(t (Fin.last n)).val-1, by omega, by omega⟩
        · exact hbounds
    · simp only [Fin.val_castSucc]
      split
      · have hn : j.val+1 ≠ n+1 := by have := j.isLt; omega
        simpa [parentLookup,hn, show j.val ≠ n by omega] using ih (fun v => t v.castSucc) j
      · rw [lookup_splice_old _ _ _ _ (by have := j.isLt; omega)]
        exact ih _ j

/-- Perform the prescribed rightmost-smaller attachment on cycle words. -/
def reconstructCode (n : ℕ) (ws : List (List ℕ)) : ParentCode n := fun v =>
  ⟨parentLookup ws (v.val+1), parentLookup_bound ws (v.val+1) (by omega)⟩

private theorem reconstruct_components (n : ℕ) (t : ParentCode n) :
    reconstructCode n (componentWords n t) = t := by
  funext v
  apply Fin.ext
  exact lookup_components n t v

/-- Minimum-first directed cycles, computed using insertion's inverse.
The cycle and partition certificates below verify this implementation. -/
def permutationWords {n : ℕ} (s : Perm (Fin n)) : List (List ℕ) :=
  componentWords n ((codeEquiv n).symm s)

/-- Restore the native root and all reconstructed parent incidences. -/
noncomputable def reconstructTree {n : ℕ} (s : Perm (Fin n)) : NativeTree n :=
  (IntervalForestBasic.treeEquivCode n).symm (reconstructCode n (permutationWords s))

private theorem reconstructTree_eq {n : ℕ} (s : Perm (Fin n)) :
    reconstructTree s = (nativeEquiv n).symm s := by
  simp only [reconstructTree, permutationWords, reconstruct_components]
  rfl

/-- An explicit certificate for the last smaller entry, with zero as the
sentinel when the preceding segment has no smaller entry. -/
def RightmostSmaller (v : ℕ) (letters : List ℕ) (p : ℕ) : Prop :=
  (p = 0 ∧ ∀ x ∈ letters, v ≤ x) ∨
  ∃ before after, letters = before ++ p :: after ∧ p < v ∧ ∀ x ∈ after, v ≤ x

private theorem previousSmaller_spec (v : ℕ) (letters : List ℕ) :
    RightmostSmaller v letters (previousSmaller v letters) := by
  induction letters using List.reverseRecOn with
  | nil => exact Or.inl ⟨rfl, by simp⟩
  | append_singleton letters y ih =>
    have he : previousSmaller v (letters ++ [y]) =
        if y < v then y else previousSmaller v letters := by
      simp [previousSmaller, List.foldl_append]
    rw [he]
    by_cases hy : y < v
    · rw [ite_eq_left hy]
      exact Or.inr ⟨letters, [], by simp, hy, by simp⟩
    · rw [ite_eq_right hy]
      rcases ih with ⟨hp,hall⟩ | ⟨before,after,heq,hp,hall⟩
      · refine Or.inl ⟨hp, ?_⟩
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact hall x hx
        · have hxy : x = y := by simpa using hx
          omega
      · refine Or.inr ⟨before,after ++ [y], ?_, hp, ?_⟩
        · calc
            letters ++ [y] = (before ++ previousSmaller v letters :: after) ++ [y] :=
              congrArg (fun l => l ++ [y]) heq
            _ = before ++ previousSmaller v letters :: (after ++ [y]) := by
              rw [List.append_assoc]
              rfl
        · intro x hx
          rcases List.mem_append.mp hx with hx | hx
          · exact hall x hx
          · have hxy : x = y := by simpa using hx
            omega


private theorem parentLookup_member (ws : List (List ℕ)) (hd : ws.flatten.Nodup)
    (w : List ℕ) (hw : w ∈ ws) (v : ℕ) (hv : v ∈ w) :
    parentLookup ws v = wordParent w v := by
  induction ws with
  | nil => simp at hw
  | cons u us ih =>
    have hn : (u ++ us.flatten).Nodup := hd
    have hs := (List.nodup_append'.mp hn).2.1
    have hdis := (List.nodup_append'.mp hn).2.2
    rcases List.mem_cons.mp hw with rfl | hw
    · simp [parentLookup,hv]
    · have hnot : v ∉ u := fun h => hdis h (List.mem_flatten.mpr ⟨w,hw,hv⟩)
      simp only [parentLookup, ite_eq_right hnot]
      exact ih hs hw

/-- The fixed forward map. The result theorem identifies the intermediate
permutation with literal decreasing-child depth-first component cycles. -/
noncomputable def F {n : ℕ} (t : NativeTree n) : Perm (Fin n) :=
  dual (nativeEquiv n t)

/-- The fixed reverse map: certified minimum-first cycles of D, followed by
rightmost-smaller attachments and restoration of the native zero root. -/
noncomputable def H {n : ℕ} (s : Perm (Fin n)) : NativeTree n :=
  reconstructTree (dual s)

/-- Operational forward specification on the existing native parent carrier.
The child list is derived from actual parent incidence, strictly decreases,
and satisfies the literal root-first DFS equation. -/
def ForwardSpec {n : ℕ} (t : NativeTree n) (s : Perm (Fin n)) : Prop :=
  let code := IntervalForestBasic.treeEquivCode n t
  (∀ r c, c ∈ children n code r ↔
    ∃ v : Fin n, v.val+1 = c ∧ (t.val.parent v.succ).map Fin.val = some r) ∧
  (∀ r, (children n code r).Pairwise (fun x y => y < x)) ∧
  (∀ r ≤ n, preorder n code r = r :: (children n code r).flatMap (preorder n code)) ∧
  CycleWords n (nativeEquiv n t) (componentWords n code) ∧
  s = dual (nativeEquiv n t) ∧
  ∀ i : Fin n,
    ((reflectPositions n i).val+1 = if i.val+1 < n then n-(i.val+1) else n) ∧
    (s i).val+1 = n+1-((nativeEquiv n t (reflectPositions n i)).val+1)

/-- Operational reverse specification. All cycle words, including singleton
cycles, are minimum-first in the supplied cyclic direction; every resulting
native parent is the rightmost preceding smaller letter, or zero. -/
def ReverseSpec {n : ℕ} (s : Perm (Fin n)) (t : NativeTree n) : Prop :=
  CycleWords n (dual s) (permutationWords (dual s)) ∧
  (∀ v : Fin n, (t.val.parent v.succ).map Fin.val =
    some (parentLookup (permutationWords (dual s)) (v.val+1))) ∧
  (∀ w ∈ permutationWords (dual s), ∀ v ∈ w,
    RightmostSmaller v (w.takeWhile (fun y => y ≠ v))
      (parentLookup (permutationWords (dual s)) v)) ∧
  t.val.parent 0 = none

private theorem forward_spec {n : ℕ} (t : NativeTree n) : ForwardSpec t (F t) := by
  let code := IntervalForestBasic.treeEquivCode n t
  have hp (v : Fin n) : (t.val.parent v.succ).map Fin.val = some (code v).val := by
    simpa only [code, Equiv.symm_apply_apply] using native_parent_code code v
  refine ⟨?_, children_decreasing n code, preorder_dfs n code, ?_, rfl, ?_⟩
  · intro r c
    rw [children_incidence]
    simp only [hp, Option.some.injEq]
    rfl
  · exact components_cycles n code
  · exact dual_formula (nativeEquiv n t)

private theorem reverse_spec {n : ℕ} (s : Perm (Fin n)) : ReverseSpec s (H s) := by
  have hc : CycleWords n (dual s) (permutationWords (dual s)) := by
    simpa only [permutationWords, Equiv.apply_symm_apply] using
      components_cycles n ((codeEquiv n).symm (dual s))
  refine ⟨hc, ?_, ?_, IntervalForestBasic.IntervalForest.parent_zero _⟩
  · intro v
    exact native_parent_code (reconstructCode n (permutationWords (dual s))) v
  · intro w hw v hv
    have hd := hc.1.nodup_iff.mpr List.nodup_range'
    rw [parentLookup_member _ hd w hw v hv]
    exact previousSmaller_spec v _

/-- The entire fixed Testart tree/permutation bijection, for every positive
parameter pair, without bounds, plane order, binary restriction or exclusion
of fixed points. Its operational specifications certify the fixed maps. -/
theorem result (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    (∀ t : NativeTree (a+b-1), ForwardSpec t (F t)) ∧
    (∀ s : Perm (Fin (a+b-1)), ReverseSpec s (H s)) ∧
    (∀ t : TreeClass a b, ∀ i, i < F t.val i ↔ i.val+1 < b) ∧
    (∀ s : PermClass a b, ∀ v, Internal (H s.val) v ↔ v.val < a) ∧
    (∀ t : TreeClass a b, H (F t.val) = t.val) ∧
    (∀ s : PermClass a b, F (H s.val) = s.val) := by
  let e := insertionClassEquiv a b ha hb
  have hf (t : TreeClass a b) : F t.val = (e t).val := rfl
  have hh (s : PermClass a b) : H s.val = (e.symm s).val :=
    reconstructTree_eq (dual s.val)
  refine ⟨forward_spec, reverse_spec, ?_, ?_, ?_, ?_⟩
  · intro t
    rw [hf]
    exact (e t).property
  · intro s
    rw [hh]
    exact (e.symm s).property
  · intro t
    rw [hf, hh]
    exact congrArg Subtype.val (e.symm_apply_apply t)
  · intro s
    rw [hh, hf]
    exact congrArg Subtype.val (e.apply_symm_apply s)


end D5.S3.Combinatorics.PriorityLattice.TestartTraversal
