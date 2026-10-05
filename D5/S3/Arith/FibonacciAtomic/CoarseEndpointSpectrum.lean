/- GID: D5/S3/Arith/FibonacciAtomic/CoarseEndpointSpectrum
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/CoarseEndpointSpectrum
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: The exact coarse endpoint spectrum of the nested compensation family. -/

import D5.S3.Arith.FibonacciAtomic.CoarseEndpointPeeling
import D5.S3.Arith.FibonacciAtomic.Scale38LeafFrontierResponse

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.CoarseEndpointSpectrum

open GenealogicalFiberTransport (Source)
open ActualTreeReadoutAcquisition (Address Reply readout leaves Strategy cost paid terminal)
open ActualImageSevenLeafSeparation (leafLabel leafAddresses seven_leaf_separation)
open ActualCoarseReadoutHistory (kappa CoarseObservable)
open CoarseEndpointPeeling (Peels)
open Scale38LeafFrontierResponse (LeafRow labelledFrontier)
open Scale38NestedCompensation (family query)
open D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization (fiber)

local notation "Index" => fun k : Nat => Unit ⊕ (Fin k ⊕ Fin k)
local notation "back" => fun t : Nat =>
  true :: false :: (List.replicate t true ++ [false,false,true])
local notation "read" => fun {m : Nat} (F : Fin m → Source) (q : Address) (i : Fin m) =>
  leafLabel (F i) q

/-- The literal small-family routes, with zero-based query indices. -/
def endpointRoute (k : Nat) (Z : Index k) : List Address :=
  if k = 1 then
    match Z with
    | .inl _ => [query 0, query 1]
    | .inr (.inl _) => [query 1, [true,true]]
    | .inr (.inr _) => [query 0, back 1]
  else
    match Z with
    | .inl _ => [query 0, back 0, query 1, query 2]
    | .inr (.inl _) => []
    | .inr (.inr i) => if i.val = 0 then [query 0, back 0, back 1, back 2]
        else [query 0, back 0, query 1, back 1]

/-- All coarse endpoint targets, together with their safe literal lists and
actual strategies whose paid sets contain precisely one nonleaf at each exit. -/
theorem result (k : Nat) (hk : 1 ≤ k) :
    let m := Fintype.card (Index k)
    let e := Fintype.equivFin (Index k)
    let F := family k ∘ e.symm
    ∀ z : Fin m,
      ((∃ qs : List Address, Peels F z Finset.univ qs) ↔
        k = 1 ∨ k = 2 ∧
          (e.symm z = .inl () ∨ ∃ i, e.symm z = .inr (.inr i))) ∧
      ((k = 1 ∨ k = 2 ∧
          (e.symm z = .inl () ∨ ∃ i, e.symm z = .inr (.inr i))) →
        Peels F z Finset.univ (endpointRoute k (e.symm z)) ∧
        ∃ π : Strategy, CoarseObservable π.policy ∧
          (∀ i, cost π (F i) = 3*k+14 - (if i = z then 1 else 0)) ∧
          paid (terminal π (F z)).1 = leafAddresses (F z) ∧
          ∀ i, i ≠ z → ∃ q,
            (endpointRoute k (e.symm z)).find?
              (fun a => decide (leafLabel (F i) a = none)) = some q ∧
            q ∉ leafAddresses (F i) ∧
            paid (terminal π (F i)).1 = leafAddresses (F i) ∪ {q}) := by
  classical
  dsimp only
  let m := Fintype.card (Index k)
  let e : Index k ≃ Fin m := Fintype.equivFin _
  let F : Fin m → Source := family k ∘ e.symm
  have foundation := Scale38NestedCompensation.result k hk
  have table := Scale38LeafFrontierResponse.result k hk
  have coverage := table.2.2.2.2.2.2.2.2.2.2.2.2.1
  have responses := table.2.2.2.2.2.2.2.2.2.2.2.2.2
  have matching (q : Address) (i z : Fin m)
      (hi : leafLabel (F i) q ≠ none) (hz : leafLabel (F z) q ≠ none) :
      leafLabel (F i) q = leafLabel (F z) q := by
    obtain ⟨a,ha⟩ := Option.ne_none_iff_exists'.mp hi
    obtain ⟨b,hb⟩ := Option.ne_none_iff_exists'.mp hz
    rw [ha,hb]
    exact congrArg some (((seven_leaf_separation.2.1 (F i) (F z)).2.2.mp
      (foundation.2.2.2.1 (e.symm i) (e.symm z))) q a b ha hb)
  have rows (Z : Index k) (q : Address) (leaf : q ∈ leaves (family k Z)) :
      ∃ (b : Bool) (r : LeafRow k), r.target = Z ∧ (q,b) ∈ r.block ∧
        leafLabel (family k Z) q = some b ∧
        ∀ U : Index k, leafLabel (family k U) q =
          if U = Z then some b else kappa (r.reply U b) := by
    obtain ⟨b,hb⟩ := ((seven_leaf_separation.1 (family k Z)).2 q).mp
      (List.mem_toFinset.mpr leaf)
    obtain ⟨r,target,block⟩ := coverage Z q b hb
    refine ⟨b,r,target,block,hb,?_⟩
    intro U
    by_cases eq : U = Z
    · subst U; simpa only [if_true] using hb
    · rw [if_neg eq]
      change kappa (readout q (family k U)) = _
      rw [responses r U (by rw [target]; exact eq) q b block]
  have obstruction (Z : Index k) (K : Index k → Prop)
      (outside : ∃ U, K U ∧ U ≠ Z)
      (blocked : ∀ q ∈ leaves (family k Z),
        (∀ U, K U → leafLabel (family k U) q ≠ none) ∨
        ∃ U V, K U ∧ K V ∧ U ≠ V ∧
          leafLabel (family k U) q = none ∧ leafLabel (family k V) q = none) :
      ∀ S qs, (∀ U, K U → e U ∈ S) → ¬ Peels F (e Z) S qs := by
    intro S qs
    induction qs generalizing S with
    | nil =>
      intro sub hp
      obtain ⟨U,hu,ne⟩ := outside
      exact ne (e.injective (Finset.mem_singleton.mp (hp (sub U hu))))
    | cons q qs ih =>
      rintro sub ⟨leaf,count,tail⟩
      have leaf' : q ∈ leaves (family k Z) := by
        simpa only [F,Function.comp_apply,e.symm_apply_apply] using leaf
      rcases blocked q leaf' with all | ⟨U,V,hu,hv,ne,nu,nv⟩
      · apply ih _ ?_ tail
        intro U hu
        have target : leafLabel (F (e Z)) q ≠ none := by
          obtain ⟨b,hb⟩ := ((seven_leaf_separation.1 (F (e Z))).2 q).mp
            (List.mem_toFinset.mpr leaf)
          rw [hb]; exact Option.some_ne_none _
        have nonleaf : leafLabel (F (e U)) q ≠ none := by
          simpa only [F,Function.comp_apply,e.symm_apply_apply] using all U hu
        exact (by
          simp only [fiber,Finset.mem_filter]
          exact ⟨sub U hu,matching q (e U) (e Z) nonleaf target⟩)
      · apply ne
        apply e.injective
        apply Finset.card_le_one.mp count
        · simp only [fiber,Finset.mem_filter]
          exact ⟨sub U hu,by simpa only [F,Function.comp_apply,e.symm_apply_apply] using nu⟩
        · simp only [fiber,Finset.mem_filter]
          exact ⟨sub V hv,by simpa only [F,Function.comp_apply,e.symm_apply_apply] using nv⟩
  have exclude_later_x (j : Fin k) (later : 1 ≤ j.val) :
      ¬ ∃ qs, Peels F (e (.inr (.inl j))) Finset.univ qs := by
    let a : Fin k := ⟨j.val-1,by omega⟩
    let U : Index k := .inr (.inr a)
    let V : Index k := .inr (.inr j)
    have distinct : U ≠ V := by
      intro eq
      have vals := congrArg (fun W : Index k =>
        match W with | .inr (.inr i) => i.val | _ => 0) eq
      dsimp [U,V,a] at vals
      omega
    have blocked : ∀ q ∈ leaves (family k (.inr (.inl j))),
        (∀ W, W = U ∨ W = V → leafLabel (family k W) q ≠ none) ∨
        ∃ W W', (W = U ∨ W = V) ∧ (W' = U ∨ W' = V) ∧ W ≠ W' ∧
          leafLabel (family k W) q = none ∧ leafLabel (family k W') q = none := by
      intro q leaf
      obtain ⟨b,r,target,_,_,report⟩ := rows (.inr (.inl j)) q leaf
      have same : leafLabel (family k U) q = leafLabel (family k V) q := by
        rw [report U,report V]
        cases r with
        | xSlot j' t different =>
          simp only [LeafRow.target,Sum.inr.injEq,Sum.inl.injEq] at target
          subst j'
          have lt : (a.val < t.val) = (j.val < t.val) := by
            dsimp [a]
            apply propext
            have ne : t.val ≠ j.val := fun h => different (Fin.ext h)
            omega
          simp [U,V,LeafRow.reply,lt]
        | xExceptional j' => simp [U,V,LeafRow.reply]
        | xTail j' => simp [U,V,LeafRow.reply]
        | xRight j' => simp [U,V,LeafRow.reply]
        | pSlot t => simp [LeafRow.target] at target
        | pTail => simp [LeafRow.target] at target
        | pOuter right => simp [LeafRow.target] at target
        | pInner => simp [LeafRow.target] at target
        | ySlot i t => simp [LeafRow.target] at target
        | yLeftTail i => simp [LeafRow.target] at target
        | yRightSlot i h => simp [LeafRow.target] at target
        | yRightTail i => simp [LeafRow.target] at target
        | yRightA i => simp [LeafRow.target] at target
      by_cases nonleaf : leafLabel (family k U) q = none
      · exact Or.inr ⟨U,V,Or.inl rfl,Or.inr rfl,distinct,nonleaf,
          same.symm.trans nonleaf⟩
      · refine Or.inl ?_
        intro W hw
        rcases hw with rfl | rfl
        · exact nonleaf
        · rw [← same]; exact nonleaf
    rintro ⟨qs,safe⟩
    exact obstruction (.inr (.inl j)) (fun W => W = U ∨ W = V)
      ⟨U,Or.inl rfl,by simp [U]⟩ blocked Finset.univ qs
      (fun _ _ => Finset.mem_univ _) safe
  have exclude_first_x (big : 2 ≤ k) :
      ¬ ∃ qs, Peels F (e (.inr (.inl ⟨0,by omega⟩))) Finset.univ qs := by
    let z : Fin k := ⟨0,by omega⟩
    let o : Fin k := ⟨1,by omega⟩
    have blocked : ∀ q ∈ leaves (family k (.inr (.inl z))),
        (∀ U : Index k, True → leafLabel (family k U) q ≠ none) ∨
        ∃ U V : Index k, True ∧ True ∧ U ≠ V ∧
          leafLabel (family k U) q = none ∧ leafLabel (family k V) q = none := by
      intro q leaf
      obtain ⟨b,r,target,_,_,report⟩ := rows (.inr (.inl z)) q leaf
      right
      cases r with
      | xSlot j t different =>
        simp only [LeafRow.target,Sum.inr.injEq,Sum.inl.injEq] at target
        subst j
        have positive : 0 < t.val := by
          have ne : t.val ≠ 0 := fun h => different (Fin.ext h)
          omega
        by_cases one : t.val = 1
        · refine ⟨.inr (.inl o),.inr (.inr z),trivial,trivial,by simp,?_,?_⟩
          · rw [report]; simp [LeafRow.reply,o,z,one,kappa]
          · rw [report]; simp [LeafRow.reply,z,positive,kappa]
        · have two : 1 < t.val := by omega
          refine ⟨.inr (.inr z),.inr (.inr o),trivial,trivial,?_,?_,?_⟩
          · simp [z,o,Fin.ext_iff]
          · rw [report]; simp [LeafRow.reply,z,positive,kappa]
          · rw [report]; simp [LeafRow.reply,o,z,two,kappa]
      | xExceptional j =>
        refine ⟨.inl (),.inr (.inr z),trivial,trivial,by simp,?_,?_⟩
        · rw [report]; simp [LeafRow.reply,kappa]
        · rw [report]; simp [LeafRow.reply,kappa]
      | xTail j =>
        refine ⟨.inr (.inr z),.inr (.inr o),trivial,trivial,?_,?_,?_⟩
        · simp [z,o,Fin.ext_iff]
        · rw [report]; simp [LeafRow.reply,kappa]
        · rw [report]; simp [LeafRow.reply,kappa]
      | xRight j =>
        refine ⟨.inl (),.inr (.inr z),trivial,trivial,by simp,?_,?_⟩
        · rw [report]; simp [LeafRow.reply,kappa]
        · rw [report]; simp [LeafRow.reply,kappa]
      | pSlot t => simp [LeafRow.target] at target
      | pTail => simp [LeafRow.target] at target
      | pOuter right => simp [LeafRow.target] at target
      | pInner => simp [LeafRow.target] at target
      | ySlot i t => simp [LeafRow.target] at target
      | yLeftTail i => simp [LeafRow.target] at target
      | yRightSlot i h => simp [LeafRow.target] at target
      | yRightTail i => simp [LeafRow.target] at target
      | yRightA i => simp [LeafRow.target] at target
    rintro ⟨qs,safe⟩
    exact obstruction (.inr (.inl z)) (fun _ => True)
      ⟨.inl (),trivial,by simp⟩ blocked Finset.univ qs
      (fun _ _ => Finset.mem_univ _) safe
  have exclude_large (big : 3 ≤ k) (Z : Index k)
      (kind : Z = .inl () ∨ ∃ i, Z = .inr (.inr i)) :
      ¬ ∃ qs, Peels F (e Z) Finset.univ qs := by
    let z : Fin k := ⟨0,by omega⟩
    let o : Fin k := ⟨1,by omega⟩
    let t : Fin k := ⟨2,by omega⟩
    let K : Index k → Prop := fun U => U ≠ .inr (.inl z)
    have blocked : ∀ q ∈ leaves (family k Z),
        (∀ U, K U → leafLabel (family k U) q ≠ none) ∨
        ∃ U V, K U ∧ K V ∧ U ≠ V ∧
          leafLabel (family k U) q = none ∧ leafLabel (family k V) q = none := by
      intro q leaf
      obtain ⟨b,r,target,_,_,report⟩ := rows Z q leaf
      rcases kind with rfl | ⟨i,rfl⟩
      · cases r with
        | pSlot s =>
          by_cases zero : s.val = 0
          · left
            intro U hu
            rw [report U]
            cases U with
            | inl u => cases u; simp
            | inr p => cases p with
              | inl j =>
                have ne : j.val ≠ 0 := by
                  intro eq
                  exact hu (congrArg (fun a : Fin k => Sum.inr (Sum.inl a))
                    (Fin.ext (by simpa only [z] using eq)))
                cases b <;> simp [LeafRow.reply,zero,ne,kappa]
              | inr j => simp [LeafRow.reply,zero,kappa]; cases b <;> simp
          · have pos : 0 < s.val := by omega
            right
            refine ⟨.inr (.inl s),.inr (.inr z),?_,by simp [K],by simp,?_,?_⟩
            · simp [K,Fin.ext_iff,z]; omega
            · rw [report]; simp [LeafRow.reply,kappa]
            · rw [report]; simp [LeafRow.reply,z,pos,kappa]
        | pTail =>
          right
          refine ⟨.inr (.inr z),.inr (.inr o),by simp [K],by simp [K],?_,?_,?_⟩
          · simp [z,o,Fin.ext_iff]
          · rw [report]; simp [LeafRow.reply,kappa]
          · rw [report]; simp [LeafRow.reply,kappa]
        | pOuter side =>
          right
          refine ⟨.inr (.inl o),.inr (.inl t),?_,?_,?_,?_,?_⟩
          · simp [K,z,o,Fin.ext_iff]
          · simp [K,z,t,Fin.ext_iff]
          · simp [o,t,Fin.ext_iff]
          · rw [report]; simp [LeafRow.reply,kappa]
          · rw [report]; simp [LeafRow.reply,kappa]
        | pInner =>
          right
          refine ⟨.inr (.inl o),.inr (.inl t),?_,?_,?_,?_,?_⟩
          · simp [K,z,o,Fin.ext_iff]
          · simp [K,z,t,Fin.ext_iff]
          · simp [o,t,Fin.ext_iff]
          · rw [report]; simp [LeafRow.reply,kappa]
          · rw [report]; simp [LeafRow.reply,kappa]
        | xSlot j s different => simp [LeafRow.target] at target
        | xExceptional j => simp [LeafRow.target] at target
        | xTail j => simp [LeafRow.target] at target
        | xRight j => simp [LeafRow.target] at target
        | ySlot i s => simp [LeafRow.target] at target
        | yLeftTail i => simp [LeafRow.target] at target
        | yRightSlot i h => simp [LeafRow.target] at target
        | yRightTail i => simp [LeafRow.target] at target
        | yRightA i => simp [LeafRow.target] at target
      · cases r with
        | ySlot i' s =>
          simp only [LeafRow.target,Sum.inr.injEq,Sum.inr.injEq] at target
          subst i'
          by_cases zero : s.val = 0
          · left
            intro U hu
            rw [report U]
            cases U with
            | inl u => simp [LeafRow.reply,kappa]; cases b <;> simp
            | inr p => cases p with
              | inl j =>
                have ne : j.val ≠ 0 := by
                  intro eq
                  exact hu (congrArg (fun a : Fin k => Sum.inr (Sum.inl a))
                    (Fin.ext (by simpa only [z] using eq)))
                cases b <;> simp [LeafRow.reply,zero,ne,kappa]
              | inr j =>
                by_cases eq : j = i
                · subst j; simp
                · simp [LeafRow.reply,zero,eq,kappa]; cases b <;> simp
          · have pos : 0 < s.val := by omega
            let a : Fin k := ⟨s.val,by omega⟩
            have nonzero : i.val ≠ 0 := by omega
            have ine : z ≠ i := by
              intro eq
              have vals := congrArg Fin.val eq
              dsimp [z] at vals
              omega
            right
            refine ⟨.inr (.inl a),.inr (.inr z),?_,by simp [K],by simp,?_,?_⟩
            · intro eq
              have eq' : a = z := Sum.inl.inj (Sum.inr.inj eq)
              have vals := congrArg Fin.val eq'
              change s.val = 0 at vals
              omega
            · rw [report]; simp [LeafRow.reply,a,kappa]
            · rw [report]; simp [LeafRow.reply,z,ine,pos,kappa]
        | yLeftTail i' =>
          right
          refine ⟨.inl (),.inr (.inl o),by simp [K],?_,by simp,?_,?_⟩
          · simp [K,z,o,Fin.ext_iff]
          · rw [report]; simp [LeafRow.reply,kappa]
          · rw [report]; simp [LeafRow.reply,kappa]
        | yRightSlot i' h =>
          right
          refine ⟨.inr (.inl o),.inr (.inl t),?_,?_,?_,?_,?_⟩
          · simp [K,z,o,Fin.ext_iff]
          · simp [K,z,t,Fin.ext_iff]
          · simp [o,t,Fin.ext_iff]
          · rw [report]; simp [LeafRow.reply,kappa]
          · rw [report]; simp [LeafRow.reply,kappa]
        | yRightTail i' =>
          right
          refine ⟨.inl (),.inr (.inl o),by simp [K],?_,by simp,?_,?_⟩
          · simp [K,z,o,Fin.ext_iff]
          · rw [report]; simp [LeafRow.reply,kappa]
          · rw [report]; simp [LeafRow.reply,kappa]
        | yRightA i' =>
          right
          refine ⟨.inr (.inl o),.inr (.inl t),?_,?_,?_,?_,?_⟩
          · simp [K,z,o,Fin.ext_iff]
          · simp [K,z,t,Fin.ext_iff]
          · simp [o,t,Fin.ext_iff]
          · rw [report]; simp [LeafRow.reply,kappa]
          · rw [report]; simp [LeafRow.reply,kappa]
        | pSlot s => simp [LeafRow.target] at target
        | pTail => simp [LeafRow.target] at target
        | pOuter side => simp [LeafRow.target] at target
        | pInner => simp [LeafRow.target] at target
        | xSlot j s different => simp [LeafRow.target] at target
        | xExceptional j => simp [LeafRow.target] at target
        | xTail j => simp [LeafRow.target] at target
        | xRight j => simp [LeafRow.target] at target
    have outside : ∃ U, K U ∧ U ≠ Z := by
      rcases kind with rfl | ⟨i,rfl⟩
      · exact ⟨.inr (.inl o),by simp [K,z,o,Fin.ext_iff],by simp⟩
      · exact ⟨.inl (),by simp [K],by simp⟩
    rintro ⟨qs,safe⟩
    exact obstruction Z K outside blocked Finset.univ qs
      (fun _ _ => Finset.mem_univ _) safe
  have small_one : ∀ (e1 : Index 1 ≃ Fin (Fintype.card (Index 1))) (Z : Index 1),
      Peels (family 1 ∘ e1.symm) (e1 Z) Finset.univ (endpointRoute 1 Z) := by
    intro e1 Z
    let F1 := family 1 ∘ e1.symm
    change Peels F1 (e1 Z) Finset.univ (endpointRoute 1 Z)
    have all : (Finset.univ : Finset (Fin (Fintype.card (Index 1)))) =
        Finset.univ.image e1 := (Finset.image_univ_of_surjective e1.surjective).symm
    have mapped (U : Index 1) : F1 (e1 U) = family 1 U := by
      change family 1 (e1.symm (e1 U)) = _
      rw [e1.symm_apply_apply]
    have bshape : FourExitRawEndpointSpectrum.B =
        .mul ActualImageSevenLeafSeparation.C ActualImageSevenLeafSeparation.A := rfl
    have count0 : (fiber (fun a v => leafLabel (F1 v) a)
        (Finset.univ.image e1) (query 0) none).card ≤ 1 := by
      have unique (v : Fin (Fintype.card (Index 1)))
          (hv : v ∈ fiber (fun a v => leafLabel (F1 v) a)
            (Finset.univ.image e1) (query 0) none) :
          v = e1 (.inr (.inl 0)) := by
        simp only [fiber,Finset.mem_filter] at hv
        obtain ⟨U,_,rfl⟩ := Finset.mem_image.mp hv.1
        have no := hv.2
        rw [mapped] at no
        rcases U with u | (j | i)
        all_goals first
          | (cases u)
          | (fin_cases j)
          | (fin_cases i)
        all_goals
          simp [family,query,FourExitRawEndpointSpectrum.comb,bshape,
            ActualImageSevenLeafSeparation.A,ActualImageSevenLeafSeparation.C,
            ActualImageSevenLeafSeparation.E,readout,leafLabel] at no ⊢
      exact Finset.card_le_one.mpr (fun v hv w hw => (unique v hv).trans (unique w hw).symm)
    have count1 : (fiber (fun a v => leafLabel (F1 v) a)
        (Finset.univ.image e1) (query 1) none).card ≤ 1 := by
      have unique (v : Fin (Fintype.card (Index 1)))
          (hv : v ∈ fiber (fun a v => leafLabel (F1 v) a)
            (Finset.univ.image e1) (query 1) none) :
          v = e1 (.inr (.inr 0)) := by
        simp only [fiber,Finset.mem_filter] at hv
        obtain ⟨U,_,rfl⟩ := Finset.mem_image.mp hv.1
        have no := hv.2
        rw [mapped] at no
        rcases U with u | (j | i)
        all_goals first
          | (cases u)
          | (fin_cases j)
          | (fin_cases i)
        all_goals
          simp [family,query,FourExitRawEndpointSpectrum.comb,bshape,
            ActualImageSevenLeafSeparation.A,ActualImageSevenLeafSeparation.C,
            ActualImageSevenLeafSeparation.E,readout,leafLabel] at no ⊢
      exact Finset.card_le_one.mpr (fun v hv w hw => (unique v hv).trans (unique w hw).symm)
    have enum : (Finset.univ : Finset (Index 1)) =
        {.inl (), .inr (.inl 0), .inr (.inr 0)} := by decide
    rw [all,enum]
    rw [enum] at count0 count1
    rcases Z with u | (j | i)
    all_goals first
      | (cases u)
      | (fin_cases j)
      | (fin_cases i)
    all_goals
        norm_num only [endpointRoute,Peels,count0,count1]
    all_goals
        simp [endpointRoute,Peels,fiber,Finset.filter,Finset.filter_image,Finset.filter_insert,
          Finset.filter_singleton,Multiset.filter_singleton,Multiset.filter_cons,mapped,family,query,FourExitRawEndpointSpectrum.comb,
          bshape,ActualImageSevenLeafSeparation.A,ActualImageSevenLeafSeparation.C,
          ActualImageSevenLeafSeparation.E,readout,leaves,leafLabel,e1.injective.eq_iff,
          Finset.card_image_of_injective _ e1.injective]
    all_goals exact Or.inr rfl
  have small_two : ∀ (e1 : Index 2 ≃ Fin (Fintype.card (Index 2))) (Z : Index 2),
      (Z = .inl () ∨ ∃ i, Z = .inr (.inr i)) →
      Peels (family 2 ∘ e1.symm) (e1 Z) Finset.univ (endpointRoute 2 Z) := by
    intro e1 Z kind
    let F1 := family 2 ∘ e1.symm
    change Peels F1 (e1 Z) Finset.univ (endpointRoute 2 Z)
    have all : (Finset.univ : Finset (Fin (Fintype.card (Index 2)))) =
        Finset.univ.image e1 := (Finset.image_univ_of_surjective e1.surjective).symm
    have mapped (U : Index 2) : F1 (e1 U) = family 2 U := by
      change family 2 (e1.symm (e1 U)) = _
      rw [e1.symm_apply_apply]
    have bshape : FourExitRawEndpointSpectrum.B =
        .mul ActualImageSevenLeafSeparation.C ActualImageSevenLeafSeparation.A := rfl
    have count0 : (fiber (fun a v => leafLabel (F1 v) a)
        (Finset.univ.image e1) (query 0) none).card ≤ 1 := by
      have unique (v : Fin (Fintype.card (Index 2)))
          (hv : v ∈ fiber (fun a v => leafLabel (F1 v) a)
            (Finset.univ.image e1) (query 0) none) :
          v = e1 (.inr (.inl 0)) := by
        simp only [fiber,Finset.mem_filter] at hv
        obtain ⟨U,_,rfl⟩ := Finset.mem_image.mp hv.1
        have no := hv.2
        rw [mapped] at no
        rcases U with u | (j | i)
        all_goals first
          | (cases u)
          | (fin_cases j)
          | (fin_cases i)
        all_goals
          simp [family,query,FourExitRawEndpointSpectrum.comb,bshape,
            ActualImageSevenLeafSeparation.A,ActualImageSevenLeafSeparation.C,
            ActualImageSevenLeafSeparation.E,readout,leafLabel] at no ⊢
      exact Finset.card_le_one.mpr (fun v hv w hw => (unique v hv).trans (unique w hw).symm)
    have enum : (Finset.univ : Finset (Index 2)) =
        {.inl (), .inr (.inl 0), .inr (.inl 1), .inr (.inr 0), .inr (.inr 1)} := by decide
    rw [all,enum]
    rw [enum] at count0
    rcases kind with rfl | ⟨i,rfl⟩
    all_goals try fin_cases i
    all_goals
        norm_num only [endpointRoute,Peels,count0]
    all_goals
        simp [endpointRoute,Peels,fiber,Finset.filter,Finset.filter_image,Finset.filter_insert,
          Finset.filter_singleton,Multiset.filter_singleton,Multiset.filter_cons,mapped,family,query,FourExitRawEndpointSpectrum.comb,
          bshape,ActualImageSevenLeafSeparation.A,ActualImageSevenLeafSeparation.C,
          ActualImageSevenLeafSeparation.E,readout,leaves,leafLabel,e1.injective.eq_iff,
          Finset.card_image_of_injective _ e1.injective]
    all_goals exact Or.inr rfl
  have small (Z : Index k)
      (allowed : k = 1 ∨ k = 2 ∧ (Z = .inl () ∨ ∃ i, Z = .inr (.inr i))) :
      Peels F (e Z) Finset.univ (endpointRoute k Z) := by
    rcases allowed with one | ⟨two,kind⟩
    · subst k; exact small_one e Z
    · subst k; exact small_two e Z kind
  have classification (Z : Index k) :
      (∃ qs, Peels F (e Z) Finset.univ qs) ↔
        k = 1 ∨ k = 2 ∧ (Z = .inl () ∨ ∃ i, Z = .inr (.inr i)) := by
    constructor
    · intro safe
      by_cases one : k = 1
      · exact Or.inl one
      have big : 2 ≤ k := by omega
      cases Z with
      | inl u =>
        cases u
        by_cases two : k = 2
        · exact Or.inr ⟨two,Or.inl rfl⟩
        · exact False.elim (exclude_large (by omega) (.inl ()) (Or.inl rfl) safe)
      | inr p => cases p with
        | inl j =>
          by_cases zero : j.val = 0
          · have eq : j = ⟨0,by omega⟩ := Fin.ext zero
            rw [eq] at safe
            exact False.elim (exclude_first_x big safe)
          · exact False.elim (exclude_later_x j (by omega) safe)
        | inr i =>
          by_cases two : k = 2
          · exact Or.inr ⟨two,Or.inr ⟨i,rfl⟩⟩
          · exact False.elim (exclude_large (by omega) (.inr (.inr i))
              (Or.inr ⟨i,rfl⟩) safe)
    · intro allowed
      exact ⟨endpointRoute k Z,small Z allowed⟩
  intro z
  obtain ⟨Z,rfl⟩ := e.surjective z
  have back_eq : (Fintype.equivFin (Index k)).symm (e Z) = Z := e.symm_apply_apply Z
  simp only [back_eq]
  refine ⟨classification Z,?_⟩
  intro allowed
  have safe := small Z allowed
  obtain ⟨π,_,observable,costs,target,exits⟩ :=
    (CoarseEndpointPeeling.result k hk (e Z)).2 (endpointRoute k Z) safe
  exact ⟨safe,π,observable,costs,target,exits⟩

end D5.S3.Arith.FibonacciAtomic.CoarseEndpointSpectrum
