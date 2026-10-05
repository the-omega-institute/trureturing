/- GID: D5/S3/Arith/FibonacciAtomic/Scale38RawEndpointSpectrum
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Full-frontier pairwise obstructions to raw endpoints in the nested compensation family. -/

import D5.S3.Arith.FibonacciAtomic.RawEndpointPeeling
import D5.S3.Arith.FibonacciAtomic.Scale38LeafFrontierResponse
import Mathlib.Data.Fin.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Scale38RawEndpointSpectrum

open GenealogicalFiberTransport (Source)
open ActualTreeReadoutAcquisition (Address Reply readout leaves vector)
open ActualJointResponseCostCore (survivors)
open ActualImageSevenLeafSeparation (leafLabel leafAddresses seven_leaf_separation)
open Scale38NestedCompensation (family)
open Scale38LeafFrontierResponse (LeafRow labelledFrontier)
open RawEndpointPeeling (Peels)

local notation "Index" => fun k : Nat => Unit ⊕ (Fin k ⊕ Fin k)

local notation "rawEndpoint" => fun (k : Nat) (z : Index k) =>
  ∃ qs : List Address,
    Peels (family k ∘ (Equiv.symm (Fintype.equivFin (Index k))))
      ((Fintype.equivFin (Index k)) z) Finset.univ qs

/-- Every enlarged slot after the first, and every contracted position before the last two,
has two competitors indistinguishable on its complete leaf frontier. None is a raw endpoint. -/
theorem result (k : Nat) (hk : 1 ≤ k) :
    (∀ j : Fin k, 1 ≤ j.val → ¬ rawEndpoint k (.inr (.inl j))) ∧
    (∀ i : Fin k, i.val + 3 ≤ k → ¬ rawEndpoint k (.inr (.inr i))) := by
  classical
  have no_peel_of_leaf_agreement (m : Nat) (F : Fin m → Source)
      (z i j : Fin m) (hiz : i ≠ z) (hjz : j ≠ z) (hij : i ≠ j)
      (agree : ∀ q, q ∈ leaves (F z) → readout q (F i) = readout q (F j))
      (compat : ∀ q, q ∈ leaves (F z) →
        readout q (F i) = readout q (F z) ∨
          readout q (F i) = .branch ∨ readout q (F i) = .absent) :
      ¬ ∃ qs : List Address, Peels F z Finset.univ qs := by
    rintro ⟨qs, hqs⟩
    have carry : ∀ (S : Finset (Fin m)) (qs : List Address),
        Peels F z S qs → i ∈ S → j ∈ S → False := by
      intro S rest
      induction rest generalizing S with
      | nil =>
          intro htail hi hj
          exact hiz (Finset.mem_singleton.mp (htail hi))
      | cons q rest ih =>
          intro htail hi hj
          rcases htail with ⟨hq, hbr, hab, hnext⟩
          rcases compat q hq with he | hbranch
          · exact ih _ hnext
              (Finset.mem_filter.mpr ⟨hi, he⟩)
              (Finset.mem_filter.mpr ⟨hj, (agree q hq).symm.trans he⟩)
          · rcases hbranch with hbranch | habsent
            · have hcard := hbr
              have hboth : i ∈ survivors S (vector F q) .branch ∧
                  j ∈ survivors S (vector F q) .branch := by
                constructor
                · exact Finset.mem_filter.mpr ⟨hi, by simpa [vector] using hbranch⟩
                · exact Finset.mem_filter.mpr ⟨hj, by
                    simpa [vector] using (agree q hq).symm.trans hbranch⟩
              exact (hij (Finset.card_le_one_iff.mp hcard hboth.1 hboth.2)).elim
            · have hcard := hab
              have hboth : i ∈ survivors S (vector F q) .absent ∧
                  j ∈ survivors S (vector F q) .absent := by
                constructor
                · exact Finset.mem_filter.mpr ⟨hi, by simpa [vector] using habsent⟩
                · exact Finset.mem_filter.mpr ⟨hj, by
                    simpa [vector] using (agree q hq).symm.trans habsent⟩
              exact (hij (Finset.card_le_one_iff.mp hcard hboth.1 hboth.2)).elim
    exact carry _ qs hqs (Finset.mem_univ i) (Finset.mem_univ j)
  
  have compatible_of_nonconflict {P Q : Source}
      (hconf : ActualImageSevenLeafSeparation.Nonconflict P Q) :
      ∀ a, a ∈ leaves P →
        readout a Q = readout a P ∨ readout a Q = .branch ∨ readout a Q = .absent := by
    intro a ha
    have haddr : a ∈ leafAddresses P := by simpa [leafAddresses] using ha
    obtain ⟨b, hb⟩ := (seven_leaf_separation.1 P).2 a |>.mp haddr
    have labels := (seven_leaf_separation.2.1 P Q).2.2.mp hconf a
    cases hp : readout a P <;> cases hq : readout a Q <;>
      simp only [leafLabel, hp, hq] at hb labels ⊢
    all_goals try { exact Or.inl rfl }
    all_goals try { exact Or.inr (Or.inl rfl) }
    all_goals try { exact Or.inr (Or.inr rfl) }
    all_goals simp_all
  
  have leaf_agreement_of_rows {k : Nat} (hk : 1 ≤ k)
      {Z U V : Index k} (hUZ : U ≠ Z) (hVZ : V ≠ Z)
      (row_eq : ∀ (r : LeafRow k), r.target = Z →
        ∀ (a : Address) (c : Bool), (a, c) ∈ r.block →
          r.reply U c = r.reply V c) :
      ∀ a, a ∈ leaves (family k Z) → readout a (family k U) = readout a (family k V) := by
    intro a ha
    have haddr : a ∈ leafAddresses (family k Z) := by
      simpa [leafAddresses] using ha
    have hsome := (seven_leaf_separation.1 (family k Z)).2 a |>.mp haddr
    obtain ⟨c, hc⟩ := hsome
    have hfront : (a,c) ∈ labelledFrontier (family k Z) := by
      simpa [labelledFrontier] using hc
    have H := Scale38LeafFrontierResponse.result k hk
    rcases H with ⟨_, _, _, _, _, _, _, _, _, _, _, _, cover, responses⟩
    obtain ⟨r, hr, hblock⟩ := cover Z a c hfront
    have hru := responses r U (by intro h; exact hUZ (by simpa [hr] using h)) a c hblock
    have hrv := responses r V (by intro h; exact hVZ (by simpa [hr] using h)) a c hblock
    exact hru.trans ((row_eq r hr a c hblock).trans hrv.symm)
  have excluded (Z U V : Index k) (hUZ : U ≠ Z) (hVZ : V ≠ Z) (hUV : U ≠ V)
      (rows : ∀ r : LeafRow k, r.target = Z →
        ∀ a c, (a,c) ∈ r.block → r.reply U c = r.reply V c) :
      ¬ rawEndpoint k Z := by
    let m := Fintype.card (Index k)
    let e : Index k ≃ Fin m := Fintype.equivFin (Index k)
    let F : Fin m → Source := family k ∘ e.symm
    have agreement := leaf_agreement_of_rows hk hUZ hVZ rows
    have nc := (Scale38NestedCompensation.result k hk).2.2.2.1 Z U
    have compatible := compatible_of_nonconflict nc
    change ¬ ∃ qs, Peels F (e Z) Finset.univ qs
    apply no_peel_of_leaf_agreement m F (e Z) (e U) (e V)
      (fun h => hUZ (e.injective h)) (fun h => hVZ (e.injective h))
      (fun h => hUV (e.injective h))
    · simpa only [F, Function.comp_apply, Equiv.symm_apply_apply] using agreement
    · simpa only [F, Function.comp_apply, Equiv.symm_apply_apply] using compatible
  constructor
  · intro j hj
    let u : Fin k := ⟨j.val - 1, by omega⟩
    let v : Fin k := j
    apply excluded (.inr (.inl j)) (.inr (.inr u)) (.inr (.inr v))
      (by simp) (by simp) (by
        intro h
        have huv : u = v := Sum.inr.inj (Sum.inr.inj h)
        have hv := congrArg Fin.val huv
        dsimp [u,v] at hv
        omega)
    intro r ht a c ha
    cases r with
    | xSlot j' t h =>
      have he : j' = j := by simpa only [LeafRow.target, Sum.inr.injEq, Sum.inl.injEq] using ht
      subst j'
      have hne : t.val ≠ j.val := fun he => h (Fin.ext he)
      simp only [LeafRow.reply]
      dsimp only [u,v]
      split_ifs <;> first | rfl | omega
    | xExceptional j' => rfl
    | xTail j' => rfl
    | xRight j' => rfl
    | pSlot t => simp [LeafRow.target] at ht
    | pTail => simp [LeafRow.target] at ht
    | pOuter b => simp [LeafRow.target] at ht
    | pInner => simp [LeafRow.target] at ht
    | ySlot i t => simp [LeafRow.target] at ht
    | yLeftTail i => simp [LeafRow.target] at ht
    | yRightSlot i h => simp [LeafRow.target] at ht
    | yRightTail i => simp [LeafRow.target] at ht
    | yRightA i => simp [LeafRow.target] at ht
  · intro i hi
    let u : Fin k := ⟨i.val+1, by omega⟩
    let v : Fin k := ⟨i.val+2, by omega⟩
    apply excluded (.inr (.inr i)) (.inr (.inl u)) (.inr (.inl v))
      (by simp) (by simp) (by
        intro h
        have huv : u = v := Sum.inl.inj (Sum.inr.inj h)
        have hv := congrArg Fin.val huv
        dsimp [u,v] at hv
        omega)
    intro r ht a c ha
    cases r with
    | ySlot i' t =>
      have he : i' = i := by simpa only [LeafRow.target, Sum.inr.injEq] using ht
      subst i'
      simp only [LeafRow.reply]
      dsimp only [u,v]
      rw [if_neg (by omega), if_neg (by omega)]
    | yLeftTail i' => rfl
    | yRightSlot i' h => rfl
    | yRightTail i' => rfl
    | yRightA i' => rfl
    | pSlot t => simp [LeafRow.target] at ht
    | pTail => simp [LeafRow.target] at ht
    | pOuter b => simp [LeafRow.target] at ht
    | pInner => simp [LeafRow.target] at ht
    | xSlot j t h => simp [LeafRow.target] at ht
    | xExceptional j => simp [LeafRow.target] at ht
    | xTail j => simp [LeafRow.target] at ht
    | xRight j => simp [LeafRow.target] at ht

end D5.S3.Arith.FibonacciAtomic.Scale38RawEndpointSpectrum
