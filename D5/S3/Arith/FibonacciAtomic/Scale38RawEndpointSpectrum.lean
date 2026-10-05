/- GID: D5/S3/Arith/FibonacciAtomic/Scale38RawEndpointSpectrum
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Complete raw endpoint spectrum and exact paid sets of literal scans. -/

import D5.S3.Arith.FibonacciAtomic.RawEndpointPeeling
import D5.S3.Arith.FibonacciAtomic.Scale38LeafFrontierResponse
import Mathlib.Data.Fin.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Scale38RawEndpointSpectrum

open GenealogicalFiberTransport (Source)
open ActualTreeReadoutAcquisition (Address Reply readout leaves vector chi Strategy terminal paid cost)
open ActualJointResponseCostCore (survivors controllerPolicy controllerOutcome)
open ActualImageSevenLeafSeparation (A C E leafLabel leafAddresses seven_leaf_separation)
open Scale38NestedCompensation (family query)
open FourExitRawEndpointSpectrum (comb comb_slot_readout comb_tail_readout)
open Scale38LeafFrontierResponse (LeafRow labelledFrontier)
open RawEndpointPeeling (Peels peelController)

local notation "B" => FourExitRawEndpointSpectrum.B

local notation "Index" => fun k : Nat => Unit ⊕ (Fin k ⊕ Fin k)

local notation "rawEndpoint" => fun (k : Nat) (z : Index k) =>
  ∃ qs : List Address,
    Peels (family k ∘ (Equiv.symm (Fintype.equivFin (Index k))))
      ((Fintype.equivFin (Index k)) z) Finset.univ qs

/-- The baseline, first enlarged slot, and last two contracted positions. -/
def endpointTargets (k : Nat) : Set (Index k) := {Z |
  match Z with
  | .inl _ => True
  | .inr (.inl j) => j.val = 0
  | .inr (.inr i) => k ≤ i.val+2}

/-- Length of each literal target scan, including its final right-side queries. -/
def scanLength (k : Nat) : Index k → Nat
  | .inl _ | .inr (.inl _) => k+1
  | .inr (.inr i) => i.val+1 + if i.val+1=k then 1 else 3

/-- The zero-based address at each step of the literal target scan. -/
def scanAddress (k : Nat) : Index k → Nat → Address
  | .inl _, t => query t
  | .inr (.inl _), t => if t < k then query (t+1) else [true,true]
  | .inr (.inr i), t => if t < i.val+1 then query t else
      true :: query (if i.val+1=k then 1 else t-(i.val+1))

/-- The first nonleaf query for each distinct competitor of an eligible target. -/
def exitAddress (k : Nat) : Index k → Index k → Address
  | .inl _, .inl _ => query k
  | .inl _, .inr (.inl j) => query j.val
  | .inl _, .inr (.inr i) => query (i.val+1)
  | .inr (.inl _), .inl _ => [true,true]
  | .inr (.inl _), .inr (.inl j) => query j.val
  | .inr (.inl _), .inr (.inr i) => query (i.val+1)
  | .inr (.inr _), .inl _ => true :: query 1
  | .inr (.inr i), .inr (.inl j) => if j.val ≤ i.val then query j.val else true :: query 0
  | .inr (.inr i), .inr (.inr j) => if j.val < i.val then query (j.val+1) else true :: query 2

/-- The complete raw endpoint spectrum, literal safe scans, actual controllers,
and exact paid address sets for every family member. -/
theorem result (k : Nat) (hk : 1 ≤ k) :
    let e := Fintype.equivFin (Index k)
    let F := family k ∘ e.symm
    (∀ Z : Index k, (∃ qs, Peels F (e Z) Finset.univ qs) ↔ Z ∈ endpointTargets k) ∧
    (∀ Z : Index k, Z ∈ endpointTargets k →
      let qs := (List.range (scanLength k Z)).map (scanAddress k Z)
      Peels F (e Z) Finset.univ qs ∧
      (∀ U : Index k, U ≠ Z →
        qs.find? (fun a => decide (chi (readout a (family k U)) = 1)) = some (exitAddress k Z U)) ∧
      ∃ π : Strategy,
        π.policy = controllerPolicy (peelController F (e Z) Finset.univ qs) ∧
        (∀ U, terminal π U = controllerOutcome (peelController F (e Z) Finset.univ qs) U) ∧
        (∀ U : Index k, cost π (family k U) = 3*k+14 - (if U = Z then 1 else 0)) ∧
        (∀ U : Index k, paid (terminal π (family k U)).1 = leafAddresses (family k U) ∪
          if U = Z then ∅ else {exitAddress k Z U})) := by
  classical
  have exclusions (k : Nat) (hk : 1 ≤ k) :
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
      cases hq : readout a Q with
      | alpha =>
        have hc : b = true := labels b true hb (by simp only [leafLabel, hq])
        subst b
        left
        cases hp : readout a P <;>
          simp only [leafLabel, hp, Option.some.injEq, reduceCtorEq] at hb ⊢
      | beta =>
        have hc : b = false := labels b false hb (by simp only [leafLabel, hq])
        subst b
        left
        cases hp : readout a P <;>
          simp only [leafLabel, hp, Option.some.injEq, reduceCtorEq] at hb ⊢
      | branch => exact Or.inr (Or.inl rfl)
      | absent => exact Or.inr (Or.inr rfl)
    
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
      | pSlot t => simp only [LeafRow.target, Sum.inr.injEq, Sum.inl.injEq, reduceCtorEq] at ht
      | pTail => simp only [LeafRow.target, Sum.inr.injEq, Sum.inl.injEq, reduceCtorEq] at ht
      | pOuter b => simp only [LeafRow.target, Sum.inr.injEq, Sum.inl.injEq, reduceCtorEq] at ht
      | pInner => simp only [LeafRow.target, Sum.inr.injEq, Sum.inl.injEq, reduceCtorEq] at ht
      | ySlot i t => simp only [LeafRow.target, Sum.inr.injEq, Sum.inl.injEq, reduceCtorEq] at ht
      | yLeftTail i => simp only [LeafRow.target, Sum.inr.injEq, Sum.inl.injEq, reduceCtorEq] at ht
      | yRightSlot i h => simp only [LeafRow.target, Sum.inr.injEq, Sum.inl.injEq, reduceCtorEq] at ht
      | yRightTail i => simp only [LeafRow.target, Sum.inr.injEq, Sum.inl.injEq, reduceCtorEq] at ht
      | yRightA i => simp only [LeafRow.target, Sum.inr.injEq, Sum.inl.injEq, reduceCtorEq] at ht
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
      | pSlot t => simp only [LeafRow.target, Sum.inr.injEq, Sum.inl.injEq, reduceCtorEq] at ht
      | pTail => simp only [LeafRow.target, Sum.inr.injEq, Sum.inl.injEq, reduceCtorEq] at ht
      | pOuter b => simp only [LeafRow.target, Sum.inr.injEq, Sum.inl.injEq, reduceCtorEq] at ht
      | pInner => simp only [LeafRow.target, Sum.inr.injEq, Sum.inl.injEq, reduceCtorEq] at ht
      | xSlot j t h => simp only [LeafRow.target, Sum.inr.injEq, Sum.inl.injEq, reduceCtorEq] at ht
      | xExceptional j => simp only [LeafRow.target, Sum.inr.injEq, Sum.inl.injEq, reduceCtorEq] at ht
      | xTail j => simp only [LeafRow.target, Sum.inr.injEq, Sum.inl.injEq, reduceCtorEq] at ht
      | xRight j => simp only [LeafRow.target, Sum.inr.injEq, Sum.inl.injEq, reduceCtorEq] at ht
  have safe_scan {m n : Nat} (F : Fin m → Source) (z : Fin m)
      (q : Nat → Address) (exit : Fin m → Nat)
      (leaf : ∀ t < n, q t ∈ leaves (F z) ∧ chi (readout (q t) (F z)) = 0)
      (before : ∀ i t, t < n → t < exit i → readout (q t) (F i) = readout (q t) (F z))
      (nonleaf : ∀ i, i ≠ z → exit i < n ∧ chi (readout (q (exit i)) (F i)) = 1)
      (unique : ∀ i j, i ≠ z → j ≠ z → exit i = exit j →
        readout (q (exit i)) (F i) = readout (q (exit j)) (F j) → i = j) :
      Peels F z Finset.univ ((List.range n).map q) := by
    classical
    let S := fun t : Nat => Finset.univ.filter (fun i => i = z ∨ t ≤ exit i)
    have loop : ∀ r t, t + r = n →
        Peels F z (S t) ((List.range' t r).map q) := by
      intro r
      induction r with
      | zero =>
        intro t ht i hi
        have hit : i = z ∨ t ≤ exit i := (Finset.mem_filter.mp hi).2
        apply Finset.mem_singleton.mpr
        rcases hit with hit | hit
        · exact hit
        · by_contra h
          have hlt := (nonleaf i h).1
          omega
      | succ r ih =>
        intro t ht
        have htn : t < n := by omega
        have target_zero := (leaf t htn).2
        have at_exit (i : Fin m) (hi : i ∈ S t)
            (y : ActualTreeReadoutAcquisition.Reply) (hy : chi y = 1)
            (hiy : readout (q t) (F i) = y) : i ≠ z ∧ exit i = t := by
          have hiz : i ≠ z := by
            intro h
            subst i
            rw [hiy, hy] at target_zero
            omega
          have hti : t ≤ exit i := ((Finset.mem_filter.mp hi).2).resolve_left hiz
          have he : exit i = t := by
            by_contra h
            have hb := before i t htn (by omega)
            rw [hiy] at hb
            have hc := congrArg chi hb
            rw [hy, target_zero] at hc
            omega
          exact ⟨hiz, he⟩
        have group (y : ActualTreeReadoutAcquisition.Reply) (hy : chi y = 1) :
            (survivors (S t) (vector F (q t)) y).card ≤ 1 := by
          apply Finset.card_le_one.mpr
          intro i hi j hj
          obtain ⟨his, hiy⟩ := Finset.mem_filter.mp hi
          obtain ⟨hjs, hjy⟩ := Finset.mem_filter.mp hj
          change readout (q t) (F i) = y at hiy
          change readout (q t) (F j) = y at hjy
          obtain ⟨hiz, hei⟩ := at_exit i his y hy hiy
          obtain ⟨hjz, hej⟩ := at_exit j hjs y hy hjy
          apply unique i j hiz hjz (hei.trans hej.symm)
          simpa only [hei, hej] using hiy.trans hjy.symm
        have next : survivors (S t) (vector F (q t)) (readout (q t) (F z)) = S (t+1) := by
          apply Finset.ext
          intro i
          change (i ∈ (Finset.univ.filter (fun j => j = z ∨ t ≤ exit j)).filter
            (fun j => readout (q t) (F j) = readout (q t) (F z))) ↔
            i ∈ Finset.univ.filter (fun j => j = z ∨ t+1 ≤ exit j)
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨hit, he⟩
            rcases hit with hit | hit
            · exact Or.inl hit
            · by_cases hiz : i = z
              · exact Or.inl hiz
              · right
                have hne : exit i ≠ t := by
                  intro h
                  have hn := (nonleaf i hiz).2
                  rw [h, he, target_zero] at hn
                  omega
                omega
          · intro hit
            rcases hit with hit | hit
            · subst i
              exact ⟨Or.inl rfl, rfl⟩
            · exact ⟨Or.inr (by omega), before i t htn (by omega)⟩
        rw [List.range'_succ, List.map_cons]
        change q t ∈ leaves (F z) ∧ _ ∧ _ ∧ _
        refine ⟨(leaf t htn).1, group .branch rfl, group .absent rfl, ?_⟩
        rw [next]
        exact ih (t+1) (by omega)
    simpa only [S, Nat.zero_le, or_true, Finset.filter_true, ← List.range_eq_range'] using
      loop n 0 (by omega)
  have first_exit {m n : Nat} (F : Fin m → Source) (z i : Fin m)
      (q : Nat → Address) (exit : Fin m → Nat) (hi : i ≠ z)
      (zero : ∀ t < n, chi (readout (q t) (F z)) = 0)
      (before : ∀ i t, t < n → t < exit i → readout (q t) (F i) = readout (q t) (F z))
      (nonleaf : ∀ i, i ≠ z → exit i < n ∧ chi (readout (q (exit i)) (F i)) = 1) :
      ((List.range n).map q).find? (fun a => decide (chi (readout a (F i)) = 1)) =
        some (q (exit i)) := by
    have hbound := (nonleaf i hi).1
    apply List.find?_eq_some_iff_getElem.mpr
    refine ⟨by simp only [(nonleaf i hi).2, decide_true], exit i,
      by simpa only [List.length_map, List.length_range] using (nonleaf i hi).1, ?_, ?_⟩
    · simp only [List.getElem_map, List.getElem_range]
    · intro j hj
      simp only [List.getElem_map, List.getElem_range]
      rw [before i j (by omega) hj, zero j (by omega)]
      decide
  let p_exit (k : Nat) : Index k → Nat := fun U => match U with
    | .inl _ => k+1
    | .inr (.inl j) => j.val
    | .inr (.inr i) => i.val+1
  
  let p_reply {k : Nat} : Index k → Reply := fun U => match U with
    | .inr (.inr _) => .absent
    | _ => .branch
  
  have p_scan (k : Nat) (hk : 1 ≤ k) :
      let e := Fintype.equivFin (Index k)
      Peels (family k ∘ e.symm) (e (.inl ())) Finset.univ
        ((List.range (k+1)).map (query)) ∧
        ∀ U : Index k, U ≠ .inl () →
          ((List.range (k+1)).map (query)).find? (fun a => decide (chi (readout a (family k U)) = 1)) =
            some ((query) ((p_exit k) U)) := by
    classical
    let z : Index k := .inl ()
    let e := Fintype.equivFin (Index k)
    let F := family k ∘ e.symm
    have base := Scale38NestedCompensation.result k hk
    have rawP := base.2.2.2.2.1
    have rawX := base.2.2.2.2.2.1
    have rawY := base.2.2.2.2.2.2.1
    have target_leaf (t : Nat) (ht : t < k+1) :
        query t ∈ leaves (family k z) ∧ chi (readout (query t) (family k z)) = 0 := by
      have hr : readout (query t) (family k z) = .alpha := rawP t (by omega)
      have hm := ((seven_leaf_separation.1 (family k z)).2 (query t)).mpr
        ⟨true, by simp only [leafLabel, hr]⟩
      exact ⟨by simpa only [leafAddresses, List.mem_toFinset] using hm, by rw [hr]; rfl⟩
    have before (U : Index k) (t : Nat) (ht : t < k+1) (hb : t < p_exit k U) :
        readout (query t) (family k U) = readout (query t) (family k z) := by
      rw [rawP t (by omega)]
      cases U with
      | inl u => exact rawP t (by omega)
      | inr v => cases v with
        | inl j => exact (rawX j).1 t hb
        | inr i => exact (rawY i).1 t (by change t < i.val+1 at hb; omega)
    have exiting (U : Index k) (hu : U ≠ z) : p_exit k U < k+1 ∧
        readout (query (p_exit k U)) (family k U) = p_reply U := by
      cases U with
      | inl u => cases u; exact (hu rfl).elim
      | inr v => cases v with
        | inl j => exact ⟨by change j.val < k+1; omega, (rawX j).2⟩
        | inr i => exact ⟨by change i.val+1 < k+1; omega, (rawY i).2⟩
    have unique (U V : Index k) (hu : U ≠ z) (hv : V ≠ z)
        (he : p_exit k U = p_exit k V)
        (hr : readout (query (p_exit k U)) (family k U) =
          readout (query (p_exit k V)) (family k V)) : U = V := by
      rw [(exiting U hu).2, (exiting V hv).2] at hr
      cases U with
      | inl u => cases u; exact (hu rfl).elim
      | inr u => cases V with
        | inl v => cases v; exact (hv rfl).elim
        | inr v =>
          cases u <;> cases v <;> simp only [p_reply] at hr
          all_goals try cases hr
          all_goals congr 2
          all_goals apply Fin.ext
          all_goals simp only [p_exit] at he
          all_goals omega
    constructor
    ·
      change Peels F (e z) Finset.univ _
      apply safe_scan F (e z) query (fun j => p_exit k (e.symm j))
      · simpa only [F, Function.comp_apply, Equiv.symm_apply_apply] using target_leaf
      · intro j t ht hb
        exact (before (e.symm j) t ht hb).trans (by simp only [F, Function.comp_apply, Equiv.symm_apply_apply])
      · intro j hj
        have hn : e.symm j ≠ z := by
          intro h; apply hj; exact (e.apply_symm_apply j).symm.trans (congrArg e h)
        have hx := exiting (e.symm j) hn
        refine ⟨hx.1, ?_⟩
        change chi (readout (query (p_exit k (e.symm j))) (family k (e.symm j))) = 1
        rw [hx.2]
        generalize e.symm j = U
        cases U with
        | inl u => rfl
        | inr v => cases v <;> rfl
      · intro a b ha hb he hr
        apply e.symm.injective
        apply unique (e.symm a) (e.symm b)
        · intro h; apply ha; exact (e.apply_symm_apply a).symm.trans (congrArg e h)
        · intro h; apply hb; exact (e.apply_symm_apply b).symm.trans (congrArg e h)
        · exact he
        · exact hr
    · intro U hu
      have hfirst := first_exit F (e z) (e U) (query) (fun j => (p_exit k) (e.symm j))
        (fun h => hu (e.injective h))
        (fun t ht => by simpa only [F, Function.comp_apply, Equiv.symm_apply_apply]
          using (target_leaf t ht).2)
        (fun j t ht hb => (before (e.symm j) t ht hb).trans
          (by simp only [F, Function.comp_apply, Equiv.symm_apply_apply]))
        (fun j hj => by
          have hn : e.symm j ≠ z := by
            intro h; apply hj; exact (e.apply_symm_apply j).symm.trans (congrArg e h)
          have hx := exiting (e.symm j) hn
          refine ⟨hx.1, ?_⟩
          change chi (readout ((query) ((p_exit k) (e.symm j))) (family k (e.symm j))) = 1
          rw [hx.2]
          generalize e.symm j = V
          cases V with
          | inl u => rfl
          | inr v =>
            cases v <;> rfl
        )
      simpa only [F, Function.comp_apply, Equiv.symm_apply_apply] using hfirst
  let x_query (k t : Nat) : Address := if t < k then query (t+1) else [true,true]
  let x_exit (k : Nat) : Index k → Nat := fun U => match U with
    | .inl _ => k
    | .inr (.inl j) => if j.val = 0 then k+1 else j.val-1
    | .inr (.inr i) => i.val
  
  let x_reply {k : Nat} : Index k → Reply := fun U => match U with
    | .inr (.inr _) => .absent
    | _ => .branch
  
  have x_scan (k : Nat) (hk : 1 ≤ k) :
      let e := Fintype.equivFin (Index k)
      Peels (family k ∘ e.symm) (e (.inr (.inl ⟨0,by omega⟩))) Finset.univ
        ((List.range (k+1)).map (x_query k)) ∧
        ∀ U : Index k, U ≠ .inr (.inl ⟨0,by omega⟩) →
          ((List.range (k+1)).map (x_query k)).find? (fun a => decide (chi (readout a (family k U)) = 1)) =
            some ((x_query k) ((x_exit k) U)) := by
    classical
    let z : Index k := .inr (.inl ⟨0,by omega⟩)
    let e := Fintype.equivFin (Index k)
    let F := family k ∘ e.symm
    have base := Scale38NestedCompensation.result k hk
    have rawP := base.2.2.2.2.1
    have rawX := base.2.2.2.2.2.1
    have rawY := base.2.2.2.2.2.2.1
    have normal (j : Fin k) (s : Nat) (hs : s ≤ k) (hne : s ≠ j.val) :
        readout (query s) (family k (.inr (.inl j))) = .alpha := by
      change readout (List.replicate s true ++ [false,false,true])
        (comb k (fun l => if l = j then B else A) C) = .alpha
      by_cases hsk : s < k
      · have hfin : (⟨s,hsk⟩ : Fin k) ≠ j := fun h => hne (congrArg Fin.val h)
        have h := comb_slot_readout k (fun l => if l = j then B else A) C ⟨s,hsk⟩ [false,true]
        rw [if_neg hfin] at h
        exact h.trans rfl
      · have he : s = k := by omega
        subst s
        exact (comb_tail_readout k (fun l => if l = j then B else A) C [false,false,true]).trans rfl
    have target (t : Nat) (ht : t < k+1) :
        readout (x_query k t) (family k z) = if t < k then .alpha else .beta := by
      by_cases htk : t < k
      · simp only [x_query, htk, ite_true]
        exact normal ⟨0,by omega⟩ (t+1) (by omega) (by change t+1 ≠ 0; omega)
      · simp only [x_query, htk, ite_false]
        rfl
    have target_leaf (t : Nat) (ht : t < k+1) :
        x_query k t ∈ leaves (family k z) ∧ chi (readout (x_query k t) (family k z)) = 0 := by
      have hr := target t ht
      have hl : ∃ b, leafLabel (family k z) (x_query k t) = some b := by
        by_cases htk : t < k
        · exact ⟨true, by simp [leafLabel, hr, htk]⟩
        · exact ⟨false, by simp [leafLabel, hr, htk]⟩
      have hm := ((seven_leaf_separation.1 (family k z)).2 (x_query k t)).mpr hl
      refine ⟨by simpa only [leafAddresses, List.mem_toFinset] using hm, ?_⟩
      rw [hr]
      split_ifs <;> rfl
    have before (U : Index k) (t : Nat) (ht : t < k+1) (hb : t < x_exit k U) :
        readout (x_query k t) (family k U) = readout (x_query k t) (family k z) := by
      cases U with
      | inl u =>
        have htk : t < k := by simpa only [x_exit] using hb
        rw [target t ht, if_pos htk]
        simpa only [x_query, if_pos htk] using rawP (t+1) (by omega)
      | inr v =>
        cases v with
        | inl j =>
          by_cases hj : j.val = 0
          · have he : j = ⟨0,by omega⟩ := Fin.ext hj
            rw [he]
          · have hsmall : t < j.val-1 := by simpa only [x_exit, if_neg hj] using hb
            have htk : t < k := by omega
            rw [target t ht, if_pos htk]
            simpa only [x_query, if_pos htk] using (rawX j).1 (t+1) (by omega)
        | inr i =>
          have hsmall : t < i.val := hb
          have htk : t < k := by omega
          rw [target t ht, if_pos htk]
          simpa only [x_query, if_pos htk] using (rawY i).1 (t+1) (by omega)
    have exiting (U : Index k) (hu : U ≠ z) : x_exit k U < k+1 ∧
        readout (x_query k (x_exit k U)) (family k U) =
          x_reply U := by
      cases U with
      | inl u =>
        refine ⟨by simp [x_exit], ?_⟩
        simp only [x_exit, x_query, Nat.lt_irrefl, if_false, x_reply]
        rfl
      | inr v =>
        cases v with
        | inl j =>
          have hj : j.val ≠ 0 := by
            intro h
            apply hu
            have he : j = ⟨0,by omega⟩ := Fin.ext h
            simp only [he]
            rfl
          have hsmall : j.val-1 < k := by omega
          have he : j.val-1+1 = j.val := by omega
          simp only [x_exit, if_neg hj, x_query, if_pos hsmall, he]
          exact ⟨by omega, (rawX j).2⟩
        | inr i =>
          refine ⟨by dsimp only [x_exit]; omega, ?_⟩
          change readout (x_query k i.val) (family k (.inr (.inr i))) = .absent
          dsimp only [x_query]
          rw [if_pos i.isLt]
          exact (rawY i).2
    have unique (U V : Index k) (hu : U ≠ z) (hv : V ≠ z)
        (he : x_exit k U = x_exit k V)
        (hr : readout (x_query k (x_exit k U)) (family k U) =
          readout (x_query k (x_exit k V)) (family k V)) : U = V := by
      rw [(exiting U hu).2, (exiting V hv).2] at hr
      cases U with
      | inl u =>
        cases V with
        | inl v => cases u; cases v; rfl
        | inr v =>
          cases v with
          | inl j => simp only [x_exit] at he; split_ifs at he <;> omega
          | inr i => cases hr
      | inr u =>
        cases u with
        | inl j =>
          cases V with
          | inl u => simp only [x_exit] at he; split_ifs at he <;> omega
          | inr v =>
            cases v with
            | inl l =>
              have hj : j.val ≠ 0 := by intro h; apply hu; congr 2; exact Fin.ext h
              have hl : l.val ≠ 0 := by intro h; apply hv; congr 2; exact Fin.ext h
              simp only [x_exit, if_neg hj, if_neg hl] at he
              congr 2
              apply Fin.ext
              omega
            | inr i => cases hr
        | inr i =>
          cases V with
          | inl u => cases hr
          | inr v =>
            cases v with
            | inl j => cases hr
            | inr l =>
              congr 2
              exact Fin.ext he
    constructor
    ·
      change Peels F (e z) Finset.univ _
      apply safe_scan F (e z) (x_query k) (fun i => x_exit k (e.symm i))
      · simpa only [F, Function.comp_apply, Equiv.symm_apply_apply] using target_leaf
      · intro i t ht hb
        exact (before (e.symm i) t ht hb).trans (by simp only [F, Function.comp_apply, Equiv.symm_apply_apply])
      · intro i hi
        have hn : e.symm i ≠ z := by
          intro h
          apply hi
          exact (e.apply_symm_apply i).symm.trans (congrArg e h)
        have hx := exiting (e.symm i) hn
        refine ⟨hx.1, ?_⟩
        change chi (readout (x_query k (x_exit k (e.symm i))) (family k (e.symm i))) = 1
        rw [hx.2]
        generalize e.symm i = U
        cases U with
        | inl u => rfl
        | inr v => cases v <;> rfl
      · intro i j hi hj he hr
        apply e.symm.injective
        apply unique (e.symm i) (e.symm j)
        · intro h; apply hi; exact (e.apply_symm_apply i).symm.trans (congrArg e h)
        · intro h; apply hj; exact (e.apply_symm_apply j).symm.trans (congrArg e h)
        · exact he
        · exact hr
    · intro U hu
      have hfirst := first_exit F (e z) (e U) (x_query k) (fun j => (x_exit k) (e.symm j))
        (fun h => hu (e.injective h))
        (fun t ht => by simpa only [F, Function.comp_apply, Equiv.symm_apply_apply]
          using (target_leaf t ht).2)
        (fun j t ht hb => (before (e.symm j) t ht hb).trans
          (by simp only [F, Function.comp_apply, Equiv.symm_apply_apply]))
        (fun j hj => by
          have hn : e.symm j ≠ z := by
            intro h; apply hj; exact (e.apply_symm_apply j).symm.trans (congrArg e h)
          have hx := exiting (e.symm j) hn
          refine ⟨hx.1, ?_⟩
          change chi (readout ((x_query k) ((x_exit k) (e.symm j))) (family k (e.symm j))) = 1
          rw [hx.2]
          generalize e.symm j = V
          cases V with
          | inl u => rfl
          | inr v =>
            cases v <;> rfl
        )
      simpa only [F, Function.comp_apply, Equiv.symm_apply_apply] using hfirst
  let y_count (k : Nat) (i : Fin k) : Nat := i.val+1 + if i.val+1=k then 1 else 3
  let y_query (k : Nat) (i : Fin k) (t : Nat) : Address :=
    if t < i.val+1 then query t else true :: query (if i.val+1=k then 1 else t-(i.val+1))
  let y_exit (k : Nat) (i : Fin k) : Index k → Nat := fun U => match U with
    | .inl _ => k
    | .inr (.inl j) => j.val
    | .inr (.inr j) => if j.val < i.val then j.val+1 else if i.val < j.val then i.val+3 else y_count k i
  let y_reply (k : Nat) (i : Fin k) : Index k → Reply := fun U => match U with
    | .inr (.inl j) => if j.val < i.val+1 then .branch else .absent
    | _ => .absent
  
  have y_scan (k : Nat) (hk : 1 ≤ k) (i : Fin k) (hi : k ≤ i.val+2) :
      let e := Fintype.equivFin (Index k)
      Peels (family k ∘ e.symm) (e (.inr (.inr i))) Finset.univ
        ((List.range (y_count k i)).map (y_query k i)) ∧
        ∀ U : Index k, U ≠ .inr (.inr i) →
          ((List.range (y_count k i)).map (y_query k i)).find? (fun a => decide (chi (readout a (family k U)) = 1)) =
            some ((y_query k i) ((y_exit k i) U)) := by
    classical
    let z : Index k := .inr (.inr i)
    let e := Fintype.equivFin (Index k)
    let F := family k ∘ e.symm
    have base := Scale38NestedCompensation.result k hk
    have rawP := base.2.2.2.2.1
    have rawX := base.2.2.2.2.2.1
    have rawY := base.2.2.2.2.2.2.1
    have right_match (j : Fin k) (h : Nat) (hh : h ≤ k-j.val) :
        readout (true :: query h) (family k (.inr (.inr j))) = .alpha := by
      have hpositive : 1 ≤ k-j.val := by omega
      exact (Scale38NestedCompensation.result (k-j.val) hpositive).2.2.2.2.1 h hh
    have right_absent (j : Fin k) :
        readout (true :: query (k-j.val+1)) (family k (.inr (.inr j))) = .absent := by
      let n := k-j.val
      exact (Scale38NestedCompensation.result (n+1) (by omega)).2.2.2.2.2.2.1
        ⟨n,by omega⟩ |>.2
    have target (t : Nat) (ht : t < y_count k i) :
        readout (y_query k i t) (family k z) = .alpha := by
      by_cases htl : t < i.val+1
      · simpa only [y_query, if_pos htl] using (rawY i).1 t (by omega)
      · simp only [y_query, if_neg htl]
        apply right_match
        unfold y_count at ht
        split_ifs at ht ⊢ <;> omega
    have target_leaf (t : Nat) (ht : t < y_count k i) :
        y_query k i t ∈ leaves (family k z) ∧ chi (readout (y_query k i t) (family k z)) = 0 := by
      have hr := target t ht
      have hm := ((seven_leaf_separation.1 (family k z)).2 (y_query k i t)).mpr
        ⟨true, by simp only [leafLabel, hr]⟩
      exact ⟨by simpa only [leafAddresses, List.mem_toFinset] using hm, by rw [hr]; rfl⟩
    have before (U : Index k) (t : Nat) (ht : t < y_count k i) (hb : t < y_exit k i U) :
        readout (y_query k i t) (family k U) = readout (y_query k i t) (family k z) := by
      rw [target t ht]
      cases U with
      | inl u =>
        have htk : t < k := hb
        by_cases htl : t < i.val+1
        · simpa only [y_query, if_pos htl] using rawP t (by omega)
        · have he : t = i.val+1 := by omega
          have hlast : i.val+1 ≠ k := by omega
          dsimp only [y_query]
          rw [if_neg htl, if_neg hlast, he, Nat.sub_self]
          rfl
      | inr v =>
        cases v with
        | inl j =>
          have htj : t < j.val := hb
          have htl : t < i.val+1 := by omega
          simpa only [y_query, if_pos htl] using (rawX j).1 t htj
        | inr j =>
          by_cases hji : j.val = i.val
          · have he : j = i := Fin.ext hji
            simpa only [he] using target t ht
          · by_cases hjlt : j.val < i.val
            · have htj : t < j.val+1 := by simpa only [y_exit, if_pos hjlt] using hb
              have htl : t < i.val+1 := by omega
              simpa only [y_query, if_pos htl] using (rawY j).1 t (by omega)
            · have hilt : i.val < j.val := by omega
              have htj : t < i.val+3 := by simpa only [y_exit, if_neg hjlt, if_pos hilt] using hb
              by_cases htl : t < i.val+1
              · simpa only [y_query, if_pos htl] using (rawY j).1 t (by omega)
              · have hlast : i.val+1 ≠ k := by omega
                simp only [y_query, if_neg htl, if_neg hlast]
                apply right_match
                omega
    have exiting (U : Index k) (hu : U ≠ z) : y_exit k i U < y_count k i ∧
        readout (y_query k i (y_exit k i U)) (family k U) = y_reply k i U := by
      cases U with
      | inl u =>
        have htl : ¬ k < i.val+1 := by omega
        have tail : (if i.val+1=k then 1 else k-(i.val+1)) = 1 := by split_ifs <;> omega
        refine ⟨by change k < y_count k i; unfold y_count; split_ifs <;> omega, ?_⟩
        simp only [y_exit, y_query, if_neg htl, tail, y_reply]
        rfl
      | inr v =>
        cases v with
        | inl j =>
          refine ⟨by change j.val < y_count k i; unfold y_count; split_ifs <;> omega, ?_⟩
          by_cases hjl : j.val < i.val+1
          · change readout (y_query k i j.val) (family k (.inr (.inl j))) =
              if j.val < i.val+1 then .branch else .absent
            simp only [y_query, if_pos hjl]
            exact (rawX j).2
          · have he : j.val = i.val+1 := by omega
            have hlast : i.val+1 ≠ k := by omega
            simp only [y_exit, y_query, y_reply, if_neg hjl, if_neg hlast, he, Nat.sub_self, Nat.lt_irrefl, if_false]
            rfl
        | inr j =>
          have hji : j.val ≠ i.val := by intro h; apply hu; congr 2; exact Fin.ext h
          by_cases hjlt : j.val < i.val
          · have htl : j.val+1 < i.val+1 := by omega
            simp only [y_exit, if_pos hjlt, y_query, if_pos htl, y_reply]
            exact ⟨by unfold y_count; split_ifs <;> omega, (rawY j).2⟩
          · have hilt : i.val < j.val := by omega
            have hlast : i.val+1 ≠ k := by omega
            have htl : ¬ i.val+3 < i.val+1 := by omega
            have hdelta : i.val+3-(i.val+1) = k-j.val+1 := by omega
            simp only [y_exit, if_neg hjlt, if_pos hilt, y_query, if_neg htl,
              if_neg hlast, hdelta, y_reply]
            exact ⟨by unfold y_count; rw [if_neg hlast]; omega, right_absent j⟩
    have unique (U V : Index k) (hu : U ≠ z) (hv : V ≠ z)
        (he : y_exit k i U = y_exit k i V)
        (hr : readout (y_query k i (y_exit k i U)) (family k U) =
          readout (y_query k i (y_exit k i V)) (family k V)) : U = V := by
      rw [(exiting U hu).2, (exiting V hv).2] at hr
      cases U with
      | inl u =>
        cases V with
        | inl v => cases u; cases v; rfl
        | inr v =>
          cases v with
          | inl j => simp only [y_exit, y_count] at he; omega
          | inr j =>
            have hji : j.val ≠ i.val := by intro h; apply hv; congr 2; exact Fin.ext h
            simp only [y_exit, y_count] at he
            split_ifs at he <;> omega
      | inr u =>
        cases u with
        | inl j =>
          cases V with
          | inl u => simp only [y_exit, y_count] at he; omega
          | inr v =>
            cases v with
            | inl l => congr 2; exact Fin.ext he
            | inr l =>
              simp only [y_exit, y_count] at he
              simp only [y_reply] at hr
              split_ifs at he hr <;> cases hr <;> omega
        | inr j =>
          cases V with
          | inl u =>
            have hji : j.val ≠ i.val := by intro h; apply hu; congr 2; exact Fin.ext h
            simp only [y_exit, y_count] at he
            split_ifs at he <;> omega
          | inr v =>
            cases v with
            | inl l =>
              simp only [y_exit, y_count] at he
              simp only [y_reply] at hr
              split_ifs at he hr <;> cases hr <;> omega
            | inr l =>
              have hji : j.val ≠ i.val := by intro h; apply hu; congr 2; exact Fin.ext h
              have hli : l.val ≠ i.val := by intro h; apply hv; congr 2; exact Fin.ext h
              simp only [y_exit, y_count] at he
              congr 2
              apply Fin.ext
              split_ifs at he <;> omega
    constructor
    ·
      change Peels F (e z) Finset.univ _
      apply safe_scan F (e z) (y_query k i) (fun j => y_exit k i (e.symm j))
      · simpa only [F, Function.comp_apply, Equiv.symm_apply_apply] using target_leaf
      · intro j t ht hb
        exact (before (e.symm j) t ht hb).trans (by simp only [F, Function.comp_apply, Equiv.symm_apply_apply])
      · intro j hj
        have hn : e.symm j ≠ z := by
          intro h; apply hj; exact (e.apply_symm_apply j).symm.trans (congrArg e h)
        have hx := exiting (e.symm j) hn
        refine ⟨hx.1, ?_⟩
        change chi (readout (y_query k i (y_exit k i (e.symm j))) (family k (e.symm j))) = 1
        rw [hx.2]
        generalize e.symm j = U
        cases U with
        | inl u => rfl
        | inr v => cases v with
          | inl l => simp only [y_reply]; split_ifs <;> rfl
          | inr l => rfl
      · intro a b ha hb he hr
        apply e.symm.injective
        apply unique (e.symm a) (e.symm b)
        · intro h; apply ha; exact (e.apply_symm_apply a).symm.trans (congrArg e h)
        · intro h; apply hb; exact (e.apply_symm_apply b).symm.trans (congrArg e h)
        · exact he
        · exact hr
    · intro U hu
      have hfirst := first_exit F (e z) (e U) (y_query k i) (fun j => (y_exit k i) (e.symm j))
        (fun h => hu (e.injective h))
        (fun t ht => by simpa only [F, Function.comp_apply, Equiv.symm_apply_apply]
          using (target_leaf t ht).2)
        (fun j t ht hb => (before (e.symm j) t ht hb).trans
          (by simp only [F, Function.comp_apply, Equiv.symm_apply_apply]))
        (fun j hj => by
          have hn : e.symm j ≠ z := by
            intro h; apply hj; exact (e.apply_symm_apply j).symm.trans (congrArg e h)
          have hx := exiting (e.symm j) hn
          refine ⟨hx.1, ?_⟩
          change chi (readout ((y_query k i) ((y_exit k i) (e.symm j))) (family k (e.symm j))) = 1
          rw [hx.2]
          generalize e.symm j = V
          cases V with
          | inl u => rfl
          | inr v =>
            cases v with
            | inl l => simp only [y_reply]; split_ifs <;> rfl
            | inr l => rfl
        )
      simpa only [F, Function.comp_apply, Equiv.symm_apply_apply] using hfirst
  let e := Fintype.equivFin (Index k)
  let F := family k ∘ e.symm
  have pschedule : scanAddress k (.inl ()) = query := rfl
  have xschedule (j : Fin k) : scanAddress k (.inr (.inl j)) = x_query k := rfl
  have yschedule (i : Fin k) : scanAddress k (.inr (.inr i)) = y_query k i := rfl
  have certificate (Z : Index k) (hZ : Z ∈ endpointTargets k) :
      Peels F (e Z) Finset.univ ((List.range (scanLength k Z)).map (scanAddress k Z)) ∧
      (∀ U : Index k, U ≠ Z →
        ((List.range (scanLength k Z)).map (scanAddress k Z)).find?
          (fun a => decide (chi (readout a (family k U)) = 1)) = some (exitAddress k Z U)) := by
    cases Z with
    | inl u =>
      cases u
      obtain ⟨hp, hf⟩ := p_scan k hk
      refine ⟨by simpa [F, e, scanLength, pschedule] using hp, ?_⟩
      intro U hu
      have hfirst := hf U hu
      cases U with
      | inl u => cases u; exact (hu rfl).elim
      | inr p => cases p <;> simpa [scanLength, pschedule, p_exit, exitAddress] using hfirst
    | inr p => cases p with
      | inl j =>
        have hj : j.val = 0 := hZ
        have he : j = ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hk⟩ := Fin.ext hj
        rw [he]
        obtain ⟨hp, hf⟩ := x_scan k hk
        refine ⟨by simpa [F, e, scanLength, xschedule] using hp, ?_⟩
        intro U hu
        have hfirst := hf U hu
        cases U with
        | inl u =>
          simpa [scanLength, xschedule, x_query, x_exit,
            Nat.lt_irrefl, if_false, exitAddress] using hfirst
        | inr p => cases p with
          | inl l =>
            have hl : l.val ≠ 0 := by intro h; apply hu; congr 2; exact Fin.ext h
            have hbound : l.val-1 < k := by omega
            have hplus : l.val-1+1=l.val := by omega
            simpa [scanLength, xschedule, x_query, x_exit,
              if_neg hl, if_pos hbound, hplus, exitAddress] using hfirst
          | inr l =>
            simpa [scanLength, xschedule, x_query, x_exit,
              if_pos l.isLt, exitAddress] using hfirst
      | inr i =>
        have hi : k ≤ i.val+2 := hZ
        obtain ⟨hp, hf⟩ := y_scan k hk i hi
        refine ⟨by simpa [F, e, scanLength, yschedule, y_count] using hp, ?_⟩
        intro U hu
        have hfirst := hf U hu
        have he : y_query k i (y_exit k i U) = exitAddress k (.inr (.inr i)) U := by
          cases U with
          | inl u =>
            have htl : ¬ k < i.val+1 := by omega
            have tail : (if i.val+1=k then 1 else k-(i.val+1)) = 1 := by split_ifs <;> omega
            simp only [y_exit, y_query, if_neg htl, tail, exitAddress]
          | inr p => cases p with
            | inl l =>
              by_cases hli : l.val ≤ i.val
              · have htl : l.val < i.val+1 := by omega
                simp [y_exit, y_query, htl, exitAddress, hli]
              · have hl : l.val = i.val+1 := by omega
                have hlast : i.val+1 ≠ k := by omega
                simp [y_exit, y_query, exitAddress, hl, hlast]
            | inr l =>
              have hli : l.val ≠ i.val := by intro h; apply hu; congr 2; exact Fin.ext h
              by_cases hlt : l.val < i.val
              · have htl : l.val+1 < i.val+1 := by omega
                simp only [y_exit, if_pos hlt, y_query, if_pos htl,
                  exitAddress, if_pos hlt]
              · have hil : i.val < l.val := by omega
                have hlast : i.val+1 ≠ k := by omega
                have htl : ¬ i.val+3 < i.val+1 := by omega
                have hsub : i.val+3-(i.val+1)=2 := by omega
                simp only [y_exit, if_neg hlt, if_pos hil, y_query,
                  if_neg htl, if_neg hlast, hsub, exitAddress, if_neg hlt]
        rw [he] at hfirst
        simpa only [scanLength, yschedule, y_count] using hfirst
  constructor
  · intro Z
    constructor
    · intro hp
      have excluded := exclusions k hk
      cases Z with
      | inl u => trivial
      | inr p => cases p with
        | inl j =>
          change j.val = 0
          by_contra h
          exact excluded.1 j (by omega) hp
        | inr i =>
          change k ≤ i.val+2
          by_contra h
          exact excluded.2 i (by omega) hp
    · intro hZ
      exact ⟨_, (certificate Z hZ).1⟩
  · intro Z hZ
    dsimp only
    let qs := (List.range (scanLength k Z)).map (scanAddress k Z)
    obtain ⟨hp,hfirst⟩ := certificate Z hZ
    refine ⟨hp, hfirst, ?_⟩
    obtain ⟨π,hpolicy,hterminal,hcost,hpaid,hother⟩ := (RawEndpointPeeling.result k hk (e Z)).2 qs hp
    refine ⟨π,hpolicy,hterminal,?_,?_⟩
    · intro U
      have hc := hcost (e U)
      simpa only [F, e, qs, Function.comp_apply, Equiv.symm_apply_apply, Equiv.apply_eq_iff_eq] using hc
    · intro U
      by_cases hu : U = Z
      · subst U
        simpa only [F, e, qs, Function.comp_apply, Equiv.symm_apply_apply, if_true,
          Finset.union_empty] using hpaid
      · obtain ⟨q,hfind,hnot,hbill⟩ := hother (e U) (fun h => hu (e.injective h))
        have hf := hfirst U hu
        have he : q = exitAddress k Z U := Option.some.inj (hfind.symm.trans (by
          simpa only [F, e, qs, Function.comp_apply, Equiv.symm_apply_apply] using hf))
        simpa only [F, e, qs, Function.comp_apply, Equiv.symm_apply_apply, if_neg hu, he] using hbill

end D5.S3.Arith.FibonacciAtomic.Scale38RawEndpointSpectrum
