/- GID: D5/S3/Combinatorics/Permutation/CoupledRepairedLeftInverse
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Permutation/CoupledRepairedLeftInverse
   mirror-E: none(waiver:noncomputable-permutation-reconstruction)
   anchors: [mathlib/module/Mathlib.Logic.Equiv.Fin.Basic, mathlib/module/Mathlib.Order.Fin.Tuple, mathlib/module/Mathlib.Data.Finset.Sort]
   utility: none
   digest: The coupled repaired digit maps recover both original permutations and have bounded forward digits. -/

import D5.S3.Combinatorics.Permutation.CoupledOrderedRecovery
import Mathlib
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Order.Fin.Tuple
import Mathlib.Data.Finset.Sort

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace D5.S3.Combinatorics.Permutation.CoupledRepairedLeftInverse

/-- Explicit actual maps. Their mathematical laws are not assumed fields. -/
structure Algorithms (k L B : Nat) where
  phi : Equiv.Perm (Fin (k+2)) -> Equiv.Perm (Fin (k+1)) ->
    Prod (Prod (Equiv.Perm (Fin (k+1))) (Equiv.Perm (Fin k))) (Prod Nat Nat)
  psi : Equiv.Perm (Fin (k+1)) -> Equiv.Perm (Fin k) ->
    Fin (L+1) -> Fin B -> Prod (Equiv.Perm (Fin (k+2))) (Equiv.Perm (Fin (k+1)))

noncomputable def cut {n : Nat} (sigma : Equiv.Perm (Fin (n+1))) (t : Fin (n+1)) :
    Equiv.Perm (Fin n) :=
  (finSuccAboveEquiv t).trans
    ((Equiv.subtypeEquiv sigma (by intro x; exact sigma.injective.ne_iff.symm)).trans
      (finSuccAboveEquiv (sigma t)).symm)
noncomputable def put {n : Nat} (s : Equiv.Perm (Fin n)) (a t : Fin (n+1)) :
    Equiv.Perm (Fin (n+1)) :=
  (finSuccEquiv' t).trans ((Equiv.optionCongr s).trans (finSuccEquiv' a).symm)
abbrev Slots {n : Nat} (sigma : Equiv.Perm (Fin n)) (T : Nat) :=
  {u : Fin n // (sigma u).val < T}
noncomputable def slotOrder {n T : Nat} (sigma : Equiv.Perm (Fin n)) (hT : T <= n) :
    Fin T ≃o Slots sigma T := by
  let e : Slots sigma T ≃ Fin T :=
    (Equiv.subtypeEquiv sigma (by intro x; rfl)).trans
      (Fin.castLEOrderIso hT).symm.toEquiv
  exact Fintype.orderIsoFinOfCardEq _ (by
    rw [Fintype.card_congr e, Fintype.card_fin])
noncomputable def lowWord {n T : Nat} (sigma : Equiv.Perm (Fin n)) (hT : T <= n) :
    Equiv.Perm (Fin T) :=
  (slotOrder sigma hT).toEquiv.trans
    ((Equiv.subtypeEquiv sigma (by intro x; rfl)).trans
      (Fin.castLEOrderIso hT).symm.toEquiv)
noncomputable def replace {n T : Nat} (sigma : Equiv.Perm (Fin n)) (hT : T <= n)
    (rho : Equiv.Perm (Fin T)) : Equiv.Perm (Fin n) :=
  sigma.trans (Equiv.permCongr (Fin.castLEOrderIso hT).toEquiv
    ((lowWord sigma hT).symm.trans rho)).ofSubtype

noncomputable def actualAlgorithms {k L B : Nat} (hLB : L <= B) (hB : B <= k+1) :
    Algorithms k L B := by
  let hL : L <= k+1 := hLB.trans hB
  refine ⟨?_, ?_⟩
  · intro sigma pi
    let t := pi 0
    let s := cut sigma t.castSucc
    let p := cut pi 0
    let theta := lowWord sigma (Nat.add_le_add_right hL 1)
    let q := theta.symm (Fin.last L)
    let rho := cut theta q
    let sdag := replace s hL rho
    let d := L - q.val
    let b := (Finset.univ.filter (fun u : Fin (k+1) =>
      u < t ∧ (s u).val < B)).card
    exact ((sdag,p),d,b)
  · intro sdag p d b
    let rho := lowWord sdag hL
    let theta := put rho (Fin.last L) ⟨L-d.val,by omega⟩
    let t := (slotOrder sdag hB b).val
    let jNat := (Finset.univ.filter (fun u : Fin (k+1) =>
      u < t ∧ (sdag u).val < L)).card
    have hj : jNat <= L := by
      let lo : Finset (Fin (k+1)) := Finset.univ.filter (fun u => (sdag u).val < L)
      have hc : lo.card = L := by
        have hh := Fintype.card_congr (slotOrder sdag hL).toEquiv.symm
        simpa [Slots, Fintype.card_subtype, lo] using hh
      have hs : (Finset.univ.filter (fun u : Fin (k+1) =>
          u < t ∧ (sdag u).val < L)) ⊆ lo := by
        intro u hu
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
        simp only [lo, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hu.2
      exact hc ▸ Finset.card_le_card hs
    let aLow := theta ⟨jNat,by omega⟩
    let eta := cut theta ⟨jNat,by omega⟩
    let s := replace sdag hL eta
    let a : Fin (k+2) := Fin.castLE (Nat.add_le_add_right hL 1) aLow
    exact (put s a t.castSucc,put p t 0)



theorem actual_full_left_composition {k L B : Nat} (hLB : L ≤ B) (hB : B ≤ k+1)
    (sigma : Equiv.Perm (Fin (k+2))) (pi : Equiv.Perm (Fin (k+1)))
    (ha : (sigma (pi 0).castSucc).val < L+1)
    (hc : (sigma (pi 0).succ).val < B+1) :
    let z := (actualAlgorithms hLB hB).phi sigma pi
    ∃ hd : z.2.1 < L+1, ∃ hb : z.2.2 < B,
      (actualAlgorithms hLB hB).psi z.1.1 z.1.2
        ⟨z.2.1,hd⟩ ⟨z.2.2,hb⟩ = (sigma,pi) := by
  classical
  have actual_column_recovery {k L B : Nat} (hLB : L ≤ B) (hB : B ≤ k+1)
      (sigma : Equiv.Perm (Fin (k+2))) (pi : Equiv.Perm (Fin (k+1)))
      (ha : (sigma (pi 0).castSucc).val < L+1)
      (hc : (sigma (pi 0).succ).val < B+1) :
      let z := (actualAlgorithms hLB hB).phi sigma pi
      ∃ hd : z.2.1 < L+1, ∃ hb : z.2.2 < B,
        ((actualAlgorithms hLB hB).psi z.1.1 z.1.2
          ⟨z.2.1,hd⟩ ⟨z.2.2,hb⟩).2 = pi := by
    classical
    let hL := hLB.trans hB
    let t := pi 0
    let a := sigma t.castSucc
    let s := cut sigma t.castSucc
    let p := cut pi 0
    let theta := lowWord sigma (Nat.add_le_add_right hL 1)
    let q := theta.symm (Fin.last L)
    let rho := cut theta q
    let sd := replace s hL rho
    let b := (Finset.univ.filter (fun u : Fin (k+1) => u < t ∧ (s u).val < B)).card
    have hs : (s t).val < B := by
      have he : a.succAbove (s t) = sigma t.succ := by
        have hh := (finSuccAboveEquiv a).apply_symm_apply
          ((Equiv.subtypeEquiv sigma (by intro x; exact sigma.injective.ne_iff.symm))
            ((finSuccAboveEquiv t.castSucc) t))
        have hv := congrArg Subtype.val hh
        change a.succAbove (s t) = sigma (t.castSucc.succAbove t) at hv
        simpa only [Fin.succAbove_of_le_castSucc _ _ le_rfl] using hv
      by_cases hh : (s t).castSucc < a
      · have hav : a.val ≤ B := by dsimp [a,t] at *; omega
        have hv : (s t).val < a.val := hh
        omega
      · have he' : (s t).val + 1 = (sigma t.succ).val := by
          simpa [Fin.succAbove_of_le_castSucc _ _ (le_of_not_gt hh)] using
            congrArg Fin.val he
        change (sigma t.succ).val < B+1 at hc
        omega
    have preserve (u : Fin (k+1)) : (sd u).val < B ↔ (s u).val < B := by
      by_cases hu : (s u).val < L
      · have hh : (sd u).val < L := by
          dsimp [sd, replace]
          rw [Equiv.Perm.ofSubtype_apply_of_mem (p := fun x : Fin (k+1) => x.val < L) (a := s u) _ hu]
          exact ((Equiv.permCongr (Fin.castLEOrderIso hL).toEquiv
            ((lowWord s hL).symm.trans rho)) ⟨s u,hu⟩).property
        exact iff_of_true (hh.trans_le hLB) (hu.trans_le hLB)
      · have hh : sd u = s u := by
          dsimp [sd, replace]
          rw [Equiv.Perm.ofSubtype_apply_of_not_mem (p := fun x : Fin (k+1) => x.val < L) (a := s u) _ hu]
        rw [hh]
    have hst : (sd t).val < B := (preserve t).mpr hs
    let e := slotOrder sd hB
    let r := e.symm ⟨t,hst⟩
    have hr : (Finset.univ.filter (fun u : Fin (k+1) =>
        u < t ∧ (sd u).val < B)).card = r.val := by
      rw [← Fin.card_Iio r]
      apply Finset.card_bij (fun u hu => e.symm ⟨u,(Finset.mem_filter.mp hu).2.2⟩)
      · intro u hu
        apply Finset.mem_Iio.mpr
        apply e.symm.lt_iff_lt.mpr
        exact (Finset.mem_filter.mp hu).2.1
      · intro u hu v hv huv
        have hh := congrArg (fun x => (e x).val) huv
        simpa using hh
      · intro v hv
        refine ⟨(e v).val, ?_, ?_⟩
        · apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_univ _, ?_, (e v).property⟩
          have hh := e.lt_iff_lt.mpr (Finset.mem_Iio.mp hv)
          rw [show e r = ⟨t,hst⟩ from e.apply_symm_apply _] at hh
          exact hh
        · exact e.symm_apply_apply v
    have hbr : b = r.val := by
      change (Finset.univ.filter (fun u : Fin (k+1) => u < t ∧ (s u).val < B)).card = _
      rw [← hr]
      apply congrArg Finset.card
      ext u
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [preserve]
    have hd : L - q.val < L+1 := by omega
    have hb : b < B := by rw [hbr]; exact r.isLt
    have recover : (slotOrder sd hB ⟨b,hb⟩).val = t := by
      have hh : (⟨b,hb⟩ : Fin B) = r := Fin.ext hbr
      rw [hh]
      exact congrArg Subtype.val (e.apply_symm_apply ⟨t,hst⟩)
    have ordinary : put p t 0 = pi := by
      ext x
      by_cases hx : x = 0
      · subst x
        simp [put,t]
      · obtain ⟨y,hy⟩ := (finSuccAboveEquiv (0 : Fin (k+1))).surjective ⟨x,hx⟩
        have hx' : x = (0 : Fin (k+1)).succAbove y := by
          simpa [finSuccAboveEquiv_apply] using congrArg Subtype.val hy.symm
        rw [hx']
        have hh := (finSuccAboveEquiv t).apply_symm_apply
          ((Equiv.subtypeEquiv pi (by intro x; exact pi.injective.ne_iff.symm))
            ((finSuccAboveEquiv (0 : Fin (k+1))) y))
        have he := congrArg Subtype.val hh
        change t.succAbove (p y) = pi ((0 : Fin (k+1)).succAbove y) at he
        change ((finSuccEquiv' t).symm ((Equiv.optionCongr p)
          ((finSuccEquiv' 0) ((0 : Fin (k+1)).succAbove y)))).val = _
        simpa only [finSuccEquiv'_succAbove, Equiv.optionCongr_apply,
          Option.map_some, finSuccEquiv'_symm_some] using congrArg Fin.val he
    change ∃ hd' : L-q.val < L+1, ∃ hb' : b < B,
      put p (slotOrder sd hB ⟨b,hb'⟩).val 0 = pi
    exact ⟨hd,hb,by rw [recover]; exact ordinary⟩

  have lowword_deletion_recovery {n L : Nat} (hL : L ≤ n)
      (sigma : Equiv.Perm (Fin (n+1))) (t : Fin (n+1))
      (ha : (sigma t).val < L+1) :
      let so := slotOrder sigma (Nat.add_le_add_right hL 1)
      let r := so.symm ⟨t,ha⟩
      lowWord (cut sigma t) hL = cut
        (lowWord sigma (Nat.add_le_add_right hL 1)) r := by
    exact (D5.S3.Combinatorics.Permutation.CoupledOrderedRecovery.shared_ordered_recovery (@cut) (@slotOrder) (@lowWord) (@replace)
      (by intros; rfl) (by intros; rfl) (by intros; rfl)).1 hL sigma t ha

  have repaired_count_recovers_deleted_label {k L B : Nat}
      (hLB : L ≤ B) (hB : B ≤ k+1)
      (sigma : Equiv.Perm (Fin (k+2))) (pi : Equiv.Perm (Fin (k+1)))
      (ha : (sigma (pi 0).castSucc).val < L+1) :
      let z := (actualAlgorithms hLB hB).phi sigma pi
      let j := (Finset.univ.filter (fun u : Fin (k+1) =>
        u < pi 0 ∧ (z.1.1 u).val < L)).card
      ∃ hj : j < L+1,
        (lowWord sigma (Nat.add_le_add_right (hLB.trans hB) 1) ⟨j,hj⟩).val =
          (sigma (pi 0).castSucc).val := by
    classical
    let hL := hLB.trans hB
    let hA := Nat.add_le_add_right hL 1
    let t := pi 0
    let a := sigma t.castSucc
    let s := cut sigma t.castSucc
    let theta := lowWord sigma hA
    let q := theta.symm (Fin.last L)
    let rho := cut theta q
    let sd := replace s hL rho
    let so := slotOrder sigma hA
    let r := so.symm ⟨t.castSucc,ha⟩
    have sor : so r = ⟨t.castSucc,ha⟩ := so.apply_symm_apply _
    have lift (u : Fin (k+1)) : a.succAbove (s u) = sigma (t.castSucc.succAbove u) := by
      have hh := (finSuccAboveEquiv a).apply_symm_apply
        ((Equiv.subtypeEquiv sigma (by intro x; exact sigma.injective.ne_iff.symm))
          ((finSuccAboveEquiv t.castSucc) u))
      exact congrArg Subtype.val hh
    have low (u : Fin (k+1)) : (sigma (t.castSucc.succAbove u)).val < L+1 ↔ (s u).val < L := by
      rw [← lift u]
      by_cases hu : (s u).castSucc < a
      · rw [Fin.succAbove_of_castSucc_lt _ _ hu]
        have hv : (s u).val < a.val := hu
        have hav : a.val < L+1 := ha
        simp only [Fin.val_castSucc]
        omega
      · rw [Fin.succAbove_of_le_castSucc _ _ (le_of_not_gt hu)]
        simp only [Fin.val_succ]
        omega
    have preserve (u : Fin (k+1)) : (sd u).val < L ↔ (s u).val < L := by
      by_cases hu : (s u).val < L
      · have hh : (sd u).val < L := by
          dsimp [sd,replace]
          rw [Equiv.Perm.ofSubtype_apply_of_mem
            (p := fun x : Fin (k+1) => x.val < L) (a := s u) _ hu]
          exact ((Equiv.permCongr (Fin.castLEOrderIso hL).toEquiv
            ((lowWord s hL).symm.trans rho)) ⟨s u,hu⟩).property
        exact iff_of_true hh hu
      · have hh : sd u = s u := by
          dsimp [sd,replace]
          rw [Equiv.Perm.ofSubtype_apply_of_not_mem
            (p := fun x : Fin (k+1) => x.val < L) (a := s u) _ hu]
        rw [hh]
    have before (u : Fin (k+1)) (hu : u < t) :
        (sigma u.castSucc).val < L+1 ↔ (s u).val < L := by
      simpa only [Fin.succAbove_of_castSucc_lt _ _
        (show u.castSucc < t.castSucc from hu)] using low u
    have rank : (Finset.univ.filter (fun u : Fin (k+1) =>
        u < t ∧ (s u).val < L)).card = r.val := by
      rw [← Fin.card_Iio r]
      apply Finset.card_bij (fun u hu => so.symm ⟨u.castSucc,
        (before u (Finset.mem_filter.mp hu).2.1).mpr (Finset.mem_filter.mp hu).2.2⟩)
      · intro u hu
        apply Finset.mem_Iio.mpr
        apply so.symm.lt_iff_lt.mpr
        exact (Finset.mem_filter.mp hu).2.1
      · intro u hu v hv hh
        have he := congrArg (fun i => (so i).val.val) hh
        exact Fin.ext (by simpa using he)
      · intro v hv
        have ht : (so v).val < t.castSucc := by
          have hh := so.lt_iff_lt.mpr (Finset.mem_Iio.mp hv)
          rw [sor] at hh
          exact hh
        let u : Fin (k+1) := ⟨(so v).val.val,by
          have hv' : (so v).val.val < t.val := ht
          exact hv'.trans t.isLt⟩
        have hu : u < t := ht
        have huc : u.castSucc = (so v).val := Fin.ext rfl
        have hlow : (s u).val < L := (before u hu).mp (huc ▸ (so v).property)
        refine ⟨u,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hu,hlow⟩,?_⟩
        apply so.injective
        rw [so.apply_symm_apply]
        exact Subtype.ext huc
    let j := (Finset.univ.filter (fun u : Fin (k+1) => u < t ∧ (sd u).val < L)).card
    have jr : j = r.val := by
      rw [← rank]
      change (Finset.univ.filter _).card = (Finset.univ.filter _).card
      apply congrArg Finset.card
      ext u
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [preserve]
    have hj : j < L+1 := by rw [jr]; exact r.isLt
    change ∃ hj' : j < L+1, (theta ⟨j,hj'⟩).val = a.val
    refine ⟨hj,?_⟩
    rw [show (⟨j,hj⟩ : Fin (L+1)) = r from Fin.ext jr]
    change (sigma (so r).val).val = a.val
    rw [sor]

  have repair {n T : Nat} (S : Equiv.Perm (Fin n)) (hT : T ≤ n)
      (rho : Equiv.Perm (Fin T)) :
      lowWord (replace S hT rho) hT = rho ∧
        replace (replace S hT rho) hT (lowWord S hT) = S := by
    exact (D5.S3.Combinatorics.Permutation.CoupledOrderedRecovery.shared_ordered_recovery (@cut) (@slotOrder) (@lowWord) (@replace)
      (by intros; rfl) (by intros; rfl) (by intros; rfl)).2 S hT rho

  have ordinary {n : Nat} (S : Equiv.Perm (Fin (n+1))) (t : Fin (n+1)) :
      put (cut S t) (S t) t = S := by
    apply Equiv.ext
    intro x
    by_cases hx : x = t
    · subst x
      simp [put]
    · obtain ⟨y,hy⟩ := (finSuccAboveEquiv t).surjective ⟨x,hx⟩
      have hx' : x = t.succAbove y :=
        congrArg Subtype.val hy.symm
      rw [hx']
      have hh := (finSuccAboveEquiv (S t)).apply_symm_apply
        ((Equiv.subtypeEquiv S (by intro x; exact S.injective.ne_iff.symm))
          ((finSuccAboveEquiv t) y))
      have he := congrArg Subtype.val hh
      change (S t).succAbove ((cut S t) y) = S (t.succAbove y) at he
      change (finSuccEquiv' (S t)).symm ((Equiv.optionCongr (cut S t))
        ((finSuccEquiv' t) (t.succAbove y))) = _
      simpa only [finSuccEquiv'_succAbove, Equiv.optionCongr_apply,
        Option.map_some, finSuccEquiv'_symm_some] using he
  let hL := hLB.trans hB
  let hA := Nat.add_le_add_right hL 1
  let t := pi 0
  let a := sigma t.castSucc
  let s := cut sigma t.castSucc
  let theta := lowWord sigma hA
  let q := theta.symm (Fin.last L)
  let rho := cut theta q
  let sd := replace s hL rho
  let z := (actualAlgorithms hLB hB).phi sigma pi
  obtain ⟨hd,hb,hcol⟩ := actual_column_recovery hLB hB sigma pi ha hc
  let td := (slotOrder sd hB ⟨z.2.2,hb⟩).val
  have htd : td = t := by
    have hfirst := congrArg (fun P : Equiv.Perm (Fin (k+1)) => P 0) hcol
    simpa [actualAlgorithms,put,td,t,z,sd,s,theta,q,rho] using hfirst
  let j := (Finset.univ.filter (fun u : Fin (k+1) => u < t ∧ (sd u).val < L)).card
  obtain ⟨hj,hlabel⟩ := repaired_count_recovers_deleted_label hLB hB sigma pi ha
  have hj' : j < L+1 := hj
  have hlabel' : (theta ⟨j,hj'⟩).val = a.val := hlabel
  let r := (slotOrder sigma hA).symm ⟨t.castSucc,ha⟩
  have thetar : theta r = ⟨a.val,ha⟩ := by
    apply Fin.ext
    change (sigma ((slotOrder sigma hA) r).val).val = a.val
    rw [(slotOrder sigma hA).apply_symm_apply]
  have jr : (⟨j,hj'⟩ : Fin (L+1)) = r :=
    theta.injective ((Fin.ext hlabel').trans thetar.symm)
  have sr : lowWord s hL = cut theta r :=
    lowword_deletion_recovery hL sigma t.castSucc ha
  have recoverTheta : put (lowWord sd hL) (Fin.last L) ⟨L-z.2.1,by omega⟩ = theta := by
    rw [(repair s hL rho).1]
    have hq : (⟨L-z.2.1,by omega⟩ : Fin (L+1)) = q := by
      apply Fin.ext
      change L-(L-q.val)=q.val
      have hq' := q.isLt
      omega
    rw [hq]
    have hmax : theta q = Fin.last L := theta.apply_symm_apply _
    rw [← hmax]
    exact ordinary theta q
  refine ⟨hd,hb,?_⟩
  apply Prod.ext
  · change put (replace sd hL
        (cut (put (lowWord sd hL) (Fin.last L) ⟨L-z.2.1,by omega⟩)
          ⟨(Finset.univ.filter (fun u : Fin (k+1) => u < td ∧ (sd u).val < L)).card,by simpa only [htd] using hj'⟩))
        (Fin.castLE hA ((put (lowWord sd hL) (Fin.last L) ⟨L-z.2.1,by omega⟩)
          ⟨(Finset.univ.filter (fun u : Fin (k+1) => u < td ∧ (sd u).val < L)).card,by simpa only [htd] using hj'⟩))
        td.castSucc = sigma
    simp only [htd,recoverTheta]
    change put (replace sd hL (cut theta ⟨j,hj'⟩))
      (Fin.castLE hA (theta ⟨j,hj'⟩)) t.castSucc = sigma
    rw [jr,← sr,(repair s hL rho).2,thetar]
    have hacast : Fin.castLE hA (⟨a.val,ha⟩ : Fin (L+1)) = a := Fin.ext rfl
    rw [hacast]
    exact ordinary sigma t.castSucc
  · exact hcol


end D5.S3.Combinatorics.Permutation.CoupledRepairedLeftInverse
