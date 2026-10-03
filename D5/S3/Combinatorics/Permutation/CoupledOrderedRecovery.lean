/- GID: D5/S3/Combinatorics/Permutation/CoupledOrderedRecovery
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Permutation/CoupledOrderedRecovery
   mirror-E: none(waiver:noncomputable-ordered-permutation-recovery)
   anchors: [mathlib/module/Mathlib.Logic.Equiv.Fin.Basic, mathlib/module/Mathlib.Data.Finset.Sort]
   utility: none
   digest: Increasing slot order recovers low-subword deletion and replacement. -/

import Mathlib
set_option autoImplicit false

namespace D5.S3.Combinatorics.Permutation.CoupledOrderedRecovery

set_option maxHeartbeats 1200000 in
theorem shared_ordered_recovery
    (cut : {n : Nat} → Equiv.Perm (Fin (n + 1)) → Fin (n + 1) → Equiv.Perm (Fin n))
    (slotOrder : {n T : Nat} → (sigma : Equiv.Perm (Fin n)) → T ≤ n →
      Fin T ≃o {u : Fin n // (sigma u).val < T})
    (lowWord : {n T : Nat} → Equiv.Perm (Fin n) → T ≤ n → Equiv.Perm (Fin T))
    (replace : {n T : Nat} → Equiv.Perm (Fin n) → T ≤ n →
      Equiv.Perm (Fin T) → Equiv.Perm (Fin n))
    (hcut : ∀ {n : Nat} (sigma : Equiv.Perm (Fin (n + 1))) (t : Fin (n + 1)),
      cut sigma t = (finSuccAboveEquiv t).trans
        ((Equiv.subtypeEquiv sigma (by intro x; exact sigma.injective.ne_iff.symm)).trans
          (finSuccAboveEquiv (sigma t)).symm))
    (hword : ∀ {n T : Nat} (sigma : Equiv.Perm (Fin n)) (hT : T ≤ n),
      lowWord sigma hT = (slotOrder sigma hT).toEquiv.trans
        ((Equiv.subtypeEquiv sigma (by intro x; rfl)).trans
          (Fin.castLEOrderIso hT).symm.toEquiv))
    (hreplace : ∀ {n T : Nat} (sigma : Equiv.Perm (Fin n)) (hT : T ≤ n)
        (rho : Equiv.Perm (Fin T)),
      replace sigma hT rho = sigma.trans (Equiv.permCongr (Fin.castLEOrderIso hT).toEquiv
        ((lowWord sigma hT).symm.trans rho)).ofSubtype) :
    (∀ {n L : Nat} (hL : L ≤ n) (sigma : Equiv.Perm (Fin (n + 1))) (t : Fin (n + 1))
      (ha : (sigma t).val < L + 1),
      let so := slotOrder sigma (Nat.add_le_add_right hL 1)
      let r := so.symm ⟨t,ha⟩
      lowWord (cut sigma t) hL = cut (lowWord sigma (Nat.add_le_add_right hL 1)) r) ∧
    (∀ {n T : Nat} (S : Equiv.Perm (Fin n)) (hT : T ≤ n) (rho : Equiv.Perm (Fin T)),
      lowWord (replace S hT rho) hT = rho ∧
        replace (replace S hT rho) hT (lowWord S hT) = S) := by
  classical
  let Slots {n : Nat} (sigma : Equiv.Perm (Fin n)) (T : Nat) :=
    {u : Fin n // (sigma u).val < T}
  have lowword_deletion_recovery {n L : Nat} (hL : L ≤ n)
      (sigma : Equiv.Perm (Fin (n + 1))) (t : Fin (n + 1))
      (ha : (sigma t).val < L + 1) :
      let so := slotOrder sigma (Nat.add_le_add_right hL 1)
      let r := so.symm ⟨t,ha⟩
      lowWord (cut sigma t) hL = cut
        (lowWord sigma (Nat.add_le_add_right hL 1)) r := by
    classical
    let hA := Nat.add_le_add_right hL 1
    let a := sigma t
    let s := cut sigma t
    let so := slotOrder sigma hA
    let r := so.symm ⟨t,ha⟩
    let theta := lowWord sigma hA
    have lift (u : Fin n) : a.succAbove (s u) = sigma (t.succAbove u) := by
      dsimp only [s]
      rw [hcut]
      have hh := (finSuccAboveEquiv a).apply_symm_apply
        ((Equiv.subtypeEquiv sigma (by intro x; exact sigma.injective.ne_iff.symm))
          ((finSuccAboveEquiv t) u))
      exact congrArg Subtype.val hh
    have low (u : Fin n) : (sigma (t.succAbove u)).val < L + 1 ↔ (s u).val < L := by
      rw [← lift u]
      by_cases hu : (s u).castSucc < a
      · rw [Fin.succAbove_of_castSucc_lt _ _ hu]
        have hv : (s u).val < a.val := hu
        have hav : a.val < L + 1 := ha
        simp only [Fin.val_castSucc]
        omega
      · rw [Fin.succAbove_of_le_castSucc _ _ (le_of_not_gt hu)]
        simp only [Fin.val_succ]
        omega
    have sor : so r = ⟨t,ha⟩ := so.apply_symm_apply _
    let F : Slots s L → {v : Slots sigma (L + 1) // v ≠ so r} := fun u =>
      ⟨⟨t.succAbove u.val, (low u.val).mpr u.property⟩, by
        intro hh
        have hv := congrArg Subtype.val hh
        rw [sor] at hv
        exact t.succAbove_ne u.val hv⟩
    have hF : Function.Bijective F := by
      constructor
      · intro u v hh
        apply Subtype.ext
        apply (Fin.strictMono_succAbove t).injective
        exact congrArg (fun x => x.val.val) hh
      · intro v
        have hv : v.val.val ≠ t := by
          intro hh
          apply v.property
          exact (Subtype.ext hh).trans sor.symm
        let u := (finSuccAboveEquiv t).symm ⟨v.val.val,hv⟩
        have he : t.succAbove u = v.val.val :=
          congrArg Subtype.val ((finSuccAboveEquiv t).apply_symm_apply ⟨v.val.val,hv⟩)
        have hu : (s u).val < L := (low u).mp (he ▸ v.val.property)
        refine ⟨⟨u,hu⟩, ?_⟩
        apply Subtype.ext
        exact Subtype.ext he
    let E : Slots s L ≃o {v : Slots sigma (L + 1) // v ≠ so r} :=
      { __ := Equiv.ofBijective F hF
        map_rel_iff' := by intro u v; exact Fin.succAbove_le_succAbove_iff }
    let R : {i : Fin (L + 1) // i ≠ r} ≃o {v : Slots sigma (L + 1) // v ≠ so r} :=
      { __ := Equiv.subtypeEquiv so.toEquiv (by intro i; exact so.injective.ne_iff.symm)
        map_rel_iff' := by intro u v; exact so.le_iff_le }
    have orderRecovery : (slotOrder s hL).trans E = (finSuccAboveOrderIso r).trans R :=
      Subsingleton.elim _ _
    have slots (i : Fin L) : t.succAbove ((slotOrder s hL i).val) =
        (so (r.succAbove i)).val := by
      exact congrArg (fun e => (e i).val.val) orderRecovery
    have thetar : theta r = ⟨a.val,ha⟩ := by
      apply Fin.ext
      dsimp only [theta]
      rw [hword]
      change (sigma (so r).val).val = a.val
      rw [sor]
    have cutlift (i : Fin L) : (theta r).succAbove ((cut theta r) i) =
        theta (r.succAbove i) := by
      rw [hcut]
      have hh := (finSuccAboveEquiv (theta r)).apply_symm_apply
        ((Equiv.subtypeEquiv theta (by intro x; exact theta.injective.ne_iff.symm))
          ((finSuccAboveEquiv r) i))
      exact congrArg Subtype.val hh
    change lowWord s hL = cut theta r
    rw [hword]
    apply Equiv.ext
    intro i
    apply Fin.ext
    have hleft := congrArg Fin.val (lift (slotOrder s hL i).val)
    rw [slots i] at hleft
    have hright := congrArg Fin.val (cutlift i)
    have theta_read : ∀ x, (theta x).val = (sigma (so x).val).val := by
      intro x
      dsimp only [theta]
      rw [hword]
      rfl
    rw [← theta_read] at hleft
    rw [thetar] at hright
    change (a.succAbove (s (slotOrder s hL i).val)).val =
      (theta (r.succAbove i)).val at hleft
    have eqLift := hleft.trans hright.symm
    by_cases hl : (s (slotOrder s hL i).val).val < a.val
    · have hr : ((cut theta r) i).val < a.val := by
        by_contra hn
        rw [Fin.succAbove_of_castSucc_lt _ _ (show
          (s (slotOrder s hL i).val).castSucc < a from hl)] at eqLift
        rw [Fin.succAbove_of_le_castSucc _ _ (show
          (⟨a.val,ha⟩ : Fin (L + 1)) ≤ ((cut theta r) i).castSucc from le_of_not_gt hn)] at eqLift
        simp only [Fin.val_castSucc, Fin.val_succ] at eqLift
        omega
      rw [Fin.succAbove_of_castSucc_lt _ _ (show
        (s (slotOrder s hL i).val).castSucc < a from hl),
        Fin.succAbove_of_castSucc_lt _ _ (show
        ((cut theta r) i).castSucc < (⟨a.val,ha⟩ : Fin (L + 1)) from hr)] at eqLift
      exact eqLift
    · have hr : a.val ≤ ((cut theta r) i).val := by
        by_contra hn
        rw [Fin.succAbove_of_le_castSucc _ _ (show
          a ≤ (s (slotOrder s hL i).val).castSucc from le_of_not_gt hl)] at eqLift
        rw [Fin.succAbove_of_castSucc_lt _ _ (show
          ((cut theta r) i).castSucc < (⟨a.val,ha⟩ : Fin (L + 1)) from lt_of_not_ge hn)] at eqLift
        simp only [Fin.val_castSucc, Fin.val_succ] at eqLift
        omega
      rw [Fin.succAbove_of_le_castSucc _ _ (show
        a ≤ (s (slotOrder s hL i).val).castSucc from le_of_not_gt hl),
        Fin.succAbove_of_le_castSucc _ _ (show
        (⟨a.val,ha⟩ : Fin (L + 1)) ≤ ((cut theta r) i).castSucc from hr)] at eqLift
      simp only [Fin.val_succ] at eqLift
      exact Nat.add_right_cancel eqLift
  have repair {n T : Nat} (S : Equiv.Perm (Fin n)) (hT : T ≤ n)
      (rho : Equiv.Perm (Fin T)) :
      lowWord (replace S hT rho) hT = rho ∧
        replace (replace S hT rho) hT (lowWord S hT) = S := by
    let sd := replace S hT rho
    have lowapply (u : Fin n) (hu : (S u).val < T) :
        (sd u).val = (rho ((lowWord S hT).symm ⟨(S u).val,hu⟩)).val := by
      dsimp only [sd]
      rw [hreplace]
      dsimp only [Equiv.trans_apply]
      rw [Equiv.Perm.ofSubtype_apply_of_mem
        (p := fun x : Fin n => x.val < T) (a := S u) _ hu]
      rfl
    have preserve (u : Fin n) : (sd u).val < T ↔ (S u).val < T := by
      by_cases hu : (S u).val < T
      · rw [lowapply u hu]
        exact iff_of_true (rho _).isLt hu
      · have hh : sd u = S u := by
          dsimp only [sd]
          rw [hreplace]
          dsimp only [Equiv.trans_apply]
          rw [Equiv.Perm.ofSubtype_apply_of_not_mem
            (p := fun x : Fin n => x.val < T) (a := S u) _ hu]
        rw [hh]
    let E : Slots sd T ≃o Slots S T := OrderIso.setCongr _ _ (by
      ext u
      exact preserve u)
    have orders : (slotOrder sd hT).trans E = slotOrder S hT := Subsingleton.elim _ _
    have slots (i : Fin T) : (slotOrder sd hT i).val = (slotOrder S hT i).val :=
      congrArg (fun e => (e i).val) orders
    have read : lowWord sd hT = rho := by
      apply Equiv.ext
      intro i
      apply Fin.ext
      rw [hword]
      change (sd (slotOrder sd hT i).val).val = (rho i).val
      rw [slots i, lowapply _ (slotOrder S hT i).property]
      have hw : (S (slotOrder S hT i).val).val = ((lowWord S hT) i).val := by
        rw [hword]
        rfl
      have hwfin : (⟨(S (slotOrder S hT i).val).val,(slotOrder S hT i).property⟩ : Fin T) =
          lowWord S hT i := Fin.ext hw
      rw [hwfin,Equiv.symm_apply_apply]
    refine ⟨read,?_⟩
    rw [hreplace]
    apply Equiv.ext
    intro u
    apply Fin.ext
    by_cases hu : (S u).val < T
    · have hsu : (sd u).val < T := (preserve u).mpr hu
      change ((Equiv.permCongr (Fin.castLEOrderIso hT).toEquiv
        ((lowWord sd hT).symm.trans (lowWord S hT))).ofSubtype (sd u)).val = (S u).val
      rw [Equiv.Perm.ofSubtype_apply_of_mem
        (p := fun x : Fin n => x.val < T) (a := sd u) _ hsu]
      rw [read]
      change ((lowWord S hT) (rho.symm ⟨(sd u).val,hsu⟩)).val = (S u).val
      have hs : (⟨(sd u).val,hsu⟩ : Fin T) =
          rho ((lowWord S hT).symm ⟨(S u).val,hu⟩) := Fin.ext (lowapply u hu)
      rw [hs,Equiv.symm_apply_apply,Equiv.apply_symm_apply]
    · have hsu : ¬(sd u).val < T := fun hh => hu ((preserve u).mp hh)
      change ((Equiv.permCongr (Fin.castLEOrderIso hT).toEquiv
        ((lowWord sd hT).symm.trans (lowWord S hT))).ofSubtype (sd u)).val = (S u).val
      rw [Equiv.Perm.ofSubtype_apply_of_not_mem
        (p := fun x : Fin n => x.val < T) (a := sd u) _ hsu]
      dsimp only [sd]
      rw [hreplace]
      dsimp only [Equiv.trans_apply]
      rw [Equiv.Perm.ofSubtype_apply_of_not_mem
        (p := fun x : Fin n => x.val < T) (a := S u) _ hu]
  exact ⟨lowword_deletion_recovery,repair⟩

end D5.S3.Combinatorics.Permutation.CoupledOrderedRecovery
