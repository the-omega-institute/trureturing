/- GID: D5/S3/ObserverMemory/ContextUpdates/CyclicSelectorRecovery
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/ContextUpdates/CyclicSelectorRecovery
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.ZMod.Basic]
   utility: none
   digest: Actual cyclic selector runs and recovery of labelled group sources. -/

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Finset.Max
import D5.S3.ObserverMemory.RefinementClosure.FiniteHorizonKernelRecurrence
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.GroupTheory.Index
import D5.S3.ObserverMemory.PredictionCertificates.LocalCertificateMinimality

import D5.S3.ObserverMemory.ContextUpdates.CyclicSelectorModel
namespace D5.S3.ObserverMemory.ContextUpdates.CyclicSelectorRecovery

open scoped BigOperators
set_option autoImplicit false


theorem cyclic_selector_recovery (m r : ℕ) [NeZero m] (hm : 2 ≤ m)
    (heven : Even m) (hr : 3 ≤ r) (f : ZMod m → ZMod 2) :
    ((((∃ x y, f x ≠ f y) →
    ∃ e : ZMod m ≃ RunPosition f,
      (∀ p, e.symm p = p.1.val + (p.2.val : ZMod m)) ∧
      (∀ z, (e z).1.val = z - ((beta f z-1 : ℕ) : ZMod m) ∧
        (e z).2.val = beta f z-1) ∧
      (∀ p, delta f (e.symm p) = delta f p.1.val - p.2.val) ∧
      (∀ z, 1 ≤ delta f z ∧ delta f z ≤ m-1) ∧
      (∀ n : ℕ, Nat.card {z : ZMod m //
        ∀ j : ℕ, j ≤ n → f (z+(j : ZMod m)) = f z} =
        ∑ s : RunStart f, (delta f s.val-n)) ∧
      (∃ L : ℕ, 1 ≤ L ∧ L ≤ m-1 ∧
        (∀ z : ZMod m, delta f z ≤ L) ∧
        (∀ j : ℕ, 1 ≤ j → j ≤ L → ∃ z : ZMod m, delta f z = j) ∧
        (∀ n : ℕ, (∀ z : ZMod m, ¬ (∀ j : ℕ, j ≤ n →
          f (z+(j : ZMod m)) = f z)) ↔ L ≤ n))) ∧
    (∀ s : Source m r, ∀ j : ℕ, clock (advance j s) = clock s) ∧
    (∀ s : Source m r, ∀ p q : ℕ,
      f (s.1.1.2+(p : ZMod m)) ≠ f (s.1.1.2+(q : ZMod m)) →
      recover f p q (observe f (advance p s)) (observe f (advance q s)) = s) ∧
    (∀ s t : Source m r, observe f s = observe f t → ∀ n : ℕ,
      trace f n s = trace f n t ↔ s = t ∨
        ∀ j : ℕ, j ≤ n → f (s.1.1.2+(j : ZMod m)) = f s.1.1.2) ∧
    (∀ s : Source m r, ∀ j : ℕ,
      f (s.1.1.2+(j : ZMod m)) = f s.1.1.2 →
      observe f (advance j s) =
        (s.1.1+(0,(j : ZMod m)),clock s,fun i =>
          (observe f s).2.2 i - if i.val = 0 then (0,(j : ZMod m)) else 0)) ∧
    (∀ z : ZMod m, baseSource m r z ≠ flipSource m r hr f z ∧
      observe f (baseSource m r z) = observe f (flipSource m r hr f z) ∧
      (∀ n : ℕ, trace f n (baseSource m r z) = trace f n (flipSource m r hr f z) ↔
        ∀ j : ℕ, j ≤ n → f (z+(j : ZMod m)) = f z)) ∧
    (∀ j : ℕ, ∀ s : Source m r, ((advance 1)^[j]) s = advance j s) ∧
    (∀ a t : Group m, ∀ u : Fin (r-1) → ZMod m,
      (∀ bits : Fin (r-1) → ZMod 2, (∑ i, bits i) = t.1-a.1 →
        observe f (fiberSource f a t u bits) = (a,t,fun i => (0,u i))) ∧
      (∀ s : Source m r, observe f s = (a,t,fun i => (0,u i)) →
        (∑ i, (s.1.2 i).1) = t.1-a.1 ∧
        fiberSource f a t u (fun i => (s.1.2 i).1) = s) ∧
      (∃ s : Source m r, observe f s = (a,t,fun i => (0,u i))))) ∧
    ((∀ a t : Group m, ∀ u : Fin (r-1) → ZMod m,
      Nat.card {s : Source m r // observe f s = (a,t,fun i => (0,u i))} = 2^(r-2)) ∧
    (∀ z : ZMod m, Nat.card {o : Snapshot m r // o.1.2 = z ∧
      ∃ s : Source m r, observe f s = o} = 4*m^r) ∧
    (∀ n : ℕ, traceClassCount (r := r) f n =
      4*m^r * (2^(r-2)*m - (2^(r-2)-1)*windowCount f n)) ∧
    traceClassCount (r := r) f 0 = 4*m^(r+1) ∧
    Nat.card (Source m r) = 2^r*m^(r+1))) ∧
    (∀ p q : ℕ, ∀ A B : Snapshot m r,
      (recoverArithmetic f p q A B).1 = recover f p q A B ∧
      (recoverArithmetic f p q A B).2.1 = 5*(r-1)+3 ∧
      (recoverArithmetic f p q A B).2.2 = 3*(r-1)+1 ∧
      (recoverArithmetic f p q A B).2.1 ≤ 5*r ∧
      (recoverArithmetic f p q A B).2.2 ≤ 3*r) := by
  have core := cyclic_selector_source_geometry m r hm heven hr f
  have cardinalities :
    (∀ a t : Group m, ∀ u : Fin (r-1) → ZMod m,
      Nat.card {s : Source m r // observe f s = (a,t,fun i => (0,u i))} = 2^(r-2)) ∧
    (∀ z : ZMod m, Nat.card {o : Snapshot m r // o.1.2 = z ∧
      ∃ s : Source m r, observe f s = o} = 4*m^r) ∧
    (∀ n : ℕ, traceClassCount (r := r) f n =
      4*m^r * (2^(r-2)*m - (2^(r-2)-1)*windowCount f n)) ∧
    traceClassCount (r := r) f 0 = 4*m^(r+1) ∧
    Nat.card (Source m r) = 2^r*m^(r+1) := by
    classical
    have main := core
    have fibers := main.2.2.2.2.2.2.2
    let pack : HSnapshot m r → Snapshot m r := fun o => (o.1,o.2.1,fun i => (0,o.2.2 i))
    let obs : Source m r → HSnapshot m r := fun s => (s.1.1,clock s,fun i => ((observe f s).2.2 i).2)
    have projectZero (s : Source m r) (i : Fin (r-1)) : ((observe f s).2.2 i).1 = 0 := by
      dsimp only [observe,project]
      split_ifs with hb
      · simpa only [Prod.fst_sub,Prod.fst_zero,sub_zero] using hb
      · change (s.1.2 i).1 - 1 = 0
        generalize (s.1.2 i).1 = bit at hb ⊢
        fin_cases bit
        · exact (hb rfl).elim
        · exact sub_self _
    have packed (s : Source m r) : pack (obs s) = observe f s := by
      apply Prod.ext
      · rfl
      · apply Prod.ext
        · rfl
        · funext i
          exact Prod.ext (projectZero s i).symm rfl
    have packInj : Function.Injective pack := by
      intro o p h
      apply Prod.ext
      · exact congrArg (fun o : Snapshot m r => o.1) h
      · apply Prod.ext
        · exact congrArg (fun o : Snapshot m r => o.2.1) h
        · funext i
          exact congrArg (fun o : Snapshot m r => (o.2.2 i).2) h
    have obsSurj : Function.Surjective obs := by
      intro o
      obtain ⟨s,hs⟩ := (fibers o.1 o.2.1 o.2.2).2.2
      exact ⟨s,packInj ((packed s).trans hs)⟩
    let Bits := fun o : HSnapshot m r =>
      {b : Fin (r-1) → ZMod 2 // (∑ i, b i) = o.2.1.1-o.1.1}
    have bitsCard (o : HSnapshot m r) : Nat.card (Bits o) = 2^(r-2) := by
      let sigma : (Fin (r-1) → ZMod 2) →+ ZMod 2 :=
        { toFun := fun b => ∑ i, b i
          map_zero' := by simp
          map_add' := by intros; simp [Finset.sum_add_distrib] }
      let i0 : Fin (r-1) := ⟨0,by omega⟩
      have surj : Function.Surjective sigma := by
        intro b
        exact ⟨Pi.single i0 b,by simp [sigma]⟩
      have h := sigma.ker.card_mul_index
      rw [AddSubgroup.index_ker,sigma.range_eq_top.mpr surj] at h
      have h' : Nat.card sigma.ker * 2 = 2^(r-1) := by
        simpa [Nat.card_eq_fintype_card,Fintype.card_fun] using h
      have hc : Nat.card sigma.ker = 2^(r-2) := by
        apply Nat.eq_of_mul_eq_mul_right (by decide : 0 < 2)
        rw [h',← pow_succ]
        congr 1
        omega
      have hf := AddMonoidHom.card_fiber_eq_of_mem_range sigma
        (x := o.2.1.1-o.1.1) (y := 0)
        (by obtain ⟨b,hb⟩ := surj (o.2.1.1-o.1.1); exact ⟨b,hb⟩)
        (by exact ⟨0,map_zero sigma⟩)
      have hf' : Nat.card (Bits o) = Nat.card sigma.ker := by
        simpa [Bits,sigma,Nat.card_eq_fintype_card,Fintype.card_subtype] using hf
      exact hf'.trans hc
    let fiberEquiv (o : HSnapshot m r) :
        {s : Source m r // observe f s = pack o} ≃ Bits o :=
      { toFun := fun s => ⟨fun i => (s.val.1.2 i).1,
          ((fibers o.1 o.2.1 o.2.2).2.1 s.val s.property).1⟩
        invFun := fun b => ⟨fiberSource f o.1 o.2.1 o.2.2 b.val,
          (fibers o.1 o.2.1 o.2.2).1 b.val b.property⟩
        left_inv := by
          intro s
          apply Subtype.ext
          exact ((fibers o.1 o.2.1 o.2.2).2.1 s.val s.property).2
        right_inv := by
          intro b
          apply Subtype.ext
          funext i
          change (((0,o.2.2 i) : Group m) +
            if b.val i = 0 then 0 else selector m (f o.1.2)).1 = b.val i
          by_cases hb : b.val i = 0
          · rw [if_pos hb]
            simpa using hb.symm
          · rw [if_neg hb]
            change 1 = b.val i
            generalize b.val i = bit at hb ⊢
            fin_cases bit
            · exact (hb rfl).elim
            · rfl }
    have fiberCard (o : HSnapshot m r) :
        Nat.card {s : Source m r // observe f s = pack o} = 2^(r-2) :=
      (Nat.card_congr (fiberEquiv o)).trans (bitsCard o)
    have phaseEquiv (z : ZMod m) :
        {o : Snapshot m r // o.1.2 = z ∧ ∃ s : Source m r, observe f s = o} ≃
        (ZMod 2 × Group m × (Fin (r-1) → ZMod m)) :=
      { toFun := fun o => (o.val.1.1,o.val.2.1,fun i => (o.val.2.2 i).2)
        invFun := fun p => ⟨pack ((p.1,z),p.2.1,p.2.2),rfl,by
          obtain ⟨s,hs⟩ := obsSurj ((p.1,z),p.2.1,p.2.2)
          exact ⟨s,by rw [← packed s,hs]⟩⟩
        left_inv := by
          intro o
          apply Subtype.ext
          obtain ⟨s,hs⟩ := o.property.2
          apply Prod.ext
          · exact Prod.ext rfl o.property.1.symm
          · apply Prod.ext
            · rfl
            · funext i
              exact Prod.ext (by rw [← hs]; exact (projectZero s i).symm) rfl
        right_inv := by intro p; rfl }
    have phaseCard (z : ZMod m) : Nat.card {o : Snapshot m r // o.1.2 = z ∧
        ∃ s : Source m r, observe f s = o} = 4*m^r := by
      rw [Nat.card_congr (phaseEquiv z)]
      simp only [Nat.card_eq_fintype_card,Fintype.card_prod,Fintype.card_fun,
        ZMod.card,Fintype.card_fin]
      have hp : m^r = m^(r-1)*m := by
        conv_lhs => rw [show r = (r-1)+1 from by omega]
        rw [pow_succ]
      rw [hp]
      ring
    have counts (n : ℕ) : traceClassCount (r := r) f n =
        4*m^r * (2^(r-2)*m - (2^(r-2)-1)*windowCount f n) := by
      let W := constantWindow f n
      let RawBits := Fin (r-1) → ZMod 2
      let Valid := fun (o : HSnapshot m r) (b : Option RawBits) =>
        if W o.1.2 then b = none else ∃ bit : Bits o, b = some bit.val
      let Label := {p : HSnapshot m r × Option RawBits // Valid p.1 p.2}
      let label : Source m r → Label := fun s =>
        ⟨(obs s,if W s.1.1.2 then none else some (fun i => (s.1.2 i).1)),by
          dsimp only [Valid,obs]
          by_cases hw : W s.1.1.2
          · simp [hw]
          · simp only [if_neg hw]
            exact ⟨(fiberEquiv (obs s)) ⟨s,(packed s).symm⟩,rfl⟩⟩
      have labelSurj : Function.Surjective label := by
        rintro ⟨⟨o,b⟩,hb⟩
        by_cases hw : W o.1.2
        · have hb' : b = none := by simpa [Valid,hw] using hb
          obtain ⟨s,hs⟩ := obsSurj o
          refine ⟨s,Subtype.ext ?_⟩
          apply Prod.ext hs
          have hw' : W s.1.1.2 := by change W (obs s).1.2; rw [hs]; exact hw
          change (if W s.1.1.2 then none else some (fun i => (s.1.2 i).1)) = b
          rw [if_pos hw',hb']
        · obtain ⟨bit,hbit⟩ : ∃ bit : Bits o, b = some bit.val := by simpa [Valid,hw] using hb
          let s := (fiberEquiv o).symm bit
          have hs : obs s.val = o := packInj ((packed s.val).trans s.property)
          have hsbit : (fun i => (s.val.1.2 i).1) = bit.val :=
            by simpa [fiberEquiv,s] using congrArg Subtype.val ((fiberEquiv o).apply_symm_apply bit)
          refine ⟨s.val,Subtype.ext ?_⟩
          apply Prod.ext hs
          have hw' : ¬W s.val.1.1.2 := by change ¬W (obs s.val).1.2; rw [hs]; exact hw
          change (if W s.val.1.1.2 then none else some (fun i => (s.val.1.2 i).1)) = b
          rw [if_neg hw',hsbit,hbit]
      have labelKernel (s t : Source m r) : label s = label t ↔ trace f n s = trace f n t := by
        have traceObs (ht : trace f n s = trace f n t) : observe f s = observe f t := by
          have h := congrFun ht ⟨0,by omega⟩
          have hz (s : Source m r) : advance 0 s = s := by
            have hz : ((0,(0 : ZMod m)) : Group m) = 0 := rfl
            simp only [advance,Nat.cast_zero,hz,ite_self,sub_zero,add_zero]
          simpa only [trace,hz] using h
        constructor
        · intro hl
          have ho : obs s = obs t := congrArg (fun p : Label => p.val.1) hl
          have hobs := (packed s).symm.trans ((congrArg pack ho).trans (packed t))
          apply (main.2.2.2.1 s t hobs n).mpr
          by_cases hw : W s.1.1.2
          · exact Or.inr hw
          · left
            have ha : s.1.1 = t.1.1 := congrArg (fun o : HSnapshot m r => o.1) ho
            have ht : ¬W t.1.1.2 := by rw [← ha]; exact hw
            have hb := congrArg (fun p : Label => p.val.2) hl
            change (if W s.1.1.2 then none else some (fun i => (s.1.2 i).1)) =
              (if W t.1.1.2 then none else some (fun i => (t.1.2 i).1)) at hb
            rw [if_neg hw,if_neg ht] at hb
            have hbits := Option.some.inj hb
            have hs := (fibers (obs s).1 (obs s).2.1 (obs s).2.2).2.1 s (packed s).symm
            have ht := (fibers (obs s).1 (obs s).2.1 (obs s).2.2).2.1 t (hobs.symm.trans (packed s).symm)
            rw [← hs.2,← ht.2,hbits]
        · intro ht
          have hobs := traceObs ht
          have ho : obs s = obs t := packInj ((packed s).trans (hobs.trans (packed t).symm))
          rcases (main.2.2.2.1 s t hobs n).mp ht with h | hw
          · subst t; rfl
          · apply Subtype.ext
            apply Prod.ext ho
            have ha : s.1.1 = t.1.1 := congrArg (fun o : HSnapshot m r => o.1) ho
            have ht : W t.1.1.2 := by rw [← ha]; exact hw
            change (if W s.1.1.2 then none else some (fun i => (s.1.2 i).1)) =
              (if W t.1.1.2 then none else some (fun i => (t.1.2 i).1))
            have hws : W s.1.1.2 := hw
            rw [if_pos hws,if_pos ht]
      have e := D5.S3.ObserverMemory.PredictionCertificates.LocalCertificateMinimality.quotientEquivOfExactKernel
        label (trace f n) labelSurj labelKernel
      change Nat.card (Quotient (Setoid.ker (trace f n))) = _
      rw [← Nat.card_congr e]
      have labelCard (o : HSnapshot m r) :
          Nat.card {b : Option RawBits // Valid o b} = if W o.1.2 then 1 else 2^(r-2) := by
        by_cases hw : W o.1.2
        · simp [Valid,hw,Nat.card_eq_fintype_card]
        · let e : Bits o ≃ {b : Option RawBits // Valid o b} :=
            { toFun := fun bit => ⟨some bit.val,by simp [Valid,hw]⟩
              invFun := fun b => (show ∃ bit : Bits o, b.val = some bit.val from by
                simpa [Valid,hw] using b.property).choose
              left_inv := by
                intro bit
                apply Subtype.ext
                exact (Option.some.inj (show ∃ chosen : Bits o, some bit.val = some chosen.val from
                  ⟨bit,rfl⟩).choose_spec).symm
              right_inv := by
                intro b
                apply Subtype.ext
                exact (show ∃ bit : Bits o, b.val = some bit.val from by
                  simpa [Valid,hw] using b.property).choose_spec.symm }
          rw [if_neg hw,← Nat.card_congr e]
          exact bitsCard o
      let splitEquiv : Label ≃ ((o : HSnapshot m r) × {b : Option RawBits // Valid o b}) :=
        { toFun := fun p => ⟨p.val.1,⟨p.val.2,p.property⟩⟩
          invFun := fun p => ⟨(p.1,p.2.val),p.2.property⟩
          left_inv := by intro p; rfl
          right_inv := by intro p; rfl }
      have hw : (Finset.univ.filter W).card = windowCount f n := by
        simp [windowCount,W,Nat.card_eq_fintype_card,Fintype.card_subtype]
      have hn : (Finset.univ.filter (fun z => ¬W z)).card = m-windowCount f n := by
        have h := Finset.card_filter_add_card_filter_not (s := Finset.univ) W
        rw [hw,Finset.card_univ,ZMod.card] at h
        omega
      have phaseSum : (∑ z : ZMod m, if W z then (1 : ℕ) else 2^(r-2)) =
          windowCount f n + 2^(r-2)*(m-windowCount f n) := by
        rw [Finset.sum_ite]
        simp only [Finset.sum_const,nsmul_eq_mul]
        rw [hw,hn]
        simp only [Nat.cast_id]
        ring
      have split : Nat.card Label =
          4*m^r * (windowCount f n + 2^(r-2)*(m-windowCount f n)) := by
        rw [Nat.card_congr splitEquiv,Nat.card_eq_fintype_card,Fintype.card_sigma]
        simp_rw [← Nat.card_eq_fintype_card,labelCard]
        dsimp [HSnapshot,Group]
        simp_rw [Fintype.sum_prod_type]
        change (∑ b : ZMod 2, ∑ z : ZMod m, ∑ tb : ZMod 2, ∑ tz : ZMod m,
          ∑ u : Fin (r-1) → ZMod m, if W z then (1 : ℕ) else 2^(r-2)) = _
        simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fun,
          ZMod.card,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id]
        try simp_rw [← mul_assoc]
        try simp_rw [← Finset.mul_sum]
        rw [phaseSum]
        have hp : m^r = m^(r-1)*m := by
          conv_lhs => rw [show r = (r-1)+1 from by omega]
          rw [pow_succ]
        rw [hp]
        ring
      rw [split]
      have bound : windowCount f n ≤ m := by
        simpa [windowCount,Nat.card_eq_fintype_card] using Fintype.card_subtype_le (constantWindow f n)
      have qpos : 1 ≤ 2^(r-2) := Nat.one_le_pow _ _ (by omega)
      have hs : windowCount f n + 2^(r-2)*(m-windowCount f n) =
          2^(r-2)*m-(2^(r-2)-1)*windowCount f n := by
        have h1 := Nat.sub_add_cancel bound
        have h2 := Nat.sub_add_cancel qpos
        have hle : (2^(r-2)-1)*windowCount f n ≤ 2^(r-2)*m :=
          Nat.mul_le_mul (Nat.sub_le _ _) bound
        symm
        apply (Nat.sub_eq_iff_eq_add hle).mpr
        nlinarith
      rw [hs]
    refine ⟨fun a t u => fiberCard (a,t,u),phaseCard,counts,?_,?_⟩
    · rw [counts]
      have h0 : windowCount f 0 = m := by
        simp [windowCount,constantWindow,Nat.card_eq_fintype_card]
      rw [h0,pow_succ]
      have hq : 1 ≤ 2^(r-2) := Nat.one_le_pow _ _ (by omega)
      have h := Nat.sub_add_cancel hq
      have hs : 2^(r-2)*m-(2^(r-2)-1)*m = m := by
        apply (Nat.sub_eq_iff_eq_add (Nat.mul_le_mul_right m (Nat.sub_le _ _))).mpr
        nlinarith
      rw [hs]
      ring
    · simp only [Source,Group,Nat.card_eq_fintype_card,Fintype.card_prod,
        Fintype.card_fun,ZMod.card,Fintype.card_fin,mul_pow]
      have hp (b : ℕ) : b^r = b^(r-1)*b := by
        conv_lhs => rw [show r = (r-1)+1 from by omega]
        rw [pow_succ]
      rw [hp 2,pow_succ,hp m]
      ring
  refine ⟨⟨core,cardinalities⟩,?_⟩
  intro p q A B
  have hv : (recoverArithmetic f p q A B).1 = recover f p q A B := rfl
  have hg : (recoverArithmetic f p q A B).2.1 = 5*(r-1)+3 := by
    simp [recoverArithmetic]
    omega
  have hc : (recoverArithmetic f p q A B).2.2 = 3*(r-1)+1 := by
    simp [recoverArithmetic]
    omega
  refine ⟨hv,hg,hc,?_,?_⟩
  · rw [hg]; omega
  · rw [hc]; omega

#print axioms cyclic_selector_recovery

end D5.S3.ObserverMemory.ContextUpdates.CyclicSelectorRecovery
