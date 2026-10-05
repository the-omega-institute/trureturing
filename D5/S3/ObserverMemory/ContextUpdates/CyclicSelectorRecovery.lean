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
  have core :
    ((∃ x y, f x ≠ f y) →
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
      (∃ s : Source m r, observe f s = (a,t,fun i => (0,u i)))) := by
    classical
    have geometry : (∃ x y, f x ≠ f y) →
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
            f (z+(j : ZMod m)) = f z)) ↔ L ≤ n)) := by
      intro hf
      classical
      have different (z : ZMod m) : ∃ w, f w ≠ f z := by
        obtain ⟨x,y,hxy⟩ := hf
        by_cases hx : f x = f z
        · exact ⟨y,fun hy => hxy (hx.trans hy.symm)⟩
        · exact ⟨x,hx⟩
      have forward (z : ZMod m) : ∃ j : ℕ,
          0 < j ∧ j < m ∧ f (z+(j : ZMod m)) ≠ f z := by
        obtain ⟨w,hw⟩ := different z
        refine ⟨(w-z).val,?_,ZMod.val_lt _,?_⟩
        · have hn : (w-z).val ≠ 0 := by
            intro he
            have hz := (ZMod.val_eq_zero _).mp he
            exact hw (by rw [sub_eq_zero.mp hz])
          omega
        · simpa only [ZMod.natCast_zmod_val,add_sub_cancel] using hw
      have backward (z : ZMod m) : ∃ j : ℕ,
          0 < j ∧ j < m ∧ f (z-(j : ZMod m)) ≠ f z := by
        obtain ⟨w,hw⟩ := different z
        refine ⟨(z-w).val,?_,ZMod.val_lt _,?_⟩
        · have hn : (z-w).val ≠ 0 := by
            intro he
            have hz := (ZMod.val_eq_zero _).mp he
            exact hw (by rw [← sub_eq_zero.mp hz])
          omega
        · simpa only [ZMod.natCast_zmod_val,sub_sub_cancel] using hw
      have ds (z : ZMod m) :
          0 < delta f z ∧ delta f z < m ∧
          f (z+(delta f z : ZMod m)) ≠ f z ∧
          ∀ j, j < delta f z → f (z+(j : ZMod m)) = f z := by
        obtain ⟨j,hj,hjm,hchange⟩ := forward z
        have ex : ∃ j : ℕ, 0 < j ∧ f (z+(j : ZMod m)) ≠ f z := ⟨j,hj,hchange⟩
        rw [delta,dif_pos ex]
        have spec := Nat.find_spec ex
        have bound := Nat.find_min' ex ⟨hj,hchange⟩
        refine ⟨spec.1,by omega,spec.2,?_⟩
        intro k hk
        by_cases hk0 : k = 0
        · simp [hk0]
        · by_contra hn
          have hle := Nat.find_min' ex ⟨by omega,hn⟩
          omega
      have bs (z : ZMod m) :
          0 < beta f z ∧ beta f z < m ∧
          f (z-(beta f z : ZMod m)) ≠ f z ∧
          ∀ j, j < beta f z → f (z-(j : ZMod m)) = f z := by
        obtain ⟨j,hj,hjm,hchange⟩ := backward z
        have ex : ∃ j : ℕ, 0 < j ∧ f (z-(j : ZMod m)) ≠ f z := ⟨j,hj,hchange⟩
        rw [beta,dif_pos ex]
        have spec := Nat.find_spec ex
        have bound := Nat.find_min' ex ⟨hj,hchange⟩
        refine ⟨spec.1,by omega,spec.2,?_⟩
        intro k hk
        by_cases hk0 : k = 0
        · simp [hk0]
        · by_contra hn
          have hle := Nat.find_min' ex ⟨by omega,hn⟩
          omega
      have dmin (z : ZMod m) (d : ℕ) (hd : 0 < d)
          (hend : f (z+(d : ZMod m)) ≠ f z)
          (hbefore : ∀ j, j < d → f (z+(j : ZMod m)) = f z) : delta f z = d := by
        obtain ⟨hpos,_,hchange,hsmall⟩ := ds z
        apply le_antisymm
        · by_contra hn
          exact hend (hsmall d (by omega))
        · by_contra hn
          exact hchange (hbefore _ (by omega))
      have bmin (z : ZMod m) (b : ℕ) (hb : 0 < b)
          (hend : f (z-(b : ZMod m)) ≠ f z)
          (hbefore : ∀ j, j < b → f (z-(j : ZMod m)) = f z) : beta f z = b := by
        obtain ⟨hpos,_,hchange,hsmall⟩ := bs z
        apply le_antisymm
        · by_contra hn
          exact hend (hsmall b (by omega))
        · by_contra hn
          exact hchange (hbefore _ (by omega))
      let start := fun z : ZMod m => z - ((beta f z-1 : ℕ) : ZMod m)
      have segment (z : ZMod m) (j : ℕ) (hj : j ≤ beta f z-1) :
          f (start z+(j : ZMod m)) = f z := by
        have hb := bs z
        have he : start z+(j : ZMod m) = z - ((beta f z-1-j : ℕ) : ZMod m) := by
          dsimp [start]
          rw [show ((beta f z-1-j : ℕ) : ZMod m) =
          ((beta f z-1 : ℕ) : ZMod m)-(j : ZMod m) from Nat.cast_sub hj]
          abel
        rw [he]
        exact hb.2.2.2 _ (by omega)
      have startMem (z : ZMod m) : f (start z-1) ≠ f (start z) := by
        have hb := bs z
        have he : start z-1 = z-(beta f z : ZMod m) := by
          dsimp [start]
          have hcast : ((beta f z-1 : ℕ) : ZMod m) = (beta f z : ZMod m)-1 := by
            rw [Nat.cast_sub (by omega),Nat.cast_one]
          rw [hcast]
          abel
        rw [he,show f (start z) = f z from by simpa using segment z 0 (by omega)]
        exact hb.2.2.1
      have startBound (z : ZMod m) : beta f z-1 < delta f (start z) := by
        by_contra hn
        have h := segment z (delta f (start z)) (by omega)
        have hs := segment z 0 (by omega)
        simp only [Nat.cast_zero,add_zero] at hs
        exact (ds (start z)).2.2.1 (h.trans hs.symm)
      have atPosition (s : RunStart f) (k : ℕ) (hk : k < delta f s.val) :
          beta f (s.val+(k : ZMod m)) = k+1 ∧
          delta f (s.val+(k : ZMod m)) = delta f s.val-k := by
        have hd := ds s.val
        have hcolor := hd.2.2.2 k hk
        constructor
        · apply bmin _ _ (by omega)
          · have he : s.val+(k : ZMod m)-((k+1 : ℕ) : ZMod m) = s.val-1 := by
              rw [Nat.cast_add,Nat.cast_one]
              abel
            rw [he,hcolor]
            exact s.property
          · intro j hj
            have hjk : j ≤ k := by omega
            have he : s.val+(k : ZMod m)-(j : ZMod m) =
                s.val+((k-j : ℕ) : ZMod m) := by
              rw [Nat.cast_sub hjk]
              abel
            rw [he,hcolor]
            exact hd.2.2.2 _ (by omega)
        · apply dmin _ _ (by omega)
          · have he : s.val+(k : ZMod m)+((delta f s.val-k : ℕ) : ZMod m) =
                s.val+(delta f s.val : ZMod m) := by
              rw [Nat.cast_sub (by omega)]
              abel
            rw [he,hcolor]
            exact hd.2.2.1
          · intro j hj
            have he : s.val+(k : ZMod m)+(j : ZMod m) =
                s.val+((k+j : ℕ) : ZMod m) := by rw [Nat.cast_add,add_assoc]
            rw [he,hcolor]
            exact hd.2.2.2 _ (by omega)
      let e : ZMod m ≃ RunPosition f :=
        { toFun := fun z => ⟨⟨start z,startMem z⟩,⟨beta f z-1,startBound z⟩⟩
          invFun := fun p => p.1.val+(p.2.val : ZMod m)
          left_inv := by intro z; dsimp [start]; abel
          right_inv := by
            intro p
            obtain ⟨s,k⟩ := p
            have hb := (atPosition s k.val k.isLt).1
            have hs : (⟨start (s.val+(k.val : ZMod m)),startMem _⟩ : RunStart f) = s := by
              apply Subtype.ext
              change start (s.val+(k.val : ZMod m)) = s.val
              dsimp [start]
              rw [hb,Nat.add_sub_cancel]
              abel
            apply Sigma.ext hs
            apply (Fin.heq_ext_iff (congrArg (fun q : RunStart f => delta f q.val) hs)).mpr
            dsimp
            rw [hb,Nat.add_sub_cancel] }
      refine ⟨e,fun _ => rfl,fun _ => ⟨rfl,rfl⟩,?_,?_,?_,?_⟩
      · intro p
        exact (atPosition p.1 p.2.val p.2.isLt).2
      · intro z
        have h := ds z
        omega

      · intro n
        have window (z : ZMod m) :
            (∀ j : ℕ, j ≤ n → f (z+(j : ZMod m)) = f z) ↔ n < delta f z := by
          constructor
          · intro hw
            by_contra hn
            exact (ds z).2.2.1 (hw _ (by omega))
          · intro hn j hj
            exact (ds z).2.2.2 j (by omega)
        let cut : {z : ZMod m // ∀ j : ℕ, j ≤ n → f (z+(j : ZMod m)) = f z} ≃
            ((s : RunStart f) × Fin (delta f s.val-n)) :=
          { toFun := fun z => ⟨(e z.val).1,⟨(e z.val).2.val,by
              have h := (atPosition (e z.val).1 (e z.val).2.val (e z.val).2.isLt).2
              change delta f (e.symm (e z.val)) = _ at h
              rw [e.symm_apply_apply] at h
              have hw := (window z.val).mp z.property
              omega⟩⟩
            invFun := fun p => ⟨p.1.val+(p.2.val : ZMod m),by
              apply (window _).mpr
              have hk : p.2.val < delta f p.1.val := by have := p.2.isLt; omega
              rw [(atPosition p.1 p.2.val hk).2]
              have := p.2.isLt
              omega⟩
            left_inv := by
              intro z
              apply Subtype.ext
              exact e.symm_apply_apply z.val
            right_inv := by
              intro p
              have hk : p.2.val < delta f p.1.val := by have := p.2.isLt; omega
              have he := e.apply_symm_apply (⟨p.1,⟨p.2.val,hk⟩⟩ : RunPosition f)
              have hs := congrArg Sigma.fst he
              have hs' : (e (p.1.val+(p.2.val : ZMod m))).1 = p.1 := hs
              apply Sigma.ext (β := fun s : RunStart f => Fin (delta f s.val-n)) hs'
              apply (Fin.heq_ext_iff
                (congrArg (fun s : RunStart f => delta f s.val-n) hs')).mpr
              exact congrArg (fun v : RunPosition f => v.2.val) he }
        rw [Nat.card_congr cut]
        simp [Nat.card_eq_fintype_card,Fintype.card_sigma]

      · let lengths : Finset ℕ := Finset.univ.image (fun s : RunStart f => delta f s.val)
        have hnon : lengths.Nonempty := by
          exact ⟨delta f (e 0).1.val,Finset.mem_image.mpr ⟨(e 0).1,Finset.mem_univ _,rfl⟩⟩
        let L := lengths.max' hnon
        have hmax (s : RunStart f) : delta f s.val ≤ L :=
          Finset.le_max' lengths _ (Finset.mem_image.mpr ⟨s,Finset.mem_univ _,rfl⟩)
        obtain ⟨smax,_,hsmax⟩ := Finset.mem_image.mp (Finset.max'_mem lengths hnon)
        have cap (z : ZMod m) : delta f z ≤ L := by
          have h := (atPosition (e z).1 (e z).2.val (e z).2.isLt).2
          change delta f (e.symm (e z)) = _ at h
          rw [e.symm_apply_apply] at h
          rw [h]
          exact (Nat.sub_le _ _).trans (hmax _)
        refine ⟨L,?_,?_,cap,?_,?_⟩
        · have h := (ds smax.val).1
          omega
        · have h := (ds smax.val).2.1
          omega
        · intro j hj hjL
          have hk : L-j < delta f smax.val := by omega
          refine ⟨smax.val+((L-j : ℕ) : ZMod m),?_⟩
          rw [(atPosition smax (L-j) hk).2,hsmax]
          omega
        · intro n
          constructor
          · intro hw
            by_contra hn
            have hc : ∀ j : ℕ, j ≤ n → f (smax.val+(j : ZMod m)) = f smax.val := by
              intro j hj
              apply (ds smax.val).2.2.2
              omega
            exact hw smax.val hc
          · intro hn z hz
            have hd := cap z
            exact (ds z).2.2.1 (hz _ (by omega))
    have hhalf : (m/2 : ℕ)+(m/2) = m := by
      have h := Nat.two_mul_div_two_of_even heven
      omega
    have halfZero : ((m/2 : ℕ) : ZMod m)+(m/2 : ℕ) = 0 := by
      rw [← Nat.cast_add,hhalf,ZMod.natCast_self]
    have halfNe : ((m/2 : ℕ) : ZMod m) ≠ 0 := by
      have hbound : m/2 < m := by omega
      have hpos : 0 < m/2 := by omega
      intro he
      have hv := congrArg ZMod.val he
      rw [ZMod.val_natCast_of_lt hbound,ZMod.val_zero] at hv
      omega
    have selectorNe (b c : ZMod 2) (hbc : b ≠ c) : selector m b ≠ selector m c := by
      fin_cases b <;> fin_cases c
      · exact (hbc rfl).elim
      · intro h
        have h' := congrArg Prod.snd h
        simpa [selector] using halfNe h'.symm
      · intro h
        have h' := congrArg Prod.snd h
        simpa [selector] using halfNe h'
      · exact (hbc rfl).elim
    have projectionTranslate (c x : Group m) (w : ZMod m) :
        project c (x-(0,w)) = project c x-(0,w) := by
      simp only [project,Prod.fst_sub,sub_zero]
      split_ifs <;> abel
    have clockAdvance (s : Source m r) (j : ℕ) : clock (advance j s) = clock s := by
      have hs : (∑ i : Fin (r-1),
          if i.val = 0 then ((0,(j : ZMod m)) : Group m) else 0) = (0,(j : ZMod m)) := by
        let i0 : Fin (r-1) := ⟨0,by omega⟩
        apply Finset.sum_eq_single i0
        · intro i _ hi
          have hn : i.val ≠ 0 := fun he => hi (Fin.ext he)
          simp [hn]
        · simp
      change (s.1.1+(0,(j : ZMod m))) +
        (∑ i : Fin (r-1), (s.1.2 i - if i.val = 0 then (0,(j : ZMod m)) else 0)) + (0,s.2) = _
      rw [Finset.sum_sub_distrib,hs]
      dsimp [clock,total]
      abel
    have normalized (s : Source m r) (j : ℕ) (i : Fin (r-1)) :
        (observe f (advance j s)).2.2 i +
          (if i.val = 0 then (0,(j : ZMod m)) else 0) =
        project (selector m (f (s.1.1.2+(j : ZMod m)))) (s.1.2 i) := by
      dsimp [observe,advance]
      by_cases hi : i.val = 0
      · simp only [if_pos hi,projectionTranslate,sub_add_cancel]
      · simp only [if_neg hi,sub_zero,add_zero]
    have decodeBit (b c : ZMod 2) (hbc : b ≠ c) (x : Group m) :
        project (selector m b) x +
          (if project (selector m c) x - project (selector m b) x = 0
            then 0 else selector m b) = x := by
      rcases x with ⟨e,z⟩
      have casesBit : e = 0 ∨ e = 1 := by
        fin_cases e
        · exact Or.inl rfl
        · exact Or.inr rfl
      rcases casesBit with he | he
      · subst e
        simp [project]
      · subst e
        have hd : project (selector m c) (1,z) -
            project (selector m b) (1,z) ≠ 0 := by
          intro he
          have he' : selector m b = selector m c := by
            have h := sub_eq_zero.mp he
            have h' : (1,z) - selector m c = (1,z) - selector m b := by
              simpa [project] using h
            exact (sub_right_inj.mp h').symm
          exact selectorNe b c hbc he'
        rw [if_neg hd]
        norm_num [project]
    have decoder (s : Source m r) (p q : ℕ)
        (hpq : f (s.1.1.2+(p : ZMod m)) ≠ f (s.1.1.2+(q : ZMod m))) :
        recover f p q (observe f (advance p s)) (observe f (advance q s)) = s := by
      have ha : (observe f (advance p s)).1-(0,(p : ZMod m)) = s.1.1 := by
        simp [observe,advance]
      have hx : (fun i : Fin (r-1) =>
          ((observe f (advance p s)).2.2 i +
            if i.val = 0 then (0,(p : ZMod m)) else 0) +
          (if ((observe f (advance q s)).2.2 i +
              if i.val = 0 then (0,(q : ZMod m)) else 0) -
            ((observe f (advance p s)).2.2 i +
              if i.val = 0 then (0,(p : ZMod m)) else 0) = 0
            then 0 else selector m (f (observe f (advance p s)).1.2))) = s.1.2 := by
        funext i
        rw [normalized s p i,normalized s q i]
        exact decodeBit _ _ hpq (s.1.2 i)
      dsimp only [recover]
      rw [ha,hx,show (observe f (advance p s)).2.1 = clock s from clockAdvance s p]
      simp [clock,total]

    have residual (s : Source m r) (j : ℕ)
        (hj : f (s.1.1.2+(j : ZMod m)) = f s.1.1.2) :
        observe f (advance j s) =
          (s.1.1+(0,(j : ZMod m)),clock s,fun i =>
            (observe f s).2.2 i - if i.val = 0 then (0,(j : ZMod m)) else 0) := by
      apply Prod.ext
      · rfl
      · apply Prod.ext
        · exact clockAdvance s j
        · funext i
          apply eq_sub_iff_add_eq.mpr
          rw [normalized s j i,hj]
          rfl
    have pairSame (s t : Source m r) (hobs : observe f s = observe f t)
        (j : ℕ) (hj : f (s.1.1.2+(j : ZMod m)) = f s.1.1.2) :
        observe f (advance j s) = observe f (advance j t) := by
      have ha : s.1.1 = t.1.1 := congrArg (fun o : Snapshot m r => o.1) hobs
      have ht : clock s = clock t := congrArg (fun o => o.2.1) hobs
      have hu : (observe f s).2.2 = (observe f t).2.2 := congrArg (fun o => o.2.2) hobs
      rw [residual s j hj,residual t j (by simpa only [← ha] using hj),ha,ht,hu]
    have traceFiber (s t : Source m r) (hobs : observe f s = observe f t) (n : ℕ) :
        trace f n s = trace f n t ↔ s = t ∨
          ∀ j : ℕ, j ≤ n → f (s.1.1.2+(j : ZMod m)) = f s.1.1.2 := by
      have ha : s.1.1 = t.1.1 := congrArg (fun o : Snapshot m r => o.1) hobs
      constructor
      · intro ht
        by_cases he : s = t
        · exact Or.inl he
        · right
          intro j hj
          by_contra hchange
          have hpq : f (s.1.1.2+(0 : ZMod m)) ≠ f (s.1.1.2+(j : ZMod m)) := by
            simpa only [add_zero] using Ne.symm hchange
          have hpq' : f (t.1.1.2+(0 : ZMod m)) ≠ f (t.1.1.2+(j : ZMod m)) := by
            simpa only [← ha] using hpq
          have hjobs : observe f (advance j s) = observe f (advance j t) :=
            congrFun ht ⟨j,by omega⟩
          have advanceZero (u : Source m r) : advance 0 u = u := by
            have hz : ((0,(0 : ZMod m)) : Group m) = 0 := rfl
            simp only [advance,Nat.cast_zero,hz,ite_self,sub_zero,add_zero]
          have hzero : observe f (advance 0 s) = observe f (advance 0 t) := by
            rw [advanceZero s,advanceZero t]
            exact hobs
          apply he
          calc
            s = recover f 0 j (observe f (advance 0 s)) (observe f (advance j s)) :=
              (decoder s 0 j (by simpa only [Nat.cast_zero] using hpq)).symm
            _ = recover f 0 j (observe f (advance 0 t)) (observe f (advance j t)) := by
              rw [hzero,hjobs]
            _ = t := decoder t 0 j (by simpa only [Nat.cast_zero] using hpq')
      · rintro (rfl | hw)
        · rfl
        · funext j
          exact pairSame s t hobs j.val (hw j.val (by have := j.isLt; omega))

    have twoSelector (b : ZMod 2) : selector m b + selector m b = 0 := by
      apply Prod.ext
      · change (1 : ZMod 2)+1=0
        rfl
      · by_cases hb : b = 0
        · simp [selector,hb]
        · simpa [selector,hb] using halfZero
    have witnesses (z : ZMod m) :
        baseSource m r z ≠ flipSource m r hr f z ∧
        observe f (baseSource m r z) = observe f (flipSource m r hr f z) ∧
        (∀ n : ℕ, trace f n (baseSource m r z) = trace f n (flipSource m r hr f z) ↔
          ∀ j : ℕ, j ≤ n → f (z+(j : ZMod m)) = f z) := by
      let c := selector m (f z)
      let i0 : Fin (r-1) := ⟨0,by omega⟩
      let i1 : Fin (r-1) := ⟨1,by omega⟩
      have hi : i0 ≠ i1 := by intro h; have := congrArg Fin.val h; dsimp [i0,i1] at this; omega
      let v0 : Fin (r-1) → Group m := Pi.single i0 c
      let v1 : Fin (r-1) → Group m := Pi.single i1 c
      have hsum : (∑ i : Fin (r-1), (v0 i+v1 i)) = 0 := by
        simpa [v0,v1,Finset.sum_add_distrib] using twoSelector (f z)
      have hne : baseSource m r z ≠ flipSource m r hr f z := by
        intro he
        have h := congrArg (fun u : Source m r => (u.1.2 i0).1) he
        have hc : c.1 = 1 := rfl
        simp only [baseSource,flipSource] at h
        change (0 : Group m).1 = (v0 i0+v1 i0).1 at h
        simp [v0,v1,Pi.single_eq_of_ne hi,hc] at h
      have hobs : observe f (baseSource m r z) = observe f (flipSource m r hr f z) := by
        apply Prod.ext
        · rfl
        · apply Prod.ext
          · change ((0,z) : Group m) + (∑ i : Fin (r-1), (0 : Group m)) + (0,0) =
              (0,z) + (∑ i : Fin (r-1), (v0 i+v1 i)) + (0,0)
            rw [hsum]
            simp
          · funext i
            change project c (0 : Group m) =
              project c (v0 i+v1 i)
            by_cases h0 : i = i0
            · subst i
              simp [v0,v1,Pi.single_eq_of_ne hi,project,c,selector]
            · by_cases h1 : i = i1
              · subst i
                simp [v0,v1,Pi.single_eq_of_ne (Ne.symm hi),project,c,selector]
              · simp [v0,v1,Pi.single_eq_of_ne h0,Pi.single_eq_of_ne h1]
      refine ⟨hne,hobs,?_⟩
      intro n
      have h := traceFiber (baseSource m r z) (flipSource m r hr f z) hobs n
      simp only [hne,false_or] at h
      exact h
    have iterates : ∀ j : ℕ, ∀ s : Source m r, ((advance 1)^[j]) s = advance j s := by
      have advanceZero (s : Source m r) : advance 0 s = s := by
        have hz : ((0,(0 : ZMod m)) : Group m) = 0 := rfl
        simp only [advance,Nat.cast_zero,hz,ite_self,sub_zero,add_zero]
      have advanceAdd (a b : ℕ) (s : Source m r) :
          advance a (advance b s) = advance (a+b) s := by
        apply Prod.ext
        · apply Prod.ext
          · dsimp [advance]
            rw [Nat.cast_add]
            apply Prod.ext <;> simp <;> abel
          · funext i
            dsimp [advance]
            by_cases hi : i.val = 0
            · simp only [if_pos hi,Nat.cast_add]
              apply Prod.ext <;> simp <;> abel
            · simp [hi]
        · rfl
      intro j s
      induction j with
      | zero => simpa using (advanceZero s).symm
      | succ j ih =>
          rw [Function.iterate_succ_apply',ih,advanceAdd]
          congr 1
          omega
    have bitCases (e : ZMod 2) : e = 0 ∨ e = 1 := by
      fin_cases e
      · exact Or.inl rfl
      · exact Or.inr rfl
    have fiberForward (a t : Group m) (u : Fin (r-1) → ZMod m)
        (bits : Fin (r-1) → ZMod 2) (hbits : (∑ i, bits i) = t.1-a.1) :
        observe f (fiberSource f a t u bits) = (a,t,fun i => (0,u i)) := by
      let c := selector m (f a.2)
      let x : Fin (r-1) → Group m := fun i => (0,u i) + if bits i = 0 then 0 else c
      have hx (i : Fin (r-1)) : (x i).1 = bits i ∧ project c (x i) = (0,u i) := by
        rcases bitCases (bits i) with h | h
        · simp [x,h,project]
        · have hc : c.1 = 1 := rfl
          simp [x,h,project,hc]
      have hsum : (∑ i, x i).1 = ∑ i, bits i := by
        change (AddMonoidHom.fst (ZMod 2) (ZMod m)) (∑ i, x i) = _
        rw [map_sum]
        exact Finset.sum_congr rfl (fun i _ => (hx i).1)
      apply Prod.ext
      · rfl
      · apply Prod.ext
        · change (a+∑ i, x i) + (0,(t-(a+∑ i, x i)).2) = t
          apply Prod.ext
          · change a.1+(∑ i, x i).1+0=t.1
            rw [hsum,hbits]
            abel
          · dsimp
            abel
        · funext i
          exact (hx i).2
    refine ⟨geometry,clockAdvance,decoder,traceFiber,residual,witnesses,iterates,?_⟩
    intro a t u
    have inverse (s : Source m r) (ho : observe f s = (a,t,fun i => (0,u i))) :
        (∑ i, (s.1.2 i).1) = t.1-a.1 ∧
        fiberSource f a t u (fun i => (s.1.2 i).1) = s := by
      have ha : s.1.1 = a := congrArg (fun o : Snapshot m r => o.1) ho
      have ht : clock s = t := congrArg (fun o : Snapshot m r => o.2.1) ho
      have hu (i : Fin (r-1)) : project (selector m (f a.2)) (s.1.2 i) = (0,u i) := by
        have h := congrArg (fun o : Snapshot m r => o.2.2 i) ho
        simpa only [observe,ha] using h
      have hsum : (∑ i, s.1.2 i).1 = ∑ i, (s.1.2 i).1 := by
        change (AddMonoidHom.fst (ZMod 2) (ZMod m)) (∑ i, s.1.2 i) = _
        exact map_sum _ _ _
      have hpar : (∑ i, (s.1.2 i).1) = t.1-a.1 := by
        have h := congrArg Prod.fst ht
        change s.1.1.1+(∑ i, s.1.2 i).1+0=t.1 at h
        rw [hsum,ha] at h
        simpa using eq_sub_iff_add_eq.mpr (by simpa [add_comm] using h)
      refine ⟨hpar,?_⟩
      have hx : (fun i : Fin (r-1) => ((0,u i) : Group m) +
          if (s.1.2 i).1 = 0 then 0 else selector m (f a.2)) = s.1.2 := by
        funext i
        have h := hu i
        dsimp [project] at h
        rw [← h]
        exact sub_add_cancel _ _
      dsimp only [fiberSource]
      rw [hx,← ha]
      apply Prod.ext
      · rfl
      · have h := congrArg Prod.snd ht
        change (total s).2+s.2=t.2 at h
        change (t-total s).2=s.2
        dsimp
        exact (eq_sub_of_add_eq' h).symm
    refine ⟨fiberForward a t u,inverse,?_⟩
    let i0 : Fin (r-1) := ⟨0,by omega⟩
    let bits : Fin (r-1) → ZMod 2 := Pi.single i0 (t.1-a.1)
    refine ⟨fiberSource f a t u bits,fiberForward a t u bits ?_⟩
    simp [bits]
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
