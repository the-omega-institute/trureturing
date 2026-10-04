/- GID: D5/S3/Combinatorics/Permutation/CoupledRepairedWeight
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Permutation/CoupledRepairedWeight
   mirror-E: none(waiver:noncomputable-integer-permutation-weight)
   anchors: [mathlib/module/Mathlib.Data.List.OfFn, mathlib/module/Mathlib.Logic.Equiv.Fin.Basic]
   utility: none
   digest: Actual repaired deletion changes the integer weight by the sum of its digits. -/

import D5.S3.Combinatorics.Permutation.CoupledOrderedRecovery
import D5.S1.Digit.Carry.ListInversions
import D5.S3.Combinatorics.Permutation.OrdinaryForbiddenCountContraction
import Mathlib
import Mathlib.Data.List.OfFn
open D5.S1.Digit.Carry.ListInversions
open D5.S3.Combinatorics.Permutation.CoupledRepairedLeftInverse
open D5.S3.Combinatorics.Permutation.OrdinaryForbiddenCountContraction
set_option autoImplicit false
namespace D5.S3.Combinatorics.Permutation.CoupledRepairedWeight

def I {n : Nat} (S : Equiv.Perm (Fin n)) : Nat :=
  inv (List.ofFn (fun u => (S u).val))

noncomputable def E {K : Nat} (F G : Fin K → Nat)
    (S : Equiv.Perm (Fin (K + 1))) (p : Equiv.Perm (Fin K)) : Int :=
  (I S : Int) + (I p : Int) - ((ForbiddenCount F G S p).1 : Int)
    - ((ForbiddenCount F G S p).2 : Int)

set_option maxHeartbeats 2400000 in
theorem actual_repaired_weight {k L B : Nat} (hLB : L ≤ B) (hB : B ≤ k + 1)
    (F G : Fin (k + 1) → Nat)
    (sigma : Equiv.Perm (Fin (k + 2))) (pi : Equiv.Perm (Fin (k + 1)))
    (hF : Monotone F) (hG : Monotone G) (hFG : ∀ i, F i ≤ G i)
    (hF0 : F 0 = L + 1) (hG0 : G 0 = B + 1) (hel : Eligible F G sigma pi) :
    let z := (actualAlgorithms hLB hB).phi sigma pi
    let Ft := fun i : Fin k => F i.succ - 1
    let Gt := fun i : Fin k => G i.succ - 1
    E F G sigma pi = E Ft Gt z.1.1 z.1.2 + (z.2.1 : Int) + (z.2.2 : Int) := by
  classical
  have cut_word {n : Nat} (S : Equiv.Perm (Fin (n + 1))) (t : Fin (n + 1)) :
      inv (List.ofFn (fun u => ((cut S t) u).val)) =
        inv ((List.ofFn (fun u => (S u).val)).erase (S t).val) := by
    classical
    have inv_map {m : Nat} (f : Fin m → Nat) (hf : StrictMono f) (W : List (Fin m)) :
        inv (W.map f) = inv (W.map Fin.val) := by
      induction W with
      | nil => rfl
      | cons x xs ih =>
        simp only [List.map_cons,inv,List.countP_map,ih]
        congr 1
        apply List.countP_congr
        intro y hy
        simp only [Function.comp_apply,decide_eq_true_eq]
        exact hf.lt_iff_lt
    have positions : List.ofFn (fun u : Fin n => t.succAbove u) =
        (List.ofFn (fun u : Fin (n + 1) => u)).filter (fun u => decide (u ≠ t)) := by
      have hl : (List.ofFn (fun u : Fin n => t.succAbove u)).SortedLT :=
        List.sortedLT_ofFn_iff.mpr (Fin.strictMono_succAbove t)
      have hr : ((List.ofFn (fun u : Fin (n + 1) => u)).filter
          (fun u => decide (u ≠ t))).SortedLT :=
        ((List.sortedLT_ofFn_iff.mpr strictMono_id).pairwise.filter _).sortedLT
      apply hl.eq_of_mem_iff hr
      intro u
      simp only [List.mem_ofFn,List.mem_filter,decide_eq_true_eq]
      constructor
      · rintro ⟨v,rfl⟩
        exact ⟨⟨t.succAbove v,rfl⟩,t.succAbove_ne v⟩
      · rintro ⟨_,hu⟩
        obtain ⟨v,hv⟩ := (finSuccAboveEquiv t).surjective ⟨u,hu⟩
        exact ⟨v,congrArg Subtype.val hv⟩
    have lift (u : Fin n) : (S t).succAbove ((cut S t) u) = S (t.succAbove u) := by
      have hh := (finSuccAboveEquiv (S t)).apply_symm_apply
        ((Equiv.subtypeEquiv S (by intro x; exact S.injective.ne_iff.symm))
          ((finSuccAboveEquiv t) u))
      exact congrArg Subtype.val hh
    have hword : List.ofFn (fun u : Fin n => ((S t).succAbove ((cut S t) u)).val) =
        (List.ofFn (fun u => (S u).val)).erase (S t).val := by
      simp_rw [lift]
      have hp := congrArg (List.map (fun u => (S u).val)) positions
      simp only [List.map_ofFn,Function.comp_def] at hp
      have hd : (List.ofFn (fun u : Fin (n + 1) => (S u).val)).Nodup :=
        List.nodup_ofFn_ofInjective (Fin.val_injective.comp S.injective)
      rw [hd.erase_eq_filter]
      rw [hp]
      have hfm := List.filter_map (f := fun u : Fin (n + 1) => (S u).val)
        (p := fun x => x != (S t).val) (l := List.ofFn (fun u : Fin (n + 1) => u))
      simp only [List.map_ofFn,Function.comp_def] at hfm
      rw [hfm]
      apply congrArg (List.map (fun u => (S u).val))
      apply List.filter_congr
      intro u hu
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq,bne_iff_ne]
      exact (not_congr (Fin.val_injective.eq_iff.trans S.injective.eq_iff)).symm
    rw [← hword]
    have hm := inv_map (fun u : Fin n => ((S t).succAbove u).val)
      (Fin.val_strictMono.comp (Fin.strictMono_succAbove (S t)))
      (List.ofFn (fun u => (cut S t) u))
    simpa only [List.map_ofFn,Function.comp_def] using hm.symm
  have row_account {n L : Nat} (hL : L ≤ n)
      (sigma : Equiv.Perm (Fin (n + 1))) (t : Fin (n + 1))
      (ha : (sigma t).val < L + 1) :
      let theta := lowWord sigma (Nat.add_le_add_right hL 1)
      let q := theta.symm (Fin.last L)
      let rho := cut theta q
      let sd := replace (cut sigma t) hL rho
      inv (List.ofFn (fun u => (sigma u).val)) =
        inv (List.ofFn (fun u => (sd u).val)) +
        ((List.ofFn (fun u => (sigma u).val)).take t.val).countP (fun x => decide (L + 1 ≤ x)) +
        (L - q.val) := by
    classical
    have cancellation (L : Nat) (X Y : List Nat)
        (h : List.Forall₂ (fun x y => (x < L ↔ y < L) ∧ (L ≤ x → x = y)) X Y) :
        inv X + inv (Y.filter (fun y => decide (y < L))) =
          inv Y + inv (X.filter (fun x => decide (x < L))) := by
      have filtered_count (W : List Nat) (a : Nat) (ha : a < L) :
          (W.filter (fun z => decide (z < L))).countP (fun z => decide (z < a)) =
            W.countP (fun z => decide (z < a)) := by
        rw [List.countP_filter]
        apply List.countP_congr
        intro z hz
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        omega
      have high_count (a : Nat) (ha : L ≤ a) {U V : List Nat}
          (hh : List.Forall₂ (fun x y => (x < L ↔ y < L) ∧ (L ≤ x → x = y)) U V) :
          U.countP (fun z => decide (z < a)) = V.countP (fun z => decide (z < a)) := by
        induction hh with
        | nil => rfl
        | @cons x y xs ys hxy htail ih =>
          have hc : (x < a) ↔ (y < a) := by
            by_cases hx : x < L
            · have hy := hxy.1.mp hx
              omega
            · have he := hxy.2 (by omega)
              rw [he]
          simp only [List.countP_cons, hc, ih]
      induction h with
      | nil => simp [inv]
      | @cons x y xs ys hxy htail ih =>
        by_cases hx : x < L
        · have hy := hxy.1.mp hx
          simp only [List.filter_cons, hx, hy, decide_true, if_true, inv]
          rw [filtered_count xs x hx, filtered_count ys y hy]
          omega
        · have hy : ¬ y < L := fun hh => hx (hxy.1.mpr hh)
          have he := hxy.2 (by omega)
          have hc := high_count x (by omega) htail
          simp only [List.filter_cons, hx, hy, decide_false, Bool.false_eq_true, if_false, inv]
          subst y
          omega
    have low_interface {n T : Nat} (S : Equiv.Perm (Fin n)) (hT : T ≤ n) :
      (List.ofFn (fun u => (S u).val)).filter (fun x => decide (x < T)) =
        List.ofFn (fun i => ((lowWord S hT) i).val) := by
      classical
      let so := slotOrder S hT
      have hleft : (List.ofFn (fun i : Fin T => (so i).val)).SortedLT := by
        apply List.sortedLT_ofFn_iff.mpr
        intro i j hij
        exact so.strictMono hij
      have hright : ((List.ofFn (fun i : Fin n => i)).filter
          (fun u => decide ((S u).val < T))).SortedLT := by
        have hsort : (List.ofFn (fun i : Fin n => i)).SortedLT :=
          List.sortedLT_ofFn_iff.mpr strictMono_id
        exact (hsort.pairwise.filter _).sortedLT
      have hpos : List.ofFn (fun i : Fin T => (so i).val) =
          (List.ofFn (fun i : Fin n => i)).filter (fun u => decide ((S u).val < T)) := by
        apply hleft.eq_of_mem_iff hright
        intro u
        simp only [List.mem_ofFn, List.mem_filter, decide_eq_true_eq]
        constructor
        · rintro ⟨i,rfl⟩
          exact ⟨⟨(so i).val,rfl⟩,(so i).property⟩
        · rintro ⟨_, hu⟩
          obtain ⟨i,hi⟩ := so.surjective ⟨u,hu⟩
          exact ⟨i,congrArg Subtype.val hi⟩
      have he := congrArg (List.map (fun u : Fin n => (S u).val)) hpos
      change (List.ofFn (fun u => (S u).val)).filter (fun x => decide (x < T)) =
        List.ofFn (fun i => (S (so i).val).val)
      have hf : ((List.ofFn (fun u : Fin n => (S u).val)).filter (fun x => decide (x < T))) =
          List.map (fun u : Fin n => (S u).val)
            ((List.ofFn (fun u : Fin n => u)).filter (fun u => decide ((S u).val < T))) := by
        simpa only [List.map_ofFn, Function.comp_def] using
          (List.filter_map (f := fun u : Fin n => (S u).val)
            (p := fun x => decide (x < T)) (l := List.ofFn (fun u : Fin n => u)))
      rw [hf]
      simpa only [List.map_ofFn,Function.comp_def] using he.symm
    have replacement {n T : Nat} (S : Equiv.Perm (Fin n)) (hT : T ≤ n)
        (rho : Equiv.Perm (Fin T)) :
        inv (List.ofFn (fun u => (S u).val)) +
          inv (List.ofFn (fun i => ((lowWord (replace S hT rho) hT) i).val)) =
        inv (List.ofFn (fun u => ((replace S hT rho) u).val)) +
          inv (List.ofFn (fun i => ((lowWord S hT) i).val)) := by
      rw [← low_interface (replace S hT rho) hT, ← low_interface S hT]
      apply cancellation T
      apply List.forall₂_iff_get.mpr
      constructor
      · simp
      · intro i hi hj
        have hin : i < n := by simpa using hi
        let u : Fin n := ⟨i,hin⟩
        simp only [List.get_eq_getElem, List.getElem_ofFn]
        change ((S u).val < T ↔ ((replace S hT rho) u).val < T) ∧
          (T ≤ (S u).val → (S u).val = ((replace S hT rho) u).val)
        by_cases hu : (S u).val < T
        · have he : ((replace S hT rho) u).val < T := by
            dsimp [replace]
            rw [Equiv.Perm.ofSubtype_apply_of_mem
              (p := fun x : Fin n => x.val < T) (a := S u) _ hu]
            exact (rho _).isLt
          exact ⟨iff_of_true hu he, fun hn => False.elim (by omega)⟩
        · have he : (replace S hT rho) u = S u := by
            dsimp [replace]
            rw [Equiv.Perm.ofSubtype_apply_of_not_mem
              (p := fun x : Fin n => x.val < T) (a := S u) _ hu]
          exact ⟨by rw [he], fun _ => congrArg Fin.val he.symm⟩
    have filtered_deletion (P S : List Nat) (a T : Nat) (ha : a < T) (hap : a ∉ P) :
        inv (P ++ [a] ++ S) +
          inv (((P ++ S).filter (fun x => decide (x < T)))) =
        inv (P ++ S) +
          inv ((P ++ [a] ++ S).filter (fun x => decide (x < T))) +
          P.countP (fun x => decide (T ≤ x)) := by
      have deletion (P S : List Nat) (a : Nat) :
          inv (P ++ [a] ++ S) = inv (P ++ S) +
            P.countP (fun p => decide (a < p)) + S.countP (fun q => decide (q < a)) := by
        have h1 := inv_window P [a] S
        have h0 := inv_window P [] S
        simp only [List.append_nil,inv,List.countP_nil,List.map_nil,List.sum_nil,
          List.map_cons,List.sum_cons,Nat.add_zero,
          ← List.countP_eq_length_filter] at h1 h0
        omega
      have hp : P.countP (fun p => decide (a < p)) =
          (P.filter (fun p => decide (p < T))).countP (fun p => decide (a < p)) +
            P.countP (fun p => decide (T ≤ p)) := by
        have h := List.countP_eq_countP_filter_add P (fun p => decide (a < p))
          (fun p => decide (p < T))
        rw [List.countP_filter] at h
        have he : (P.filter (fun p => !decide (p < T))).countP (fun p => decide (a < p)) =
            P.countP (fun p => decide (T ≤ p)) := by
          rw [List.countP_filter]
          apply List.countP_congr
          intro p hp
          simp only [Bool.and_eq_true,not_decide_eq_true,decide_eq_true_eq]
          omega
        rw [he] at h
        simpa only [List.countP_filter] using h
      have hs : (S.filter (fun q => decide (q < T))).countP (fun q => decide (q < a)) =
          S.countP (fun q => decide (q < a)) := by
        rw [List.countP_filter]
        apply List.countP_congr
        intro q hq
        simp only [Bool.and_eq_true,decide_eq_true_eq]
        omega
      have h1 := deletion P S a
      have h2 := deletion (P.filter (fun p => decide (p < T)))
        (S.filter (fun q => decide (q < T))) a
      simp only [List.filter_append,List.filter_cons,List.filter_nil,ha,decide_true,if_true]
      omega
    have recover :=
      D5.S3.Combinatorics.Permutation.CoupledOrderedRecovery.shared_ordered_recovery
        (@cut) (@slotOrder) (@lowWord) (@replace)
      (by intros; rfl) (by intros; rfl) (by intros; rfl)
    let hA := Nat.add_le_add_right hL 1
    let theta := lowWord sigma hA
    let q := theta.symm (Fin.last L)
    let rho := cut theta q
    let s := cut sigma t
    let sd := replace s hL rho
    let r := (slotOrder sigma hA).symm ⟨t,ha⟩
    have hr : theta r = ⟨(sigma t).val,ha⟩ := by
      apply Fin.ext
      change (sigma ((slotOrder sigma hA) r).val).val = _
      rw [(slotOrder sigma hA).apply_symm_apply]
    have hs := recover.1 hL sigma t ha
    have hrho := (recover.2 s hL rho).1
    have hc := replacement s hL rho
    rw [hrho,hs] at hc
    have hc1 := cut_word sigma t
    have hc2 := cut_word theta r
    rw [hr] at hc2
    have hw := low_interface sigma hA
    change (List.ofFn (fun u => (sigma u).val)).filter (fun x => decide (x < L + 1)) =
      List.ofFn (fun i => (theta i).val) at hw
    rw [← hw,List.erase_filter] at hc2
    dsimp only at hc2
    rw [hc2,hc1] at hc
    let X := List.ofFn (fun u => (sigma u).val)
    let a := (sigma t).val
    let P := X.take t.val
    let S := X.drop (t.val + 1)
    have ht : t.val < X.length := by simpa [X] using t.isLt
    have split : P ++ [a] ++ S = X := by
      have he := List.take_concat_get' X t.val ht
      have hv : X[t.val] = a := by
        dsimp only [X]
        rw [List.getElem_ofFn]
      rw [hv] at he
      dsimp only [P,S]
      rw [he,List.take_append_drop]
    have hn : X.Nodup := List.nodup_ofFn_ofInjective (Fin.val_injective.comp sigma.injective)
    have hap : a ∉ P := by
      have hh : (P ++ [a] ++ S).Nodup := split ▸ hn
      rw [List.append_assoc] at hh
      have hd := (List.nodup_append'.mp hh).2.2
      exact fun h => hd h (by simp)
    have he : X.erase a = P ++ S := by
      rw [← split,List.append_assoc,List.erase_append_right _ hap]
      simp
    have hd := filtered_deletion P S a (L + 1) ha hap
    rw [split,← he,hw] at hd
    have hq : theta q = Fin.last L := theta.apply_symm_apply _
    let Y := List.ofFn (fun u => (theta u).val)
    let Q := Y.take q.val
    let R := Y.drop (q.val + 1)
    have hqt : q.val < Y.length := by simpa [Y] using q.isLt
    have ysplit : Q ++ [L] ++ R = Y := by
      have he := List.take_concat_get' Y q.val hqt
      have hv : Y[q.val] = L := by
        dsimp only [Y]
        rw [List.getElem_ofFn]
        exact congrArg Fin.val hq
      rw [hv] at he
      dsimp only [Q,R]
      rw [he,List.take_append_drop]
    have hy : Y.Nodup := List.nodup_ofFn_ofInjective (Fin.val_injective.comp theta.injective)
    have hqnot : L ∉ Q := by
      have hh : (Q ++ [L] ++ R).Nodup := ysplit ▸ hy
      rw [List.append_assoc] at hh
      exact fun h => (List.nodup_append'.mp hh).2.2 h (by simp)
    have hrnot : L ∉ R := by
      have hh : (Q ++ [L] ++ R).Nodup := ysplit ▸ hy
      rw [List.append_assoc] at hh
      exact (List.nodup_cons.mp (List.nodup_append'.mp hh).2.1).1
    have hyerase : Y.erase L = Q ++ R := by
      rw [← ysplit,List.append_assoc,List.erase_append_right _ hqnot]
      simp
    have qp : Q.countP (fun p => decide (L < p)) = 0 := by
      apply List.countP_eq_zero.mpr
      intro p hp
      have hpY : p ∈ Y := List.mem_of_mem_take hp
      obtain ⟨i,hi⟩ := List.mem_ofFn.mp hpY
      have hi' := (theta i).isLt
      rw [← hi]
      simp only [decide_eq_true_eq]
      omega
    have rp : R.countP (fun p => decide (p < L)) = L - q.val := by
      have hall : R.countP (fun p => decide (p < L)) = R.length := by
        apply List.countP_eq_length.mpr
        intro p hp
        have hpY : p ∈ Y := List.mem_of_mem_drop hp
        obtain ⟨i,hi⟩ := List.mem_ofFn.mp hpY
        have hi' := (theta i).isLt
        have hpne : p ≠ L := fun he => hrnot (he ▸ hp)
        simp only [decide_eq_true_eq]
        omega
      rw [hall]
      simp [R,Y]
    have hmax1 := inv_window Q [L] R
    have hmax0 := inv_window Q [] R
    simp only [List.append_nil,inv,List.countP_nil,List.map_nil,List.sum_nil,
      List.map_cons,List.sum_cons,Nat.add_zero,
      ← List.countP_eq_length_filter] at hmax1 hmax0
    rw [ysplit] at hmax1
    have hmaxcut := cut_word theta q
    rw [hq] at hmaxcut
    change inv (List.ofFn (fun u => (rho u).val)) = inv (Y.erase L) at hmaxcut
    rw [hyerase] at hmaxcut
    rw [qp,rp] at hmax1
    have maxcost : inv Y = inv (List.ofFn (fun u => (rho u).val)) + (L - q.val) := by
      omega
    change inv X = inv (List.ofFn (fun u => (sd u).val)) +
      P.countP (fun x => decide (L + 1 ≤ x)) + (L - q.val)
    dsimp only [X,a,Y,s,sd,rho,theta] at hc hd maxcost ⊢
    omega
  have prefix_count {m : Nat} (sigma : Equiv.Perm (Fin m)) (r : Nat) (hr : r ≤ m)
      (P : Nat → Prop) [DecidablePred P] :
      ((List.ofFn (fun u => (sigma u).val )).take r).countP (fun x => decide (P x)) =
        (Finset.univ.filter (fun u : Fin m => u.val < r ∧ P (sigma u).val)).card := by
    let U := List.ofFn (fun u : Fin m => u)
    let V := U.take r
    have hm : (List.ofFn (fun u => (sigma u).val)).take r =
        V.map (fun u => (sigma u).val) := by
      dsimp only [V,U]
      simp only [List.map_take,List.map_ofFn,Function.comp_def]
    have hs : V.toFinset = Finset.univ.filter (fun u : Fin m => u.val < r) := by
      ext u
      simp only [List.mem_toFinset,Finset.mem_filter,Finset.mem_univ,true_and]
      change u ∈ U.take r ↔ u.val < r
      rw [List.mem_take_iff_getElem]
      constructor
      · rintro ⟨i,hi,he⟩
        have him : i < m := by simpa only [U,List.length_ofFn] using (lt_min_iff.mp hi).2
        have he' : (⟨i,him⟩ : Fin m) = u := by simpa only [U,List.getElem_ofFn] using he
        have hv := congrArg Fin.val he'
        exact hv ▸ (lt_min_iff.mp hi).1
      · intro hu
        refine ⟨u.val,lt_min_iff.mpr ⟨hu,?_⟩,?_⟩
        · simpa only [U,List.length_ofFn] using u.isLt
        · dsimp only [U]
          rw [List.getElem_ofFn]
    rw [hm,List.countP_map]
    have hn : V.Nodup := (List.nodup_ofFn_ofInjective (fun a b h => h)).take
    have hc := hn.card_eq_countP (P := fun u : Fin m => P (sigma u).val)
    rw [hs,Finset.filter_filter] at hc
    simpa only [Function.comp_def] using hc.symm
  have count_invariance {k L : Nat} (F G : Fin k → Nat)
      (S : Equiv.Perm (Fin (k + 1))) (p : Equiv.Perm (Fin k))
      (hL : L ≤ k + 1) (rho : Equiv.Perm (Fin L))
      (hF : ∀ i, L ≤ F i) (hG : ∀ i, L ≤ G i) :
      ForbiddenCount F G (replace S hL rho) p = ForbiddenCount F G S p := by
    classical
    let sd := replace S hL rho
    have low (u : Fin (k + 1)) : (sd u).val < L ↔ (S u).val < L := by
      dsimp only [sd,replace,Equiv.trans_apply]
      exact Equiv.Perm.ofSubtype_apply_mem_iff_mem (p := fun x : Fin (k + 1) => x.val < L) _ (S u)
    have high (u : Fin (k + 1)) (hu : L ≤ (S u).val) : sd u = S u := by
      dsimp only [sd,replace,Equiv.trans_apply]
      exact Equiv.Perm.ofSubtype_apply_of_not_mem _ (by omega)
    have compare (u v : Fin (k + 1)) (T : Nat) (hT : L ≤ T) :
        (sd u < sd v ∧ T ≤ (sd v).val) ↔ (S u < S v ∧ T ≤ (S v).val) := by
      by_cases hv : (S v).val < L
      · have hdv := (low v).mpr hv
        have hn1 : ¬T ≤ (sd v).val := by omega
        have hn2 : ¬T ≤ (S v).val := by omega
        simp only [hn1,hn2,and_false]
      · rw [high v (by omega)]
        by_cases hu : (S u).val < L
        · have hdu := (low u).mpr hu
          have hc1 : sd u < S v := by change (sd u).val < (S v).val; omega
          have hc2 : S u < S v := by change (S u).val < (S v).val; omega
          simp only [hc1,hc2,true_and]
        · rw [high u (by omega)]
    have hfront (i : Fin k) : Front F sd p i = Front F S p i := by
      ext j
      simp only [Front,Finset.mem_filter,Finset.mem_univ,true_and]
      have hc := compare (p i).castSucc (p j).castSucc (F i) (hF i)
      constructor
      · rintro ⟨hij,hr,hp,ht⟩
        have hh := hc.mp ⟨hr,ht⟩
        exact ⟨hij,hh.1,hp,hh.2⟩
      · rintro ⟨hij,hr,hp,ht⟩
        have hh := hc.mpr ⟨hr,ht⟩
        exact ⟨hij,hh.1,hp,hh.2⟩
    have hback (i : Fin k) : Back G sd p i = Back G S p i := by
      ext j
      cases j with
      | none =>
        simp only [Back,Finset.mem_filter,Finset.mem_univ,true_and]
        exact compare (p i).succ 0 (G i) (hG i)
      | some j =>
        simp only [Back,Finset.mem_filter,Finset.mem_univ,true_and]
        have hc := compare (p i).succ (p j).succ (G i) (hG i)
        constructor
        · rintro ⟨hij,hr,hp,ht⟩
          have hh := hc.mp ⟨hr,ht⟩
          exact ⟨hij,hh.1,hp,hh.2⟩
        · rintro ⟨hij,hr,hp,ht⟩
          have hh := hc.mpr ⟨hr,ht⟩
          exact ⟨hij,hh.1,hp,hh.2⟩
    apply Prod.ext
    · simp only [ForbiddenCount]
      apply Finset.sum_congr rfl
      intro i hi
      rw [hfront]
    · simp only [ForbiddenCount]
      apply Finset.sum_congr rfl
      intro i hi
      rw [hback]
  have digit_partition {k L B : Nat} (hLB : L ≤ B) (hB : B ≤ k + 1)
      (sigma : Equiv.Perm (Fin (k + 2))) (pi : Equiv.Perm (Fin (k + 1)))
      (ha : (sigma (pi 0).castSucc).val < L + 1) :
      (pi 0).val =
        (Finset.univ.filter (fun u : Fin (k + 2) =>
          u.val < (pi 0).val ∧ B + 1 ≤ (sigma u).val)).card +
        ((actualAlgorithms hLB hB).phi sigma pi).2.2 := by
    classical
    let t := pi 0
    let a := sigma t.castSucc
    let s := cut sigma t.castSucc
    let hi := Finset.univ.filter (fun u : Fin (k + 2) => u.val < t.val ∧ B + 1 ≤ (sigma u).val)
    let lo := Finset.univ.filter (fun u : Fin (k + 2) => u.val < t.val ∧ ¬B + 1 ≤ (sigma u).val)
    have low (u : Fin (k + 1)) (hu : u < t) : (s u).val < B ↔ (sigma u.castSucc).val < B + 1 := by
      have hh := (finSuccAboveEquiv a).apply_symm_apply
        ((Equiv.subtypeEquiv sigma (by intro x; exact sigma.injective.ne_iff.symm))
          ((finSuccAboveEquiv t.castSucc) u))
      have he := congrArg Subtype.val hh
      change a.succAbove (s u) = sigma (t.castSucc.succAbove u) at he
      rw [Fin.succAbove_of_castSucc_lt _ _ (show u.castSucc < t.castSucc from hu)] at he
      have hav : a.val ≤ B := by dsimp only [a,t]; omega
      by_cases hv : (s u).castSucc < a
      · rw [Fin.succAbove_of_castSucc_lt _ _ hv] at he
        have he' := congrArg Fin.val he
        have hh : (s u).val < a.val := hv
        simp only [Fin.val_castSucc] at he'
        omega
      · rw [Fin.succAbove_of_le_castSucc _ _ (le_of_not_gt hv)] at he
        have he' := congrArg Fin.val he
        simp only [Fin.val_succ] at he'
        omega
    have hb : (Finset.univ.filter (fun u : Fin (k + 1) =>
        u < t ∧ (s u).val < B)).card = lo.card := by
      apply Finset.card_bij (fun u _ => u.castSucc)
      · intro u hu
        simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hu
        simp only [lo,Finset.mem_filter,Finset.mem_univ,true_and,Fin.val_castSucc]
        exact ⟨hu.1,by have hh := (low u hu.1).mp hu.2; omega⟩
      · intro u hu v hv he
        exact Fin.castSucc_injective _ he
      · intro v hv
        simp only [lo,Finset.mem_filter,Finset.mem_univ,true_and] at hv
        let u : Fin (k + 1) := ⟨v.val,hv.1.trans t.isLt⟩
        have huc : u.castSucc = v := Fin.ext rfl
        have hut : u < t := hv.1
        refine ⟨u,?_,huc⟩
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ _,hut,(low u hut).mpr (by rw [huc]; omega)⟩
    have ht : hi.card + lo.card = t.val := by
      have h := Finset.card_filter_add_card_filter_not
        (p := fun u : Fin (k + 2) => B + 1 ≤ (sigma u).val)
        (s := Finset.Iio t.castSucc)
      have hehi : (Finset.Iio t.castSucc).filter (fun u => B + 1 ≤ (sigma u).val) = hi := by
        ext u
        simp only [Finset.mem_filter,Finset.mem_Iio,hi,Finset.mem_univ,true_and]
        rfl
      have helo : (Finset.Iio t.castSucc).filter (fun u => ¬B + 1 ≤ (sigma u).val) = lo := by
        ext u
        simp only [Finset.mem_filter,Finset.mem_Iio,lo,Finset.mem_univ,true_and]
        rfl
      rw [hehi,helo,Fin.card_Iio] at h
      exact h
    change t.val = hi.card +
      (Finset.univ.filter (fun u : Fin (k + 1) => u < t ∧ (s u).val < B)).card
    rw [hb]
    exact ht.symm
  have column_account {n : Nat} (pi : Equiv.Perm (Fin (n + 1))) :
      I pi = I (cut pi 0) + (pi 0).val := by
    let t := pi 0
    let X := List.ofFn (fun u => (pi u).val)
    let Y := List.ofFn (fun u : Fin n => (pi u.succ).val)
    have hc := cut_word pi 0
    have hx : X = t.val :: Y := by
      dsimp only [X,Y,t]
      exact List.ofFn_succ
    change inv (List.ofFn (fun u => ((cut pi 0) u).val)) = inv (X.erase t.val) at hc
    rw [hx,List.erase_cons_head] at hc
    have hcount := prefix_count pi (n + 1) le_rfl (fun x => x < t.val)
    have htX : X.take (n + 1) = X := List.take_of_length_le (by simp [X])
    change (X.take (n + 1)).countP (fun x => decide (x < t.val)) =
      (Finset.univ.filter (fun u : Fin (n + 1) =>
        u.val < n + 1 ∧ (pi u).val < t.val)).card at hcount
    rw [htX] at hcount
    have hcset : (Finset.univ.filter (fun u : Fin (n + 1) =>
        u.val < n + 1 ∧ (pi u).val < t.val)).card = t.val := by
      conv_rhs => rw [← Fin.card_Iio t]
      apply Finset.card_bij (fun u _ => pi u)
      · intro u hu
        simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hu
        exact Finset.mem_Iio.mpr hu.2
      · intro u hu v hv he
        exact pi.injective he
      · intro v hv
        refine ⟨pi.symm v,?_,pi.apply_symm_apply v⟩
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _,(pi.symm v).isLt,?_⟩
        have hvtFin : v < t := Finset.mem_Iio.mp hv
        have hvt : v.val < t.val := hvtFin
        simpa only [pi.apply_symm_apply] using hvt
    rw [hcset,hx,List.countP_cons] at hcount
    simp only [Nat.lt_irrefl,decide_false,Bool.false_eq_true,ite_false,Nat.add_zero] at hcount
    change inv X = inv (List.ofFn (fun u => ((cut pi 0) u).val)) + t.val
    rw [hx,inv,hc,hcount]
  let hL := hLB.trans hB
  let t := pi 0
  let s := cut sigma t.castSucc
  let p := cut pi 0
  let theta := lowWord sigma (Nat.add_le_add_right hL 1)
  let q := theta.symm (Fin.last L)
  let rho := cut theta q
  let sd := replace s hL rho
  let d := L - q.val
  let b := (Finset.univ.filter (fun u : Fin (k + 1) => u < t ∧ (s u).val < B)).card
  let HA := (Finset.univ.filter (fun u : Fin (k + 2) => u.val < t.val ∧ L + 1 ≤ (sigma u).val)).card
  let HG := (Finset.univ.filter (fun u : Fin (k + 2) => u.val < t.val ∧ B + 1 ≤ (sigma u).val)).card
  let Ft := fun i : Fin k => F i.succ - 1
  let Gt := fun i : Fin k => G i.succ - 1
  have ha : (sigma t.castSucc).val < L + 1 := by simpa only [hF0] using (hel 0).1
  have hr := row_account hL sigma t.castSucc ha
  change I sigma = I sd +
    ((List.ofFn (fun u => (sigma u).val)).take t.val).countP (fun x => decide (L + 1 ≤ x)) + d at hr
  have hpref := prefix_count sigma t.val (by omega) (fun x => L + 1 ≤ x)
  rw [hpref] at hr
  have hp := column_account pi
  have hb := digit_partition hLB hB sigma pi ha
  have raw : I sigma + I pi = I sd + I p + HA + HG + d + b := by
    change I sigma = I sd + HA + d at hr
    change I pi = I p + t.val at hp
    change t.val = HG + b at hb
    omega
  have hFt (i : Fin k) : L ≤ Ft i := by
    have hm := hF (Fin.zero_le i.succ)
    rw [hF0] at hm
    dsimp only [Ft]
    omega
  have hGt (i : Fin k) : L ≤ Gt i := by
    have hm := hG (Fin.zero_le i.succ)
    rw [hG0] at hm
    dsimp only [Gt]
    omega
  have hs := count_invariance Ft Gt s p hL rho hFt hGt
  have hn := ordinary_forbidden_count_contraction F G sigma pi hF hG hFG hel
  simp only [hF0,hG0] at hn
  change (ForbiddenCount F G sigma pi).1 = (ForbiddenCount Ft Gt s p).1 + HA ∧
    (ForbiddenCount F G sigma pi).2 = (ForbiddenCount Ft Gt s p).2 + HG at hn
  rw [← hs] at hn
  have ri : (I sigma : Int) + (I pi : Int) =
      (I sd : Int) + (I p : Int) + (HA : Int) + (HG : Int) + (d : Int) + (b : Int) := by
    exact_mod_cast raw
  change E F G sigma pi = E Ft Gt sd p + (d : Int) + (b : Int)
  unfold E
  rw [hn.1,hn.2]
  push_cast
  dsimp only [sd] at ri ⊢
  omega
end D5.S3.Combinatorics.Permutation.CoupledRepairedWeight
