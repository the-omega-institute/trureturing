/- GID: D5/S1/Words/HughesPeriodicRepair
   generality: G
   mirror-B: D5/B/S1/Words/HughesPeriodicRepair
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Contiguous deletion obstruction for the native periodic insertion repair. -/

import D5.S1.Words.HughesUnaryInsertion
import D5.S1.Words.Powers.WordPower
import Mathlib.Data.Fintype.Fin
import Batteries.Tactic.OpenPrivate

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.HughesPeriodicRepair

open D5.S1.Words.HughesBlockExchange
open D5.S1.Words.UnaryGapWords
open D5.S1.Words.Powers
open D5.S1.Words.Complexity.ShuffleOrders.Binary.BinaryScheduleOrder

open private bump sizes_ne_nil from D5.S1.Words.UnaryGapWords
open private rho_positive starts_rep last_rep terminal_zero from
  D5.S1.Words.HughesUnaryInsertion
open private admissible_endpoints from D5.S1.Words.HughesBlockExchange

variable {α : Type*}
noncomputable section
local instance : DecidableEq α := Classical.decEq α

private theorem power_add (s : List α) (m n : Nat) :
    wordPower (m+n) s = wordPower m s ++ wordPower n s := by
  simp only [wordPower, List.replicate_add, List.flatten_append]

private theorem split_power (T : List α) (n : Nat) (x y : List α)
    (he : x ++ y = wordPower n T) :
    (∃ t r, n=t+r ∧ x=wordPower t T ∧ y=wordPower r T) ∨
    ∃ t r p q, n=t+r+1 ∧ T=p++q ∧ p≠[] ∧ q≠[] ∧
      x=wordPower t T++p ∧ y=q++wordPower r T := by
  induction n generalizing x y with
  | zero =>
    have hx : x=[] := by simpa using (List.append_eq_nil_iff.mp (by simpa using he)).1
    have hy : y=[] := by simpa [hx] using he
    exact Or.inl ⟨0,0,rfl,by simpa using hx,by simpa using hy⟩
  | succ n ih =>
    rw [wordPower_succ] at he
    rcases List.append_eq_append_iff.mp he with ⟨s,hx,hT⟩ | ⟨s,hx,hy⟩
    · by_cases hs : s=[]
      · subst s
        exact Or.inl ⟨1,n,by omega,by simpa using hx.symm,by simpa using hT⟩
      · by_cases hx0 : x=[]
        · subst x
          exact Or.inl ⟨0,n+1,by omega,by simp,by simpa [wordPower_succ] using he⟩
        · exact Or.inr ⟨0,n,x,s,by omega,hx,hx0,hs,by simp,by simpa using hT⟩
    · obtain h | h := ih s y hy.symm
      · obtain ⟨t,r,hn,hs,hy⟩ := h
        exact Or.inl ⟨t+1,r,by omega,by simpa [wordPower_succ,hs] using hx,hy⟩
      · obtain ⟨t,r,p,q,hn,hT,hp,hq,hs,hy⟩ := h
        exact Or.inr ⟨t+1,r,p,q,by omega,hT,hp,hq,
          by simpa [wordPower_succ,hs,List.append_assoc] using hx,hy⟩

private theorem aba_cut (A B : α) (n : Nat) (x y : List α)
    (he : x++y=wordPower n [A,B,A]) :
    (∃ t r, n=t+r ∧ x=wordPower t [A,B,A] ∧ y=wordPower r [A,B,A]) ∨
    (∃ t r, n=t+r+1 ∧ x=wordPower t [A,B,A]++[A] ∧
      y=[B,A]++wordPower r [A,B,A]) ∨
    (∃ t r, n=t+r+1 ∧ x=wordPower t [A,B,A]++[A,B] ∧
      y=[A]++wordPower r [A,B,A]) := by
  obtain h | ⟨t,r,p,q,hn,hT,hp,hq,hx,hy⟩ := split_power [A,B,A] n x y he
  · exact Or.inl h
  · cases p with
    | nil => exact (hp rfl).elim
    | cons c p =>
      cases p with
      | nil =>
        simp only [List.cons_append,List.nil_append,List.cons.injEq] at hT
        rcases hT with ⟨rfl,rfl⟩
        exact Or.inr (Or.inl ⟨t,r,hn,hx,hy⟩)
      | cons d p =>
        cases p with
        | nil =>
          simp only [List.cons_append,List.nil_append,List.cons.injEq] at hT
          rcases hT with ⟨rfl,rfl,rfl⟩
          exact Or.inr (Or.inr ⟨t,r,hn,hx,hy⟩)
        | cons e p =>
          have hl := congrArg List.length hT
          simp only [List.length_cons,List.length_append,List.length_nil] at hl
          have : q=[] := List.length_eq_zero_iff.mp (by omega)
          exact (hq this).elim

private theorem sizes_period (A B : α) (hAB : A≠B) (n d : Nat)
    (w : List α) (ds : List Nat) (hs : sizes A w=d::ds) :
    sizes A (wordPower n [A,B,A]++w) =
      if n=0 then d::ds else 1 :: (List.replicate (n-1) 2 ++ (d+1)::ds) := by
  induction n with
  | zero => simp [hs]
  | succ n ih =>
    rw [wordPower_succ]
    simp only [List.append_assoc,List.cons_append,List.nil_append]
    simp only [sizes, if_pos rfl, if_neg hAB.symm, bump]
    rw [ih]
    by_cases hn : n=0
    · subst n; simp [bump]
    · obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
      simp [bump,List.replicate_succ]

private theorem sizes_power_append (A B : α) (hAB : A ≠ B) (n : Nat) (w : List α) :
    sizes A (wordPower n [A,B,A] ++ w) =
      if n = 0 then sizes A w
      else 1 :: (List.replicate (n-1) 2 ++ bump (sizes A w)) := by
  cases hs : sizes A w with
  | nil => exact (sizes_ne_nil A w hs).elim
  | cons d ds => simpa [hs,bump] using sizes_period A B hAB n d w ds hs

private theorem sizes_power (A B : α) (hAB : A ≠ B) (n : Nat) :
    sizes A (wordPower n [A,B,A]) =
      if n = 0 then [0] else 1 :: (List.replicate (n-1) 2 ++ [1]) := by
  simpa [sizes,bump] using sizes_power_append A B hAB n []

private def signature (A : α) (w : List α) : List Nat :=
  (sizes A w).filter (· ≠ 2)

private theorem signature_boundary (A B : α) (hAB : A ≠ B) (t H J r : Nat) :
    signature A (wordPower t [A,B,A] ++
      (wordPower H [A,B,A] ++ [A,B,A,B,A] ++ wordPower J [A,B,A]) ++
        wordPower r [A,B,A]) = [1,1,1] := by
  have he : wordPower t [A,B,A] ++
      (wordPower H [A,B,A] ++ [A,B,A,B,A] ++ wordPower J [A,B,A]) ++
        wordPower r [A,B,A] =
      wordPower (t+H) [A,B,A] ++ [A,B,A,B,A] ++ wordPower (J+r) [A,B,A] := by
    simp only [power_add,List.append_assoc]
  rw [he]
  generalize t+H=tt
  generalize J+r=rr
  by_cases ht : tt=0 <;> by_cases hr : rr=0 <;>
    simp [signature,List.append_assoc,sizes_power_append A B hAB,
      sizes_power A B hAB,ht,hr,sizes,hAB.symm,bump,List.filter_append]

private theorem signature_first_cut (A B : α) (hAB : A ≠ B) (t H J r : Nat) :
    signature A ((wordPower t [A,B,A] ++ [A]) ++
      (wordPower H [A,B,A] ++ [A,B,A,B,A] ++ wordPower J [A,B,A]) ++
        ([B,A] ++ wordPower r [A,B,A])) =
      if t=0 then [1,1,1] else [1,3,1,1,1] := by
  by_cases ht : t=0 <;> by_cases hh : H=0 <;>
    by_cases hj : J=0 <;> by_cases hr : r=0 <;>
    simp [signature,List.append_assoc,sizes_power_append A B hAB,
      sizes_power A B hAB,ht,hh,hj,hr,sizes,hAB.symm,bump,List.filter_append]

private theorem signature_second_cut (A B : α) (hAB : A ≠ B) (t H J r : Nat) :
    signature A ((wordPower t [A,B,A] ++ [A,B]) ++
      (wordPower H [A,B,A] ++ [A,B,A,B,A] ++ wordPower J [A,B,A]) ++
        ([A] ++ wordPower r [A,B,A])) =
      if r=0 then [1,1,1] else [1,1,1,3,1] := by
  by_cases ht : t=0 <;> by_cases hh : H=0 <;>
    by_cases hj : J=0 <;> by_cases hr : r=0 <;>
    simp [signature,List.append_assoc,sizes_power_append A B hAB,
      sizes_power A B hAB,ht,hh,hj,hr,sizes,hAB.symm,bump,List.filter_append]

private theorem signature_successor (A B : α) (hAB : A ≠ B) (H J K L : Nat) :
    signature A (wordPower K [A,B,A] ++ [A,B] ++ wordPower (H+1) [A,B,A] ++
      [A] ++ wordPower (L+1) [A,B,A] ++ [B,A] ++ wordPower J [A,B,A]) =
      [1,1,3,1,1] := by
  by_cases hk : K=0 <;> by_cases hj : J=0 <;>
    simp [signature,List.append_assoc,sizes_power_append A B hAB,
      sizes_power A B hAB,hk,hj,sizes,hAB.symm,bump,List.filter_append]

private theorem no_deletion (A B : α) (hAB : A ≠ B) (H J K L : Nat)
    (x y : List α)
    (hv : x++y = wordPower (K+L+2) [A,B,A]) :
    x ++ (wordPower H [A,B,A] ++ [A,B,A,B,A] ++ wordPower J [A,B,A]) ++ y ≠
      wordPower K [A,B,A] ++ [A,B] ++ wordPower (H+1) [A,B,A] ++
        [A] ++ wordPower (L+1) [A,B,A] ++ [B,A] ++ wordPower J [A,B,A] := by
  intro he
  have hs := congrArg (signature A) he
  rw [signature_successor A B hAB] at hs
  obtain ⟨t,r,_,rfl,rfl⟩ | ⟨t,r,_,rfl,rfl⟩ | ⟨t,r,_,rfl,rfl⟩ :=
    aba_cut A B (K+L+2) x y hv
  · rw [signature_boundary A B hAB] at hs
    simp at hs
  · rw [signature_first_cut A B hAB] at hs
    split_ifs at hs <;> simp at hs
  · rw [signature_second_cut A B hAB] at hs
    split_ifs at hs <;> simp at hs

private theorem valid_append (u v w u' v' w' : List α) (M N : List Side)
    (hM : ValidMask u v w M) (hN : ValidMask u' v' w' N) :
    ValidMask (u++u') (v++v') (w++w') (M++N) := by
  obtain ⟨hl,hU,hV⟩ := (mask_projections _ _ _ _).mp hM
  obtain ⟨hl',hU',hV'⟩ := (mask_projections _ _ _ _).mp hN
  apply (mask_projections _ _ _ _).mpr
  exact ⟨by simp [hl,hl'],
    by rw [projection_append _ _ _ _ _ hl.symm,hU,hU'],
    by rw [projection_append _ _ _ _ _ hl.symm,hV,hV']⟩

private theorem valid_first (u : List α) :
    ValidMask u [] u (List.replicate u.length .first) := by
  apply (mask_projections _ _ _ _).mpr
  simp [projection_pure]

private theorem valid_second (v : List α) :
    ValidMask [] v v (List.replicate v.length .second) := by
  apply (mask_projections _ _ _ _).mpr
  simp [projection_pure]

private theorem one_run_shape (M : List Side) (hr : rho M=1) :
    ∃ p q r : Nat, M=List.replicate p .second ++
      List.replicate q .first ++ List.replicate r .second := by
  induction M with
  | nil => simp [rho_starts,starts] at hr
  | cons s M ih =>
    cases s with
    | first =>
      have hz : starts .first M=0 := by
        simp only [rho_starts,starts,step] at hr
        simp at hr
        omega
      obtain ⟨q,r,he⟩ := terminal_zero M hz
      exact ⟨0,q+1,r,by simp [he,List.replicate_succ]⟩
    | second =>
      obtain ⟨p,q,r,he⟩ := ih (by simpa [rho_starts,starts,step] using hr)
      exact ⟨p+1,q,r,by simp [he,List.replicate_succ,List.append_assoc]⟩

private theorem mask_one_deletion (u v w : List α) (M : List Side)
    (hM : ValidMask u v w M) (hr : rho M=1) :
    ∃ x y : List α, w=x++u++y ∧ v=x++y := by
  obtain ⟨p,q,r,hshape⟩ := one_run_shape M hr
  obtain ⟨hl,hU,hV⟩ := (mask_projections _ _ _ _).mp hM
  have hlen : p+q+r=w.length := by simpa [hshape,Nat.add_assoc] using hl
  let x := w.take p
  let a := (w.drop p).take q
  let y := (w.drop p).drop q
  have lx : x.length=p := by simp [x]; omega
  have la : a.length=q := by simp [a]; omega
  have ly : y.length=r := by simp [y]; omega
  have hw : w=x++a++y := by
    dsimp [x,a,y]
    rw [List.append_assoc,List.take_append_drop,List.take_append_drop]
  have hmask : M=List.replicate x.length .second ++
      List.replicate a.length .first ++ List.replicate y.length .second := by
    simpa [lx,la,ly] using hshape
  rw [hw,hmask] at hU hV
  simp only [List.append_assoc] at hU hV
  rw [projection_append _ _ _ _ _ (by simp),
    projection_append _ _ _ _ _ (by simp)] at hU hV
  simp only [projection_pure,ite_true,reduceCtorEq,ite_false,List.nil_append,
    List.append_nil] at hU hV
  exact ⟨x,y,by simpa [hU] using hw,hV.symm⟩

private theorem mask_positive (u v w : List α) (hu : u≠[]) (M : List Side)
    (hM : ValidMask u v w M) : 0<rho M := by
  apply rho_positive
  have hc : M.count .first=u.length := hM.1.1
  rw [hc]
  exact List.length_pos_iff.mpr hu

private theorem degree_one_iff (u v w : List α) (hu : u≠[]) :
    degree u v w=((1 : Nat) : WithTop Nat) ↔
      ∃ x y : List α, w=x++u++y ∧ v=x++y := by
  classical
  constructor
  · intro he
    unfold degree minRuns at he
    split at he
    · rename_i hex
      obtain ⟨M,hM,hr⟩ := Nat.find_spec hex
      have hn : Nat.find hex=1 := by exact_mod_cast he
      exact mask_one_deletion u v w M hM (hr.trans hn)
    · simp at he
  · rintro ⟨x,y,rfl,rfl⟩
    let M := List.replicate x.length Side.second ++
      List.replicate u.length Side.first ++ List.replicate y.length Side.second
    have hM : ValidMask u (x++y) (x++u++y) M := by
      simpa [M] using valid_append _ _ _ _ _ _ _ _
        (valid_append _ _ _ _ _ _ _ _ (valid_second x) (valid_first u))
        (valid_second y)
    have hr : rho M=1 := by
      have hp : u.length≠0 := Nat.ne_of_gt (List.length_pos_iff.mpr hu)
      simp [M,rho_starts,starts_append,starts_rep,last_rep,step,hp]
    apply le_antisymm
    · simpa [degree,hr] using minRuns_le _ M hM
    · apply (le_minRuns _ _).mpr
      intro N hN
      have hp := mask_positive u (x++y) (x++u++y) hu N hN
      exact_mod_cast hp

/-- The predecessors H,J,K,L range over all naturals, so all four positive
parameters H+1,J+1,K+1,L+1, including 1, occur. -/
theorem shifted_successor_degree (A B : α) (hAB : A≠B) (H J K L : Nat) :
    degree
      (wordPower H [A,B,A] ++ [A,B,A,B,A] ++ wordPower J [A,B,A])
      (wordPower ((K+1)+(L+1)) [A,B,A])
      (wordPower K [A,B,A] ++ [A,B] ++ wordPower (H+1) [A,B,A] ++
        [A] ++ wordPower (L+1) [A,B,A] ++ [B,A] ++ wordPower J [A,B,A]) =
      ((2 : Nat) : WithTop Nat) := by
  let u := wordPower H [A,B,A] ++ [A,B,A,B,A] ++ wordPower J [A,B,A]
  let v := wordPower ((K+1)+(L+1)) [A,B,A]
  let X := wordPower K [A,B,A] ++ [A,B]
  let P := wordPower (H+1) [A,B,A]
  let Q := [A] ++ wordPower (L+1) [A,B,A]
  let C := [B,A] ++ wordPower J [A,B,A]
  let z := X++P++Q++C
  have hU : P++C=u := by
    simp only [P,C,u,power_add,wordPower_one,List.append_assoc,List.cons_append,
      List.nil_append]
  have hV : X++Q=v := by
    dsimp [X,Q,v]
    rw [power_add _ (K+1) (L+1),power_add _ K 1]
    simp only [wordPower_one,List.append_assoc,List.cons_append,List.nil_append]
  let M := List.replicate X.length Side.second ++ List.replicate P.length Side.first ++
    List.replicate Q.length Side.second ++ List.replicate C.length Side.first
  have hM : ValidMask u v z M := by
    rw [←hU,←hV]
    simpa only [List.nil_append,List.append_nil] using
      valid_append _ _ _ _ _ _ _ _
        (valid_append _ _ _ _ _ _ _ _
          (valid_append _ _ _ _ _ _ _ _ (valid_second X) (valid_first P))
          (valid_second Q)) (valid_first C)
  have hp : P.length≠0 := by simp [P,length_wordPower]
  have hq : Q.length≠0 := by simp [Q]
  have hc : C.length≠0 := by simp [C]
  have hr : rho M=2 := by
    simp [M,List.append_assoc,rho_starts,starts_append,
      starts_rep,last_rep,step,hp,hq,hc]
  have hu : u≠[] := by simp [u]
  have hz : z = wordPower K [A,B,A] ++ [A,B] ++ wordPower (H+1) [A,B,A] ++
      [A] ++ wordPower (L+1) [A,B,A] ++ [B,A] ++ wordPower J [A,B,A] := by
    simp only [z,X,P,Q,C,List.append_assoc,List.cons_append,List.nil_append]
  rw [←hz]
  change degree u v z = _
  have hlow : ((1 : Nat) : WithTop Nat) ≤ degree u v z := by
    apply (le_minRuns _ _).mpr
    intro N hN
    have hp := mask_positive u v z hu N hN
    exact_mod_cast hp
  have hnone : degree u v z ≠ ((1 : Nat) : WithTop Nat) := by
    intro hd
    obtain ⟨x,y,hw,hv⟩ := (degree_one_iff u v z hu).mp hd
    apply no_deletion A B hAB H J K L x y
      (by simpa [v,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hv.symm)
    simpa only [u,hz] using hw.symm
  apply le_antisymm
  · simpa [degree,hr] using minRuns_le _ M hM
  · apply (le_minRuns _ _).mpr
    intro N hN
    have hpos := mask_positive u v z hu N hN
    have hnot : rho N≠1 := by
      intro hone
      apply hnone
      apply le_antisymm _ hlow
      simpa [degree,hone] using minRuns_le _ N hN
    have hl : 2≤rho N := by omega
    exact_mod_cast hl

def fiveMask (a p b q c : List α) : List Side :=
  List.replicate a.length .first ++ List.replicate p.length .second ++
    List.replicate b.length .first ++ List.replicate q.length .second ++
      List.replicate c.length .first

def fourCuts (a p b q c : List α) (i : Fin 4) : BlockCut α :=
  match i.val with
  | 0 => ⟨[],a,p,b++q++c⟩
  | 1 => ⟨a,p,b,q++c⟩
  | 2 => ⟨a++p,b,q,c⟩
  | _ => ⟨a++p++b,q,c,[]⟩

private theorem five_valid (a p b q c : List α) :
    ValidMask (a++b++c) (p++q) (a++p++b++q++c) (fiveMask a p b q c) := by
  simpa only [List.nil_append,List.append_nil,fiveMask] using
    valid_append _ _ _ _ _ _ _ _
      (valid_append _ _ _ _ _ _ _ _
        (valid_append _ _ _ _ _ _ _ _
          (valid_append _ _ _ _ _ _ _ _ (valid_first a) (valid_second p))
          (valid_first b)) (valid_second q)) (valid_first c)

private theorem five_runs (a p b q c : List α)
    (ha : a≠[]) (hp : p≠[]) (hb : b≠[]) (hq : q≠[]) (hc : c≠[]) :
    rho (fiveMask a p b q c)=3 := by
  have ha' := Nat.ne_of_gt (List.length_pos_iff.mpr ha)
  have hp' := Nat.ne_of_gt (List.length_pos_iff.mpr hp)
  have hb' := Nat.ne_of_gt (List.length_pos_iff.mpr hb)
  have hq' := Nat.ne_of_gt (List.length_pos_iff.mpr hq)
  have hc' := Nat.ne_of_gt (List.length_pos_iff.mpr hc)
  simp [fiveMask,List.append_assoc,rho_starts,starts_append,
    starts_rep,last_rep,step,ha',hp',hb',hq',hc']

private theorem five_admissible (a p b q c : List α)
    (ha : a≠[]) (hp : p≠[]) (hb : b≠[]) (hq : q≠[]) (hc : c≠[]) (i : Fin 4) :
    original (fourCuts a p b q c i)=a++p++b++q++c ∧
      Admissible (fourCuts a p b q c i) (fiveMask a p b q c) := by
  have ha' := Nat.ne_of_gt (List.length_pos_iff.mpr ha)
  have hp' := Nat.ne_of_gt (List.length_pos_iff.mpr hp)
  have hb' := Nat.ne_of_gt (List.length_pos_iff.mpr hb)
  have hq' := Nat.ne_of_gt (List.length_pos_iff.mpr hq)
  have hc' := Nat.ne_of_gt (List.length_pos_iff.mpr hc)
  fin_cases i
  · constructor
    · simp [fourCuts,original,List.append_assoc]
    · apply (admissible_endpoints _ _).mpr
      refine ⟨ha,hp,⟨[],List.replicate a.length .first,
        List.replicate p.length .second,List.replicate b.length .first ++
          List.replicate q.length .second ++ List.replicate c.length .first⟩,
        ?_,?_,Or.inl ⟨rfl,rfl,?_,?_⟩⟩
      · exact ⟨rfl,by simp [fourCuts],by simp [fourCuts],by simp [fourCuts]⟩
      · change fiveMask a p b q c = [] ++ List.replicate a.length .first ++
          List.replicate p.length .second ++ (List.replicate b.length .first ++
            List.replicate q.length .second ++ List.replicate c.length .first)
        simp [fiveMask,List.append_assoc]
      · simp
      · simp [List.head?_append,List.head?_replicate,hb']
  · constructor
    · simp [fourCuts,original,List.append_assoc]
    · apply (admissible_endpoints _ _).mpr
      refine ⟨hp,hb,⟨List.replicate a.length .first,List.replicate p.length .second,
        List.replicate b.length .first,List.replicate q.length .second ++
          List.replicate c.length .first⟩,?_,?_,Or.inr ⟨rfl,rfl,?_,?_⟩⟩
      · exact ⟨by simp [fourCuts],by simp [fourCuts],by simp [fourCuts],
          by simp [fourCuts]⟩
      · change fiveMask a p b q c = List.replicate a.length .first ++
          List.replicate p.length .second ++ List.replicate b.length .first ++
            (List.replicate q.length .second ++ List.replicate c.length .first)
        simp only [fiveMask,List.append_assoc]
      · simp [List.getLast?_replicate,ha']
      · simp [List.head?_append,List.head?_replicate,hq']
  · constructor
    · simp [fourCuts,original,List.append_assoc]
    · apply (admissible_endpoints _ _).mpr
      refine ⟨hb,hq,⟨List.replicate a.length .first ++ List.replicate p.length .second,
        List.replicate b.length .first,List.replicate q.length .second,
        List.replicate c.length .first⟩,?_,?_,Or.inl ⟨rfl,rfl,?_,?_⟩⟩
      · exact ⟨by simp [fourCuts],by simp [fourCuts],by simp [fourCuts],
          by simp [fourCuts]⟩
      · rfl
      · simp [List.getLast?_append,List.getLast?_replicate,hp']
      · simp [List.head?_replicate,hc']
  · constructor
    · simp [fourCuts,original,List.append_assoc]
    · apply (admissible_endpoints _ _).mpr
      refine ⟨hq,hc,⟨List.replicate a.length .first ++ List.replicate p.length .second ++
        List.replicate b.length .first,List.replicate q.length .second,
        List.replicate c.length .first,[]⟩,?_,?_,Or.inr ⟨rfl,rfl,?_,?_⟩⟩
      · exact ⟨by simp [fourCuts],by simp [fourCuts],by simp [fourCuts],rfl⟩
      · change fiveMask a p b q c = (List.replicate a.length .first ++
          List.replicate p.length .second ++ List.replicate b.length .first) ++
            List.replicate q.length .second ++ List.replicate c.length .first ++ []
        simp only [fiveMask,List.append_nil]
      · simp [List.getLast?_append,List.getLast?_replicate,hb']
      · simp

private theorem power_commute (T : List α) (m n : Nat) :
    wordPower m T ++ wordPower n T = wordPower n T ++ wordPower m T := by
  rw [←power_add,←power_add,Nat.add_comm]

private theorem minimum_of_degree (u v w : List α) (M : List Side) (r : Nat)
    (hM : ValidMask u v w M) (hr : rho M=r)
    (hd : degree u v w=(r : WithTop Nat)) : IsMinimumMask u v w M r := by
  refine ⟨hM,hr,?_⟩
  intro N hN
  have he := minRuns_le _ N hN
  change degree u v w ≤ (rho N : WithTop Nat) at he
  rw [hd] at he
  exact_mod_cast he

/-- Original and shifted native masks, their specified maximal exchanges, and
the conditional alternative-minimum conclusion. -/
theorem periodic_repair (A B : α) (hAB : A≠B) (H J K L : Nat) :
    let a := wordPower H [A,B,A] ++ [A,B]
    let c := [B,A] ++ wordPower J [A,B,A]
    let p := wordPower (K+1) [A,B,A]
    let q := wordPower (L+1) [A,B,A]
    let x := wordPower K [A,B,A] ++ [A,B]
    let u := a++[A]++c
    let v := p++q
    let w := a++p++[A]++q++c
    let M := fiveMask a p [A] q c
    let N := fiveMask a x [A] ([A]++q) c
    let E := fourCuts a x [A] ([A]++q) c 0
    ValidMask u v w M ∧ rho M=3 ∧
    (∀ i : Fin 4, original (fourCuts a p [A] q c i)=w ∧
      Admissible (fourCuts a p [A] q c i) M ∧
      successor (fourCuts a p [A] q c i)=(if i.val<2 then v++u else u++v) ∧
      degree u v (successor (fourCuts a p [A] q c i))=((1 : Nat) : WithTop Nat)) ∧
    ValidMask u v w N ∧ rho N=3 ∧ original E=w ∧ Admissible E N ∧
    successor E=wordPower K [A,B,A] ++ [A,B] ++ wordPower (H+1) [A,B,A] ++
      [A] ++ q ++ [B,A] ++ wordPower J [A,B,A] ∧
    degree u v (successor E)=((2 : Nat) : WithTop Nat) ∧
    (degree u v w=((3 : Nat) : WithTop Nat) →
      IsMinimumMask u v w M 3 ∧ IsMinimumMask u v w N 3) := by
  dsimp only
  let a := wordPower H [A,B,A] ++ [A,B]
  let c := [B,A] ++ wordPower J [A,B,A]
  let p := wordPower (K+1) [A,B,A]
  let q := wordPower (L+1) [A,B,A]
  let x := wordPower K [A,B,A] ++ [A,B]
  have ha : a≠[] := by simp [a]
  have hc : c≠[] := by simp [c]
  have hp : p≠[] := by simp [p,wordPower_succ]
  have hq : q≠[] := by simp [q,wordPower_succ]
  have hx : x≠[] := by simp [x]
  have hA : [A]≠[] := by simp
  have hAq : [A]++q≠[] := by simp
  have hax : a++[A]=wordPower (H+1) [A,B,A] := by
    simp only [a,power_add,wordPower_one,List.append_assoc,List.cons_append,List.nil_append]
  have hAc : [A]++c=wordPower (J+1) [A,B,A] := by
    simp only [c,wordPower_succ,List.append_assoc,List.cons_append,List.nil_append]
  have hpx : p=x++[A] := by
    simp only [p,x,power_add,wordPower_one,List.append_assoc,List.cons_append,List.nil_append]
  have hv : p++q=wordPower ((K+1)+(L+1)) [A,B,A] := (power_add _ _ _).symm
  have hN : ValidMask (a++[A]++c) (p++q) (a++p++[A]++q++c)
      (fiveMask a x [A] ([A]++q) c) := by
    simpa only [hpx,List.append_assoc] using five_valid a x [A] ([A]++q) c
  have rM := five_runs a p [A] q c ha hp hA hq hc
  have rN := five_runs a x [A] ([A]++q) c ha hx hA hAq hc
  have hE := five_admissible a x [A] ([A]++q) c ha hx hA hAq hc 0
  have hEw : original (fourCuts a x [A] ([A]++q) c 0)=a++p++[A]++q++c := by
    simpa only [hpx,List.append_assoc] using hE.1
  have hEz : successor (fourCuts a x [A] ([A]++q) c 0)=
      wordPower K [A,B,A] ++ [A,B] ++ wordPower (H+1) [A,B,A] ++
        [A] ++ q ++ [B,A] ++ wordPower J [A,B,A] := by
    change x++a++([A]++([A]++q)++c) = _
    calc
      _ = x++(a++[A])++[A]++q++c := by simp only [List.append_assoc]
      _ = _ := by rw [hax]; simp only [x,c,List.append_assoc]
  refine ⟨five_valid a p [A] q c,rM,?_,hN,rN,hEw,hE.2,hEz,?_,?_⟩
  · intro i
    change original (fourCuts a p [A] q c i)=a++p++[A]++q++c ∧
      Admissible (fourCuts a p [A] q c i) (fiveMask a p [A] q c) ∧
      successor (fourCuts a p [A] q c i)=
        (if i.val<2 then (p++q)++(a++[A]++c) else (a++[A]++c)++(p++q)) ∧
      degree (a++[A]++c) (p++q) (successor (fourCuts a p [A] q c i))=
        ((1 : Nat) : WithTop Nat)
    have hi := five_admissible a p [A] q c ha hp hA hq hc i
    have hHq : (a++[A])++q=q++(a++[A]) := by
      rw [hax]
      exact power_commute _ (H+1) (L+1)
    have hHv : (a++[A])++(p++q)=(p++q)++(a++[A]) := by
      rw [hax,hv]
      exact power_commute _ (H+1) ((K+1)+(L+1))
    have hvJ : (p++q)++([A]++c)=([A]++c)++(p++q) := by
      rw [hv,hAc]
      exact power_commute _ ((K+1)+(L+1)) (J+1)
    have hpJ : p++([A]++c)=([A]++c)++p := by
      rw [hAc]
      exact power_commute _ (K+1) (J+1)
    have hword : successor (fourCuts a p [A] q c i)=
        (if i.val<2 then (p++q)++(a++[A]++c) else (a++[A]++c)++(p++q)) := by
      fin_cases i
      · change p++a++([A]++q++c)=(p++q)++(a++[A]++c)
        calc
          _ = p++((a++[A])++q)++c := by simp only [List.append_assoc]
          _ = p++(q++(a++[A]))++c := by rw [hHq]
          _ = _ := by simp only [List.append_assoc]
      · change a++[A]++p++(q++c)=(p++q)++(a++[A]++c)
        calc
          _ = ((a++[A])++(p++q))++c := by simp only [List.append_assoc]
          _ = ((p++q)++(a++[A]))++c := by rw [hHv]
          _ = _ := by simp only [List.append_assoc]
      · simp only [show ¬(2 : Nat)<2 by omega,if_false]
        change (a++p)++q++[A]++c=(a++[A]++c)++(p++q)
        calc
          _ = a++((p++q)++([A]++c)) := by simp only [List.append_assoc]
          _ = a++(([A]++c)++(p++q)) := by rw [hvJ]
          _ = _ := by simp only [List.append_assoc]
      · simp only [show ¬(3 : Nat)<2 by omega,if_false]
        change (a++p++[A])++c++q++[]=(a++[A]++c)++(p++q)
        calc
          _ = a++(p++([A]++c))++q := by simp only [List.append_assoc,List.append_nil]
          _ = a++(([A]++c)++p)++q := by rw [hpJ]
          _ = _ := by simp only [List.append_assoc]
    refine ⟨hi.1,hi.2,hword,?_⟩
    rw [hword]
    have hu : a++[A]++c≠[] := by simp
    split_ifs
    · apply (degree_one_iff _ _ _ hu).mpr
      exact ⟨p++q,[],by simp,by simp⟩
    · apply (degree_one_iff _ _ _ hu).mpr
      exact ⟨[],p++q,by simp,by simp⟩
  · rw [hEz,hv]
    simpa only [a,c,q,List.append_assoc,List.cons_append,List.nil_append] using
      shifted_successor_degree A B hAB H J K L
  · intro hd
    exact ⟨minimum_of_degree _ _ _ _ 3 (five_valid a p [A] q c) rM hd,
      minimum_of_degree _ _ _ _ 3 hN rN hd⟩

#print axioms shifted_successor_degree
#print axioms periodic_repair

end
end D5.S1.Words.HughesPeriodicRepair
