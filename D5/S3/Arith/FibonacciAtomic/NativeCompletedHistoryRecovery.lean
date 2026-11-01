/- GID: D5/S3/Arith/FibonacciAtomic/NativeCompletedHistoryRecovery
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Native overlap recognition recovers every unknown entry and literal completed history. -/

import D5.S3.Arith.FibonacciAtomic.NativeLocalSourceExecution
import D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeFiniteNormalInversion
import D5.S3.Arith.FibonacciAtomic.SourceTransportCentralizer
import D5.S3.Arith.FibonacciAtomic.Geometry.NativeGuardedLeafRepair
import D5.S3.Arith.FibonacciAtomic.SourceCoordinates.IntrinsicSubstitutionCoordinates

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.NativeCompletedHistoryRecovery

open GenealogicalFiberTransport (Source substitution composition)
open NativeLocalSourceExecution (Native native eventIndex splitLeft)
open Observer.NativeFiniteNormalInversion (encode expand inverseCode finite_normal_inverse)

inductive Letter where
  | F | G
  deriving DecidableEq

def act : Letter → Source → Source
  | .F, t => substitution t
  | .G, t => splitLeft t

/-- Literal chronological words, including the empty list. -/
def run (t : Source) (W : List Letter) : Source := W.foldl (fun s X => act X s) t

/-- Collapse exactly the deepest left-spine beta/alpha pair. -/
def collapse : Source → Option Source
  | .of _ => none
  | .mul l r =>
    if l = .of false ∧ r = .of true then some (.of false)
    else (collapse l).map (fun p => .mul p r)

/-- Existing finite normal inversion supplies a candidate; literal replay
validates it on all inputs, including those outside the actual image. -/
def rhoPredecessor (z : Source) : Option Source := do
  let D ← inverseCode 1 (encode z)
  let p := expand D
  if substitution p = z then some p else none

/-- Right subtrees are replaced, while the terminal left beta is retained. -/
def H : Source → Source
  | .of b => .of b
  | .mul l r => .mul (H l) (substitution r)

def previous (n0 : Nat) (z : Source) : Option (Source × Letter) := do
  let c ← collapse z
  if eventIndex c = n0 ∨ (collapse c).isSome then some (c,.G)
  else do
    let p ← rhoPredecessor z
    if Native p then some (p,.F) else none

/-- One recursive computation returns its accepted predecessor count and answer.
The count includes accepted descents even when a later check rejects. -/
def recoverFuel (fuel n0 : Nat) (z : Source) : Nat × Option (Source × List Letter) :=
    if n0 ≤ 1 ∨ ¬ Native z ∨ eventIndex z < n0 then (0,none)
    else if eventIndex z = n0 then (0,some (z,[]))
    else match fuel with
      | 0 => (0,none)
      | k+1 => match previous n0 z with
        | none => (0,none)
        | some (p,X) =>
          if n0 ≤ eventIndex p ∧ eventIndex p < eventIndex z then
            let d := recoverFuel k n0 p
            (d.1+1,d.2.map (fun a => (a.1,a.2 ++ [X])))
          else (0,none)

def recover (n0 : Nat) (z : Source) : Option (Source × List Letter) :=
  (recoverFuel (eventIndex z - n0) n0 z).2

/-- This is the first projection of the same execution used by recover. -/
def recoverySteps (n0 : Nat) (z : Source) : Nat :=
  (recoverFuel (eventIndex z - n0) n0 z).1

private theorem act_native (X : Letter) (t : Source) (h : Native t) : Native (act X t) := by
  cases X with
  | F => exact (NativeLocalSourceExecution.native_execution.1 t).2.2
  | G => exact (NativeLocalSourceExecution.native_execution.2.1 t h).2.1

private theorem act_index (X : Letter) (t : Source) (h : Native t) :
    eventIndex (act X t) = eventIndex t + (match X with | .F => t.length | .G => 1) := by
  cases X with
  | F => exact (NativeLocalSourceExecution.native_execution.2.2.2.1 t h).1
  | G => exact (NativeLocalSourceExecution.native_execution.2.2.2.1 t h).2.1

private theorem run_append (t : Source) (V W : List Letter) :
    run t (V ++ W) = run (run t V) W := by simp [run, List.foldl_append]

private theorem run_native (t : Source) (hn : Native t) (W : List Letter) : Native (run t W) := by
  induction W using List.reverseRecOn with
  | nil => exact hn
  | append_singleton W X ih =>
    rw [run_append]
    change Native (act X (run t W))
    exact act_native X _ ih

private theorem run_bound (t : Source) (hn : Native t) (W : List Letter) :
    eventIndex t + W.length ≤ eventIndex (run t W) := by
  induction W using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton W X ih =>
    have step := act_index X (run t W) (run_native t hn W)
    have pos := (run t W).length_pos
    rw [run_append]
    change eventIndex t + (W ++ [X]).length ≤ eventIndex (act X (run t W))
    simp only [List.length_append, List.length_singleton]
    cases X <;> simp only at step <;> omega

private theorem g_not_beta (t : Source) : splitLeft t ≠ .of false := by
  cases t with
  | of b => cases b <;> intro h <;> cases h
  | mul l r => intro h; cases h

private theorem collapse_g (t : Source) (hn : Native t) : collapse (splitLeft t) = some t := by
  induction t with
  | of b => cases b <;> simp_all [Native, native, splitLeft, collapse]
  | mul l r ihl ihr =>
    have hl := (Bool.and_eq_true_iff.mp hn).1
    simp only [splitLeft, collapse, g_not_beta l, false_and, ↓reduceIte, ihl hl,
      Option.map_some]

private theorem collapse_sound (z p : Source) (h : collapse z = some p) :
    splitLeft p = z ∧ (Native z → Native p) := by
  induction z generalizing p with
  | of b => cases h
  | mul l r ihl ihr =>
    simp only [collapse] at h
    split_ifs at h with special
    · rcases special with ⟨rfl,rfl⟩
      cases h
      exact ⟨rfl,fun _ => rfl⟩
    · obtain ⟨q,hq,rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨eq,hn⟩ := ihl q hq
      refine ⟨congrArg (fun x => FreeMagma.mul x r) eq, ?_⟩
      intro native_z
      obtain ⟨hl,hr⟩ := Bool.and_eq_true_iff.mp native_z
      exact Bool.and_eq_true_iff.mpr ⟨hn hl,hr⟩

private theorem rho_not_alpha (t : Source) : substitution t ≠ .of true := by
  exact SourceCoordinates.IntrinsicSubstitutionCoordinates.no_alpha t

private theorem H_native (t : Source) (hn : Native t) : Native (H t) := by
  induction t with
  | of b => exact hn
  | mul l r ihl ihr =>
    obtain ⟨hl,hr⟩ := Bool.and_eq_true_iff.mp hn
    have sub : native true (substitution r) = true := by
      cases eq : substitution r with
      | of b => simp [native]
      | mul a b =>
        simpa only [Native,eq,native] using (NativeLocalSourceExecution.native_execution.1 r).2.2
    exact Bool.and_eq_true_iff.mpr ⟨ihl hl,sub⟩

private theorem f_eq_g_H (t : Source) (hn : Native t) : substitution t = splitLeft (H t) := by
  induction t with
  | of b => cases b <;> simp_all [Native,native,H,splitLeft,substitution,FreeMagma.lift_of]
  | mul l r ihl ihr =>
    have hl := (Bool.and_eq_true_iff.mp hn).1
    exact congrArg (fun x => FreeMagma.mul x (substitution r)) (ihl hl)

private theorem collapse_H (t : Source) : collapse (H t) = none := by
  induction t with
  | of b => rfl
  | mul l r ihl ihr => simp [H,collapse,rho_not_alpha,ihl]

private theorem H_index (t : Source) (hn : Native t) :
    eventIndex (H t) + 1 = eventIndex t + t.length := by
  have f := act_index .F t hn
  have g := act_index .G (H t) (H_native t hn)
  change eventIndex (substitution t) = _ at f
  rw [f_eq_g_H t hn] at f
  exact g.symm.trans f

private theorem rho_predecessor_sound (z p : Source) (h : rhoPredecessor z = some p) :
    substitution p = z := by
  obtain ⟨D,hD,h⟩ := Option.bind_eq_some_iff.mp h
  dsimp only at h
  split_ifs at h with eq
  cases h
  exact eq

private theorem rho_predecessor_complete (t : Source) : rhoPredecessor (substitution t) = some t := by
  have image : Observer.NativeImageSaturationInterface.NativeImage 1
      (Observer.NativeCompletionPrefixLifting.embed (substitution t)) := by
    refine ⟨Observer.NativeCompletionPrefixLifting.embed t, ?_⟩
    exact Observer.CompletionHomogeneousFixedPoints.iterate_embed 1 t
  obtain ⟨_,_,D,⟨hD,_,eq⟩,_⟩ := finite_normal_inverse 1 (substitution t) image
  have inj : Function.Injective substitution :=
    SourceTransportCentralizer.source_transport_centralizer.2.2.1 substitution
      ⟨fun s t => substitution.map_mul s t,fun _ => rfl⟩
  have same : expand D = t := inj eq
  simp [rhoPredecessor,hD,same]

private theorem collapse_act (X : Letter) (t : Source) (hn : Native t) :
    collapse (act X t) = some (match X with | .F => H t | .G => t) := by
  cases X with
  | F => exact (congrArg collapse (f_eq_g_H t hn)).trans (collapse_g _ (H_native t hn))
  | G => exact collapse_g t hn

private theorem run_output (t : Source) (hn : Native t) (W : List Letter) (hw : W ≠ []) :
    (collapse (run t W)).isSome := by
  induction W using List.reverseRecOn with
  | nil => exact (hw rfl).elim
  | append_singleton W X ih =>
    rw [run_append]
    change (collapse (act X (run t W))).isSome = true
    rw [collapse_act X _ (run_native t hn W)]
    rfl

private theorem multileaf (t : Source) (hn : Native t) (hi : 1 < eventIndex t) : 2 ≤ t.length := by
  cases t with
  | of b => cases b <;> simp_all [Native,native,eventIndex,composition]
  | mul l r =>
    have := l.length_pos
    have := r.length_pos
    simp only [FreeMagma.length]
    omega

private theorem previous_last (n0 : Nat) (h0 : 1 < n0) (t : Source)
    (hn : Native t) (ht : eventIndex t = n0) (W : List Letter) (X : Letter) :
    previous n0 (act X (run t W)) = some (run t W,X) := by
  let s := run t W
  have ns : Native s := run_native t hn W
  have bs : n0 ≤ eventIndex s := by have := run_bound t hn W; dsimp [s]; omega
  cases X with
  | G =>
    have selected : eventIndex s = n0 ∨ (collapse s).isSome := by
      by_cases hw : W = []
      · subst W
        exact Or.inl ht
      · exact Or.inr (run_output t hn W hw)
    change previous n0 (splitLeft s) = some (s,.G)
    simp [previous,collapse_g s ns,selected]
  | F =>
    have eq := collapse_act .F s ns
    have hc := H_index s ns
    have len := multileaf s ns (by omega)
    have not_boundary : eventIndex (H s) ≠ n0 := by omega
    have not_selected : ¬ (eventIndex (H s) = n0 ∨ (collapse (H s)).isSome) := by
      simp [not_boundary,collapse_H]
    change previous n0 (act .F s) = some (s,.F)
    change collapse (substitution s) = some (H s) at eq
    simp [previous,act,eq,not_selected,rho_predecessor_complete s,ns]

private theorem previous_sound (n0 : Nat) (z p : Source) (X : Letter)
    (hz : Native z) (hp : previous n0 z = some (p,X)) :
    Native p ∧ act X p = z ∧ eventIndex p < eventIndex z := by
  obtain ⟨c,hc,hp⟩ := Option.bind_eq_some_iff.mp hp
  split_ifs at hp with select
  · cases hp
    obtain ⟨eq,hn⟩ := collapse_sound z p hc
    have np := hn hz
    refine ⟨np,eq,?_⟩
    have hi := act_index .G p np
    change eventIndex (splitLeft p) = eventIndex p + 1 at hi
    rw [eq] at hi
    omega
  · obtain ⟨q,hq,hp⟩ := Option.bind_eq_some_iff.mp hp
    split_ifs at hp with nq
    cases hp
    have eq := rho_predecessor_sound z p hq
    refine ⟨nq,eq,?_⟩
    rw [← eq]
    change eventIndex p < eventIndex (act .F p)
    rw [act_index .F p nq]
    exact Nat.lt_add_of_pos_right p.length_pos

private theorem recover_fuel_complete (n0 : Nat) (h0 : 1 < n0) (t : Source)
    (hn : Native t) (ht : eventIndex t = n0) (W : List Letter) :
    ∀ fuel : Nat, eventIndex (run t W) - n0 ≤ fuel →
      (recoverFuel fuel n0 (run t W)).2 = some (t,W) := by
  induction W using List.reverseRecOn with
  | nil =>
    intro fuel hf
    simp only [run,List.foldl_nil]
    rw [recoverFuel.eq_def]
    simp [hn,ht,show ¬ n0 ≤ 1 by omega]
  | append_singleton W X ih =>
    intro fuel hf
    have ns := run_native t hn W
    have nr := act_native X (run t W) ns
    have lower := run_bound t hn W
    have increment := act_index X (run t W) ns
    have pos := (run t W).length_pos
    have strict : eventIndex (run t W) < eventIndex (act X (run t W)) := by
      cases X <;> simp_all <;> omega
    have base : n0 ≤ eventIndex (run t W) := by omega
    have above : n0 < eventIndex (act X (run t W)) := by omega
    rw [run_append] at hf ⊢
    change eventIndex (act X (run t W)) - n0 ≤ fuel at hf
    change (recoverFuel fuel n0 (act X (run t W))).2 = some (t,W ++ [X])
    cases fuel with
    | zero => omega
    | succ k =>
      rw [recoverFuel.eq_def]
      rw [if_neg (by simp only [not_or]; exact ⟨by omega,not_not.mpr nr,by omega⟩),
        if_neg (by omega),previous_last n0 h0 t hn ht W X]
      simp only []
      rw [if_pos ⟨base,strict⟩]
      change ((recoverFuel k n0 (run t W)).2.map
        (fun a => (a.1,a.2 ++ [X]))) = some (t,W ++ [X])
      rw [ih k (by omega)]
      rfl

private theorem recover_fuel_sound (fuel n0 : Nat) (z t : Source) (W : List Letter)
    (h : (recoverFuel fuel n0 z).2 = some (t,W)) :
    1 < n0 ∧ Native t ∧ eventIndex t = n0 ∧ run t W = z ∧
      W.length ≤ eventIndex z - n0 ∧ (recoverFuel fuel n0 z).1 = W.length := by
  induction fuel generalizing z t W with
  | zero =>
    rw [recoverFuel.eq_def] at h
    split_ifs at h with bad base
    cases h
    refine ⟨by omega,by tauto,base,rfl,by simp,?_⟩
    rw [recoverFuel.eq_def,if_neg bad,if_pos base]
    rfl
  | succ k ih =>
    rw [recoverFuel.eq_def] at h
    split_ifs at h with bad base
    · cases h
      refine ⟨by omega,by tauto,base,rfl,by simp,?_⟩
      rw [recoverFuel.eq_def,if_neg bad,if_pos base]
      rfl
    · cases hp : previous n0 z with
      | none => simp only [hp] at h; cases h
      | some pair =>
        rcases pair with ⟨p,X⟩
        simp only [hp] at h
        split_ifs at h with bound
        obtain ⟨⟨s,V⟩,hv,h⟩ := Option.map_eq_some_iff.mp h
        cases h
        obtain ⟨h0,nt,et,eq,len,count⟩ := ih p s V hv
        have nz : Native z := by tauto
        obtain ⟨np,step,dec⟩ := previous_sound n0 z p X nz hp
        refine ⟨h0,nt,et,?_,?_,?_⟩
        · rw [run_append,eq]
          exact step
        · simp only [List.length_append,List.length_singleton]
          omega
        · rw [recoverFuel.eq_def,if_neg bad,if_neg base,hp]
          simp only []
          rw [if_pos bound]
          change (recoverFuel k n0 p).1+1 = (V ++ [X]).length
          rw [count]
          simp

private theorem recover_fuel_bound (fuel n0 : Nat) (z : Source) :
    (recoverFuel fuel n0 z).1 ≤ fuel := by
  induction fuel generalizing n0 z with
  | zero =>
    rw [recoverFuel.eq_def]
    split_ifs <;> exact Nat.le_refl 0
  | succ k ih =>
    rw [recoverFuel.eq_def]
    split_ifs with bad base
    · exact Nat.zero_le _
    · exact Nat.zero_le _
    · cases hp : previous n0 z with
      | none => exact Nat.zero_le _
      | some pair =>
        rcases pair with ⟨p,X⟩
        simp only []
        split_ifs with bound
        · exact Nat.succ_le_succ (ih n0 p)
        · exact Nat.zero_le _

private theorem recover_iff (n0 : Nat) (z t : Source) (W : List Letter) :
    recover n0 z = some (t,W) ↔
      1 < n0 ∧ Native t ∧ eventIndex t = n0 ∧ run t W = z := by
  constructor
  · intro h
    exact ⟨(recover_fuel_sound _ _ _ _ _ h).1,
      (recover_fuel_sound _ _ _ _ _ h).2.1,
      (recover_fuel_sound _ _ _ _ _ h).2.2.1,
      (recover_fuel_sound _ _ _ _ _ h).2.2.2.1⟩
  · rintro ⟨h0,hn,ht,rfl⟩
    exact recover_fuel_complete n0 h0 t hn ht W _ (Nat.le_refl _)

private theorem run_injective (n0 : Nat) (h0 : 1 < n0) (s t : Source)
    (hs : Native s) (ht : Native t) (es : eventIndex s = n0) (et : eventIndex t = n0)
    (V W : List Letter) (eq : run s V = run t W) : s = t ∧ V = W := by
  have left := (recover_iff n0 (run s V) s V).mpr ⟨h0,hs,es,rfl⟩
  have right := (recover_iff n0 (run t W) t W).mpr ⟨h0,ht,et,rfl⟩
  rw [eq] at left
  exact Prod.mk.inj (Option.some.inj (left.symm.trans right))

def K : Source := .mul (.of false) (.of true)

private theorem run_first (X : Letter) (U : List Letter) :
    run (.of false) (X :: U) = run K U := by cases X <;> rfl

private theorem beta_empty (W : List Letter) : run (.of false) W = .of false ↔ W = [] := by
  constructor
  · intro eq
    have bound := run_bound (.of false) rfl W
    rw [eq] at bound
    have len : W.length = 0 := by change 1 + W.length ≤ 1 at bound; omega
    exact List.length_eq_zero_iff.mp len
  · rintro rfl
    rfl

private theorem beta_fibre (z : Source)
    (reached : ∃ W : List Letter, W ≠ [] ∧ run (.of false) W = z) :
    ∃! U : List Letter, ∀ W : List Letter,
      run (.of false) W = z ↔ W = .F :: U ∨ W = .G :: U := by
  obtain ⟨W,nonempty,endpoint⟩ := reached
  have not_beta : z ≠ .of false := by
    intro eq
    exact nonempty ((beta_empty W).mp (endpoint.trans eq))
  cases W with
  | nil => exact (nonempty rfl).elim
  | cons X U =>
    rw [run_first] at endpoint
    have fibre : ∀ V : List Letter,
        run (.of false) V = z ↔ V = .F :: U ∨ V = .G :: U := by
      intro V
      constructor
      · intro hv
        cases V with
        | nil => exact (not_beta hv.symm).elim
        | cons Y V =>
          rw [run_first] at hv
          have same := (run_injective 2 (by decide) K K rfl rfl rfl rfl V U
            (hv.trans endpoint.symm)).2
          subst V
          cases Y <;> simp
      · rintro (rfl | rfl) <;> exact (run_first _ U).trans endpoint
    refine ⟨U,fibre,?_⟩
    intro V hv
    have eq := (fibre (.F :: V)).mp ((hv (.F :: V)).mpr (Or.inl rfl))
    rcases eq with eq | eq
    · exact (List.cons.inj eq).2
    · cases eq

private theorem beta_fibre_decoded (z : Source)
    (reached : ∃ W : List Letter, W ≠ [] ∧ run (.of false) W = z) :
    ∃! U : List Letter, recover 2 z = some (K,U) ∧
      ∀ W : List Letter, run (.of false) W = z ↔ W = .F :: U ∨ W = .G :: U := by
  obtain ⟨U,fibre,unique⟩ := beta_fibre z reached
  refine ⟨U,⟨?_,fibre⟩,?_⟩
  · have eq : run K U = z := (run_first .F U).symm.trans
      ((fibre (.F :: U)).mpr (Or.inl rfl))
    exact (recover_iff 2 z K U).mpr ⟨by decide,rfl,rfl,eq⟩
  · intro V hv
    exact unique V hv.2

private theorem supplement_separation {A : Type} (E : List Letter → A)
    (U : List Letter) :
    (∃ D : A → List Letter, ∀ W : List Letter,
      run (.of false) W = run K U → D (E W) = W) ↔
      E (.F :: U) ≠ E (.G :: U) := by
  classical
  have reached : ∃ W : List Letter, W ≠ [] ∧ run (.of false) W = run K U :=
    ⟨.F :: U,by simp,run_first .F U⟩
  obtain ⟨V,fibre,_⟩ := beta_fibre (run K U) reached
  have same : V = U := by
    rcases (fibre (.F :: U)).mp (run_first .F U) with h | h
    · exact (List.cons.inj h).2.symm
    · cases h
  subst V
  constructor
  · rintro ⟨D,hD⟩ equal
    have hf := hD (.F :: U) (run_first .F U)
    have hg := hD (.G :: U) (run_first .G U)
    rw [equal,hg] at hf
    cases hf
  · intro different
    refine ⟨fun a => if a = E (.F :: U) then .F :: U else .G :: U,?_⟩
    intro W hw
    rcases (fibre W).mp hw with rfl | rfl
    · simp
    · simp [Ne.symm different]

/-- Literal original guarded calls; tags carry their actual P/S meaning. -/
def toCall (e : NativeLocalSourceExecution.Event) : Geometry.NativeGuardedLeafRepair.Call :=
  if e.2 then .promote e.1 else .split e.1

def fromCall : Geometry.NativeGuardedLeafRepair.Call → NativeLocalSourceExecution.Event
  | .promote p => (p,true)
  | .split p => (p,false)

private theorem to_from (c : Geometry.NativeGuardedLeafRepair.Call) : toCall (fromCall c) = c := by
  cases c <;> rfl

private theorem edit_canonical (t : Source) (p : NativeLocalSourceExecution.Address) (k : Bool) :
    NativeLocalSourceExecution.edit t p k =
      if ActualLeafHistoryRigidity.subtree p t = some (.of k) then
        some (ActualImageAddressCertificate.replace t p (substitution (.of k))) else none := by
  induction p generalizing t with
  | nil =>
    cases t with
    | of b => cases b <;> cases k <;> rfl
    | mul l r => cases k <;> rfl
  | cons d p ih =>
    cases t with
    | of b => cases b <;> cases d <;> cases k <;> rfl
    | mul l r =>
      cases d <;>
        simp only [NativeLocalSourceExecution.edit,ActualLeafHistoryRigidity.subtree,
          ActualImageAddressCertificate.replace,ih] <;> split_ifs <;> simp_all

private theorem guarded_cons (t : Source) (p : NativeLocalSourceExecution.Address)
    (k : Bool) (cs : List Geometry.NativeGuardedLeafRepair.Call) :
    Geometry.NativeGuardedLeafRepair.run t (toCall (p,k) :: cs) =
      (NativeLocalSourceExecution.edit t p k).bind
        (fun u => Geometry.NativeGuardedLeafRepair.run u cs) := by
  have distinct : (FreeMagma.of true : Source) ≠ .of false := by
    intro h
    cases h
  rw [edit_canonical]
  cases k <;> cases hs : ActualLeafHistoryRigidity.subtree p t with
  | none => simp [Geometry.NativeGuardedLeafRepair.run,toCall,hs]
  | some v =>
    cases v with
    | of b => cases b <;> simp [Geometry.NativeGuardedLeafRepair.run,toCall,hs,
        substitution,FreeMagma.lift_of,distinct,Ne.symm distinct]
    | mul l r => simp [Geometry.NativeGuardedLeafRepair.run,toCall,hs]

private theorem replay_guarded (t : Source) (es : List NativeLocalSourceExecution.Event) :
    NativeLocalSourceExecution.replay t es =
      Geometry.NativeGuardedLeafRepair.run t (es.map toCall) := by
  induction es generalizing t with
  | nil => rfl
  | cons e es ih =>
    rcases e with ⟨p,k⟩
    simp only [List.map_cons,guarded_cons,NativeLocalSourceExecution.replay,ih]

private theorem guarded_replay (t : Source) (cs : List Geometry.NativeGuardedLeafRepair.Call) :
    Geometry.NativeGuardedLeafRepair.run t cs =
      NativeLocalSourceExecution.replay t (cs.map fromCall) := by
  have identity : (fun c => toCall (fromCall c)) = id := funext to_from
  simpa only [List.map_map,Function.comp_def,identity,List.map_id] using
    (replay_guarded t (cs.map fromCall)).symm

private theorem guarded_attained (t : Source) : Native t ↔
    (∃ cs : List Geometry.NativeGuardedLeafRepair.Call,
      Geometry.NativeGuardedLeafRepair.run (.of true) cs = some t) ∧ t ≠ .of true := by
  rw [NativeLocalSourceExecution.native_execution.2.2.2.2.2 t]
  constructor
  · rintro ⟨⟨es,h⟩,ne⟩
    exact ⟨⟨es.map toCall,(replay_guarded (.of true) es).symm.trans h⟩,ne⟩
  · rintro ⟨⟨cs,h⟩,ne⟩
    exact ⟨⟨cs.map fromCall,(guarded_replay (.of true) cs).symm.trans h⟩,ne⟩

private theorem guarded_append (t : Source) (cs ds : List Geometry.NativeGuardedLeafRepair.Call) :
    Geometry.NativeGuardedLeafRepair.run t (cs ++ ds) =
      (Geometry.NativeGuardedLeafRepair.run t cs).bind
        (fun u => Geometry.NativeGuardedLeafRepair.run u ds) := by
  have step (t : Source) (c : Geometry.NativeGuardedLeafRepair.Call)
      (cs : List Geometry.NativeGuardedLeafRepair.Call) :
      Geometry.NativeGuardedLeafRepair.run t (c :: cs) =
        (NativeLocalSourceExecution.edit t (fromCall c).1 (fromCall c).2).bind
          (fun u => Geometry.NativeGuardedLeafRepair.run u cs) := by
    cases c with
    | promote p => exact guarded_cons t p true cs
    | split p => exact guarded_cons t p false cs
  induction cs generalizing t with
  | nil => rfl
  | cons c cs ih => simp only [List.cons_append,step,ih,Option.bind_assoc]

/-- Each macro seals its own old frontier or acquires its current leftmost beta. -/
def macroCalls (X : Letter) (t : Source) : List Geometry.NativeGuardedLeafRepair.Call :=
  match X with
  | .F => (NativeLocalSourceExecution.oldFrontier t).map toCall
  | .G => [.split (NativeLocalSourceExecution.leftmost t)]

/-- The complete chronological native primitive expansion; no macro delimiters
are added to the source records. -/
def primitiveWord : Source → List Letter → List Geometry.NativeGuardedLeafRepair.Call
  | _, [] => []
  | t, X :: W => macroCalls X t ++ primitiveWord (act X t) W

private theorem macro_calls (X : Letter) (t : Source) (hn : Native t) :
    Geometry.NativeGuardedLeafRepair.run t (macroCalls X t) = some (act X t) := by
  cases X with
  | F => exact (replay_guarded t _).symm.trans (NativeLocalSourceExecution.native_execution.1 t).1
  | G =>
    change Geometry.NativeGuardedLeafRepair.run t
      (toCall (NativeLocalSourceExecution.leftmost t,false) :: []) = _
    rw [guarded_cons,(NativeLocalSourceExecution.native_execution.2.1 t hn).1]
    rfl

private theorem primitive_word (t : Source) (W : List Letter) (hn : Native t) :
    Geometry.NativeGuardedLeafRepair.run t (primitiveWord t W) = some (run t W) := by
  induction W generalizing t with
  | nil => rfl
  | cons X W ih =>
    rw [primitiveWord,guarded_append,macro_calls X t hn]
    exact ih (act X t) (act_native X t hn)

private theorem primitive_length (t : Source) (W : List Letter) (hn : Native t) :
    (primitiveWord t W).length = eventIndex (run t W) - eventIndex t := by
  have h := NativeLocalSourceExecution.native_execution.2.2.1 t (run t W)
    ((primitiveWord t W).map fromCall)
    ((guarded_replay t (primitiveWord t W)).symm.trans (primitive_word t W hn))
  simp only [List.length_map] at h
  omega

private theorem native_run (t : Source) (W : List Letter) (hn : Native t)
    (labels : Geometry.NativeGuardedLeafRepair.RawMap) (next : ℤ)
    (x : Geometry.NativeGuardedLeafRepair.Value) :
    ∃ (labels' : Geometry.NativeGuardedLeafRepair.RawMap) (next' : ℤ)
      (y : Geometry.NativeGuardedLeafRepair.Value),
      Geometry.NativeGuardedLeafRepair.nativeRun t labels next x (primitiveWord t W) =
        some (run t W,labels',next',y) ∧
      (∀ p : NativeLocalSourceExecution.Address,
        p ∈ Geometry.NativeMaterialRootRecognition.material t → y p = x p) ∧
      (∀ p : NativeLocalSourceExecution.Address,
        p ∈ Geometry.NativeMaterialRootRecognition.material (run t W) →
        p ∉ Geometry.NativeMaterialRootRecognition.material t → y p = 0) := by
  let h : Geometry.NativeGuardedLeafRepair.History t := {
    final := run t W
    calls := primitiveWord t W
    trace := primitive_word t W hn
    domain := by
      obtain ⟨cs,trace⟩ := ((guarded_attained (run t W)).mp (run_native t hn W)).1
      exact Geometry.NativeGuardedLeafRepair.run_preserves_D
        Geometry.NativeGuardedLeafRepair.alphaRHistory.domain trace }
  exact Geometry.NativeGuardedLeafRepair.history_preserves_values h labels next x

/-- A concrete supplementary bit records the first completed macro. -/
def firstChoice : List Letter → Bool
  | .F :: _ => true
  | _ => false

private theorem first_choice_sufficient (U : List Letter) :
    ∃ D : Bool → List Letter, ∀ W : List Letter,
      run (.of false) W = run K U → D (firstChoice W) = W := by
  exact (supplement_separation firstChoice U).mpr (by simp [firstChoice])

private theorem attained_native (t : Source) (positive : 0 < eventIndex t)
    (attained : ∃ cs : List Geometry.NativeGuardedLeafRepair.Call,
      Geometry.NativeGuardedLeafRepair.run (.of true) cs = some t) : Native t := by
  apply (guarded_attained t).mpr
  refine ⟨attained,?_⟩
  intro eq
  subst t
  change 0 < 0 at positive
  omega

private theorem recover_canonical (n0 : Nat) (z t : Source) (W : List Letter) :
    recover n0 z = some (t,W) ↔
      1 < n0 ∧
      (∃ cs : List Geometry.NativeGuardedLeafRepair.Call,
        Geometry.NativeGuardedLeafRepair.run (.of true) cs = some t) ∧
      eventIndex t = n0 ∧ run t W = z := by
  constructor
  · intro h
    obtain ⟨h0,hn,ht,eq⟩ := (recover_iff n0 z t W).mp h
    exact ⟨h0,((guarded_attained t).mp hn).1,ht,eq⟩
  · rintro ⟨h0,ha,ht,eq⟩
    exact (recover_iff n0 z t W).mpr
      ⟨h0,attained_native t (by omega) ha,ht,eq⟩

private theorem run_injective_canonical (n0 : Nat) (h0 : 1 < n0) (s t : Source)
    (hs : ∃ cs : List Geometry.NativeGuardedLeafRepair.Call,
      Geometry.NativeGuardedLeafRepair.run (.of true) cs = some s)
    (ht : ∃ cs : List Geometry.NativeGuardedLeafRepair.Call,
      Geometry.NativeGuardedLeafRepair.run (.of true) cs = some t)
    (es : eventIndex s = n0) (et : eventIndex t = n0)
    (V W : List Letter) (eq : run s V = run t W) : s = t ∧ V = W := by
  exact run_injective n0 h0 s t (attained_native s (by omega) hs)
    (attained_native t (by omega) ht) es et V W eq

/-- The complete finite recovery statement on the native ordered syntax.
No old tree, entry composition, entry depth or word length is supplied. -/
theorem completed_history_recovery :
    (∀ (n0 : Nat) (z t : Source) (W : List Letter),
      recover n0 z = some (t,W) ↔
        1 < n0 ∧
        (∃ cs : List Geometry.NativeGuardedLeafRepair.Call,
          Geometry.NativeGuardedLeafRepair.run (.of true) cs = some t) ∧
        eventIndex t = n0 ∧ run t W = z) ∧
    (∀ (n0 : Nat) (z : Source),
      recover n0 z = none ↔
        ¬ ∃ (t : Source) (W : List Letter),
          1 < n0 ∧
        (∃ cs : List Geometry.NativeGuardedLeafRepair.Call,
          Geometry.NativeGuardedLeafRepair.run (.of true) cs = some t) ∧
        eventIndex t = n0 ∧ run t W = z) ∧
    (∀ (n0 : Nat) (z t : Source) (W : List Letter),
      recover n0 z = some (t,W) →
        W.length ≤ eventIndex z - n0 ∧ recoverySteps n0 z = W.length) ∧
    (∀ (n0 : Nat) (z p : Source) (X : Letter), Native z →
      previous n0 z = some (p,X) →
        Native p ∧ act X p = z ∧ eventIndex p < eventIndex z) ∧
    (∀ (n0 : Nat), 1 < n0 → ∀ (s t : Source),
      (∃ cs : List Geometry.NativeGuardedLeafRepair.Call,
        Geometry.NativeGuardedLeafRepair.run (.of true) cs = some s) →
      (∃ cs : List Geometry.NativeGuardedLeafRepair.Call,
        Geometry.NativeGuardedLeafRepair.run (.of true) cs = some t) →
      eventIndex s = n0 → eventIndex t = n0 → ∀ (V W : List Letter),
        run s V = run t W → s = t ∧ V = W) ∧
    (∀ W : List Letter, run (.of false) W = .of false ↔ W = []) ∧
    (∀ z : Source, (∃ W : List Letter, W ≠ [] ∧ run (.of false) W = z) →
      ∃! U : List Letter, recover 2 z = some (K,U) ∧
        ∀ W : List Letter, run (.of false) W = z ↔ W = .F :: U ∨ W = .G :: U) ∧
    (∀ (A : Type) (E : List Letter → A) (U : List Letter),
      (∃ D : A → List Letter, ∀ W : List Letter,
        run (.of false) W = run K U → D (E W) = W) ↔
          E (.F :: U) ≠ E (.G :: U)) ∧
    (∀ (t : Source) (es : List NativeLocalSourceExecution.Event),
      NativeLocalSourceExecution.replay t es =
        Geometry.NativeGuardedLeafRepair.run t (es.map toCall)) ∧
    (∀ t : Source, Native t ↔
      (∃ cs : List Geometry.NativeGuardedLeafRepair.Call,
        Geometry.NativeGuardedLeafRepair.run (.of true) cs = some t) ∧ t ≠ .of true) ∧
    (∀ (t : Source) (W : List Letter), Native t →
      Geometry.NativeGuardedLeafRepair.run t (primitiveWord t W) = some (run t W) ∧
      (primitiveWord t W).length = eventIndex (run t W) - eventIndex t) ∧
    (∀ (t : Source) (W : List Letter), Native t →
      ∀ (labels : Geometry.NativeGuardedLeafRepair.RawMap) (next : ℤ)
        (x : Geometry.NativeGuardedLeafRepair.Value),
      ∃ (labels' : Geometry.NativeGuardedLeafRepair.RawMap) (next' : ℤ)
        (y : Geometry.NativeGuardedLeafRepair.Value),
        Geometry.NativeGuardedLeafRepair.nativeRun t labels next x (primitiveWord t W) =
          some (run t W,labels',next',y) ∧
        (∀ p : NativeLocalSourceExecution.Address,
        p ∈ Geometry.NativeMaterialRootRecognition.material t → y p = x p) ∧
        (∀ p : NativeLocalSourceExecution.Address,
          p ∈ Geometry.NativeMaterialRootRecognition.material (run t W) →
          p ∉ Geometry.NativeMaterialRootRecognition.material t → y p = 0)) ∧
    (∀ U : List Letter,
      ∃ D : Bool → List Letter, ∀ W : List Letter,
        run (.of false) W = run K U → D (firstChoice W) = W) ∧
    (∀ (n0 : Nat) (z : Source), recoverySteps n0 z ≤ eventIndex z - n0) := by
  refine ⟨recover_canonical,?_,?_,previous_sound,run_injective_canonical,beta_empty,beta_fibre_decoded,
    fun _ E U => supplement_separation E U,replay_guarded,guarded_attained,
    fun t W hn => ⟨primitive_word t W hn,primitive_length t W hn⟩,
    native_run,first_choice_sufficient,fun n0 z => recover_fuel_bound _ n0 z⟩
  · intro n0 z
    constructor
    · intro h ⟨t,W,good⟩
      have := (recover_canonical n0 z t W).mpr good
      rw [h] at this
      cases this
    · intro absent
      cases h : recover n0 z with
      | none => rfl
      | some p =>
        exact (absent ⟨p.1,p.2,(recover_canonical n0 z p.1 p.2).mp h⟩).elim
  · intro n0 z t W h
    exact (recover_fuel_sound _ _ _ _ _ h).2.2.2.2

#print axioms completed_history_recovery

end D5.S3.Arith.FibonacciAtomic.NativeCompletedHistoryRecovery
