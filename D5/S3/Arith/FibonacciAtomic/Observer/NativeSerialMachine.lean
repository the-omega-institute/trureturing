/- GID: D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialMachine
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Native source-blind serial steps, actual register evolution and chronological replay. -/

import D5.S3.Arith.FibonacciAtomic.Observer.NativeDepthPatterns
import Mathlib.Data.Set.Finite.List
import Mathlib.Computability.StateTransition

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialMachine

open GenealogicalFiberTransport (Source substitution)
open ActualTreeReadoutAcquisition (Address Reply readout)

/-- Control and output types are unrestricted. The interpreter receives only
control, never the register, its epoch, or a clock. -/
inductive Op (C O : Type) where
  | localStep : C → Op C O
  | read : Address → (Reply → C) → Op C O
  | applyRho : C → Op C O
  | stop : O → Op C O

/-- Local steps and true updates remain real chronological actions. -/
inductive Event where
  | localStep : Event
  | update : Nat → Event
  | read : Nat → Address → Reply → Event
  deriving DecidableEq

abbrev Trace := List Event
abbrev Descriptor := Nat × Address

def reads : Trace → List (Nat × Address × Reply)
  | [] => []
  | .read e a y :: t => (e,a,y) :: reads t
  | _ :: t => reads t

def answers (t : Trace) : List Reply := (reads t).map (fun x => x.2.2)

def Config (C : Type) := C × Nat × Source × Trace

/-- Exactly one physical register is carried forward. History is appended,
never inspected by the transition function. -/
def nativeStep {C O : Type} (δ : C → Op C O) (x : Config C) : Option (Config C) :=
  match δ x.1 with
  | .localStep c => some (c,x.2.1,x.2.2.1,x.2.2.2 ++ [.localStep])
  | .applyRho c => some (c,x.2.1+1,substitution x.2.2.1,x.2.2.2 ++ [.update x.2.1])
  | .read a k => let y := readout a x.2.2.1
                some (k y,x.2.1,x.2.2.1,x.2.2.2 ++ [.read x.2.1 a y])
  | .stop _ => none

/-- Finite actual termination retaining every local/update/read step. -/
inductive Run {C O : Type} (δ : C → Op C O) : C → Nat → Source → Trace → O → Prop
  | stop {c e r o} : δ c = .stop o → Run δ c e r [] o
  | localStep {c c' e r t o} : δ c = .localStep c' →
      Run δ c' e r t o → Run δ c e r (.localStep :: t) o
  | update {c c' e r t o} : δ c = .applyRho c' →
      Run δ c' (e+1) (substitution r) t o → Run δ c e r (.update e :: t) o
  | read {c e r a k y t o} : δ c = .read a k → readout a r = y →
      Run δ (k y) e r t o → Run δ c e r (.read e a y :: t) o

abbrev Boundary (C O : Type) := C × Nat × Sum Address O

/-- Partial source-free replay. A finite derivation exists only when the supplied
word reaches its next Read or Stop; no total boundary oracle is assumed. -/
inductive Replay {C O : Type} (δ : C → Op C O) :
    C → Nat → List Reply → Trace → Boundary C O → Prop
  | stop {c e o} : δ c = .stop o → Replay δ c e [] [] (c,e,.inr o)
  | await {c e a k} : δ c = .read a k → Replay δ c e [] [] (c,e,.inl a)
  | localStep {c c' e w t b} : δ c = .localStep c' →
      Replay δ c' e w t b → Replay δ c e w (.localStep :: t) b
  | update {c c' e w t b} : δ c = .applyRho c' →
      Replay δ c' (e+1) w t b → Replay δ c e w (.update e :: t) b
  | read {c e a k y w t b} : δ c = .read a k →
      Replay δ (k y) e w t b → Replay δ c e (y :: w) (.read e a y :: t) b

/-- Finite replay has a unique full trace and boundary, independently of any
source used to witness reachability. -/
theorem replay_deterministic {C O : Type} {δ : C → Op C O}
    {c : C} {e : Nat} {w : List Reply} {t s : Trace} {b d : Boundary C O}
    (p : Replay δ c e w t b) (q : Replay δ c e w s d) : t = s ∧ b = d := by
  induction p generalizing s d with
  | stop h =>
      cases q with
      | stop hq =>
          have he := Op.stop.inj (h.symm.trans hq)
          cases he
          exact ⟨rfl,rfl⟩
      | await hq =>
          cases h.symm.trans hq
      | localStep hq q =>
          cases h.symm.trans hq
      | update hq q =>
          cases h.symm.trans hq
  | await h =>
      cases q with
      | stop hq =>
          cases h.symm.trans hq
      | await hq =>
          obtain ⟨he,hk⟩ := Op.read.inj (h.symm.trans hq)
          cases he
          exact ⟨rfl,rfl⟩
      | localStep hq q =>
          cases h.symm.trans hq
      | update hq q =>
          cases h.symm.trans hq
  | localStep h p ih =>
      cases q with
      | stop hq =>
          cases h.symm.trans hq
      | await hq =>
          cases h.symm.trans hq
      | localStep hq q =>
          have he := Op.localStep.inj (h.symm.trans hq)
          cases he
          obtain ⟨he,hb⟩ := ih q
          exact ⟨congrArg (List.cons _) he,hb⟩
      | update hq q =>
          cases h.symm.trans hq
      | read hq q =>
          cases h.symm.trans hq
  | update h p ih =>
      cases q with
      | stop hq =>
          cases h.symm.trans hq
      | await hq =>
          cases h.symm.trans hq
      | localStep hq q =>
          cases h.symm.trans hq
      | update hq q =>
          have he := Op.applyRho.inj (h.symm.trans hq)
          cases he
          obtain ⟨he,hb⟩ := ih q
          exact ⟨congrArg (List.cons _) he,hb⟩
      | read hq q =>
          cases h.symm.trans hq
  | read h p ih =>
      cases q with
      | localStep hq q =>
          cases h.symm.trans hq
      | update hq q =>
          cases h.symm.trans hq
      | read hq q =>
          obtain ⟨he,hk⟩ := Op.read.inj (h.symm.trans hq)
          cases he
          cases hk
          obtain ⟨he,hb⟩ := ih q
          exact ⟨congrArg (List.cons _) he,hb⟩

/-- Every actual read has a uniquely determined replay boundary indexed by the
preceding reply word. Terminal replay retains all silent steps. -/
theorem operational_replay {C O : Type} {δ : C → Op C O}
    {c : C} {e : Nat} {r : Source} {t : Trace} {o : O}
    (run : Run δ c e r t o) :
    (∃ c' e', Replay δ c e (answers t) t (c',e',.inr o)) ∧
    (∀ n a y, Event.read n a y ∈ t →
      ∃ w s c', w.length < (answers t).length ∧ Replay δ c e w s (c',n,.inl a)) ∧
    (∀ w s z b d, Replay δ c e w s b → Replay δ c e w z d → s = z ∧ b = d) := by
  refine ⟨?_, ?_, fun _ _ _ _ _ => replay_deterministic⟩
  · induction run with
    | stop h => exact ⟨_,_,Replay.stop h⟩
    | localStep h run ih =>
        obtain ⟨c',e',p⟩ := ih
        exact ⟨c',e',Replay.localStep h p⟩
    | update h run ih =>
        obtain ⟨c',e',p⟩ := ih
        exact ⟨c',e',Replay.update h p⟩
    | read h hy run ih =>
        obtain ⟨c',e',p⟩ := ih
        exact ⟨c',e',Replay.read h p⟩
  · induction run with
    | stop h => simp
    | localStep h run ih =>
        intro n a y hm
        have hm' : Event.read n a y ∈ _ := (List.mem_cons.mp hm).resolve_left (by simp)
        obtain ⟨w,s,c',hw,p⟩ := ih n a y hm'
        exact ⟨w,.localStep::s,c',hw,Replay.localStep h p⟩
    | update h run ih =>
        intro n a y hm
        have hm' : Event.read n a y ∈ _ := (List.mem_cons.mp hm).resolve_left (by simp)
        obtain ⟨w,s,c',hw,p⟩ := ih n a y hm'
        exact ⟨w,.update _::s,c',hw,Replay.update h p⟩
    | @read c e r a k y t o h hy run ih =>
        intro n b z hm
        rcases List.mem_cons.mp hm with he | hm
        · cases he
          exact ⟨[],[],c,by simp [answers,reads],Replay.await h⟩
        · obtain ⟨w,s,c',hw,p⟩ := ih n b z hm
          exact ⟨y::w,.read e a y::s,c',by simpa [answers,reads] using hw,Replay.read h p⟩

/-- Every reached reply prefix has a finite source-free replay to its next
Read or Stop. An actual terminating run supplies existence, and replay
uniqueness makes the trace and boundary independent of that source witness. -/
theorem reached_prefix_replay {C O : Type} {δ : C → Op C O}
    {c : C} {e : Nat} {r : Source} {t : Trace} {o : O}
    (run : Run δ c e r t o) (w : List Reply) (pre : w <+: answers t) :
    ∃ s b, Replay δ c e w s b ∧ s <+: t ∧ answers s = w ∧
      (w = answers t ↔ b.2.2 = .inr o) := by
  induction run generalizing w with
  | stop h =>
      have he : w = [] := by simpa [answers,reads] using pre
      subst w
      exact ⟨[],_,Replay.stop h,by simp,by rfl,by simp [answers,reads]⟩
  | localStep h run ih =>
      obtain ⟨s,b,p,hs,hw,hb⟩ := ih w pre
      exact ⟨.localStep::s,b,Replay.localStep h p,by simpa using hs,hw,hb⟩
  | update h run ih =>
      obtain ⟨s,b,p,hs,hw,hb⟩ := ih w pre
      exact ⟨.update _::s,b,Replay.update h p,by simpa using hs,hw,hb⟩
  | @read c e r a k y t o h hy run ih =>
      cases w with
      | nil =>
          exact ⟨[],(c,e,.inl a),Replay.await h,by simp,rfl,by simp [answers,reads]⟩
      | cons z w =>
          have hp : z = y ∧ w <+: answers t := by simpa [answers,reads] using pre
          rcases hp with ⟨hz,hp⟩
          subst z
          obtain ⟨s,b,p,hs,hw,hb⟩ := ih w hp
          refine ⟨.read e a y::s,b,Replay.read h p,by simpa using hs,?_,?_⟩
          · simpa [answers,reads] using congrArg (List.cons y) hw
          · simpa [answers,reads] using hb

/-- Actual evolution preserves the certified original source and exact log. -/
theorem actual_register_execution {C O : Type} (δ : C → Op C O)
    {c : C} {e : Nat} {r : Source} {t : Trace} {o : O}
    (run : Run δ c e r t o) (u : Source) (cert : r = substitution^[e] u)
    (old : Trace) :
    ∃ c' e', e ≤ e' ∧
      StateTransition.Reaches (nativeStep δ) (c,e,r,old)
        (c',e',substitution^[e'] u,old ++ t) ∧
      δ c' = .stop o ∧
      (∀ n a y, Event.read n a y ∈ t → readout a (substitution^[n] u) = y) := by
  induction run generalizing old with
  | @stop c e r o h =>
      subst r
      exact ⟨_,_,le_rfl,by simp only [List.append_nil]; exact Relation.ReflTransGen.refl,h,by simp⟩
  | @localStep c c' e r t o h run ih =>
      obtain ⟨d,n,hn,reach,stop,truth⟩ := ih cert (old ++ [.localStep])
      refine ⟨d,n,hn,?_,stop,?_⟩
      · have first : StateTransition.Reaches (nativeStep δ) (c,e,r,old)
            (c',e,r,old ++ [.localStep]) :=
          Relation.ReflTransGen.single (by change nativeStep δ _ = some _; simp [nativeStep,h])
        exact Relation.ReflTransGen.trans first (by simpa only [StateTransition.Reaches, List.append_assoc, List.singleton_append] using reach)
      · intro n a y hm
        exact truth n a y ((List.mem_cons.mp hm).resolve_left (by simp))
  | @update c c' e r t o h run ih =>
      have cert' : substitution r = substitution^[e+1] u := by
        rw [cert,Function.iterate_succ_apply']
      obtain ⟨d,n,hn,reach,stop,truth⟩ := ih cert' (old ++ [.update e])
      refine ⟨d,n,by omega,?_,stop,?_⟩
      · have first : StateTransition.Reaches (nativeStep δ) (c,e,r,old)
            (c',e+1,substitution r,old ++ [.update e]) :=
          Relation.ReflTransGen.single (by change nativeStep δ _ = some _; simp [nativeStep,h])
        exact Relation.ReflTransGen.trans first (by simpa only [StateTransition.Reaches, List.append_assoc, List.singleton_append] using reach)
      · intro n a y hm
        exact truth n a y ((List.mem_cons.mp hm).resolve_left (by simp))
  | @read c e r a k y t o h hy run ih =>
      obtain ⟨d,n,hn,reach,stop,truth⟩ := ih cert (old ++ [.read e a y])
      refine ⟨d,n,hn,?_,stop,?_⟩
      · have first : StateTransition.Reaches (nativeStep δ) (c,e,r,old)
            (k y,e,r,old ++ [.read e a y]) :=
          Relation.ReflTransGen.single (by change nativeStep δ _ = some _; simp [nativeStep,h,hy])
        exact Relation.ReflTransGen.trans first (by simpa only [StateTransition.Reaches, List.append_assoc, List.singleton_append] using reach)
      · intro n b z hm
        rcases List.mem_cons.mp hm with he | hm
        · cases he; simpa [← cert] using hy
        · exact truth n b z hm

end D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialMachine
