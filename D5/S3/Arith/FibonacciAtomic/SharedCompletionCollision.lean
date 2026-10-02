/- GID: D5/S3/Arith/FibonacciAtomic/SharedCompletionCollision
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/SharedCompletionCollision
   mirror-E: none(waiver:unbounded-shared-collision-proof)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: The six-state shared-completion collision law for every positive length and cut. -/

import D5.S3.Arith.FibonacciAtomic.FirstRejectionCutCapacity
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 4096

namespace D5.S3.Arith.FibonacciAtomic.SharedCompletionCollision

open D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd
open D5.S3.Arith.FibonacciAtomic.FirstRejectionCutCapacity
open scoped BigOperators

abbrev Complement (k : ℕ) (A : Finset (Fin (k + 1))) :=
  {r // r ∉ A} → Window

inductive State
  | s00 | s01 | s10 | s11 | E | D
  deriving DecidableEq

instance : Fintype State where
  elems := {.s00, .s01, .s10, .s11, .E, .D}
  complete := by intro q; cases q <;> simp

def previous : State → Option (Bool × Bool)
  | .s00 => some (false, false)
  | .s01 => some (false, true)
  | .s10 => some (true, false)
  | .s11 => some (true, true)
  | .E | .D => none

def liveState (p : Bool × Bool) : State :=
  match p with
  | (false, false) => .s00
  | (false, true) => .s01
  | (true, false) => .s10
  | (true, true) => .s11

def stopStep (terminal : Bool) (q : State) (c d : Window) : State :=
  match q with
  | .E => .E
  | .D => .D
  | .s00 | .s01 | .s10 | .s11 =>
      let p := (previous q).get!
      let α := p.1 && first c
      let β := p.2 && first d
      if α && β then .E
      else if α || β then .D
      else if terminal then
        if (c = .zero) = (d = .zero) then .E else .D
      else liveState (last c, last d)

def pairRun : State → List (Window × Window) → State
  | q, [] => q
  | q, [p] => stopStep true q p.1 p.2
  | q, p :: ps => pairRun (stopStep false q p.1 p.2) ps

def pairRunWord {k : ℕ} (u v : Word k) : State :=
  pairRun .s00 (List.ofFn (fun i => (u i, v i)))


noncomputable def fullMerge {k : ℕ} (A : Finset (Fin (k + 1)))
    (a : Side k A) (w : Word k) : Word k :=
  merge A a (fun r => w r.1)

noncomputable def fullProbability (k : ℕ) (A : Finset (Fin (k+1)))
    (a a' : Side k A) : ℚ := (∑ w : Word k,
    if task (fullMerge A a w) = task (fullMerge A a' w) then (1 : ℚ) else 0) / 5^(k+1)

noncomputable def collisionProbability (k : ℕ) (A : Finset (Fin (k+1)))
    (P Q : Profile k A) : ℚ := fullProbability k A (representative P) (representative Q)

noncomputable def SharedMatrix (k : ℕ) (A : Finset (Fin (k + 1)))
    (P Q : Profile k A) (i : Fin (k + 1)) : Matrix State State ℚ :=
  fun s t =>
    (∑ x : Window,
      if stopStep (i = Fin.last k) s
          (if h : i ∈ A then representative P ⟨i, h⟩ else x)
          (if h : i ∈ A then representative Q ⟨i, h⟩ else x) = t
      then (1 : ℚ) else 0) / 5

def matrixProduct {n : ℕ} (Q : Fin n → Matrix State State ℚ) : Matrix State State ℚ :=
  (List.ofFn Q).prod

def matrixEntry {n : ℕ} (Q : Fin n → Matrix State State ℚ) : ℚ :=
  matrixProduct Q .s00 .E

def nonterminalNumerator : Matrix State State ℚ
  | .s00, .s00 => 3
  | .s00, .s01 => 0 | .s00, .s10 => 0 | .s00, .s11 => 2 | .s00, .E => 0 | .s00, .D => 0
  | .s01, .s00 => 2
  | .s01, .s01 => 0 | .s01, .s10 => 0 | .s01, .s11 => 1 | .s01, .E => 0 | .s01, .D => 2
  | .s10, .s00 => 2
  | .s10, .s01 => 0 | .s10, .s10 => 0 | .s10, .s11 => 1 | .s10, .E => 0 | .s10, .D => 2
  | .s11, .s00 => 2
  | .s11, .s01 => 0 | .s11, .s10 => 0 | .s11, .s11 => 1 | .s11, .E => 2 | .s11, .D => 0
  | .E, .s00 => 0 | .E, .s01 => 0 | .E, .s10 => 0 | .E, .s11 => 0 | .E, .E => 5 | .E, .D => 0
  | .D, .s00 => 0 | .D, .s01 => 0 | .D, .s10 => 0 | .D, .s11 => 0 | .D, .E => 0 | .D, .D => 5

def terminalNumerator : Matrix State State ℚ
  | .s00, .s00 => 0
  | .s00, .s01 => 0 | .s00, .s10 => 0 | .s00, .s11 => 0 | .s00, .E => 5 | .s00, .D => 0
  | .s01, .s00 => 0
  | .s01, .s01 => 0 | .s01, .s10 => 0 | .s01, .s11 => 0 | .s01, .E => 3 | .s01, .D => 2
  | .s10, .s00 => 0
  | .s10, .s01 => 0 | .s10, .s10 => 0 | .s10, .s11 => 0 | .s10, .E => 3 | .s10, .D => 2
  | .s11, .s00 => 0
  | .s11, .s01 => 0 | .s11, .s10 => 0 | .s11, .s11 => 0 | .s11, .E => 5 | .s11, .D => 0
  | .E, .s00 => 0 | .E, .s01 => 0 | .E, .s10 => 0 | .E, .s11 => 0 | .E, .E => 5 | .E, .D => 0
  | .D, .s00 => 0 | .D, .s01 => 0 | .D, .s10 => 0 | .D, .s11 => 0 | .D, .E => 0 | .D, .D => 5

def nonterminalMatrix : Matrix State State ℚ := (1 / 5 : ℚ) • nonterminalNumerator
def terminalMatrix : Matrix State State ℚ := (1 / 5 : ℚ) • terminalNumerator

noncomputable def independentCollision (k : ℕ) (A : Finset (Fin (k + 1)))
    (a a' : Side k A) : ℚ := (∑ u : Word k, ∑ v : Word k,
      if task (fullMerge A a u) = task (fullMerge A a' v) then (1 : ℚ) else 0) /
    (5 : ℚ) ^ (2 * (k + 1))

def emptySide0 : Side 0 (∅ : Finset (Fin 1)) :=
  by
    intro r
    cases r with
    | mk val h => contradiction

def emptyProfile0 : Profile 0 (∅ : Finset (Fin 1)) :=
  ⟨⟨⊤, by simp [Allowed]⟩, fun i => Fin.elim0 i⟩

noncomputable def actualMatrix (k : ℕ) (A : Finset (Fin (k+1)))
    (a a' : Side k A) (i : Fin (k+1)) : Matrix State State ℚ :=
  fun s t => (∑ x : Window,
    if stopStep (i = Fin.last k) s
      (if h : i ∈ A then a ⟨i,h⟩ else x)
      (if h : i ∈ A then a' ⟨i,h⟩ else x) = t then (1 : ℚ) else 0) / 5

noncomputable def sharedProbability (k : ℕ) (A : Finset (Fin (k+1)))
    (a a' : Side k A) : ℚ := (∑ b : Complement k A,
    if task (merge A a b) = task (merge A a' b) then (1 : ℚ) else 0) /
      5^(Fintype.card {i : Fin (k+1) // i ∉ A})

-- The prefix induction and its probability and operator consequences elaborate in one proof.
set_option maxHeartbeats 4000000 in
theorem result (k : ℕ) (A : Finset (Fin (k+1))) (P Q : Profile k A)
    (a a' : Side k A) (ha : code A a = encode P) (ha' : code A a' = encode Q) :
    (∀ u v : Word k, (pairRunWord u v = .E ↔ task u = task v) ∧
      (pairRunWord u v = .D ↔ task u ≠ task v) ∧
      (pairRunWord u v = .E ∨ pairRunWord u v = .D)) ∧
    fullProbability k A a a' = sharedProbability k A a a' ∧
    sharedProbability k A a a' = matrixEntry (actualMatrix k A a a') ∧
    sharedProbability k A a a' = collisionProbability k A P Q ∧
    matrixEntry (actualMatrix k A a a') = matrixEntry (SharedMatrix k A P Q) ∧
    collisionProbability k A P Q = matrixEntry (SharedMatrix k A P Q) ∧
    (∀ c c' : Side k A, code A c = encode P → code A c' = encode Q →
      matrixEntry (actualMatrix k A c c') = matrixEntry (actualMatrix k A a a')) ∧
    (∀ (i : Fin (k+1)) (h : i ∈ A) (s t : State),
      actualMatrix k A a a' i s t =
      if stopStep (i = Fin.last k) s (a ⟨i,h⟩) (a' ⟨i,h⟩) = t then 1 else 0) ∧
    (∀ i : Fin (k+1), i ∉ A → actualMatrix k A a a' i =
      if i = Fin.last k then terminalMatrix else nonterminalMatrix) ∧
    (∀ (i : Fin (k+1)) (s : State), (∀ t, 0 ≤ actualMatrix k A a a' i s t) ∧
      (∑ t : State, actualMatrix k A a a' i s t) = 1) ∧
    (∀ (i : Fin (k+1)) (t : State),
      actualMatrix k A a a' i .E t = (if .E = t then 1 else 0) ∧
      actualMatrix k A a a' i .D t = (if .D = t then 1 else 0)) ∧
    collisionProbability k A P P = 1 ∧
    (∀ c c' : Side k A, code A c = encode P → code A c' = encode P →
      sharedProbability k A c c' = 1) ∧
    (A = ∅ → collisionProbability k A P Q = 1) ∧
    (A = Finset.univ → sharedProbability k A a a' =
      if task (extend A a) = task (extend A a') then 1 else 0) ∧
    collisionProbability 0 ∅ emptyProfile0 emptyProfile0 = 1 ∧
    independentCollision 0 ∅ emptySide0 emptySide0 = 17/25 ∧
    stopStep true .s00 .zero .middle = .D ∧
    stopStep false .s00 .zero .middle = .s00 ∧
    task (fun _ : Fin 1 => Window.zero) = ((0 : Fin 1) : Label 0) ∧
    task (fun _ : Fin 1 => Window.middle) = (⊤ : Label 0) := by
  have bridge (u v : Word k) : pairRunWord u v = .E ↔ task u = task v := by
    classical
    let prev (w : Word k) (m : ℕ) : Bool :=
      if h : 0 < m ∧ m ≤ k+1 then last (w ⟨m-1, by omega⟩) else false
    let inc (w : Word k) (i : Fin (k+1)) := prev w i.val && first (w i)
    let C (w : Word k) := List.ofFn (inc w)
    let H (w : Word k) (m : ℕ) := ((C w).take m).findIdx? id
    let q (m : ℕ) := ((List.ofFn (fun i => (u i,v i))).take m).foldl
      (fun s p => stopStep false s p.1 p.2) .s00
    have bound (w : Word k) (m r : ℕ) (h : H w m = some r) : r < m := by
      have hr := (List.findIdx?_eq_some_iff_findIdx_eq.mp h).1
      dsimp [C] at hr
      simp only [List.length_take, List.length_ofFn] at hr
      omega
    have hs (w : Word k) (m : ℕ) (hm : m < k+1) :
        H w (m+1) = match H w m with
          | some r => some r | none => if inc w ⟨m,hm⟩ then some m else none := by
      change (((C w).take (m+1)).findIdx? id) = _
      rw [List.take_succ_eq_append_getElem (by simpa only [C,List.length_ofFn] using hm)]
      simp only [List.findIdx?_append, List.findIdx?_singleton, id_eq,
        C, List.getElem_ofFn, List.length_take, List.length_ofFn]
      rw [Nat.min_eq_left (by omega : m ≤ k+1)]
      change (H w m).or ((if inc w ⟨m,hm⟩ then some 0 else none).map
        (fun i => i+m)) = _
      cases h : H w m <;> cases hi : inc w ⟨m,hm⟩ <;> simp
    have ps (w : Word k) (m : ℕ) (hm : m < k+1) :
        prev w (m+1) = last (w ⟨m,hm⟩) := by
      simp only [prev, dite_true, show 0 < m+1 ∧ m+1 ≤ k+1 by omega,
        Nat.add_sub_cancel, and_self, dite_true]
    have qs (m : ℕ) (hm : m < k+1) :
        q (m+1) = stopStep false (q m) (u ⟨m,hm⟩) (v ⟨m,hm⟩) := by
      change (List.take (m+1) (List.ofFn (fun i => (u i,v i)))).foldl _ _ = _
      rw [List.take_succ_eq_append_getElem (by simpa only [List.length_ofFn] using hm)]
      simp only [List.foldl_append,List.foldl_cons,List.foldl_nil,List.getElem_ofFn]
      rfl
    have liveStep (r r' : Bool) (c d : Window) (m : ℕ) :
        stopStep false (liveState (r,r')) c d =
        match (if r && first c then some m else none),
          (if r' && first d then some m else none) with
        | none, none => liveState (last c,last d)
        | some a, some b => if a=b then .E else .D
        | _, _ => .D := by
      cases r <;> cases r' <;> cases c <;> cases d <;>
        simp [stopStep,liveState,previous,first,last]
    have inv : ∀ m : ℕ, m ≤ k →
        (∀ (w : Word k) (r : ℕ), H w m = some r → r < m) ∧
        (q m = match H u m, H v m with
          | none, none => liveState (prev u m, prev v m)
          | some r, some s => if r = s then .E else .D
          | _, _ => .D) := by
      intro m
      induction m with
      | zero => intro _; exact ⟨fun w r => bound w 0 r, by simp [q,H,prev,liveState]⟩
      | succ m ih =>
        intro hm
        obtain ⟨hb,he⟩ := ih (by omega)
        refine ⟨fun w r => bound w (m+1) r, ?_⟩
        rw [qs m (by omega), he, hs u m (by omega), hs v m (by omega),
          ps u m (by omega), ps v m (by omega)]
        cases hu : H u m with
        | none =>
          cases hv : H v m with
          | none =>
            exact liveStep _ _ _ _ _
          | some s =>
            have hsm : s < m := hb v s hv
            by_cases hi : inc u ⟨m,by omega⟩ = true <;>
              simp [hi,stopStep,show m ≠ s by omega]
        | some r =>
          cases hv : H v m with
          | none =>
            have hrm : r < m := hb u r hu
            by_cases hi : inc v ⟨m,by omega⟩ = true <;>
              simp [hi,stopStep,show r ≠ m by omega]
          | some s => by_cases h : r = s <;> simp [h,stopStep]
    let Z (w : Word k) := decide (w (Fin.last k) = Window.zero)
    let J (w : Word k) := C w ++ [Z w]
    have finSearch (w : Word k) :
        (J w).findIdx? id = match H w k with
          | some r => some r
          | none => if inc w (Fin.last k) then some k
            else if Z w then some (k+1) else none := by
      have hc : C w = (C w).take k ++ [inc w (Fin.last k)] := by
        have hh := List.take_succ_eq_append_getElem (l := C w) (i := k)
          (by simp only [C,List.length_ofFn]; omega)
        have ht : (C w).take (k+1) = C w :=
          List.take_of_length_le (by simp only [C,List.length_ofFn]; omega)
        rw [ht] at hh
        simpa only [C,List.getElem_ofFn,Fin.last] using hh
      change ((C w ++ [Z w]).findIdx? id) = _
      rw [hc]
      simp only [List.findIdx?_append, List.findIdx?_singleton, id_eq,
        List.length_append, List.length_singleton, List.length_take,
        C, List.length_ofFn]
      rw [Nat.min_eq_left (by omega : k ≤ k+1)]
      change ((H w k).or ((if inc w (Fin.last k) then some 0 else none).map
        (fun i => i+k))).or ((if Z w then some 0 else none).map (fun i => i+(k+1))) = _
      cases hh : H w k <;> cases hi : inc w (Fin.last k) <;> cases hz : Z w <;> simp
    have liveTerminal (r r' : Bool) (c d : Window) :
        stopStep true (liveState (r,r')) c d = .E ↔
        (if r && first c then some k else if c = .zero then some (k+1) else none) =
        (if r' && first d then some k else if d = .zero then some (k+1) else none) := by
      cases r <;> cases r' <;> cases c <;> cases d <;> simp [stopStep,liveState,previous,first]
    have terminal : stopStep true (q k) (u (Fin.last k)) (v (Fin.last k)) = .E ↔
        (J u).findIdx? id = (J v).findIdx? id := by
      obtain ⟨hb,he⟩ := inv k le_rfl
      rw [he, finSearch u, finSearch v]
      cases hu : H u k with
      | none =>
        cases hv : H v k with
        | none =>
          simpa only [inc,Fin.val_last,Z,decide_eq_true_eq] using
            liveTerminal (prev u k) (prev v k) (u (Fin.last k)) (v (Fin.last k))
        | some s =>
          have hsm := hb v s hv
          by_cases hi : inc u (Fin.last k) = true <;>
            cases hz : Z u <;>
            simp [hi,hz,stopStep,show k ≠ s by omega,show k+1 ≠ s by omega]
      | some r =>
        cases hv : H v k with
        | none =>
          have hrm := hb u r hu
          by_cases hi : inc v (Fin.last k) = true <;>
            cases hz : Z v <;>
            simp [hi,hz,stopStep,show r ≠ k by omega,show r ≠ k+1 by omega]
        | some s => by_cases h : r = s <;> simp [h,stopStep]
    have shape (w : Word k) : J w = false :: List.ofFn (fun j => decide (bad w j)) := by
      apply List.ext_getElem
      · simp only [J,C,List.length_append,List.length_ofFn,List.length_singleton,
          List.length_cons,List.length_nil]
      · intro i hi hi'
        cases i with
        | zero => simp [J,C,inc,prev,List.getElem_append_left]
        | succ i =>
          have hil : i < k+1 := by simpa only [List.length_cons,List.length_ofFn,
            Nat.succ_lt_succ_iff] using hi'
          by_cases hin : i < k
          · rw [List.getElem_append_left (by simp only [C,List.length_ofFn]; omega)]
            simp only [C,List.getElem_ofFn,List.getElem_cons_succ]
            simp only [inc,prev,Fin.val_mk,show 0 < i+1 ∧ i+1 ≤ k+1 by omega,
              dite_true,Nat.add_sub_cancel,bad,hin,and_self,Bool.decide_and]
            simp
          · have hei : i = k := by omega
            subst i
            change (C w ++ [Z w])[k+1] = _
            rw [List.getElem_append_right (as := C w) (by simp only [C,List.length_ofFn]; omega)]
            simp only [
              C,List.length_ofFn,Nat.sub_self,List.getElem_cons_zero,
              List.getElem_cons_succ,List.getElem_ofFn,Z,bad,Fin.val_mk,lt_self_iff_false,
              dite_false,Fin.last]
    have spec (w : Word k) (j : Fin (k+1)) :
        task w ≤ (j : Label k) ↔ ∃ i, bad w i ∧ i ≤ j := by
      simp only [task, Finset.inf_le_iff (WithTop.coe_lt_top j), Finset.mem_univ, true_and]
      apply exists_congr
      intro i
      by_cases h : bad w i <;> simp [h]
    let S : Label k → Option ℕ := fun t => Option.map (fun j : Fin (k+1) => j.val+1) t
    have identify (w : Word k) : (J w).findIdx? id = S (task w) := by
      rw [shape]
      cases ht : task w using WithTop.recTopCoe with
      | top =>
        have nohit (j : Fin (k+1)) : ¬ bad w j := by
          intro h
          have hh := (spec w j).mpr ⟨j,h,le_rfl⟩
          simp [ht] at hh
        have hn : (List.ofFn (fun j => decide (bad w j))).findIdx? id = none := by
          apply List.findIdx?_eq_none_iff.mpr
          intro x hx
          obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hx
          simp [nohit]
        simp only [List.findIdx?_cons,id_eq,Bool.false_eq_true,ite_false,hn,Option.map_none]
        rfl
      | coe j =>
        have hit : bad w j := by
          obtain ⟨i,hi,hij⟩ := (spec w j).mp (le_of_eq ht)
          have hji : j ≤ i := by
            have hh := (spec w i).mpr ⟨i,hi,le_rfl⟩
            rw [ht] at hh
            exact WithTop.coe_le_coe.mp hh
          simpa [le_antisymm hij hji] using hi
        have before (i : Fin (k+1)) (hij : i < j) : ¬ bad w i := by
          intro hi
          have hh := (spec w i).mpr ⟨i,hi,le_rfl⟩
          rw [ht] at hh
          exact (not_le_of_gt hij) (WithTop.coe_le_coe.mp hh)
        have search : (List.ofFn (fun j => decide (bad w j))).findIdx? id = some j.val := by
          apply List.findIdx?_eq_some_iff_getElem.mpr
          refine ⟨by simpa using j.isLt, ?_, ?_⟩
          · simpa only [List.getElem_ofFn,id_eq,decide_eq_true_eq] using hit
          · intro i hij; simpa only [List.getElem_ofFn,id_eq,decide_eq_true_eq] using
              before ⟨i,by omega⟩ hij
        simp only [List.findIdx?_cons,id_eq,Bool.false_eq_true,ite_false,search,Option.map_some]
        rfl
    have inj : Function.Injective S := by
      intro x y h
      cases x with
      | none =>
        cases y with
        | none => rfl
        | some b => simpa [S] using h
      | some a =>
        cases y with
        | none => simpa [S] using h
        | some b =>
          have he : a.val+1 = b.val+1 := by simpa [S] using h
          exact congrArg some (Fin.ext (by omega : a.val = b.val))
    have runAppend (ps : List (Window × Window)) (s : State) (c d : Window) :
        pairRun s (ps ++ [(c,d)]) = stopStep true
          (ps.foldl (fun s p => stopStep false s p.1 p.2) s) c d := by
      induction ps generalizing s with
      | nil => rfl
      | cons p ps ih =>
        cases ps with
        | nil => simpa [pairRun] using ih (stopStep false s p.1 p.2)
        | cons p' ps => simpa [pairRun] using ih (stopStep false s p.1 p.2)
    have qr : pairRunWord u v = stopStep true (q k) (u (Fin.last k)) (v (Fin.last k)) := by
      rw [pairRunWord,List.ofFn_succ_last,runAppend]
      congr 1
      dsimp [q]
      congr 1
      apply List.ext_getElem
      · simp
      · intro i hi hi'; simp only [List.getElem_ofFn,List.getElem_take]; rfl
    rw [qr, terminal, identify u, identify v]
    exact inj.eq_iff
  let rr (n : ℕ) (δ : Fin n → State → Window → State) (s : State)
      (w : Fin n → Window) :=
    (List.ofFn (fun i => fun s => δ i s (w i))).foldl (fun s f => f s) s
  let W (n : ℕ) (δ : Fin n → State → Window → State) (i : Fin n) :
      Matrix State State ℚ := fun s t => ∑ x : Window, if δ i s x = t then 1 else 0
  have rs (n : ℕ) (δ : Fin (n+1) → State → Window → State) (s : State)
      (x : Window) (w : Fin n → Window) :
      rr (n+1) δ s (Fin.cons x w) = rr n (fun i => δ i.succ) (δ 0 s x) w := by
    simp only [rr,List.ofFn_succ,Fin.cons_zero,Fin.cons_succ,List.foldl_cons]
  have count : ∀ n (δ : Fin n → State → Window → State) (s t : State),
      (∑ w : Fin n → Window, if rr n δ s w = t then (1 : ℚ) else 0) =
      (List.ofFn (W n δ)).prod s t := by
    intro n
    induction n with
    | zero =>
      intro δ s t
      rw [List.ofFn_zero,List.prod_nil]
      simp [rr,Matrix.one_apply]
    | succ n ih =>
      intro δ s t
      calc
        _ = ∑ x : Window, ∑ w : Fin n → Window,
            if rr n (fun i => δ i.succ) (δ 0 s x) w = t then (1 : ℚ) else 0 := by
          rw [← (Fin.consEquiv (fun _ : Fin (n+1) => Window)).sum_comp
            (fun w => if rr (n+1) δ s w = t then (1 : ℚ) else 0), Fintype.sum_prod_type]
          apply Finset.sum_congr rfl
          intro x _
          apply Finset.sum_congr rfl
          intro w _
          exact congrArg (fun y : State => if y = t then (1 : ℚ) else 0) (rs n δ s x w)
        _ = ∑ x : Window, (List.ofFn (W n (fun i => δ i.succ))).prod (δ 0 s x) t := by
          apply Finset.sum_congr rfl
          intro x _
          exact ih _ _ _
        _ = _ := by
          rw [List.ofFn_succ,List.prod_cons,Matrix.mul_apply]
          simp only [W,Finset.sum_mul]
          rw [Finset.sum_comm]
          simp
  have scale : ∀ n (δ : Fin n → State → Window → State),
      (List.ofFn (fun i => (1/5 : ℚ) • W n δ i)).prod =
      (1/5 : ℚ)^n • (List.ofFn (W n δ)).prod := by
    intro n
    induction n with
    | zero => intro δ; simp
    | succ n ih =>
      intro δ
      rw [List.ofFn_succ,List.prod_cons,ih,List.ofFn_succ,List.prod_cons,
        Matrix.smul_mul,Matrix.mul_smul,smul_smul,pow_succ']
  have average (n : ℕ) (δ : Fin n → State → Window → State) (s t : State) :
      (∑ w : Fin n → Window, if rr n δ s w = t then (1 : ℚ) else 0) / 5^n =
      (List.ofFn (fun i => (1/5 : ℚ) • W n δ i)).prod s t := by
    rw [count,scale]
    simp [div_eq_mul_inv,Matrix.smul_apply,mul_comm]
  have mergeAt (a : Side k A) (w : Word k) (i : Fin (k+1)) :
      fullMerge A a w i = if h : i ∈ A then a ⟨i,h⟩ else w i := by
    simp [fullMerge,merge,Equiv.piEquivPiSubtypeProd,Equiv.coe_fn_symm_mk]
  have runAppend (ps : List (Window × Window)) (s : State) (c d : Window) :
      pairRun s (ps ++ [(c,d)]) = stopStep true
        (ps.foldl (fun s p => stopStep false s p.1 p.2) s) c d := by
    induction ps generalizing s with
    | nil => rfl
    | cons p ps ih => cases ps <;> simpa [pairRun] using ih (stopStep false s p.1 p.2)
  have scheduled (u v : Word k) (w : Word k) :
      rr (k+1) (fun i s _ => stopStep (i = Fin.last k) s (u i) (v i)) .s00 w =
      pairRunWord u v := by
    dsimp only [rr,pairRunWord]
    rw [List.ofFn_succ_last,List.foldl_append,List.foldl_cons,List.foldl_nil,
      List.ofFn_succ_last,runAppend]
    simp only [decide_true]
    congr 1
    have hp : List.ofFn (fun i : Fin k => fun s =>
        stopStep (i.castSucc = Fin.last k) s (u i.castSucc) (v i.castSucc)) =
        (List.ofFn (fun i : Fin k => (u i.castSucc,v i.castSucc))).map
          (fun p s => stopStep false s p.1 p.2) := by
      rw [List.map_ofFn]
      apply congrArg List.ofFn
      funext i s
      simp [Fin.castSucc_ne_last]
    rw [hp,List.foldl_map]
  have allAverage (a a' : Side k A) : fullProbability k A a a' =
      matrixEntry (actualMatrix k A a a') := by
    let δ (i : Fin (k+1)) (s : State) (x : Window) :=
      stopStep (i = Fin.last k) s
        (if h : i ∈ A then a ⟨i,h⟩ else x)
        (if h : i ∈ A then a' ⟨i,h⟩ else x)
    have runEq (w : Word k) : rr (k+1) δ .s00 w =
        pairRunWord (fullMerge A a w) (fullMerge A a' w) := by
      have h := scheduled (fullMerge A a w) (fullMerge A a' w) w
      rw [← h]
      dsimp only [rr]
      simp only [δ,mergeAt]
    have hm : (fun i => (1/5 : ℚ) • W (k+1) δ i) = actualMatrix k A a a' := by
      funext i s t
      change (1/5 : ℚ) * W (k+1) δ i s t = _
      dsimp only [W,δ,actualMatrix]
      ring
    rw [fullProbability]
    convert average (k+1) δ .s00 .E using 1
    · apply congrArg (fun r : ℚ => r / 5^(k+1))
      apply Finset.sum_congr rfl
      intro w _
      simp only [runEq,bridge]
    · rw [hm]; rfl
  have windows : (Finset.univ : Finset Window) = {.zero,.low,.middle,.ends,.high} := rfl
  have cardWindow : Fintype.card Window = 5 := by decide
  have cardSide : Fintype.card (Side k A) = 5^A.card := by
    simp [Side,Fintype.card_fun,cardWindow]
  have addCards : A.card + Fintype.card {i : Fin (k+1) // i ∉ A} = k+1 := by
    rw [Fintype.card_subtype_compl]
    simp only [Fintype.card_fin,Fintype.card_coe]
    have h : A.card ≤ k+1 := by simpa using Finset.card_le_univ A
    omega
  have pushforward (f : Complement k A → ℚ) :
      (∑ w : Word k, f (fun r => w r.1)) = (5 : ℚ)^A.card * ∑ b, f b := by
    let e := Equiv.piEquivPiSubtypeProd (fun i : Fin (k+1) => i ∈ A) (fun _ => Window)
    have hs (c : Side k A) (b : Complement k A) :
        (fun r : {i : Fin (k+1) // i ∉ A} => e.symm (c,b) r.1) = b :=
      congrArg Prod.snd (e.apply_symm_apply (c,b))
    rw [← e.symm.sum_comp (fun w => f (fun r => w r.1)),Fintype.sum_prod_type]
    simp only [hs]
    simp [cardSide]
  have fullShared (a a' : Side k A) : fullProbability k A a a' =
      sharedProbability k A a a' := by
    rw [fullProbability]
    change (∑ w : Word k,
      (fun b : Complement k A => if task (merge A a b) = task (merge A a' b)
        then (1 : ℚ) else 0) (fun r => w r.1)) / 5^(k+1) = _
    rw [pushforward (fun b : Complement k A =>
      if task (merge A a b) = task (merge A a' b) then (1 : ℚ) else 0)]
    have hp : (5 : ℚ)^(k+1) = 5^A.card * 5^(Fintype.card {i : Fin (k+1) // i ∉ A}) := by
      calc (5 : ℚ)^(k+1) = 5^(A.card + Fintype.card {i : Fin (k+1) // i ∉ A}) :=
             congrArg _ addCards.symm
           _ = _ := pow_add _ _ _
    rw [hp]
    dsimp only [sharedProbability]
    field_simp
  have reps (P : Profile k A) (a : Side k A) (ha : code A a = encode P)
      (b : Complement k A) : task (merge A a b) =
        task (merge A (representative P) b) := by
    have hresp := ((FirstRejectionCutCapacity.result k A).2.2.1 a (representative P)).mpr
      (ha.trans ((FirstRejectionCutCapacity.result k A).1 P).symm)
    have transport (c : Side k A) :
        D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.response
          (fun _ : Fin (k+1) => Window)
          task (fun i => i ∈ A) c b = task (merge A c b) := by
      dsimp only [D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.response,merge]
      congr 1
      funext i
      by_cases hi : i ∈ A <;> simp [Equiv.piEquivPiSubtypeProd,hi]
    exact (transport a).symm.trans ((congrFun hresp b).trans (transport (representative P)))
  have canonical (P Q : Profile k A) (a a' : Side k A)
      (ha : code A a = encode P) (ha' : code A a' = encode Q) :
      sharedProbability k A a a' = collisionProbability k A P Q := by
    rw [← fullShared]
    simp only [collisionProbability,fullProbability]
    apply congrArg (fun r : ℚ => r / 5^(k+1))
    apply Finset.sum_congr rfl
    intro w _
    simp only [fullMerge,reps P a ha,reps Q a' ha']
    split_ifs <;> simp_all
  have diagonal (P : Profile k A) : collisionProbability k A P P = 1 := by
    simp [collisionProbability,fullProbability,Fintype.card_fun,cardWindow,Word]
  have fixed (a a' : Side k A) (i : Fin (k+1)) (h : i ∈ A) (s t : State) :
      actualMatrix k A a a' i s t =
      if stopStep (i = Fin.last k) s (a ⟨i,h⟩) (a' ⟨i,h⟩) = t then 1 else 0 := by
    simp only [actualMatrix,h,dite_true,Finset.sum_const,Finset.card_univ,cardWindow,
      nsmul_eq_mul,Nat.cast_ofNat]
    split_ifs <;> norm_num
  have shared (a a' : Side k A) (i : Fin (k+1)) (h : i ∉ A) :
      actualMatrix k A a a' i = if i = Fin.last k then terminalMatrix else nonterminalMatrix := by
    ext s t
    simp only [actualMatrix,h,dite_false]
    by_cases hi : i = Fin.last k <;> cases s <;> cases t <;>
      norm_num [actualMatrix,h,hi,terminalMatrix,nonterminalMatrix,
        terminalNumerator,nonterminalNumerator,windows,
        stopStep,previous,liveState,first,last,
        Matrix.smul_apply,Pi.smul_apply,smul_eq_mul] <;> simp +decide [Finset.sum_insert]
  have stochastic (a a' : Side k A) (i : Fin (k+1)) (s : State) :
      (∀ t, 0 ≤ actualMatrix k A a a' i s t) ∧
      (∑ t : State, actualMatrix k A a a' i s t) = 1 := by
    constructor
    · intro t
      apply div_nonneg
      · apply Finset.sum_nonneg; intro x _; split_ifs <;> norm_num
      · norm_num
    · simp only [actualMatrix,← Finset.sum_div]
      rw [Finset.sum_comm]
      simp [cardWindow]
  have absorb (a a' : Side k A) (i : Fin (k+1)) (t : State) :
      actualMatrix k A a a' i .E t = (if .E = t then 1 else 0) ∧
      actualMatrix k A a a' i .D t = (if .D = t then 1 else 0) := by
    simp only [actualMatrix,stopStep]
    constructor <;> by_cases he : State.E = t <;> by_cases hd : State.D = t <;>
      simp [he,hd,cardWindow]
  have empty (P Q : Profile k A) (h : A = ∅) : collisionProbability k A P Q = 1 := by
    subst A
    have hrep : (representative P : Side k ∅) = representative Q := by
      apply funext
      intro i
      exact (Finset.notMem_empty i.val i.property).elim
    rw [show collisionProbability k ∅ P Q = collisionProbability k ∅ P P by
      simp only [collisionProbability,hrep]]
    exact diagonal P
  have full (a a' : Side k A) (h : A = Finset.univ) :
      sharedProbability k A a a' =
      if task (extend A a) = task (extend A a') then 1 else 0 := by
    have noComp : Fintype.card {i : Fin (k+1) // i ∉ A} = 0 := by simp [h]
    have hm (b : Complement k A) (c : Side k A) : merge A c b = extend A c := by
      funext i
      simp [merge,extend,Equiv.piEquivPiSubtypeProd,Equiv.coe_fn_symm_mk,h]
    simp [sharedProbability,hm,noComp,Complement,Fintype.card_fun,cardWindow]
  have singleton (c : Window) : task (fun _ : Fin 1 => c) =
      if c = .zero then ((0 : Fin 1) : Label 0) else ⊤ := by
    simp [task,bad,Finset.univ_unique]
  have emptyMerge0 (w : Word 0) : fullMerge ∅ emptySide0 w = w := by
    funext i
    simp [fullMerge,merge,Equiv.piEquivPiSubtypeProd,Equiv.coe_fn_symm_mk]
  have independent : independentCollision 0 ∅ emptySide0 emptySide0 = 17/25 := by
    simp only [independentCollision,emptyMerge0]
    rw [← (Equiv.funUnique (Fin 1) Window).symm.sum_comp]
    simp only [Equiv.funUnique_symm_apply]
    simp_rw [← (Equiv.funUnique (Fin 1) Window).symm.sum_comp]
    simp only [Equiv.funUnique_symm_apply]
    change (∑ c : Window, ∑ d : Window,
      if task (fun _ : Fin 1 => c) = task (fun _ : Fin 1 => d) then (1 : ℚ) else 0) /
      5^(2*(0+1)) = 17/25
    simp only [singleton]
    norm_num [windows] <;>
      simp +decide [Finset.sum_insert,Finset.filter_insert,Finset.filter_singleton] <;> norm_num
  have endStates (u v : Word k) : pairRunWord u v = .E ∨ pairRunWord u v = .D := by
    have ht (s : State) (c d : Window) :
        stopStep true s c d = .E ∨ stopStep true s c d = .D := by
      cases s <;> cases c <;> cases d <;> decide
    rw [pairRunWord,List.ofFn_succ_last,runAppend]
    exact ht _ _ _
  have different (u v : Word k) : pairRunWord u v = .D ↔ task u ≠ task v := by
    have hs := endStates u v
    have he := bridge u v
    constructor
    · intro hd ht; have hE := he.mpr ht; rw [hd] at hE; contradiction
    · intro hn; rcases hs with hE | hD
      · exact (hn (he.mp hE)).elim
      · exact hD
  have transfer (c c' : Side k A) : sharedProbability k A c c' =
      matrixEntry (actualMatrix k A c c') := (fullShared c c').symm.trans (allAverage c c')
  have canonMatrix : collisionProbability k A P Q = matrixEntry (SharedMatrix k A P Q) := by
    have h := (canonical P Q (representative P) (representative Q)
      ((FirstRejectionCutCapacity.result k A).1 P)
      ((FirstRejectionCutCapacity.result k A).1 Q)).symm.trans
        (transfer (representative P) (representative Q))
    exact h
  refine ⟨fun u v => ⟨bridge u v,different u v,endStates u v⟩, fullShared a a',
    transfer a a',canonical P Q a a' ha ha',
    (transfer a a').symm.trans ((canonical P Q a a' ha ha').trans canonMatrix),
    canonMatrix,?_,fixed a a',shared a a',stochastic a a',absorb a a',diagonal P,?_,
    empty P Q,full a a',?_,independent,?_,?_,?_,?_⟩
  · intro c c' hc hc'
    exact (transfer c c').symm.trans ((canonical P Q c c' hc hc').trans
      ((canonical P Q a a' ha ha').symm.trans (transfer a a')))
  · intro c c' hc hc'
    exact (canonical P P c c' hc hc').trans (diagonal P)
  · simp [collisionProbability,fullProbability,Word,Fintype.card_fun,cardWindow]
  · simp [stopStep,previous,show Window.middle ≠ Window.zero by decide]
  · rfl
  · simpa using singleton Window.zero
  · simpa [show Window.middle ≠ Window.zero by decide] using singleton Window.middle

#print axioms result

end D5.S3.Arith.FibonacciAtomic.SharedCompletionCollision
