/- GID: D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/WindowRegisterCore
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/WindowRegisterCore
   mirror-E: none(waiver:unbounded-operational-correspondence)
   anchors: [mathlib/module/Mathlib.Data.Nat.Fib.Zeckendorf]
   utility: none
   digest: Fixed register tracks and physical copy with unrelated-tape frames. -/

import D5.S3.Arith.FibonacciAtomic.NativeContinuation.Acquisition.WindowAcquisitionPacked


namespace PhysicalWindowContinuation.RegisterHandoff

abbrev Lane := Fin 4

def target (j : Lane) : Track := ⟨j.val + 2, by omega⟩

def select (j : Lane) (b : Bits) : Bool :=
  if j = 0 then b.1 else if j = 1 then b.2.1 else if j = 2 then b.2.2.1 else b.2.2.2

inductive PortControl where
  | home (j : Lane) | targetEnter (j : Lane) | packedEnter (j : Lane)
  | scan (j : Lane) | store (j : Lane) (b : Bool)
  | targetAdvance (j : Lane) | packedAdvance (j : Lane)
  | trimEnter (j : Lane) | trim (j : Lane) | erase (j : Lane) | trimMove (j : Lane)
  | endMove (j : Lane) | endWrite (j : Lane)
  | zeroMove (j : Lane) | zeroWrite (j : Lane)
  | rewindMove (j : Lane) | rewind (j : Lane)
  | packedRewindMove (j : Lane) | packedRewind (j : Lane)
  | laneDone (j : Lane) | done | reject
  deriving DecidableEq, Fintype, Repr

inductive PortInstruction where
  | read (track : Track) (next : Symbol → PortControl)
  | write (track : Track) (value : Symbol) (next : PortControl)
  | move (track : Track) (right : Bool) (next : PortControl)
  | halt

def program : PortControl → PortInstruction
  | .home j => .write (target j) .home (.targetEnter j)
  | .targetEnter j => .move (target j) true (.packedEnter j)
  | .packedEnter j => .move workTrack true (.scan j)
  | .scan j => .read workTrack fun s => match s with
      | .column b => .store j (select j b)
      | .blank => .trimEnter j
      | _ => .reject
  | .store j b => .write (target j) (.unit b) (.targetAdvance j)
  | .targetAdvance j => .move (target j) true (.packedAdvance j)
  | .packedAdvance j => .move workTrack true (.scan j)
  | .trimEnter j => .move (target j) false (.trim j)
  | .trim j => .read (target j) fun s => match s with
      | .unit false => .erase j
      | .unit true => .endMove j
      | .home => .zeroMove j
      | _ => .reject
  | .erase j => .write (target j) .blank (.trimMove j)
  | .trimMove j => .move (target j) false (.trim j)
  | .endMove j => .move (target j) true (.endWrite j)
  | .endWrite j => .write (target j) (.window .zero) (.rewindMove j)
  | .zeroMove j => .move (target j) true (.zeroWrite j)
  | .zeroWrite j => .write (target j) (.unit false) (.endMove j)
  | .rewindMove j => .move (target j) false (.rewind j)
  | .rewind j => .read (target j) fun s => match s with
      | .unit _ => .rewindMove j
      | .home => .packedRewindMove j
      | _ => .reject
  | .packedRewindMove j => .move workTrack false (.packedRewind j)
  | .packedRewind j => .read workTrack fun s => match s with
      | .column _ => .packedRewindMove j
      | .home => .laneDone j
      | _ => .reject
  | .laneDone j => if hj : j.val + 1 < 4 then
      .read workTrack fun _ => .home ⟨j.val+1,hj⟩
    else .read workTrack fun _ => .done
  | .done | .reject => .halt

structure PortConfig where
  control : PortControl
  head : Track → ℤ
  cell : Track → ℤ → Symbol

def step (c : PortConfig) : PortConfig :=
  match program c.control with
  | .read t f => { c with control := f (c.cell t (c.head t)) }
  | .write t b k => { c with
      control := k
      cell := Function.update c.cell t (Function.update (c.cell t) (c.head t) b) }
  | .move t d k => { c with
      control := k
      head := Function.update c.head t (c.head t + (if d then 1 else -1)) }
  | .halt => c

def run (c : PortConfig) (n : ℕ) := step^[n] c

def tape (xs : List Symbol) (z : ℤ) : Symbol :=
  if z = 0 then .home else if 0 < z then xs[z.toNat-1]?.getD .blank else .blank

/-- `m` and `h` are a proof-level literal snapshot, never runtime registers. -/
def config (m : Track → ℤ → Symbol) (h : Track → ℤ) (j : Lane)
    (bs : List Bits) (xs : List Symbol) (p q : ℤ) (k : PortControl) : PortConfig where
  control := k
  head := Function.update (Function.update h workTrack p) (target j) q
  cell := Function.update (Function.update m workTrack (word bs)) (target j) (tape xs)

def Frame (m : Track → ℤ → Symbol) (h : Track → ℤ) (j : Lane)
    (bs : List Bits) (L : ℕ) (c : PortConfig) : Prop :=
  c.cell workTrack = word bs ∧
  (∀ t, t ≠ workTrack → t ≠ target j → c.cell t = m t ∧ c.head t = h t) ∧
  0 ≤ c.head workTrack ∧ c.head workTrack ≤ L+1 ∧
  0 ≤ c.head (target j) ∧ c.head (target j) ≤ L+2

theorem target_ne_work (j : Lane) : target j ≠ workTrack := by
  intro he
  have := congrArg Fin.val he
  simp [target,workTrack] at this

theorem target_ne_source (j : Lane) : target j ≠ sourceTrack := by
  intro he
  have := congrArg Fin.val he
  simp [target,sourceTrack] at this

theorem config_ext {a b : PortConfig} (hc : a.control = b.control)
    (hh : a.head = b.head) (hm : a.cell = b.cell) : a = b := by
  cases a; cases b; cases hc; cases hh; cases hm; rfl

theorem tape_read (pre suf : List Symbol) (b : Symbol) :
    tape (pre ++ b :: suf) (pre.length + 1) = b := by
  have hp : 0 < (pre.length : ℤ) + 1 := by omega
  simp [tape,ne_of_gt hp,hp]

theorem tape_blank (xs : List Symbol) : tape xs (xs.length+1) = .blank := by
  have hp : 0 < (xs.length : ℤ)+1 := by omega
  simp [tape,ne_of_gt hp,hp]

theorem tape_append (pre : List Symbol) (b : Symbol) :
    Function.update (tape pre) (pre.length+1) b = tape (pre++[b]) := by
  funext z
  by_cases hz : z = (pre.length : ℤ)+1
  · subst z
    simp only [Function.update_self]
    exact (tape_read pre [] b).symm
  · simp only [Function.update_of_ne hz]
    by_cases h0 : z = 0
    · simp [tape,h0]
    by_cases hp : 0 < z
    · have hn : z.toNat-1 ≠ pre.length := by omega
      simp only [tape,h0,hp,↓reduceIte,List.getElem?_append]
      by_cases hl : z.toNat-1 < pre.length
      · simp [hl]
      · have hs : z.toNat-1-pre.length ≠ 0 := by omega
        simp [hl,hs]
    · simp [tape,h0,hp]

theorem tape_erase (pre : List Symbol) (b : Symbol) :
    Function.update (tape (pre++[b])) (pre.length+1) .blank = tape pre := by
  rw [← tape_append]
  funext z
  by_cases hz : z = (pre.length : ℤ)+1
  · subst z
    simp [tape_blank]
  · simp [Function.update_of_ne hz]

theorem config_frame (m : Track → ℤ → Symbol) (h : Track → ℤ) (j : Lane)
    (bs : List Bits) (xs : List Symbol) (p q : ℤ) (k : PortControl) (L : ℕ)
    (hp : 0 ≤ p) (hpL : p ≤ L+1) (hq : 0 ≤ q) (hqL : q ≤ L+2) :
    Frame m h j bs L (config m h j bs xs p q k) := by
  have ht := target_ne_work j
  refine ⟨by simp [config,ht.symm],?_,?_,?_,?_,?_⟩
  · intro t hw hr
    simp [config,hw,hr]
  all_goals simp only [config,Function.update_self,Function.update_of_ne ht.symm]; omega

theorem frame_join (m h j bs L a b x y) (he : run x a = y)
    (hx : ∀ t ≤ a, Frame m h j bs L (run x t))
    (hy : ∀ t ≤ b, Frame m h j bs L (run y t)) :
    ∀ t ≤ b+a, Frame m h j bs L (run x t) := by
  intro t ht
  by_cases hta : t ≤ a
  · exact hx t hta
  · rw [show t = (t-a)+a by omega,run,Function.iterate_add_apply]
    change Frame m h j bs L (run (run x a) (t-a))
    rw [he]
    exact hy _ (by omega)

/-- One actual read, one bit write, and two individual head moves. -/
theorem copy_four (m h j) (pre suf : List Bits) (b : Bits) :
    run (config m h j (pre++b::suf) ((pre.map (select j)).map Symbol.unit)
      (pre.length+1) (pre.length+1) (.scan j)) 4 =
    config m h j (pre++b::suf) (((pre++[b]).map (select j)).map Symbol.unit)
      (pre.length+2) (pre.length+2) (.scan j) := by
  have ht := target_ne_work j
  simp only [run,show 4 = 1+1+1+1 from rfl,
    Function.iterate_succ_apply,Function.iterate_zero_apply]
  apply config_ext
  · simp [step,program,config,ht.symm,word_read]
  · simp [step,program,config,ht.symm,word_read]
    funext t
    by_cases hw : t=workTrack <;> by_cases hr : t=target j <;>
      simp_all [Function.update_apply]
    all_goals omega
  · simp [step,program,config,ht.symm,word_read]
    funext t z
    by_cases hr : t=target j
    · subst t
      simpa [List.map_append,Function.update_apply] using
        congrFun (tape_append ((pre.map (select j)).map Symbol.unit) (.unit (select j b))) z
    · simp [hr,Function.update_apply]

end PhysicalWindowContinuation.RegisterHandoff

namespace PhysicalWindowContinuation.RegisterHandoff

theorem copy_four_frame (m h j) (pre suf : List Bits) (b : Bits) (L : ℕ)
    (hL : pre.length+1 ≤ L) :
    ∀ n ≤ 4, Frame m h j (pre++b::suf) L
      (run (config m h j (pre++b::suf) ((pre.map (select j)).map Symbol.unit)
        (pre.length+1) (pre.length+1) (.scan j)) n) := by
  have ht := target_ne_work j
  intro n hn
  interval_cases n
  all_goals
    simp only [run,Function.iterate_succ_apply,Function.iterate_zero_apply]
    simp [Frame,step,program,config,ht,ht.symm,word_read,Function.update_apply]
    refine ⟨?_,by omega,by omega,by omega,by omega⟩
    intro t hw hr
    simp [hw,hr]

theorem copy_prefix (m h j) (pre bs : List Bits) (L : ℕ)
    (hL : pre.length+bs.length ≤ L) :
    run (config m h j (pre++bs) ((pre.map (select j)).map Symbol.unit)
      (pre.length+1) (pre.length+1) (.scan j)) (4*bs.length) =
      config m h j (pre++bs) (((pre++bs).map (select j)).map Symbol.unit)
        (pre.length+bs.length+1) (pre.length+bs.length+1) (.scan j) ∧
    ∀ n ≤ 4*bs.length, Frame m h j (pre++bs) L
      (run (config m h j (pre++bs) ((pre.map (select j)).map Symbol.unit)
        (pre.length+1) (pre.length+1) (.scan j)) n) := by
  induction bs generalizing pre with
  | nil =>
    refine ⟨by simp [run],?_⟩
    intro n hn
    have hn0 : n=0 := by simpa using hn
    subst n
    exact config_frame _ _ _ _ _ _ _ _ _ (by omega) (by simp at hL; omega)
      (by omega) (by simp at hL; omega)
  | cons b bs ih =>
    have hh : (pre++[b]).length=pre.length+1 := by simp
    obtain ⟨he,hf⟩ := ih (pre++[b]) (by simp at hL; omega)
    have hs := copy_four m h j pre bs b
    have he' : run (config m h j (pre++b::bs) ((pre.map (select j)).map Symbol.unit)
        (pre.length+1) (pre.length+1) (.scan j)) (4*bs.length+4) =
      config m h j (pre++b::bs) (((pre++b::bs).map (select j)).map Symbol.unit)
        (pre.length+(b::bs).length+1) (pre.length+(b::bs).length+1) (.scan j) := by
      rw [run,Function.iterate_add_apply]
      change run (run _ 4) (4*bs.length)=_
      rw [hs]
      simpa [List.append_assoc,hh,Int.add_assoc,Int.add_comm,Int.add_left_comm] using he
    refine ⟨?_,?_⟩
    · rw [show 4*(b::bs).length=4*bs.length+4 by simp; omega]
      exact he'
    · rw [show 4*(b::bs).length=4*bs.length+4 by simp; omega]
      apply frame_join m h j (pre++b::bs) L 4 (4*bs.length) _ _ hs
      · exact copy_four_frame m h j pre bs b L (by simp at hL; omega)
      · simpa [List.append_assoc,hh,Int.add_assoc] using hf

/-- Remove high-end zero padding; zero has one explicit zero bit. -/
def stripped (bs : List Bool) : List Bool := (bs.reverse.dropWhile (! ·)).reverse

def normalized (bs : List Bool) : List Bool :=
  if stripped bs = [] then [false] else stripped bs

theorem stripped_false (bs : List Bool) : stripped (bs++[false])=stripped bs := by
  simp [stripped,List.reverse_append,List.dropWhile_cons]

theorem stripped_true (bs : List Bool) : stripped (bs++[true])=bs++[true] := by
  simp [stripped,List.reverse_append,List.dropWhile_cons]

theorem normalized_false (bs : List Bool) : normalized (bs++[false])=normalized bs := by
  simp [normalized,stripped_false]

theorem normalized_true (bs : List Bool) : normalized (bs++[true])=bs++[true] := by
  simp [normalized,stripped_true]

theorem normalized_length (bs : List Bool) : (normalized bs).length ≤ bs.length+1 := by
  unfold normalized
  split
  · simp
  · have hh := List.length_dropWhile_le (p := (! ·)) (l := bs.reverse)
    change (stripped bs).length ≤ bs.length+1
    dsimp only [stripped]
    simp only [List.length_reverse] at hh ⊢
    omega

/-- The physical clearing loop does not change the natural number. -/
theorem normalized_value (bs : List Bool) :
    Nat.ofDigits 2 ((normalized bs).map Bool.toNat)=Nat.ofDigits 2 (bs.map Bool.toNat) := by
  induction bs using List.reverseRecOn with
  | nil => simp [normalized,stripped,Nat.ofDigits]
  | append_singleton bs b ih =>
    cases b
    · rw [normalized_false,ih]
      simp [List.map_append,Nat.ofDigits_append_zero]
    · rw [normalized_true]

/-- Every output is either the single zero or ends in a one. -/
theorem normalized_shape (bs : List Bool) :
    normalized bs=[false] ∨ ∃ pre, normalized bs=pre++[true] := by
  induction bs using List.reverseRecOn with
  | nil => simp [normalized,stripped]
  | append_singleton bs b ih =>
    cases b
    · simpa [normalized_false] using ih
    · exact Or.inr ⟨bs,normalized_true bs⟩


end PhysicalWindowContinuation.RegisterHandoff
