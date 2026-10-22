/- GID: D5/S0/Computability/WindowAcquisitionCore
   generality: I
   mirror-B: D5/B/S0/Computability/WindowAcquisitionCore
   mirror-E: none(waiver:unbounded-operational-correspondence)
   anchors: [mathlib/module/Mathlib.Logic.Function.Iterate]
   utility: none
   digest: Finite-control local window arithmetic with an attained scan and rewind. -/

import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Option
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.IntervalCases
import Lean.Elab.Tactic.Omega
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import D5.S0.Computability.Coding.PhysicalSixParser
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace PhysicalWindowContinuation

inductive Window where
  | zero | low | middle | both | high
  deriving DecidableEq, Repr

instance : Fintype Window where
  elems := {.zero, .low, .middle, .both, .high}
  complete w := by cases w <;> simp

def low : Window → Bool
  | .low | .both => true
  | _ => false

def high : Window → Bool
  | .high | .both => true
  | _ => false

def displacement : Window → Fin 3 × Fin 5
  | .zero => (0, 0)
  | .low => (1, 0)
  | .middle => (0, 1)
  | .both => (2, 1)
  | .high => (1, 1)

abbrev Bits := Bool × Bool × Bool × Bool

inductive Symbol where
  | blank | home
  | window (w : Window)
  | unit (b : Bool)
  | column (bits : Bits)
  deriving DecidableEq, Fintype, Repr

structure Carry where
  first : Fin 3
  second : Fin 5
  count : Bool
  deriving DecidableEq, Fintype, Repr

def active (c : Carry) : Bool := c.first != 0 || c.second != 0 || c.count

def transfer (c : Carry) (bits : Bits) : Bits × Carry :=
  let a := bits.1.toNat + 2 * bits.2.1.toNat + c.first.val
  let b := 2 * bits.1.toNat + 3 * bits.2.1.toNat + c.second.val
  let k := bits.2.2.1.toNat + c.count.toNat
  ((decide (a % 2 = 1), decide (b % 2 = 1), decide (k % 2 = 1), false),
   { first := ⟨a / 2, by
       have hc := c.first.isLt
       have ha := Bool.toNat_le bits.1
       have hb := Bool.toNat_le bits.2.1
       dsimp [a]
       omega⟩
     second := ⟨b / 2, by
       have hc := c.second.isLt
       have ha := Bool.toNat_le bits.1
       have hb := Bool.toNat_le bits.2.1
       dsimp [b]
       omega⟩
     count := decide (k / 2 = 1) })

def finishTransfer (carry : Fin 5) (bits : Bits) : Bits × Fin 5 :=
  let n := 2 * bits.1.toNat + 3 * bits.2.1.toNat + carry.val
  ((bits.1, bits.2.1, bits.2.2.1, decide (n % 2 = 1)),
   ⟨n / 2, by
      have hc := carry.isLt
      have ha := Bool.toNat_le bits.1
      have hb := Bool.toNat_le bits.2.1
      dsimp [n]
      omega⟩)

inductive Control where
  | initHome | initMove | initZero | initBack
  | source (previous : Bool)
  | enter (previous : Bool) (carry : Carry)
  | scan (previous : Bool) (carry : Carry)
  | store (previous : Bool) (bits : Bits) (carry : Carry)
  | advance (previous : Bool) (carry : Carry)
  | rewind (previous : Bool)
  | rewindMove (previous : Bool)
  | sourceMove (previous : Bool)
  | finishEnter (carry : Fin 5)
  | finishScan (carry : Fin 5) (seen : Bool)
  | finishStore (bits : Bits) (carry : Fin 5) (seen : Bool)
  | finishAdvance (carry : Fin 5) (seen : Bool)
  | finishRewind (positive : Bool)
  | finishRewindMove (positive : Bool)
  | done | reject
  deriving DecidableEq, Fintype, Repr

abbrev Track := Fin 8

def sourceTrack : Track := 0
def workTrack : Track := 1

inductive Instruction where
  | read (track : Track) (next : Symbol → Control)
  | write (track : Track) (value : Symbol) (next : Control)
  | move (track : Track) (right : Bool) (next : Control)
  | halt

def zeros : Bits := (false, false, false, false)

def program : Control → Instruction
  | .initHome => .write workTrack .home .initMove
  | .initMove => .move workTrack true .initZero
  | .initZero => .write workTrack (.column zeros) .initBack
  | .initBack => .move workTrack false (.source false)
  | .source previous => .read sourceTrack fun symbol =>
      match symbol with
      | .window w => if previous && high w then .reject
          else .enter (low w) ⟨(displacement w).1, (displacement w).2, true⟩
      | .unit e => if previous && e then .reject else .finishEnter (if e then 1 else 0)
      | _ => .reject
  | .enter previous carry => .move workTrack true (.scan previous carry)
  | .scan previous carry => .read workTrack fun symbol =>
      match symbol with
      | .column bits => let next := transfer carry bits
          .store previous next.1 next.2
      | .blank => if active carry then
          let next := transfer carry zeros
          .store previous next.1 next.2
        else .rewindMove previous
      | _ => .reject
  | .store previous bits carry => .write workTrack (.column bits) (.advance previous carry)
  | .advance previous carry => .move workTrack true (.scan previous carry)
  | .rewindMove previous => .move workTrack false (.rewind previous)
  | .rewind previous => .read workTrack fun symbol =>
      match symbol with
      | .home => .sourceMove previous
      | .column _ => .rewindMove previous
      | _ => .reject
  | .sourceMove previous => .move sourceTrack true (.source previous)
  | .finishEnter carry => .move workTrack true (.finishScan carry false)
  | .finishScan carry seen => .read workTrack fun symbol =>
      match symbol with
      | .column bits => let next := finishTransfer carry bits
          .finishStore next.1 next.2 (seen || next.1.2.2.2)
      | .blank => if carry != 0 then
          let next := finishTransfer carry zeros
          .finishStore next.1 next.2 (seen || next.1.2.2.2)
        else .finishRewindMove seen
      | _ => .reject
  | .finishStore bits carry seen =>
      .write workTrack (.column bits) (.finishAdvance carry seen)
  | .finishAdvance carry seen => .move workTrack true (.finishScan carry seen)
  | .finishRewindMove positive => .move workTrack false (.finishRewind positive)
  | .finishRewind positive => .read workTrack fun symbol =>
      match symbol with
      | .home => if positive then .done else .reject
      | .column _ => .finishRewindMove positive
      | _ => .reject
  | .done | .reject => .halt

structure Configuration where
  control : Control
  head : Track → ℤ
  cell : Track → ℤ → Symbol

def step (c : Configuration) : Configuration :=
  match program c.control with
  | .read t f => { c with control := f (c.cell t (c.head t)) }
  | .write t b k => { c with
      control := k
      cell := Function.update c.cell t (Function.update (c.cell t) (c.head t) b) }
  | .move t d k => { c with
      control := k
      head := Function.update c.head t (c.head t + (if d then 1 else -1)) }
  | .halt => c

def run (c : Configuration) (n : ℕ) : Configuration := step^[n] c

def initial (w : List Window) (e : Bool) : Configuration where
  control := .initHome
  head := fun _ => 0
  cell := fun t z => if t = sourceTrack ∧ 0 ≤ z then
    ((w.map Symbol.window ++ [.unit e])[z.toNat]?).getD .blank else .blank

def word (bs : List Bits) (z : ℤ) : Symbol :=
  if z = 0 then .home else if 0 < z then
    ((bs.map Symbol.column)[z.toNat - 1]?).getD .blank else .blank

def boundary (source : ℤ → Symbol) (p : ℤ) (bs : List Bits)
    (q : ℤ) (k : Control) : Configuration where
  control := k
  head := fun t => if t = workTrack then q else if t = sourceTrack then p else 0
  cell := fun t => if t = workTrack then word bs
    else if t = sourceTrack then source else fun _ => .blank

theorem config_ext {a b : Configuration} (hc : a.control = b.control)
    (hh : a.head = b.head) (hm : a.cell = b.cell) : a = b := by
  cases a
  cases b
  cases hc
  cases hh
  cases hm
  rfl

theorem word_read (pre suf : List Bits) (b : Bits) :
    word (pre ++ b :: suf) (pre.length + 1) = .column b := by
  have hp : 0 < (pre.length : ℤ) + 1 := by omega
  simp [word, ne_of_gt hp, hp]

theorem word_replace (pre suf : List Bits) (a b : Bits) :
    Function.update (word (pre ++ a :: suf)) (pre.length + 1) (.column b) =
      word (pre ++ b :: suf) := by
  funext z
  by_cases hz : z = (pre.length : ℤ) + 1
  · subst z
    simp only [Function.update_self]
    exact (word_read pre suf b).symm
  · simp only [Function.update_of_ne hz]
    by_cases h0 : z = 0
    · simp [word, h0]
    by_cases hp : 0 < z
    · have hn : z.toNat - 1 ≠ pre.length := by omega
      simp only [word, h0, hp, ↓reduceIte, List.map_append, List.map_cons,
        List.getElem?_append, List.length_map]
      by_cases hl : z.toNat - 1 < pre.length
      · simp [hl]
      · have hs : z.toNat - 1 - pre.length ≠ 0 := by omega
        simp [hl, List.getElem?_cons, hs]
    · simp [word, h0, hp]

def Safe (source : ℤ → Symbol) (p : ℤ) (L : ℕ) (c : Configuration) : Prop :=
  c.cell sourceTrack = source ∧ c.head sourceTrack = p ∧
  (∀ t, t ≠ workTrack → t ≠ sourceTrack →
    c.head t = 0 ∧ c.cell t = fun _ => .blank) ∧
  0 ≤ c.head workTrack ∧ c.head workTrack ≤ L + 1

theorem boundary_safe (source : ℤ → Symbol) (p : ℤ) (bs : List Bits)
    (q : ℤ) (k : Control) (L : ℕ) (hq : 0 ≤ q) (hL : q ≤ L + 1) :
    Safe source p L (boundary source p bs q k) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [boundary, workTrack, sourceTrack]
  · simp [boundary, workTrack, sourceTrack]
  · intro t ht hs
    simp [boundary, ht, hs]
  · simpa [boundary] using hq
  · simpa [boundary] using hL

theorem scan_three (source : ℤ → Symbol) (p : ℤ) (pre suf : List Bits)
    (b : Bits) (previous : Bool) (carry : Carry) :
    run (boundary source p (pre ++ b :: suf) (pre.length + 1)
      (.scan previous carry)) 3 =
    boundary source p (pre ++ (transfer carry b).1 :: suf) (pre.length + 2)
      (.scan previous (transfer carry b).2) := by
  simp only [run, show 3 = 1 + 1 + 1 from rfl,
    Function.iterate_succ_apply, Function.iterate_zero_apply]
  apply config_ext
  · simp [step, program, boundary, word_read]
  · simp [step, program, boundary, word_read]
    funext t
    by_cases hw : t = workTrack
    · simp [hw]
      omega
    · simp [hw]
  · simp [step, program, boundary, word_read]
    funext t z
    by_cases hw : t = workTrack
    · subst t
      simpa [boundary, Function.update_apply] using
        congrFun (word_replace pre suf b (transfer carry b).1) z
    · simp [hw]

def sweep : Carry → List Bits → List Bits × Carry
  | carry, [] => ([], carry)
  | carry, b :: bs =>
      let one := transfer carry b
      let rest := sweep one.2 bs
      (one.1 :: rest.1, rest.2)

theorem sweep_length (carry : Carry) (bs : List Bits) :
    (sweep carry bs).1.length = bs.length := by
  induction bs generalizing carry with
  | nil => rfl
  | cons b bs ih => simp [sweep, ih]

theorem scan_prefix (source : ℤ → Symbol) (p : ℤ) (pre bs : List Bits)
    (previous : Bool) (carry : Carry) :
    run (boundary source p (pre ++ bs) (pre.length + 1)
      (.scan previous carry)) (3 * bs.length) =
    boundary source p (pre ++ (sweep carry bs).1) (pre.length + bs.length + 1)
      (.scan previous (sweep carry bs).2) := by
  induction bs generalizing carry pre with
  | nil => simp [sweep, run]
  | cons b bs ih =>
    rw [show 3 * (b :: bs).length = 3 * bs.length + 3 by simp; omega]
    rw [run, Function.iterate_add_apply]
    change run (run _ 3) (3 * bs.length) = _
    rw [scan_three]
    have next := ih (pre ++ [(transfer carry b).1]) (transfer carry b).2
    simpa [List.append_assoc, sweep, List.length_append, Nat.add_assoc,
      Int.add_assoc, Int.add_left_comm, Int.add_comm] using next

theorem scan_three_safe (source : ℤ → Symbol) (p : ℤ) (pre suf : List Bits)
    (b : Bits) (previous : Bool) (carry : Carry) (L : ℕ)
    (hL : pre.length + 1 ≤ L) :
    ∀ t ≤ 3, Safe source p L
      (run (boundary source p (pre ++ b :: suf) (pre.length + 1)
        (.scan previous carry)) t) := by
  intro t ht
  interval_cases t
  all_goals
    simp only [run, Function.iterate_succ_apply, Function.iterate_zero_apply]
    simp [Safe, step, program, boundary, word_read, Function.update_apply,
      workTrack, sourceTrack]
    refine ⟨?_, by omega, by omega⟩
    intro t hw hs
    simp [hw, hs]

theorem scan_prefix_safe (source : ℤ → Symbol) (p : ℤ) (pre bs : List Bits)
    (previous : Bool) (carry : Carry) (L : ℕ) (hL : pre.length + bs.length ≤ L) :
    ∀ t ≤ 3 * bs.length, Safe source p L
      (run (boundary source p (pre ++ bs) (pre.length + 1)
        (.scan previous carry)) t) := by
  induction bs generalizing carry pre with
  | nil =>
    intro t ht
    have he : t = 0 := by simpa using ht
    subst t
    rw [List.append_nil]
    exact boundary_safe source p pre (pre.length + 1)
      (.scan previous carry) L (by omega) (by simp at hL; omega)
  | cons b bs ih =>
    intro t ht
    by_cases hsmall : t ≤ 3
    · exact scan_three_safe source p pre bs b previous carry L
        (by simp at hL; omega) t hsmall
    · have he : t = (t - 3) + 3 := by omega
      rw [he, run, Function.iterate_add_apply]
      change Safe source p L (run (run _ 3) (t - 3))
      rw [scan_three]
      have next := ih (pre ++ [(transfer carry b).1]) (transfer carry b).2
        (by simp only [List.length_append, List.length_singleton]
            simp only [List.length_cons] at hL
            omega) (t - 3) (by simp at ht; omega)
      simpa [List.append_assoc, Int.add_assoc] using next

theorem word_blank (bs : List Bits) : word bs (bs.length + 1) = .blank := by
  have hp : 0 < (bs.length : ℤ) + 1 := by omega
  simp [word, ne_of_gt hp, hp]

theorem word_append (pre : List Bits) (b : Bits) :
    Function.update (word pre) (pre.length + 1) (.column b) = word (pre ++ [b]) := by
  funext z
  by_cases hz : z = (pre.length : ℤ) + 1
  · subst z
    simp only [Function.update_self]
    exact (word_read pre [] b).symm
  · simp only [Function.update_of_ne hz]
    by_cases h0 : z = 0
    · simp [word, h0]
    by_cases hp : 0 < z
    · have hn : z.toNat - 1 ≠ pre.length := by omega
      simp only [word, h0, hp, ↓reduceIte, List.map_append, List.map_cons,
        List.map_nil, List.getElem?_append, List.length_map]
      by_cases hl : z.toNat - 1 < pre.length
      · simp [hl]
      · have hs : z.toNat - 1 - pre.length ≠ 0 := by omega
        simp [hl, hs]
    · simp [word, h0, hp]

def flush : ℕ → Carry → List Bits × Carry
  | 0, c => ([], c)
  | n + 1, c => if active c then
      let one := transfer c zeros
      let rest := flush n one.2
      (one.1 :: rest.1, rest.2)
    else ([], c)

theorem flush_length (fuel : ℕ) (carry : Carry) :
    (flush fuel carry).1.length ≤ fuel := by
  induction fuel generalizing carry with
  | zero => simp [flush]
  | succ fuel ih =>
    simp only [flush]
    split
    · simpa using Nat.succ_le_succ (ih (transfer carry zeros).2)
    · simp

theorem flush_three_inactive : ∀ carry : Carry, active (flush 3 carry).2 = false := by
  decide

theorem scan_blank_three (source : ℤ → Symbol) (p : ℤ) (pre : List Bits)
    (previous : Bool) (carry : Carry) (ha : active carry = true) :
    run (boundary source p pre (pre.length + 1) (.scan previous carry)) 3 =
    boundary source p (pre ++ [(transfer carry zeros).1]) (pre.length + 2)
      (.scan previous (transfer carry zeros).2) := by
  simp only [run, show 3 = 1 + 1 + 1 from rfl,
    Function.iterate_succ_apply, Function.iterate_zero_apply]
  apply config_ext
  · simp [step, program, boundary, word_blank, ha]
  · simp [step, program, boundary, word_blank, ha]
    funext t
    by_cases hw : t = workTrack
    · simp [hw]
      omega
    · simp [hw]
  · simp [step, program, boundary, word_blank, ha]
    funext t z
    by_cases hw : t = workTrack
    · subst t
      simpa [Function.update_apply] using
        congrFun (word_append pre (transfer carry zeros).1) z
    · simp [hw]

theorem scan_blank_safe (source : ℤ → Symbol) (p : ℤ) (pre : List Bits)
    (previous : Bool) (carry : Carry) (ha : active carry = true) (L : ℕ)
    (hL : pre.length + 1 ≤ L) :
    ∀ t ≤ 3, Safe source p L
      (run (boundary source p pre (pre.length + 1) (.scan previous carry)) t) := by
  intro t ht
  interval_cases t
  all_goals
    simp only [run, Function.iterate_succ_apply, Function.iterate_zero_apply]
    simp [Safe, step, program, boundary, word_blank, ha, Function.update_apply,
      workTrack, sourceTrack]
    refine ⟨?_, by omega, by omega⟩
    intro t hw hs
    simp [hw, hs]

theorem safe_join (source : ℤ → Symbol) (p : ℤ) (L a b : ℕ)
    (x y : Configuration) (he : run x a = y)
    (hx : ∀ t ≤ a, Safe source p L (run x t))
    (hy : ∀ t ≤ b, Safe source p L (run y t)) :
    ∀ t ≤ b + a, Safe source p L (run x t) := by
  intro t ht
  by_cases hta : t ≤ a
  · exact hx t hta
  · rw [show t = (t - a) + a by omega, run, Function.iterate_add_apply]
    change Safe source p L (run (run x a) (t - a))
    rw [he]
    exact hy _ (by omega)

theorem scan_flush (source : ℤ → Symbol) (p : ℤ) (pre : List Bits)
    (previous : Bool) (carry : Carry) (fuel L : ℕ)
    (hstop : active (flush fuel carry).2 = false) (hL : pre.length + fuel ≤ L) :
    ∃ T : ℕ, T ≤ 3 * fuel + 1 ∧
      run (boundary source p pre (pre.length + 1) (.scan previous carry)) T =
        boundary source p (pre ++ (flush fuel carry).1)
          (pre.length + (flush fuel carry).1.length + 1) (.rewindMove previous) ∧
      ∀ t ≤ T, Safe source p L
        (run (boundary source p pre (pre.length + 1) (.scan previous carry)) t) := by
  induction fuel generalizing pre carry with
  | zero =>
    have ha : active carry = false := hstop
    refine ⟨1, by omega, ?_, ?_⟩
    · simp [flush, run, step, program, boundary, word_blank, ha]
    · intro t ht
      interval_cases t
      all_goals
        simp [Safe, run, step, program, boundary, word_blank, ha,
          workTrack, sourceTrack]
        refine ⟨?_, by omega, by omega⟩
        intro t hw hs
        simp [hw, hs]
  | succ fuel ih =>
    by_cases ha : active carry = true
    · have hstop' : active (flush fuel (transfer carry zeros).2).2 = false := by
        simpa [flush, ha] using hstop
      obtain ⟨T, hT, he, hs⟩ := ih (pre ++ [(transfer carry zeros).1])
        (transfer carry zeros).2 hstop'
        (by simp only [List.length_append, List.length_singleton]; omega)
      have hthree := scan_blank_three source p pre previous carry ha
      have hh : (pre ++ [(transfer carry zeros).1]).length = pre.length + 1 := by simp
      have he' : run (boundary source p pre (pre.length + 1)
          (.scan previous carry)) (T + 3) =
          boundary source p (pre ++ (flush (fuel + 1) carry).1)
            (pre.length + (flush (fuel + 1) carry).1.length + 1)
            (.rewindMove previous) := by
        rw [run, Function.iterate_add_apply]
        change run (run _ 3) T = _
        rw [hthree]
        simpa [flush, ha, List.append_assoc, hh, Int.add_assoc, Int.add_left_comm,
          Int.add_comm] using he
      refine ⟨T + 3, by omega, he', ?_⟩
      apply safe_join source p L 3 T _ _ hthree
      · exact scan_blank_safe source p pre previous carry ha L (by omega)
      · simpa [hh, Int.add_assoc] using hs
    · have ha' : active carry = false := by cases h : active carry <;> simp_all
      refine ⟨1, by omega, ?_, ?_⟩
      · simp [flush, run, step, program, boundary, word_blank, ha']
      · intro t ht
        interval_cases t
        all_goals
          simp [Safe, run, step, program, boundary, word_blank, ha',
            workTrack, sourceTrack]
          refine ⟨?_, by omega, by omega⟩
          intro t hw hs
          simp [hw, hs]

theorem word_get (bs : List Bits) (j : ℕ) (hj : j < bs.length) :
    word bs (j + 1) = .column bs[j] := by
  have hp : 0 < (j : ℤ) + 1 := by omega
  simp [word, ne_of_gt hp, hp, hj]

theorem rewind_two (source : ℤ → Symbol) (p : ℤ) (bs : List Bits)
    (j : ℕ) (previous : Bool) (hj : j < bs.length) :
    run (boundary source p bs (j + 1) (.rewind previous)) 2 =
      boundary source p bs j (.rewind previous) := by
  simp only [run, show 2 = 1 + 1 from rfl,
    Function.iterate_succ_apply, Function.iterate_zero_apply]
  apply config_ext
  · simp [step, program, boundary, word_get, hj]
  · simp [step, program, boundary, word_get, hj]
    funext t
    by_cases hw : t = workTrack
    · simp [hw]
    · simp [hw]
  · simp [step, program, boundary, word_get, hj]

theorem rewind_two_safe (source : ℤ → Symbol) (p : ℤ) (bs : List Bits)
    (j : ℕ) (previous : Bool) (hj : j < bs.length) (L : ℕ) (hL : j ≤ L) :
    ∀ t ≤ 2, Safe source p L
      (run (boundary source p bs (j + 1) (.rewind previous)) t) := by
  intro t ht
  interval_cases t
  all_goals
    simp only [run, Function.iterate_succ_apply, Function.iterate_zero_apply]
    simp [Safe, step, program, boundary, word_get, hj, Function.update_apply,
      workTrack, sourceTrack]
    repeat' apply And.intro
    all_goals first | (intro t hw hs; simp [hw, hs]) | omega

theorem rewind_all (source : ℤ → Symbol) (p : ℤ) (bs : List Bits)
    (j : ℕ) (previous : Bool) (hj : j ≤ bs.length) (L : ℕ) (hL : j ≤ L) :
    run (boundary source p bs j (.rewind previous)) (2 * j + 1) =
      boundary source p bs 0 (.sourceMove previous) ∧
    ∀ t ≤ 2 * j + 1, Safe source p L
      (run (boundary source p bs j (.rewind previous)) t) := by
  induction j with
  | zero =>
    constructor
    · simp [run, step, program, boundary, word]
    · intro t ht
      interval_cases t
      all_goals
        simp [Safe, run, step, program, boundary, word, workTrack, sourceTrack]
        repeat' apply And.intro
        all_goals first | (intro t hw hs; simp [hw, hs]) | omega
  | succ j ih =>
    have htwo := rewind_two source p bs j previous (by omega)
    obtain ⟨he, hs⟩ := ih (by omega) (by omega)
    constructor
    · rw [show 2 * (j + 1) + 1 = (2 * j + 1) + 2 by omega,
        run, Function.iterate_add_apply]
      change run (run _ 2) (2 * j + 1) = _
      simp only [Nat.cast_add, Nat.cast_one]
      rw [htwo]
      exact he
    · rw [show 2 * (j + 1) + 1 = (2 * j + 1) + 2 by omega]
      simpa only [Nat.cast_add, Nat.cast_one] using
        safe_join source p L 2 (2 * j + 1) _ _ htwo
          (rewind_two_safe source p bs j previous (by omega) L (by omega)) hs

def updated (carry : Carry) (bs : List Bits) : List Bits :=
  let scanned := sweep carry bs
  scanned.1 ++ (flush 3 scanned.2).1

theorem update_scan_return (source : ℤ → Symbol) (p : ℤ) (bs : List Bits)
    (previous : Bool) (carry : Carry) :
    ∃ T : ℕ, T ≤ 5 * bs.length + 18 ∧
      run (boundary source p bs 1 (.scan previous carry)) T =
        boundary source p (updated carry bs) 0 (.sourceMove previous) ∧
      (updated carry bs).length ≤ bs.length + 3 ∧
      ∀ t ≤ T, Safe source p (bs.length + 3)
        (run (boundary source p bs 1 (.scan previous carry)) t) := by
  let mid := (sweep carry bs).1
  let rem := (sweep carry bs).2
  let tail := (flush 3 rem).1
  have hm : mid.length = bs.length := sweep_length carry bs
  have ht : tail.length ≤ 3 := flush_length 3 rem
  have hout : updated carry bs = mid ++ tail := rfl
  have ho : (updated carry bs).length ≤ bs.length + 3 := by
    rw [hout, List.length_append, hm]
    omega
  have first := scan_prefix source p [] bs previous carry
  have firstSafe := scan_prefix_safe source p [] bs previous carry (bs.length + 3)
    (by simp)
  simp only [List.nil_append, List.length_nil, Nat.cast_zero, zero_add] at first firstSafe
  obtain ⟨t, htime, hflush, hflushSafe⟩ := scan_flush source p mid previous rem 3
    (bs.length + 3) (flush_three_inactive rem) (by omega)
  have flushEnd :
      run (boundary source p mid (bs.length + 1) (.scan previous rem)) t =
        boundary source p (updated carry bs) ((updated carry bs).length + 1)
          (.rewindMove previous) := by
    simpa only [hout, List.length_append, Nat.cast_add, hm] using hflush
  have flushSafe : ∀ n ≤ t, Safe source p (bs.length + 3)
      (run (boundary source p mid (bs.length + 1) (.scan previous rem)) n) := by
    simpa only [hm] using hflushSafe
  let out := updated carry bs
  have turn :
      run (boundary source p out (out.length + 1) (.rewindMove previous)) 1 =
        boundary source p out out.length (.rewind previous) := by
    apply config_ext
    · rfl
    · funext k
      simp [run, step, program, boundary, Function.update_apply]
      by_cases hk : k = workTrack <;> simp [hk]
    · rfl
  have turnSafe : ∀ n ≤ 1, Safe source p (bs.length + 3)
      (run (boundary source p out (out.length + 1) (.rewindMove previous)) n) := by
    intro n hn
    interval_cases n
    all_goals
      simp [Safe, run, step, program, boundary, Function.update_apply,
        workTrack, sourceTrack]
      repeat' apply And.intro
      all_goals first | (intro k hw hs; simp [hw, hs]) | (dsimp [out] at *; omega)
  obtain ⟨rewindEnd, rewindSafe⟩ := rewind_all source p out out.length previous
    (by rfl) (bs.length + 3) ho
  let T := (2 * out.length + 1) + (1 + (t + 3 * bs.length))
  refine ⟨T, by dsimp [T, out]; omega, ?_, ho, ?_⟩
  · dsimp [T]
    simp only [run, Function.iterate_add_apply]
    change run (run (run (run _ (3 * bs.length)) t) 1) (2 * out.length + 1) = _
    rw [first, flushEnd, turn]
    exact rewindEnd
  · have s1 := safe_join source p (bs.length + 3) (3 * bs.length) t
      _ _ first firstSafe flushSafe
    have e1 : run (boundary source p bs 1 (.scan previous carry))
        (t + 3 * bs.length) =
        boundary source p out (out.length + 1) (.rewindMove previous) := by
      rw [run, Function.iterate_add_apply]
      change run (run _ (3 * bs.length)) t = _
      rw [first]
      exact flushEnd
    have s2 := safe_join source p (bs.length + 3) (t + 3 * bs.length) 1
      _ _ e1 s1 turnSafe
    have e2 : run (boundary source p bs 1 (.scan previous carry))
        (1 + (t + 3 * bs.length)) =
        boundary source p out out.length (.rewind previous) := by
      rw [run, Function.iterate_add_apply]
      change run (run _ (t + 3 * bs.length)) 1 = _
      rw [e1]
      exact turn
    exact safe_join source p (bs.length + 3) (1 + (t + 3 * bs.length))
      (2 * out.length + 1) _ _ e2 s2 rewindSafe



end PhysicalWindowContinuation
