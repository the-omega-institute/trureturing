/- GID: D5/S0/Computability/BinaryMachine/StackEncoding
   generality: G
   mirror-B: D5/B/S0/Computability/BinaryMachine/StackEncoding
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Licensed finite binary machine StackEncoding supply. -/

module

/-
Licensed content port from RBarish-UTokyo/NPCompleteness-Lean4,
immutable revision 3e603e795b44fedcf7d6dd65b7d1e30547ead925, Complexity/StackEncoding.lean.
Apache-2.0; full license and finite replacement contract:
docs/reports/licenses/RBarishBinaryMachine.md and RBarishBinaryMachine-LICENSE.txt.
Only module imports and this repository header are adapted.
-/

public import D5.S0.Computability.BinaryMachine.StackCompiler
import Lean.Elab.Tactic.Omega

@[expose] public section
namespace Complexity.StackEncoding
open StackCompiler
open StackMachine (Registers)

def registersList {stacks : Nat} (r : Registers stacks) := List.ofFn r

def before {stacks : Nat} (r : Registers stacks) (k : Fin (stacks + 1)) :=
  (registersList r).take k.val

def after {stacks : Nat} (r : Registers stacks) (k : Fin (stacks + 1)) :=
  (registersList r).drop (k.val + 1)

def tail {stacks : Nat} (r : Registers stacks) (k : Fin (stacks + 1)) :=
  stackPrefix (after r k) ++ [.sep]

def suffix {stacks : Nat} (r : Registers stacks) (k : Fin (stacks + 1)) :=
  (r k).map Symbol.bit ++ tail r k

def encodeRegisters {stacks : Nat} (r : Registers stacks) :=
  stackPrefix (registersList r) ++ [.sep]

def homeTape {stacks : Nat} (r : Registers stacks) : Tape :=
  ⟨[.blank], encodeRegisters r⟩

@[simp] theorem registersList_length {stacks : Nat} (r : Registers stacks) :
    (registersList r).length = stacks + 1 := by simp [registersList]

@[simp] theorem before_length {stacks : Nat} (r : Registers stacks)
    (k : Fin (stacks + 1)) : (before r k).length = k.val := by
  simp [before, Nat.min_eq_left (Nat.le_of_lt k.isLt)]

theorem registersList_split {stacks : Nat} (r : Registers stacks)
    (k : Fin (stacks + 1)) :
    registersList r = before r k ++ r k :: after r k := by
  have hk : k.val < (registersList r).length := by simp
  have he : (registersList r)[k.val]'hk = r k := by
    exact List.getElem_ofFn hk
  change registersList r = (registersList r).take k.val ++ r k ::
    (registersList r).drop (k.val + 1)
  rw [← he, List.getElem_cons_drop]
  exact (List.take_append_drop _ _).symm

theorem registersList_set {stacks : Nat} (r : Registers stacks)
    (k : Fin (stacks + 1)) (value : List Bool) :
    registersList (StackMachine.set r k value) = (registersList r).set k.val value := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [registersList, List.getElem_ofFn, List.getElem_set, StackMachine.set]
    split <;> rename_i h
    · have hv : i = k.val := congrArg Fin.val h
      simp [hv]
    · have hv : k.val ≠ i := by
        intro he
        apply h
        exact Fin.ext he.symm
      simp [hv]

@[simp] theorem before_set {stacks : Nat} (r : Registers stacks)
    (k : Fin (stacks + 1)) (value : List Bool) :
    before (StackMachine.set r k value) k = before r k := by
  simp only [before, registersList_set, List.take_set]
  apply List.set_eq_of_length_le
  simp

@[simp] theorem after_set {stacks : Nat} (r : Registers stacks)
    (k : Fin (stacks + 1)) (value : List Bool) :
    after (StackMachine.set r k value) k = after r k := by
  simp [after, registersList_set, List.drop_set]

theorem stackPrefix_append (xs ys : List (List Bool)) :
    stackPrefix (xs ++ ys) = stackPrefix xs ++ stackPrefix ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [stackPrefix, ih, List.append_assoc]

theorem encodeRegisters_split {stacks : Nat} (r : Registers stacks)
    (k : Fin (stacks + 1)) :
    encodeRegisters r = stackPrefix (before r k) ++ .sep :: suffix r k := by
  unfold encodeRegisters
  rw [registersList_split r k, stackPrefix_append]
  simp [stackPrefix, suffix, tail, List.append_assoc]

theorem encodeRegisters_set {stacks : Nat} (r : Registers stacks)
    (k : Fin (stacks + 1)) (value : List Bool) :
    encodeRegisters (StackMachine.set r k value) =
      stackPrefix (before r k) ++ .sep :: (value.map Symbol.bit ++ tail r k) := by
  rw [encodeRegisters_split _ k]
  simp [suffix, tail]

@[simp] theorem tail_ne_nil {stacks : Nat} (r : Registers stacks)
    (k : Fin (stacks + 1)) : tail r k ≠ [] := by simp [tail]

@[simp] theorem suffix_ne_nil {stacks : Nat} (r : Registers stacks)
    (k : Fin (stacks + 1)) : suffix r k ≠ [] := by simp [suffix]

theorem tail_nonblank {stacks : Nat} (r : Registers stacks)
    (k : Fin (stacks + 1)) : ∀ a ∈ tail r k, a ≠ .blank := by
  intro a ha
  simp only [tail, List.mem_append, List.mem_singleton] at ha
  rcases ha with ha | rfl
  · exact stackPrefix_nonblank _ a ha
  · decide

theorem suffix_nonblank {stacks : Nat} (r : Registers stacks)
    (k : Fin (stacks + 1)) : ∀ a ∈ suffix r k, a ≠ .blank := by
  intro a ha
  simp only [suffix, List.mem_append, List.mem_map] at ha
  rcases ha with ⟨b, _, rfl⟩ | ha
  · simp
  · exact tail_nonblank r k a ha

theorem encodeRegisters_nonblank {stacks : Nat} (r : Registers stacks) :
    ∀ a ∈ encodeRegisters r, a ≠ .blank := by
  intro a ha
  simp only [encodeRegisters, List.mem_append, List.mem_singleton] at ha
  rcases ha with ha | rfl
  · exact stackPrefix_nonblank _ a ha
  · decide

@[simp] theorem encodeRegisters_ne_nil {stacks : Nat} (r : Registers stacks) :
    encodeRegisters r ≠ [] := by simp [encodeRegisters]

@[simp] theorem homeTape_read {stacks : Nat} (r : Registers stacks) :
    (homeTape r).read = .sep := by
  simp [homeTape, encodeRegisters, registersList, List.ofFn_succ, stackPrefix, Tape.read]

theorem stackPrefix_length_le (xs : List (List Bool)) (bound : Nat)
    (hb : ∀ x ∈ xs, x.length ≤ bound) :
    (stackPrefix xs).length ≤ xs.length * (bound + 1) := by
  induction xs with
  | nil => simp [stackPrefix]
  | cons x xs ih =>
    have hx := hb x (by simp)
    have hr := ih (fun y hy => hb y (by simp [hy]))
    simp only [stackPrefix, List.length_cons, List.length_append, List.length_map]
    rw [Nat.add_mul, Nat.one_mul]
    omega

theorem encodeRegisters_length_le {stacks : Nat} (r : Registers stacks) (bound : Nat)
    (hb : ∀ k, (r k).length ≤ bound) :
    (encodeRegisters r).length ≤ (stacks + 1) * (bound + 1) + 1 := by
  have h := stackPrefix_length_le (registersList r) bound (by
    intro x hx
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hx
    exact hb k)
  simpa [encodeRegisters] using Nat.add_le_add_right h 1

theorem bits_map_append_sep (bits : List Bool) (right : List Symbol) :
    Tape.bits (bits.map Symbol.bit ++ .sep :: right) = bits := by
  induction bits with
  | nil => rfl
  | cons b rest ih => simp [Tape.bits, ih]

theorem stackPrefix_append_sep_starts (xs : List (List Bool)) :
    ∃ rest, stackPrefix xs ++ [.sep] = .sep :: rest := by
  cases xs with
  | nil => exact ⟨[], rfl⟩
  | cons x xs => exact ⟨x.map Symbol.bit ++ (stackPrefix xs ++ [.sep]), by simp [stackPrefix]⟩

theorem tail_eq_cons {stacks : Nat} (r : Registers stacks)
    (k : Fin (stacks + 1)) : ∃ rest, tail r k = .sep :: rest :=
  stackPrefix_append_sep_starts (after r k)

@[simp] theorem tail_head {stacks : Nat} (r : Registers stacks)
    (k : Fin (stacks + 1)) : (tail r k).headD .blank = .sep := by
  obtain ⟨rest, hr⟩ := tail_eq_cons r k
  simp [hr]

@[simp] theorem output_move_right {stacks : Nat} (r : Registers stacks) :
    ((homeTape r).move .right).output = r 0 := by
  have hs := stackPrefix_append_sep_starts (List.ofFn (fun i : Fin stacks => r i.succ))
  obtain ⟨rest, hr⟩ := hs
  simp only [homeTape, encodeRegisters, registersList, List.ofFn_succ, stackPrefix,
    List.cons_append, List.append_assoc, Tape.move, Tape.output]
  rw [hr, bits_map_append_sep]


theorem stackPrefix_empty_ofFn (n : Nat) :
    stackPrefix (List.ofFn (fun _ : Fin n => ([] : List Bool))) =
      List.replicate n .sep := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.ofFn_succ, stackPrefix, ih, List.replicate_succ]

theorem encodeRegisters_initial (stacks : Nat) (input : List Bool) :
    encodeRegisters (fun j : Fin (stacks + 1) => if j = 0 then input else []) =
      .sep :: (input.map Symbol.bit ++ List.replicate (stacks + 1) .sep) := by
  simp only [encodeRegisters, registersList, List.ofFn_succ, ↓reduceIte,
    Fin.succ_ne_zero, stackPrefix, List.cons_append, List.append_assoc]
  rw [stackPrefix_empty_ofFn, ← List.replicate_succ']

theorem homeTape_initial (M : StackMachine.Machine) (input : List Bool) :
    homeTape (StackMachine.initial M input).registers =
      ⟨[.blank], .sep :: (input.map Symbol.bit ++ List.replicate (M.stacks + 1) .sep)⟩ := by
  simp only [homeTape, StackMachine.initial, encodeRegisters_initial]

end Complexity.StackEncoding
