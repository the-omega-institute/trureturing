/- GID: D5/S0/Computability/BinaryMachine/StackWords
   generality: G
   mirror-B: D5/B/S0/Computability/BinaryMachine/StackWords
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Licensed finite binary machine StackWords supply. -/

module

/-
Licensed content port from RBarish-UTokyo/NPCompleteness-Lean4,
immutable revision 3e603e795b44fedcf7d6dd65b7d1e30547ead925, Complexity/StackWords.lean.
Apache-2.0; full license and finite replacement contract:
docs/reports/licenses/RBarishBinaryMachine.md and RBarishBinaryMachine-LICENSE.txt.
Only module imports and this repository header are adapted.
-/

public import D5.S0.Computability.BinaryMachine.StackProgram
import Lean.Elab.Tactic.Omega

/-!
# Verified word operations built from individual stack instructions

All programs in this file have explicit finite control.  Execution theorems
give the complete final register function, so untouched registers are preserved.
-/

@[expose] public section

namespace Complexity.StackWords

open Complexity.StackMachine (Registers branch)
open Complexity.StackProgram

@[simp] theorem set_overwrite {k : Nat} (r : Registers k) (j : Fin (k + 1))
    (xs ys : List Bool) : StackMachine.set (StackMachine.set r j xs) j ys = StackMachine.set r j ys := by
  funext a
  by_cases ha : a = j <;> simp [StackMachine.set, ha]

@[simp] theorem set_unchanged {k : Nat} (r : Registers k) (j : Fin (k + 1)) :
    StackMachine.set r j (r j) = r := by
  funext a
  by_cases ha : a = j
  · subst a; simp
  · simp [StackMachine.set, ha]

/-- Empty a register: one pop per bit, an empty pop, then halt. -/
def clear {k : Nat} (j : Fin (k + 1)) : Program k Bool where
  start := false
  code := fun q => if q then .halt true else .pop j true false false

theorem exec_clear_aux {k : Nat} (j : Fin (k + 1)) (xs : List Bool)
    (r : Registers k) (hr : r j = xs) :
    Exec (clear j) false r (xs.length + 2) (true, StackMachine.set r j []) := by
  induction xs generalizing r with
  | nil =>
    apply Exec.next (q' := true) (r' := StackMachine.set r j [])
    · simp [StackProgram.step, clear, hr, branch]
    · exact .halt rfl
  | cons b xs ih =>
    have ht := ih (StackMachine.set r j xs) (by simp)
    have hs : StackProgram.step (clear j) false r = .inr (false, StackMachine.set r j xs) := by
      cases b <;> simp [StackProgram.step, clear, hr, branch]
    have hh := Exec.next hs ht
    simpa [set_overwrite, Nat.add_assoc] using hh

theorem exec_clear {k : Nat} (j : Fin (k + 1)) (r : Registers k) :
    Exec (clear j) false r ((r j).length + 2) (true, StackMachine.set r j []) :=
  exec_clear_aux j (r j) r rfl

/-- Pop each source bit and push it to the destination. -/
def transfer {k : Nat} (src dst : Fin (k + 1)) : Program k (Fin 4) where
  start := 0
  code := fun q => if q = 0 then .pop src 1 2 3
    else if q = 1 then .halt true
    else if q = 2 then .push dst false 0
    else .push dst true 0

theorem transfer_registers {k : Nat} (src dst : Fin (k + 1)) (_hne : src ≠ dst)
    (r : Registers k) (b : Bool) (xs : List Bool) :
    StackMachine.set (StackMachine.set (StackMachine.set (StackMachine.set r src xs) dst (b :: r dst)) src []) dst
      (xs.reverse ++ (StackMachine.set (StackMachine.set r src xs) dst (b :: r dst)) dst) =
      StackMachine.set (StackMachine.set r src []) dst ((b :: xs).reverse ++ r dst) := by
  funext a
  by_cases hd : a = dst
  · subst a
    simp [List.reverse_cons, List.append_assoc]
  · by_cases hs : a = src
    · subst a; simp [hd]
    · simp [StackMachine.set, hd, hs]

theorem exec_transfer_aux {k : Nat} (src dst : Fin (k + 1)) (hne : src ≠ dst)
    (xs : List Bool) (r : Registers k) (hr : r src = xs) :
    Exec (transfer src dst) 0 r (2 * xs.length + 2)
      (true, StackMachine.set (StackMachine.set r src []) dst (xs.reverse ++ r dst)) := by
  induction xs generalizing r with
  | nil =>
    have heq : StackMachine.set (StackMachine.set r src []) dst (r dst) = StackMachine.set r src [] := by
      have hh : (StackMachine.set r src []) dst = r dst := by simp [Ne.symm hne]
      rw [← hh, set_unchanged]
    simp only [List.length_nil, Nat.mul_zero, Nat.zero_add,
      List.reverse_nil, List.nil_append, heq]
    apply Exec.next (q' := 1) (r' := StackMachine.set r src [])
    · simp [StackProgram.step, transfer, hr, branch]
    · exact .halt (by simp [StackProgram.step, transfer])
  | cons b xs ih =>
    let r' := StackMachine.set (StackMachine.set r src xs) dst (b :: r dst)
    have hr' : r' src = xs := by simp [r', hne]
    have ht := ih r' hr'
    have hpop : StackProgram.step (transfer src dst) 0 r =
        .inr ((if b then 3 else 2), StackMachine.set r src xs) := by
      cases b <;> simp [StackProgram.step, transfer, hr, branch]
    have hpush : StackProgram.step (transfer src dst) (if b then 3 else 2) (StackMachine.set r src xs) =
        .inr (0, r') := by
      cases b <;> simp [StackProgram.step, transfer, r', Ne.symm hne]
    have hh := Exec.next hpop (Exec.next hpush ht)
    have hout := transfer_registers src dst hne r b xs
    change StackMachine.set (StackMachine.set r' src []) dst (xs.reverse ++ r' dst) = _ at hout
    rw [hout] at hh
    simpa [Nat.mul_add, Nat.add_assoc] using hh

theorem exec_transfer {k : Nat} (src dst : Fin (k + 1)) (hne : src ≠ dst)
    (r : Registers k) :
    Exec (transfer src dst) 0 r (2 * (r src).length + 2)
      (true, StackMachine.set (StackMachine.set r src []) dst ((r src).reverse ++ r dst)) :=
  exec_transfer_aux src dst hne (r src) r rfl

theorem transfer_frame {k : Nat} (src dst a : Fin (k + 1))
    (hs : a ≠ src) (hd : a ≠ dst) (r : Registers k) :
    StackMachine.set (StackMachine.set r src []) dst ((r src).reverse ++ r dst) a = r a := by
  simp [hs, hd]

/-- A static mapping used only to choose the literal bit in each push instruction. -/
def mapBit (zero one b : Bool) : Bool := if b then one else zero

/-- Reverse-transfer to two destinations.  The second push has two fixed bit values. -/
def scatter {k : Nat} (src first second : Fin (k + 1)) (zero one : Bool) :
    Program k (Fin 6) where
  start := 0
  code := fun q => if q = 0 then .pop src 1 2 4
    else if q = 1 then .halt true
    else if q = 2 then .push first false 3
    else if q = 3 then .push second zero 0
    else if q = 4 then .push first true 5
    else .push second one 0

theorem scatter_registers {k : Nat} (src first second : Fin (k + 1))
    (_hsf : src ≠ first) (_hss : src ≠ second) (_hfs : first ≠ second)
    (zero one : Bool) (r : Registers k) (b : Bool) (xs : List Bool) :
    let r' := StackMachine.set (StackMachine.set (StackMachine.set r src xs) first (b :: r first)) second
      (mapBit zero one b :: r second)
    StackMachine.set (StackMachine.set (StackMachine.set r' src []) first (xs.reverse ++ r' first)) second
      (xs.reverse.map (mapBit zero one) ++ r' second) =
      StackMachine.set (StackMachine.set (StackMachine.set r src []) first ((b :: xs).reverse ++ r first)) second
        ((b :: xs).reverse.map (mapBit zero one) ++ r second) := by
  dsimp only
  funext a
  by_cases hsecond : a = second
  · subst a
    simp [List.reverse_cons, List.map_append, List.append_assoc]
  · by_cases hfirst : a = first
    · subst a
      simp [hsecond, List.reverse_cons, List.append_assoc]
    · by_cases hsrc : a = src
      · subst a
        simp [hsecond, hfirst]
      · simp [StackMachine.set, hsecond, hfirst, hsrc]

theorem exec_scatter_aux {k : Nat} (src first second : Fin (k + 1))
    (hsf : src ≠ first) (hss : src ≠ second) (hfs : first ≠ second)
    (zero one : Bool) (xs : List Bool) (r : Registers k) (hr : r src = xs) :
    Exec (scatter src first second zero one) 0 r (3 * xs.length + 2)
      (true, StackMachine.set (StackMachine.set (StackMachine.set r src []) first (xs.reverse ++ r first)) second
        (xs.reverse.map (mapBit zero one) ++ r second)) := by
  induction xs generalizing r with
  | nil =>
    have heq : StackMachine.set (StackMachine.set (StackMachine.set r src []) first (r first)) second (r second) = StackMachine.set r src [] := by
      funext a
      by_cases hs : a = src
      · subst a; simp [hsf, hss]
      · by_cases hf : a = first
        · subst a; simp [Ne.symm hsf, hfs]
        · by_cases ht : a = second
          · subst a; simp [Ne.symm hss]
          · simp [StackMachine.set, hs, hf, ht]
    simp only [List.length_nil, Nat.mul_zero, Nat.zero_add, List.reverse_nil,
      List.map_nil, List.nil_append, heq]
    apply Exec.next (q' := 1) (r' := StackMachine.set r src [])
    · simp [StackProgram.step, scatter, hr, branch]
    · exact .halt (by simp [StackProgram.step, scatter])
  | cons b xs ih =>
    let r' := StackMachine.set (StackMachine.set (StackMachine.set r src xs) first (b :: r first)) second
      (mapBit zero one b :: r second)
    have hr' : r' src = xs := by simp [r', hsf, hss]
    have ht := ih r' hr'
    have hpop : StackProgram.step (scatter src first second zero one) 0 r =
        .inr ((if b then 4 else 2), StackMachine.set r src xs) := by
      cases b <;> simp [StackProgram.step, scatter, hr, branch]
    have hfirst : StackProgram.step (scatter src first second zero one) (if b then 4 else 2) (StackMachine.set r src xs) =
        .inr ((if b then 5 else 3), StackMachine.set (StackMachine.set r src xs) first (b :: r first)) := by
      cases b <;> simp [StackProgram.step, scatter, Ne.symm hsf]
    have hsecond : StackProgram.step (scatter src first second zero one) (if b then 5 else 3)
        (StackMachine.set (StackMachine.set r src xs) first (b :: r first)) = .inr (0, r') := by
      cases b <;> simp [StackProgram.step, scatter, r', mapBit, Ne.symm hss, Ne.symm hfs]
    have hh := Exec.next hpop (Exec.next hfirst (Exec.next hsecond ht))
    have hout := scatter_registers src first second hsf hss hfs zero one r b xs
    change StackMachine.set (StackMachine.set (StackMachine.set r' src []) first (xs.reverse ++ r' first)) second
      (xs.reverse.map (mapBit zero one) ++ r' second) = _ at hout
    rw [hout] at hh
    simpa [Nat.mul_add, Nat.add_assoc] using hh

theorem exec_scatter {k : Nat} (src first second : Fin (k + 1))
    (hsf : src ≠ first) (hss : src ≠ second) (hfs : first ≠ second)
    (zero one : Bool) (r : Registers k) :
    Exec (scatter src first second zero one) 0 r (3 * (r src).length + 2)
      (true, StackMachine.set (StackMachine.set (StackMachine.set r src []) first ((r src).reverse ++ r first)) second
        ((r src).reverse.map (mapBit zero one) ++ r second)) :=
  exec_scatter_aux src first second hsf hss hfs zero one (r src) r rfl

/-- Preserve the source while overwriting the destination with a fixed bitwise mapping. -/
def copyMap {k : Nat} (src dst scratch : Fin (k + 1)) (zero one : Bool) :
    Program k (Sum Bool (Sum (Fin 4) (Fin 6))) :=
  seq (clear dst) (seq (transfer src scratch) (scatter scratch src dst zero one))

def copyMapEncoding : Encoding (Sum Bool (Sum (Fin 4) (Fin 6))) :=
  Encoding.bool.sum ((Encoding.fin 3).sum (Encoding.fin 5))

/-- Scratch starts empty and is restored empty; every register except `dst` is preserved. -/
theorem exec_copyMap {k : Nat} (src dst scratch : Fin (k + 1))
    (hsd : src ≠ dst) (hst : src ≠ scratch) (hdt : dst ≠ scratch)
    (zero one : Bool) (r : Registers k) (hempty : r scratch = []) :
    Exec (copyMap src dst scratch zero one) (.inl false) r
      ((r dst).length + 5 * (r src).length + 6)
      (true, StackMachine.set r dst ((r src).map (mapBit zero one))) := by
  let r₀ := StackMachine.set r dst []
  let r₁ := StackMachine.set (StackMachine.set r₀ src []) scratch ((r₀ src).reverse ++ r₀ scratch)
  let r₂ := StackMachine.set (StackMachine.set (StackMachine.set r₁ scratch []) src
    ((r₁ scratch).reverse ++ r₁ src)) dst
      ((r₁ scratch).reverse.map (mapBit zero one) ++ r₁ dst)
  have hclear : Exec (clear dst) false r ((r dst).length + 2) (true, r₀) := exec_clear dst r
  have htransfer : Exec (transfer src scratch) 0 r₀ (2 * (r₀ src).length + 2) (true, r₁) :=
    exec_transfer src scratch hst r₀
  have hscatter : Exec (scatter scratch src dst zero one) 0 r₁
      (3 * (r₁ scratch).length + 2) (true, r₂) :=
    exec_scatter scratch src dst (Ne.symm hst) (Ne.symm hdt) hsd zero one r₁
  have hseq := exec_seq (clear dst)
    (seq (transfer src scratch) (scatter scratch src dst zero one)) hclear
    (exec_seq (transfer src scratch) (scatter scratch src dst zero one) htransfer hscatter)
  have hout : r₂ = StackMachine.set r dst ((r src).map (mapBit zero one)) := by
    funext a
    by_cases hd : a = dst
    · subst a
      simp [r₂, r₁, r₀, hsd, hst, hdt, Ne.symm hsd, Ne.symm hdt, hempty]
    · by_cases hs : a = src
      · subst a
        simp [r₂, r₁, r₀, hd, hst, Ne.symm hdt, hempty]
      · by_cases ht : a = scratch
        · subst a
          simp [r₂, hd, hs, hempty]
        · simp [r₂, r₁, r₀, StackMachine.set, hd, hs, ht]
  have hcost : (r dst).length + 2 +
      (2 * (r₀ src).length + 2 + (3 * (r₁ scratch).length + 2)) =
      (r dst).length + 5 * (r src).length + 6 := by
    simp [r₁, r₀, hsd, Ne.symm hdt, hempty]
    omega
  rw [hout, hcost] at hseq
  exact hseq

@[simp] theorem mapBit_identity (b : Bool) : mapBit false true b = b := by
  cases b <;> rfl

@[simp] theorem mapBit_constant (b : Bool) : mapBit true true b = true := by
  cases b <;> rfl

theorem map_identity (xs : List Bool) : xs.map (mapBit false true) = xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simp [ih]

theorem map_ones (xs : List Bool) :
    xs.map (mapBit true true) = List.replicate xs.length true := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simp [ih, List.replicate_succ]

def copy {k : Nat} (src dst scratch : Fin (k + 1)) := copyMap src dst scratch false true

theorem exec_copy {k : Nat} (src dst scratch : Fin (k + 1))
    (hsd : src ≠ dst) (hst : src ≠ scratch) (hdt : dst ≠ scratch)
    (r : Registers k) (hempty : r scratch = []) :
    Exec (copy src dst scratch) (.inl false) r
      ((r dst).length + 5 * (r src).length + 6) (true, StackMachine.set r dst (r src)) := by
  simpa [copy, map_identity] using exec_copyMap src dst scratch hsd hst hdt false true r hempty

/-- Write source length as a unary counter, preserving source and scratch. -/
def length {k : Nat} (src dst scratch : Fin (k + 1)) := copyMap src dst scratch true true

theorem exec_length {k : Nat} (src dst scratch : Fin (k + 1))
    (hsd : src ≠ dst) (hst : src ≠ scratch) (hdt : dst ≠ scratch)
    (r : Registers k) (hempty : r scratch = []) :
    Exec (length src dst scratch) (.inl false) r
      ((r dst).length + 5 * (r src).length + 6)
      (true, StackMachine.set r dst (List.replicate (r src).length true)) := by
  simpa [length, map_ones] using exec_copyMap src dst scratch hsd hst hdt true true r hempty

/-- The unary increment program is a literal one-bit push followed by halt. -/
def increment {k : Nat} (j : Fin (k + 1)) := push j true

theorem exec_increment {k : Nat} (j : Fin (k + 1)) (r : Registers k) (n : Nat)
    (hr : r j = List.replicate n true) :
    Exec (increment j) false r 2 (true, StackMachine.set r j (List.replicate (n + 1) true)) := by
  simpa [increment, hr, List.replicate_succ] using exec_push j true r

/-- Unary decrement saturates at zero. -/
def decrement {k : Nat} (j : Fin (k + 1)) := pop j

theorem exec_decrement {k : Nat} (j : Fin (k + 1)) (r : Registers k) (n : Nat)
    (hr : r j = List.replicate n true) :
    Exec (decrement j) false r 2 (true, StackMachine.set r j (List.replicate (n - 1) true)) := by
  have htail : (List.replicate n true).tail = List.replicate (n - 1) true := by
    cases n <;> simp [List.replicate_succ]
  simpa [decrement, hr, htail] using exec_pop j r

theorem copy_frame {k : Nat} (src dst a : Fin (k + 1)) (h : a ≠ dst) (r : Registers k) :
    StackMachine.set r dst (r src) a = r a := by simp [h]

theorem length_frame {k : Nat} (src dst a : Fin (k + 1)) (h : a ≠ dst) (r : Registers k) :
    StackMachine.set r dst (List.replicate (r src).length true) a = r a := by simp [h]

/-- The compiled clear program executes in the proved exact number of stack instructions. -/
theorem compiled_clear_runs {k : Nat} (j : Fin (k + 1)) (r : Registers k) :
    StackMachine.run (compile (clear j) Encoding.bool) ((r j).length + 2)
      ⟨0, r⟩ = some (true, StackMachine.set r j []) :=
  compile_exec Encoding.bool (exec_clear j r)

theorem compiled_transfer_runs {k : Nat} (src dst : Fin (k + 1)) (hne : src ≠ dst)
    (r : Registers k) (bound : Nat) (hb : (r src).length ≤ bound) :
    StackMachine.run (compile (transfer src dst) (Encoding.fin 3)) (2 * bound + 2)
      ⟨0, r⟩ = some (true, StackMachine.set (StackMachine.set r src []) dst
        ((r src).reverse ++ r dst)) := by
  apply StackMachine.run_mono _ (fuel := 2 * (r src).length + 2) (by omega)
  exact compile_exec (Encoding.fin 3) (exec_transfer src dst hne r)

/-- A linear stack-machine time bound for a preserving copy. -/
theorem compiled_copy_runs {k : Nat} (src dst scratch : Fin (k + 1))
    (hsd : src ≠ dst) (hst : src ≠ scratch) (hdt : dst ≠ scratch)
    (r : Registers k) (hempty : r scratch = []) (bound : Nat)
    (hs : (r src).length ≤ bound) (hd : (r dst).length ≤ bound) :
    StackMachine.run (compile (copy src dst scratch) copyMapEncoding) (6 * bound + 6)
      ⟨(compile (copy src dst scratch) copyMapEncoding).start, r⟩ =
        some (true, StackMachine.set r dst (r src)) := by
  apply StackMachine.run_mono _ (fuel := (r dst).length + 5 * (r src).length + 6) (by omega)
  exact compile_exec copyMapEncoding (exec_copy src dst scratch hsd hst hdt r hempty)

/-- A linear stack-machine time bound for a preserving unary length computation. -/
theorem compiled_length_runs {k : Nat} (src dst scratch : Fin (k + 1))
    (hsd : src ≠ dst) (hst : src ≠ scratch) (hdt : dst ≠ scratch)
    (r : Registers k) (hempty : r scratch = []) (bound : Nat)
    (hs : (r src).length ≤ bound) (hd : (r dst).length ≤ bound) :
    StackMachine.run (compile (length src dst scratch) copyMapEncoding) (6 * bound + 6)
      ⟨(compile (length src dst scratch) copyMapEncoding).start, r⟩ =
        some (true, StackMachine.set r dst (List.replicate (r src).length true)) := by
  apply StackMachine.run_mono _ (fuel := (r dst).length + 5 * (r src).length + 6) (by omega)
  exact compile_exec copyMapEncoding (exec_length src dst scratch hsd hst hdt r hempty)

end Complexity.StackWords
