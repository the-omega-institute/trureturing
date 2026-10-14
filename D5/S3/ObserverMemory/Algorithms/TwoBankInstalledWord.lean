/- GID: D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/TwoBankInstalledWord
   mirror-E: none(waiver:unbounded-symbolic-execution)
   anchors: []
   utility: none
   digest: A total two-bank installation routes native replies by paid single-bit writes. -/

import D5.S3.ObserverMemory.Algorithms.NativeExecutionTransport
import D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Finset.Sort

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ObserverMemory.Algorithms.TwoBankInstalledWord

/- This is a symbolic construction for arbitrary bank width and source table.
It does not enumerate bounded instances, certify a numerical instance, or expose
a decision checker, so its utility classification is none. -/

open scoped symmDiff

abbrev Bank (k : Nat) := Finset (Fin k)
abbrev Flag := Fin 5
abbrev Address := List Bool

/-- The five flag indices are alpha, beta, branch, absent, and acknowledgement. -/
inductive Opcode where
  | read (address : Address)
  | update
  | halt (output : Bool)
  deriving DecidableEq

def Typed : Opcode → Flag → Prop
  | .read _, r => r.val < 4
  | .update, r => r = 4
  | .halt _, _ => False

instance (i : Opcode) (r : Flag) : Decidable (Typed i r) := by
  cases i <;> unfold Typed <;> infer_instance

/-- All bit patterns are present, including unsupported flag/phase combinations.
The phase indices run through 000,001,011,010,110,111,101,100. -/
structure Word (k : Nat) where
  a : Bank k
  b : Bank k
  flags : Finset Flag
  phase : Fin 8
  deriving DecidableEq

/-- Fixed finite source instructions and their typed successor controls. -/
structure Table (k : Nat) where
  instruction : Bank k → Opcode
  delta : Bank k → Flag → Bank k

variable {k : Nat}

/-- Select the least differing bit in the fixed order and flip it. -/
def toward (a t : Bank k) : Bank k :=
  if h : (a ∆ t).Nonempty then a ∆ {(a ∆ t).min' h} else a

private theorem toward_distance (a t : Bank k) (h : a ≠ t) :
    (toward a t ∆ t).card + 1 = (a ∆ t).card := by
  have hn : (a ∆ t).Nonempty := Finset.symmDiff_nonempty.mpr h
  let j := (a ∆ t).min' hn
  have hj : j ∈ a ∆ t := Finset.min'_mem _ _
  have he : (a ∆ {j}) ∆ t = (a ∆ t).erase j := by
    ext i
    simp only [Finset.mem_symmDiff, Finset.mem_singleton, Finset.mem_erase]
    by_cases hi : i = j
    · subst i
      simp only [Finset.mem_symmDiff] at hj
      tauto
    · tauto
  rw [toward, dif_pos hn]
  change (a ∆ {j} ∆ t).card + 1 = _
  rw [he]
  exact Finset.card_erase_add_one hj

private theorem toward_flip (a t : Bank k) (h : a ≠ t) :
    ∃ j : Fin k, toward a t = a ∆ {j} := by
  have hn : (a ∆ t).Nonempty := Finset.symmDiff_nonempty.mpr h
  exact ⟨(a ∆ t).min' hn, dif_pos hn⟩

/-- Recognize exactly the singleton flag patterns. -/
def singleFlag (f : Finset Flag) : Option Flag :=
  if h : f.Nonempty then
    if f = {f.min' h} then some (f.min' h) else none
  else none

private theorem singleFlag_singleton (r : Flag) : singleFlag {r} = some r := by
  simp [singleFlag]

private theorem singleFlag_empty : singleFlag ∅ = none := by
  simp [singleFlag]

private theorem singleFlag_spec {f : Finset Flag} {r : Flag}
    (h : singleFlag f = some r) : f = {r} := by
  unfold singleFlag at h
  split at h
  · split at h
    · simp only [Option.some.injEq] at h
      subst r
      assumption
    · contradiction
  · contradiction

/-- A row installs one instruction and all its immediate response choices. -/
structure Row (k : Nat) where
  instruction : Opcode
  next : Flag → Word k

private def root (w : Word k) : Row k := ⟨.read [], fun _ => w⟩

/-- The entire row table, including the hold completion on unsupported words. -/
def installed (T : Table k) (w : Word k) : Row k :=
  match w.phase.val with
  | 0 =>
      if w.flags = ∅ ∧ w.b = ∅ then
        ⟨T.instruction w.a, fun r => { w with flags := {r} }⟩
      else match singleFlag w.flags with
      | some r =>
          if Typed (T.instruction w.a) r then
            root (if w.b = T.delta w.a r then { w with phase := 1 }
              else { w with b := toward w.b (T.delta w.a r) })
          else root w
      | none => root w
  | 1 =>
      match singleFlag w.flags with
      | some _ => root (if w.a = ∅ then { w with phase := 2 }
          else { w with a := toward w.a ∅ })
      | none => root w
  | 2 =>
      if w.a = ∅ then
        match singleFlag w.flags with
        | some _ => root { w with flags := ∅ }
        | none => root (if w.flags = ∅ then { w with phase := 3 } else w)
      else root w
  | 3 =>
      if w.flags = ∅ ∧ w.a = ∅ then
        ⟨T.instruction w.b, fun r => { w with flags := {r} }⟩
      else match singleFlag w.flags with
      | some r =>
          if Typed (T.instruction w.b) r then
            root (if w.a = T.delta w.b r then { w with phase := 4 }
              else { w with a := toward w.a (T.delta w.b r) })
          else root w
      | none => root w
  | 4 =>
      match singleFlag w.flags with
      | some _ => root (if w.b = ∅ then { w with phase := 5 }
          else { w with b := toward w.b ∅ })
      | none => root w
  | 5 =>
      if w.b = ∅ then
        match singleFlag w.flags with
        | some _ => root { w with flags := ∅ }
        | none => root (if w.flags = ∅ then { w with phase := 6 } else w)
      else root w
  | 6 => root (if w.b = ∅ ∧ w.flags = ∅ then { w with phase := 7 } else w)
  | _ => root (if w.b = ∅ ∧ w.flags = ∅ then { w with phase := 0 } else w)

/-- The two ready representations of the same encoded control. -/
def ready (right : Bool) (z : Bank k) : Word k :=
  if right then ⟨∅, z, ∅, 3⟩ else ⟨z, ∅, ∅, 0⟩

/-- A charged root-read path ignores the raw reply at every routing step. -/
inductive Routing (T : Table k) : Word k → Word k → Nat → Prop where
  | refl (w : Word k) : Routing T w w 0
  | step {w v u : Word k} {n : Nat} :
      installed T w = root v → w ≠ v → Routing T v u n → Routing T w u (n + 1)

private theorem routing_trans {T : Table k} {w v u : Word k} {m n : Nat}
    (p : Routing T w v m) (q : Routing T v u n) : Routing T w u (m + n) := by
  induction p with
  | refl => simpa using q
  | step h hd _ ih =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Routing.step h hd (ih q)

private theorem routing_toward (T : Table k) (embed : Bank k → Word k)
    (a t : Bank k) (inj : Function.Injective embed)
    (hop : ∀ b, b ≠ t → installed T (embed b) = root (embed (toward b t))) :
    Routing T (embed a) (embed t) (a ∆ t).card := by
  generalize hn : (a ∆ t).card = n
  induction n using Nat.strong_induction_on generalizing a with
  | h n ih =>
      by_cases he : a = t
      · subst a
        simp only [symmDiff_self] at hn
        subst n
        exact .refl _
      · have hd := toward_distance a t he
        have suffix := ih (toward a t ∆ t).card (by omega) (toward a t) rfl
        have diff : embed a ≠ embed (toward a t) := by
          intro eq
          have same := inj eq
          rw [← same] at hd
          omega
        have path := Routing.step (hop a he) diff suffix
        simpa only [hd, hn] using path

private theorem fill_left (T : Table k) (z b : Bank k) (r : Flag)
    (typed : Typed (T.instruction z) r) :
    Routing T ⟨z, b, {r}, 0⟩ ⟨z, T.delta z r, {r}, 1⟩
      ((b ∆ T.delta z r).card + 1) := by
  have fill := routing_toward T (fun b => ⟨z, b, {r}, 0⟩) b (T.delta z r)
    (by intro x y h; exact congrArg Word.b h) (by
    intro b hb
    simp [installed, singleFlag_singleton, typed, hb])
  have finish : Routing T ⟨z, T.delta z r, {r}, 0⟩ ⟨z, T.delta z r, {r}, 1⟩ 1 :=
    .step (by simp [installed, singleFlag_singleton, typed]) (by simp [Word.mk.injEq])
      (.refl _)
  exact routing_trans fill finish

private theorem clear_left (T : Table k) (z t : Bank k) (r : Flag) :
    Routing T ⟨z, t, {r}, 1⟩ (ready true t) (z.card + 3) := by
  have clear := routing_toward T (fun a => ⟨a, t, {r}, 1⟩) z ∅
    (by intro x y h; exact congrArg Word.a h) (by
    intro a ha
    simp [installed, singleFlag_singleton, ha])
  have finish : Routing T ⟨∅, t, {r}, 1⟩ (ready true t) 3 := by
    apply Routing.step (v := ⟨∅, t, {r}, 2⟩)
    · simp [installed, singleFlag_singleton]
    · simp [Word.mk.injEq]
    apply Routing.step (v := ⟨∅, t, ∅, 2⟩)
    · simp [installed, singleFlag_singleton]
    · simp [Word.mk.injEq]
    apply Routing.step (v := ready true t)
    · simp [installed, singleFlag_empty, ready]
    · simp [Word.mk.injEq, ready]
    exact .refl _
  simpa [Finset.symmDiff_def] using routing_trans clear finish

private theorem fill_right (T : Table k) (z a : Bank k) (r : Flag)
    (typed : Typed (T.instruction z) r) :
    Routing T ⟨a, z, {r}, 3⟩ ⟨T.delta z r, z, {r}, 4⟩
      ((a ∆ T.delta z r).card + 1) := by
  have fill := routing_toward T (fun a => ⟨a, z, {r}, 3⟩) a (T.delta z r)
    (by intro x y h; exact congrArg Word.a h) (by
    intro a ha
    simp [installed, singleFlag_singleton, typed, ha])
  have finish : Routing T ⟨T.delta z r, z, {r}, 3⟩ ⟨T.delta z r, z, {r}, 4⟩ 1 :=
    .step (by simp [installed, singleFlag_singleton, typed]) (by simp [Word.mk.injEq])
      (.refl _)
  exact routing_trans fill finish

private theorem clear_right (T : Table k) (z t : Bank k) (r : Flag) :
    Routing T ⟨t, z, {r}, 4⟩ (ready false t) (z.card + 5) := by
  have clear := routing_toward T (fun b => ⟨t, b, {r}, 4⟩) z ∅
    (by intro x y h; exact congrArg Word.b h) (by
    intro b hb
    simp [installed, singleFlag_singleton, hb])
  have finish : Routing T ⟨t, ∅, {r}, 4⟩ (ready false t) 5 := by
    apply Routing.step (v := ⟨t, ∅, {r}, 5⟩)
    · simp [installed, singleFlag_singleton]
    · simp [Word.mk.injEq]
    apply Routing.step (v := ⟨t, ∅, ∅, 5⟩)
    · simp [installed, singleFlag_singleton]
    · simp [Word.mk.injEq]
    apply Routing.step (v := ⟨t, ∅, ∅, 6⟩)
    · simp [installed, singleFlag_empty]
    · simp [Word.mk.injEq]
    apply Routing.step (v := ⟨t, ∅, ∅, 7⟩)
    · simp [installed]
    · simp [Word.mk.injEq]
    apply Routing.step (v := ready false t)
    · simp [installed, ready]
    · simp [Word.mk.injEq, ready]
    exact .refl _
  simpa [Finset.symmDiff_def] using routing_trans clear finish

/-- The original instruction first writes its reply flag; the remaining calls
are root Reads and end at exactly the opposite ready representation. -/
theorem typed_transfer (T : Table k) (right : Bool) (z : Bank k) (r : Flag)
    (typed : Typed (T.instruction z) r) :
    (installed T (ready right z)).instruction = T.instruction z ∧
    Routing T ((installed T (ready right z)).next r)
      (ready (!right) (T.delta z r))
      (z.card + (T.delta z r).card + if right then 6 else 4) := by
  cases right
  · constructor
    · simp [ready, installed]
    · have path := routing_trans (fill_left T z ∅ r typed) (clear_left T z (T.delta z r) r)
      convert path using 1 <;> simp [ready, installed, Finset.symmDiff_def]
      omega
  · constructor
    · simp [ready, installed]
    · have path := routing_trans (fill_right T z ∅ r typed) (clear_right T z (T.delta z r) r)
      convert path using 1 <;> simp [ready, installed, Finset.symmDiff_def]
      omega

/-- One logical bit changes: a bank bit, a flag, or the next Gray phase. -/
inductive Change : Word k → Word k → Prop where
  | a (w : Word k) (j : Fin k) : Change w { w with a := w.a ∆ {j} }
  | b (w : Word k) (j : Fin k) : Change w { w with b := w.b ∆ {j} }
  | flag (w : Word k) (r : Flag) : Change w { w with flags := w.flags ∆ {r} }
  | phase (w : Word k) : Change w
      { w with phase := ⟨(w.phase.val + 1) % 8, Nat.mod_lt _ (by decide)⟩ }

private theorem change_a_toward (w : Word k) (t : Bank k) (h : w.a ≠ t) :
    Change w { w with a := toward w.a t } := by
  obtain ⟨j, hj⟩ := toward_flip w.a t h
  rw [hj]
  exact .a w j

private theorem change_b_toward (w : Word k) (t : Bank k) (h : w.b ≠ t) :
    Change w { w with b := toward w.b t } := by
  obtain ⟨j, hj⟩ := toward_flip w.b t h
  rw [hj]
  exact .b w j

private theorem change_set_flag (w : Word k) (r : Flag) (h : w.flags = ∅) :
    Change w { w with flags := {r} } := by
  simpa [h, Finset.symmDiff_def] using Change.flag w r

private theorem change_clear_flag (w : Word k) (r : Flag) (h : singleFlag w.flags = some r) :
    Change w { w with flags := ∅ } := by
  have hf := singleFlag_spec h
  simpa [hf, Finset.symmDiff_def] using Change.flag w r

/-- Every installed response, including unsupported rows, holds or flips one bit. -/
theorem installed_local (T : Table k) (w : Word k) (r : Flag) :
    (installed T w).next r = w ∨ Change w ((installed T w).next r) := by
  rcases w with ⟨a, b, f, p⟩
  fin_cases p <;> simp only [installed]
  all_goals
    repeat' split
    all_goals simp only [root, true_or]
    all_goals try { exact Or.inr (Change.phase _) }
    all_goals try { right; apply change_a_toward; assumption }
    all_goals try { right; apply change_b_toward; assumption }
    all_goals try { right; apply change_set_flag; tauto }
    all_goals try { right; apply change_clear_flag; assumption }
    all_goals right
    all_goals simpa using Change.phase (Word.mk a b f 7)

abbrev Slot (k : Nat) := Fin k ⊕ Fin k ⊕ Flag ⊕ Fin 3

def phaseBits (p : Fin 8) : Fin 3 → Bool :=
  match p.val with
  | 0 => ![false, false, false]
  | 1 => ![false, false, true]
  | 2 => ![false, true, true]
  | 3 => ![false, true, false]
  | 4 => ![true, true, false]
  | 5 => ![true, true, true]
  | 6 => ![true, false, true]
  | _ => ![true, false, false]

def logical (w : Word k) : Slot k → Bool
  | .inl i => decide (i ∈ w.a)
  | .inr (.inl i) => decide (i ∈ w.b)
  | .inr (.inr (.inl i)) => decide (i ∈ w.flags)
  | .inr (.inr (.inr i)) => phaseBits w.phase i

def OneBit {ι : Type} [DecidableEq ι] (x y : ι → Bool) : Prop :=
  ∃ i, ∀ j, y j = if j = i then !(x j) else x j

private theorem phase_oneBit (p : Fin 8) :
    OneBit (phaseBits p) (phaseBits ⟨(p.val + 1) % 8, Nat.mod_lt _ (by decide)⟩) := by
  unfold OneBit
  fin_cases p <;> decide

private theorem change_logical {w v : Word k} (h : Change w v) :
    OneBit (logical w) (logical v) := by
  cases h with
  | a i =>
      refine ⟨.inl i, ?_⟩
      rintro (j | (j | (j | j))) <;> simp only [logical]
      · by_cases hj : j = i <;> by_cases ha : j ∈ w.a <;>
          simp [Finset.mem_symmDiff, hj, ha]
      all_goals simp
  | b i =>
      refine ⟨.inr (.inl i), ?_⟩
      rintro (j | (j | (j | j))) <;> simp only [logical]
      · simp
      · by_cases hj : j = i <;> by_cases ha : j ∈ w.b <;>
          simp [Finset.mem_symmDiff, hj, ha]
      all_goals simp
  | flag i =>
      refine ⟨.inr (.inr (.inl i)), ?_⟩
      rintro (j | (j | (j | j))) <;> simp only [logical]
      · simp
      · simp
      · by_cases hj : j = i <;> by_cases ha : j ∈ w.flags <;>
          simp [Finset.mem_symmDiff, hj, ha]
      · simp
  | phase =>
      obtain ⟨i, hi⟩ := phase_oneBit w.phase
      refine ⟨.inr (.inr (.inr i)), ?_⟩
      rintro (j | (j | (j | j))) <;> simp only [logical]
      · simp
      · simp
      · simp
      · simpa using hi j

/-- Concatenation order is A, B, the five flags, then the three phase bits. -/
def slotIndex (k : Nat) : Slot k ≃ Fin (k + (k + (5 + 3))) :=
  (Equiv.sumCongr (Equiv.refl _) (Equiv.sumCongr (Equiv.refl _) finSumFinEquiv)).trans
    ((Equiv.sumCongr (Equiv.refl _) finSumFinEquiv).trans finSumFinEquiv)

/-- Zero interleaving leaves every odd position zero. -/
def interleave {m : Nat} (x : Fin m → Bool) (i : Fin (2 * m - 1)) : Bool :=
  if h : i.val % 2 = 0 then x ⟨i.val / 2, by omega⟩ else false

def physical (w : Word k) : Fin (2 * (k + (k + (5 + 3))) - 1) → Bool :=
  interleave (logical w ∘ (slotIndex k).symm)

private theorem interleave_no_adjacent {m : Nat} (x : Fin m → Bool)
    (i j : Fin (2 * m - 1)) (h : i.val + 1 = j.val) :
    interleave x i = false ∨ interleave x j = false := by
  unfold interleave
  by_cases hi : i.val % 2 = 0
  · right
    have hj : j.val % 2 ≠ 0 := by omega
    simp [hj]
  · left
    simp [hi]

private theorem oneBit_interleave {m : Nat} {x y : Fin m → Bool} (h : OneBit x y) :
    OneBit (interleave x) (interleave y) := by
  obtain ⟨i, hi⟩ := h
  refine ⟨⟨2 * i.val, by omega⟩, ?_⟩
  intro j
  unfold interleave
  by_cases hj : j.val % 2 = 0
  · simp only [dif_pos hj]
    rw [hi]
    have he : (⟨j.val / 2, by omega⟩ : Fin m) = i ↔
        j = (⟨2 * i.val, by omega⟩ : Fin (2 * m - 1)) := by
      simp only [Fin.ext_iff]
      omega
    simp only [he]
  · have he : j ≠ (⟨2 * i.val, by omega⟩ : Fin (2 * m - 1)) := by
      intro eq
      apply hj
      rw [eq]
      simp
    simp [hj, he]

private theorem change_physical {w v : Word k} (h : Change w v) :
    OneBit (physical w) (physical v) := by
  apply oneBit_interleave
  obtain ⟨i, hi⟩ := change_logical h
  refine ⟨slotIndex k i, ?_⟩
  intro j
  simpa only [Function.comp_apply, Equiv.symm_apply_eq] using hi ((slotIndex k).symm j)

/-- All installed words and their successors are sparse, and each row holds or
changes exactly one physical bit, without any reachability hypothesis. -/
theorem physical_rows (T : Table k) (w : Word k) (r : Flag) :
    (∀ i j, i.val + 1 = j.val → physical w i = false ∨ physical w j = false) ∧
    (∀ i j, i.val + 1 = j.val →
      physical ((installed T w).next r) i = false ∨
      physical ((installed T w).next r) j = false) ∧
    ((installed T w).next r = w ∨
      OneBit (physical w) (physical ((installed T w).next r))) := by
  refine ⟨interleave_no_adjacent _, interleave_no_adjacent _, ?_⟩
  exact (installed_local T w r).imp id change_physical

/-- Decode the eight possible phase bit patterns. -/
def phaseIndex (x : Fin 3 → Bool) : Fin 8 :=
  if x 0 then
    if x 1 then (if x 2 then 5 else 4) else (if x 2 then 6 else 7)
  else
    if x 1 then (if x 2 then 2 else 3) else (if x 2 then 1 else 0)

private def phaseEquiv : Fin 8 ≃ (Fin 3 → Bool) where
  toFun := phaseBits
  invFun := phaseIndex
  left_inv := by decide
  right_inv := by decide

/-- Every logical bit pattern, with no support restriction, is installed. -/
def logicalEquiv : Word k ≃ (Slot k → Bool) where
  toFun := logical
  invFun x := ⟨Finset.univ.filter (fun i => x (.inl i)),
    Finset.univ.filter (fun i => x (.inr (.inl i))),
    Finset.univ.filter (fun i => x (.inr (.inr (.inl i)))),
    phaseIndex (fun i => x (.inr (.inr (.inr i))))⟩
  left_inv w := by
    rcases w with ⟨a, b, f, p⟩
    simp only [logical]
    congr 1
    · ext i; simp
    · ext i; simp
    · ext i; simp
    · exact phaseEquiv.left_inv p
  right_inv x := by
    funext i
    rcases i with i | (i | (i | i))
    · simp [logical]
    · simp [logical]
    · simp [logical]
    · exact congrFun (phaseEquiv.right_inv (fun j => x (.inr (.inr (.inr j))))) i

instance : Fintype (Word k) := Fintype.ofEquiv (Slot k → Bool) logicalEquiv.symm

private theorem word_card : Fintype.card (Word k) = 2 ^ (2 * k + 8) := by
  rw [Fintype.card_congr logicalEquiv]
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_sum, Fintype.card_fin, Slot, Flag]
  congr 1
  omega

private theorem interleave_even {m : Nat} (x : Fin m → Bool) (i : Fin m) :
    interleave x ⟨2 * i.val, by omega⟩ = x i := by
  simp [interleave]

private theorem physical_injective : Function.Injective (physical (k := k)) := by
  intro w v eq
  apply logicalEquiv.injective
  change logical w = logical v
  funext i
  have hi := congrFun eq ⟨2 * (slotIndex k i).val, by have := (slotIndex k i).isLt; omega⟩
  simpa only [physical, interleave_even, Function.comp_apply, Equiv.symm_apply_apply] using hi

/-- Installation is exactly the full image of zero-interleaved logical words. -/
def installedWords (k : Nat) : Finset (Fin (2 * (k + (k + (5 + 3))) - 1) → Bool) :=
  Finset.univ.image physical

private theorem installation_size : (installedWords k).card = 2 ^ (2 * k + 8) := by
  rw [installedWords, Finset.card_image_of_injective _ physical_injective, Finset.card_univ]
  exact word_card

abbrev RawReply := Fin 4

def replyFlag (r : RawReply) : Flag := ⟨r.val, by omega⟩

/-- These are the actual primitive events, including every padding root Read. -/
inductive Event where
  | read (address : Address) (reply : RawReply)
  | update
  deriving DecidableEq

/-- A finite execution whose every immediate response changes one physical bit. -/
inductive Execution (T : Table k) (obs : Nat → Address → RawReply) :
    Word k → Nat → Word k → Nat → List Event → Prop where
  | refl (w : Word k) (a : Nat) : Execution T obs w a w a []
  | read {w v : Word k} {a b : Nat} {p : Address} {events : List Event} :
      (installed T w).instruction = .read p →
      OneBit (physical w) (physical ((installed T w).next (replyFlag (obs a p)))) →
      Execution T obs ((installed T w).next (replyFlag (obs a p))) a v b events →
      Execution T obs w a v b (.read p (obs a p) :: events)
  | update {w v : Word k} {a b : Nat} {events : List Event} :
      (installed T w).instruction = .update →
      OneBit (physical w) (physical ((installed T w).next 4)) →
      Execution T obs ((installed T w).next 4) (a + 1) v b events →
      Execution T obs w a v b (.update :: events)

private theorem routing_execution {T : Table k} {w v : Word k} {n : Nat}
    (path : Routing T w v n) (obs : Nat → Address → RawReply) (a : Nat) :
    Execution T obs w a v a (List.replicate n (.read [] (obs a []))) := by
  induction path with
  | refl => exact .refl _ _
  | @step w v u n hop diff tail ih =>
      have localStep := installed_local T w (replyFlag (obs a []))
      rw [hop] at localStep
      have one : OneBit (physical w) (physical v) := by
        rcases localStep with same | change
        · exact (diff same.symm).elim
        · exact change_physical change
      rw [List.replicate_succ]
      apply Execution.read (p := [])
      · simp [hop, root]
      · simpa [hop, root] using one
      · simpa [hop, root] using ih

private theorem execution_trans {T : Table k} {obs : Nat → Address → RawReply}
    {w v u : Word k} {a b c : Nat} {s t : List Event}
    (left : Execution T obs w a v b s) (right : Execution T obs v b u c t) :
    Execution T obs w a u c (s ++ t) := by
  induction left with
  | refl => exact right
  | read hi hc _ ih => exact .read hi hc (ih right)
  | update hi hc _ ih => exact .update hi hc (ih right)

/-- One source instruction and all its padding calls, with the real initial
reply retained verbatim and no extra Update. -/
theorem native_transfer (T : Table k) (obs : Nat → Address → RawReply)
    (right : Bool) (z : Bank k) (a : Nat) :
    (∀ p, T.instruction z = .read p →
      Execution T obs (ready right z) a
        (ready (!right) (T.delta z (replyFlag (obs a p)))) a
        (.read p (obs a p) :: List.replicate
          (z.card + (T.delta z (replyFlag (obs a p))).card + if right then 6 else 4)
          (.read [] (obs a [])))) ∧
    (T.instruction z = .update →
      Execution T obs (ready right z) a (ready (!right) (T.delta z 4)) (a + 1)
        (.update :: List.replicate
          (z.card + (T.delta z 4).card + if right then 6 else 4)
          (.read [] (obs (a + 1) [])))) := by
  have firstBit (r : Flag) :
      OneBit (physical (ready right z))
        (physical ((installed T (ready right z)).next r)) := by
    apply change_physical
    cases right
    · simpa [ready, installed] using change_set_flag (ready false z) r (by rfl)
    · simpa [ready, installed] using change_set_flag (ready true z) r (by rfl)
  constructor
  · intro p hp
    have ht : Typed (T.instruction z) (replyFlag (obs a p)) := by
      rw [hp]
      exact (obs a p).isLt
    obtain ⟨instruction, path⟩ := typed_transfer T right z (replyFlag (obs a p)) ht
    exact .read (instruction.trans hp) (firstBit _) (routing_execution path obs a)
  · intro hu
    have ht : Typed (T.instruction z) 4 := by simp [hu, Typed]
    obtain ⟨instruction, path⟩ := typed_transfer T right z 4 ht
    exact .update (instruction.trans hu) (firstBit _) (routing_execution path obs (a + 1))

open GuardedPhaseExecution (Instruction Run)

/-- The original table as a native program, with no auxiliary memory. -/
def sourceProgram (T : Table k) (z : Bank k) : Instruction (Bank k) Address RawReply :=
  match T.instruction z with
  | .read p => .read p (fun r => T.delta z (replyFlag r))
  | .update => .update (T.delta z 4)
  | .halt _ => .halt

/-- The installed word itself is the entire mutable control. -/
def wordProgram (T : Table k) (w : Word k) : Instruction (Word k) Address RawReply :=
  match (installed T w).instruction with
  | .read p => .read p (fun r => (installed T w).next (replyFlag r))
  | .update => .update ((installed T w).next 4)
  | .halt _ => .halt

abbrev Installed (k : Nat) := {x // x ∈ installedWords k}

/-- A physical row is selected by the physical word alone. The inverse merely
specifies finite data expanded when the table is installed. -/
noncomputable def physicalEquiv : Word k ≃ Installed k :=
  Equiv.ofBijective (fun w => ⟨physical w, Finset.mem_image.mpr ⟨w, Finset.mem_univ _, rfl⟩⟩)
    ⟨fun _ _ h => physical_injective (congrArg Subtype.val h), by
      intro w
      obtain ⟨v, _, hv⟩ := Finset.mem_image.mp w.property
      exact ⟨v, Subtype.ext hv⟩⟩

noncomputable def physicalInstruction (T : Table k) (w : Installed k) : Opcode :=
  (installed T (physicalEquiv.symm w)).instruction

noncomputable def physicalProgram (T : Table k) (w : Installed k) :
    Instruction (Installed k) Address RawReply :=
  GuardedPhaseExecution.transportProgram physicalEquiv id (wordProgram T) w

private theorem execution_run {T : Table k} {obs : Nat → Address → RawReply}
    {w v : Word k} {a b : Nat} {events : List Event}
    (path : Execution T obs w a v b events) : Run (wordProgram T) obs w a v b := by
  induction path with
  | refl => exact .refl _ _
  | read hi _ _ ih => exact .read (by rw [wordProgram, hi]) ih
  | update hi _ _ ih => exact .update (by rw [wordProgram, hi]) ih

/-- Every finite source execution has an actual installed execution on the same
source epochs; the word alternates ready banks once per source instruction. -/
theorem simulate_run {T : Table k} {obs : Nat → Address → RawReply}
    {z t : Bank k} {a b : Nat} (path : Run (sourceProgram T) obs z a t b)
    (right : Bool) :
    ∃ last events, Execution T obs (ready right z) a (ready last t) b events := by
  induction path generalizing right with
  | refl => exact ⟨right, [], .refl _ _⟩
  | @read z p next a t b hop tail ih =>
      cases hz : T.instruction z with
      | read q =>
          have eq : Instruction.read q (fun r => T.delta z (replyFlag r)) =
              Instruction.read p next := by simpa [sourceProgram, hz] using hop
          cases eq
          obtain ⟨last, events, rest⟩ := ih (!right)
          exact ⟨last, _, execution_trans ((native_transfer T obs right z a).1 _ hz) rest⟩
      | update => simp [sourceProgram, hz] at hop
      | halt bit => simp [sourceProgram, hz] at hop
  | @update z next a t b hop tail ih =>
      cases hz : T.instruction z with
      | read q => simp [sourceProgram, hz] at hop
      | update =>
          have eq : T.delta z 4 = next := by simpa [sourceProgram, hz] using hop
          subst next
          obtain ⟨last, events, rest⟩ := ih (!right)
          exact ⟨last, _, execution_trans ((native_transfer T obs right z a).2 hz) rest⟩
      | halt bit => simp [sourceProgram, hz] at hop

private theorem execution_physical {T : Table k} {obs : Nat → Address → RawReply}
    {w v : Word k} {a b : Nat} {events : List Event}
    (path : Execution T obs w a v b events) :
    Run (physicalProgram T) obs (physicalEquiv w) a (physicalEquiv v) b := by
  apply (GuardedPhaseExecution.run_transport_iff physicalEquiv id
    (prog := wordProgram T) (obs := obs)
    (instructions := by
      intro q
      simp [physicalProgram, GuardedPhaseExecution.transportProgram])
    (responses := by intros; rfl)).mp
  exact execution_run path

private theorem suffix_after_native {T : Table k} {obs : Nat → Address → RawReply}
    {w v u : Word k} {a b c : Nat} {events : List Event} {bit : Bool}
    (initial : Run (wordProgram T) obs w a u c)
    (whole : Execution T obs w a v b events)
    (halt : (installed T v).instruction = .halt bit) :
    ∃ suffix, Execution T obs u c v b suffix := by
  induction initial generalizing v b events with
  | refl => exact ⟨events, whole⟩
  | @read w p next a u c hi rest ih =>
      cases whole with
      | refl => simp [wordProgram, halt] at hi
      | @read _ v _ b q es hrow hbit tail =>
          have eq : Instruction.read q (fun r => (installed T w).next (replyFlag r)) =
              Instruction.read p next := by simpa [wordProgram, hrow] using hi
          cases eq
          exact ih tail halt
      | update hrow hbit tail => simp [wordProgram, hrow] at hi
  | @update w next a u c hi rest ih =>
      cases whole with
      | refl => simp [wordProgram, halt] at hi
      | read hrow hbit tail => simp [wordProgram, hrow] at hi
      | update hrow hbit tail =>
          have eq : (installed T w).next 4 = next := by
            simpa [wordProgram, hrow] using hi
          subst next
          exact ih tail halt

private theorem execution_trace_unique {T : Table k} {obs : Nat → Address → RawReply}
    {w v u : Word k} {a b c : Nat} {s t : List Event} {bit bit' : Bool}
    (left : Execution T obs w a v b s) (right : Execution T obs w a u c t)
    (halt : (installed T v).instruction = .halt bit)
    (halt' : (installed T u).instruction = .halt bit') : s = t := by
  induction left generalizing u c t with
  | refl =>
      cases right with
      | refl => rfl
      | read hi _ _ => cases halt.symm.trans hi
      | update hi _ _ => cases halt.symm.trans hi
  | read hi hc tail ih =>
      cases right with
      | refl => cases hi.symm.trans halt'
      | read hj _ suffix =>
          cases hi.symm.trans hj
          exact congrArg _ (ih suffix halt halt')
      | update hj _ _ => cases hi.symm.trans hj
  | update hi hc tail ih =>
      cases right with
      | refl => cases hi.symm.trans halt'
      | read hj _ _ => cases hi.symm.trans hj
      | update hj _ suffix => exact congrArg _ (ih suffix halt halt')

/-- The finite future trace is proof data; no row consults this predicate. -/
def TerminatesWith (T : Table k) (obs : Nat → Address → RawReply)
    (w : Word k) (a : Nat) (events : List Event) : Prop :=
  ∃ v b bit, Execution T obs w a v b events ∧ (installed T v).instruction = .halt bit

/-- The remaining number of primitive calls on terminating configurations. -/
noncomputable def remaining (T : Table k) (obs : Nat → Address → RawReply)
    (w : Word k) (a : Nat) : Nat := by
  classical
  exact if h : ∃ events, TerminatesWith T obs w a events then
    (Classical.choose h).length else 0

private theorem remaining_eq {T : Table k} {obs : Nat → Address → RawReply}
    {w v : Word k} {a b : Nat} {events : List Event} {bit : Bool}
    (path : Execution T obs w a v b events) (halt : (installed T v).instruction = .halt bit) :
    remaining T obs w a = events.length := by
  have existsTrace : ∃ es, TerminatesWith T obs w a es := ⟨events, v, b, bit, path, halt⟩
  rw [remaining, dif_pos existsTrace]
  obtain ⟨u, c, bit', other, final⟩ := Classical.choose_spec existsTrace
  exact congrArg List.length (execution_trace_unique other path final halt)

private theorem execution_shift {T : Table k} {obs obs' : Nat → Address → RawReply}
    {w v : Word k} {a b : Nat} {events : List Event}
    (path : Execution T obs w a v b events) (c : Nat)
    (responses : ∀ n p, obs (a + n) p = obs' (c + n) p) :
    ∃ d, b = a + d ∧ Execution T obs' w c v (c + d) events := by
  induction path generalizing c with
  | refl => exact ⟨0, by omega, by simpa using Execution.refl _ _⟩
  | @read w v a b p events hi hc tail ih =>
      have reply : obs a p = obs' c p := by simpa using responses 0 p
      obtain ⟨d, hd, rest⟩ := ih c responses
      refine ⟨d, hd, ?_⟩
      rw [reply] at rest hc ⊢
      exact .read hi hc rest
  | @update w v a b events hi hc tail ih =>
      obtain ⟨d, hd, rest⟩ := ih (c + 1) (by
        intro n p
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using responses (n + 1) p)
      refine ⟨d + 1, by omega, ?_⟩
      convert Execution.update hi hc rest using 1
      omega

open D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition (Reply readout)
open D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source substitution)

/-- The four raw native replies in the fixed flag order. -/
def rawReply (r : Reply) : RawReply :=
  match r with
  | .alpha => 0 | .beta => 1 | .branch => 2 | .absent => 3

/-- The original source field; only Update advances its substitution epoch. -/
def actualObservation (y : Source) (n : Nat) (p : Address) : RawReply :=
  rawReply (readout p ((substitution : Source → Source)^[n] y))

/-- Rank evaluated from the actual current source, with no historical epoch. -/
noncomputable def sourceRank (T : Table k) (y : Source) (w : Word k) : Nat :=
  remaining T (actualObservation y) w 0

private theorem remaining_current_source {T : Table k} {y : Source}
    {w v : Word k} {a b : Nat} {events : List Event} {bit : Bool}
    (path : Execution T (actualObservation y) w a v b events)
    (halt : (installed T v).instruction = .halt bit) :
    remaining T (actualObservation y) w a =
      sourceRank T ((substitution : Source → Source)^[a] y) w := by
  obtain ⟨d, hd, shifted⟩ := execution_shift path 0
    (obs' := actualObservation ((substitution : Source → Source)^[a] y)) (by
      intro n p
      simp only [actualObservation, Nat.zero_add]
      rw [← Function.iterate_add_apply, Nat.add_comm a n])
  rw [remaining_eq path halt, sourceRank, remaining_eq shifted halt]

/-- The rank is independent of which history and epoch represent the same
actual source and observer word, whenever that configuration terminates. -/
def SourceRankInvariant (T : Table k) : Prop :=
  ∀ (y y' : Source) (w v u : Word k) (a b c d : Nat) (es fs : List Event) (bit bit' : Bool),
    Execution T (actualObservation y) w a v b es →
    (installed T v).instruction = .halt bit →
    Execution T (actualObservation y') w c u d fs →
    (installed T u).instruction = .halt bit' →
    (substitution : Source → Source)^[a] y = (substitution : Source → Source)^[c] y' →
    remaining T (actualObservation y) w a = remaining T (actualObservation y') w c

private theorem source_rank_invariant (T : Table k) : SourceRankInvariant T := by
  intro y y' w v u a b c d es fs bit bit' first halt second halt' same
  rw [remaining_current_source first halt, remaining_current_source second halt', same]

private theorem remaining_step {T : Table k} {obs : Nat → Address → RawReply}
    {w v u : Word k} {a b c : Nat} {event : Event} {events : List Event} {bit : Bool}
    (step : Execution T obs w a v b [event]) (tail : Execution T obs v b u c events)
    (halt : (installed T u).instruction = .halt bit) :
    remaining T obs w a = remaining T obs v b + 1 := by
  rw [remaining_eq (execution_trans step tail) halt, remaining_eq tail halt]
  simp

/-- A source Halt is reached with its fixed output. Any halt-ended native
execution of the installed table has this same endpoint and source epoch. -/
theorem installed_halt {T : Table k} {obs : Nat → Address → RawReply}
    {z t : Bank k} {a b : Nat} {bit : Bool}
    (path : Run (sourceProgram T) obs z a t b) (halt : T.instruction t = .halt bit)
    (right : Bool) :
    (installedWords k).card = 2 ^ (2 * k + 8) ∧
    2 * (k + (k + (5 + 3))) - 1 = 4 * k + 15 ∧
    (∀ s : Bool, ∀ u : Bank k, ∀ r : Flag,
      u.card + (T.delta u r).card + (if s then 7 else 5) ≤ 2 * k + 7) ∧
    (∀ w : Word k, ∀ r : Flag,
      (∀ i j, i.val + 1 = j.val → physical w i = false ∨ physical w j = false) ∧
      ((installed T w).next r = w ∨
        OneBit (physical w) (physical ((installed T w).next r)))) ∧
    ∃ last events, Execution T obs (ready right z) a (ready last t) b events ∧
      (installed T (ready last t)).instruction = .halt bit ∧
      (∀ w c, Run (wordProgram T) obs (ready right z) a w c →
        wordProgram T w = .halt → w = ready last t ∧ c = b) ∧
      physicalInstruction T (physicalEquiv (ready last t)) = .halt bit ∧
      Run (physicalProgram T) obs (physicalEquiv (ready right z)) a
        (physicalEquiv (ready last t)) b ∧
      (∀ w c, Run (physicalProgram T) obs (physicalEquiv (ready right z)) a w c →
        physicalProgram T w = .halt → w = physicalEquiv (ready last t) ∧ c = b) ∧
      remaining T obs (ready right z) a = events.length ∧
      remaining T obs (ready last t) b = 0 ∧
      (∀ w c, Run (wordProgram T) obs (ready right z) a w c →
        ∃ suffix, Execution T obs w c (ready last t) b suffix ∧
          remaining T obs w c = suffix.length) ∧
      (∀ w v u : Word k, ∀ a' b' c' : Nat, ∀ e es bit',
        Execution T obs w a' v b' [e] → Execution T obs v b' u c' es →
        (installed T u).instruction = .halt bit' →
        remaining T obs w a' = remaining T obs v b' + 1) ∧ SourceRankInvariant T := by
  refine ⟨installation_size, by omega, ?_, ?_, ?_⟩
  · intro s u r
    have h₁ := card_finset_fin_le u
    have h₂ := card_finset_fin_le (T.delta u r)
    cases s <;> simp only [Bool.false_eq_true, if_false, if_true] <;> omega
  · intro w r
    have hs := physical_rows T w r
    exact ⟨hs.1, hs.2.2⟩
  obtain ⟨last, events, run⟩ := simulate_run path right
  have hi : (installed T (ready last t)).instruction = .halt bit := by
    cases last <;> simp [ready, installed, halt]
  refine ⟨last, events, run, hi, ?_, by simpa [physicalInstruction] using hi,
    execution_physical run, ?_, remaining_eq run hi,
    remaining_eq (.refl _ _) hi, ?_, ?_, source_rank_invariant T⟩
  · intro w c other final
    exact GuardedPhaseExecution.run_halt_unique other (execution_run run) final
      (by simp [wordProgram, hi])
  · intro w c other final
    exact GuardedPhaseExecution.run_halt_unique other (execution_physical run) final
      (by simp [physicalProgram, GuardedPhaseExecution.transportProgram, wordProgram, hi,
        GuardedPhaseExecution.Instruction.transport])
  · intro w c initial
    obtain ⟨suffix, tail⟩ := suffix_after_native initial run hi
    exact ⟨suffix, tail, remaining_eq tail hi⟩
  · intro w v u a' b' c' e es bit' step tail halt'
    exact remaining_step step tail halt'

end D5.S3.ObserverMemory.Algorithms.TwoBankInstalledWord
