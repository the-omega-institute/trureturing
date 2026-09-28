/- GID: D5/S3/ObserverMemory/Prediction/DelayedPulseMemoryGap
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Prediction/DelayedPulseMemoryGap
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Delayed pulses have exact static and all-time finite-memory minima. -/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Function.Iterate
import Mathlib.Order.Bounds.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ObserverMemory.Prediction.DelayedPulseMemoryGap

/-- The output of the successor system is one exactly at the pulse index. -/
def pulse (m n : ℕ) : ℝ := if n = m then 1 else 0

/-- A static label predicts all times in the prescribed window. -/
def StaticCorrect {C : Type*} (m H : ℕ) (ε : ℝ)
    (encode : ℕ → C) (decode : C → ℕ → ℝ) : Prop :=
  ∀ n t, t ≤ H → |decode (encode n) t - pulse m (n + t)| ≤ ε

/-- A fixed state update predicts every time from every initial source state. -/
def UpdaterCorrect {Q : Type*} (m : ℕ) (ε : ℝ)
    (encode : ℕ → Q) (update : Q → Q) (readout : Q → ℝ) : Prop :=
  ∀ n t, |readout (update^[t] (encode n)) - pulse m (n + t)| ≤ ε

/-- Finite label counts for static approximate prediction. -/
def staticSizes (m H : ℕ) (ε : ℝ) : Set ℕ :=
  {k | ∃ (C : Type) (_ : Fintype C) (encode : ℕ → C) (decode : C → ℕ → ℝ),
    Fintype.card C = k ∧ StaticCorrect m H ε encode decode}

/-- Finite state counts for all-time approximate prediction. -/
def updaterSizes (m : ℕ) (ε : ℝ) : Set ℕ :=
  {k | ∃ (Q : Type) (_ : Fintype Q) (encode : ℕ → Q)
    (update : Q → Q) (readout : Q → ℝ),
    Fintype.card Q = k ∧ UpdaterCorrect m ε encode update readout}

/-- Store the pulse's remaining delay if it is in the window, or a silent label. -/
def staticEncode (m H n : ℕ) : Fin (min H m + 2) :=
  if h : n ≤ m ∧ m - n ≤ H then ⟨m - n, by omega⟩
  else ⟨min H m + 1, by omega⟩

/-- The silent label never outputs one within the window. -/
def staticDecode (m H : ℕ) (c : Fin (min H m + 2)) (t : ℕ) : ℝ :=
  if c.val = t ∧ t ≤ min H m then 1 else 0

/-- States past the pulse merge into the absorbing state `m + 1`. -/
def machineEncode (m n : ℕ) : Fin (m + 2) :=
  ⟨min n (m + 1), by omega⟩

/-- Advance the stored source state, keeping the last state absorbing. -/
def machineUpdate (m : ℕ) (q : Fin (m + 2)) : Fin (m + 2) :=
  ⟨min (q.val + 1) (m + 1), by omega⟩

/-- Only the pulse state has a nonzero readout. -/
def machineReadout (m : ℕ) (q : Fin (m + 2)) : ℝ := pulse m q.val

/-- The explicit encoders attain both exact minima: a static window needs
`min H m + 2` labels, while a fixed all-time updater needs `m + 2` states.
The quantifiers include zero horizon, zero pulse index, and zero error. -/
theorem delayed_pulse_memory_gap (m H : ℕ) (ε : ℝ)
    (hε : 0 ≤ ε) (hhalf : ε < 1 / 2) :
    (StaticCorrect m H ε (staticEncode m H) (staticDecode m H) ∧
      IsLeast (staticSizes m H ε) (min H m + 2)) ∧
    (UpdaterCorrect m ε (machineEncode m) (machineUpdate m) (machineReadout m) ∧
      IsLeast (updaterSizes m ε) (m + 2)) := by
  constructor
  · have correct : StaticCorrect m H ε (staticEncode m H) (staticDecode m H) := by
      intro n t ht
      have exactOutput : staticDecode m H (staticEncode m H n) t = pulse m (n + t) := by
        unfold staticDecode staticEncode pulse
        split_ifs <;> simp_all <;> omega
      rw [exactOutput, sub_self, abs_zero]
      exact hε
    refine ⟨correct, ⟨?_, ?_⟩⟩
    · exact ⟨Fin (min H m + 2), inferInstance, staticEncode m H,
        staticDecode m H, Fintype.card_fin _, correct⟩
    · rintro k ⟨C, inst, encode, decode, rfl, hc⟩
      let representative : Fin (min H m + 2) → ℕ := fun i =>
        if i.val ≤ min H m then m - i.val else m + 1
      have separated : ∀ i j : Fin (min H m + 2), i.val < j.val →
          encode (representative i) ≠ encode (representative j) := by
        intro i j hij heq
        have hi : i.val ≤ min H m := by omega
        have leftPulse : pulse m (representative i + i.val) = 1 := by
          simp only [representative, if_pos hi, pulse]
          rw [if_pos (by omega)]
        have rightPulse : pulse m (representative j + i.val) = 0 := by
          have hne : representative j + i.val ≠ m := by
            dsimp [representative]
            split_ifs <;> omega
          exact if_neg hne
        have hleft := hc (representative i) i.val (by omega)
        have hright := hc (representative j) i.val (by omega)
        rw [leftPulse, heq] at hleft
        rw [rightPulse, sub_zero] at hright
        have hl := (abs_le.mp hleft).1
        have hr := (abs_le.mp hright).2
        linarith
      have hinj : Function.Injective (encode ∘ representative) := by
        intro i j heq
        by_contra hne
        have hv : i.val ≠ j.val := fun h => hne (Fin.ext h)
        rcases lt_or_gt_of_ne hv with hij | hji
        · exact separated i j hij heq
        · exact separated j i hji heq.symm
      simpa only [Fintype.card_fin] using Fintype.card_le_of_injective _ hinj
  · have invariant : ∀ n t,
        ((machineUpdate m)^[t] (machineEncode m n)).val = min (n + t) (m + 1) := by
      intro n t
      induction t with
      | zero => simp [machineEncode]
      | succ t ih =>
        rw [Function.iterate_succ_apply']
        change min (((machineUpdate m)^[t] (machineEncode m n)).val + 1) (m + 1) = _
        rw [ih]
        omega
    have correct : UpdaterCorrect m ε (machineEncode m) (machineUpdate m)
        (machineReadout m) := by
      intro n t
      have exactOutput : machineReadout m ((machineUpdate m)^[t] (machineEncode m n)) =
          pulse m (n + t) := by
        unfold machineReadout
        rw [invariant]
        have heq : min (n + t) (m + 1) = m ↔ n + t = m := by omega
        simp only [pulse, heq]
      rw [exactOutput, sub_self, abs_zero]
      exact hε
    refine ⟨correct, ⟨?_, ?_⟩⟩
    · exact ⟨Fin (m + 2), inferInstance, machineEncode m, machineUpdate m,
        machineReadout m, Fintype.card_fin _, correct⟩
    · rintro k ⟨Q, inst, encode, update, readout, rfl, hc⟩
      have separated : ∀ i j : Fin (m + 2), i.val < j.val → encode i.val ≠ encode j.val := by
        intro i j hij heq
        have hi : i.val ≤ m := by omega
        have hleft := hc i.val (m - i.val)
        have hright := hc j.val (m - i.val)
        have hp : pulse m (i.val + (m - i.val)) = 1 := by
          simp [pulse, Nat.add_sub_of_le hi]
        have hq : pulse m (j.val + (m - i.val)) = 0 := by
          simp [pulse, show j.val + (m - i.val) ≠ m by omega]
        rw [hp, heq] at hleft
        rw [hq, sub_zero] at hright
        have hl := (abs_le.mp hleft).1
        have hr := (abs_le.mp hright).2
        linarith
      have hinj : Function.Injective (fun i : Fin (m + 2) => encode i.val) := by
        intro i j heq
        by_contra hne
        have hv : i.val ≠ j.val := fun h => hne (Fin.ext h)
        rcases lt_or_gt_of_ne hv with hij | hji
        · exact separated i j hij heq
        · exact separated j i hji heq.symm
      simpa only [Fintype.card_fin] using Fintype.card_le_of_injective _ hinj

#print axioms delayed_pulse_memory_gap

end D5.S3.ObserverMemory.Prediction.DelayedPulseMemoryGap
