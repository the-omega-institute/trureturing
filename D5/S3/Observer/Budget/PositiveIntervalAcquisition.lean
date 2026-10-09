/- GID: D5/S3/Observer/Budget/PositiveIntervalAcquisition
   generality: G
   mirror-B: D5/B/S3/Observer/Budget/PositiveIntervalAcquisition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Nat.Log]
   utility: none
   digest: Finite intervals admit logarithmic sensing with positive forward waits. -/

import D5.S3.Observer.Budget.DyadicForwardWaitingOptimality
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Budget.PositiveIntervalAcquisition

open DyadicForwardWaitingOptimality (Protocol execute CorrectOn threshold)

/-- The strictly positive forward distance to a prescribed phase. -/
def waitTo (P now target : Nat) : Nat :=
  if now % P < target then target - now % P else P + target - now % P

/-- Half-open intervals use their lower midpoint. A singleton stops immediately. -/
def acquire (P : Nat) : (d : Nat) → Nat → Nat → Nat → Protocol d
  | 0, lo, _, _ => .stop lo
  | d + 1, lo, hi, now =>
      if hi ≤ lo + 1 then .stop lo else
        let m := (lo + hi) / 2
        let w := waitTo P now (P - m)
        .query w (fun bit => if bit = 0 then acquire P d lo m (now + w)
          else acquire P d m hi (now + w))

/-- The list contains precisely the waiting increments on this execution. -/
def waits (read : Nat → Nat → Fin 2) {d : Nat} : Protocol d → Nat → Nat → List Nat
  | .stop _, _, _ => []
  | .query w next, now, r => w :: waits read (next (read (now + w) r)) (now + w) r

/-- Decode a physical high digit using the retained first digit and full elapsed count. -/
def decodedRead (p P b now r : Nat) : Fin 2 :=
  if ((b * P + r + now) / P) % p = (b + now / P) % p then 0 else 1

private theorem waitTo_spec {P now t : Nat} (hP : 0 < P) (ht : t < P)
    (hne : now % P ≠ t) :
    0 < waitTo P now t ∧ waitTo P now t < P ∧
      (now + waitTo P now t) % P = t := by
  have hn := Nat.mod_lt now hP
  unfold waitTo
  split_ifs with h
  · refine ⟨by omega, by omega, ?_⟩
    rw [Nat.add_mod, Nat.mod_eq_of_lt (show t - now % P < P by omega),
      show now % P + (t - now % P) = t by omega, Nat.mod_eq_of_lt ht]
  · refine ⟨by omega, by omega, ?_⟩
    rw [Nat.add_mod, Nat.mod_eq_of_lt (show P + t - now % P < P by omega),
      show now % P + (P + t - now % P) = P + t by omega,
      Nat.add_mod_left, Nat.mod_eq_of_lt ht]


theorem interval_wait {P lo hi now : Nat} (hlo : lo < hi)
    (hhi : hi ≤ P) (hlive : lo + 1 < hi)
    (halign : now % P = (P - lo) % P ∨ now % P = (P - hi) % P) :
    let m := (lo + hi) / 2
    lo < m ∧ m < hi ∧
      0 < waitTo P now (P - m) ∧ waitTo P now (P - m) < P ∧
      (now + waitTo P now (P - m)) % P = P - m := by
  dsimp only
  have hm : lo < (lo + hi) / 2 ∧ (lo + hi) / 2 < hi := by omega
  have hP : 0 < P := by omega
  have target : P - (lo + hi) / 2 < P := by omega
  have different : now % P ≠ P - (lo + hi) / 2 := by
    rcases halign with hl | hr
    · by_cases hz : lo = 0
      · subst lo
        simp only [Nat.sub_zero, Nat.mod_self] at hl
        omega
      · rw [Nat.mod_eq_of_lt (show P - lo < P by omega)] at hl
        omega
    · rw [Nat.mod_eq_of_lt (show P - hi < P by omega)] at hr
      omega
  exact ⟨hm.1, hm.2, waitTo_spec hP target different⟩

private theorem acquire_spec {P : Nat} {read : Nat → Nat → Fin 2}
    (law : ∀ now r, r < P → read now r = threshold P now r) (d : Nat) :
    ∀ lo hi now, lo < hi → hi ≤ P → hi - lo ≤ 2 ^ d →
      (now % P = (P - lo) % P ∨ now % P = (P - hi) % P) →
      ∀ r, lo ≤ r → r < hi →
        (execute read (acquire P d lo hi now) now r).1 = r ∧
        (execute read (acquire P d lo hi now) now r).2 ≤ now + d * (P - 1) ∧
        (waits read (acquire P d lo hi now) now r).length ≤ d ∧
        (∀ w ∈ waits read (acquire P d lo hi now) now r, 0 < w ∧ w < P) ∧
        (r + 1 = hi →
          (waits read (acquire P d lo hi now) now r).length = Nat.clog 2 (hi - lo)) := by
  induction d with
  | zero =>
    intro lo hi now hlo hhi hsize halign r hrlo hrhi
    have hr : r = lo := by simp only [Nat.pow_zero] at hsize; omega
    have hs : hi - lo = 1 := by simp only [Nat.pow_zero] at hsize; omega
    simp only [acquire, execute, waits, List.length_nil, Nat.zero_mul, Nat.add_zero]
    exact ⟨hr.symm, le_rfl, le_rfl, by simp, by simp [hs]⟩
  | succ d ih =>
    intro lo hi now hlo hhi hsize halign r hrlo hrhi
    by_cases stop : hi ≤ lo + 1
    · have hr : r = lo := by omega
      have hs : hi - lo = 1 := by omega
      simp only [acquire, if_pos stop, execute, waits, List.length_nil]
      refine ⟨hr.symm, Nat.le_add_right _ _, Nat.zero_le _, by simp, ?_⟩
      simp [hs]
    · let m := (lo + hi) / 2
      let w := waitTo P now (P - m)
      obtain ⟨hmlo, hmhi, hwpos, hwlt, phase⟩ := interval_wait hlo hhi (by omega) halign
      change lo < m at hmlo
      change m < hi at hmhi
      change 0 < w at hwpos
      change w < P at hwlt
      change (now + w) % P = P - m at phase
      have halves : m - lo ≤ 2 ^ d ∧ hi - m ≤ 2 ^ d := by
        dsimp [m]
        rw [Nat.pow_succ] at hsize
        omega
      have align : (now + w) % P = (P - m) % P := by
        rw [phase, Nat.mod_eq_of_lt (show P - m < P by omega)]
      have answer : read (now + w) r = if r < m then 0 else 1 := by
        rw [law _ _ (by omega), threshold, phase,
          Nat.sub_sub_self (show m ≤ P by omega)]
      have budget (t : Nat) (ht : t ≤ now + w + d * (P - 1)) :
          t ≤ now + (d + 1) * (P - 1) := by
        rw [Nat.add_mul, Nat.one_mul]
        omega
      by_cases left : r < m
      · have child := ih lo m (now + w) hmlo (by omega) halves.1 (Or.inr align)
          r hrlo left
        simp only [acquire, if_neg stop, execute, waits]
        change (execute read (if read (now + w) r = 0 then acquire P d lo m (now + w)
          else acquire P d m hi (now + w)) (now + w) r).1 = r ∧ _
        rw [answer, if_pos left]
        simp only [ite_true, List.length_cons, List.mem_cons]
        refine ⟨child.1, budget _ child.2.1, Nat.add_le_add_right child.2.2.1 1, ?_, ?_⟩
        · intro v hv
          rcases hv with rfl | hv
          · exact ⟨hwpos, hwlt⟩
          · exact child.2.2.2.1 v hv
        · intro last
          omega
      · have child := ih m hi (now + w) hmhi hhi halves.2 (Or.inl align)
          r (by omega) hrhi
        have bitne : (1 : Fin 2) ≠ 0 := by decide
        simp only [acquire, if_neg stop, execute, waits]
        change (execute read (if read (now + w) r = 0 then acquire P d lo m (now + w)
          else acquire P d m hi (now + w)) (now + w) r).1 = r ∧ _
        rw [answer, if_neg left]
        simp only [if_neg bitne, List.length_cons, List.mem_cons]
        refine ⟨child.1, budget _ child.2.1, Nat.add_le_add_right child.2.2.1 1, ?_, ?_⟩
        · intro v hv
          rcases hv with rfl | hv
          · exact ⟨hwpos, hwlt⟩
          · exact child.2.2.2.1 v hv
        · intro last
          rw [child.2.2.2.2 last]
          have half : hi - m = (hi - lo + 2 - 1) / 2 := by dsimp [m]; omega
          rw [half]
          exact (Nat.clog_of_two_le (by decide : 1 < 2)
            (show 2 ≤ hi - lo by omega)).symm


private theorem readout_law {p P : Nat} (hp : 2 ≤ p) (hP : 0 < P)
    (b now r : Nat) (hr : r < P) :
    ((b * P + r + now) % (p * P)) / P =
      (b + now / P + (threshold P now r).val) % p ∧
    decodedRead p P b now r = threshold P now r := by
  have baseDiv : (b * P + r) / P = b := by
    rw [Nat.mul_comm b P, Nat.mul_add_div hP, Nat.div_eq_of_lt hr, Nat.add_zero]
  have baseMod : (b * P + r) % P = r := by
    rw [Nat.add_mod, Nat.mul_mod_left, Nat.zero_add, Nat.mod_mod,
      Nat.mod_eq_of_lt hr]
  have raw : ((b * P + r + now) / P) % p =
      (b + now / P + (threshold P now r).val) % p := by
    rw [Nat.add_div hP, baseDiv, baseMod]
    unfold threshold
    split_ifs <;> simp only [Fin.val_zero, Fin.val_one] <;> congr 1 <;> omega
  have different : (b + now / P + 1) % p ≠ (b + now / P) % p := by
    rw [Nat.add_mod, Nat.mod_eq_of_lt (show 1 < p by omega)]
    have bound := Nat.mod_lt (b + now / P) (show 0 < p by omega)
    by_cases small : (b + now / P) % p + 1 < p
    · rw [Nat.mod_eq_of_lt small]
      omega
    · rw [show (b + now / P) % p + 1 = p by omega, Nat.mod_self]
      omega
  constructor
  · rw [Nat.mul_comm p P, Nat.mod_mul_right_div_self]
    exact raw
  · unfold decodedRead
    rw [raw]
    by_cases cut : r < P - now % P
    · simp only [threshold, if_pos cut, Fin.val_zero, Nat.add_zero, ite_true]
    · simp only [threshold, if_neg cut, Fin.val_one, if_neg different]

/-- One tree works for every retained first digit. Its physical observations
recover the low residue, and all waiting increments are strictly positive.
The rightmost original residue attains the logarithmic query budget. -/
theorem result (p P : Nat) (hp : 2 ≤ p) (hP : 0 < P) :
    ∃ T : Protocol (Nat.clog 2 P),
      T = acquire P (Nat.clog 2 P) 0 P 0 ∧
      (∀ b now r, r < P →
        ((b * P + r + now) % (p * P)) / P =
          (b + now / P + (threshold P now r).val) % p ∧
        decodedRead p P b now r = threshold P now r) ∧
      (∀ b r, r < P →
        (execute (decodedRead p P b) T 0 r).1 = r ∧
        (execute (decodedRead p P b) T 0 r).2 ≤ Nat.clog 2 P * (P - 1) ∧
        (waits (decodedRead p P b) T 0 r).length ≤ Nat.clog 2 P ∧
        ∀ w ∈ waits (decodedRead p P b) T 0 r, 0 < w ∧ w < P) ∧
      (∀ b, (waits (decodedRead p P b) T 0 (P - 1)).length = Nat.clog 2 P) ∧
      (P = 1 → T = .stop 0) := by
  refine ⟨acquire P (Nat.clog 2 P) 0 P 0, rfl, readout_law hp hP, ?_, ?_, ?_⟩
  · intro b r hr
    have facts := acquire_spec (fun now r hr => (readout_law hp hP b now r hr).2)
      (Nat.clog 2 P) 0 P 0 hP le_rfl (by simpa using Nat.le_pow_clog (by decide) P)
      (Or.inl (by simp)) r (Nat.zero_le _) hr
    simp only [Nat.zero_add] at facts
    exact ⟨facts.1, facts.2.1, facts.2.2.1, facts.2.2.2.1⟩
  · intro b
    have facts := acquire_spec (fun now r hr => (readout_law hp hP b now r hr).2)
      (Nat.clog 2 P) 0 P 0 hP le_rfl (by simpa using Nat.le_pow_clog (by decide) P)
      (Or.inl (by simp)) (P - 1) (Nat.zero_le _) (by omega)
    simpa using facts.2.2.2.2 (by omega)
  · intro singleton
    subst P
    rfl

end D5.S3.Observer.Budget.PositiveIntervalAcquisition
