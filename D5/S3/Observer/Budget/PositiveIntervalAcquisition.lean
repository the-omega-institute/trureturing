/- GID: D5/S3/Observer/Budget/PositiveIntervalAcquisition
   generality: G
   mirror-B: D5/B/S3/Observer/Budget/PositiveIntervalAcquisition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Nat.Log]
   utility: none
   digest: Arbitrary finite intervals admit correct logarithmic sensing with positive forward waits. -/

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

end D5.S3.Observer.Budget.PositiveIntervalAcquisition
