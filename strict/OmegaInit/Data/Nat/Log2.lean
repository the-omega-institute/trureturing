/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Robin Arnez
-/
module
prelude
public import OmegaInit.Core
import OmegaInit.Data.Nat.Basic
import OmegaInit.Data.Nat.Div.Basic

namespace Omega.Nat

private abbrev twoN := Nat.succ (Nat.succ Nat.zero)
private theorem halves (n : Nat) (h : Nat.le twoN n) : Nat.lt (Nat.div n twoN) n :=
  Nat.div_lt_self (Nat.lt_of_lt_of_le Nat.zero_lt_two h) Nat.one_lt_two

end Omega.Nat
port_proof Nat.log2_terminates using Omega.Nat.halves

namespace Omega.Nat

/-- The reducible recursion step uses the decrease theorem at its current argument. -/
public abbrev log2_terminates._f (x : Nat) :
    ∀ (f : Nat.below (motive := fun n => Nat.le 2 n → Nat.lt (Nat.div n 2) n) x),
      Nat.le 2 x → Nat.lt (Nat.div x 2) x := fun _ => log2_terminates x

end Omega.Nat
port_definition Nat.log2 with_native_code
port_proof Nat.log2.eq_1 by_reflexivity
namespace Omega.Nat

private noncomputable abbrev steps (k n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun _ => Nat.zero)
    (fun _ ih x => Bool.rec (motive := fun _ => Nat) Nat.zero (Nat.succ (ih (Nat.div x twoN))) (Nat.ble twoN x)) k n

private theorem stepsZero (k : Nat) : Eq (steps k Nat.zero) Nat.zero :=
  Nat.casesOn (motive := fun i => Eq (steps i Nat.zero) Nat.zero) k rfl (fun _ => rfl)

private theorem log2_rec_irrel {n k k' : Nat} (hk : Nat.le n k) (hk' : Nat.le n k') :
    Eq (steps k n) (steps k' n) :=
  Nat.rec (motive := fun i => ∀ n j, Nat.le n i → Nat.le n j → Eq (steps i n) (steps j n))
    (fun _ j h _ => (stepsZero j).symm.trans (congrArg (fun x => steps j x) (Nat.le_zero.mp h).symm))
    (fun i ih n j h =>
      Nat.casesOn (motive := fun j => Nat.le n j → Eq (steps (Nat.succ i) n) (steps j n)) j
        (fun hz => (congrArg (fun x => steps (Nat.succ i) x) (Nat.le_zero.mp hz)).trans (stepsZero (Nat.succ i)))
        (fun j h' =>
          Bool.casesOn (motive := fun bit => Eq (Nat.ble twoN n) bit →
            Eq (Bool.rec (motive := fun _ => Nat) Nat.zero (Nat.succ (steps i (Nat.div n twoN))) bit)
              (Bool.rec (motive := fun _ => Nat) Nat.zero (Nat.succ (steps j (Nat.div n twoN))) bit))
            (Nat.ble twoN n) (fun _ => rfl) (fun e =>
              let dec := halves n (le_of_ble_eq_true e)
              congrArg Nat.succ (ih (Nat.div n twoN) j (Nat.le_of_lt_add_one (Nat.lt_of_lt_of_le dec h))
                (Nat.le_of_lt_add_one (Nat.lt_of_lt_of_le dec h')))) rfl)) k n k' hk hk'

private theorem unfoldLog (n : Nat) : Eq (log2 n)
    (@ite Nat (Nat.le twoN n) (Nat.decLe twoN n) (Nat.succ (log2 (Nat.div n twoN))) Nat.zero) :=
  Nat.casesOn (motive := fun n => Eq (log2 n)
    (@ite Nat (Nat.le twoN n) (Nat.decLe twoN n) (Nat.succ (log2 (Nat.div n twoN))) Nat.zero)) n rfl
    (fun i =>
      let m := Nat.succ i
      let q := Nat.div m twoN
      let step := fun bit => Bool.rec (motive := fun _ => Nat) Nat.zero (Nat.succ (steps i q)) bit
      Bool.casesOn (motive := fun bit => Eq (Nat.ble twoN m) bit →
        Eq (step bit) (@ite Nat (Nat.le twoN m) (Nat.decLe twoN m) (Nat.succ (log2 q)) Nat.zero))
        (Nat.ble twoN m)
        (fun e => (ite_eq_right (fun h => Bool.ne_false_of_eq_true (ble_eq_true_of_le h) e)).symm)
        (fun e =>
          let h := le_of_ble_eq_true e
          let compatible := log2_rec_irrel (Nat.le_of_lt_add_one (halves m h)) (Nat.le_refl q)
          (congrArg Nat.succ compatible).trans (ite_eq_left h).symm) rfl)

private theorem boundedSteps (k : Nat) : ∀ n, Nat.le (steps k n) k :=
  Nat.rec (motive := fun k => ∀ n, Nat.le (steps k n) k)
    (fun _ => Nat.le_refl Nat.zero)
    (fun i ih n => Bool.casesOn (motive := fun bit =>
      Nat.le (Bool.rec (motive := fun _ => Nat) Nat.zero (Nat.succ (steps i (Nat.div n twoN))) bit) (Nat.succ i))
      (Nat.ble twoN n) (Nat.zero_le _) (Nat.succ_le_succ (ih _))) k

private theorem boundedLog (n : Nat) : Nat.le (log2 n) n := boundedSteps n n

end Omega.Nat
port_proof Nat.log2_def using Omega.Nat.unfoldLog
port_proof Nat.log2_le_self using Omega.Nat.boundedLog

public section
namespace Nat
export _root_.Omega.Nat (log2 log2_def log2_le_self log2_terminates)
end Nat
