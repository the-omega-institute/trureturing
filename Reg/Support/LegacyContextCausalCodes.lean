import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Option

namespace Reg.Support.LegacyContextCausalCodes

/-- Lossless encodings of source data, independent of any proposition. -/
def contextCode (b : Bool × Bool × Bool) : Fin 8 :=
  Bool.rec
    (Bool.rec
      (Bool.rec ⟨Nat.zero, by decide⟩ ⟨(Nat.succ Nat.zero), by decide⟩ b.2.2)
      (Bool.rec ⟨(Nat.succ (Nat.succ Nat.zero)), by decide⟩ ⟨(Nat.succ (Nat.succ (Nat.succ Nat.zero))), by decide⟩ b.2.2) b.2.1)
    (Bool.rec
      (Bool.rec ⟨(Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))), by decide⟩ ⟨(Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero))))), by decide⟩ b.2.2)
      (Bool.rec ⟨(Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))), by decide⟩ ⟨(Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero))))))), by decide⟩ b.2.2) b.2.1) b.1

def contextDecode (i : Fin 8) : Bool × Bool × Bool :=
  match i.val with
  | 0 => (false, false, false)
  | 1 => (false, false, true)
  | 2 => (false, true, false)
  | 3 => (false, true, true)
  | 4 => (true, false, false)
  | 5 => (true, false, true)
  | 6 => (true, true, false)
  | _ => (true, true, true)

def contextEquiv : (Bool × Bool × Bool) ≃ Fin 8 where
  toFun := contextCode
  invFun := contextDecode
  left_inv := by decide +kernel
  right_inv := by decide +kernel

#print axioms contextEquiv
end Reg.Support.LegacyContextCausalCodes
