module
import all Init.Data.Array.Basic
public import Init.Data.UInt.Lemmas

namespace OmegaChecks.InitPort.Alternatives

private def anyEntry {m : Type → Type w} [Monad m] (size start stop : Nat)
    (run : Nat → Nat → m Bool) : m Bool :=
  if start < stop then
    let last := min stop size
    if start < last then run start last else pure false
  else pure false

private def anyStep {m : Type → Type w} [Monad m] (i last : USize)
    (test next : Unit → m Bool) : m Bool := do
  if i == last then pure false
  else if ← test () then pure true else next ()

private def anyLoop {α : Type u} {m : Type → Type w} [Monad m] (p : α → m Bool)
    (xs : Array α) (last : USize) (fuel : Nat) : USize → m Bool :=
  Nat.rec (fun _ => pure false) (fun _ next i =>
    anyStep i last (fun _ => if h : i.toNat < xs.size then p (xs.uget i h) else pure false)
      (fun _ => next (i+1))) fuel

/-- The word endpoint can coincide with the start before the natural endpoints coincide. -/
public def Array.anyMUnsafe {α : Type u} {m : Type → Type w} [Monad m]
    (p : α → m Bool) (xs : _root_.Array α) (start := 0) (stop := xs.size) : m Bool :=
  anyEntry xs.size start stop fun j last => anyLoop p xs (.ofNat last) (last - j) (.ofNat j)

end OmegaChecks.InitPort.Alternatives
