module
public import Init.Data.Array.Basic
public import Init.Data.ByteArray.Basic
public import Init.Data.FloatArray.Basic

namespace OmegaChecks.InitPort.Alternatives

private def forInStep {β : Type v} {m : Type v → Type w} [Monad m] (i limit : USize) (b : β)
    (action : Unit → m (ForInStep β)) (next : β → m β) : m β := do
  if i < limit then
    match ← action () with
    | .done c => pure c
    | .yield c => next c
  else pure b

private def wordForIn {β : Type v} {m : Type v → Type w} [Monad m] (size : Nat) (limit : USize)
    (action : (i : USize) → i.toNat < size → β → m (ForInStep β)) (fuel : Nat) : USize → β → m β :=
  Nat.rec (fun _ b => pure b) (fun _ next i b =>
    forInStep i limit b
      (fun _ => if h : i.toNat < size then action i h b else pure (.done b))
      (fun c => next (i+1) c)) fuel

public def Array.forIn'Unsafe {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m]
    (xs : _root_.Array α) (b : β) (f : (a : α) → a ∈ xs → β → m (ForInStep β)) : m β :=
  wordForIn xs.size xs.usize (fun i h => f (xs.uget i h) (_root_.Array.getElem_mem h))
    xs.usize.toNat 0 b

public def ByteArray.forInUnsafe {β : Type v} {m : Type v → Type w} [Monad m]
    (xs : _root_.ByteArray) (b : β) (f : UInt8 → β → m (ForInStep β)) : m β :=
  wordForIn xs.size xs.usize (fun i h => f (xs.uget i h)) xs.usize.toNat 0 b

public def FloatArray.forInUnsafe {β : Type v} {m : Type v → Type w} [Monad m]
    (xs : _root_.FloatArray) (b : β) (f : Float → β → m (ForInStep β)) : m β :=
  wordForIn xs.size xs.usize (fun i h => f (xs.uget i h)) xs.usize.toNat 0 b

end OmegaChecks.InitPort.Alternatives
