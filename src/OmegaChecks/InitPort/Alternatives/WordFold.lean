module
public import Init.Data.Array.Basic
public import Init.Data.ByteArray.Basic
public import Init.Data.FloatArray.Basic

namespace OmegaChecks.InitPort.Alternatives

private def foldEntry {β : Type v} {m : Type v → Type w} [Monad m] (size start stop : Nat)
    (init : β) (run : Nat → Nat → β → m β) : m β :=
  if start < stop then
    if stop ≤ size then run start stop init
    else if start < size then run start size init
    else pure init
  else pure init

private def foldStep {β : Type v} {m : Type v → Type w} [Monad m] (i last : USize)
    (b : β) (update : Unit → m β) (next : β → m β) : m β := do
  if i == last then pure b else next (← update ())

private def foldLoop {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m]
    (size : Nat) (get : (i : USize) → i.toNat < size → α) (f : β → α → m β)
    (address advance : USize → USize) (last : USize) (fuel : Nat) : USize → β → m β :=
  Nat.rec (fun _ b => pure b) (fun _ next i b =>
    foldStep i last b (fun _ => if h : (address i).toNat < size then f b (get (address i) h) else pure b)
      (fun c => next (advance i) c)) fuel

private def wordFold {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m]
    (size : Nat) (get : (i : USize) → i.toNat < size → α) (f : β → α → m β)
    (b : β) (start stop : Nat) : m β :=
  foldEntry size start stop b fun j last => foldLoop size get f id (· + 1) (.ofNat last) (last-j) (.ofNat j)

private def wordFoldRight {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m]
    (size : Nat) (get : (i : USize) → i.toNat < size → α) (f : β → α → m β)
    (b : β) (start stop : Nat) : m β :=
  let run (j last : Nat) := foldLoop size get f (· - 1) (· - 1) (.ofNat last) (j-last) (.ofNat j) b
  if start ≤ size then
    if stop < start then run start stop else pure b
  else if stop < size then run size stop
  else pure b

public def Array.foldrMUnsafe {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m]
    (f : α → β → m β) (init : β) (xs : _root_.Array α) (start := xs.size) (stop := 0) : m β :=
  wordFoldRight xs.size xs.uget (fun b a => f a b) init start stop

public def Array.foldlMUnsafe {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m]
    (f : β → α → m β) (init : β) (xs : _root_.Array α) (start := 0) (stop := xs.size) : m β :=
  wordFold xs.size xs.uget f init start stop

public def ByteArray.foldlMUnsafe {β : Type v} {m : Type v → Type w} [Monad m]
    (f : β → UInt8 → m β) (init : β) (xs : _root_.ByteArray) (start := 0) (stop := xs.size) : m β :=
  wordFold xs.size (fun i h => xs.uget i h) f init start stop

public def FloatArray.foldlMUnsafe {β : Type v} {m : Type v → Type w} [Monad m]
    (f : β → Float → m β) (init : β) (xs : _root_.FloatArray) (start := 0) (stop := xs.size) : m β :=
  wordFold xs.size xs.uget f init start stop

end OmegaChecks.InitPort.Alternatives
