/- GID: D5/S3/Arith/FibonacciAtomic/ImmediateWindowStateCapacity
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/ImmediateWindowStateCapacity
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: High-to-low Fibonacci windows have exactly two observable residue fibers and one error state. -/

import D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd
import D5.S3.Arith.FibonacciAtomic.GraftAffineClosure
import D5.S0.Automata.DFAOStateLowerBound
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.ImmediateWindowStateCapacity

open D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd (Window first last)
open D5.S3.Arith.FibonacciAtomic.GraftAffineClosure (step quantity)
open D5.S0.Automata.DFAOStateLowerBound

/-- The three-bit clock is the third iterate of the Fibonacci step. -/
def clock {m : ℕ} (x : ZMod m × ZMod m) : ZMod m × ZMod m :=
  step (step (step x))

/-- Window bits have the low-to-high printed order of Definition 7.1. -/
def displacement {m : ℕ} : Window → ZMod m × ZMod m
  | .zero => (0, 0)
  | .low => (1, 0)
  | .middle => (0, 1)
  | .ends => (2, 1)
  | .high => (1, 1)

/-- The two observations are the present quantity and the next null-window quantity. -/
def windowObserve {m : ℕ} (x : ZMod m × ZMod m) : ZMod m × ZMod m :=
  (quantity x, quantity (clock x))

abbrev RawState (m : ℕ) := Option (Bool × (ZMod m × ZMod m))

/-- The seam checks the previous higher window's low bit against the next high bit. -/
def rawTransition {m : ℕ} : RawState m → Window → RawState m
  | none, _ => none
  | some (s, x), b =>
    if s && last b then none else some (first b, clock x + displacement b)

def rawOutput {m : ℕ} : RawState m → Option (ZMod m)
  | none => none
  | some (_, x) => some (quantity x)

/-- A total reader, including empty words, high-end null padding and absorbing errors. -/
def rawMachine (m : ℕ) : DFAO Window (Option (ZMod m)) (RawState m) where
  step := rawTransition
  start := some (false, (0, 0))
  accept := ∅
  output := rawOutput

/-- The task is the immediate modular quantity after every finite input word.
There is no End symbol and no nonzero-leading-window check. -/
def task (m : ℕ) (w : List Window) : Option (ZMod m) :=
  (rawMachine m).evalOutput w

/-- Only the actual image of the determinant-two observation is retained. -/
def Observation (m : ℕ) := Set.range (@windowObserve m)

abbrev SummaryState (m : ℕ) := Option (Bool × Observation m)

/-- Choose a representative solely to define a transition on the actual image. -/
noncomputable def representative {m : ℕ} (z : Observation m) : ZMod m × ZMod m :=
  Classical.choose z.property

/-- Reduction retains the historical seam, both observations, and the error label. -/
def reduce {m : ℕ} : RawState m → SummaryState m
  | none => none
  | some (s, x) => some (s, ⟨windowObserve x, ⟨x, rfl⟩⟩)

noncomputable def summaryTransition {m : ℕ} : SummaryState m → Window → SummaryState m
  | none, _ => none
  | some (s, z), b => reduce (rawTransition (some (s, representative z)) b)

def summaryOutput {m : ℕ} : SummaryState m → Option (ZMod m)
  | none => none
  | some (_, z) => some z.val.1

noncomputable def summaryMachine (m : ℕ) : DFAO Window (Option (ZMod m)) (SummaryState m) where
  step := summaryTransition
  start := reduce (some (false, (0, 0)))
  accept := ∅
  output := summaryOutput

/-- The exact state capacity; gcd accounts for the even-modulus observation kernel. -/
def capacity (m : ℕ) : ℕ := 2 * m ^ 2 / Nat.gcd m 2 + 1

#check IsAddCyclic.card_nsmulAddMonoidHom_range
#check nsmulAddMonoidHom
#check ZMod.card
#check Nat.card_zmod
#check Equiv.Perm.pow_apply
#check Equiv.Perm.iterate_eq_pow
#check DFA.evalFrom_of_append
#check DFA.evalFrom_cons
#check DFA.evalFrom_append_singleton
#check Function.iterate_succ_apply
#check Function.iterate_add_apply
#check Set.card_range
#check Nat.mul_div_assoc

end D5.S3.Arith.FibonacciAtomic.ImmediateWindowStateCapacity
