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

/-- The image reader simulates every word, including continuations from errors. -/
private theorem simulation (m : ℕ) (w : List Window) (q : RawState m) :
    (summaryMachine m).toDFA.evalFrom (reduce q) w =
      reduce ((rawMachine m).toDFA.evalFrom q w) := by
  have observed_step (x y d : ZMod m × ZMod m)
      (h : windowObserve x = windowObserve y) :
      windowObserve (clock x + d) = windowObserve (clock y + d) := by
    have hu := congrArg Prod.fst h
    have hv := congrArg Prod.snd h
    dsimp [windowObserve, clock, step, quantity] at hu hv ⊢
    apply Prod.ext
    · dsimp
      linear_combination hv
    · dsimp
      linear_combination hu + 4 * hv
  have commute (q : RawState m) (b : Window) :
      summaryTransition (reduce q) b = reduce (rawTransition q b) := by
    cases q with
    | none => rfl
    | some q =>
      rcases q with ⟨s, x⟩
      have hr : windowObserve (representative ⟨windowObserve x, ⟨x, rfl⟩⟩) =
          windowObserve x := Classical.choose_spec (show windowObserve x ∈
            Set.range (@windowObserve m) from ⟨x, rfl⟩)
      by_cases h : (s && last b) = true
      · simp [reduce, summaryTransition, rawTransition, h]
      · simp only [reduce, summaryTransition, rawTransition, h, ↓reduceIte]
        exact congrArg (fun z : Observation m => some (first b, z))
          (Subtype.ext (observed_step _ _ _ hr))
  induction w generalizing q with
  | nil => rfl
  | cons b w ih =>
    rw [DFA.evalFrom_cons, DFA.evalFrom_cons]
    change (summaryMachine m).toDFA.evalFrom (summaryTransition (reduce q) b) w = _
    rw [commute]
    exact ih _

/-- Every raw residue state is reached by an actual forward window word. -/
private theorem raw_reachable (m : ℕ) [NeZero m] (q : RawState m) :
    ∃ w : List Window, (rawMachine m).toDFA.eval w = q := by
  classical
  let Reach (x : ZMod m × ZMod m) : Prop :=
    ∃ w : List Window, (rawMachine m).toDFA.eval w = some (false, x)
  let p (d : ZMod m × ZMod m) : Equiv.Perm (ZMod m × ZMod m) := {
    toFun x := clock x + d
    invFun y := (-3 * (y.1 - d.1) + 2 * (y.2 - d.2),
      2 * (y.1 - d.1) - (y.2 - d.2))
    left_inv x := by ext <;> simp [clock, step] <;> ring
    right_inv y := by ext <;> simp [clock, step] <;> ring
  }
  have forward (b : Window) (hb : first b = false) (x : ZMod m × ZMod m)
      (hx : Reach x) : Reach (p (displacement b) x) := by
    obtain ⟨w, hw⟩ := hx
    refine ⟨w ++ [b], ?_⟩
    change (rawMachine m).toDFA.evalFrom _ (w ++ [b]) = _
    rw [DFA.evalFrom_append_singleton]
    change rawTransition ((rawMachine m).toDFA.eval w) b = _
    rw [hw]
    simp [rawTransition, hb, p]
  have iterate_forward (b : Window) (hb : first b = false) (n : ℕ)
      (x : ZMod m × ZMod m) (hx : Reach x) : Reach ((p (displacement b) ^ n) x) := by
    induction n with
    | zero => simpa using hx
    | succ n ih =>
      simpa only [pow_succ', Equiv.Perm.mul_apply] using forward b hb _ ih
  have inverse_forward (b : Window) (hb : first b = false)
      (x : ZMod m × ZMod m) (hx : Reach x) :
      Reach ((p (displacement b)).symm x) := by
    let P := p (displacement b)
    have hp : P ^ (orderOf P - 1) = P⁻¹ := by
      apply mul_right_cancel (b := P)
      rw [← pow_succ, Nat.sub_add_cancel (orderOf_pos P), pow_orderOf_eq_one,
        inv_mul_cancel]
    have h := iterate_forward b hb (orderOf P - 1) x hx
    rw [show p (displacement b) ^ (orderOf P - 1) =
      (p (displacement b))⁻¹ from hp] at h
    exact h
  have plus_beta (x : ZMod m × ZMod m) (hx : Reach x) : Reach (x + (0, 1)) := by
    have h := forward .middle rfl _ (inverse_forward .zero rfl x hx)
    convert h using 1 <;> ext <;> simp [p, clock, step, displacement] <;> ring
  have plus_alpha (x : ZMod m × ZMod m) (hx : Reach x) : Reach (x + (1, 0)) := by
    have h := forward .high rfl _ (inverse_forward .middle rfl x hx)
    convert h using 1 <;> ext <;> simp [p, clock, step, displacement] <;> ring
  have zero_reach : Reach (0, 0) := ⟨[], rfl⟩
  have alpha_reach (n : ℕ) : Reach ((n : ZMod m), 0) := by
    induction n with
    | zero => simpa using zero_reach
    | succ n ih => simpa using plus_alpha _ ih
  have pair_reach (n k : ℕ) : Reach ((n : ZMod m), (k : ZMod m)) := by
    induction k with
    | zero => simpa using alpha_reach n
    | succ k ih => simpa using plus_beta _ ih
  have all_zero_seam (x : ZMod m × ZMod m) : Reach x := by
    simpa using pair_reach x.1.val x.2.val
  cases q with
  | none => exact ⟨[.low, .high], rfl⟩
  | some q =>
    rcases q with ⟨s, x⟩
    cases s with
    | false => exact all_zero_seam x
    | true =>
      obtain ⟨w, hw⟩ := all_zero_seam ((p (displacement .low)).symm x)
      refine ⟨w ++ [.low], ?_⟩
      change (rawMachine m).toDFA.evalFrom _ (w ++ [.low]) = _
      rw [DFA.evalFrom_append_singleton]
      change rawTransition ((rawMachine m).toDFA.eval w) .low = _
      rw [hw]
      change some (true, (p (displacement .low)) ((p (displacement .low)).symm x)) = _
      rw [Equiv.apply_symm_apply]

end D5.S3.Arith.FibonacciAtomic.ImmediateWindowStateCapacity
