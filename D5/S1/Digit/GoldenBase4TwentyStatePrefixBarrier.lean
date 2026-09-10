/- GID: D5/S1/Digit/GoldenBase4TwentyStatePrefixBarrier
   generality: I
   mirror-B: D5/B/S1/Digit/GoldenBase4TwentyStatePrefixBarrier
   mirror-E: none(waiver:explicit-finite-prefix-witness)
   anchors: []
   utility: none
   digest: An explicit twenty-state typed machine fits every power index below 367 and first fails at 367, so no dictionary confined to that prefix can establish a twenty-one-state lower bound. -/

import D5.S1.Digit.GoldenBase4DenseInput

/- This is a finite-prefix obstruction to an insufficient lower-bound dataset,
   not an all-powers upper construction. Machine semantics and the original
   M01 input/digit functions are reused. The table was found by identifying
   reference states 2 and 3 and keeping the zero successor of state 2, which
   changes transitions and is not a behavior-preserving reference quotient.
   The finite checks below use certified bounded Zeckendorf computation. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Digit.GoldenBase4TwentyStatePrefixBarrier

open D5.S0.Automata.TypedPartialDFAOOverBase
open D5.S1.Digit.GoldenBase4AutomataOracle

/-- The thirteen previous-zero rows and seven previous-one rows. -/
def stateType (q : Fin 20) : BinaryZeckendorfState :=
  if q.val < 13 then .previousZero else .previousOne

/-- Zero successors of the explicit finite-prefix witness. -/
def zeroTarget : Fin 20 → Fin 20 :=
  ![0,8,7,6,5,4,4,3,3,2,2,2,1,12,11,11,10,9,8,8]

/-- One successors; unused entries remain hidden behind the type guard. -/
def oneTarget : Fin 20 → Fin 20 :=
  ![17,19,18,17,17,17,16,16,15,14,14,13,13,0,0,0,0,0,0,0]

/-- The output is always a base-four digit. -/
def output : Fin 20 → Fin 4 :=
  ![0,3,3,3,3,0,0,0,0,0,1,1,1,1,1,2,2,2,2,3]

/-- Every legal symbol has a successor; consecutive ones remain undefined. -/
def step (q : Fin 20) (a : Fin 2) : Option (Fin 20) :=
  if a = 0 then some (zeroTarget q)
  else if q.val < 13 then some (oneTarget q) else none

/-- A concrete machine in the same candidate class as the original problem. -/
def machine : TypedPartialDFAO binaryZeckendorfBase (Fin 4) (Fin 20) where
  start := 0
  stateType := stateType
  step := step
  output := output
  start_type := rfl
  step_type := by decide

-- A descending scan avoids the canonical algorithm's input-sized search bound.
private def boundedDigits : Nat → Nat → Nat → Nat → List Nat
  | 0, _, _, _ => []
  | k + 1, n, f, g =>
    if f ≤ n then (k + 2) :: boundedDigits k (n - f) (g - f) f
    else boundedDigits k n (g - f) f

private theorem boundedDigits_eq (k n : Nat) (bound : n < Nat.fib (k + 2)) :
    boundedDigits k n (Nat.fib (k + 1)) (Nat.fib (k + 2)) = Nat.zeckendorf n := by
  induction k generalizing n with
  | zero =>
    have : n = 0 := by norm_num at bound; omega
    subst n
    simp [boundedDigits]
  | succ k ih =>
    change n < Nat.fib (k + 3) at bound
    have recurrence : Nat.fib (k + 3) = Nat.fib (k + 1) + Nat.fib (k + 2) :=
      Nat.fib_add_two
    have monotone : Nat.fib (k + 1) ≤ Nat.fib (k + 2) := Nat.fib_mono (by omega)
    have difference : Nat.fib (k + 3) - Nat.fib (k + 2) = Nat.fib (k + 1) := by omega
    change boundedDigits (k + 1) n (Nat.fib (k + 2)) (Nat.fib (k + 3)) = _
    simp only [boundedDigits, difference]
    split_ifs with hn
    · have greatest : Nat.greatestFib n = k + 2 := by
        have lower := Nat.le_greatestFib.mpr hn
        have upper := Nat.greatestFib_lt.mpr bound
        omega
      have positive : 0 < n := by
        have hf : 0 < Nat.fib (k + 2) := Nat.fib_pos.mpr (by omega)
        omega
      have remainder : n - Nat.fib (k + 2) < Nat.fib (k + 2) := by omega
      rw [Nat.zeckendorf_of_pos positive, greatest, ih _ remainder]
    · exact ih n (by omega)

private def powerDigits (n : Nat) : List Nat :=
  boundedDigits (3 * n + 2) (4 ^ n) (Nat.fastFib (3 * n + 3)) (Nat.fastFib (3 * n + 4))

private theorem powerDigits_bound (n : Nat) : 4 ^ n < Nat.fib (3 * n + 4) := by
  have lower : ∀ n : Nat, 4 ^ n ≤ Nat.fib (3 * n + 2) := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ih =>
      have h1 := Nat.fib_add_two (n := 3 * n)
      have h2 := Nat.fib_add_two (n := 3 * n + 1)
      have h3 := Nat.fib_add_two (n := 3 * n + 2)
      have h4 := Nat.fib_add_two (n := 3 * n + 3)
      have hm := Nat.fib_mono (show 3 * n ≤ 3 * n + 1 by omega)
      norm_num only [Nat.add_assoc] at h2 h3 h4
      rw [pow_succ]
      rw [show 3 * (n + 1) + 2 = 3 * n + 5 by omega]
      omega
  have h := lower n
  have recurrence := Nat.fib_add_two (n := 3 * n + 2)
  norm_num only [Nat.add_assoc] at recurrence
  have positive : 0 < Nat.fib (3 * n + 3) := Nat.fib_pos.mpr (by omega)
  omega

private theorem powerDigits_eq (n : Fin 368) :
    powerDigits n.val = D5.S0.Conventions.wdigits (4 ^ n.val) := by
  simpa only [powerDigits, Nat.fastFib_eq, D5.S0.Conventions.wdigits] using
    boundedDigits_eq (3 * n.val + 2) (4 ^ n.val) (powerDigits_bound n.val)

private def boundedWord : Nat → Nat → Nat → Nat → List (Fin 2)
  | 0, _, _, _ => []
  | k + 1, n, f, g =>
    if f ≤ n then 1 :: boundedWord k (n - f) (g - f) f
    else 0 :: boundedWord k n (g - f) f

private theorem boundedDigits_lt (k n f g i : Nat) (hi : i ∈ boundedDigits k n f g) :
    i < k + 2 := by
  induction k generalizing n f g with
  | zero => simp [boundedDigits] at hi
  | succ k ih =>
    simp only [boundedDigits] at hi
    split_ifs at hi with h
    · rcases List.mem_cons.mp hi with rfl | hi
      · omega
      · have := ih _ _ _ hi; omega
    · have := ih _ _ _ hi; omega

private theorem boundedWord_eq (k n f g : Nat) :
    boundedWord k n f g = (List.range k).reverse.map
      (fun i => if i + 2 ∈ boundedDigits k n f g then (1 : Fin 2) else 0) := by
  induction k generalizing n f g with
  | zero => simp [boundedWord]
  | succ k ih =>
    simp only [boundedWord, boundedDigits, List.range_succ, List.reverse_append,
      List.reverse_singleton, List.map_cons, List.cons_append,
      List.nil_append]
    by_cases h : f ≤ n
    · simp only [if_pos h, List.mem_cons, true_or, ite_true, ih]
      congr 1
      apply List.map_congr_left
      intro i hi
      have hil : i < k := List.mem_range.mp (List.mem_reverse.mp hi)
      simp [show i ≠ k by omega]
    · have absent : k + 2 ∉ boundedDigits k n (g - f) f := by
        intro hi
        have := boundedDigits_lt k n (g - f) f (k + 2) hi
        omega
      simp only [if_neg h, absent, ite_false, ih]

private def powerWord (n : Nat) : List (Fin 2) :=
  let digits := powerDigits n
  let len := match digits with
    | [] => 1
    | largest :: _ => largest - 1
  boundedWord len (4 ^ n) (Nat.fastFib (len + 1)) (Nat.fastFib (len + 2))

private theorem powerWord_eq (n : Fin 368) : powerWord n.val = base4PowerWord n.val := by
  have positive : 0 < 4 ^ n.val := pow_pos (by decide) _
  have greatest : 2 ≤ Nat.greatestFib (4 ^ n.val) := by
    apply Nat.le_greatestFib.mpr
    norm_num
    omega
  have digits := Nat.zeckendorf_of_pos positive
  have bound : 4 ^ n.val < Nat.fib (Nat.greatestFib (4 ^ n.val) - 1 + 2) := by
    rw [show Nat.greatestFib (4 ^ n.val) - 1 + 2 = Nat.greatestFib (4 ^ n.val) + 1 by omega]
    exact Nat.lt_fib_greatestFib_add_one (4 ^ n.val)
  simp only [powerWord, powerDigits_eq n, D5.S0.Conventions.wdigits, digits,
    Nat.fastFib_eq, boundedWord_eq, boundedDigits_eq _ _ bound,
    base4PowerWord, zeckendorfMSDWord, zeckendorfWordLength]
  apply List.map_congr_left
  intro i _
  simp only [zeckendorfBit, D5.S0.Conventions.wdigits, digits]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
private theorem agrees_before_367 : ∀ n : Fin 367,
    machine.evalOutput (base4PowerWord n.val) =
      GoldenBase4IntervalMachine.machine.evalOutput (base4PowerWord n.val) := by
  have h : ∀ n : Fin 367, machine.evalOutput (powerWord n.val) =
      GoldenBase4IntervalMachine.machine.evalOutput (powerWord n.val) := by
    decide +kernel
  intro n
  simpa only [powerWord_eq ⟨n.val, by omega⟩] using h n

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
private theorem reference_at_367 :
    GoldenBase4IntervalMachine.machine.evalOutput (base4PowerWord 367) =
      some (0 : Fin 4) := by
  rw [← powerWord_eq ⟨367, by decide⟩]
  decide +kernel

/-- Every original power input with index below 367 is computed correctly. -/
theorem correct_before_367 (n : Nat) (hn : n < 367) :
    machine.evalOutput (base4PowerWord n) = some (base4GoldenDigit n) := by
  exact (agrees_before_367 ⟨n, hn⟩).trans
    (GoldenBase4DenseInput.base4PowerWord_correct n)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
/-- At index 367 the concrete twenty-state table emits one. -/
theorem output_at_367 :
    machine.evalOutput (base4PowerWord 367) = some (1 : Fin 4) := by
  rw [← powerWord_eq ⟨367, by decide⟩]
  decide +kernel

/-- The original exact arithmetic oracle has digit zero at index 367. -/
theorem true_digit_at_367 : base4GoldenDigit 367 = 0 := by
  have h := GoldenBase4DenseInput.base4PowerWord_correct 367
  rw [reference_at_367] at h
  exact (Option.some.inj h).symm

/-- This finite-prefix witness is not a solution of the infinite problem. -/
theorem fails_at_367 :
    machine.evalOutput (base4PowerWord 367) ≠ some (base4GoldenDigit 367) := by
  rw [output_at_367, true_digit_at_367]
  decide

/-- Every failure of this witness is at least the explicitly attained index. -/
theorem no_earlier_failure (n : Nat)
    (bad : machine.evalOutput (base4PowerWord n) ≠ some (base4GoldenDigit n)) :
    367 ≤ n := by
  by_contra h
  exact bad (correct_before_367 n (by omega))

/-- Both published initial anchors hold, including the leading-zero loop. -/
theorem initial_anchors :
    machine.step machine.start 0 = some machine.start ∧ machine.output machine.start = 0 :=
  ⟨rfl, rfl⟩

/-- Every collection of observations confined to indices below 367 has a
20-state witness. This includes the original 79 rows and the 144 gap4 rows.
The indices may repeat and the collection may be described by any index type. -/
theorem every_subprefix_has_twenty_state_witness {I : Type*}
    (index : I → Nat) (small : ∀ i, index i < 367) :
    ∃ M : TypedPartialDFAO binaryZeckendorfBase (Fin 4) (Fin 20),
      (∀ i, M.evalOutput (base4PowerWord (index i)) = some (base4GoldenDigit (index i))) ∧
      M.step M.start 0 = some M.start ∧ M.output M.start = 0 := by
  exact ⟨machine, fun i => correct_before_367 (index i) (small i), initial_anchors⟩

#print axioms correct_before_367
#print axioms fails_at_367
#print axioms every_subprefix_has_twenty_state_witness

end D5.S1.Digit.GoldenBase4TwentyStatePrefixBarrier
