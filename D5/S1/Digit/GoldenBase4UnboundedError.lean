/- GID: D5/S1/Digit/GoldenBase4UnboundedError
   generality: I
   mirror-B: D5/B/S1/Digit/GoldenBase4UnboundedError
   mirror-E: none(waiver:finite-separation-and-pumping-certificate)
   anchors: []
   digest: Every anchored typed machine with fewer than twenty-one states has arithmetic errors on legal words with arbitrarily many nonzero digits. -/

import D5.S1.Digit.GoldenBase4IntervalMachine

/- The reference table and all run semantics are reused. The conclusion concerns
   legal integer inputs, not necessarily powers of four. It rules out bounded
   Hamming-weight disagreement as a way of certifying a smaller powers-only
   machine. No analytic or Diophantine theorem is postulated or imported here.
   Proof scripts are supplied for logical review; Lean was not run in this session. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Digit.GoldenBase4UnboundedError

open D5.S0.Automata.TypedPartialDFAOOverBase
open D5.S1.Digit.GoldenBase4IntervalMachine

private def core (i : Fin 20) : Fin 21 := ⟨i.val + 1, by omega⟩

private def accessTail : Fin 20 → List (Fin 2) :=
  ![[0,1,0,1,0,0], [0,1,0,0], [0,0], [0,0,1,0,0],
    [0,0,0,0], [0,0,0,0,0], [0,0,0], [0,1,0,0,0],
    [0,0,1,0], [0], [0,0,0,1,0], [0,1,0], [0,1,0,1,0],
    [0,1,0,1], [0,1], [0,0,1,0,1], [0,0,0,1], [],
    [0,0,1], [0,1,0,1,0,0,1]]

private def suffix : Fin 13 → List (Fin 2) :=
  ![[], [0], [1], [1,0,1], [0,0,1,0], [0,1], [1,0],
    [0,0,1], [0,1,0], [1,0,0,1], [0,0,0,1,0],
    [0,1,0,0,1], [1,0,1,0,0,1]]

private theorem access_certificate : ∀ i : Fin 20,
    machine.runFrom 18 (accessTail i) = some (core i) := by decide

private theorem zero_moves_core : ∀ i : Fin 20,
    zeroTarget (core i) ≠ core i := by decide

private theorem separation_certificate : ∀ q t : Fin 21,
    machine.stateType q = machine.stateType t → q ≠ t →
    ∃ j : Fin 13,
      machine.runFrom q (suffix j) ≠ none ∧
      machine.runFrom t (suffix j) ≠ none ∧
      (machine.runFrom q (suffix j)).map output ≠
        (machine.runFrom t (suffix j)).map output := by decide

private def cycleWord : List (Fin 2) := [0,0,0,0,1]

private def pump : Nat → List (Fin 2)
  | 0 => [1]
  | k + 1 => pump k ++ cycleWord

private theorem pump_count (k : Nat) : (pump k).count 1 = k + 1 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [pump, cycleWord, List.count_append, ih, Nat.add_assoc]

private theorem run_append_of_run {Q : Type*}
    (M : TypedPartialDFAO binaryZeckendorfBase (Fin 4) Q)
    {w : List (Fin 2)} {q : Q} (h : M.run w = some q)
    (v : List (Fin 2)) : M.run (w ++ v) = M.runFrom q v := by
  change M.runFrom M.start (w ++ v) = _
  rw [M.runFrom_append, show M.runFrom M.start w = some q from h]
  rfl

private theorem output_append_of_run {Q : Type*}
    (M : TypedPartialDFAO binaryZeckendorfBase (Fin 4) Q)
    {w : List (Fin 2)} {q : Q} (h : M.run w = some q)
    (v : List (Fin 2)) :
    M.evalOutput (w ++ v) = (M.runFrom q v).map M.output := by
  change (M.run (w ++ v)).map M.output = _
  rw [run_append_of_run M h v]

private theorem run_pump (k : Nat) : machine.run (pump k) = some 18 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [pump, run_append_of_run machine ih]
      rfl

private def accessWord (k : Nat) (i : Fin 20) : List (Fin 2) :=
  pump k ++ accessTail i

private theorem run_accessWord (k : Nat) (i : Fin 20) :
    machine.run (accessWord k i) = some (core i) := by
  rw [accessWord, run_append_of_run machine (run_pump k)]
  exact access_certificate i

private theorem accessWord_weight (k : Nat) (i : Fin 20) :
    k < (accessWord k i).count 1 := by
  simp only [accessWord, List.count_append, pump_count]
  omega

private theorem successful_types {Q : Type*}
    (M : TypedPartialDFAO binaryZeckendorfBase (Fin 4) Q)
    {w : List (Fin 2)} {q : Fin 21} {t : Q}
    (hr : machine.run w = some q) (hm : M.run w = some t) :
    machine.stateType q = M.stateType t := by
  have h1 := machine.runFrom_type
    (show machine.runFrom machine.start w = some q from hr)
  have h2 := M.runFrom_type (show M.runFrom M.start w = some t from hm)
  rw [machine.start_type] at h1
  rw [M.start_type] at h2
  exact Option.some.inj (h1.symm.trans h2)

private theorem some_of_ne_none {Q : Type*} {x : Option Q} (h : x ≠ none) :
    ∃ q, x = some q := by
  cases x with
  | none => exact False.elim (h rfl)
  | some q => exact ⟨q, rfl⟩

/-- Above a supplied nonzero-digit threshold, identical candidate states cannot
represent different states of the exact reference table. -/
theorem high_weight_collision {Q : Type*}
    (M : TypedPartialDFAO binaryZeckendorfBase (Fin 4) Q) (k : Nat)
    (agree : ∀ w : List (Fin 2), k < w.count 1 →
      (∃ q, machine.run w = some q) → M.evalOutput w = machine.evalOutput w)
    (x y : List (Fin 2)) (q t : Fin 21) (u : Q)
    (hx : k < x.count 1) (hy : k < y.count 1)
    (hrx : machine.run x = some q) (hry : machine.run y = some t)
    (hmx : M.run x = some u) (hmy : M.run y = some u) : q = t := by
  by_contra hne
  have ht : machine.stateType q = machine.stateType t :=
    (successful_types M hrx hmx).trans (successful_types M hry hmy).symm
  obtain ⟨j, hq, ht', hd⟩ := separation_certificate q t ht hne
  obtain ⟨q', hq'⟩ := some_of_ne_none hq
  obtain ⟨t', ht''⟩ := some_of_ne_none ht'
  have hxr : machine.run (x ++ suffix j) = some q' := by
    rw [run_append_of_run machine hrx]
    exact hq'
  have hyr : machine.run (y ++ suffix j) = some t' := by
    rw [run_append_of_run machine hry]
    exact ht''
  have hxa := agree (x ++ suffix j) (by simp only [List.count_append]; omega) ⟨q', hxr⟩
  have hya := agree (y ++ suffix j) (by simp only [List.count_append]; omega) ⟨t', hyr⟩
  apply hd
  calc
    (machine.runFrom q (suffix j)).map output = machine.evalOutput (x ++ suffix j) :=
      (output_append_of_run machine hrx _).symm
    _ = M.evalOutput (x ++ suffix j) := hxa.symm
    _ = M.evalOutput (y ++ suffix j) := by
      rw [output_append_of_run M hmx, output_append_of_run M hmy]
    _ = machine.evalOutput (y ++ suffix j) := hya
    _ = (machine.runFrom t (suffix j)).map output :=
      output_append_of_run machine hry _

/-- Agreement outside a bounded-nonzero-digit language already requires all
21 states when the initial zero self-loop is retained. No powers-only premise
is substituted for this stronger agreement premise. -/
theorem bounded_error_weight_requires_twenty_one {Q : Type*} [Fintype Q]
    (M : TypedPartialDFAO binaryZeckendorfBase (Fin 4) Q)
    (zeroLoop : M.step M.start 0 = some M.start) (k : Nat)
    (agree : ∀ w : List (Fin 2), k < w.count 1 →
      (∃ q, machine.run w = some q) → M.evalOutput w = machine.evalOutput w) :
    21 ≤ Fintype.card Q := by
  classical
  have realized : ∀ i : Fin 20, ∃ q, M.run (accessWord k i) = some q := by
    intro i
    have h := agree (accessWord k i) (accessWord_weight k i)
      ⟨core i, run_accessWord k i⟩
    change (M.run (accessWord k i)).map M.output =
      (machine.run (accessWord k i)).map output at h
    rw [run_accessWord] at h
    obtain ⟨q, hq, _⟩ := Option.map_eq_some_iff.mp h
    exact ⟨q, hq⟩
  let f : Fin 20 → Q := fun i => Classical.choose (realized i)
  have hf (i : Fin 20) : M.run (accessWord k i) = some (f i) :=
    Classical.choose_spec (realized i)
  have hi : Function.Injective f := by
    intro i j hij
    have hr := high_weight_collision M k agree (accessWord k i) (accessWord k j)
      (core i) (core j) (f i) (accessWord_weight k i) (accessWord_weight k j)
      (run_accessWord k i) (run_accessWord k j) (hf i) (by rw [hij]; exact hf j)
    apply Fin.ext
    have hv := congrArg Fin.val hr
    simp only [core] at hv
    omega
  have hs (i : Fin 20) : f i ≠ M.start := by
    intro he
    have hm : M.run (accessWord k i) = some M.start := by rw [← he]; exact hf i
    have hm0 : M.run (accessWord k i ++ [0]) = some M.start := by
      rw [run_append_of_run M hm]
      simp [TypedPartialDFAO.runFrom, runTransition, zeroLoop]
    have hr0 : machine.run (accessWord k i ++ [0]) = some (zeroTarget (core i)) := by
      rw [run_append_of_run machine (run_accessWord k i)]
      rfl
    have hh : k < (accessWord k i ++ [0]).count 1 := by
      simp only [List.count_append]
      have := accessWord_weight k i
      omega
    have heq := high_weight_collision M k agree
      (accessWord k i) (accessWord k i ++ [0])
      (core i) (zeroTarget (core i)) M.start
      (accessWord_weight k i) hh (run_accessWord k i) hr0 hm hm0
    exact zero_moves_core i heq.symm
  let g : Option (Fin 20) → Q
    | none => M.start
    | some i => f i
  have hg : Function.Injective g := by
    intro a b hab
    cases a with
    | none =>
        cases b with
        | none => rfl
        | some j => exact False.elim (hs j hab.symm)
    | some i =>
        cases b with
        | none => exact False.elim (hs i hab)
        | some j => exact congrArg some (hi hab)
  have card := Fintype.card_le_of_injective g hg
  simpa using card

/-- Every anchored candidate below 21 states has errors on successful legal
reference inputs with arbitrarily many ones. These inputs need not be powers. -/
theorem small_machine_unbounded_error_weight {Q : Type*} [Fintype Q]
    (M : TypedPartialDFAO binaryZeckendorfBase (Fin 4) Q)
    (zeroLoop : M.step M.start 0 = some M.start)
    (small : Fintype.card Q < 21) (k : Nat) :
    ∃ w : List (Fin 2), ∃ q : Fin 21,
      k < w.count 1 ∧ machine.run w = some q ∧
        M.evalOutput w ≠ some (output q) := by
  classical
  by_contra hn
  have agree : ∀ w : List (Fin 2), k < w.count 1 →
      (∃ q, machine.run w = some q) → M.evalOutput w = machine.evalOutput w := by
    intro w hw hr
    obtain ⟨q, hq⟩ := hr
    have he : M.evalOutput w = some (output q) := by
      by_contra hd
      exact hn ⟨w, q, hw, hq, hd⟩
    simpa [TypedPartialDFAO.evalOutput, hq] using he
  exact (Nat.not_lt_of_ge (bounded_error_weight_requires_twenty_one M zeroLoop k agree)) small

/-- The mismatched label is the true radix-four arithmetic output of the
Fibonacci-weighted input, by the existing interval-machine theorem. -/
theorem small_machine_unbounded_arithmetic_errors {Q : Type*} [Fintype Q]
    (M : TypedPartialDFAO binaryZeckendorfBase (Fin 4) Q)
    (zeroLoop : M.step M.start 0 = some M.start)
    (small : Fintype.card Q < 21) (k : Nat) :
    ∃ w : List (Fin 2), ∃ q : Fin 21,
      k < w.count 1 ∧ machine.run w = some q ∧
      M.evalOutput w ≠ some (output q) ∧
      ⌊4 * (Real.goldenRatio * (fibPair w).1)⌋ -
        4 * ⌊Real.goldenRatio * (fibPair w).1⌋ = ((output q).val : Int) := by
  obtain ⟨w, q, hw, hr, he⟩ := small_machine_unbounded_error_weight M zeroLoop small k
  exact ⟨w, q, hw, hr, he, successful_run_digit w q hr⟩

#print axioms bounded_error_weight_requires_twenty_one
#print axioms small_machine_unbounded_arithmetic_errors

end D5.S1.Digit.GoldenBase4UnboundedError
