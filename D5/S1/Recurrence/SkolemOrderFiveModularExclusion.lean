/- GID: D5/S1/Recurrence/SkolemOrderFiveModularExclusion
   generality: I
   mirror-B: D5/B/S1/Recurrence/SkolemOrderFiveModularExclusion
   mirror-E: none(waiver:exact-finite-state-arithmetic)
   anchors: []
   utility: kind=bounded-enumeration; basis=terminal=atom:6d2d16231bf01aa995c79d28ae4e852832fd13dd1025947663e87843bcf84062
   digest: A period-31 parity orbit excludes zeros from 16 residue classes. -/

import Mathlib.Algebra.LinearRecurrence
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Recurrence.SkolemOrderFiveModularExclusion

/-- A five-coordinate state over the integers modulo two. -/
structure State where
  x0 : ZMod 2
  x1 : ZMod 2
  x2 : ZMod 2
  x3 : ZMod 2
  x4 : ZMod 2
deriving DecidableEq, Repr

private theorem state_ext {s t : State}
    (h0 : s.x0 = t.x0) (h1 : s.x1 = t.x1) (h2 : s.x2 = t.x2)
    (h3 : s.x3 = t.x3) (h4 : s.x4 = t.x4) : s = t := by
  cases s
  cases t
  simp_all

/-- The companion step forced by coefficient residues `(1, 0, 0, 1, 0)`. -/
def step (s : State) : State :=
  ⟨s.x1, s.x2, s.x3, s.x4, s.x0 + s.x3⟩

/-- The prescribed coefficient vector modulo two. -/
def coeffBits : Fin 5 → ZMod 2 := ![1, 0, 0, 1, 0]

/-- The prescribed initial vector modulo two. -/
def initialBits : Fin 5 → ZMod 2 := ![1, 0, 0, 0, 0]

/-- The initial state `(1, 0, 0, 0, 0)` modulo two. -/
def initialState : State := ⟨1, 0, 0, 0, 0⟩

/-- The order-five integer recurrence with coefficient vector `a`. -/
def intRecurrence (a : Fin 5 → ℤ) : LinearRecurrence ℤ where
  order := 5
  coeffs := a

/-- Five consecutive integer terms, reduced coordinatewise modulo two. -/
def reducedState (u : ℕ → ℤ) (n : ℕ) : State :=
  ⟨u n, u (n + 1), u (n + 2), u (n + 3), u (n + 4)⟩

/-- The binary companion orbit from the prescribed initial state. -/
def orbitState (n : ℕ) : State :=
  step^[n] initialState

/-- The fifteen residue classes modulo thirty-one in which a zero may occur. -/
def possibleZeroResidues : Finset ℕ :=
  {1, 2, 3, 4, 6, 8, 12, 15, 16, 17, 23, 24, 27, 29, 30}

/-- Reduction modulo two commutes with one recurrence step for every integer lift
whose five coefficients have the prescribed residue vector. -/
theorem reduction_commutes_with_step
    (a : Fin 5 → ℤ) (u : ℕ → ℤ)
    (hrec : (intRecurrence a).IsSolution u)
    (hcoeff : ∀ i : Fin 5, (a i : ZMod 2) = coeffBits i)
    (n : ℕ) :
    reducedState u (n + 1) = step (reducedState u n) := by
  apply state_ext
  · rfl
  · rfl
  · rfl
  · rfl
  · change (∀ m : ℕ, u (m + 5) = ∑ i : Fin 5, a i * u (m + i)) at hrec
    have h := congrArg (fun z : ℤ => (z : ZMod 2)) (hrec n)
    push_cast at h
    rw [Fin.sum_univ_five] at h
    simpa [reducedState, step, coeffBits, Nat.add_assoc, hcoeff] using h

/-- The binary orbit returns to its initial state after thirty-one steps. -/
theorem orbit_closes : Function.IsPeriodicPt step 31 initialState := by
  decide

/-- No positive iterate below thirty-one returns to the initial state. -/
theorem orbit_no_early_return :
    ∀ k : Fin 30, orbitState (k.val + 1) ≠ initialState := by
  decide

private theorem orbit_mod (n : ℕ) : orbitState (n % 31) = orbitState n := by
  exact orbit_closes.iterate_mod_apply n

private theorem reduced_state_eq_orbit
    (a : Fin 5 → ℤ) (u : ℕ → ℤ)
    (hrec : (intRecurrence a).IsSolution u)
    (hcoeff : ∀ i : Fin 5, (a i : ZMod 2) = coeffBits i)
    (hinit : ∀ i : Fin 5, (u i : ZMod 2) = initialBits i) :
    ∀ n : ℕ, reducedState u n = orbitState n := by
  intro n
  induction n with
  | zero =>
      apply state_ext
      · simpa [reducedState, orbitState, initialState, initialBits] using hinit (0 : Fin 5)
      · simpa [reducedState, orbitState, initialState, initialBits] using hinit (1 : Fin 5)
      · simpa [reducedState, orbitState, initialState, initialBits] using hinit (2 : Fin 5)
      · simpa [reducedState, orbitState, initialState, initialBits] using hinit (3 : Fin 5)
      · simpa [reducedState, orbitState, initialState, initialBits] using hinit (4 : Fin 5)
  | succ n ih =>
      calc
        reducedState u (n + 1) = step (reducedState u n) :=
          reduction_commutes_with_step a u hrec hcoeff n
        _ = step (orbitState n) := congrArg step ih
        _ = orbitState (n + 1) := by
          simp [orbitState, Function.iterate_succ_apply']

/-- The first coordinate is one on all sixteen residues outside the exceptional set. -/
theorem orbit_nonzero_readoff :
    ∀ r : Fin 31,
      r.val ∉ possibleZeroResidues → (orbitState r.val).x0 = 1 := by
  decide

/-- Every lifted integer solution is odd outside the fifteen exceptional residue classes. -/
theorem odd_of_mod31_not_mem
    (a : Fin 5 → ℤ) (u : ℕ → ℤ)
    (hrec : (intRecurrence a).IsSolution u)
    (hcoeff : ∀ i : Fin 5, (a i : ZMod 2) = coeffBits i)
    (hinit : ∀ i : Fin 5, (u i : ZMod 2) = initialBits i) :
    ∀ n : ℕ, n % 31 ∉ possibleZeroResidues → Odd (u n) := by
  intro n hout
  have hstate := reduced_state_eq_orbit a u hrec hcoeff hinit n
  let r : Fin 31 := ⟨n % 31, Nat.mod_lt n (by decide)⟩
  have hbit : (orbitState (n % 31)).x0 = 1 := by
    apply orbit_nonzero_readoff r
    exact hout
  rw [orbit_mod n] at hbit
  rw [← ZMod.intCast_eq_one_iff_odd]
  calc
    (u n : ZMod 2) = (reducedState u n).x0 := rfl
    _ = (orbitState n).x0 := congrArg State.x0 hstate
    _ = 1 := hbit

/-- Uniform oddness and its zero-index consequence for every order-five integer recurrence
in the prescribed coefficient and initial congruence classes. -/
theorem zero_index_mod31_mem
    (a : Fin 5 → ℤ) (u : ℕ → ℤ)
    (hrec : (intRecurrence a).IsSolution u)
    (hcoeff : ∀ i : Fin 5, (a i : ZMod 2) = coeffBits i)
    (hinit : ∀ i : Fin 5, (u i : ZMod 2) = initialBits i) :
    (∀ n : ℕ, n % 31 ∉ possibleZeroResidues → Odd (u n)) ∧
      (∀ n : ℕ, u n = 0 → n % 31 ∈ possibleZeroResidues) := by
  constructor
  · exact odd_of_mod31_not_mem a u hrec hcoeff hinit
  · intro n hzero
    by_contra hout
    have hodd := odd_of_mod31_not_mem a u hrec hcoeff hinit n hout
    simp [hzero] at hodd

-- Fidelity witnesses: the quantified domains are inhabited and the assumptions co-occur.
example : Fin 5 → ℤ := ![1, 0, 0, 1, 0]

example : ∃ a : Fin 5 → ℤ, ∃ u : ℕ → ℤ,
    (intRecurrence a).IsSolution u ∧
      (∀ i : Fin 5, (a i : ZMod 2) = coeffBits i) ∧
      (∀ i : Fin 5, (u i : ZMod 2) = initialBits i) := by
  let a : Fin 5 → ℤ := ![1, 0, 0, 1, 0]
  let v : Fin 5 → ℤ := ![1, 0, 0, 0, 0]
  refine ⟨a, (intRecurrence a).mkSol v, ?_, ?_, ?_⟩
  · exact (intRecurrence a).is_sol_mkSol v
  · decide
  · intro i
    rw [(intRecurrence a).mkSol_eq_init v i]
    fin_cases i <;> decide

#print axioms reduction_commutes_with_step
#print axioms orbit_closes
#print axioms orbit_no_early_return
#print axioms orbit_nonzero_readoff
#print axioms odd_of_mod31_not_mem
#print axioms zero_index_mod31_mem

end D5.S1.Recurrence.SkolemOrderFiveModularExclusion
