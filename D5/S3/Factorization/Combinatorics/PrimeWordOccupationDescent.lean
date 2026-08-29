/- GID: D5/S3/Factorization/Combinatorics/PrimeWordOccupationDescent
   generality: G
   mirror-B: D5/B/S3/Factorization/Combinatorics/PrimeWordOccupationDescent
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Prime histories cannot be recovered; word actions descend exactly when commuting. -/

import D5.S3.Factorization.FreeCommMonoid
import D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Factorization.Combinatorics.PrimeWordOccupationDescent

open D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality

/- Library-search audit trail (2026-08-29):
   * `Multiset Nat.Primes` is the canonical free commutative prime carrier imported from
     `FreeCommMonoid`; list coercion is Mathlib's quotient by `List.Perm`.
   * `runWord` is imported as the canonical left-to-right action of an input word.
   * Mathlib hits `Multiset.lift_coe`, `Quotient.sound`, and the `List.Perm` constructors provide
     the quotient proof. No full no-section or descent-if-and-only-if theorem was found. -/

/-- The prime occupation multiset does not determine an ordered prime word: no single decoder is
a left inverse to the canonical list-to-multiset quotient on every word. -/
theorem no_prime_history_reconstruction :
    Not (exists recover : Multiset Nat.Primes -> List Nat.Primes,
      forall word : List Nat.Primes, recover (word : Multiset Nat.Primes) = word) := by
  rintro ⟨recover, leftInverse⟩
  let two : Nat.Primes := ⟨2, Nat.prime_two⟩
  let three : Nat.Primes := ⟨3, Nat.prime_three⟩
  have occupation_eq :
      (([two, three] : List Nat.Primes) : Multiset Nat.Primes) =
        (([three, two] : List Nat.Primes) : Multiset Nat.Primes) := by
    exact Quotient.sound (List.Perm.swap two three []).symm
  have word_eq : ([two, three] : List Nat.Primes) = [three, two] := by
    calc
      [two, three] = recover (([two, three] : List Nat.Primes) :
          Multiset Nat.Primes) := (leftInverse [two, three]).symm
      _ = recover (([three, two] : List Nat.Primes) : Multiset Nat.Primes) :=
        congrArg recover occupation_eq
      _ = [three, two] := leftInverse [three, two]
  have two_eq_three : two = three := by
    simpa using congrArg List.head? word_eq
  have value_eq : (2 : Nat) = 3 := congrArg Subtype.val two_eq_three
  omega

/-- A family of state updates factors through the word-to-multiset occupation quotient exactly
when every pair of updates commutes. The quantified factor is the descended occupation
dynamics, and its public computation rule fixes it on every word. -/
theorem order_descent_criterion {Prime State : Type*}
    (update : Prime -> State -> State) :
    (exists descended : Multiset Prime -> State -> State,
      forall word : List Prime,
        descended (word : Multiset Prime) = runWord update word) <->
    (forall p q : Prime, Function.Commute (update p) (update q)) := by
  constructor
  · rintro ⟨descended, computation⟩
    intro p q state
    have occupation_eq :
        (([p, q] : List Prime) : Multiset Prime) =
          (([q, p] : List Prime) : Multiset Prime) := by
      exact Quotient.sound (List.Perm.swap p q []).symm
    have word_action_eq : runWord update [p, q] = runWord update [q, p] := by
      calc
        runWord update [p, q] = descended (([p, q] : List Prime) :
            Multiset Prime) := (computation [p, q]).symm
        _ = descended (([q, p] : List Prime) : Multiset Prime) :=
          congrArg descended occupation_eq
        _ = runWord update [q, p] := computation [q, p]
    simpa [runWord] using (congrFun word_action_eq state).symm
  · intro commute
    have perm_invariant : forall {first second : List Prime},
        List.Perm first second -> runWord update first = runWord update second := by
      intro first second permutation
      induction permutation with
      | nil => rfl
      | cons p permutation inductionHypothesis =>
          funext state
          simp only [runWord]
          exact congrFun inductionHypothesis (update p state)
      | swap p q tail =>
          funext state
          simp only [runWord]
          exact congrArg (runWord update tail) ((commute p q).eq state)
      | trans _ _ firstEquality secondEquality =>
          exact firstEquality.trans secondEquality
    let descended : Multiset Prime -> State -> State :=
      Quotient.lift (runWord update)
        (fun _first _second permutation => perm_invariant permutation)
    have computation : forall word : List Prime,
        descended (word : Multiset Prime) = runWord update word := by
      intro word
      exact Multiset.lift_coe word (runWord update)
        (fun _first _second permutation => perm_invariant permutation)
    exact ⟨descended, computation⟩

#print axioms no_prime_history_reconstruction
#print axioms order_descent_criterion

end D5.S3.Factorization.Combinatorics.PrimeWordOccupationDescent
