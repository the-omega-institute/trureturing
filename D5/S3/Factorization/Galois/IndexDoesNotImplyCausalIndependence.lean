/- GID: D5/S3/Factorization/Galois/IndexDoesNotImplyCausalIndependence
   generality: G
   mirror-B: D5/B/S3/Factorization/Galois/IndexDoesNotImplyCausalIndependence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Distinct primes can share noise; separate coordinates give the control case. -/
/- Library-search audit trail (2026-08-25):
   * Repository and pinned Mathlib searches found no exact crosswise-recombination
     definition for causal independence of two readout functions.
   * `GaloisFusion.differently_named_extensions_not_independent` is a related diagonal
     counterexample for field restrictions, but it has no prime-indexed noise modules or
     independent control model and is not reused as a substitute.
   * `SamePrimeScaleRedundancy.different_prime_joint_strictly_finer` was read at its
     actual signature: it proves two strict inclusions between equality-kernel sets.
   * Exact pinned hits `Nat.prime_two` and `Nat.prime_three` certify the concrete prime
     addresses below. No probability or intervention library is imported.
-/

import Mathlib.Data.Nat.Prime.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Factorization.Galois.IndexDoesNotImplyCausalIndependence

/-!
We choose the smallest functional, fiberwise reading of causal independence. Two readouts are
independent when any value realized by the left readout and any value realized by the right
readout can be realized together by one latent state. Equivalently, their joint range is the
product of their marginal ranges. This detects whether their fiber partitions cross freely.

This choice needs neither a probability law nor an intervention language. Consequently it does
not claim stochastic independence or a do-calculus theorem. Those stronger frameworks are
deliberately omitted because the source principle needs only one coupled witness and one control.

The separation from FPOD 7.1 is exact. The theorem
`different_prime_joint_strictly_finer` proves that the equality kernel of the joint readings at
two and three is strictly contained in each single-reading kernel. That is a statement about
discriminating states. It says nothing about how either reading is generated, which exogenous
noise it uses, or which interventions affect it. Strictly finer joint discrimination therefore
cannot imply causal independence and cannot negate the shared-noise witness below.

Only shared exogenous noise is formalized here. Directed edges, a common environment variable,
simultaneous disturbance by one apparatus, and distinct addresses with coupled mechanisms are
other members of the same family and are not separately formalized in this module.

Primality carries no mechanism-level weight. The counterexample certifies that two and three are
prime, but coupling uses only the shared Boolean noise. The control theorem is stated for arbitrary
natural-number addresses and uses only their inequality.
-/

/-- Two readouts are independent when all crosswise combinations of realized values occur. -/
def CausallyIndependent {E A B : Type*} (left : E -> A) (right : E -> B) : Prop :=
  ∀ eLeft eRight, ∃ e, left e = left eLeft ∧ right e = right eRight

/-- Every address reads the same supplied exogenous-noise mechanism. -/
def sharedNoiseModule {E X : Type*} (_p : Nat) (noise : E -> X) : E -> X :=
  noise

/-- Address `p` reads only coordinate `p` of an address-indexed noise family. -/
def coordinateNoiseModule {X : Type*} (p : Nat) : (Nat -> X) -> X :=
  fun noise => noise p

/-- The distinct prime addresses two and three can both expose one Boolean exogenous variable,
so the value false from one state cannot be combined with the value true from another. -/
theorem distinct_prime_indices_can_share_exogenous_noise :
    ∃ p q : Nat, Nat.Prime p ∧ Nat.Prime q ∧ p ≠ q ∧
      ¬CausallyIndependent
        (sharedNoiseModule p (fun noise : Bool => noise))
        (sharedNoiseModule q (fun noise : Bool => noise)) := by
  refine ⟨2, 3, Nat.prime_two, Nat.prime_three, by decide, ?_⟩
  intro independent
  rcases independent false true with ⟨noise, hfalse, htrue⟩
  change noise = false at hfalse
  change noise = true at htrue
  cases hfalse
  cases htrue
#print axioms distinct_prime_indices_can_share_exogenous_noise

/-- In the control model, unequal addresses read separate exogenous coordinates and hence are
independent: overwrite the left coordinate while preserving the distinct right coordinate. -/
theorem distinct_indices_imply_independence_for_coordinate_noise
    {X : Type*} (p q : Nat) (hpq : p ≠ q) :
    CausallyIndependent (coordinateNoiseModule (X := X) p)
      (coordinateNoiseModule (X := X) q) := by
  intro leftNoise rightNoise
  let combined : Nat -> X := fun i => if i = p then leftNoise p else rightNoise i
  refine ⟨combined, ?_, ?_⟩
  · simp [coordinateNoiseModule, combined]
  · simp [coordinateNoiseModule, combined, Ne.symm hpq]
#print axioms distinct_indices_imply_independence_for_coordinate_noise

/-- Address inequality is necessary for the universal coordinate-noise control theorem: at the
single prime address two, the false and true coordinate values cannot be combined. -/
theorem index_distinctness_is_necessary_for_coordinate_noise :
    Nat.Prime 2 ∧
      ¬CausallyIndependent
        (coordinateNoiseModule (X := Bool) (2 : Nat))
        (coordinateNoiseModule (X := Bool) (2 : Nat)) := by
  refine ⟨Nat.prime_two, ?_⟩
  intro independent
  rcases independent (fun _ => false) (fun _ => true) with ⟨noise, hfalse, htrue⟩
  change noise 2 = false at hfalse
  change noise 2 = true at htrue
  have hne : false ≠ true := by decide
  exact hne (hfalse.symm.trans htrue)
#print axioms index_distinctness_is_necessary_for_coordinate_noise

section DegenerateAudit

-- On an empty latent carrier the universal recombination condition is vacuous.
example {A B : Type*} (left : Empty -> A) (right : Empty -> B) :
    CausallyIndependent left right := by
  intro eLeft
  exact eLeft.elim

-- If shared exogenous noise degenerates to a constant, this criterion detects no coupling.
example {E X : Type*} (p q : Nat) (value : X) :
    CausallyIndependent
      (sharedNoiseModule p (fun _ : E => value))
      (sharedNoiseModule q (fun _ : E => value)) := by
  intro eLeft _
  exact ⟨eLeft, rfl, rfl⟩

-- More generally, two constant modules are independent even when their output types differ.
example {E A B : Type*} (leftValue : A) (rightValue : B) :
    CausallyIndependent (fun _ : E => leftValue) (fun _ : E => rightValue) := by
  intro eLeft _
  exact ⟨eLeft, rfl, rfl⟩

-- A one-element latent type reduces every readout to the preceding constant case.
example : CausallyIndependent (fun _ : Unit => false) (fun _ : Unit => true) := by
  intro _ _
  exact ⟨(), rfl, rfl⟩

-- At `p = q`, the antecedent `p ≠ q` is false, so the implication is vacuously true.
example {E A B : Type*} (left : Nat -> E -> A) (right : Nat -> E -> B) (p : Nat) :
    p ≠ p -> CausallyIndependent (left p) (right p) := by
  intro hp
  exact (hp rfl).elim

-- Address zero is legal and independent from address one in the coordinate-noise control model.
example :
    CausallyIndependent
      (coordinateNoiseModule (X := Bool) (0 : Nat))
      (coordinateNoiseModule (X := Bool) (1 : Nat)) := by
  exact distinct_indices_imply_independence_for_coordinate_noise 0 1 (by decide)

-- There is no depth or budget parameter `n`; an `n = 0` audit is therefore inapplicable.

end DegenerateAudit

/-!
Hypothesis audit, declaration by declaration:

* `distinct_prime_indices_can_share_exogenous_noise` has no hypotheses or instances. The prime
  facts and address inequality are proved as parts of its witness; the coupling proof uses neither
  primality fact and depends only on the shared nonconstant Boolean noise.
* `distinct_indices_imply_independence_for_coordinate_noise` has exactly one hypothesis, `p ≠ q`.
  It is used to preserve coordinate `q` after coordinate `p` is overwritten. The following named
  theorem instantiates the same model at the prime address two and proves this hypothesis necessary.
* `index_distinctness_is_necessary_for_coordinate_noise` has no hypotheses or instances.

No algebraic, finite, inhabited, decidable-equality, or primality instance is assumed by any of the
three definitions or theorem signatures.
-/

end D5.S3.Factorization.Galois.IndexDoesNotImplyCausalIndependence
