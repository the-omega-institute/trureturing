# Local Reciprocity Matrix and Its Two Reading Directions

## Abstract

The odd-prime reciprocity matrix has distinct row and column collision relations.

**Definition 1.1 (Odd-prime index space).**

Lean statement: `D5/S3/PrimeForms/Splitting/LocalReciprocityMatrix.OddPrime`

*Formalization.* `D5/S3/PrimeForms/Splitting/LocalReciprocityMatrix.OddPrime` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The observer coordinate consists of natural primes other than two.

**Definition 1.2 (Discriminant coordinate space).**

Lean statement: `D5/S3/PrimeForms/Splitting/LocalReciprocityMatrix.Discriminant`

*Formalization.* `D5/S3/PrimeForms/Splitting/LocalReciprocityMatrix.Discriminant` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Discriminant coordinates are integer values, including zero and one.

**Definition 1.3 (Local reciprocity matrix).**

Lean statement: `D5/S3/PrimeForms/Splitting/LocalReciprocityMatrix.localReciprocityMatrix`

*Formalization.* `D5/S3/PrimeForms/Splitting/LocalReciprocityMatrix.localReciprocityMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The entry at an odd prime and discriminant is the Legendre symbol.

**Definition 1.4 (A prime observes discriminants).**

Lean statement: `D5/S3/PrimeForms/Splitting/LocalReciprocityMatrix.primeObservesDiscriminants`

*Formalization.* `D5/S3/PrimeForms/Splitting/LocalReciprocityMatrix.primeObservesDiscriminants` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Fixing the prime produces the row map from discriminants to readings.

**Definition 1.5 (A discriminant observes primes).**

Lean statement: `D5/S3/PrimeForms/Splitting/LocalReciprocityMatrix.discriminantObservesPrimes`

*Formalization.* `D5/S3/PrimeForms/Splitting/LocalReciprocityMatrix.discriminantObservesPrimes` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Fixing the discriminant produces the column map from primes to readings.

**Definition 1.6 (Row indistinguishability).**

Lean statement: `D5/S3/PrimeForms/Splitting/LocalReciprocityMatrix.SameAtPrime`

*Formalization.* `D5/S3/PrimeForms/Splitting/LocalReciprocityMatrix.SameAtPrime` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Two discriminants are row-indistinguishable when one prime reads them equally.

**Definition 1.7 (Column indistinguishability).**

Lean statement: `D5/S3/PrimeForms/Splitting/LocalReciprocityMatrix.SameAtDiscriminant`

*Formalization.* `D5/S3/PrimeForms/Splitting/LocalReciprocityMatrix.SameAtDiscriminant` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Two primes are column-indistinguishable when one discriminant reads them equally.

**Definition 1.8 (Split reading).**

Lean statement: `D5/S3/PrimeForms/Splitting/LocalReciprocityMatrix.IsSplitAt`

*Formalization.* `D5/S3/PrimeForms/Splitting/LocalReciprocityMatrix.IsSplitAt` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The split predicate is the decidable condition that the entry equals one.

**Definition 1.9 (Inert reading).**

Lean statement: `D5/S3/PrimeForms/Splitting/LocalReciprocityMatrix.IsInertAt`

*Formalization.* `D5/S3/PrimeForms/Splitting/LocalReciprocityMatrix.IsInertAt` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The inert predicate is the decidable condition that the entry equals minus one.

**Definition 1.10 (Ramified reading).**

Lean statement: `D5/S3/PrimeForms/Splitting/LocalReciprocityMatrix.IsRamifiedAt`

*Formalization.* `D5/S3/PrimeForms/Splitting/LocalReciprocityMatrix.IsRamifiedAt` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The ramified predicate is the decidable condition that the entry equals zero.

**Theorem 1.11 (Every matrix entry has one of three values).**

$$\operatorname{localReciprocityMatrix}\left(p, Delta\right) \in \{-1, 0, 1\}.$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/Splitting/LocalReciprocityMatrix.local_reciprocity_value_trichotomy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Legendre character dichotomy away from zero and its exact zero criterion place every entry in the set consisting of minus one, zero, and one.

**Theorem 1.12 (Split means nonzero square).**

$$\operatorname{IsSplitAt}\left(p, Delta\right) \iff \operatorname{NeqMod}\left(Delta, 0, p\right) \land \operatorname{IsSquareMod}\left(Delta, p\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/Splitting/LocalReciprocityMatrix.split_iff_nonzero_square_mod_prime` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An entry is split exactly when the discriminant is a nonzero square modulo the fixed prime.

**Theorem 1.13 (Inert means nonsquare).**

$$\operatorname{IsInertAt}\left(p, Delta\right) \iff \neg\operatorname{IsSquareMod}\left(Delta, p\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/Splitting/LocalReciprocityMatrix.inert_iff_nonsquare_mod_prime` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An entry is inert exactly when the discriminant is not a square modulo the fixed prime.

**Theorem 1.14 (Ramified means divisibility).**

$$\operatorname{IsRamifiedAt}\left(p, Delta\right) \iff \operatorname{Dvd}\left(p, Delta\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/Splitting/LocalReciprocityMatrix.ramified_iff_prime_dvd_discriminant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact zero criterion identifies ramification with divisibility of the discriminant by the fixed prime.

**Theorem 1.15 (A fixed row has a collision).**

$$5 \neq 8 \land\\\operatorname{localReciprocityMatrix}\left(3, 5\right) = \operatorname{localReciprocityMatrix}\left(3, 8\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/Splitting/LocalReciprocityMatrix.row_reading_collision_at_three` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The distinct discriminants five and eight both have inert reading at the fixed prime three.

**Theorem 1.16 (A fixed column has a collision).**

$$3 \neq 7 \land\\\operatorname{localReciprocityMatrix}\left(3, 5\right) = \operatorname{localReciprocityMatrix}\left(7, 5\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/Splitting/LocalReciprocityMatrix.column_reading_collision_at_five` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The distinct primes three and seven both have inert reading at the fixed discriminant five.

**Theorem 1.17 (Reciprocity does not identify the two axes).**

$$\operatorname{localReciprocityMatrix}\left(5, 13\right) = \operatorname{localReciprocityMatrix}\left(13, 5\right) \land\\\operatorname{localReciprocityMatrix}\left(3, 5\right) = \operatorname{localReciprocityMatrix}\left(3, 8\right) \land\\\neg(\operatorname{localReciprocityMatrix}\left(3, 5\right) = \operatorname{localReciprocityMatrix}\left(5, 5\right)).$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/Splitting/LocalReciprocityMatrix.reciprocity_does_not_identify_reading_directions` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Quadratic reciprocity equates the transposed cells at five and thirteen. Nevertheless, five and eight collide in the row at three while three and five are separated in the column at five.

**Theorem 1.18 (Degenerate discriminants are explicit).**

$$(\forall p: OddPrime, \operatorname{localReciprocityMatrix}\left(p, 0\right) = 0 \land \operatorname{localReciprocityMatrix}\left(p, 1\right) = 1) \land\\\operatorname{localReciprocityMatrix}\left(3, 4\right) = 1 \land\\\operatorname{localReciprocityMatrix}\left(3, 9\right) = 0.$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/Splitting/LocalReciprocityMatrix.discriminant_degeneracy_audit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Zero gives a constant ramified column and one gives a constant split column. At three, square four splits while divisible square nine ramifies.

**Theorem 1.19 (Primality is necessary for the divisibility reading).**

$$\operatorname{jacobiSym}\left(3, 9\right) = 0 \land \neg\operatorname{Dvd}\left(9, 3\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/Splitting/LocalReciprocityMatrix.primality_is_necessary_for_ramified_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At composite Jacobi index nine, numerator three gives zero although nine does not divide three. Dropping primality breaks the law.

**Theorem 1.20 (The prime two has no inert value).**

$$\forall Delta: Z, \operatorname{legendreSym}\left(2, Delta\right) \neq -1.$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/Splitting/LocalReciprocityMatrix.oddness_is_necessary_for_inert_value` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At the prime two every nonzero class is a square, so its Legendre symbol never takes the inert value minus one.

## References

- Truth anchor: `D5/S3/PrimeForms/Splitting/LocalReciprocityMatrix.Discriminant`
- Truth anchor: `D5/S3/PrimeForms/Splitting/LocalReciprocityMatrix.IsInertAt`
- Truth anchor: `D5/S3/PrimeForms/Splitting/LocalReciprocityMatrix.IsRamifiedAt`
- Truth anchor: `D5/S3/PrimeForms/Splitting/LocalReciprocityMatrix.IsSplitAt`
- Truth anchor: `D5/S3/PrimeForms/Splitting/LocalReciprocityMatrix.OddPrime`
- Truth anchor: `D5/S3/PrimeForms/Splitting/LocalReciprocityMatrix.SameAtDiscriminant`
- Truth anchor: `D5/S3/PrimeForms/Splitting/LocalReciprocityMatrix.SameAtPrime`
- Truth anchor: `D5/S3/PrimeForms/Splitting/LocalReciprocityMatrix.column_reading_collision_at_five`
- Truth anchor: `D5/S3/PrimeForms/Splitting/LocalReciprocityMatrix.discriminantObservesPrimes`
- Truth anchor: `D5/S3/PrimeForms/Splitting/LocalReciprocityMatrix.discriminant_degeneracy_audit`
- Truth anchor: `D5/S3/PrimeForms/Splitting/LocalReciprocityMatrix.inert_iff_nonsquare_mod_prime`
- Truth anchor: `D5/S3/PrimeForms/Splitting/LocalReciprocityMatrix.localReciprocityMatrix`
- Truth anchor: `D5/S3/PrimeForms/Splitting/LocalReciprocityMatrix.local_reciprocity_value_trichotomy`
- Truth anchor: `D5/S3/PrimeForms/Splitting/LocalReciprocityMatrix.oddness_is_necessary_for_inert_value`
- Truth anchor: `D5/S3/PrimeForms/Splitting/LocalReciprocityMatrix.primality_is_necessary_for_ramified_iff`
- Truth anchor: `D5/S3/PrimeForms/Splitting/LocalReciprocityMatrix.primeObservesDiscriminants`
- Truth anchor: `D5/S3/PrimeForms/Splitting/LocalReciprocityMatrix.ramified_iff_prime_dvd_discriminant`
- Truth anchor: `D5/S3/PrimeForms/Splitting/LocalReciprocityMatrix.reciprocity_does_not_identify_reading_directions`
- Truth anchor: `D5/S3/PrimeForms/Splitting/LocalReciprocityMatrix.row_reading_collision_at_three`
- Truth anchor: `D5/S3/PrimeForms/Splitting/LocalReciprocityMatrix.split_iff_nonzero_square_mod_prime`
