# The quotient terminal-vector annihilator

## Abstract

The exact integer certificate for the 59-coordinate terminal vector gives an annihilator at every nonnegative shift.

**Definition 1.1 (The sparse matrix).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridQuotient.rows`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridQuotient.rows` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The list at each of the 59 rows contains its nonzero column-and-integer-weight pairs. These are the 207 nonzero entries of the supplied quotient certificate.

**Definition 1.2 (The terminal vector).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridQuotient.terminal`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridQuotient.terminal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The 59 integer terminal values form the zeroth vector.

**Definition 1.3 (Finite power certificate).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridQuotient.values`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridQuotient.values` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

All 49 vectors, indexed from exponent 0 through 48, are literal exact integers. They are certificate inputs, not assumed powers.

**Definition 1.4 (The entire denominator).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridQuotient.denominator`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridQuotient.denominator` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The 49 coefficients in increasing degree order are exactly those of Colin Barker's denominator in OEIS A286848, https://oeis.org/A286848. Its constant coefficient is 1 and its degree is 48. Attribution and CC-BY-SA-4.0 apply to the reproduced formula: https://creativecommons.org/licenses/by-sa/4.0/.

**Definition 1.5 (Integer linear multiplication).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridQuotient.step`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridQuotient.step` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Sparse row evaluation is packaged as an integer linear map, so sums and integer scalar multiples commute with each matrix step.

**Theorem 1.6 (Check every successive vector).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridQuotient.power_steps`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridQuotient.power_steps` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every k in Fin 48 and every i in Fin 59, step(values(k.castSucc))(i) = values(k.succ)(i). Kernel decisions verify every coordinate.

**Theorem 1.7 (Check the initial vector).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridQuotient.initial_vector`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridQuotient.initial_vector` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

values(0) = terminal. The equality is definitional.

**Theorem 1.8 (Check all residual coordinates).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridQuotient.finite_annihilator`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridQuotient.finite_annihilator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every i in Fin 59, the sum over j in Fin 49 of denominator(j) times values(48-j)(i) is zero. Every one of the 59 coordinates is kernel checked.

**Definition 1.9 (The unrestricted matrix orbit).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridQuotient.orbit`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridQuotient.orbit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

orbit(0) = terminal and orbit(k+1) = step(orbit(k)) for every natural k.

**Theorem 1.10 (Every shift).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridQuotient.shifted_annihilator`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridQuotient.shifted_annihilator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural k, the vector sum over j in Fin 49 of denominator(j) scalar-multiplying orbit(k+48-j) is zero. Induction applies the linear map to the previous zero residual; the conclusion is not extrapolated from finite agreement.

The supplied numerical certificate has SHA-256 ab0c5370648ec80cad7798774a9ce6ad7cf62b7d34f296441e3a897715f0701c. The total transfer partition identifies the full and quotient orbits through TR=RB, f=Rg and betaR=alpha. Evaluation against alpha then transports this vector annihilator to the actual subset counts; the complete initial numerator convolutions fix every remaining coefficient.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridQuotient.denominator`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridQuotient.finite_annihilator`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridQuotient.initial_vector`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridQuotient.orbit`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridQuotient.power_steps`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridQuotient.rows`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridQuotient.shifted_annihilator`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridQuotient.step`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridQuotient.terminal`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridQuotient.values`
