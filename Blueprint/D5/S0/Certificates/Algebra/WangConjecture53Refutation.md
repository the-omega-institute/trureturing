# Wang Conjecture 5.3: an Ordinary Semigroup Algebra Counterexample

## Abstract

Wang's Conjecture 5.3 fails for a six-element finite commutative monoid over Q: the ordinary algebraic constant is one and the proposed right side is at least two.

**Definition 1.1 (Positive multiples without adjoining zero).**

Lean statement: `D5/S0/Certificates/Algebra/WangConjecture53Refutation.positiveMultiple`

*Formalization.* `D5/S0/Certificates/Algebra/WangConjecture53Refutation.positiveMultiple` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Guoqing Wang (2025). *Semigroup rings and algebraically independent sequences with respect to idempotents in commutative semigroups*. URL: <https://arxiv.org/abs/2509.18724v1>.

*Commentary.*

Index n denotes the positive multiple (n+1)a. The universal assertion requires only a finite commutative semigroup, with no identity assumption.

**Definition 1.2 (The positive cyclic subsemigroup).**

Lean statement: `D5/S0/Certificates/Algebra/WangConjecture53Refutation.cyclic`

*Formalization.* `D5/S0/Certificates/Algebra/WangConjecture53Refutation.cyclic` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Guoqing Wang (2025). *Semigroup rings and algebraically independent sequences with respect to idempotents in commutative semigroups*. URL: <https://arxiv.org/abs/2509.18724v1>.

*Commentary.*

The carrier consists of positive multiples only. It excludes an artificial zeroth multiple in a nonunital semigroup.

**Definition 1.3 (Cyclic idempotent specification).**

Lean statement: `D5/S0/Certificates/Algebra/WangConjecture53Refutation.IsCyclicIdempotent`

*Formalization.* `D5/S0/Certificates/Algebra/WangConjecture53Refutation.IsCyclicIdempotent` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Guoqing Wang (2025). *Semigroup rings and algebraically independent sequences with respect to idempotents in commutative semigroups*. URL: <https://arxiv.org/abs/2509.18724v1>.

*Commentary.*

The element belongs to the positive cyclic subsemigroup and satisfies e+e=e.

**Definition 1.4 (The actual cyclic idempotent).**

Lean statement: `D5/S0/Certificates/Algebra/WangConjecture53Refutation.cyclicIdempotent`

*Formalization.* `D5/S0/Certificates/Algebra/WangConjecture53Refutation.cyclicIdempotent` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Guoqing Wang (2025). *Semigroup rings and algebraically independent sequences with respect to idempotents in commutative semigroups*. URL: <https://arxiv.org/abs/2509.18724v1>.

*Commentary.*

A finite positive cyclic subsemigroup has a unique idempotent. Existence reuses Mathlib's compact-semigroup theorem with the discrete topology; uniqueness uses common positive multiples. The selector's fallback is unreachable for every element of a finite commutative semigroup.

**Definition 1.5 (A cyclic group with its own identity).**

Lean statement: `D5/S0/Certificates/Algebra/WangConjecture53Refutation.CyclicIsGroup`

*Formalization.* `D5/S0/Certificates/Algebra/WangConjecture53Refutation.CyclicIsGroup` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Guoqing Wang (2025). *Semigroup rings and algebraically independent sequences with respect to idempotents in commutative semigroups*. URL: <https://arxiv.org/abs/2509.18724v1>.

*Commentary.*

An identity and inverses must lie inside the positive cyclic subsemigroup. This property, rather than idempotence alone, controls epsilon.

**Definition 1.6 (The cyclic period).**

Lean statement: `D5/S0/Certificates/Algebra/WangConjecture53Refutation.period`

*Formalization.* `D5/S0/Certificates/Algebra/WangConjecture53Refutation.period` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Guoqing Wang (2025). *Semigroup rings and algebraically independent sequences with respect to idempotents in commutative semigroups*. URL: <https://arxiv.org/abs/2509.18724v1>.

*Commentary.*

Take the least positive eventual shift of positive multiples. This is the source period, not the index where periodicity begins.

**Definition 1.7 (LCM of the periods).**

Lean statement: `D5/S0/Certificates/Algebra/WangConjecture53Refutation.semigroupExponent`

*Formalization.* `D5/S0/Certificates/Algebra/WangConjecture53Refutation.semigroupExponent` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Guoqing Wang (2025). *Semigroup rings and algebraically independent sequences with respect to idempotents in commutative semigroups*. URL: <https://arxiv.org/abs/2509.18724v1>.

*Commentary.*

The exponent is the least common multiple of all cyclic periods. The six-label witness has period one at each element and exponent one.

**Definition 1.8 (The source splitting condition).**

Lean statement: `D5/S0/Certificates/Algebra/WangConjecture53Refutation.Splitting`

*Formalization.* `D5/S0/Certificates/Algebra/WangConjecture53Refutation.Splitting` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Guoqing Wang (2025). *Semigroup rings and algebraically independent sequences with respect to idempotents in commutative semigroups*. URL: <https://arxiv.org/abs/2509.18724v1>.

*Commentary.*

The root set zeta^exp(S)=1 has cardinality exp(S). Extended cardinality retains the distinction between a finite root count and an infinite set.

**Definition 1.9 (Both admissibility branches).**

Lean statement: `D5/S0/Certificates/Algebra/WangConjecture53Refutation.Admissible`

*Formalization.* `D5/S0/Certificates/Algebra/WangConjecture53Refutation.Admissible` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Guoqing Wang (2025). *Semigroup rings and algebraically independent sequences with respect to idempotents in commutative semigroups*. URL: <https://arxiv.org/abs/2509.18724v1>.

*Commentary.*

Either the splitting condition holds, or K has prime characteristic p and the exponent is a power of p. Branch (i) requires neither algebraic closure nor characteristic zero. Q is used only for the counterexample.

**Definition 1.10 (A factor in the ordinary semigroup algebra).**

Lean statement: `D5/S0/Certificates/Algebra/WangConjecture53Refutation.factor`

*Formalization.* `D5/S0/Certificates/Algebra/WangConjecture53Refutation.factor` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Guoqing Wang (2025). *Semigroup rings and algebraically independent sequences with respect to idempotents in commutative semigroups*. URL: <https://arxiv.org/abs/2509.18724v1>.

*Commentary.*

Reuse AddMonoidAlgebra K S: coefficients are finitely supported on all of S, and multiplication is the upstream convolution. The factor is the basis vector at s minus a times the basis vector at its cyclic idempotent. Even an absorbing semigroup label remains an independent basis vector.

**Definition 1.11 (Positive products in a possibly nonunital algebra).**

Lean statement: `D5/S0/Certificates/Algebra/WangConjecture53Refutation.factorProduct`

*Formalization.* `D5/S0/Certificates/Algebra/WangConjecture53Refutation.factorProduct` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Guoqing Wang (2025). *Semigroup rings and algebraically independent sequences with respect to idempotents in commutative semigroups*. URL: <https://arxiv.org/abs/2509.18724v1>.

*Commentary.*

Multiply the ordered factors associatively for every positive length. The empty branch is zero and supplies no positive admissible length; no unit is asserted for an arbitrary nonunital semigroup algebra.

**Definition 1.12 (Every tuple of individually nonzero coefficients).**

Lean statement: `D5/S0/Certificates/Algebra/WangConjecture53Refutation.GoodSequence`

*Formalization.* `D5/S0/Certificates/Algebra/WangConjecture53Refutation.GoodSequence` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Guoqing Wang (2025). *Semigroup rings and algebraically independent sequences with respect to idempotents in commutative semigroups*. URL: <https://arxiv.org/abs/2509.18724v1>.

*Commentary.*

Quantify over a separate coefficient at each position, requiring it to be nonzero at every position of the finite sequence. Coefficients outside that prefix do not enter the product. Repeated semigroup labels still have independently chosen coefficients.

**Definition 1.13 (The algebraic Davenport constant).**

Lean statement: `D5/S0/Certificates/Algebra/WangConjecture53Refutation.algebraicD`

*Formalization.* `D5/S0/Certificates/Algebra/WangConjecture53Refutation.algebraicD` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Guoqing Wang (2025). *Semigroup rings and algebraically independent sequences with respect to idempotents in commutative semigroups*. URL: <https://arxiv.org/abs/2509.18724v1>.

*Commentary.*

Take the ENat supremum of all admissible finite lengths. Infinity means unboundedness of finite lengths, without defining an infinite product. Length zero contributes only the bottom of this supremum. In particular, an empty semigroup has constant zero as stipulated by the paper.

**Definition 1.14 (Actual principal ideals).**

Lean statement: `D5/S0/Certificates/Algebra/WangConjecture53Refutation.Below`

*Formalization.* `D5/S0/Certificates/Algebra/WangConjecture53Refutation.Below` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Guoqing Wang (2025). *Semigroup rings and algebraically independent sequences with respect to idempotents in commutative semigroups*. URL: <https://arxiv.org/abs/2509.18724v1>.

*Commentary.*

Membership means x=a or x=a+c for a genuine semigroup element c. Including a itself does not require an adjoined identity.

**Definition 1.15 (Green H-equivalence).**

Lean statement: `D5/S0/Certificates/Algebra/WangConjecture53Refutation.Green`

*Formalization.* `D5/S0/Certificates/Algebra/WangConjecture53Refutation.Green` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Guoqing Wang (2025). *Semigroup rings and algebraically independent sequences with respect to idempotents in commutative semigroups*. URL: <https://arxiv.org/abs/2509.18724v1>.

*Commentary.*

Two elements are equivalent exactly when their principal ideals are equal.

**Definition 1.16 (The Green congruence).**

Lean statement: `D5/S0/Certificates/Algebra/WangConjecture53Refutation.greenCon`

*Formalization.* `D5/S0/Certificates/Algebra/WangConjecture53Refutation.greenCon` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Guoqing Wang (2025). *Semigroup rings and algebraically independent sequences with respect to idempotents in commutative semigroups*. URL: <https://arxiv.org/abs/2509.18724v1>.

*Commentary.*

Equality of principal ideals is an additive congruence in a commutative semigroup; the proof establishes compatibility with addition. Use its upstream AddCon quotient and canonical quotient map directly. For the witness, an exact finite check of principal ideals proves this map injective.

**Definition 1.17 (Sequence sums and existing identities).**

Lean statement: `D5/S0/Certificates/Algebra/WangConjecture53Refutation.SequenceSum`

*Formalization.* `D5/S0/Certificates/Algebra/WangConjecture53Refutation.SequenceSum` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Guoqing Wang (2025). *Semigroup rings and algebraically independent sequences with respect to idempotents in commutative semigroups*. URL: <https://arxiv.org/abs/2509.18724v1>.

*Commentary.*

A nonempty list sums by the semigroup operation. The empty list sums to a only when a is already a two-sided identity in that semigroup.

**Definition 1.18 (Irreducibility at a specified sum).**

Lean statement: `D5/S0/Certificates/Algebra/WangConjecture53Refutation.IrreducibleAt`

*Formalization.* `D5/S0/Certificates/Algebra/WangConjecture53Refutation.IrreducibleAt` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Guoqing Wang (2025). *Semigroup rings and algebraically independent sequences with respect to idempotents in commutative semigroups*. URL: <https://arxiv.org/abs/2509.18724v1>.

*Commentary.*

The sequence sums to a and no proper sublist has the same sum. Empty sublists are included. In a commutative semigroup, lists enumerate the unordered sequences and their submultisets without changing sums.

**Definition 1.19 (The relative Davenport constant).**

Lean statement: `D5/S0/Certificates/Algebra/WangConjecture53Refutation.relativeD`

*Formalization.* `D5/S0/Certificates/Algebra/WangConjecture53Refutation.relativeD` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Guoqing Wang (2025). *Semigroup rings and algebraically independent sequences with respect to idempotents in commutative semigroups*. URL: <https://arxiv.org/abs/2509.18724v1>.

*Commentary.*

Take the ENat supremum of irreducible lengths at the given sum, retaining the source's relative constant rather than a global reducibility threshold.

**Definition 1.20 (The actual H-class).**

Lean statement: `D5/S0/Certificates/Algebra/WangConjecture53Refutation.HClass`

*Formalization.* `D5/S0/Certificates/Algebra/WangConjecture53Refutation.HClass` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Guoqing Wang (2025). *Semigroup rings and algebraically independent sequences with respect to idempotents in commutative semigroups*. URL: <https://arxiv.org/abs/2509.18724v1>.

*Commentary.*

The class is a subtype of S consisting of elements with the same principal ideal.

**Definition 1.21 (Actual stabilizer translations).**

Lean statement: `D5/S0/Certificates/Algebra/WangConjecture53Refutation.Gamma`

*Formalization.* `D5/S0/Certificates/Algebra/WangConjecture53Refutation.Gamma` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Guoqing Wang (2025). *Semigroup rings and algebraically independent sequences with respect to idempotents in commutative semigroups*. URL: <https://arxiv.org/abs/2509.18724v1>.

*Commentary.*

The carrier consists of maps H_a to itself realized by c+x for a genuine c in S. Equal maps are identified. Addition is composition, corresponding to addition of realizing elements. No identity is adjoined; the carrier is allowed to be empty.

**Definition 1.22 (The source epsilon).**

Lean statement: `D5/S0/Certificates/Algebra/WangConjecture53Refutation.epsilon`

*Formalization.* `D5/S0/Certificates/Algebra/WangConjecture53Refutation.epsilon` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Guoqing Wang (2025). *Semigroup rings and algebraically independent sequences with respect to idempotents in commutative semigroups*. URL: <https://arxiv.org/abs/2509.18724v1>.

*Commentary.*

Epsilon is zero exactly for a positive cyclic group, and one otherwise.

**Definition 1.23 (The complete proposed right side).**

Lean statement: `D5/S0/Certificates/Algebra/WangConjecture53Refutation.rightSide`

*Formalization.* `D5/S0/Certificates/Algebra/WangConjecture53Refutation.rightSide` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Guoqing Wang (2025). *Semigroup rings and algebraically independent sequences with respect to idempotents in commutative semigroups*. URL: <https://arxiv.org/abs/2509.18724v1>.

*Commentary.*

Take the supremum over a in S of epsilon(a) times the relative Davenport constant at the canonical quotient image, plus the algebraic constant of the actual translation semigroup. For finite S this is the finite maximum appearing in the conjecture.

**Definition 1.24 (The complete universal assertion).**

Lean statement: `D5/S0/Certificates/Algebra/WangConjecture53Refutation.claim`

*Formalization.* `D5/S0/Certificates/Algebra/WangConjecture53Refutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Guoqing Wang (2025). *Semigroup rings and algebraically independent sequences with respect to idempotents in commutative semigroups*. URL: <https://arxiv.org/abs/2509.18724v1>.

*Commentary.*

Quantify over all finite commutative semigroups and fields satisfying either source branch. Assert equality of the two source constants. The finite monoid counterexample is substituted into this full semigroup assertion; the claim imposes no global monoid or sequence-length restriction.

**Definition 1.25 (The six semigroup labels).**

Lean statement: `D5/S0/Certificates/Algebra/WangConjecture53Refutation.Model`

*Formalization.* `D5/S0/Certificates/Algebra/WangConjecture53Refutation.Model` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Guoqing Wang (2025). *Semigroup rings and algebraically independent sequences with respect to idempotents in commutative semigroups*. URL: <https://arxiv.org/abs/2509.18724v1>.

*Commentary.*

The carrier is {0,1} times {0,1,2}. All six labels remain in the ordinary algebra.

**Definition 1.26 (Union and truncated addition).**

Lean statement: `D5/S0/Certificates/Algebra/WangConjecture53Refutation.modelAdd`

*Formalization.* `D5/S0/Certificates/Algebra/WangConjecture53Refutation.modelAdd` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Guoqing Wang (2025). *Semigroup rings and algebraically independent sequences with respect to idempotents in commutative semigroups*. URL: <https://arxiv.org/abs/2509.18724v1>.

*Commentary.*

Add by maximum in the first coordinate and min(2,n+m) in the second. The finite commutative monoid laws are checked by Lean's kernel.

**Definition 1.27 (Cyclic idempotents of the witness).**

Lean statement: `D5/S0/Certificates/Algebra/WangConjecture53Refutation.modelE`

*Formalization.* `D5/S0/Certificates/Algebra/WangConjecture53Refutation.modelE` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Guoqing Wang (2025). *Semigroup rings and algebraically independent sequences with respect to idempotents in commutative semigroups*. URL: <https://arxiv.org/abs/2509.18724v1>.

*Commentary.*

Level zero remains zero; levels one and two have cyclic idempotent level two, with the first coordinate retained.

**Definition 1.28 (The transient term).**

Lean statement: `D5/S0/Certificates/Algebra/WangConjecture53Refutation.transient`

*Formalization.* `D5/S0/Certificates/Algebra/WangConjecture53Refutation.transient` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Guoqing Wang (2025). *Semigroup rings and algebraically independent sequences with respect to idempotents in commutative semigroups*. URL: <https://arxiv.org/abs/2509.18724v1>.

*Commentary.*

The label (0,1) gives an always-nonzero singleton factor, detected by its coefficient one at this independent basis label.

**Definition 1.29 (The marker term).**

Lean statement: `D5/S0/Certificates/Algebra/WangConjecture53Refutation.marker`

*Formalization.* `D5/S0/Certificates/Algebra/WangConjecture53Refutation.marker` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Guoqing Wang (2025). *Semigroup rings and algebraically independent sequences with respect to idempotents in commutative semigroups*. URL: <https://arxiv.org/abs/2509.18724v1>.

*Commentary.*

The label (1,0), together with the transient term, forms an irreducible two-term sequence at the target in the canonical quotient.

**Definition 1.30 (The target quotient class).**

Lean statement: `D5/S0/Certificates/Algebra/WangConjecture53Refutation.target`

*Formalization.* `D5/S0/Certificates/Algebra/WangConjecture53Refutation.target` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Guoqing Wang (2025). *Semigroup rings and algebraically independent sequences with respect to idempotents in commutative semigroups*. URL: <https://arxiv.org/abs/2509.18724v1>.

*Commentary.*

The target is (1,1). Its positive cyclic semigroup is not a group, so its epsilon equals one.

**Theorem 1.31 (Conjecture 5.3 has a negative answer).**

Lean statement: `D5/S0/Certificates/Algebra/WangConjecture53Refutation.result`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Algebra/WangConjecture53Refutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/wang-conjecture53` (refuted) by `D5/S0/Certificates/Algebra/WangConjecture53Refutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"wang-conjecture53","declaration_gid":"D5/S0/Certificates/Algebra/WangConjecture53Refutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Guoqing Wang (2025). *Semigroup rings and algebraically independent sequences with respect to idempotents in commutative semigroups*. URL: <https://arxiv.org/abs/2509.18724v1>.

*Commentary.*

Over Q, every nonzero coefficient assignment leaves the singleton at (0,1) nonzero. The all-ones assignment kills every sequence of length at least two: an idempotent yields a zero factor, while two transient factors have four equal basis products and cancel. Thus d(S,Q)=1. Principal ideals distinguish all six labels. At (1,1), the quotient sequence [(0,1),(1,0)] is irreducible and epsilon is one, so the proposed right side is at least two. Q meets splitting branch (i), since exp(S)=1. This single admissible instance refutes the full universal equality. The exact right-side maximum, minimality, independent novelty, and separate Conjecture 3.26 are not claimed.

## References

- Truth anchor: `D5/S0/Certificates/Algebra/WangConjecture53Refutation.Admissible`
- Truth anchor: `D5/S0/Certificates/Algebra/WangConjecture53Refutation.Below`
- Truth anchor: `D5/S0/Certificates/Algebra/WangConjecture53Refutation.CyclicIsGroup`
- Truth anchor: `D5/S0/Certificates/Algebra/WangConjecture53Refutation.Gamma`
- Truth anchor: `D5/S0/Certificates/Algebra/WangConjecture53Refutation.GoodSequence`
- Truth anchor: `D5/S0/Certificates/Algebra/WangConjecture53Refutation.Green`
- Truth anchor: `D5/S0/Certificates/Algebra/WangConjecture53Refutation.HClass`
- Truth anchor: `D5/S0/Certificates/Algebra/WangConjecture53Refutation.IrreducibleAt`
- Truth anchor: `D5/S0/Certificates/Algebra/WangConjecture53Refutation.IsCyclicIdempotent`
- Truth anchor: `D5/S0/Certificates/Algebra/WangConjecture53Refutation.Model`
- Truth anchor: `D5/S0/Certificates/Algebra/WangConjecture53Refutation.SequenceSum`
- Truth anchor: `D5/S0/Certificates/Algebra/WangConjecture53Refutation.Splitting`
- Truth anchor: `D5/S0/Certificates/Algebra/WangConjecture53Refutation.algebraicD`
- Truth anchor: `D5/S0/Certificates/Algebra/WangConjecture53Refutation.claim`
- Truth anchor: `D5/S0/Certificates/Algebra/WangConjecture53Refutation.cyclic`
- Truth anchor: `D5/S0/Certificates/Algebra/WangConjecture53Refutation.cyclicIdempotent`
- Truth anchor: `D5/S0/Certificates/Algebra/WangConjecture53Refutation.epsilon`
- Truth anchor: `D5/S0/Certificates/Algebra/WangConjecture53Refutation.factor`
- Truth anchor: `D5/S0/Certificates/Algebra/WangConjecture53Refutation.factorProduct`
- Truth anchor: `D5/S0/Certificates/Algebra/WangConjecture53Refutation.greenCon`
- Truth anchor: `D5/S0/Certificates/Algebra/WangConjecture53Refutation.marker`
- Truth anchor: `D5/S0/Certificates/Algebra/WangConjecture53Refutation.modelAdd`
- Truth anchor: `D5/S0/Certificates/Algebra/WangConjecture53Refutation.modelE`
- Truth anchor: `D5/S0/Certificates/Algebra/WangConjecture53Refutation.period`
- Truth anchor: `D5/S0/Certificates/Algebra/WangConjecture53Refutation.positiveMultiple`
- Truth anchor: `D5/S0/Certificates/Algebra/WangConjecture53Refutation.relativeD`
- Truth anchor: `D5/S0/Certificates/Algebra/WangConjecture53Refutation.result`
- Truth anchor: `D5/S0/Certificates/Algebra/WangConjecture53Refutation.rightSide`
- Truth anchor: `D5/S0/Certificates/Algebra/WangConjecture53Refutation.semigroupExponent`
- Truth anchor: `D5/S0/Certificates/Algebra/WangConjecture53Refutation.target`
- Truth anchor: `D5/S0/Certificates/Algebra/WangConjecture53Refutation.transient`
