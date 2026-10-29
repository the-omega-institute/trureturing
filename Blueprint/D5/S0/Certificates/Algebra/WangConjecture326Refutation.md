# Wang Conjecture 3.26: an Infinite Ordinary Semigroup Algebra Counterexample

## Abstract

One infinite commutative periodic semigroup over Q has algebraic Davenport constant at most one and unbounded relative constants in its actual Green quotient.

**Definition 1.1 (Positive cyclic generation).**

Lean statement: `D5/S0/Certificates/Algebra/WangConjecture326Refutation.cyclic`

*Formalization.* `D5/S0/Certificates/Algebra/WangConjecture326Refutation.cyclic` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Guoqing Wang (2025). *Semigroup rings and algebraically independent sequences with respect to idempotents in commutative semigroups*. URL: <https://arxiv.org/abs/2509.18724v1>.

*Commentary.*

Use the native additive subsemigroup closure of {a}, containing positive sums only. No identity or zeroth multiple is adjoined.

**Definition 1.2 (Pointwise periodicity).**

Lean statement: `D5/S0/Certificates/Algebra/WangConjecture326Refutation.Periodic`

*Formalization.* `D5/S0/Certificates/Algebra/WangConjecture326Refutation.Periodic` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Guoqing Wang (2025). *Semigroup rings and algebraically independent sequences with respect to idempotents in commutative semigroups*. URL: <https://arxiv.org/abs/2509.18724v1>.

*Commentary.*

Every individual cyclic closure is finite. There is no Finite S or Fintype S hypothesis, so the statement includes infinite semigroups.

**Definition 1.3 (Actual cyclic idempotency).**

Lean statement: `D5/S0/Certificates/Algebra/WangConjecture326Refutation.IsCyclicIdempotent`

*Formalization.* `D5/S0/Certificates/Algebra/WangConjecture326Refutation.IsCyclicIdempotent` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Guoqing Wang (2025). *Semigroup rings and algebraically independent sequences with respect to idempotents in commutative semigroups*. URL: <https://arxiv.org/abs/2509.18724v1>.

*Commentary.*

The selected element belongs to the positive cyclic subsemigroup and satisfies e+e=e.

**Definition 1.4 (Cyclic idempotent selection).**

Lean statement: `D5/S0/Certificates/Algebra/WangConjecture326Refutation.cyclicIdempotent`

*Formalization.* `D5/S0/Certificates/Algebra/WangConjecture326Refutation.cyclicIdempotent` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Guoqing Wang (2025). *Semigroup rings and algebraically independent sequences with respect to idempotents in commutative semigroups*. URL: <https://arxiv.org/abs/2509.18724v1>.

*Commentary.*

Select an idempotent in the cyclic closure. Under pointwise periodicity Mathlib's compact-subsemigroup theorem proves existence using only the finite cyclic set with the discrete topology. The fallback is unreachable. The witness calculation identifies this choice with its unique cyclic idempotent.

**Definition 1.5 (A positive cyclic group with its own identity).**

Lean statement: `D5/S0/Certificates/Algebra/WangConjecture326Refutation.CyclicIsGroup`

*Formalization.* `D5/S0/Certificates/Algebra/WangConjecture326Refutation.CyclicIsGroup` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Guoqing Wang (2025). *Semigroup rings and algebraically independent sequences with respect to idempotents in commutative semigroups*. URL: <https://arxiv.org/abs/2509.18724v1>.

*Commentary.*

Quantify an identity and inverses inside the actual positive cyclic subsemigroup. The identity need not equal an ambient monoid identity.

**Definition 1.6 (The full ordinary convolution algebra).**

Lean statement: `D5/S0/Certificates/Algebra/WangConjecture326Refutation.factor`

*Formalization.* `D5/S0/Certificates/Algebra/WangConjecture326Refutation.factor` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Guoqing Wang (2025). *Semigroup rings and algebraically independent sequences with respect to idempotents in commutative semigroups*. URL: <https://arxiv.org/abs/2509.18724v1>.

*Commentary.*

The factor is single(a,1)-single(e(a),c) in upstream AddMonoidAlgebra R S. R is any commutative unitary ring. Every label, including level two, is retained.

**Definition 1.7 (Positive products without an algebra unit).**

Lean statement: `D5/S0/Certificates/Algebra/WangConjecture326Refutation.factorProduct`

*Formalization.* `D5/S0/Certificates/Algebra/WangConjecture326Refutation.factorProduct` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Guoqing Wang (2025). *Semigroup rings and algebraically independent sequences with respect to idempotents in commutative semigroups*. URL: <https://arxiv.org/abs/2509.18724v1>.

*Commentary.*

For a nonempty list start with its first factor and fold multiplication over the indexed tail. Each coefficient uses its own original position. The empty branch is zero, contributing only zero to the length supremum.

**Definition 1.8 (Every independently nonzero coefficient tuple).**

Lean statement: `D5/S0/Certificates/Algebra/WangConjecture326Refutation.GoodSequence`

*Formalization.* `D5/S0/Certificates/Algebra/WangConjecture326Refutation.GoodSequence` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Guoqing Wang (2025). *Semigroup rings and algebraically independent sequences with respect to idempotents in commutative semigroups*. URL: <https://arxiv.org/abs/2509.18724v1>.

*Commentary.*

Quantify c:N->R and require c(i) nonzero at every occupied position. Values outside the finite prefix are unused. Equal labels retain distinct positions.

**Definition 1.9 (The algebraic Davenport constant).**

Lean statement: `D5/S0/Certificates/Algebra/WangConjecture326Refutation.algebraicD`

*Formalization.* `D5/S0/Certificates/Algebra/WangConjecture326Refutation.algebraicD` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Guoqing Wang (2025). *Semigroup rings and algebraically independent sequences with respect to idempotents in commutative semigroups*. URL: <https://arxiv.org/abs/2509.18724v1>.

*Commentary.*

The ENat supremum is taken over all finite good sequence lengths. Top means unbounded finite lengths, without an infinite product.

**Definition 1.10 (Actual principal ideals).**

Lean statement: `D5/S0/Certificates/Algebra/WangConjecture326Refutation.principalIdeal`

*Formalization.* `D5/S0/Certificates/Algebra/WangConjecture326Refutation.principalIdeal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Guoqing Wang (2025). *Semigroup rings and algebraically independent sequences with respect to idempotents in commutative semigroups*. URL: <https://arxiv.org/abs/2509.18724v1>.

*Commentary.*

The principal ideal contains a itself and every a+c for c in S, with no artificial identity. In the witness membership is A subset B and k<=l.

**Definition 1.11 (The actual Green congruence).**

Lean statement: `D5/S0/Certificates/Algebra/WangConjecture326Refutation.greenCon`

*Formalization.* `D5/S0/Certificates/Algebra/WangConjecture326Refutation.greenCon` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Guoqing Wang (2025). *Semigroup rings and algebraically independent sequences with respect to idempotents in commutative semigroups*. URL: <https://arxiv.org/abs/2509.18724v1>.

*Commentary.*

The relation is equality of principal ideals. Compatibility with addition is proved in the definition. Use the native AddCon quotient and quotient map.

**Definition 1.12 (Sums including the empty subsequence).**

Lean statement: `D5/S0/Certificates/Algebra/WangConjecture326Refutation.SequenceSum`

*Formalization.* `D5/S0/Certificates/Algebra/WangConjecture326Refutation.SequenceSum` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Guoqing Wang (2025). *Semigroup rings and algebraically independent sequences with respect to idempotents in commutative semigroups*. URL: <https://arxiv.org/abs/2509.18724v1>.

*Commentary.*

Nonempty lists sum by folding the semigroup operation. Empty lists sum only to an existing two-sided identity. For any monoid this is equivalent to List.sum.

**Definition 1.13 (Irreducibility at a specified sum).**

Lean statement: `D5/S0/Certificates/Algebra/WangConjecture326Refutation.IrreducibleAt`

*Formalization.* `D5/S0/Certificates/Algebra/WangConjecture326Refutation.IrreducibleAt` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Guoqing Wang (2025). *Semigroup rings and algebraically independent sequences with respect to idempotents in commutative semigroups*. URL: <https://arxiv.org/abs/2509.18724v1>.

*Commentary.*

The list sums to a, and no shorter sublist has that sum, including the empty sublist. Lists enumerate unordered source sequences in a commutative semigroup.

**Definition 1.14 (The relative Davenport constant).**

Lean statement: `D5/S0/Certificates/Algebra/WangConjecture326Refutation.relativeD`

*Formalization.* `D5/S0/Certificates/Algebra/WangConjecture326Refutation.relativeD` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Guoqing Wang (2025). *Semigroup rings and algebraically independent sequences with respect to idempotents in commutative semigroups*. URL: <https://arxiv.org/abs/2509.18724v1>.

*Commentary.*

Take the ENat supremum of all irreducible lengths at the specified element.

**Definition 1.15 (The source's uniform filtered supremum).**

Lean statement: `D5/S0/Certificates/Algebra/WangConjecture326Refutation.nongroupSup`

*Formalization.* `D5/S0/Certificates/Algebra/WangConjecture326Refutation.nongroupSup` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Guoqing Wang (2025). *Semigroup rings and algebraically independent sequences with respect to idempotents in commutative semigroups*. URL: <https://arxiv.org/abs/2509.18724v1>.

*Commentary.*

Take one supremum over all a whose positive cyclic subsemigroup is not a group, using relativeD at the actual canonical quotient image of a.

**Definition 1.16 (The complete published universal implication).**

$$claim:\operatorname{Prop} \Leftrightarrow \forall (S:\operatorname{Type}), [\operatorname{AddCommSemigroup}(S)] (\operatorname{Periodic}(S)) \Rightarrow (\forall (R:\operatorname{Type}), [\operatorname{CommRing}(R)] (\operatorname{algebraicD}(S,R) < \infty) \Rightarrow (\operatorname{nongroupSup}(S) < \infty))$$

*Formalization.* `D5/S0/Certificates/Algebra/WangConjecture326Refutation.claim` (`✓ std3`).

*Citation.* Guoqing Wang (2025). *Semigroup rings and algebraically independent sequences with respect to idempotents in commutative semigroups*. URL: <https://arxiv.org/abs/2509.18724v1>.

*Commentary.*

Every commutative semigroup, including infinite and nonunital ones, is in scope. Periodic means pointwise finite positive cyclic closure. R ranges over every commutative unitary ring, with no field or nontriviality restriction. The antecedent is finiteness of the ordinary algebraic constant; the consequent is one uniform finite bound on the source's filtered relative constants. The closed Prop uses ordinary small carriers.

**Definition 1.17 (One fixed infinite carrier).**

Lean statement: `D5/S0/Certificates/Algebra/WangConjecture326Refutation.Model`

*Formalization.* `D5/S0/Certificates/Algebra/WangConjecture326Refutation.Model` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Guoqing Wang (2025). *Semigroup rings and algebraically independent sequences with respect to idempotents in commutative semigroups*. URL: <https://arxiv.org/abs/2509.18724v1>.

*Commentary.*

The carrier is Finset(N) times Fin 3. The map i maps to ({i},0) is injective, giving a separate certificate of infinitude. This instance is not consumed by result and is neither a result helper nor an escape witness. No finite truncation replaces this carrier.

**Definition 1.18 (Union and min-capped addition).**

Lean statement: `D5/S0/Certificates/Algebra/WangConjecture326Refutation.modelAdd`

*Formalization.* `D5/S0/Certificates/Algebra/WangConjecture326Refutation.modelAdd` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Guoqing Wang (2025). *Semigroup rings and algebraically independent sequences with respect to idempotents in commutative semigroups*. URL: <https://arxiv.org/abs/2509.18724v1>.

*Commentary.*

Add (A,k) and (B,l) as (A union B,min(2,k+l)). The Fin 3 levels use this custom min-cap operation, never modular addition. The identity is (empty,0).

**Definition 1.19 (The witness cyclic idempotent).**

Lean statement: `D5/S0/Certificates/Algebra/WangConjecture326Refutation.modelE`

*Formalization.* `D5/S0/Certificates/Algebra/WangConjecture326Refutation.modelE` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Guoqing Wang (2025). *Semigroup rings and algebraically independent sequences with respect to idempotents in commutative semigroups*. URL: <https://arxiv.org/abs/2509.18724v1>.

*Commentary.*

Retain the finite subset; level zero remains zero, and positive levels go to level two. The positive cyclic closure is exactly {x,E(x)}.

**Definition 1.20 (A weight detecting relative length).**

Lean statement: `D5/S0/Certificates/Algebra/WangConjecture326Refutation.weight`

*Formalization.* `D5/S0/Certificates/Algebra/WangConjecture326Refutation.weight` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Guoqing Wang (2025). *Semigroup rings and algebraically independent sequences with respect to idempotents in commutative semigroups*. URL: <https://arxiv.org/abs/2509.18724v1>.

*Commentary.*

Set w(A,k)=card(A)+1(k!=0). Union cardinality and the nonzero-level indicator make this weight subadditive. It bounds the weight of a sum by the length of any sequence whose terms all have weight one.

**Definition 1.21 (One sequence for every natural n).**

Lean statement: `D5/S0/Certificates/Algebra/WangConjecture326Refutation.witnessSequence`

*Formalization.* `D5/S0/Certificates/Algebra/WangConjecture326Refutation.witnessSequence` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Guoqing Wang (2025). *Semigroup rings and algebraically independent sequences with respect to idempotents in commutative semigroups*. URL: <https://arxiv.org/abs/2509.18724v1>.

*Commentary.*

Start with (empty,1), then add one term ({i},0) for each i<n. Each term has weight one. The length is n+1 and the sum is target(n).

**Definition 1.22 (The targets inside the same semigroup).**

Lean statement: `D5/S0/Certificates/Algebra/WangConjecture326Refutation.target`

*Formalization.* `D5/S0/Certificates/Algebra/WangConjecture326Refutation.target` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Guoqing Wang (2025). *Semigroup rings and algebraically independent sequences with respect to idempotents in commutative semigroups*. URL: <https://arxiv.org/abs/2509.18724v1>.

*Commentary.*

The target is (range(n),1). Its weight is n+1. Its two-element positive cyclic subsemigroup has no identity of its own, so it satisfies the nongroup filter.

**Theorem 1.23 (Conjecture 3.26 is false).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Algebra/WangConjecture326Refutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/wang-conjecture326` (refuted) by `D5/S0/Certificates/Algebra/WangConjecture326Refutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"wang-conjecture326","declaration_gid":"D5/S0/Certificates/Algebra/WangConjecture326Refutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Guoqing Wang (2025). *Semigroup rings and algebraically independent sequences with respect to idempotents in commutative semigroups*. URL: <https://arxiv.org/abs/2509.18724v1>.

*Commentary.*

Over Q the all-ones coefficient assignment kills every sequence of length at least two. An idempotent gives a zero factor; two level-one terms give four coincident basis products whose coefficients cancel. Thus algebraicD(Model,Q)<=1. Principal ideals distinguish every model element, so the actual Green quotient map is injective. Every subsequence of witnessSequence(n) with sum target(n) has at least n+1 terms by the subadditive weight, proving quotient irreducibility. Every target is cyclic nongroup, and its relative constant is at least n+1. The filtered supremum is therefore top inside this single infinite periodic semigroup. This negates the entire original implication. Exact individual constants, novelty, priority, and the separate Conjecture 5.3 are not conclusions of this theorem. Every authored theorem has proof_shape: bind-only. The admission basis is the named external Tier1 open-problem-resolution exception in issue 23896. Consumed private theorems organize this derivation and supply no escape witness. The only public authored theorem is this designated literal refutation, exempt from the four-slot escape audit.

## References

- Truth anchor: `D5/S0/Certificates/Algebra/WangConjecture326Refutation.CyclicIsGroup`
- Truth anchor: `D5/S0/Certificates/Algebra/WangConjecture326Refutation.GoodSequence`
- Truth anchor: `D5/S0/Certificates/Algebra/WangConjecture326Refutation.IrreducibleAt`
- Truth anchor: `D5/S0/Certificates/Algebra/WangConjecture326Refutation.IsCyclicIdempotent`
- Truth anchor: `D5/S0/Certificates/Algebra/WangConjecture326Refutation.Model`
- Truth anchor: `D5/S0/Certificates/Algebra/WangConjecture326Refutation.Periodic`
- Truth anchor: `D5/S0/Certificates/Algebra/WangConjecture326Refutation.SequenceSum`
- Truth anchor: `D5/S0/Certificates/Algebra/WangConjecture326Refutation.algebraicD`
- Truth anchor: `D5/S0/Certificates/Algebra/WangConjecture326Refutation.claim`
- Truth anchor: `D5/S0/Certificates/Algebra/WangConjecture326Refutation.cyclic`
- Truth anchor: `D5/S0/Certificates/Algebra/WangConjecture326Refutation.cyclicIdempotent`
- Truth anchor: `D5/S0/Certificates/Algebra/WangConjecture326Refutation.factor`
- Truth anchor: `D5/S0/Certificates/Algebra/WangConjecture326Refutation.factorProduct`
- Truth anchor: `D5/S0/Certificates/Algebra/WangConjecture326Refutation.greenCon`
- Truth anchor: `D5/S0/Certificates/Algebra/WangConjecture326Refutation.modelAdd`
- Truth anchor: `D5/S0/Certificates/Algebra/WangConjecture326Refutation.modelE`
- Truth anchor: `D5/S0/Certificates/Algebra/WangConjecture326Refutation.nongroupSup`
- Truth anchor: `D5/S0/Certificates/Algebra/WangConjecture326Refutation.principalIdeal`
- Truth anchor: `D5/S0/Certificates/Algebra/WangConjecture326Refutation.relativeD`
- Truth anchor: `D5/S0/Certificates/Algebra/WangConjecture326Refutation.result`
- Truth anchor: `D5/S0/Certificates/Algebra/WangConjecture326Refutation.target`
- Truth anchor: `D5/S0/Certificates/Algebra/WangConjecture326Refutation.weight`
- Truth anchor: `D5/S0/Certificates/Algebra/WangConjecture326Refutation.witnessSequence`
