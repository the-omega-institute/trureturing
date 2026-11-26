# Character expansion of the elementary free sieve

## Abstract

Character expansion of the elementary free sieve

**Definition 1.1 (The local density product).**

$$\operatorname{theta}\left(e\right) = \prod_{q \in \operatorname{primeFactors}\left(e\right)} {1 - \frac{1}{q}}$$

*Formalization.* `D5/S3/Arith/PrimitiveRoot/CharacterExpansion.theta` (`✓ std3`).

*Citation.* S. D. Cohen, T. Oliveira e Silva, T. S. Trudgian (2015). *On Grosswald's conjecture on primitive roots*. DOI: [10.4064/aa8109-12-2015](https://doi.org/10.4064/aa8109-12-2015). URL: <https://doi.org/10.4064/aa8109-12-2015>.

*Commentary.*

The product runs over the distinct prime divisors of e. Each factor is positive, including the empty product at e=1.

**Theorem 1.2 (The reciprocal-sum criterion for signed coefficient bounds).**

$$\forall e \in \mathbb{N},\; \forall T \in \operatorname{Finset}\left(\mathbb{N}\right),\; \sum_{t \in T} {\frac{1}{t}} \le \frac{\operatorname{card}\left(T\right)}{2} \Leftrightarrow \left(\operatorname{pow}\left(2, \operatorname{omega}\left(e\right)\right) - \operatorname{delta}\left(T\right) \le \operatorname{K}\left(e, T\right) \land 0 \le \operatorname{K}\left(e, T\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/PrimitiveRoot/CharacterExpansion.errorCoefficient_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* K. McGown, E. Treviño, T. Trudgian (2016). *Resolving Grosswald's conjecture on GRH*. DOI: [10.7169/facm/2016.55.2.5](https://doi.org/10.7169/facm/2016.55.2.5). URL: <https://doi.org/10.7169/facm/2016.55.2.5>.

*Commentary.*

The reciprocal sum over T is at most card(T)/2 exactly when 2^omega(e)-delta(T)<=K(e,T) and K(e,T)>=0, for every margin. It suffices that each member of T is at least two, allowing composites. In particular, the hypothesis holds for every set of primes. Nonnegativity alone does not identify K with the absolute error mass.

**Theorem 1.3 (Positive local density).**

$$\forall e \in \mathbb{N},\; 0 < \operatorname{theta}\left(e\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/PrimitiveRoot/CharacterExpansion.theta_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. D. Cohen, T. Oliveira e Silva, T. S. Trudgian (2015). *On Grosswald's conjecture on primitive roots*. DOI: [10.4064/aa8109-12-2015](https://doi.org/10.4064/aa8109-12-2015). URL: <https://doi.org/10.4064/aa8109-12-2015>.

*Commentary.*

Each prime divisor q is greater than one, so 1-1/q is positive. Their finite product is positive, also for e=0 and e=1.

**Definition 1.4 (The remaining-prime margin).**

$$\operatorname{delta}\left(T\right) = 1 - \sum_{t \in T} {\frac{1}{t}}$$

*Formalization.* `D5/S3/Arith/PrimitiveRoot/CharacterExpansion.delta` (`✓ std3`).

*Citation.* K. McGown, E. Treviño, T. Trudgian (2016). *Resolving Grosswald's conjecture on GRH*. DOI: [10.7169/facm/2016.55.2.5](https://doi.org/10.7169/facm/2016.55.2.5). URL: <https://doi.org/10.7169/facm/2016.55.2.5>.

*Commentary.*

The margin may be positive, zero or negative.

**Definition 1.5 (The combined error coefficient).**

$$\operatorname{K}\left(e, T\right) = \operatorname{delta}\left(T\right) \cdot \left(\operatorname{pow}\left(2, \operatorname{omega}\left(e\right)\right) - 1\right) + \left(\operatorname{card}\left(T\right) - 1 + \operatorname{delta}\left(T\right)\right) \cdot \operatorname{pow}\left(2, \operatorname{omega}\left(e\right)\right)$$

*Formalization.* `D5/S3/Arith/PrimitiveRoot/CharacterExpansion.errorCoefficient` (`✓ std3`).

*Citation.* K. McGown, E. Treviño, T. Trudgian (2016). *Resolving Grosswald's conjecture on GRH*. DOI: [10.7169/facm/2016.55.2.5](https://doi.org/10.7169/facm/2016.55.2.5). URL: <https://doi.org/10.7169/facm/2016.55.2.5>.

*Commentary.*

Here omega(e) is the number of distinct prime divisors of e. The cardinality of T is interpreted as a real number before subtracting one. This coefficient is nonnegative for every set of sieve primes. For delta>=0 it bounds the total nonprincipal coefficient mass divided by theta(e) when T is disjoint from the prime support of e. K_abs=K exactly when delta>=0 or e has no prime factors.

**Definition 1.6 (Absolute coefficient mass for every margin).**

$$\operatorname{Kabs}\left(e, T\right) = \operatorname{abs}\left(\operatorname{delta}\left(T\right)\right) \cdot \left(\operatorname{pow}\left(2, \operatorname{omega}\left(e\right)\right) - 1\right) + \left(\operatorname{card}\left(T\right) - 1 + \operatorname{delta}\left(T\right)\right) \cdot \operatorname{pow}\left(2, \operatorname{omega}\left(e\right)\right)$$

*Formalization.* `D5/S3/Arith/PrimitiveRoot/CharacterExpansion.errorCoefficientAbs` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* K. McGown, E. Treviño, T. Trudgian (2016). *Resolving Grosswald's conjecture on GRH*. DOI: [10.7169/facm/2016.55.2.5](https://doi.org/10.7169/facm/2016.55.2.5). URL: <https://doi.org/10.7169/facm/2016.55.2.5>.

*Commentary.*

The first coefficient uses the absolute margin. The remaining coefficient is the sum of 1-1/t over T. No sign of delta is required.

**Theorem 1.7 (The complete coefficient agreement criterion).**

$$\forall e \in \mathbb{N},\; \forall T \in \operatorname{Finset}\left(\mathbb{N}\right),\; \operatorname{Kabs}\left(e, T\right) = \operatorname{K}\left(e, T\right) \Leftrightarrow \left(0 \le \operatorname{delta}\left(T\right) \lor \operatorname{primeFactors}\left(e\right) = \operatorname{empty}\left(\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/PrimitiveRoot/CharacterExpansion.errorCoefficientAbs_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* K. McGown, E. Treviño, T. Trudgian (2016). *Resolving Grosswald's conjecture on GRH*. DOI: [10.7169/facm/2016.55.2.5](https://doi.org/10.7169/facm/2016.55.2.5). URL: <https://doi.org/10.7169/facm/2016.55.2.5>.

*Commentary.*

K_abs-K=(abs(delta)-delta)(2^omega(e)-1). Thus equality holds exactly when delta is nonnegative or e has no prime factors.

**Theorem 1.8 (A two-sided elementary sieve estimate for every margin).**

$$\forall p \in \mathbb{N},\; \operatorname{Prime}\left(p\right) \Rightarrow \left(\forall W \in \operatorname{ZMod}\left(p\right) \to \mathbb{R},\; \forall e \in \mathbb{N},\; \left(\forall q \in \mathbb{N},\; q \in \operatorname{primeFactors}\left(e\right) \Rightarrow \operatorname{dvd}\left(q, p - 1\right)\right) \Rightarrow \left(\forall T \in \operatorname{Finset}\left(\mathbb{N}\right),\; \left(\forall t \in \mathbb{N},\; t \in T \Rightarrow \left(\operatorname{Prime}\left(t\right) \land \left(\operatorname{dvd}\left(t, p - 1\right) \land \left(\neg t \in \operatorname{primeFactors}\left(e\right)\right)\right)\right)\right) \Rightarrow \left(\forall M \in \mathbb{R},\; \left(\forall chi \in \operatorname{DirichletCharacter}\left(\mathbb{C}, p\right),\; \left(\neg chi = 1\right) \Rightarrow \left(\left(\operatorname{dvd}\left(\operatorname{orderOf}\left(chi\right), \prod_{q \in \operatorname{primeFactors}\left(e\right)} {q}\right) \lor \left(\exists t \in \mathbb{N},\; t \in T \land \operatorname{dvd}\left(\operatorname{orderOf}\left(chi\right), t \cdot \prod_{q \in \operatorname{primeFactors}\left(e\right)} {q}\right)\right)\right) \Rightarrow \operatorname{abs}\left(\operatorname{re}\left(\sum_{a \in \operatorname{Residues}\left(p\right)} {\operatorname{W}\left(a\right) \cdot \operatorname{chi}\left(a\right)}\right)\right) \le M\right)\right) \Rightarrow \operatorname{abs}\left(\sum_{a \in \operatorname{Units}\left(p\right)} {\operatorname{W}\left(a\right) \cdot \operatorname{if}\left(\forall q \in \mathbb{N},\; q \in \operatorname{primeFactors}\left(e\right) \Rightarrow \left(\neg a \in \operatorname{powerSubgroup}\left(\operatorname{Units}\left(p\right), q\right)\right), 1, 0\right) \cdot \left(1 - \operatorname{card}\left(\{t \in T \mid a \in \operatorname{powerSubgroup}\left(\operatorname{Units}\left(p\right), t\right)\}\right)\right)} - \operatorname{theta}\left(e\right) \cdot \operatorname{delta}\left(T\right) \cdot \sum_{a \in \operatorname{Units}\left(p\right)} {\operatorname{W}\left(a\right)}\right) \le \operatorname{theta}\left(e\right) \cdot \operatorname{Kabs}\left(e, T\right) \cdot M\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/PrimitiveRoot/CharacterExpansion.weighted_sieve_error_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* K. McGown, E. Treviño, T. Trudgian (2016). *Resolving Grosswald's conjecture on GRH*. DOI: [10.7169/facm/2016.55.2.5](https://doi.org/10.7169/facm/2016.55.2.5). URL: <https://doi.org/10.7169/facm/2016.55.2.5>.

*Commentary.*

Under the support and character bounds of the signed estimate, the elementary sieve weight differs from theta(e)delta(T) times the total unit weight by at most theta(e)K_abs(e,T)M. The weight is any real function and delta may have either sign.

**Theorem 1.9 (Character sums are supported on units).**

$$\forall p \in \mathbb{N},\; \left(\neg p = 0\right) \Rightarrow \left(\forall W \in \operatorname{ZMod}\left(p\right) \to \mathbb{C},\; \forall chi \in \operatorname{DirichletCharacter}\left(\mathbb{C}, p\right),\; \sum_{a \in \operatorname{Residues}\left(p\right)} {\operatorname{W}\left(a\right) \cdot \operatorname{chi}\left(a\right)} = \sum_{a \in \operatorname{Units}\left(p\right)} {\operatorname{W}\left(a\right) \cdot \operatorname{chi}\left(a\right)}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/PrimitiveRoot/CharacterExpansion.sum_units_character` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. D. Cohen, T. Oliveira e Silva, T. S. Trudgian (2015). *On Grosswald's conjecture on primitive roots*. DOI: [10.4064/aa8109-12-2015](https://doi.org/10.4064/aa8109-12-2015). URL: <https://doi.org/10.4064/aa8109-12-2015>.

*Commentary.*

For any nonzero modulus p, every Dirichlet character is zero on nonunits. Restriction to the unit group therefore preserves a character sum with an arbitrary complex weight. In particular, the principal character contributes the total unit weight, rather than the total weight over all residue classes.

**Theorem 1.10 (An inhabited controlled character family forces a nonnegative bound).**

$$\forall p \in \mathbb{N},\; \operatorname{Prime}\left(p\right) \Rightarrow \left(\forall W \in \operatorname{ZMod}\left(p\right) \to \mathbb{C},\; \forall M \in \mathbb{R},\; \forall t \in \mathbb{N},\; \left(\forall chi \in \operatorname{DirichletCharacter}\left(\mathbb{C}, p\right),\; \operatorname{orderOf}\left(chi\right) = \operatorname{gcd}\left(t, p - 1\right) \Rightarrow \operatorname{abs}\left(\operatorname{re}\left(\sum_{a \in \operatorname{Residues}\left(p\right)} {\operatorname{W}\left(a\right) \cdot \operatorname{chi}\left(a\right)}\right)\right) \le M\right) \Rightarrow 0 \le M\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/PrimitiveRoot/CharacterExpansion.bound_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* K. McGown, E. Treviño, T. Trudgian (2016). *Resolving Grosswald's conjecture on GRH*. DOI: [10.7169/facm/2016.55.2.5](https://doi.org/10.7169/facm/2016.55.2.5). URL: <https://doi.org/10.7169/facm/2016.55.2.5>.

*Commentary.*

Put d=gcd(t,p-1). Since p is prime, d is positive and divides p-1, so a character of order d exists, including the principal character when d=1. If the absolute real part of the W-weighted sum is at most M for every character of this exact order, choose one such character. Its absolute real sum is nonnegative, so M is nonnegative. No bounds for characters of other orders are required.

**Theorem 1.11 (A two-sided estimate for elementary sieve weight).**

$$\forall p \in \mathbb{N},\; \operatorname{Prime}\left(p\right) \Rightarrow \left(\forall W \in \operatorname{ZMod}\left(p\right) \to \mathbb{R},\; \forall e \in \mathbb{N},\; \left(\forall q \in \mathbb{N},\; q \in \operatorname{primeFactors}\left(e\right) \Rightarrow \operatorname{dvd}\left(q, p - 1\right)\right) \Rightarrow \left(\forall T \in \operatorname{Finset}\left(\mathbb{N}\right),\; \left(\forall t \in \mathbb{N},\; t \in T \Rightarrow \left(\operatorname{Prime}\left(t\right) \land \left(\operatorname{dvd}\left(t, p - 1\right) \land \left(\neg t \in \operatorname{primeFactors}\left(e\right)\right)\right)\right)\right) \Rightarrow \left(\forall M \in \mathbb{R},\; \left(\forall chi \in \operatorname{DirichletCharacter}\left(\mathbb{C}, p\right),\; \left(\neg chi = 1\right) \Rightarrow \left(\left(\operatorname{dvd}\left(\operatorname{orderOf}\left(chi\right), \prod_{q \in \operatorname{primeFactors}\left(e\right)} {q}\right) \lor \left(\exists t \in \mathbb{N},\; t \in T \land \operatorname{dvd}\left(\operatorname{orderOf}\left(chi\right), t \cdot \prod_{q \in \operatorname{primeFactors}\left(e\right)} {q}\right)\right)\right) \Rightarrow \operatorname{abs}\left(\operatorname{re}\left(\sum_{a \in \operatorname{Residues}\left(p\right)} {\operatorname{W}\left(a\right) \cdot \operatorname{chi}\left(a\right)}\right)\right) \le M\right)\right) \Rightarrow \left(\left(0 \le \operatorname{delta}\left(T\right) \lor \operatorname{primeFactors}\left(e\right) = \operatorname{empty}\left(\right)\right) \Rightarrow \operatorname{abs}\left(\sum_{a \in \operatorname{Units}\left(p\right)} {\operatorname{W}\left(a\right) \cdot \operatorname{if}\left(\forall q \in \mathbb{N},\; q \in \operatorname{primeFactors}\left(e\right) \Rightarrow \left(\neg a \in \operatorname{powerSubgroup}\left(\operatorname{Units}\left(p\right), q\right)\right), 1, 0\right) \cdot \left(1 - \operatorname{card}\left(\{t \in T \mid a \in \operatorname{powerSubgroup}\left(\operatorname{Units}\left(p\right), t\right)\}\right)\right)} - \operatorname{theta}\left(e\right) \cdot \operatorname{delta}\left(T\right) \cdot \sum_{a \in \operatorname{Units}\left(p\right)} {\operatorname{W}\left(a\right)}\right) \le \operatorname{theta}\left(e\right) \cdot \operatorname{K}\left(e, T\right) \cdot M\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/PrimitiveRoot/CharacterExpansion.weighted_sieve_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* K. McGown, E. Treviño, T. Trudgian (2016). *Resolving Grosswald's conjecture on GRH*. DOI: [10.7169/facm/2016.55.2.5](https://doi.org/10.7169/facm/2016.55.2.5). URL: <https://doi.org/10.7169/facm/2016.55.2.5>.

*Commentary.*

Let p be prime. Every prime divisor of e divides p-1. Every member t of T is prime, divides p-1 and is absent from the prime support of e. Write R for the radical of e. For each nonprincipal character of order dividing R or tR with t in T, assume the absolute real part of its W-weighted sum is at most M. If delta(T)>=0 or e has no prime factors, the elementary sieve weight differs from the theta-delta main term by at most theta(e)K(e,T)M in either direction. This expansion does not need a cover condition or any sign condition on W.

For a prime q dividing p-1, the characters trivial on the q-th power subgroup form a group of cardinality q. Orthogonality makes their sum q on that subgroup and zero elsewhere. Removing the principal character gives the local q-free expansion. Multiplying local factors gives the e-free indicator with principal coefficient theta(e). The remaining normalized coefficient mass is 2^omega(e)-1. Distinct prime orders are coprime, so every error character is nonprincipal; its order divides R.

The exclusion terms for t in T use characters of order dividing tR. Because t is absent from the prime support of e, their products are nonprincipal. Their normalized mass is (1-1/t)2^omega(e). Together with the delta(T) multiple of the e-free error, these masses sum to K(e,T). Every coefficient is real, so the estimate needs only real parts. The coefficient agreement criterion converts the absolute coefficient to K; the e-free error vanishes when e has no prime factors.

## References

- Truth anchor: `D5/S3/Arith/PrimitiveRoot/CharacterExpansion.bound_nonneg`
- Truth anchor: `D5/S3/Arith/PrimitiveRoot/CharacterExpansion.delta`
- Truth anchor: `D5/S3/Arith/PrimitiveRoot/CharacterExpansion.errorCoefficient`
- Truth anchor: `D5/S3/Arith/PrimitiveRoot/CharacterExpansion.errorCoefficientAbs`
- Truth anchor: `D5/S3/Arith/PrimitiveRoot/CharacterExpansion.errorCoefficientAbs_eq`
- Truth anchor: `D5/S3/Arith/PrimitiveRoot/CharacterExpansion.errorCoefficient_nonneg`
- Truth anchor: `D5/S3/Arith/PrimitiveRoot/CharacterExpansion.sum_units_character`
- Truth anchor: `D5/S3/Arith/PrimitiveRoot/CharacterExpansion.theta`
- Truth anchor: `D5/S3/Arith/PrimitiveRoot/CharacterExpansion.theta_pos`
- Truth anchor: `D5/S3/Arith/PrimitiveRoot/CharacterExpansion.weighted_sieve_error_bound`
- Truth anchor: `D5/S3/Arith/PrimitiveRoot/CharacterExpansion.weighted_sieve_lower_bound`
- Dependency: [D5/S3/Factorization/Galois/GeneralPowerCharacterLayer](../../Factorization/Galois/GeneralPowerCharacterLayer.md)
