# Kotěšovec's first monomial-sum conjecture

## Abstract

Every positive modulus with nonzero complete monomial sums at every degree at least two is powerful.

**Definition 1.1 (Complete monomial sum).**

$$\forall m: \mathbb{N}, \forall s: \mathbb{N}, \operatorname{monomialSum}\left(m, s\right) = \sum_{k \in \operatorname{Finset}.\operatorname{range}\left(m\right)} \operatorname{Complex}.\operatorname{exp}\left(\frac{2 \cdot \operatorname{Real}.\operatorname{pi} \cdot \operatorname{Complex}.\operatorname{I} \cdot ((k^{s}: \mathbb{N}): \mathbb{C})}{(m: \mathbb{C})}\right)$$

*Formalization.* `D5/S3/Arith/CharacterSums/KotesovecConjectureOne.monomialSum` (`✓ std3`).

*Citation.* Václav Kotěšovec (2024). *OEIS A368959: nonzero complete monomial exponential sums*. URL: <https://oeis.org/A368959>.

*Commentary.*

OEIS A368959, NAME: "Numbers m such that Sum_{k=0..m-1} exp(2*Pi*i*k^s/m) <> 0 for all s>=2." The exponent k^s is computed in the natural numbers before its cast to the complex numbers; the range contains exactly m terms.

**Definition 1.2 (Membership in A368959).**

$$\forall m: \mathbb{N}, \operatorname{InA368959}\left(m\right) = ((0 < m) \land (\forall s: \mathbb{N}, (2 \le s) \Rightarrow (\operatorname{monomialSum}\left(m, s\right) \neq 0)))$$

*Formalization.* `D5/S3/Arith/CharacterSums/KotesovecConjectureOne.InA368959` (`✓ std3`).

*Citation.* Václav Kotěšovec (2024). *OEIS A368959: nonzero complete monomial exponential sums*. URL: <https://oeis.org/A368959>.

*Commentary.*

OEIS A368959, NAME: "Numbers m such that Sum_{k=0..m-1} exp(2*Pi*i*k^s/m) <> 0 for all s>=2." The positive-integer domain follows the entry's offset. Both m and s range over the natural numbers.

**Definition 1.3 (Biquadratefree powerful numbers).**

$$\forall m: \mathbb{N}, \operatorname{InA338325}\left(m\right) = ((0 < m) \land (\forall p: \mathbb{N}, (p \in \operatorname{Nat}.\operatorname{primeFactors}\left(m\right)) \Rightarrow ((\operatorname{Nat}.\operatorname{factorization}\left(m, p\right) = 2) \lor (\operatorname{Nat}.\operatorname{factorization}\left(m, p\right) = 3))))$$

*Formalization.* `D5/S3/Arith/CharacterSums/KotesovecConjectureOne.InA338325` (`✓ std3`).

*Citation.* Václav Kotěšovec (2024). *OEIS A368959: nonzero complete monomial exponential sums*. URL: <https://oeis.org/A368959>.

*Commentary.*

OEIS A338325, NAME: "Biquadratefree powerful numbers: numbers whose exponents in their prime factorization are either 2 or 3." The exponent restriction applies to every prime factor of the positive integer m.

**Definition 1.4 (The first conjecture).**

$$claimOne = (\forall m: \mathbb{N}, (\operatorname{InA368959}\left(m\right)) \Rightarrow (\operatorname{Powerful}\left(m\right)))$$

*Formalization.* `D5/S3/Arith/CharacterSums/KotesovecConjectureOne.claimOne` (`✓ std3`).

*Citation.* Václav Kotěšovec (2024). *OEIS A368959: nonzero complete monomial exponential sums*. URL: <https://oeis.org/A368959>.

*Commentary.*

OEIS A368959, COMMENTS: "Conjecture 1: This is a subset of A001694." A001694 denotes the powerful numbers. Powerful is the existing predicate from PowerfulNumber: a nonzero natural number whose every prime divisor has its square dividing the number.

**Definition 1.5 (Additive-character monomial sum).**

$$\forall R: Type, [\operatorname{CommRing}\left(R\right)], [\operatorname{Fintype}\left(R\right)], \forall psi: \operatorname{AddChar}\left(R, \mathbb{C}\right), \forall s: \mathbb{N}, \operatorname{powerSum}\left(psi, s\right) = \sum_{x: R} psi\left(x^{s}\right)$$

*Formalization.* `D5/S3/Arith/CharacterSums/KotesovecConjectureOne.powerSum` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Václav Kotěšovec (2024). *OEIS A368959: nonzero complete monomial exponential sums*. URL: <https://oeis.org/A368959>.

*Commentary.*

The sum over a finite commutative ring evaluates an additive character on the s-th power of each ring element. The standard additive character of ZMod m recovers monomialSum.

**Definition 1.6 (Nonvanishing for every injective character).**

$$\forall n: \mathbb{N}, [\operatorname{NeZero}\left(n\right)], \operatorname{Good}\left(n\right) = (\forall psi: \operatorname{AddChar}\left(\operatorname{ZMod}\left(n\right), \mathbb{C}\right), (\operatorname{Function}.\operatorname{Injective}\left(psi\right)) \Rightarrow (\forall s: \mathbb{N}, (2 \le s) \Rightarrow (\operatorname{powerSum}\left(psi, s\right) \neq 0)))$$

*Formalization.* `D5/S3/Arith/CharacterSums/KotesovecConjectureOne.Good` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Václav Kotěšovec (2024). *OEIS A368959: nonzero complete monomial exponential sums*. URL: <https://oeis.org/A368959>.

*Commentary.*

Good n means that every injective complex additive character of ZMod n has nonzero power sums in every natural degree s at least two.

**Theorem 1.7 (Prime squares).**

$$\forall p: \mathbb{N}, (\operatorname{Nat}.\operatorname{Prime}\left(p\right)) \Rightarrow ([\operatorname{NeZero}\left(p^{2}\right)], \operatorname{Good}\left(p^{2}\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/KotesovecConjectureOne.good_prime_square` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Václav Kotěšovec (2024). *OEIS A368959: nonzero complete monomial exponential sums*. URL: <https://oeis.org/A368959>.

*Commentary.*

For every prime p, every injective character modulo p squared has nonzero monomial sums at all degrees at least two. At these degrees p has no power-map preimage, whereas zero has a preimage.

**Theorem 1.8 (Prime cubes).**

$$\forall p: \mathbb{N}, (\operatorname{Nat}.\operatorname{Prime}\left(p\right)) \Rightarrow ([\operatorname{NeZero}\left(p^{3}\right)], \operatorname{Good}\left(p^{3}\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/KotesovecConjectureOne.good_prime_cube` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Václav Kotěšovec (2024). *OEIS A368959: nonzero complete monomial exponential sums*. URL: <https://oeis.org/A368959>.

*Commentary.*

For degrees at least three the missing-preimage argument applies. Odd quadratic sums have nonzero squared norm. Modulo eight at degree two, the fibers over one and five have sizes four and zero.

**Theorem 1.9 (Coprime products).**

$$\forall r: \mathbb{N}, \forall t: \mathbb{N}, [\operatorname{NeZero}\left(r\right)], [\operatorname{NeZero}\left(t\right)], (\operatorname{Nat}.\operatorname{Coprime}\left(r, t\right)) \Rightarrow ((\operatorname{Good}\left(r\right)) \Rightarrow ((\operatorname{Good}\left(t\right)) \Rightarrow (\operatorname{Good}\left(r \cdot t\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/KotesovecConjectureOne.good_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Václav Kotěšovec (2024). *OEIS A368959: nonzero complete monomial exponential sums*. URL: <https://oeis.org/A368959>.

*Commentary.*

Chinese remaindering factors each power sum into two character sums. The restrictions of an injective character remain injective, so nonvanishing passes to coprime products. This supplies the products in the second conjecture.

**Theorem 1.10 (The standard additive character).**

$$\forall n: \mathbb{N}, [\operatorname{NeZero}\left(n\right)], (\operatorname{Good}\left(n\right)) \Rightarrow (\operatorname{InA368959}\left(n\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/KotesovecConjectureOne.good_to_membership` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Václav Kotěšovec (2024). *OEIS A368959: nonzero complete monomial exponential sums*. URL: <https://oeis.org/A368959>.

*Commentary.*

Specializing the injective character to ZMod.stdAddChar converts Good n to membership in A368959. This converts the family and the four extra moduli in the second conjecture.

**Theorem 1.11 (The biquadratefree powerful family).**

$$\forall m: \mathbb{N}, (\operatorname{InA338325}\left(m\right)) \Rightarrow (\operatorname{InA368959}\left(m\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/KotesovecConjectureOne.family_inclusion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Václav Kotěšovec (2024). *OEIS A368959: nonzero complete monomial exponential sums*. URL: <https://oeis.org/A368959>.

*Commentary.*

Every positive integer with prime-factorization exponents two or three is a product of coprime prime squares and cubes. Nonvanishing for these factors proves membership in A368959.

**Theorem 1.12 (The modulus 243).**

$$\operatorname{Good}\left(243\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/KotesovecConjectureOne.good_243` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Václav Kotěšovec (2024). *OEIS A368959: nonzero complete monomial exponential sums*. URL: <https://oeis.org/A368959>.

*Commentary.*

For degree three the fibers over zero and eighty-one have sizes twenty-seven and zero; for degree four they have sizes twenty-seven and fifty-four. Quadratic nonvanishing handles degree two and the missing-preimage argument handles all degrees at least five.

**Theorem 1.13 (The modulus 2401).**

$$\operatorname{Good}\left(2401\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/KotesovecConjectureOne.good_2401` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Václav Kotěšovec (2024). *OEIS A368959: nonzero complete monomial exponential sums*. URL: <https://oeis.org/A368959>.

*Commentary.*

For degree three the fibers over zero and three hundred forty-three have sizes forty-nine and one hundred forty-seven. Quadratic nonvanishing handles degree two and the missing-preimage argument handles all degrees at least four.

**Theorem 1.14 (Every A368959 term is powerful).**

$$\forall m: \mathbb{N}, (\operatorname{InA368959}\left(m\right)) \Rightarrow (\operatorname{Powerful}\left(m\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/KotesovecConjectureOne.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Václav Kotěšovec (2024). *OEIS A368959: nonzero complete monomial exponential sums*. URL: <https://oeis.org/A368959>.

*Commentary.*

If a prime p divides m only once, Chinese remaindering isolates a prime-modulus factor. At degree p, Fermat's identity turns this factor into the sum of a nontrivial additive character, which is zero. Thus every prime divisor of a modulus in A368959 occurs at least twice.

## References

- Truth anchor: `D5/S3/Arith/CharacterSums/KotesovecConjectureOne.Good`
- Truth anchor: `D5/S3/Arith/CharacterSums/KotesovecConjectureOne.InA338325`
- Truth anchor: `D5/S3/Arith/CharacterSums/KotesovecConjectureOne.InA368959`
- Truth anchor: `D5/S3/Arith/CharacterSums/KotesovecConjectureOne.claimOne`
- Truth anchor: `D5/S3/Arith/CharacterSums/KotesovecConjectureOne.family_inclusion`
- Truth anchor: `D5/S3/Arith/CharacterSums/KotesovecConjectureOne.good_2401`
- Truth anchor: `D5/S3/Arith/CharacterSums/KotesovecConjectureOne.good_243`
- Truth anchor: `D5/S3/Arith/CharacterSums/KotesovecConjectureOne.good_mul`
- Truth anchor: `D5/S3/Arith/CharacterSums/KotesovecConjectureOne.good_prime_cube`
- Truth anchor: `D5/S3/Arith/CharacterSums/KotesovecConjectureOne.good_prime_square`
- Truth anchor: `D5/S3/Arith/CharacterSums/KotesovecConjectureOne.good_to_membership`
- Truth anchor: `D5/S3/Arith/CharacterSums/KotesovecConjectureOne.monomialSum`
- Truth anchor: `D5/S3/Arith/CharacterSums/KotesovecConjectureOne.powerSum`
- Truth anchor: `D5/S3/Arith/CharacterSums/KotesovecConjectureOne.result`
- Dependency: [D5/S3/Arith/Powerful/PowerfulNumber](../Powerful/PowerfulNumber.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/CountedOriginalOrbitGyration](../../ConceptDynamics/Coding/CountedOriginalOrbitGyration.md)
