# Galois Prime Observers

## Abstract

A tagged Frobenius observer has an infinite unramified fiber.

**Theorem 1.1 (A finite Frobenius output merges infinitely many unramified primes).**

$$\forall G, \operatorname{Finite}(\operatorname{ConjClasses}(G)) \Rightarrow\\{}\forall O: Primes \to \operatorname{Option}(\operatorname{ConjClasses}(G)), \operatorname{Finite}(\operatorname{RamifiedPrimes}(O)) \Rightarrow\\{}\exists c\in \operatorname{ConjClasses}(G), \operatorname{Infinite}(\{p \in Primes \mid O(p) = \operatorname{some}(c)\}).$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Galois/GaloisPrimeObserver.frobenius_observation_has_infinite_fiber` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The named galoisPrimeObserver returns none on the ramified branch and some conjugacy class on the unramified branch. This tag prevents a total Frobenius value from being asserted at every prime.

The named mathlibFrobeniusAt is the local bridge. On an unramified ideal it returns the class of Mathlib's arithFrobAt; on a ramified ideal it returns none. No parallel Frobenius theory is introduced.

The strong infinite pigeonhole theorem first supplies an infinite fiber of the tagged observer. Finiteness of the ramified set rules out none, leaving an infinite fiber labeled by some Frobenius conjugacy class.

The proof uses only a monoid with finitely many conjugacy classes. It does not assume fields, a number field, or a finite group; those structures belong only to the Mathlib bridge.

**Lemma 1.2 (All-ramified tagging refutes the unramified-fiber conclusion).**

$$\operatorname{Infinite}(RamifiedPrimes) \land \neg\exists c\in \operatorname{ConjClasses}(Unit), \operatorname{Infinite}(\{p \in Primes \mid R(p) = \operatorname{some}(c)\}).$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Galois/GaloisPrimeObserver.finite_ramification_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take the trivial group and tag every rational prime as ramified. The ramified set is infinite, the observer is constantly none, and every some-class fiber is empty. This is the concrete counterexample for omitting finite ramification.

**Lemma 1.3 (An infinite conjugacy-class output can preserve prime identity).**

$$\operatorname{Infinite}(\operatorname{ConjClasses}(\operatorname{Multiplicative}(\mathbb{N}))) \land \neg\exists c\in \operatorname{ConjClasses}(\operatorname{Multiplicative}(\mathbb{N})), \operatorname{Infinite}(\{p \in Primes \mid J(p) = \operatorname{some}(c)\}).$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Galois/GaloisPrimeObserver.finite_conjugacy_output_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use the commutative monoid Multiplicative Nat, whose conjugacy-class quotient is infinite, and send each rational prime to the class of its underlying natural number. Commutativity makes the class map injective, so every fiber is finite.

The degenerate audit also covers the opposite endpoint: for the trivial group, the unramified observer is constant and its sole class has all rational primes as an infinite fiber. A monoid's conjugacy-class output cannot be empty because it contains the class of one.

## References

- Truth anchor: `D5/S3/Factorization/Galois/GaloisPrimeObserver.finite_conjugacy_output_is_necessary`
- Truth anchor: `D5/S3/Factorization/Galois/GaloisPrimeObserver.finite_ramification_is_necessary`
- Truth anchor: `D5/S3/Factorization/Galois/GaloisPrimeObserver.frobenius_observation_has_infinite_fiber`
