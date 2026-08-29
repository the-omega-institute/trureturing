# Prime Word Occupation Descent

## Abstract

Prime-word history is not recoverable, and word actions descend exactly when commuting.

**Theorem 1.1 (No prime-history reconstruction).**

$$\neg \exists s: \operatorname{Multiset}(\operatorname{Primes}(\mathbb{N})) \to \operatorname{List}(\operatorname{Primes}(\mathbb{N})), \forall w: \operatorname{List}(\operatorname{Primes}(\mathbb{N})), s(\operatorname{occupation}(w)) = w.$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Combinatorics/PrimeWordOccupationDescent.no_prime_history_reconstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Ordered prime histories are lists of Mathlib prime subtypes, while the occupation state is their canonical multiset quotient. The words [2,3] and [3,2] have the same occupation state but are distinct, so no section can recover every original word.

**Theorem 1.2 (Order descent criterion).**

$$\begin{gathered}\forall P, X: Type,\\{}\forall U: P \to \left(X \to X\right),\\{}(\exists V: \operatorname{Multiset}(P) \to \left(X \to X\right), \forall w: \operatorname{List}(P), V(\operatorname{occupation}(w)) = \operatorname{runWord}(U, w)) \iff (\forall p, q: P, \operatorname{Commute}(U(p), U(q))).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Combinatorics/PrimeWordOccupationDescent.order_descent_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary input and state types, U assigns a state update to each input. The public witness is a dynamics on input multisets whose value on every list occupation is the imported left-to-right runWord action.

Pairwise commutativity makes runWord invariant under list permutation and therefore defines the quotient dynamics. Conversely, applying any descended dynamics to the equal occupations of [p,q] and [q,p] forces the two updates to commute.

## References

- Truth anchor: `D5/S3/Factorization/Combinatorics/PrimeWordOccupationDescent.no_prime_history_reconstruction`
- Truth anchor: `D5/S3/Factorization/Combinatorics/PrimeWordOccupationDescent.order_descent_criterion`
- Dependency: [D5/S3/Factorization/FreeCommMonoid](../FreeCommMonoid.md)
- Dependency: [D5/S3/ObserverMemory/Prediction/ControlledBehaviorUniversality](../../ObserverMemory/Prediction/ControlledBehaviorUniversality.md)
