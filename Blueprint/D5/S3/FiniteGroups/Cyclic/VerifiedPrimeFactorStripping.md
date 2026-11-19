# Verified prime-factor stripping

## Abstract

Repeated division by supplied factors computes the order from any positive returning exponent whose prime support is included in the supplied list.

Let G be an arbitrary monoid with decidable equality, x an element, m a natural exponent, and P a finite list of natural numbers. The executable function stripFactor x p m checks 1<p, 0<m, p dividing m, and x^(m/p)=1. When every check passes it recursively replaces m by m/p; otherwise it returns m. Natural division strictly decreases the positive recursive argument. The function stripFactors x P m folds this operation from left to right through P, starting at m. Neither function receives the true order, a minimality certificate, nor an assumed terminal invariant.

**Theorem 1.1 (Correctness under original prime-support coverage).**

$$\forall G \in \mathit{Typeu},\; [\operatorname{Monoid}\left(G\right)] [\operatorname{DecidableEq}\left(G\right)] \forall x \in G,\; \forall P \in \operatorname{List}\left(\mathit{Nat}\right),\; \forall m \in \mathit{Nat},\; 0 < m \Rightarrow \left(x^{m} = 1 \Rightarrow \left(\left(\forall p \in \mathit{Nat},\; \operatorname{Prime}\left(p\right) \Rightarrow \left(\operatorname{Dvd}\left(p, m\right) \Rightarrow \operatorname{Mem}\left(p, P\right)\right)\right) \Rightarrow \left(0 < \operatorname{stripFactors}\left(x, P, m\right) \land \left(\operatorname{Dvd}\left(\operatorname{stripFactors}\left(x, P, m\right), m\right) \land \left(x^{\operatorname{stripFactors}\left(x, P, m\right)} = 1 \land \operatorname{stripFactors}\left(x, P, m\right) = \operatorname{orderOf}\left(x\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/Cyclic/VerifiedPrimeFactorStripping.stripFactors_correct` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In the display Prime is natural primality, Dvd is natural divisibility, and Mem is list membership. Assume m>0 and x^m=1. Coverage means that every prime divisor p of the ORIGINAL input m is itself a member of P. The output M is positive, divides m, returns x to one, and equals orderOf x. The universe of G is arbitrary. No group, finiteness, cancellation or commutativity hypothesis is required. Duplicates and extra composite numbers, zero and one are allowed in P. Coverage is a proof hypothesis, not an executable input to either function.

Strong induction on the current exponent proves the actual single-factor run invariant. Its output M is positive, still returns to one, and satisfies m=p^k*M for a natural k. If p>1, then p does not divide M/orderOf x. In a recursive branch the induction hypothesis at m/p combines with m=p*(m/p), increasing k by one. At a terminal branch, if M/orderOf x=p*k, order divisibility gives M=p*(orderOf x*k); division by p would still return to one, contradicting the stopping guard. This proves the invariant across every state-changing recursive call.

Induction over the list proves a second invariant: the output is a positive returning divisor of the initial exponent and its quotient by the order is divisible by none of the processed factors greater than one. If N is the output after later factors and M is an earlier returning state, N divides M and the order divides both. The pinned Nat.div_dvd_div_iff_right therefore gives N/orderOf x dividing M/orderOf x. Every previously excluded factor remains excluded. This handles repetitions and arbitrary extra list entries without a primality hypothesis on those entries.

Every prime divisor of the final output divides the original input, so coverage puts it in P. If division of the final exponent by such a prime still returned to one, order divisibility and Nat.dvd_div_iff_mul_dvd would make that prime divide the output quotient by the order, contradicting the fold invariant. The proof then directly applies Mathlib's orderOf_eq_of_pow_and_pow_div_prime. The new proof content is the recursion and processed-list invariant; the terminal group fact and quotient-divisibility fact retain their upstream ownership.

The repeated-division algorithm is classical: Andrew V. Sutherland, MIT 18.783, Spring 2015, Lecture 8, Section 8.3, Algorithm 8.2, printed page 3, https://math.mit.edu/classes/18.783/2015/LectureNotes8.pdf. That source starts from a returning multiple in an additive group and its prime factorization, then removes each prime while the reduced multiple still returns to zero. Here multiplication and one replace addition and zero. The repo-derived specification extends the input contract to arbitrary decidable monoids, an original-prime-support list with repetitions and arbitrary extra natural entries, and total zero-input behavior. The classical algorithm is literature-attested; no algorithmic novelty is asserted. No source code is transcribed from the lecture notes.

For x=2 in the multiplicative monoid ZMod 21, input 12 with P=[2,3] returns 6; input 132 with P=[2,3,11] also returns 6. The identity with input 12 and P=[2,3] returns 1. With only P=[6], the same identity input returns 2, even though both original prime divisors divide a listed composite. Thus divisibility by some list member cannot replace actual prime membership. With P=[2] it returns 3. Input 1 with an empty list returns 1. Factors zero and one are inert, and the exponent zero returns zero for every list. Zero is deliberately excluded from correctness because x^0=1 holds even when the element has infinite order.

The inputs include a positive returning multiple and a list covering its prime support. Their acquisition and verification costs are outside this theorem. It gives no bit or gate complexity, probabilistic success estimate, quantum sampling law, physical implementation or complete integer-factorization procedure. The operations and equality of a concrete monoid must be executable for evaluation.

## References

- Truth anchor: `D5/S3/FiniteGroups/Cyclic/VerifiedPrimeFactorStripping.stripFactors_correct`
