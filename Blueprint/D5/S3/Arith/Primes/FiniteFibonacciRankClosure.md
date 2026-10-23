# Finite Fibonacci rank closure

## Abstract

The prime support of Fibonacci entry ranks has a bounded least closure over every finite set of primes greater than five.

For a prime p, its Fibonacci entry rank is the least positive index r for which p divides F_r. The first-entry divisibility theorem and the golden Frobenius zero supply this rank. The construction below follows prime factors of these actual ranks.

**Definition 1.1 (Least positive zero witness).**

Lean statement: `D5/S3/Arith/Primes/FiniteFibonacciRankClosure.rankWitness`

*Formalization.* `D5/S3/Arith/Primes/FiniteFibonacciRankClosure.rankWitness` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each prime p, this witness gives a positive index r with p dividing F_r, together with a proof that every other positive zero index is at least r.

**Definition 1.2 (The original entry rank).**

Lean statement: `D5/S3/Arith/Primes/FiniteFibonacciRankClosure.fibonacciRank`

*Formalization.* `D5/S3/Arith/Primes/FiniteFibonacciRankClosure.fibonacciRank` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At a prime p, this value is the least positive r with p dividing F_r. Its value at a nonprime input is one, so it contributes no prime factors to the closure operation.

**Definition 1.3 (Initial prime set).**

Lean statement: `D5/S3/Arith/Primes/FiniteFibonacciRankClosure.rankClosureSeed`

*Formalization.* `D5/S3/Arith/Primes/FiniteFibonacciRankClosure.rankClosureSeed` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The initial set consists of the prescribed finite set together with the primes two, three and five.

**Definition 1.4 (Prime-support expansion).**

Lean statement: `D5/S3/Arith/Primes/FiniteFibonacciRankClosure.rankClosureStep`

*Formalization.* `D5/S3/Arith/Primes/FiniteFibonacciRankClosure.rankClosureStep` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

One step retains each current prime and adjoins every prime divisor of its Fibonacci entry rank.

**Definition 1.5 (Iterated closure).**

Lean statement: `D5/S3/Arith/Primes/FiniteFibonacciRankClosure.fibonacciRankClosure`

*Formalization.* `D5/S3/Arith/Primes/FiniteFibonacciRankClosure.fibonacciRankClosure` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Let B be the larger of five and the largest member of the prescribed set. Starting from the initial set, apply the expansion once per prime at most B. This gives a finite, explicitly determined set.

**Theorem 1.6 (Bounded least closure).**

Lean statement: `D5/S3/Arith/Primes/FiniteFibonacciRankClosure.finite_fibonacci_rank_closure`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/FiniteFibonacciRankClosure.finite_fibonacci_rank_closure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite set S of primes greater than five, the iterated closure contains S and the three small primes, contains only primes at most B, and is unchanged by one further expansion. It is contained in every expansion-closed finite set that contains the same initial primes. Indeed, a prime divisor of the rank of p is smaller than p when p exceeds five; the ranks at two, three and five contribute only primes at most five. The expanding sets therefore stay inside the finite universe of primes at most B. Equal cardinalities on successive steps give a fixed point, and induction gives its leastness.

Application to exact finite divisibility patterns. Let S be any finite set of distinct positive primes, and let K be a nonnegative integer. For a prime index r, put L_r=ceil(F_r/10), U_r=floor(F_r/5), and N(r,g)=1+F_r*g for integer g between these endpoints. There is one integer threshold R, depending only on S and K, such that every prime r at least R and every Boolean assignment b on S admit such a g with p dividing N(r,g) exactly when b(p) is true, and with at least K distinct prime divisors of that same N(r,g) outside S. This includes empty S and assignments having any number of zero coordinates. The assertion for K at least one follows in particular.

Choose a K-element prime set T disjoint from S. Infinitude of primes and the finite-subset theorem provide T; its being the first K available primes is unnecessary. Set A=S union T, Q equal to the product of the primes in A, and z(q) equal to the positive least zero index supplied by rankWitness. Take R to be the larger of one plus the maximum of z on A and 10*(Q+1)+5, with maximum zero on an empty set. Both T and R are chosen before b. For prime r at least R, fibonacci_entry_point turns q dividing F_r into z(q) dividing r. The rank is positive and cannot be one because F_1=1. Since z(q) is smaller than r, primality of r excludes this divisibility. Thus F_r is coprime to each q in A.

For q in T or a true coordinate of S, prescribe the negative inverse of F_r modulo q; for a false coordinate, prescribe zero. Distinct prime moduli are coprime, so Nat.chineseRemainderOfFinset gives one residue a satisfying all prescriptions simultaneously. The inverse identity is ZMod.coe_mul_inv_eq_one. A true coordinate or a member of T therefore divides 1+F_r*g whenever g has this residue, while a false coordinate gives residue one for that integer and therefore does not divide it.

Nat.le_fib_self gives F_r at least 10*(Q+1) at every index under consideration. The ceiling bound L_r < F_r/10+1 and the floor bound U_r > F_r/5-1 imply the integer inequality L_r+Q <= U_r. Use the integer representative g=L_r+((a-L_r) mod Q), with the Euclidean remainder in the range from zero through Q-1. It satisfies L_r <= g < L_r+Q <= U_r and is congruent to a modulo every q in A. This retains the actual integer pair (r,g), rather than replacing the window by an abstract residue carrier. The endpoints are the integer ceiling and floor of the exact rational quotients; the natural prime index is cast to its positive integer label.

The resulting N(r,g) is positive. Its natural-number cast has exactly the same integer value, so membership in its primeFactors finset is equivalent to prime divisibility. Every member of T lies in that finset with S removed. Cardinality monotonicity gives at least K external divisors. This set-difference cardinality is the residual support rho_S: the total number of distinct prime divisors minus those detected in S. All observed and unobserved conditions concern the same integer.

This is an application of the supplied Fibonacci rank, CRT, inverse, prime infinitude and integer-remainder facts, with no claim of a new entry-rank or CRT theorem or of literature priority. It gives existence in every sufficiently large prime-index window, not a uniform algorithmic resource bound. Small windows may be empty or force a bit to zero when its prime divides F_r. No fixed window has unbounded support, and the external support need not have exactly K elements. Transferring complete randomized query tables, one common seed, stopping and closed-cap cost semantics to the full numerical source carrier requires further correspondence results.

## References

- Truth anchor: `D5/S3/Arith/Primes/FiniteFibonacciRankClosure.fibonacciRank`
- Truth anchor: `D5/S3/Arith/Primes/FiniteFibonacciRankClosure.fibonacciRankClosure`
- Truth anchor: `D5/S3/Arith/Primes/FiniteFibonacciRankClosure.finite_fibonacci_rank_closure`
- Truth anchor: `D5/S3/Arith/Primes/FiniteFibonacciRankClosure.rankClosureSeed`
- Truth anchor: `D5/S3/Arith/Primes/FiniteFibonacciRankClosure.rankClosureStep`
- Truth anchor: `D5/S3/Arith/Primes/FiniteFibonacciRankClosure.rankWitness`
