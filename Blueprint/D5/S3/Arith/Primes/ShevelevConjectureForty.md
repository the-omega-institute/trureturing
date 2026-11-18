# Unbounded separation of Ramanujan and Labos primes

## Abstract

For every pair of natural bounds H and N, a positive n >= N satisfies L_n + H < R_n.

Journal Definition 1 defines R_n as the largest prime satisfying pi(R_n)-pi(R_n/2)=n and proves equivalence to the least positive integer g(n) such that every real x >= g(n) has pi(x)-pi(x/2) >= n. This encoding uses that threshold form, which is Definition 1 in the latest arXiv:0909.0715 version. The Labos minimum is journal Definition 3 and latest-arXiv Definition 2. Proposition 18 gives unbounded separation with R indexed by n plus one; the theorem here removes that shift. Conjecture 41, on infinitely many peculiar primes, is outside the conclusion.

**Definition 1.1 (The integer count).**

Lean statement: `D5/S3/Arith/Primes/ShevelevConjectureForty.count`

*Formalization.* `D5/S3/Arith/Primes/ShevelevConjectureForty.count` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a natural m, count m is pi(m) minus pi(m/2), where division by two is natural division. It counts primes strictly greater than m/2 and no greater than m.

**Theorem 1.2 (Subtraction does not truncate).**

Lean statement: `D5/S3/Arith/Primes/ShevelevConjectureForty.subtrahend_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/ShevelevConjectureForty.subtrahend_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Monotonicity of prime counting and m/2 at most m show that the second term never exceeds the first. Thus natural subtraction agrees with the ordinary nonnegative difference.

**Theorem 1.3 (The prime-counting step).**

Lean statement: `D5/S3/Arith/Primes/ShevelevConjectureForty.primeCounting_succ`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/ShevelevConjectureForty.primeCounting_succ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At the successor of m the prime count increases by one if that successor is prime, and otherwise remains unchanged. This is the existing counting recurrence for the prime predicate.

**Theorem 1.4 (Upward steps are at most one).**

Lean statement: `D5/S3/Arith/Primes/ShevelevConjectureForty.count_succ_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/ShevelevConjectureForty.count_succ_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The upper endpoint adds at most one prime, while the lower-endpoint count is nondecreasing. Their difference can therefore increase by at most one.

**Theorem 1.5 (Positive levels are attained).**

Lean statement: `D5/S3/Arith/Primes/ShevelevConjectureForty.exists_count_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/ShevelevConjectureForty.exists_count_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If 1 <= n and n <= count b, some positive m <= b has count m = n. Take the first m whose count is at least n. It is positive because the count at zero is zero. Its predecessor has count less than n, and the step bound forces equality at m.

**Theorem 1.6 (Constancy on a prime-free interval).**

Lean statement: `D5/S3/Arith/Primes/ShevelevConjectureForty.primeCounting_eq_of_no_prime`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/ShevelevConjectureForty.primeCounting_eq_of_no_prime` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If a <= b and every integer t with a < t <= b is not prime, pi(b)=pi(a). If the two counts differed, the existing counting theorem would give a prime in the intervening integer interval, contradicting the hypothesis.

**Theorem 1.7 (A prime contributes before its double).**

Lean statement: `D5/S3/Arith/Primes/ShevelevConjectureForty.count_before_double_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/ShevelevConjectureForty.count_before_double_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a prime p, the count at 2p-1 is positive. The lower endpoint is p-1, and the upper endpoint is at least p, so the prime p is included.

**Theorem 1.8 (The left side dominates).**

Lean statement: `D5/S3/Arith/Primes/ShevelevConjectureForty.count_window_left`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/ShevelevConjectureForty.count_window_left` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive H, if every integer in [2p-H,2p+H] is composite, the count at 2p-H is at least the count at 2p-1. The upper prime count is constant and the lower one is nondecreasing.

**Theorem 1.9 (Strict descent across twice a prime).**

Lean statement: `D5/S3/Arith/Primes/ShevelevConjectureForty.count_window_right`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/ShevelevConjectureForty.count_window_right` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural H, if p is prime and the window is prime-free, the count at 2p+H is strictly less than the count at 2p-1. The upper prime count remains constant, while the lower prime count has acquired p. The nontruncation inequality preserves this strict comparison.

**Theorem 1.10 (Dyadic counts eventually exceed every fixed bound).**

Lean statement: `D5/S3/Arith/Primes/ShevelevConjectureForty.eventually_count_ge`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/ShevelevConjectureForty.eventually_count_ge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reuse EulerLayerRootCorrection.prime_number_limits, proved from MediumPNT and the square-root bound on psi minus theta. Eventually 5x/6 <= theta(x) <= 7x/6, giving theta(2m)-theta(m) >= m/2. The finite prime sum over (m,2m] is at most (pi(2m)-pi(m))*log(2m). Since log(2m)/m tends to zero, every fixed k is eventually at most pi(2m)-pi(m). This is a consumed consequence of the frozen prime-number theorem, not an independent first-freeze basis.

**Definition 1.11 (The real dyadic count).**

Lean statement: `D5/S3/Arith/Primes/ShevelevConjectureForty.ramanujanCount`

*Formalization.* `D5/S3/Arith/Primes/ShevelevConjectureForty.ramanujanCount` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Vladimir Shevelev (2012). *Ramanujan and Labos Primes, Their Generalizations, and Classifications of Primes*. URL: <https://cs.uwaterloo.ca/journals/JIS/VOL15/Shevelev/shevelev19.html>.

*Commentary.*

For real x this is pi of the natural floor of x minus pi of the natural floor of x/2. For nonnegative x it counts primes in (x/2,x]. Negative x has count zero.

**Definition 1.12 (Ramanujan thresholds).**

Lean statement: `D5/S3/Arith/Primes/ShevelevConjectureForty.RamanujanSet`

*Formalization.* `D5/S3/Arith/Primes/ShevelevConjectureForty.RamanujanSet` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Vladimir Shevelev (2012). *Ramanujan and Labos Primes, Their Generalizations, and Classifications of Primes*. URL: <https://cs.uwaterloo.ca/journals/JIS/VOL15/Shevelev/shevelev19.html>.

*Commentary.*

For natural n the set consists of positive integers m such that every real x >= m has at least n primes in (x/2,x]. The real quantifier is unrestricted above m.

**Definition 1.13 (Labos occurrences).**

Lean statement: `D5/S3/Arith/Primes/ShevelevConjectureForty.LabosSet`

*Formalization.* `D5/S3/Arith/Primes/ShevelevConjectureForty.LabosSet` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Vladimir Shevelev (2012). *Ramanujan and Labos Primes, Their Generalizations, and Classifications of Primes*. URL: <https://cs.uwaterloo.ca/journals/JIS/VOL15/Shevelev/shevelev19.html>.

*Commentary.*

For natural n the set consists of positive integers m at which the real dyadic count equals n.

**Definition 1.14 (The Ramanujan minimum).**

Lean statement: `D5/S3/Arith/Primes/ShevelevConjectureForty.ramanujanPrime`

*Formalization.* `D5/S3/Arith/Primes/ShevelevConjectureForty.ramanujanPrime` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Vladimir Shevelev (2012). *Ramanujan and Labos Primes, Their Generalizations, and Classifications of Primes*. URL: <https://cs.uwaterloo.ca/journals/JIS/VOL15/Shevelev/shevelev19.html>.

*Commentary.*

R_n is the natural infimum of the Ramanujan threshold set. Nonemptiness below ensures that this infimum belongs to the set and is its least element.

**Definition 1.15 (The Labos minimum).**

Lean statement: `D5/S3/Arith/Primes/ShevelevConjectureForty.labosPrime`

*Formalization.* `D5/S3/Arith/Primes/ShevelevConjectureForty.labosPrime` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Vladimir Shevelev (2012). *Ramanujan and Labos Primes, Their Generalizations, and Classifications of Primes*. URL: <https://cs.uwaterloo.ca/journals/JIS/VOL15/Shevelev/shevelev19.html>.

*Commentary.*

L_n is the natural infimum of the Labos occurrence set. For every positive n that set is nonempty, so this is the least positive occurrence in journal Definition 3 (latest-arXiv Definition 2).

**Theorem 1.16 (No truncated subtraction).**

Lean statement: `D5/S3/Arith/Primes/ShevelevConjectureForty.primeCounting_half_floor_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/ShevelevConjectureForty.primeCounting_half_floor_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Vladimir Shevelev (2012). *Ramanujan and Labos Primes, Their Generalizations, and Classifications of Primes*. URL: <https://cs.uwaterloo.ca/journals/JIS/VOL15/Shevelev/shevelev19.html>.

*Commentary.*

For every real x the lower-endpoint prime count is no greater than the upper-endpoint count. Natural floor commutes with division by two, and natural division never increases its argument.

**Theorem 1.17 (Recovering the upper count).**

Lean statement: `D5/S3/Arith/Primes/ShevelevConjectureForty.ramanujanCount_add_half`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/ShevelevConjectureForty.ramanujanCount_add_half` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Vladimir Shevelev (2012). *Ramanujan and Labos Primes, Their Generalizations, and Classifications of Primes*. URL: <https://cs.uwaterloo.ca/journals/JIS/VOL15/Shevelev/shevelev19.html>.

*Commentary.*

Adding the lower prime count to the interval count gives the upper prime count exactly. This uses the nontruncation inequality.

**Theorem 1.18 (Reduction to integers).**

Lean statement: `D5/S3/Arith/Primes/ShevelevConjectureForty.ramanujanCount_eq_count_floor`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/ShevelevConjectureForty.ramanujanCount_eq_count_floor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Vladimir Shevelev (2012). *Ramanujan and Labos Primes, Their Generalizations, and Classifications of Primes*. URL: <https://cs.uwaterloo.ca/journals/JIS/VOL15/Shevelev/shevelev19.html>.

*Commentary.*

The count at real x equals the integer dyadic count at the natural floor of x, because taking the natural floor commutes with division by two.

**Theorem 1.19 (Integer inputs).**

Lean statement: `D5/S3/Arith/Primes/ShevelevConjectureForty.ramanujanCount_nat`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/ShevelevConjectureForty.ramanujanCount_nat` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Vladimir Shevelev (2012). *Ramanujan and Labos Primes, Their Generalizations, and Classifications of Primes*. URL: <https://cs.uwaterloo.ca/journals/JIS/VOL15/Shevelev/shevelev19.html>.

*Commentary.*

At a natural input the real count agrees exactly with the integer dyadic count.

**Theorem 1.20 (Ramanujan thresholds exist).**

Lean statement: `D5/S3/Arith/Primes/ShevelevConjectureForty.ramanujanSet_nonempty`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/ShevelevConjectureForty.ramanujanSet_nonempty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Vladimir Shevelev (2012). *Ramanujan and Labos Primes, Their Generalizations, and Classifications of Primes*. URL: <https://cs.uwaterloo.ca/journals/JIS/VOL15/Shevelev/shevelev19.html>.

*Commentary.*

For every natural n, including zero, the Ramanujan threshold set is nonempty. The number of primes in (m,2m] tends to infinity. If a real x is large, m=floor(x)/2 is large, 2m <= floor(x), and the dyadic count at x is at least pi(2m)-pi(m).

**Theorem 1.21 (Labos occurrences exist).**

Lean statement: `D5/S3/Arith/Primes/ShevelevConjectureForty.labosSet_nonempty`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/ShevelevConjectureForty.labosSet_nonempty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Vladimir Shevelev (2012). *Ramanujan and Labos Primes, Their Generalizations, and Classifications of Primes*. URL: <https://cs.uwaterloo.ca/journals/JIS/VOL15/Shevelev/shevelev19.html>.

*Commentary.*

For every n >= 1 the Labos occurrence set is nonempty. A Ramanujan threshold gives an integer with count at least n, and the integer level-crossing theorem gives a positive input with count exactly n.

**Theorem 1.22 (Arbitrarily large separation).**

Lean statement: `D5/S3/Arith/Primes/ShevelevConjectureForty.exists_separation`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/ShevelevConjectureForty.exists_separation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Vladimir Shevelev (2012). *Ramanujan and Labos Primes, Their Generalizations, and Classifications of Primes*. URL: <https://cs.uwaterloo.ca/journals/JIS/VOL15/Shevelev/shevelev19.html>.

*Commentary.*

Choose a composite window of radius H+1 around twice a prime p. Put n=count(2p-1), which is positive since p is counted. The count at the left endpoint is at least n, so an earlier positive input attains n and L_n lies no later than that endpoint. At the right endpoint the count is less than n, so every Ramanujan threshold is later than that endpoint. Consequently L_n+H<R_n.

**Theorem 1.23 (Conjecture 40).**

Lean statement: `D5/S3/Arith/Primes/ShevelevConjectureForty.result`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/ShevelevConjectureForty.result` (`✓ std3`). ∎

*Resolves.* `Problems/shevelev-2012-conjecture-40` (proved) by `D5/S3/Arith/Primes/ShevelevConjectureForty.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"shevelev-2012-conjecture-40","declaration_gid":"D5/S3/Arith/Primes/ShevelevConjectureForty.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Vladimir Shevelev (2012). *Ramanujan and Labos Primes, Their Generalizations, and Classifications of Primes*. URL: <https://cs.uwaterloo.ca/journals/JIS/VOL15/Shevelev/shevelev19.html>.

*Commentary.*

For all natural H and N there exists a natural n >= N with 1 <= n and L_n+H<R_n. Apply the separation theorem with a bound at least H and at least each of the finitely many R_j for j<N. The resulting index cannot be below N, since then its R_n would be no larger than that bound, contradicting the strict separation. This proves the stated infinite limsup, rather than only unboundedness at an unspecified finite set of indices. No assertion about Conjecture 41 follows.

## References

- Truth anchor: `D5/S3/Arith/Primes/ShevelevConjectureForty.LabosSet`
- Truth anchor: `D5/S3/Arith/Primes/ShevelevConjectureForty.RamanujanSet`
- Truth anchor: `D5/S3/Arith/Primes/ShevelevConjectureForty.count`
- Truth anchor: `D5/S3/Arith/Primes/ShevelevConjectureForty.count_before_double_pos`
- Truth anchor: `D5/S3/Arith/Primes/ShevelevConjectureForty.count_succ_le`
- Truth anchor: `D5/S3/Arith/Primes/ShevelevConjectureForty.count_window_left`
- Truth anchor: `D5/S3/Arith/Primes/ShevelevConjectureForty.count_window_right`
- Truth anchor: `D5/S3/Arith/Primes/ShevelevConjectureForty.eventually_count_ge`
- Truth anchor: `D5/S3/Arith/Primes/ShevelevConjectureForty.exists_count_eq`
- Truth anchor: `D5/S3/Arith/Primes/ShevelevConjectureForty.exists_separation`
- Truth anchor: `D5/S3/Arith/Primes/ShevelevConjectureForty.labosPrime`
- Truth anchor: `D5/S3/Arith/Primes/ShevelevConjectureForty.labosSet_nonempty`
- Truth anchor: `D5/S3/Arith/Primes/ShevelevConjectureForty.primeCounting_eq_of_no_prime`
- Truth anchor: `D5/S3/Arith/Primes/ShevelevConjectureForty.primeCounting_half_floor_le`
- Truth anchor: `D5/S3/Arith/Primes/ShevelevConjectureForty.primeCounting_succ`
- Truth anchor: `D5/S3/Arith/Primes/ShevelevConjectureForty.ramanujanCount`
- Truth anchor: `D5/S3/Arith/Primes/ShevelevConjectureForty.ramanujanCount_add_half`
- Truth anchor: `D5/S3/Arith/Primes/ShevelevConjectureForty.ramanujanCount_eq_count_floor`
- Truth anchor: `D5/S3/Arith/Primes/ShevelevConjectureForty.ramanujanCount_nat`
- Truth anchor: `D5/S3/Arith/Primes/ShevelevConjectureForty.ramanujanPrime`
- Truth anchor: `D5/S3/Arith/Primes/ShevelevConjectureForty.ramanujanSet_nonempty`
- Truth anchor: `D5/S3/Arith/Primes/ShevelevConjectureForty.result`
- Truth anchor: `D5/S3/Arith/Primes/ShevelevConjectureForty.subtrahend_le`
- Dependency: [D5/S3/Arith/Primes/PrimeDoubleCompositeWindow](PrimeDoubleCompositeWindow.md)
- Dependency: [D5/S3/Arith/Robin/EulerLayerRootCorrection](../Robin/EulerLayerRootCorrection.md)
