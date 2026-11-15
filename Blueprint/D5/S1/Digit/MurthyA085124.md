# Murthy's joint decimal divisibility classification

## Abstract

The positive terms of Murthy's decimal digit-product sequence have an exact classification.

Write P(N) for DigitProductSlices.digitProduct N, the product of Nat.digits 10 N. These are the ordinary decimal digits, in reverse order, with no leading zero. The product is independent of their order. The explicit positive-N condition excludes the empty expansion of zero, whose list product in Lean is one.

**Definition 1.1 (The exact qualifying predicate).**

$$\forall n \in \mathbb{N},\; \forall N \in \mathbb{N},\; \operatorname{admissible}\left(n, N\right) \Leftrightarrow \left(0 < N \land \left(n \mid N \land \left(0 < \operatorname{P}\left(N\right) \land n \mid \operatorname{P}\left(N\right)\right)\right)\right)$$

*Formalization.* `D5/S1/Digit/MurthyA085124.admissible` (`✓ std3`).

*Citation.* Amarnath Murthy (2003). *OEIS A085124, Smallest multiple of n whose digital product is also a positive multiple of n, or 0 if no such number exists*. URL: <https://oeis.org/A085124>.

*Commentary.*

Both divisibilities have n on the left. Positivity of the product excludes every zero digit. There is no bound on n, N, digit length or prime exponents.

**Definition 1.2 (The least positive multiple, or zero).**

$$\forall n \in \mathbb{N},\; \operatorname{a}\left(n\right) = \begin{cases}\operatorname{min}\left(\{N : \mathbb{N} \mid \operatorname{admissible}\left(n, N\right)\}\right)&\exists N \in \mathbb{N},\; \operatorname{admissible}\left(n, N\right)\\0&\neg (\exists N \in \mathbb{N},\; \operatorname{admissible}\left(n, N\right))\end{cases}$$

*Formalization.* `D5/S1/Digit/MurthyA085124.a085124` (`✓ std3`).

*Citation.* Amarnath Murthy (2003). *OEIS A085124, Smallest multiple of n whose digital product is also a positive multiple of n, or 0 if no such number exists*. URL: <https://oeis.org/A085124>.

*Commentary.*

OEIS A085124, NAME: Smallest multiple of n whose digital product is also a positive multiple of n, or 0 if no such number exists. Nat.find supplies the least qualifying natural when the set is inhabited; the other branch is zero. The source domain starts at n=1.

**Theorem 1.3 (Classification and full least-or-zero bridge).**

$$\forall n \in \mathbb{N},\; 0 < n \Rightarrow \left(\left(\left(\exists N \in \mathbb{N},\; \operatorname{admissible}\left(n, N\right)\right) \Leftrightarrow \left(\left(\forall p \in \mathbb{N},\; \operatorname{Prime}\left(p\right) \Rightarrow \left(p \mid n \Rightarrow p \le 7\right)\right) \land \left(\neg (10 \mid n)\right)\right)\right) \land \left(\left(0 < \operatorname{a}\left(n\right) \Leftrightarrow \left(\left(\forall p \in \mathbb{N},\; \operatorname{Prime}\left(p\right) \Rightarrow \left(p \mid n \Rightarrow p \le 7\right)\right) \land \left(\neg (10 \mid n)\right)\right)\right) \land \left(\left(\operatorname{a}\left(n\right) = 0 \Leftrightarrow \left(\neg (\exists N \in \mathbb{N},\; \operatorname{admissible}\left(n, N\right))\right)\right) \land \left(0 < \operatorname{a}\left(n\right) \Rightarrow \left(\operatorname{admissible}\left(n, \operatorname{a}\left(n\right)\right) \land \left(\forall N \in \mathbb{N},\; \operatorname{admissible}\left(n, N\right) \Rightarrow \operatorname{a}\left(n\right) \le N\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/MurthyA085124.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Amarnath Murthy (2003). *OEIS A085124, Smallest multiple of n whose digital product is also a positive multiple of n, or 0 if no such number exists*. URL: <https://oeis.org/A085124>.

*Acknowledgement.* N. S. (2016). *Answer to Does every number not ending with zero have a multiple without zero digits at all?*. URL: <https://math.stackexchange.com/a/2067782>.

*Commentary.*

For every positive natural n, existence is equivalent to all prime divisors being at most seven and ten not dividing n. The same condition is equivalent to positivity of the least-or-zero sequence. Its zero value means that no qualifying integer exists; whenever positive, it qualifies and is at most every qualifying N. This includes n=1: N=1 qualifies and the minimum is one. For necessity, a prime divisor of n divides a nonzero decimal digit. A multiple of ten has a terminal zero. For sufficiency write n=p^k m with p either two or five, m coprime to ten and p^k coprime to m. The absence of a factor ten permits this decomposition. N. S.'s digit lifting supplies a zero-free k-digit suffix divisible by p^k, including the empty suffix at k=0. Prepend the prime factors of n, with multiplicity, and a digit one to make a nonempty block. The block product is divisible by n. Let b be ten to its length. Euler's theorem modulo m(b-1), followed by the geometric sum identity and cancellation of b-1, supplies a positive repetition count for which m divides the repetition sum. Literal repetition preserves the p^k divisibility, positive product and divisibility of that product by n. All digit reconstruction and arithmetic are kernel checked for arbitrary parameters. The suffix and repetition mechanism are prior work; their use with a prime-factor word and the joint classification are a repository derivation. The bounded literature screen found no exact resolution and does not establish global novelty.

## References

- Truth anchor: `D5/S1/Digit/MurthyA085124.a085124`
- Truth anchor: `D5/S1/Digit/MurthyA085124.admissible`
- Truth anchor: `D5/S1/Digit/MurthyA085124.result`
- Dependency: [D5/S1/Digit/DigitProductSlices](DigitProductSlices.md)
