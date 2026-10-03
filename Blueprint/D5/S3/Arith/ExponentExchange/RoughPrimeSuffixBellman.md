# Rough Prime Suffix Maxima

## Abstract

The exact rough-integer maximum is attained by a consecutive prime suffix.

Write q(y,i) for the i-th prime strictly above y, S(y,i,t) for the product of its consecutive prime powers with exponent list t, and W(y,i,t) for the product of reciprocal geometric sums G(q,a). Both empty products are one. F(y,i,b,h,t) means that t has positive, weakly decreasing entries, its first entry is at most h, and S is at most b. R(y,n) means every prime divisor of n is greater than y. Z(n) is sigma1(n)/n in the real numbers. V is the semantic maximum of W over F, U is the maximum of Z over rough integers in [1,B], and c(y,B) is Nat.log(q(y,0),B), the natural-number floor logarithm. All number variables are natural numbers; t is a finite list of natural numbers, and W, Z, V and U are real-valued. Precisely, q(y,i) = Nat.nth(Nat.Prime,Nat.primeCounting(y)+i), G(q,a) = sum_{k=0}^a (q^{-1})^k, S(y,i,[]) = W(y,i,[]) = 1, S(y,i,a::t) = q(y,i)^a S(y,i+1,t), and W(y,i,a::t) = G(q(y,i),a) W(y,i+1,t). Ordered(h,[]) is true, Ordered(h,a::t) means 0<a <= h and Ordered(a,t), and F means Ordered and S <= b. For b=0, V is zero; for B=0, U is zero.

**Theorem 1.1 (Finite suffix states).**

$$\forall     y  , i  , b  , h   : \mathbb{N} ,    Finite\left(\{ t : List\left(\mathbb{N}\right) \mid   F\left(y, i, b, h, t\right) \} \right) $$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ExponentExchange/RoughPrimeSuffixBellman.feasible_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary natural y, i, b and h, the feasible list set is finite. The represented positive integer exceeds the list length, and every entry is at most h. Thus only finitely many lists can fit the state.

**Theorem 1.2 (Complete branches and attained upper bounds).**

$$\begin{aligned}\forall     y  , i  , b  , h   : \mathbb{N} ,    1 \le b \Rightarrow [ \\V\left(y, i, b, h\right) = max\left(\{ 1 \} \cup   \{ G\left(q\left(y, i\right), a\right) \cdot V\left(y, i + 1 , div\left(b, q\left(y, i\right)^{a}\right), a\right) \mid   a : \mathbb{N} , 1 \le a \le h \land q\left(y, i\right)^{a} \le b \} \right) \\\land ( \forall     t   : List\left(\mathbb{N}\right) ,    F\left(y, i, b, h, t\right) \Rightarrow W\left(y, i, t\right) \le V\left(y, i, b, h\right) ) \\\land ( \exists     t   : List\left(\mathbb{N}\right) ,    F\left(y, i, b, h, t\right) \land W\left(y, i, t\right) = V\left(y, i, b, h\right) ) \\\land ( \forall     a   : \mathbb{N} ,    1 \le a \land q\left(y, i\right)^{a} \le b \Rightarrow div\left(b, q\left(y, i\right)^{a}\right) < b ) ] \end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ExponentExchange/RoughPrimeSuffixBellman.bellman_complete` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed finite branch set consists of one and every G(q(y,i),a) times V(y,i+1,div(b,q(y,i)^a),a), for natural a with 1 <= a <= h and q(y,i)^a <= b. The operation div is natural division. The four displayed clauses are denoted C(y,i,b,h) below. Splitting a nonempty exponent list gives exactly one legal branch; joining a legal head to a child suffix gives a feasible parent. Positive branches strictly reduce the integer budget, so every branch path terminates. No positive branch is omitted, and a zero head ends the entire suffix.

**Theorem 1.3 (Actual suffix prime support).**

$$\begin{aligned}\forall     y  , i   : \mathbb{N} ,    \forall     t   : List\left(\mathbb{N}\right) ,    [ 0 < S\left(y, i, t\right) \\\land ( \forall     p   : \mathbb{N} ,    Prime\left(p\right) \land dvd\left(p, S\left(y, i, t\right)\right) \Rightarrow \exists     j   : \mathbb{N} ,    j < length\left(t\right) \land p = q\left(y, i + j \right) ) \\\land R\left(y, S\left(y, i, t\right)\right) ] \end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ExponentExchange/RoughPrimeSuffixBellman.suffix_prime_factors` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every prime divisor of S occurs at a position of the actual exponent list. Distinct positions use strictly increasing primes. In particular S is positive and rough, even when the list is empty.

**Theorem 1.4 (Equality with the global rough maximum).**

$$\begin{aligned}\forall     y  , B   : \mathbb{N} ,    1 \le y \land 1 \le B \Rightarrow [ \\( \forall     i  , b  , h   : \mathbb{N} ,    1 \le b \Rightarrow C\left(y, i, b, h\right) ) \\\land ( \forall     p   : \mathbb{N} ,    ( Prime\left(p\right) \land y < p ) \Leftrightarrow \exists     i   : \mathbb{N} ,    p = q\left(y, i\right) ) \\\land ( \forall     a   : \mathbb{N} ,    a \le c\left(y, B\right) \Leftrightarrow q\left(y, 0\right)^{a} \le B ) \\\land ( \forall     i   : \mathbb{N} ,    \forall     t   : List\left(\mathbb{N}\right) ,    Z\left(S\left(y, i, t\right)\right) = W\left(y, i, t\right) ) \\\land ( \exists     n   : \mathbb{N} ,    \exists     t   : List\left(\mathbb{N}\right) ,    1 \le n \le B \land R\left(y, n\right) \land F\left(y, 0, B, c\left(y, B\right), t\right) \\\land S\left(y, 0, t\right) = n \land W\left(y, 0, t\right) = U\left(y, B\right) ) \\\land U\left(y, B\right) = V\left(y, 0, B, c\left(y, B\right)\right) ] \end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ExponentExchange/RoughPrimeSuffixBellman.rough_prime_suffix_complete` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every y >= 1 and B >= 1, all six displayed clauses hold. C retains the complete branch equation, every suffix upper bound, attainment, and strict budget descent for every state with b >= 1. The prime sequence contains every prime above y, and a <= c is equivalent to the first prime power fitting B. The sigma identity holds for every suffix list, without an ordering assumption. The existential clause gives one actual rough maximizing integer and a feasible suffix representing that exact integer. Its weight is U, and U equals the root suffix maximum. This includes B = 1, c = 0 and the empty suffix. No executable evaluator or certificate checker is defined by these semantic maxima.

The finite rough-integer family contains one and has a maximizing member. An inversion of allowed prime valuations, including a zero valuation at the smaller prime, gives a smaller rough integer with strictly greater Z by prime exponent exchange. Thus maximizing valuations are weakly decreasing. To reconstruct a maximizing integer, enumerate its prime valuations over a finite range bounded by primeCounting(n). The valuation order makes the positive entries an initial consecutive prefix: once a valuation is zero, all later entries are zero. Factorization reconstruction recovers n exactly. Coprimality of a head prime with the tail and the prime-power sigma formula identify W with Z. The full first prime power divides n, giving the logarithmic head bound. This suffix gives U <= V; an attaining feasible suffix gives a positive rough integer in [1,B], proving V <= U.

## References

- Truth anchor: `D5/S3/Arith/ExponentExchange/RoughPrimeSuffixBellman.bellman_complete`
- Truth anchor: `D5/S3/Arith/ExponentExchange/RoughPrimeSuffixBellman.feasible_finite`
- Truth anchor: `D5/S3/Arith/ExponentExchange/RoughPrimeSuffixBellman.rough_prime_suffix_complete`
- Truth anchor: `D5/S3/Arith/ExponentExchange/RoughPrimeSuffixBellman.suffix_prime_factors`
- Dependency: [D5/S3/Arith/ExponentExchange/IntegerSwap](IntegerSwap.md)
- Dependency: [D5/S3/Arith/RobinExponentSwap](../RobinExponentSwap.md)
