# The recurrence of the Hermite absolute-tie orders

## Abstract

The fifth-lag recurrence for the complete increasing enumeration of physicists Hermite absolute-tie orders.

Use HermiteAbsoluteTieOrders.IsAbsMax and HasExactlyTwo without changing their definitions. The polynomial is HermiteSignedMode.physicistsHermite over the rationals. For each natural order k, IsAbsMax compares absolute coefficients at every exponent from zero through k, including parity-zero coefficients. HasExactlyTwo means there are distinct exponents u<v and these are precisely all maximizing exponents. Thus no restricted coefficient row or selected family of orders enters the assertion.

**Definition 1.1 (The complete actual-enumeration assertion).**

$$claim = (\exists g:\mathbb{Z} \to \mathbb{N}, (\forall n:\mathbb{Z}, (1 \le n) \implies (0 < g\left(n\right))) \land ((\forall n:\mathbb{Z}, \forall m:\mathbb{Z}, (1 \le n) \implies ((n < m) \implies (g\left(n\right) < g\left(m\right)))) \land ((\forall k:\mathbb{N}, (\operatorname{HasExactlyTwo}\left(k\right)) \iff (\exists n:\mathbb{Z}, ((1 \le n) \land (k = g\left(n\right))) \land (\forall m:\mathbb{Z}, ((1 \le m) \land (k = g\left(m\right))) \implies (m = n)))) \land (\forall n:\mathbb{Z}, (6 \le n) \implies ((g\left(n\right):\mathbb{Z}) = (g\left(n-1\right):\mathbb{Z})+2\cdot(g\left(n-2\right):\mathbb{Z})-2\cdot(g\left(n-3\right):\mathbb{Z})-(g\left(n-4\right):\mathbb{Z})+(g\left(n-5\right):\mathbb{Z}))))))$$

*Formalization.* `D5/S3/Analytic/Polynomial/HermiteTieRecurrence.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mike Sheppard (2025). *Orders k of Hermite polynomials whose maximal coefficient in absolute value appears twice*. URL: <https://oeis.org/A381737/internal?rev=28>.

*Commentary.*

The function g has a value in the natural numbers at every integer argument. At every positive integer index its value is positive, and its values strictly increase on positive indices. For every natural order k, HasExactlyTwo holds if and only if k is g(n) at exactly one positive integer index n. The unique-existence notation is expanded into existence and uniqueness in the formula. At every integer n at least six, the five preceding indices are positive and the stated recurrence holds. Each individual value of g is cast to the integers before any subtraction.

**Theorem 1.2 (The full A381737 Conjecture 2 recurrence).**

$$\exists g:\mathbb{Z} \to \mathbb{N}, (\forall n:\mathbb{Z}, (1 \le n) \implies (0 < g\left(n\right))) \land ((\forall n:\mathbb{Z}, \forall m:\mathbb{Z}, (1 \le n) \implies ((n < m) \implies (g\left(n\right) < g\left(m\right)))) \land ((\forall k:\mathbb{N}, (\operatorname{HasExactlyTwo}\left(k\right)) \iff (\exists n:\mathbb{Z}, ((1 \le n) \land (k = g\left(n\right))) \land (\forall m:\mathbb{Z}, ((1 \le m) \land (k = g\left(m\right))) \implies (m = n)))) \land (\forall n:\mathbb{Z}, (6 \le n) \implies ((g\left(n\right):\mathbb{Z}) = (g\left(n-1\right):\mathbb{Z})+2\cdot(g\left(n-2\right):\mathbb{Z})-2\cdot(g\left(n-3\right):\mathbb{Z})-(g\left(n-4\right):\mathbb{Z})+(g\left(n-5\right):\mathbb{Z})))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Polynomial/HermiteTieRecurrence.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a381737-hermite-tie-recurrence` (proved) by `D5/S3/Analytic/Polynomial/HermiteTieRecurrence.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a381737-hermite-tie-recurrence","declaration_gid":"D5/S3/Analytic/Polynomial/HermiteTieRecurrence.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Mike Sheppard (2025). *Orders k of Hermite polynomials whose maximal coefficient in absolute value appears twice*. URL: <https://oeis.org/A381737/internal?rev=28>.

*Commentary.*

HermiteAbsoluteTieOrders.result supplies the positive, strictly increasing, exhaustive, uniquely indexed enumeration b(m)=2m(m+2)+(m+1)(-1)^(m+1) for positive natural m. Define g(n) as the natural value of b(n.toNat). Positivity of b at positive indices makes the casts exact. Conversion between positive integer and positive natural indices preserves order, existence and uniqueness, so this is the actual enumeration of all qualifying orders. For t=n-5, expand b(t+5), b(t+4), b(t+3), b(t+2), b(t+1) and b(t). The quadratic part and the alternating linear part each satisfy the displayed recurrence; expansion of powers of minus one and polynomial normalization give their sum. This proves the recurrence for every n at least six, with no finite cutoff or additional assumption. The recurrence is the assertion named Conjecture 2 in OEIS A381737 revision 28, offset 1,1. Its proof is a consequence of the stronger Conjecture 1 enumeration.

## References

- Truth anchor: `D5/S3/Analytic/Polynomial/HermiteTieRecurrence.claim`
- Truth anchor: `D5/S3/Analytic/Polynomial/HermiteTieRecurrence.result`
- Dependency: [D5/S3/Analytic/Polynomial/HermiteAbsoluteTieOrders](HermiteAbsoluteTieOrders.md)
