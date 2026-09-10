# Congruences for the Exponential Square-Weight Family

## Abstract

Odd square-weight parameters have binary parity support; parameter two has period four modulo eight.

For integer q, define the integral normalization b(q,n), and set a(q,0)=1 and a(q,n)=n b(q,n) for positive n. For q nonzero, source_iff proves that these are exactly the coefficients of the self-referential formal equation A=exp(L). Here L=x+Sum (q n^2-1)a(q,n)x^n/(q n^2), with the sum starting at n=2. The equation is formal, with no assertion of analytic convergence. The integer parameter is 5, 3, 1 or 2; it is not the square-root parameter used in the entries' reversion formulas.

All indices are natural. Subtraction in an index is natural subtraction; coefficients and weights use integer or rational ring subtraction. int and rat are the indicated canonical casts; mod2 and mod8 are casts to ZMod(2) and ZMod(8). mapRat maps an integer power series to the rationals. mk constructs a power series from its coefficients; coeff extracts a coefficient, C is a constant series, derivative is the formal derivative over the displayed ring, subst is formal substitution, and expQ is the standard rational exponential power series. Ico(r,n) means r<=j<n, and range(n) means 0<=j<n.

The imported d and a1 are the exact frozen q=1 definitions `D5/S1/Recurrence/Residue/ExponentialSquareWeightCatalanParity.d` and `D5/S1/Recurrence/Residue/ExponentialSquareWeightCatalanParity.a`. Their parity theorem `D5/S1/Recurrence/Residue/ExponentialSquareWeightCatalanParity.hanna_conjecture` already settles A397242. It is reused here and receives no second problem claim. The new work is strong induction transporting odd parameters modulo two, and endpoint separation of the parameter-two convolution modulo eight.

**Definition 1.1 (The integral normalization).**

$$\forall q: \mathbb{Z}, \forall n: \mathbb{N}, \operatorname{b}\left(q, n\right) = (\operatorname{if} (2 \le n) \operatorname{then} ((q) \cdot (\operatorname{int}\left(n - 1\right))) \cdot (\operatorname{b}\left(q, n - 1\right)) + \sum_{j \in \operatorname{range}\left(n\right)} ((\operatorname{if} ((2 \le j) \land (j < n)) \operatorname{then} ((((q) \cdot ((\operatorname{int}\left(j\right))^{2}) - 1) \cdot (\operatorname{int}\left(n - j\right))) \cdot (\operatorname{b}\left(q, j\right))) \cdot (\operatorname{b}\left(q, n - j\right)) \operatorname{else} 0)) \operatorname{else} (\operatorname{if} (n = 1) \operatorname{then} 1 \operatorname{else} 0))$$

*Formalization.* `D5/S1/Recurrence/Residue/ParametricExponentialSquareCongruence.b` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The guarded recursion only calls smaller indices; b(q,0)=0 and b(q,1)=1.

**Definition 1.2 (Original coefficients).**

$$\forall q: \mathbb{Z}, \forall n: \mathbb{N}, \operatorname{a}\left(q, n\right) = (\operatorname{if} (n = 0) \operatorname{then} 1 \operatorname{else} (\operatorname{int}\left(n\right)) \cdot (\operatorname{b}\left(q, n\right)))$$

*Formalization.* `D5/S1/Recurrence/Residue/ParametricExponentialSquareCongruence.a` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Positive coefficients are index multiples of the integer normalization.

**Theorem 1.3 (The bounded convolution).**

$$\forall q: \mathbb{Z}, \forall n: \mathbb{N}, (2 \le n) \implies (\operatorname{b}\left(q, n\right) = ((q) \cdot (\operatorname{int}\left(n - 1\right))) \cdot (\operatorname{b}\left(q, n - 1\right)) + \sum_{j \in \operatorname{Ico}\left(2, n\right)} (((((q) \cdot ((\operatorname{int}\left(j\right))^{2}) - 1) \cdot (\operatorname{int}\left(n - j\right))) \cdot (\operatorname{b}\left(q, j\right))) \cdot (\operatorname{b}\left(q, n - j\right))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/ParametricExponentialSquareCongruence.b_recurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Filtering the guarded range gives exactly the interval 2<=j<n.

**Theorem 1.4 (Normalization at positive indices).**

$$\forall q: \mathbb{Z}, \forall n: \mathbb{N}, (1 \le n) \implies (\operatorname{a}\left(q, n\right) = (\operatorname{int}\left(n\right)) \cdot (\operatorname{b}\left(q, n\right)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/ParametricExponentialSquareCongruence.a_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This companion exposes the positive branch for the source and congruence proofs.

**Definition 1.5 (Scaled logarithmic derivative).**

$$\forall q: \mathbb{Z}, \operatorname{M}\left(q\right) = \operatorname{mk}\left((n \mapsto (\operatorname{if} (n = 0) \operatorname{then} 0 \operatorname{else} (\operatorname{if} (n = 1) \operatorname{then} q \operatorname{else} ((q) \cdot ((\operatorname{int}\left(n\right))^{2}) - 1) \cdot (\operatorname{b}\left(q, n\right)))))\right)$$

*Formalization.* `D5/S1/Recurrence/Residue/ParametricExponentialSquareCongruence.M` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

M has coefficients 0, q and (q n^2-1)b(q,n), in degrees 0, 1 and n>=2.

**Theorem 1.6 (The integral differential equation).**

$$\forall q: \mathbb{Z}, (\operatorname{coeff}\left(0, \operatorname{mk}\left(\operatorname{a}\left(q\right)\right)\right) = 1) \land ((\operatorname{C}\left(q\right)) \cdot ((X) \cdot (\operatorname{derivative}\left(\mathbb{Z}, \operatorname{mk}\left(\operatorname{a}\left(q\right)\right)\right))) = (\operatorname{M}\left(q\right)) \cdot (\operatorname{mk}\left(\operatorname{a}\left(q\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/ParametricExponentialSquareCongruence.log_derivative_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Separate the last coefficient and degree-one term of M A. The remaining sum is b's recurrence, so adding the diagonal yields q n^2 b(q,n).

**Theorem 1.7 (Exact rational weights).**

$$\forall q: \mathbb{Z}, \forall n: \mathbb{N}, (2 \le n) \implies (\operatorname{coeff}\left(n, \operatorname{mapRat}\left(\operatorname{M}\left(q\right)\right)\right) = \frac{((\operatorname{rat}\left(q\right)) \cdot ((\operatorname{rat}\left(n\right))^{2}) - 1) \cdot (\operatorname{rat}\left(\operatorname{a}\left(q, n\right)\right))}{\operatorname{rat}\left(n\right)})$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/ParametricExponentialSquareCongruence.coeff_M_rat` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Cancel the nonzero index n after using a(q,n)=n b(q,n).

**Theorem 1.8 (Rational differential uniqueness).**

$$\forall q: \mathbb{Z}, \forall f: \mathbb{N} \to \mathbb{Q}, \forall m: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (q \neq 0) \implies ((f\left(0\right) = 1) \implies ((\operatorname{coeff}\left(0, m\right) = 0) \implies ((\operatorname{coeff}\left(1, m\right) = \operatorname{rat}\left(q\right)) \implies ((\forall n: \mathbb{N}, (2 \le n) \implies (\operatorname{coeff}\left(n, m\right) = \frac{((\operatorname{rat}\left(q\right)) \cdot ((\operatorname{rat}\left(n\right))^{2}) - 1) \cdot (f\left(n\right))}{\operatorname{rat}\left(n\right)})) \implies (((\operatorname{C}\left(\operatorname{rat}\left(q\right)\right)) \cdot ((X) \cdot (\operatorname{derivative}\left(\mathbb{Q}, \operatorname{mk}\left(f\right)\right))) = (m) \cdot (\operatorname{mk}\left(f\right))) \implies (\forall n: \mathbb{N}, f\left(n\right) = \operatorname{rat}\left(\operatorname{a}\left(q, n\right)\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/ParametricExponentialSquareCongruence.generating_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Strong induction equates all smaller convolution terms. At degree one q nonzero forces the coefficient 1. At higher degrees the diagonal weight cancels q n^2, leaving a coefficient difference equal to zero.

**Definition 1.9 (The source exponent).**

$$\forall q: \mathbb{Z}, \forall f: \mathbb{N} \to \mathbb{Q}, \operatorname{exponent}\left(q, f\right) = \operatorname{mk}\left((n \mapsto (\operatorname{if} (n = 0) \operatorname{then} 0 \operatorname{else} (\operatorname{if} (n = 1) \operatorname{then} 1 \operatorname{else} \frac{((\operatorname{rat}\left(q\right)) \cdot ((\operatorname{rat}\left(n\right))^{2}) - 1) \cdot (\operatorname{f}\left(n\right))}{(\operatorname{rat}\left(q\right)) \cdot ((\operatorname{rat}\left(n\right))^{2})})))\right)$$

*Formalization.* `D5/S1/Recurrence/Residue/ParametricExponentialSquareCongruence.exponent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The constant term is zero, the linear coefficient is one, and all higher divisions occur in Q.

**Theorem 1.10 (Literal equivalence with the OEIS equation).**

$$\forall q: \mathbb{Z}, \forall f: \mathbb{N} \to \mathbb{Q}, (q \neq 0) \implies ((\operatorname{mk}\left(f\right) = \operatorname{subst}\left(\operatorname{expQ}, \operatorname{exponent}\left(q, f\right)\right)) \iff (\forall n: \mathbb{N}, \operatorname{f}\left(n\right) = \operatorname{rat}\left(\operatorname{a}\left(q, n\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/ParametricExponentialSquareCongruence.source_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The forward implication differentiates exp(L) using Mathlib's chain rule and derivative_exp, then applies generating_unique. Conversely the integer solution and exp(L) satisfy F'=L'F with the same constant coefficient; coefficient induction proves linear ODE uniqueness. This establishes existence and uniqueness for every nonzero integer parameter.

**Theorem 1.11 (Transport to the frozen normalization).**

$$\forall q: \mathbb{Z}, \forall n: \mathbb{N}, (\operatorname{Odd}\left(q\right)) \implies (\operatorname{mod2}\left(\operatorname{b}\left(q, n\right)\right) = \operatorname{mod2}\left(\operatorname{d}\left(n\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/ParametricExponentialSquareCongruence.normalized_mod_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Strong induction reduces the recurrence coefficients using q=1 in ZMod(2) and substitutes the induction hypothesis in both smaller factors. This is the live new witness for the odd-parameter endpoints.

**Theorem 1.12 (Parity for every odd parameter).**

$$\forall q: \mathbb{Z}, \forall n: \mathbb{N}, (\operatorname{Odd}\left(q\right)) \implies ((\operatorname{Odd}\left(\operatorname{a}\left(q, n\right)\right)) \iff (\exists k: \mathbb{N}, n + 1 = (2)^{k}))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/ParametricExponentialSquareCongruence.odd_parameter_parity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Multiply the transported normalization by n and apply the frozen hanna_conjecture. The constant coefficient is handled separately.

**Theorem 1.13 (The stronger parameter-two invariant).**

$$\forall n: \mathbb{N}, (2 \le n) \implies (\operatorname{mod8}\left(\operatorname{b}\left(2, n\right)\right) = (\operatorname{if} (\operatorname{mod}\left(n, 4\right) = 3) \operatorname{then} 6 \operatorname{else} 2))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/ParametricExponentialSquareCongruence.normalized_mod_eight` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For n>=3, the endpoint contributes (2n(n-1)-1)b(2,n-1). Every interior term reduces to 4(n-j) modulo eight, whose sum is 2(n-2)(n-1)-4. Eight residue cases close the induction step. The induction quantifies over all indices; it is not bounded enumeration.

**Theorem 1.14 (A397346 modulo eight).**

$$\forall n: \mathbb{N}, (2 \le n) \implies (\operatorname{mod}\left(\operatorname{a}\left(2, n\right), 8\right) = (\operatorname{if} (\operatorname{mod}\left(n, 4\right) = 2) \operatorname{then} 4 \operatorname{else} (\operatorname{if} (\operatorname{mod}\left(n, 4\right) = 0) \operatorname{then} 0 \operatorname{else} 2)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/ParametricExponentialSquareCongruence.residues_q2` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a397346-square-weight-mod-eight` (proved) by `D5/S1/Recurrence/Residue/ParametricExponentialSquareCongruence.residues_q2`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a397346-square-weight-mod-eight","declaration_gid":"D5/S1/Recurrence/Residue/ParametricExponentialSquareCongruence.residues_q2","resolution_kind":"proved"} -->

*Citation.* Paul D. Hanna (2026). *OEIS A397346: exponential square-weight congruence*. URL: <https://oeis.org/A397346>.

*Commentary.*

Multiplication by n turns the normalized invariant into residues 4,2,0,2 from n=2, with period four.

**Theorem 1.15 (A397345 parity).**

$$\forall n: \mathbb{N}, (\operatorname{Odd}\left(\operatorname{a}\left(5, n\right)\right)) \iff (\exists k: \mathbb{N}, n + 1 = (2)^{k})$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/ParametricExponentialSquareCongruence.parity_q5` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a397345-square-weight-parity` (proved) by `D5/S1/Recurrence/Residue/ParametricExponentialSquareCongruence.parity_q5`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a397345-square-weight-parity","declaration_gid":"D5/S1/Recurrence/Residue/ParametricExponentialSquareCongruence.parity_q5","resolution_kind":"proved"} -->

*Citation.* Paul D. Hanna (2026). *OEIS A397345, A397348 and A397346: exponential square-weight congruences*. URL: <https://oeis.org/A397345>.

*Commentary.*

Specialize the odd-parameter theorem using 5=2*2+1. The source_iff theorem identifies this coefficient sequence with the NAME equation.

**Theorem 1.16 (A397348 parity).**

$$\forall n: \mathbb{N}, (\operatorname{Odd}\left(\operatorname{a}\left(3, n\right)\right)) \iff (\exists k: \mathbb{N}, n + 1 = (2)^{k})$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/ParametricExponentialSquareCongruence.parity_q3` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a397348-square-weight-parity` (proved) by `D5/S1/Recurrence/Residue/ParametricExponentialSquareCongruence.parity_q3`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a397348-square-weight-parity","declaration_gid":"D5/S1/Recurrence/Residue/ParametricExponentialSquareCongruence.parity_q3","resolution_kind":"proved"} -->

*Citation.* Paul D. Hanna (2026). *OEIS A397348: exponential square-weight congruence*. URL: <https://oeis.org/A397348>.

*Commentary.*

Specialize using 3=2*1+1, with the same literal source correspondence.

**Theorem 1.17 (The four dispatched endpoints).**

$$(\forall n: \mathbb{N}, (\operatorname{Odd}\left(\operatorname{a}\left(5, n\right)\right)) \iff (\exists k: \mathbb{N}, n + 1 = (2)^{k})) \land ((\forall n: \mathbb{N}, (\operatorname{Odd}\left(\operatorname{a}\left(3, n\right)\right)) \iff (\exists k: \mathbb{N}, n + 1 = (2)^{k})) \land ((\forall n: \mathbb{N}, (\operatorname{Odd}\left(\operatorname{a1}\left(n\right)\right)) \iff (\exists k: \mathbb{N}, n + 1 = (2)^{k})) \land (\forall n: \mathbb{N}, (2 \le n) \implies (\operatorname{mod}\left(\operatorname{a}\left(2, n\right), 8\right) = (\operatorname{if} (\operatorname{mod}\left(n, 4\right) = 2) \operatorname{then} 4 \operatorname{else} (\operatorname{if} (\operatorname{mod}\left(n, 4\right) = 0) \operatorname{then} 0 \operatorname{else} 2))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/ParametricExponentialSquareCongruence.family_conjectures` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This conjunction packages the three new endpoints and the already frozen A397242 parity theorem. It is a companion, not an additional resolution. No asymptotic limits, priority claim or further modulus is asserted.

## References

- Truth anchor: `D5/S1/Recurrence/Residue/ExponentialSquareWeightCatalanParity.a`
- Truth anchor: `D5/S1/Recurrence/Residue/ExponentialSquareWeightCatalanParity.d`
- Truth anchor: `D5/S1/Recurrence/Residue/ExponentialSquareWeightCatalanParity.hanna_conjecture`
- Truth anchor: `D5/S1/Recurrence/Residue/ParametricExponentialSquareCongruence.M`
- Truth anchor: `D5/S1/Recurrence/Residue/ParametricExponentialSquareCongruence.a`
- Truth anchor: `D5/S1/Recurrence/Residue/ParametricExponentialSquareCongruence.a_eq`
- Truth anchor: `D5/S1/Recurrence/Residue/ParametricExponentialSquareCongruence.b`
- Truth anchor: `D5/S1/Recurrence/Residue/ParametricExponentialSquareCongruence.b_recurrence`
- Truth anchor: `D5/S1/Recurrence/Residue/ParametricExponentialSquareCongruence.coeff_M_rat`
- Truth anchor: `D5/S1/Recurrence/Residue/ParametricExponentialSquareCongruence.exponent`
- Truth anchor: `D5/S1/Recurrence/Residue/ParametricExponentialSquareCongruence.family_conjectures`
- Truth anchor: `D5/S1/Recurrence/Residue/ParametricExponentialSquareCongruence.generating_unique`
- Truth anchor: `D5/S1/Recurrence/Residue/ParametricExponentialSquareCongruence.log_derivative_identity`
- Truth anchor: `D5/S1/Recurrence/Residue/ParametricExponentialSquareCongruence.normalized_mod_eight`
- Truth anchor: `D5/S1/Recurrence/Residue/ParametricExponentialSquareCongruence.normalized_mod_two`
- Truth anchor: `D5/S1/Recurrence/Residue/ParametricExponentialSquareCongruence.odd_parameter_parity`
- Truth anchor: `D5/S1/Recurrence/Residue/ParametricExponentialSquareCongruence.parity_q3`
- Truth anchor: `D5/S1/Recurrence/Residue/ParametricExponentialSquareCongruence.parity_q5`
- Truth anchor: `D5/S1/Recurrence/Residue/ParametricExponentialSquareCongruence.residues_q2`
- Truth anchor: `D5/S1/Recurrence/Residue/ParametricExponentialSquareCongruence.source_iff`
- Dependency: [D5/S1/Recurrence/Residue/ExponentialSquareWeightCatalanParity](ExponentialSquareWeightCatalanParity.md)
