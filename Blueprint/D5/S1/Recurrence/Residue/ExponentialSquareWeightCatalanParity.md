# Exponential Square Weights and Catalan Parity

## Abstract

The coefficients of OEIS A397242 are odd exactly one below a power of two.

The first conjecture in hanna2026a397242 concerns the equation A=exp(L), where L=x+Sum (n^2-1)a(n)x^n/n^2 for n>=2. Its formal differential reading is A(0)=1 and X A'=M A, with M=X L'. The differential identity and rational uniqueness below use exactly this reading. The two conjectures modulo three are separate statements.

Indices are natural numbers. Subtraction inside an index is natural subtraction, whereas the factors n^2-1 use ring subtraction. The functions a and d have integer values; int casts a natural number to an integer, ratNat and ratInt cast to the rationals, and modTwo casts an integer to ZMod(2). All displayed fractions are rational division. The operator mk constructs a formal power series, coeff extracts a coefficient, and derivative takes the formal derivative over its indicated ring. The maps mapRat and mapTwo apply the canonical integer-to-rational and integer-to-ZMod(2) ring homomorphisms. The sets range(n) and Ico(r,n) mean 0<=j<n and r<=j<n.

The symbol K denotes the imported integer series `D5/S1/Recurrence/Invariants/CatalanCompositionSquareParity.catalanSeries`. Its imported catalan_equation states K(0)=0, coeff(1,K)=1 and K=X+K^2; binary_catalan identifies the support of mapTwo(K) as the powers of two. This is the formal prerequisite for the Catalan identification and the parity theorem.

**Definition 1.1 (Integral normalized coefficients).**

$$\begin{aligned}\operatorname{d}: \mathbb{N} \to \mathbb{Z}\\\forall n: \mathbb{N}, \operatorname{d}\left(n\right) = (\operatorname{if} (2 \le n) \operatorname{then} (\operatorname{int}\left(n - 1\right)) \cdot (\operatorname{d}\left(n - 1\right)) + \sum_{j \in \operatorname{range}\left(n\right)} ((\operatorname{if} ((2 \le j) \land (j < n)) \operatorname{then} ((((\operatorname{int}\left(j\right))^{2} - 1) \cdot (\operatorname{int}\left(n - j\right))) \cdot (\operatorname{d}\left(j\right))) \cdot (\operatorname{d}\left(n - j\right)) \operatorname{else} 0)) \operatorname{else} (\operatorname{if} (n = 1) \operatorname{then} 1 \operatorname{else} 0))\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/Residue/ExponentialSquareWeightCatalanParity.d` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The guarded recursion uses only smaller indices. Its base values are d(0)=0 and d(1)=1.

**Definition 1.2 (The coefficient sequence).**

$$\begin{aligned}\operatorname{a}: \mathbb{N} \to \mathbb{Z}\\\forall n: \mathbb{N}, \operatorname{a}\left(n\right) = (\operatorname{if} (n = 0) \operatorname{then} 1 \operatorname{else} (\operatorname{int}\left(n\right)) \cdot (\operatorname{d}\left(n\right)))\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/Residue/ExponentialSquareWeightCatalanParity.a` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The constant coefficient is one. Every positive-index coefficient is n times the integral normalized coefficient d(n).

**Theorem 1.3 (The integral convolution recurrence).**

$$\forall n: \mathbb{N}, (2 \le n) \implies (\operatorname{d}\left(n\right) = (\operatorname{int}\left(n - 1\right)) \cdot (\operatorname{d}\left(n - 1\right)) + \sum_{j \in \operatorname{Ico}\left(2, n\right)} (((((\operatorname{int}\left(j\right))^{2} - 1) \cdot (\operatorname{int}\left(n - j\right))) \cdot (\operatorname{d}\left(j\right))) \cdot (\operatorname{d}\left(n - j\right))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/ExponentialSquareWeightCatalanParity.d_recurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Removing the guards restricts the convolution to 2<=j<n. The coefficient of d(n) is one, so the recurrence determines integers without division.

**Theorem 1.4 (The integral normalization).**

$$\forall n: \mathbb{N}, (1 \le n) \implies (\operatorname{a}\left(n\right) = (\operatorname{int}\left(n\right)) \cdot (\operatorname{d}\left(n\right)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/ExponentialSquareWeightCatalanParity.a_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At every positive index the defining branch gives a(n)=n d(n).

**Definition 1.5 (The integral logarithmic derivative).**

$$M: \operatorname{PowerSeries}\left(\mathbb{Z}\right), M = \operatorname{mk}\left((n \mapsto (\operatorname{if} (n = 0) \operatorname{then} 0 \operatorname{else} (\operatorname{if} (n = 1) \operatorname{then} 1 \operatorname{else} ((\operatorname{int}\left(n\right))^{2} - 1) \cdot (\operatorname{d}\left(n\right)))))\right)$$

*Formalization.* `D5/S1/Recurrence/Residue/ExponentialSquareWeightCatalanParity.M` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The series M has coefficients zero and one at degrees zero and one. At every higher degree its coefficient is (n^2-1)d(n).

**Theorem 1.6 (The formal exponential equation).**

$$(\operatorname{coeff}\left(0, \operatorname{mk}\left(\operatorname{a}\right)\right) = 1) \land ((X) \cdot (\operatorname{derivative}\left(\mathbb{Z}, \operatorname{mk}\left(\operatorname{a}\right)\right)) = (M) \cdot (\operatorname{mk}\left(\operatorname{a}\right)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/ExponentialSquareWeightCatalanParity.log_derivative_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Coefficient comparison separates the endpoints and linear term of M A. The remaining convolution is the recurrence for d(n). Adding (n^2-1)d(n) gives n^2 d(n), which is coefficient n of X A'. The constant coefficient of A is one.

**Theorem 1.7 (The exact rational weights).**

$$\forall n: \mathbb{N}, (2 \le n) \implies (\operatorname{coeff}\left(n, \operatorname{mapRat}\left(M\right)\right) = \frac{((\operatorname{ratNat}\left(n\right))^{2} - 1) \cdot (\operatorname{ratInt}\left(\operatorname{a}\left(n\right)\right))}{\operatorname{ratNat}\left(n\right)})$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/ExponentialSquareWeightCatalanParity.coeff_M_rat` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For n>=2, substitution of a(n)=n d(n) and cancellation of the nonzero rational n gives coefficient (n^2-1)a(n)/n. This is coefficient n of X L' for the exponent in hanna2026a397242.

**Theorem 1.8 (Uniqueness among rational solutions).**

$$\forall b: \mathbb{N} \to \mathbb{Q}, \forall m: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (b\left(0\right) = 1) \implies ((\operatorname{coeff}\left(0, m\right) = 0) \implies ((\operatorname{coeff}\left(1, m\right) = 1) \implies ((\forall n: \mathbb{N}, (2 \le n) \implies (\operatorname{coeff}\left(n, m\right) = \frac{((\operatorname{ratNat}\left(n\right))^{2} - 1) \cdot (b\left(n\right))}{\operatorname{ratNat}\left(n\right)})) \implies (((X) \cdot (\operatorname{derivative}\left(\mathbb{Q}, \operatorname{mk}\left(b\right)\right)) = (m) \cdot (\operatorname{mk}\left(b\right))) \implies (\forall n: \mathbb{N}, b\left(n\right) = \operatorname{ratInt}\left(\operatorname{a}\left(n\right)\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/ExponentialSquareWeightCatalanParity.generating_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Strong induction compares the two differential equations. Every interior convolution term agrees at smaller indices. Degree one is forced to one; at higher degrees clearing n from the remaining equation forces equality of the nth coefficients.

**Theorem 1.9 (The decimated Catalan series).**

$$(X) \cdot (\operatorname{mk}\left((m \mapsto \operatorname{modTwo}\left(\operatorname{d}\left((2) \cdot (m) + 1\right)\right))\right)) = \operatorname{mapTwo}\left(K\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/ExponentialSquareWeightCatalanParity.mod_two_catalan` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reduction modulo two kills the convolution at even indices, giving d(2m)=d(2m-1) for m>=1. Splitting the odd-index convolution into even and odd summation indices then gives the Catalan recurrence for e(m)=d(2m+1) in ZMod(2). Its series E satisfies E=1+X E^2. Both X E and mapTwo(K) satisfy Y=X+Y^2 and have constant coefficient zero. Their difference is annihilated by the unit 1-Y-Z, so they agree.

**Theorem 1.10 (The first A397242 conjecture).**

$$\forall n: \mathbb{N}, \operatorname{Odd}\left(\operatorname{a}\left(n\right)\right) \iff (\exists k: \mathbb{N}, n + 1 = (2)^{k})$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/ExponentialSquareWeightCatalanParity.hanna_conjecture` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a397242-exponential-square-weight-catalan-parity` (proved) by `D5/S1/Recurrence/Residue/ExponentialSquareWeightCatalanParity.hanna_conjecture`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a397242-exponential-square-weight-catalan-parity","declaration_gid":"D5/S1/Recurrence/Residue/ExponentialSquareWeightCatalanParity.hanna_conjecture","resolution_kind":"proved"} -->

*Citation.* Paul D. Hanna (2026). *OEIS A397242, o.g.f. A(x) = exp(x + Sum (n^2-1) a(n) x^n / n^2), parity conjecture*. URL: <https://oeis.org/A397242>.

*Commentary.*

At positive even indices the factor n makes a(n) even. At index 2m+1 the Catalan identity and imported binary support say that d(2m+1) is odd exactly when m+1 is a power of two. Doubling translates this to n+1 being a power of two. The constant coefficient corresponds to 2^0.

## References

- Truth anchor: `D5/S1/Recurrence/Invariants/CatalanCompositionSquareParity.catalanSeries`
- Truth anchor: `D5/S1/Recurrence/Residue/ExponentialSquareWeightCatalanParity.M`
- Truth anchor: `D5/S1/Recurrence/Residue/ExponentialSquareWeightCatalanParity.a`
- Truth anchor: `D5/S1/Recurrence/Residue/ExponentialSquareWeightCatalanParity.a_eq`
- Truth anchor: `D5/S1/Recurrence/Residue/ExponentialSquareWeightCatalanParity.coeff_M_rat`
- Truth anchor: `D5/S1/Recurrence/Residue/ExponentialSquareWeightCatalanParity.d`
- Truth anchor: `D5/S1/Recurrence/Residue/ExponentialSquareWeightCatalanParity.d_recurrence`
- Truth anchor: `D5/S1/Recurrence/Residue/ExponentialSquareWeightCatalanParity.generating_unique`
- Truth anchor: `D5/S1/Recurrence/Residue/ExponentialSquareWeightCatalanParity.hanna_conjecture`
- Truth anchor: `D5/S1/Recurrence/Residue/ExponentialSquareWeightCatalanParity.log_derivative_identity`
- Truth anchor: `D5/S1/Recurrence/Residue/ExponentialSquareWeightCatalanParity.mod_two_catalan`
- Dependency: [D5/S1/Recurrence/Invariants/CatalanCompositionSquareParity](../Invariants/CatalanCompositionSquareParity.md)
