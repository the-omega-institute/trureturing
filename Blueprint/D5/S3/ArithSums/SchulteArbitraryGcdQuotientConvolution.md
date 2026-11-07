# Schulte's arbitrary-function gcd-quotient convolution

## Abstract

Arbitrary complex weights on Schulte's gcd quotient form a Dirichlet convolution.

Let N denote the natural numbers including zero, P the positive integers, and C the complex numbers. All gcd operations and slashes are natural-number operations. Write ofNat for the canonical map from N to C, phi for Euler's totient, and ite(p,x,y) for x when p holds and y otherwise. Divisor sums use positive divisors; at zero the natural divisor set is empty. No value of a function on P at zero is assumed.

**Definition 1.1 (The original ordered square).**

$$\forall g \in \mathbb{N} \to \mathbb{C},\; \forall n \in \mathbb{N},\; \operatorname{square}\left(g, n\right) = \sum_{i = 1..n} \sum_{k = 1..n} \operatorname{g}\left((\operatorname{gcd}\left(i, n\right)) / (\operatorname{gcd}\left(\operatorname{gcd}\left(i, k\right), n\right))\right)$$

*Formalization.* `D5/S3/ArithSums/SchulteArbitraryGcdQuotientConvolution.square` (`✓ std3`).

*Citation.* Werner Schulte (2022). *OEIS A350900: gcd-quotient triangle, arbitrary arithmetic weights and row sums*. URL: <https://oeis.org/A350900>.

*Commentary.*

For a function g on N, square(g,n) sums over every ordered pair 1<=i<=n and 1<=k<=n, including the diagonal. For n>0, h=gcd(gcd(i,k),n) is positive and divides g=gcd(i,n). Hence q=g/h is positive, q*h=g, and q divides n. In particular every summand queries a positive argument. The value at n=0 is an empty sum, rather than an additional asserted source case.

**Definition 1.2 (The divisor-totient function).**

$$\forall n \in \mathbb{N},\; \operatorname{H}\left(n\right) = \sum_{e \mid n} \operatorname{ofNat}\left(e\right) \cdot \operatorname{ofNat}\left(\operatorname{phi}\left(e\right)\right)$$

*Formalization.* `D5/S3/ArithSums/SchulteArbitraryGcdQuotientConvolution.H` (`✓ std3`).

*Citation.* Werner Schulte (2022). *OEIS A350900: gcd-quotient triangle, arbitrary arithmetic weights and row sums*. URL: <https://oeis.org/A350900>.

*Commentary.*

H is A057660, interpreted in C. Each divisor e and phi(e) is cast separately before multiplication.

**Definition 1.3 (A zero extension of a positive-domain weight).**

$$\forall f \in \mathbb{P} \to \mathbb{C},\; \forall n \in \mathbb{N},\; \operatorname{positiveLift}\left(f, n\right) = \operatorname{ite}\left(0 < n, \operatorname{f}\left(n\right), 0\right)$$

*Formalization.* `D5/S3/ArithSums/SchulteArbitraryGcdQuotientConvolution.positiveLift` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Werner Schulte (2022). *OEIS A350900: gcd-quotient triangle, arbitrary arithmetic weights and row sums*. URL: <https://oeis.org/A350900>.

*Commentary.*

At n>0 the expression f(n) means f applied to the positive integer with value n. The extension is zero only at n=0. For arbitrary z in C, write extension(f,z) for the function d |-> ite(0<d,f(d),z); it agrees with positiveLift(f) on P.

**Definition 1.4 (The positive-domain square statistic).**

$$\forall f \in \mathbb{P} \to \mathbb{C},\; \forall n \in \mathbb{N},\; \operatorname{A}\left(f, n\right) = \operatorname{square}\left(\operatorname{positiveLift}\left(f\right), n\right)$$

*Formalization.* `D5/S3/ArithSums/SchulteArbitraryGcdQuotientConvolution.A` (`✓ std3`).

*Citation.* Werner Schulte (2022). *OEIS A350900: gcd-quotient triangle, arbitrary arithmetic weights and row sums*. URL: <https://oeis.org/A350900>.

*Commentary.*

A is defined by the original square with a zero extension, independently of its later convolution formula. Every function P -> C is permitted, without reality, positivity, boundedness or multiplicativity assumptions.

**Definition 1.5 (Normalized coprime multiplicativity).**

$$\forall f \in \mathbb{P} \to \mathbb{C},\; \operatorname{PositiveMultiplicative}\left(f\right) \Leftrightarrow \left(\operatorname{f}\left(1\right) = 1 \land \left(\forall a \in \mathbb{P},\; \forall b \in \mathbb{P},\; \operatorname{gcd}\left(a, b\right) = 1 \Rightarrow \operatorname{f}\left(a \cdot b\right) = \operatorname{f}\left(a\right) \cdot \operatorname{f}\left(b\right)\right)\right)$$

*Formalization.* `D5/S3/ArithSums/SchulteArbitraryGcdQuotientConvolution.PositiveMultiplicative` (`✓ std3`).

*Citation.* Werner Schulte (2022). *OEIS A350900: gcd-quotient triangle, arbitrary arithmetic weights and row sums*. URL: <https://oeis.org/A350900>.

*Commentary.*

Multiplicative means f(1)=1 and f(ab)=f(a)f(b) for coprime positive a,b. Complete multiplicativity is not required. Coprimality is that of their underlying natural numbers.

**Theorem 1.6 (The whole arbitrary-function identity and its source clauses).**

$$\forall f \in \mathbb{P} \to \mathbb{C},\; \begin{aligned}(\forall n \in \mathbb{N},\; 0 < n \Rightarrow \operatorname{A}\left(f, n\right) = \sum_{d \mid n} \operatorname{positiveLift}\left(f, d\right) \cdot \operatorname{ofNat}\left(\operatorname{phi}\left(d\right)\right) \cdot \operatorname{H}\left((n) / (d)\right))\\\land (\operatorname{PositiveMultiplicative}\left(f\right) \Rightarrow \left(\operatorname{A}\left(f, 1\right) = 1 \land \left(\forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; 0 < a \Rightarrow \left(0 < b \Rightarrow \left(\operatorname{gcd}\left(a, b\right) = 1 \Rightarrow \operatorname{A}\left(f, a \cdot b\right) = \operatorname{A}\left(f, a\right) \cdot \operatorname{A}\left(f, b\right)\right)\right)\right)\right))\\\land (\forall z \in \mathbb{C},\; \forall n \in \mathbb{N},\; 0 < n \Rightarrow \operatorname{square}\left(\operatorname{extension}\left(f, z\right), n\right) = \operatorname{A}\left(f, n\right))\\\land (\forall n \in \mathbb{N},\; \operatorname{A}\left(idPositive, n\right) = \operatorname{ofNat}\left(\operatorname{rowSum}\left(n\right)\right))\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithSums/SchulteArbitraryGcdQuotientConvolution.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Werner Schulte (2022). *OEIS A350900: gcd-quotient triangle, arbitrary arithmetic weights and row sums*. URL: <https://oeis.org/A350900>.

*Commentary.*

For every f:P -> C, the first clause holds for every n>0. Its right side is the Dirichlet convolution of the pointwise product f(d)*phi(d) with H, not a pointwise product of those two functions. The second clause preserves normalization at one and every coprime positive product. The third permits every zero-extension value z. In the last clause, idPositive is d |-> ofNat(d) on P, and rowSum is the natural-valued SchulteGcdQuotientRowSumConvolution.rowSum, cast into C.

To derive the identity, first replace each interval 1..n by 0..n-1: the endpoint values agree. For fixed i put g=gcd(i,n). Associativity and commutativity of gcd identify the inner argument with g/gcd(g,k). This has period g, and g divides n, so its weighted sum is n/g complete periods. In one period, group by e=gcd(g,k), whose multiplicity is phi(g/e), and reindex d=g/e. The inner sum is therefore (n/g)*Sum_{d|g} phi(d)*f(d). Grouping the outer indices by g gives multiplicity phi(n/g). The complex gcd regrouping uses the real and imaginary parts of the existing RoldanCirculantEnergyP2Q3.sum_gcd_multiplicity theorem.

In arithmetic-function notation let G be the pointwise product of the zero extension of f with phi, B the pointwise product id*phi, and Z the divisor-convolution unit-summand function zeta, equal to one on P and zero at zero. Then H=B*Z and the regrouped square is B*(Z*G)=G*(B*Z), where the displayed stars denote Dirichlet convolution. Expanding the last convolution yields the first clause. Totient, id and zeta are normalized multiplicative functions; pointwise products and Dirichlet convolutions preserve that property, yielding the second clause. Positivity of q proves the third clause. For idPositive its zero extension is exactly ofNat, so distributing natural casts through both finite sums gives the row-sum clause.

The source is the complete arbitrary-function COMMENTS sentence of OEIS A350900 in the revision identified by the source note. The separate triangle-symmetry assertion is outside this statement. The mathematics uses classical gcd-fibre counting and arithmetic-function convolution; it asserts no historical priority. The source note records the uninspected literature whose contents cannot be inferred from bibliographic data.

## References

- Truth anchor: `D5/S3/ArithSums/SchulteArbitraryGcdQuotientConvolution.A`
- Truth anchor: `D5/S3/ArithSums/SchulteArbitraryGcdQuotientConvolution.H`
- Truth anchor: `D5/S3/ArithSums/SchulteArbitraryGcdQuotientConvolution.PositiveMultiplicative`
- Truth anchor: `D5/S3/ArithSums/SchulteArbitraryGcdQuotientConvolution.positiveLift`
- Truth anchor: `D5/S3/ArithSums/SchulteArbitraryGcdQuotientConvolution.result`
- Truth anchor: `D5/S3/ArithSums/SchulteArbitraryGcdQuotientConvolution.square`
- Dependency: [D5/S3/Arith/RoldanCirculantEnergyP2Q3](../Arith/RoldanCirculantEnergyP2Q3.md)
- Dependency: [D5/S3/ArithSums/SchulteGcdQuotientRowSumConvolution](SchulteGcdQuotientRowSumConvolution.md)
