# Even residues of the logarithmic Laplacian

## Abstract

The Rosenzweig-Stanfill residue bracket vanishes for every even index.

**Definition 1.1 (Bounded Bell profiles).**

$$\forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; bellProfiles\left(n, k\right) = filter\left(univ\left(Fin\left(natSub\left(n, k\right) + 1\right) \to Fin\left(k + 1\right)\right), (j:(Fin\left(natSub\left(n, k\right) + 1\right) \to Fin\left(k + 1\right))) \mapsto ((\sum_{i \in Fin\left(natSub\left(n, k\right) + 1\right)} (val\left(j\left(i\right)\right)) = k) \land (\sum_{i \in Fin\left(natSub\left(n, k\right) + 1\right)} ((val\left(i\right) + 1) \cdot (val\left(j\left(i\right)\right))) = n))\right)$$

*Formalization.* `D5/S3/ArithSums/LogLaplacianEvenResidueVanishing.bellProfiles` (`✓ std3`).

*Citation.* Bart Rosenzweig and Jonathan Stanfill (2026). *On the fundamental solutions of two nonlocal parabolic equations related to logarithmic Laplacians*. DOI: [10.48550/arXiv.2606.04225](https://doi.org/10.48550/arXiv.2606.04225). URL: <https://arxiv.org/abs/2606.04225v1>.

*Commentary.*

Equation (1.21), page 6, requires the sum of the profile entries to be k and their weighted sum to be n. Fin(L) means the integers 0 through L-1; val is the natural value of a finite index. natSub denotes truncated natural subtraction. Each entry is at most k because the entries sum to k.

**Definition 1.2 (Partial ordinary Bell polynomials).**

$$\forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; \forall s \in \mathbb{N} \to \mathbb{C},\; bell\left(n, k, s\right) = \sum_{j \in bellProfiles\left(n, k\right)} (((((k)!: \mathbb{C})) / (\prod_{i \in Fin\left(natSub\left(n, k\right) + 1\right)} (((val\left(j\left(i\right)\right))!: \mathbb{C})))) \cdot (\prod_{i \in Fin\left(natSub\left(n, k\right) + 1\right)} ((s\left(val\left(i\right) + 1\right))^{val\left(j\left(i\right)\right)})))$$

*Formalization.* `D5/S3/ArithSums/LogLaplacianEvenResidueVanishing.bell` (`✓ std3`).

*Citation.* Bart Rosenzweig and Jonathan Stanfill (2026). *On the fundamental solutions of two nonlocal parabolic equations related to logarithmic Laplacians*. DOI: [10.48550/arXiv.2606.04225](https://doi.org/10.48550/arXiv.2606.04225). URL: <https://arxiv.org/abs/2606.04225v1>.

*Commentary.*

Equation (1.20), page 6, is the multinomial profile sum for the partial ordinary Bell polynomial. The sequence s has complex values. Every natural coefficient and factorial in complex arithmetic is cast to C.

**Definition 1.3 (Negative integral polylogarithms).**

$$\forall j \in \mathbb{N},\; \forall z \in \mathbb{C},\; negativePolylog\left(j, z\right) = iterate\left(((f:\mathbb{C} \to \mathbb{C}) \mapsto ((x:\mathbb{C}) \mapsto (x) \cdot (deriv\left(f, x\right)))), j, ((x:\mathbb{C}) \mapsto (x) / (1 - x)), z\right)$$

*Formalization.* `D5/S3/ArithSums/LogLaplacianEvenResidueVanishing.negativePolylog` (`✓ std3`).

*Citation.* Bart Rosenzweig and Jonathan Stanfill (2026). *On the fundamental solutions of two nonlocal parabolic equations related to logarithmic Laplacians*. DOI: [10.48550/arXiv.2606.04225](https://doi.org/10.48550/arXiv.2606.04225). URL: <https://arxiv.org/abs/2606.04225v1>.

*Commentary.*

Equation (2.49), page 13, recursively applies the Euler derivative z times deriv(f,z), starting with z/(1-z). iterate applies the displayed operator j times. deriv is the complex derivative, including its totalized value outside differentiability.

**Definition 1.4 (The Bernoulli sequence).**

$$\forall n \in \mathbb{N},\; s2\left(n\right) = ite\left(n = 0, 0, (-((B\left(n\right): \mathbb{C}))) / ((n: \mathbb{C}))\right)$$

*Formalization.* `D5/S3/ArithSums/LogLaplacianEvenResidueVanishing.s2` (`✓ std3`).

*Citation.* Bart Rosenzweig and Jonathan Stanfill (2026). *On the fundamental solutions of two nonlocal parabolic equations related to logarithmic Laplacians*. DOI: [10.48550/arXiv.2606.04225](https://doi.org/10.48550/arXiv.2606.04225). URL: <https://arxiv.org/abs/2606.04225v1>.

*Commentary.*

Theorem 1.5, page 4: "where the sequence S₂ satisfies sₖ⁽²⁾ = −Bₖ/k, k ∈ N." Here B denotes the pinned Bernoulli number with B₁ = −1/2. Only positive entries occur in the Bell sum; the unused zero entry is set to zero. The separately occurring Euler constant s₀⁽²⁾ is not an argument of that sum.

**Definition 1.5 (The residue polynomials).**

$$\forall j \in \mathbb{N},\; \forall t \in \mathbb{C},\; p\left(j, t\right) = \sum_{k \in range\left(j + 1\right)} (((((-(1))^{k}) / (((k)!: \mathbb{C}))) \cdot (bell\left(j, k, s2\right))) \cdot ((t)^{k}))$$

*Formalization.* `D5/S3/ArithSums/LogLaplacianEvenResidueVanishing.p` (`✓ std3`).

*Citation.* Bart Rosenzweig and Jonathan Stanfill (2026). *On the fundamental solutions of two nonlocal parabolic equations related to logarithmic Laplacians*. DOI: [10.48550/arXiv.2606.04225](https://doi.org/10.48550/arXiv.2606.04225). URL: <https://arxiv.org/abs/2606.04225v1>.

*Commentary.*

Definition 1.1, page 2: "Given a sequence of numbers, S, indexed over a set J ⊇ N, we define" the finite sum (1.5). This definition specializes that sum to S₂. The carrier for t and the polynomial value is C; j and k are natural numbers.

**Definition 1.6 (The primary recursive coefficients).**

$$\begin{aligned}\forall a \in \mathbb{R},\; c\left(a, 0\right) = (1) / ((2) \cdot ((sin\left(a\right): \mathbb{C})))\\\forall a \in \mathbb{R},\; \forall j \in \mathbb{N},\; c\left(a, j + 1\right) = ite\left(a = (\pi) / (2), (((2)^{j + 2} - 1) \cdot ((B\left(j + 2\right): \mathbb{C}))) / (((j + 2)!: \mathbb{C})), ((sin\left(a\right): \mathbb{C})) \cdot (((-(((I) \cdot (((cos\left((2) \cdot (a)\right)) / (sin\left((2) \cdot (a)\right)): \mathbb{C})))^{ite\left(Even\left(j + 1\right), 1, 0\right)})) / (((j + 1)!: \mathbb{C}))) \cdot (negativePolylog\left(j + 1, exp\left(((2) \cdot ((a: \mathbb{C}))) \cdot (I)\right)\right)) - \sum_{q \in Fin\left(j\right)} ((c\left(a, val\left(q\right) + 1\right)) \cdot (c\left(a, natSub\left(j, val\left(q\right)\right)\right))))\right)\end{aligned}$$

*Formalization.* `D5/S3/ArithSums/LogLaplacianEvenResidueVanishing.c` (`✓ std3`).

*Citation.* Bart Rosenzweig and Jonathan Stanfill (2026). *On the fundamental solutions of two nonlocal parabolic equations related to logarithmic Laplacians*. DOI: [10.48550/arXiv.2606.04225](https://doi.org/10.48550/arXiv.2606.04225). URL: <https://arxiv.org/abs/2606.04225v1>.

*Commentary.*

Equation (1.14), page 4, defines the primary array, including its separate Bernoulli value at a = pi/2. Here a encodes alpha. ite selects its second argument when its first argument holds and its third otherwise. The exponent ite(Even(j+1),1,0) is exactly (1+(-1)^(j+1))/2. The finite index q in Fin(j) replaces the paper's index from 1 through j by val(q)+1. The real sine and the real ratio cos(2a)/sin(2a) are embedded into C; exp is the complex exponential after a is embedded into C.

**Definition 1.7 (The finite difference array).**

$$\forall a \in \mathbb{R},\; \forall j \in \mathbb{N},\; \forall k \in \mathbb{N},\; d\left(a, j, k\right) = ite\left(k = 0, ite\left(j = 0, 1, 0\right), ite\left(k \le j, ((1) / ((((2) \cdot (j))!: \mathbb{C}))) \cdot (\sum_{ell \in Icc\left(k, j\right)} ((((((binomial\left(natSub\left(ell, 1\right), natSub\left(k, 1\right)\right): \mathbb{C})) \cdot ((-(1))^{natSub\left(ell, k\right)})) / ((4)^{ell})) / (((sin\left(a\right): \mathbb{C}))^{(2) \cdot (ell)})) \cdot (\sum_{v \in range\left((2) \cdot (ell) + 1\right)} ((((-(1))^{v}) \cdot ((binomial\left((2) \cdot (ell), v\right): \mathbb{C}))) \cdot (((ell: \mathbb{C}) - (v: \mathbb{C}))^{(2) \cdot (j)}))))), 0\right)\right)$$

*Formalization.* `D5/S3/ArithSums/LogLaplacianEvenResidueVanishing.d` (`✓ std3`).

*Citation.* Bart Rosenzweig and Jonathan Stanfill (2026). *On the fundamental solutions of two nonlocal parabolic equations related to logarithmic Laplacians*. DOI: [10.48550/arXiv.2606.04225](https://doi.org/10.48550/arXiv.2606.04225). URL: <https://arxiv.org/abs/2606.04225v1>.

*Commentary.*

Equation (1.14), page 4, defines d(j,0) as the Kronecker delta and gives the displayed finite sum when j >= k >= 1. The extension for k > j is zero and is never used by the residue sums. All quotients here are complex division; powers retain natural exponents. In the innermost factor ell-v is complex subtraction after both natural indices are cast, so it can be negative; natSub is used only for the natural binomial and exponent indices.

**Definition 1.8 (The coefficient convolution).**

$$\forall a \in \mathbb{R},\; \forall i \in \mathbb{N},\; \forall k \in \mathbb{N},\; b\left(a, i, k\right) = \sum_{j \in range\left(natDiv\left(i, 2\right) + 1\right)} ((d\left(a, k + j, k\right)) \cdot (c\left(a, natSub\left(i, (2) \cdot (j)\right)\right)))$$

*Formalization.* `D5/S3/ArithSums/LogLaplacianEvenResidueVanishing.b` (`✓ std3`).

*Citation.* Bart Rosenzweig and Jonathan Stanfill (2026). *On the fundamental solutions of two nonlocal parabolic equations related to logarithmic Laplacians*. DOI: [10.48550/arXiv.2606.04225](https://doi.org/10.48550/arXiv.2606.04225). URL: <https://arxiv.org/abs/2606.04225v1>.

*Commentary.*

Equation (1.14), page 4, convolves d(k+j,k) with c(i-2j). natDiv(i,2) means floor(i/2), using natural integer division.

**Definition 1.9 (Squared Pochhammer weights).**

$$\forall k \in \mathbb{N},\; w\left(k\right) = ((\prod_{q \in range\left(k\right)} ((1) / (2) + (q: \mathbb{C})))^{2}) / ((((k)!: \mathbb{C}))^{2})$$

*Formalization.* `D5/S3/ArithSums/LogLaplacianEvenResidueVanishing.w` (`✓ std3`).

*Citation.* Bart Rosenzweig and Jonathan Stanfill (2026). *On the fundamental solutions of two nonlocal parabolic equations related to logarithmic Laplacians*. DOI: [10.48550/arXiv.2606.04225](https://doi.org/10.48550/arXiv.2606.04225). URL: <https://arxiv.org/abs/2606.04225v1>.

*Commentary.*

The weight in (1.13), page 4, is ((1/2)_k)^2/(k!)^2. The Pochhammer factor is the product over q from 0 through k-1; the empty product is one.

**Definition 1.10 (The inner residue sum).**

$$\forall a \in \mathbb{R},\; \forall ell \in \mathbb{N},\; A\left(a, ell\right) = \sum_{k \in range\left(natDiv\left(ell, 2\right) + 1\right)} ((w\left(k\right)) \cdot (b\left(a, natSub\left(ell, (2) \cdot (k)\right), k\right)))$$

*Formalization.* `D5/S3/ArithSums/LogLaplacianEvenResidueVanishing.A` (`✓ std3`).

*Citation.* Bart Rosenzweig and Jonathan Stanfill (2026). *On the fundamental solutions of two nonlocal parabolic equations related to logarithmic Laplacians*. DOI: [10.48550/arXiv.2606.04225](https://doi.org/10.48550/arXiv.2606.04225). URL: <https://arxiv.org/abs/2606.04225v1>.

*Commentary.*

This notation abbreviates exactly the inner finite sum of (1.13), page 4. The upper bound natDiv(ell,2) is floor(ell/2).

**Definition 1.11 (The bracket in (1.13)).**

$$\forall m \in \mathbb{N},\; \forall a \in \mathbb{R},\; paperBracket\left(m, a\right) = \sum_{ell \in Icc\left(1, m + 1\right)} (((((-(1))^{ell}) \cdot (((ell)!: \mathbb{C}))) \cdot (p\left(natSub\left(m + 1, ell\right), -((m: \mathbb{C}))\right))) \cdot (A\left(a, ell\right))) + ((1) / (2)) \cdot (\sum_{ell \in range\left(m + 1\right)} (((((-(1))^{ell}) \cdot (((ell)!: \mathbb{C}))) \cdot (p\left(natSub\left(m, ell\right), -((m: \mathbb{C}))\right))) \cdot (A\left(a, ell\right))))$$

*Formalization.* `D5/S3/ArithSums/LogLaplacianEvenResidueVanishing.paperBracket` (`✓ std3`).

*Citation.* Bart Rosenzweig and Jonathan Stanfill (2026). *On the fundamental solutions of two nonlocal parabolic equations related to logarithmic Laplacians*. DOI: [10.48550/arXiv.2606.04225](https://doi.org/10.48550/arXiv.2606.04225). URL: <https://arxiv.org/abs/2606.04225v1>.

*Commentary.*

The two finite sums are the bracket in (1.13), page 4. The first interval includes 1 and m+1, and range(m+1) includes 0 through m. The external factor 2 exp(gamma_E m)/pi is nonzero and therefore has no effect on vanishing.

**Definition 1.12 (Open Problem 1.6(iv)).**

$$claim = (\forall m \in \mathbb{N},\; (Even\left(m\right)) \Rightarrow (\forall a \in \mathbb{R},\; (0 < a) \Rightarrow ((a < \pi) \Rightarrow (paperBracket\left(m, a\right) = 0))))$$

*Formalization.* `D5/S3/ArithSums/LogLaplacianEvenResidueVanishing.claim` (`✓ std3`).

*Citation.* Bart Rosenzweig and Jonathan Stanfill (2026). *On the fundamental solutions of two nonlocal parabolic equations related to logarithmic Laplacians*. DOI: [10.48550/arXiv.2606.04225](https://doi.org/10.48550/arXiv.2606.04225). URL: <https://arxiv.org/abs/2606.04225v1>.

*Commentary.*

Open Problem 1.6, page 4: "Consider the notation of Theorem 1.5. Then the following are conjectured to be true:" Clause (iv): "For every α ∈ (0, π), (1.13) is equal to zero whenever m ≥ 0 is even." The encoding uses m : N, so m >= 0 includes zero, and a : R for α. paperBracket is the bracket of (1.13), with its literal recursive c-array and partial ordinary Bell polynomial definitions.

**Theorem 1.13 (Vanishing for every even index).**

$$\forall m \in \mathbb{N},\; (Even\left(m\right)) \Rightarrow (\forall a \in \mathbb{R},\; (0 < a) \Rightarrow ((a < \pi) \Rightarrow (paperBracket\left(m, a\right) = 0)))$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithSums/LogLaplacianEvenResidueVanishing.result` (`✓ std3`). ∎

*Resolves.* `Problems/rosenzweig-stanfill-2026-open-problem-1-6-even-residues` (proved) by `D5/S3/ArithSums/LogLaplacianEvenResidueVanishing.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"rosenzweig-stanfill-2026-open-problem-1-6-even-residues","declaration_gid":"D5/S3/ArithSums/LogLaplacianEvenResidueVanishing.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Bart Rosenzweig and Jonathan Stanfill (2026). *On the fundamental solutions of two nonlocal parabolic equations related to logarithmic Laplacians*. DOI: [10.48550/arXiv.2606.04225](https://doi.org/10.48550/arXiv.2606.04225). URL: <https://arxiv.org/abs/2606.04225v1>.

*Commentary.*

Centering the primary coefficient series by exp(-s/2) makes it even: its square is the inverse of 2 cosh(s)-2 cos(2a). The b-array convolution multiplies that series by an even series. Bernoulli translation to 1/2 then makes the residue functional annihilate the odd derivative for every even m. These are identities of formal power-series coefficients; no analytic convergence hypothesis is needed.

## References

- Truth anchor: `D5/S3/ArithSums/LogLaplacianEvenResidueVanishing.A`
- Truth anchor: `D5/S3/ArithSums/LogLaplacianEvenResidueVanishing.b`
- Truth anchor: `D5/S3/ArithSums/LogLaplacianEvenResidueVanishing.bell`
- Truth anchor: `D5/S3/ArithSums/LogLaplacianEvenResidueVanishing.bellProfiles`
- Truth anchor: `D5/S3/ArithSums/LogLaplacianEvenResidueVanishing.c`
- Truth anchor: `D5/S3/ArithSums/LogLaplacianEvenResidueVanishing.claim`
- Truth anchor: `D5/S3/ArithSums/LogLaplacianEvenResidueVanishing.d`
- Truth anchor: `D5/S3/ArithSums/LogLaplacianEvenResidueVanishing.negativePolylog`
- Truth anchor: `D5/S3/ArithSums/LogLaplacianEvenResidueVanishing.p`
- Truth anchor: `D5/S3/ArithSums/LogLaplacianEvenResidueVanishing.paperBracket`
- Truth anchor: `D5/S3/ArithSums/LogLaplacianEvenResidueVanishing.result`
- Truth anchor: `D5/S3/ArithSums/LogLaplacianEvenResidueVanishing.s2`
- Truth anchor: `D5/S3/ArithSums/LogLaplacianEvenResidueVanishing.w`
- Dependency: [D5/S1/Recurrence/Invariants/CompositionalIterateCongruence](../../S1/Recurrence/Invariants/CompositionalIterateCongruence.md)
- Dependency: [D5/S1/Recurrence/Parity/StirlingPowerFactorialPrimePeriod](../../S1/Recurrence/Parity/StirlingPowerFactorialPrimePeriod.md)
