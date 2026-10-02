# Nonvanishing Bell values for the logarithmic Laplacian

## Abstract

The Bell polynomial values in Rosenzweig and Stanfill's Open Problem 1.3 are nonzero at every positive natural index.

**Definition 1.1 (Natural Bell profiles).**

$$\forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; BellProfile\left(n, k\right) = \{r : Fin\left(n - k + 1\right) \to \mathbb{N} \mid (\sum_{i: Fin\left(n - k + 1\right)} r\left(i\right) = k) \land (\sum_{i: Fin\left(n - k + 1\right)} (val\left(i\right) + 1) \cdot r\left(i\right) = n)\}$$

*Formalization.* `D5/S3/ArithSums/LogLaplacianBellNonvanishing.BellProfile` (`✓ std3`).

*Citation.* B. Rosenzweig; J. Stanfill (2026). *On the fundamental solutions of two nonlocal parabolic equations related to logarithmic Laplacians*. DOI: [10.48550/arXiv.2606.04225](https://doi.org/10.48550/arXiv.2606.04225). URL: <https://arxiv.org/abs/2606.04225>.

*Commentary.*

Section 1.2, page 6: “with the sum being over all sequences $j_{1},j_{2},...,j_{n - k + 1}$ of nonnegative integers such that $j_{1}+j_{2}+...+j_{n - k + 1} = k,\qquad j_{1}+2j_{2}+...+(n - k + 1)j_{n - k + 1} = n$.”

BellProfile is the subtype of natural-valued functions with exactly the two source constraints. The zero-based index i corresponds to the source index i+1. The subtraction n-k is truncated natural subtraction, Nat.sub n k; Fin(L) is the type of natural indices smaller than L and val(i) is its natural value.

**Definition 1.2 (The partial ordinary Bell polynomial).**

$$\forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; \forall s \in \mathbb{N} \to \mathbb{Q},\; bellOrdinary\left(n, k, s\right) = \sum_{r: BellProfile\left(n, k\right)} \frac{((k)!: \mathbb{Q})}{\prod_{i: Fin\left(n - k + 1\right)} ((val\left(r\right)\left(i\right))!: \mathbb{Q})} \cdot \prod_{i: Fin\left(n - k + 1\right)} s\left(val\left(i\right) + 1\right)^{val\left(r\right)\left(i\right)}$$

*Formalization.* `D5/S3/ArithSums/LogLaplacianBellNonvanishing.bellOrdinary` (`✓ std3`).

*Citation.* B. Rosenzweig; J. Stanfill (2026). *On the fundamental solutions of two nonlocal parabolic equations related to logarithmic Laplacians*. DOI: [10.48550/arXiv.2606.04225](https://doi.org/10.48550/arXiv.2606.04225). URL: <https://arxiv.org/abs/2606.04225>.

*Commentary.*

Section 1.2, page 6: “$\widehat{B}_{n,k}$ denotes the partial ordinary Bell polynomials [4, p. 136] $\widehat{B}_{n,k}(z_{1},z_{2},...,z_{n - k + 1}) = \sum \frac{k!}{j_{1}!j_{2}!...j_{n - k + 1}!} z_{1}^{j_{1}}z_{2}^{j_{2}}...z_{n - k + 1}^{j_{n - k + 1}}$,”

This is the defining sum (1.20), with rational coefficients. The function val(r) is the underlying natural sequence of the subtype r; every factorial is formed in N before the displayed cast to Q. Each entry is at most k, so these profiles form a finite type.

**Definition 1.3 (The polynomial of Definition 1.1).**

$$\forall n \in \mathbb{N},\; \forall s \in \mathbb{N} \to \mathbb{Q},\; \forall t \in \mathbb{Q},\; pBell\left(n, s, t\right) = \sum_{k = 0}^{n} \frac{(-(1: \mathbb{Q}))^{k}}{((k)!: \mathbb{Q})} \cdot bellOrdinary\left(n, k, s\right) \cdot t^{k}$$

*Formalization.* `D5/S3/ArithSums/LogLaplacianBellNonvanishing.pBell` (`✓ std3`).

*Citation.* B. Rosenzweig; J. Stanfill (2026). *On the fundamental solutions of two nonlocal parabolic equations related to logarithmic Laplacians*. DOI: [10.48550/arXiv.2606.04225](https://doi.org/10.48550/arXiv.2606.04225). URL: <https://arxiv.org/abs/2606.04225>.

*Commentary.*

Definition 1.1, page 2: “Given a sequence of numbers, $S$, indexed over a set J⊇ℕ, we define $p_{j,S}(t):=\sum_{k=0}^{j} \frac{(-1)^{k}}{k!} \widehat{B}_{j,k}(s_{1},...,s_{j - k + 1}) t^{k}=\frac{(-1)^{j}}{j!} det \mathcal{N}_{j,S}(t),\qquad j \in \mathbb{N}_{0}$, where $\widehat{B}_{n,k}$ denote the partial ordinary Bell polynomials (see Section 1.2) and the $j \times j$ lower Hessenberg matrix $\mathcal{N}_{j,S}(t)$ consists of $s_{1} t$ on the diagonal, $(k + 1)s_{k + 1} t$ on the $k$th subdiagonal, the sequence $1,2,...,j - 1$ on the first superdiagonal, and zeros on all other superdiagonals (cf. [19, Eq. (5.3)]):”

pBell uses the first expression of (1.5), with n representing j, s a rational sequence and t rational. The determinant expression is not used; the displayed sum includes both endpoints k=0 and k=n.

**Definition 1.4 (The sequence of equation (1.8)).**

$$\forall k \in \mathbb{N},\; \left(S_{1}\right)\left(k\right) = \frac{((1: \mathbb{Q}) - (2: \mathbb{Q})^{(1: \mathbb{Z}) - (k: \mathbb{Z})}) \cdot ((2: \mathbb{Q}) \cdot bernoulli\left(k\right))}{(k: \mathbb{Q})}$$

*Formalization.* `D5/S3/ArithSums/LogLaplacianBellNonvanishing.S1` (`✓ std3`).

*Citation.* B. Rosenzweig; J. Stanfill (2026). *On the fundamental solutions of two nonlocal parabolic equations related to logarithmic Laplacians*. DOI: [10.48550/arXiv.2606.04225](https://doi.org/10.48550/arXiv.2606.04225). URL: <https://arxiv.org/abs/2606.04225>.

*Commentary.*

Equation (1.8), page 2: “$s_{k}^{(1)}=(1 - 2^{1 - k}) \cdot \frac{2 \cdot B_{k}}{k}=-\frac{2}{k} B_{k}(\frac{1}{2}),\qquad k \in \mathbb{N}$.” Section 1.2, page 5: “$B_{k}$ denotes the Bernoulli numbers with the convention $B_{1} = -\frac{1}{2}$;”.

The first expression of (1.8) defines S1, with the exponent 1-k formed in Z and rational division. Mathlib bernoulli has the convention B1=-1/2. The paper uses positive k; the extension to k=0 is zero and never enters a Bell summand.

**Definition 1.5 (Open Problem 1.3).**

$$claim \Leftrightarrow (\forall m \in \mathbb{N},\; (1 \le m) \Rightarrow (pBell\left(2 \cdot m, S_{1}, \frac{(1: \mathbb{Q})}{(2: \mathbb{Q})} - (m: \mathbb{Q})\right) \ne (0: \mathbb{Q})))$$

*Formalization.* `D5/S3/ArithSums/LogLaplacianBellNonvanishing.claim` (`✓ std3`).

*Citation.* B. Rosenzweig; J. Stanfill (2026). *On the fundamental solutions of two nonlocal parabolic equations related to logarithmic Laplacians*. DOI: [10.48550/arXiv.2606.04225](https://doi.org/10.48550/arXiv.2606.04225). URL: <https://arxiv.org/abs/2606.04225>.

*Commentary.*

Open Problem 1.3, page 2: “Show that $p_{2m,S_{1}}(\frac{1}{2} - m) \ne 0$ for all $m \in \mathbb{N}$ where the sequence $S_{1}$ satisfies (1.8).”

The paper's N is the positive naturals, encoded as m:N with 1<=m. pBell, bellOrdinary and S1 are the defining expressions of (1.5), (1.20)-(1.21) and (1.8); m is cast to Q at the evaluation point. Thus claim is the universal nonvanishing assertion.

**Theorem 1.6 (Nonvanishing at every positive index).**

$$\forall m \in \mathbb{N},\; (1 \le m) \Rightarrow (pBell\left(2 \cdot m, S_{1}, \frac{(1: \mathbb{Q})}{(2: \mathbb{Q})} - (m: \mathbb{Q})\right) \ne (0: \mathbb{Q}))$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithSums/LogLaplacianBellNonvanishing.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* B. Rosenzweig; J. Stanfill (2026). *On the fundamental solutions of two nonlocal parabolic equations related to logarithmic Laplacians*. DOI: [10.48550/arXiv.2606.04225](https://doi.org/10.48550/arXiv.2606.04225). URL: <https://arxiv.org/abs/2606.04225>.

*Commentary.*

Put a=(2m-1)/2 and b_r=24^r a S1(2r). The von Staudt-Clausen theorem gives v2(B_{2r})=-1, hence v2(b_r)=r-1-v2(r)>=0 for r>=1 and v2(b_1)=0. Odd-index coefficients vanish. After multiplying the Bell value by 24^m m!, a nonzero profile contributes (m!/product j_i!) product b_{i/2}^{j_i}. A positive count at an index i>=4 gives strictly positive valuation, using v2((2j)!)=v2(j!)+j and product-factorial divisibility. The only remaining profile has j_2=m and all other counts zero; its contribution b_1^m has valuation zero. The ultrametric inequality therefore makes the scaled sum nonzero with valuation zero, proving the assertion. The identity scaled_pBell links the defining Bell sum to the finite-profile sum; scaledEntry_pos_val supplies the strict positive valuation of each nonprincipal even profile.

## References

- Truth anchor: `D5/S3/ArithSums/LogLaplacianBellNonvanishing.BellProfile`
- Truth anchor: `D5/S3/ArithSums/LogLaplacianBellNonvanishing.S1`
- Truth anchor: `D5/S3/ArithSums/LogLaplacianBellNonvanishing.bellOrdinary`
- Truth anchor: `D5/S3/ArithSums/LogLaplacianBellNonvanishing.claim`
- Truth anchor: `D5/S3/ArithSums/LogLaplacianBellNonvanishing.pBell`
- Truth anchor: `D5/S3/ArithSums/LogLaplacianBellNonvanishing.result`
