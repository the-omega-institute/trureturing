# Six-support quotient, balanced threshold, endpoint applications and integer finiteness

## Abstract

The six-support weighted quotient, its symmetric representative, sharp balanced threshold, global endpoint spectrum, fixed-real-gap endpoint application and integer finiteness.

The support order for C is 1,2,3,12,13,23. The public source is paper/core/body.tex in the-omega-institute/ideal-intersection-laplacian at commit b93becea662a746badeadba42fdc3d3eb3db9382. Its quotient and energy occur on lines 574–600 and 774–784; its balanced sharpness proposition occurs on lines 114–145. The matrix model and balanced statement are attributed to that source. The Lean proofs and this exposition are independently authored; no novelty or graph-integrality classification is asserted.

**Definition 1.1 (The literal nonsymmetric quotient).**

$$\forall a \in \mathrm{Real},\; \forall b \in \mathrm{Real},\; \forall c \in \mathrm{Real},\; \operatorname{quotient}\left(a, b, c\right) = \begin{pmatrix}b + c + b \cdot c&-b&-c&0&0&-\left(b \cdot c\right)\\-a&a + c + a \cdot c&-c&0&-\left(a \cdot c\right)&0\\-a&-b&a + b + a \cdot b&-\left(a \cdot b\right)&0&0\\0&0&-c&c&0&0\\0&-b&0&0&b&0\\-a&0&0&0&0&a\end{pmatrix}$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/SixSupportLaplacianLowRoot.quotient` (`✓ std3`).

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

Rows and columns have the stated original support order. Multiplying on the left by diag(a,b,c,ab,ac,bc) makes the matrix symmetric.

**Definition 1.2 (Support weights).**

$$\forall a \in \mathrm{Real},\; \forall b \in \mathrm{Real},\; \forall c \in \mathrm{Real},\; \operatorname{weights}\left(a, b, c\right) = [a,b,c,a \cdot b,a \cdot c,b \cdot c]$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/SixSupportLaplacianLowRoot.weights` (`✓ std3`).

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

The final three weights are the pair-support class sizes.

**Definition 1.3 (Paired-coordinate reversal).**

$$\operatorname{supportPermutation} = \operatorname{permutation}\left([0,1,2,5,4,3]\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/SixSupportLaplacianLowRoot.supportPermutation` (`✓ std3`).

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

This involution changes the support order to 1,2,3,23,13,12.

**Definition 1.4 (Square-root diagonal).**

$$\forall a \in \mathrm{Real},\; \forall b \in \mathrm{Real},\; \forall c \in \mathrm{Real},\; \operatorname{rootWeights}\left(a, b, c\right) = [\operatorname{sqrt}\left(a\right),\operatorname{sqrt}\left(b\right),\operatorname{sqrt}\left(c\right),\operatorname{sqrt}\left(b\right) \cdot \operatorname{sqrt}\left(c\right),\operatorname{sqrt}\left(a\right) \cdot \operatorname{sqrt}\left(c\right),\operatorname{sqrt}\left(a\right) \cdot \operatorname{sqrt}\left(b\right)]$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/SixSupportLaplacianLowRoot.rootWeights` (`✓ std3`).

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

All six entries are positive when a,b,c are positive. Their squares are the reordered support weights.

**Definition 1.5 (The symmetric representative).**

$$\forall a \in \mathrm{Real},\; \forall b \in \mathrm{Real},\; \forall c \in \mathrm{Real},\; \operatorname{symmetric}\left(a, b, c\right) = \begin{pmatrix}b + c + b \cdot c&-\left(\operatorname{sqrt}\left(a\right) \cdot \operatorname{sqrt}\left(b\right)\right)&-\left(\operatorname{sqrt}\left(a\right) \cdot \operatorname{sqrt}\left(c\right)\right)&-\left(\operatorname{sqrt}\left(a\right) \cdot \operatorname{sqrt}\left(b\right) \cdot \operatorname{sqrt}\left(c\right)\right)&0&0\\-\left(\operatorname{sqrt}\left(a\right) \cdot \operatorname{sqrt}\left(b\right)\right)&a + c + a \cdot c&-\left(\operatorname{sqrt}\left(b\right) \cdot \operatorname{sqrt}\left(c\right)\right)&0&-\left(\operatorname{sqrt}\left(a\right) \cdot \operatorname{sqrt}\left(b\right) \cdot \operatorname{sqrt}\left(c\right)\right)&0\\-\left(\operatorname{sqrt}\left(a\right) \cdot \operatorname{sqrt}\left(c\right)\right)&-\left(\operatorname{sqrt}\left(b\right) \cdot \operatorname{sqrt}\left(c\right)\right)&a + b + a \cdot b&0&0&-\left(\operatorname{sqrt}\left(a\right) \cdot \operatorname{sqrt}\left(b\right) \cdot \operatorname{sqrt}\left(c\right)\right)\\-\left(\operatorname{sqrt}\left(a\right) \cdot \operatorname{sqrt}\left(b\right) \cdot \operatorname{sqrt}\left(c\right)\right)&0&0&a&0&0\\0&-\left(\operatorname{sqrt}\left(a\right) \cdot \operatorname{sqrt}\left(b\right) \cdot \operatorname{sqrt}\left(c\right)\right)&0&0&b&0\\0&0&-\left(\operatorname{sqrt}\left(a\right) \cdot \operatorname{sqrt}\left(b\right) \cdot \operatorname{sqrt}\left(c\right)\right)&0&0&c\end{pmatrix}$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/SixSupportLaplacianLowRoot.symmetric` (`✓ std3`).

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

The paired diagonal is a,b,c; each singleton is coupled to its complementary pair by minus sqrt(a)sqrt(b)sqrt(c), equal to minus sqrt(abc) at positive parameters.

**Definition 1.6 (Return to the actual quotient).**

$$\forall a \in \mathrm{Real},\; \forall b \in \mathrm{Real},\; \forall c \in \mathrm{Real},\; \forall z \in \operatorname{Fin}\left(6\right) \to \mathrm{Real},\; \forall i \in \operatorname{Fin}\left(6\right),\; \operatorname{toQuotientVector}\left(a, b, c, z\right)\left(i\right) = \frac{z\left(\operatorname{inverse}\left(\operatorname{supportPermutation}, i\right)\right)}{\operatorname{rootWeights}\left(a, b, c\right)\left(\operatorname{inverse}\left(\operatorname{supportPermutation}, i\right)\right)}$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/SixSupportLaplacianLowRoot.toQuotientVector` (`✓ std3`).

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

The inverse coordinate permutation and positive inverse diagonal preserve nonzero vectors and transport the same real eigenvalue to C.

**Theorem 1.7 (Weighted energy, kernel and similarity).**

$$\forall a \in \mathrm{Real},\; \forall b \in \mathrm{Real},\; \forall c \in \mathrm{Real},\; 0 < a \Rightarrow \left(0 < b \Rightarrow \left(0 < c \Rightarrow \left(\left(\left(\forall z \in \operatorname{Fin}\left(6\right) \to \mathrm{Real},\; \operatorname{dotProduct}\left(\lambda i : \operatorname{Fin}\left(6\right) \mapsto \operatorname{weights}\left(a, b, c\right)\left(i\right) \cdot z\left(i\right), \operatorname{mulVec}\left(\operatorname{quotient}\left(a, b, c\right), z\right)\right) = a \cdot b \cdot \left(z\left(0\right) - z\left(1\right)\right)^{2} + a \cdot c \cdot \left(z\left(0\right) - z\left(2\right)\right)^{2} + b \cdot c \cdot \left(z\left(1\right) - z\left(2\right)\right)^{2} + a \cdot b \cdot c \cdot \left(\left(z\left(0\right) - z\left(5\right)\right)^{2} + \left(z\left(1\right) - z\left(4\right)\right)^{2} + \left(z\left(2\right) - z\left(3\right)\right)^{2}\right)\right) \land \left(\left(\forall z \in \operatorname{Fin}\left(6\right) \to \mathrm{Real},\; \operatorname{mulVec}\left(\operatorname{quotient}\left(a, b, c\right), z\right) = 0 \Leftrightarrow \left(\exists t \in \mathrm{Real},\; z = \lambda i : \operatorname{Fin}\left(6\right) \mapsto t\right)\right) \land \left(\operatorname{mulVec}\left(\operatorname{quotient}\left(a, b, c\right), \lambda i : \operatorname{Fin}\left(6\right) \mapsto 1\right) = 0 \land \operatorname{vecMul}\left(\operatorname{weights}\left(a, b, c\right), \operatorname{quotient}\left(a, b, c\right)\right) = 0\right)\right)\right) \land \left(\operatorname{PosSemidef}\left(\operatorname{symmetric}\left(a, b, c\right)\right) \land \left(\operatorname{symmetric}\left(a, b, c\right) = \operatorname{diagonal}\left(\operatorname{rootWeights}\left(a, b, c\right)\right) \cdot \operatorname{submatrix}\left(\operatorname{quotient}\left(a, b, c\right), \operatorname{supportPermutation}, \operatorname{supportPermutation}\right) \cdot \operatorname{diagonal}\left(\lambda i : \operatorname{Fin}\left(6\right) \mapsto \operatorname{inverse}\left(\operatorname{rootWeights}\left(a, b, c\right)\left(i\right)\right)\right) \land \left(\forall e \in \mathrm{Real},\; \forall z \in \operatorname{Fin}\left(6\right) \to \mathrm{Real},\; z \ne 0 \Rightarrow \left(\operatorname{mulVec}\left(\operatorname{symmetric}\left(a, b, c\right), z\right) = e \cdot z \Rightarrow \left(\operatorname{toQuotientVector}\left(a, b, c, z\right) \ne 0 \land \operatorname{mulVec}\left(\operatorname{quotient}\left(a, b, c\right), \operatorname{toQuotientVector}\left(a, b, c, z\right)\right) = e \cdot \operatorname{toQuotientVector}\left(a, b, c, z\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/SixSupportLaplacianLowRoot.quotient_geometry` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

The energy is a sum over the singleton triangle and the three complementary-pair edges. Positivity forces all six coordinates of a zero-kernel vector to agree. The symmetric form is also a sum of six real squares. The exact similarity and eigenvector transport concern C itself.

**Theorem 1.8 (A negative plane at a small second weight).**

$$\forall a \in \mathrm{Real},\; \forall b \in \mathrm{Real},\; \forall c \in \mathrm{Real},\; 0 < a \Rightarrow \left(0 < b \Rightarrow \left(0 < c \Rightarrow \left(a \le b \Rightarrow \left(b \le 3 \Rightarrow \left(\exists t \in \mathrm{Real},\; \operatorname{Injective}\left(\lambda u : \operatorname{Fin}\left(2\right) \to \mathrm{Real} \mapsto [u\left(0\right),u\left(1\right),0,t \cdot u\left(0\right),t \cdot u\left(1\right),0]\right) \land \left(\forall u \in \operatorname{Fin}\left(2\right) \to \mathrm{Real},\; u \ne 0 \Rightarrow \operatorname{dotProduct}\left([u\left(0\right),u\left(1\right),0,t \cdot u\left(0\right),t \cdot u\left(1\right),0], \operatorname{mulVec}\left(\operatorname{symmetric}\left(a, b, c\right) - 3 \cdot 1, [u\left(0\right),u\left(1\right),0,t \cdot u\left(0\right),t \cdot u\left(1\right),0]\right)\right) < 0\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/SixSupportLaplacianLowRoot.small_second_negative_plane` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

For positive a,b,c with a at most b and b at most three, put p=sqrt(a)sqrt(b)sqrt(c), A=b+c+bc, B=a+c+ac, and t=(A+B+sqrt(a)sqrt(b)+1)/p. The plane consists of (u,v,0,tu,tv,0) in reordered coordinates. Its first two coordinates make the parametrization injective. The two paired diagonal contributions are nonpositive, and the singleton cross term is controlled by the square of u+v. The quadratic form of the symmetric matrix minus three times the identity is strictly negative on every nonzero vector of this plane. No division by a−3 or b−3 occurs, so their equality boundaries are included.

**Theorem 1.9 (Low eigenvalue for every positive real triple).**

$$\forall a \in \mathrm{Real},\; \forall b \in \mathrm{Real},\; \forall c \in \mathrm{Real},\; 0 < a \Rightarrow \left(a \le b \Rightarrow \left(b \le c \Rightarrow \left(\exists e \in \mathrm{Real},\; 0 < e \land \left(e < 3 \land \left(\exists z \in \operatorname{Fin}\left(6\right) \to \mathrm{Real},\; z \ne 0 \land \operatorname{mulVec}\left(\operatorname{quotient}\left(a, b, c\right), z\right) = e \cdot z\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/SixSupportLaplacianLowRoot.positive_real_low_eigenvalue` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

For balanced weights at least one, the proof directly consumes the balanced threshold theorem and its actual quotient eigenpair. For the remaining triples it uses three explicit negative planes for the symmetric matrix shifted by three. When b is at most three, the small-second plane applies. When a is at most three but b is greater than three, the paired b and c coordinates are eliminated and the positive singleton diagonal completes a square; this includes a equal to three. When a is greater than three, the source comparison matrix is nonpositive on vectors (x,sqrt(b)y,sqrt(c)y): its form is minus (b+c)/2 times (x+2sqrt(a)y) squared minus 3/(2a) times (2bc-a(b+c))x squared. Ordering makes the latter coefficient nonnegative, including equal parameters. The positive Schur correction makes the lifted plane strictly negative. This explicit plane is a repository synthesis of the source geometry. A vector in each plane is chosen orthogonal to the simple zero kernel. The real Hermitian spectral expansion then forces a positive eigenvalue below three. The proved similarity transports its nonzero real eigenvector to the actual nonsymmetric quotient C. No ordered-eigenvalue convention or unproved inertia count is assumed.

**Definition 1.10 (The balanced smaller root).**

$$\forall m \in \mathrm{Real},\; \operatorname{balancedLow}\left(m\right) = \frac{m^{2} + 4 \cdot m - m \cdot \operatorname{sqrt}\left(\left(m + 4\right)^{2} - 12\right)}{2}$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/SixSupportLaplacianLowRoot.balancedLow` (`✓ std3`).

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

The discriminant is strictly positive for m at least one.

**Theorem 1.11 (Balanced smallest positive eigenvalue and sharp threshold).**

$$\left(\forall m \in \mathrm{Real},\; 1 \le m \Rightarrow \left(\left(\exists z \in \operatorname{Fin}\left(6\right) \to \mathrm{Real},\; z \ne 0 \land \operatorname{mulVec}\left(\operatorname{quotient}\left(m, m, m\right), z\right) = \operatorname{balancedLow}\left(m\right) \cdot z\right) \land \left(0 < \operatorname{balancedLow}\left(m\right) \land \left(\operatorname{balancedLow}\left(m\right) < m \land \left(\frac{3 \cdot m}{m + 4} < \operatorname{balancedLow}\left(m\right) \land \left(\operatorname{balancedLow}\left(m\right) < 3 \land \left(\operatorname{balancedLow}\left(m\right) = \frac{6 \cdot m}{m + 4 + \operatorname{sqrt}\left(\left(m + 4\right)^{2} - 12\right)} \land \left(\left(\forall e \in \mathrm{Real},\; 0 < e \Rightarrow \left(\forall z \in \operatorname{Fin}\left(6\right) \to \mathrm{Real},\; z \ne 0 \Rightarrow \left(\operatorname{mulVec}\left(\operatorname{quotient}\left(m, m, m\right), z\right) = e \cdot z \Rightarrow \operatorname{balancedLow}\left(m\right) \le e\right)\right)\right) \land \left(\left(\forall x \in \mathrm{Real},\; \operatorname{det}\left(x \cdot 1 - \operatorname{quotient}\left(m, m, m\right)\right) = x \cdot \left(x - m^{2} - m\right) \cdot \left(x^{2} - \left(m^{2} + 4 \cdot m\right) \cdot x + 3 \cdot m^{2}\right)^{2}\right) \land \left(\operatorname{balancedLow}\left(m\right) < m^{2} + m \land m^{2} + m < \frac{m^{2} + 4 \cdot m + m \cdot \operatorname{sqrt}\left(\left(m + 4\right)^{2} - 12\right)}{2}\right)\right)\right)\right)\right)\right)\right)\right)\right)\right) \land \left(\operatorname{Tendsto}\left(\operatorname{balancedLow}, \operatorname{atTop}, \operatorname{nhds}\left(3\right)\right) \land \left(\operatorname{Tendsto}\left(\lambda n : \mathrm{Nat} \mapsto \operatorname{balancedLow}\left(\operatorname{realCast}\left(n\right)\right), \operatorname{atTop}, \operatorname{nhds}\left(3\right)\right) \land \left(\forall K \in \mathrm{Real},\; K < 3 \Rightarrow \left(\exists n \in \mathrm{Nat},\; 1 \le n \land \left(K < \operatorname{balancedLow}\left(\operatorname{realCast}\left(n\right)\right) \land \left(\exists z \in \operatorname{Fin}\left(6\right) \to \mathrm{Real},\; z \ne 0 \land \operatorname{mulVec}\left(\operatorname{quotient}\left(\operatorname{realCast}\left(n\right), \operatorname{realCast}\left(n\right), \operatorname{realCast}\left(n\right)\right), z\right) = \operatorname{balancedLow}\left(\operatorname{realCast}\left(n\right)\right) \cdot z\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/SixSupportLaplacianLowRoot.balanced_sharp_threshold` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

The factorization gives zero, m squared plus m, and the two quadratic roots, each quadratic root counted twice. For q_m(x)=x squared minus (m squared plus 4m)x plus 3m squared, q_m(0)=3m squared is positive, q_m(m)=minus m cubed is negative, and q_m(3)=9−12m is negative when m is at least one. The smaller quadratic root lies between zero and m; the larger root exceeds m squared plus m. A nonzero real symmetric eigenvector is constructed and transported by the proved similarity to C. Rationalization gives the strict lower bound 3m/(m+4), while the upper bound is three. The lower bound tends to three, so squeezing proves the real limit and the positive-integer subsequence limit. For every K below three there is a positive integer m whose smallest positive quotient eigenvalue exceeds K; every other positive real quotient eigenvalue then also exceeds K. Thus no constant smaller than three bounds the smallest positive quotient eigenvalues uniformly. The positive-real theorem supplies the same uniform bound for unequal ordered weights; the integer consequence follows by specializing its parameters.

Global separation and endpoint-one isolation. The following complete real-parameter application is attributed to thm:endpoint-one-spectrum and its proof through sharpness in paper/sections/endpoint-one-spectrum.tex of the public source at b93becea662a746badeadba42fdc3d3eb3db9382. The argument below is independently authored and uses the existing quotient geometry, real inertia and characteristic-polynomial suppliers. It is application exposition; the existing Describe statements retain their displayed geometry, low-root and balanced scope and do not certify this additional result. No fresh kernel acceptance of this application is asserted.

Statement on the actual spectrum. For every real a,b,c with 2 ≤ a ≤ b ≤ c, take C = SixSupportLaplacianLowRoot.quotient a b c in support order 1,2,3,12,13,23, with weights a,b,c,ab,ac,bc. Write χ_C(X) for its characteristic polynomial and h_C(X) = χ_C(X)/X for exact polynomial division. Thus χ_C(X) = X h_C(X), and h_C(x) = det(xI−C)/x when x ≠ 0. Let λ₁,…,λ₆ be its ascending real characteristic roots, counted with algebraic multiplicity, and put s = a+b+c. Then

0 = λ₁ < λ₂ ≤ λ₃ < a+b < s ≤ λ₄ ≤ λ₅ ≤ λ₆, with λ₄ = s if and only if (a,b,c) = (2,2,2).

At that boundary χ_C(X) = X(X−6)(X²−12X+12)². If h_C(1) = 0, then b+c ≥ 2a²−2a+1, with equality if and only if b = a and c = (a−1)(2a−1). If also a > κ = 2+sqrt(3), one is a simple root and the smallest positive quotient root. The exact monic quartic R_C(X) = h_C(X)/(X−1) has ascending roots μ₁,…,μ₄, with algebraic multiplicity, satisfying a < μ₁ < min{c,a+b} and s < μ₂ ≤ μ₃ ≤ μ₄. In particular every residual root exceeds a.

The cutoff is sharp on the entire ordered real endpoint-one family b = a, c = (a−1)(2a−1), a ≥ 2: h_C(1) = 0 there; at a = κ its smallest residual root equals a; and for every real 2 ≤ a < κ at least one residual root lies below a. The assertion below the cutoff removes only one occurrence of the root one and makes no assumption that one is simple in that range.

Actual carrier and multiplicities. All three parameters are positive, so quotient_geometry supplies the constant one-dimensional kernel of C and positive semidefiniteness of the existing S = symmetric a b c. In stored coordinates S has support order 1,2,3,23,13,12. With p = supportPermutation = [0,1,2,5,4,3] and D = diag(rootWeights a b c), that same theorem gives S = D C[p,p] D⁻¹. Every entry of D is positive. Reindexing by p and conjugating by this invertible diagonal preserve the entire characteristic polynomial, by Matrix.charpoly_reindex and charpoly_units_conj (or the equivalent intertwining form charpoly_eq_of_mul_eq_mul).

Use Matrix.IsHermitian.eigenvalues₀ for S and reverse its antitone Fin 6 enumeration: λᵢ is its entry at 6−i for 1 ≤ i ≤ 6. The pinned spectral theorem, charpoly_eq, roots_charpoly_eq_eigenvalues₀ and sort_roots_charpoly_eq_eigenvalues₀ give χ_C(X) = ∏ᵢ₌₁⁶(X−λᵢ) and χ_C.roots equal to the multiset of these six entries. Similarity transfers the one-dimensional constant kernel to S; Hermitian diagonalization and rank-nullity make zero occur exactly once. Positive semidefiniteness then gives λ₂,…,λ₆ > 0. Consequently h_C is monic of degree five with precisely those five positive roots, including their multiplicities. On h_C(1) = 0, exact division by X−1 defines a monic quartic R_C and removes exactly one occurrence of one from this multiset. These are the actual characteristic roots of C, rather than an assumed list of eigenvalues or a set that discards repetitions.

Real count bounds used in the proof. For a real t, let N(t) be the number of the six λᵢ strictly below t, counted with multiplicity. In the same orthonormal eigenbasis, tI−S is diagonal with entries t−λᵢ, so its positive index is N(t); the positive index of S−tI counts λᵢ > t. RHLinalg.finrank_le_posIndex_of_posDefOn and posIndex_conj_le apply over ℝ to an actual positive subspace or coordinate compression. Their hypotheses require Hermitianity and the displayed form signs, without assuming distinct roots or strict parameter ordering. The spectral diagonalization and the existing real invertible-congruence inertia theorem identify these indices with the stated counts.

For an upper count, use the positive spectral subspace supplied by posIndex_eq_max_finrank_posDefOn. If a shifted form is nonpositive on a coordinate subspace E, its positive spectral subspace meets E only in zero: a nonzero intersection vector would have both a positive and a nonpositive form value. Submodule.finrank_add_finrank_le_of_disjoint therefore bounds the positive index by 6−dim(E). This also handles a zero diagonal entry and repeated parameters. Finally, if no root equals t, the six-factor characteristic product has sign (−1)^(6−N(t)) = (−1)^N(t). This parity conclusion will always be used together with a proved interval for N(t).

A division-free determinant identity. For an arbitrary real x, put A_a(x) = (x−a)(x−b−c−bc)−abc, A_b(x) = (x−b)(x−a−c−ac)−abc and A_c(x) = (x−c)(x−a−b−ab)−abc. The literal six-by-six quotient gives

χ_C(x) = A_a(x)A_b(x)A_c(x) − ab(x−a)(x−b)A_c(x) − ac(x−a)(x−c)A_b(x) − bc(x−b)(x−c)A_a(x) + 2abc(x−a)(x−b)(x−c).

To obtain this from Matrix.det_apply, group the fixed-point and transposition choices for each pendant pair support with its sole singleton neighbor. The grouped factors are the three A terms. A transposition between two singleton supports contributes the corresponding negative ab, ac or bc term, and the two orientations of their triangle give the final positive term. No other nonzero permutation cycle is possible. No division by x−a, x−b or x−c occurs, so this identity remains valid at each of those points and at repeated parameters. At x = 1 it is the same determinant identity used in the fixed-gap application below, with no gap or eventual-size hypothesis.

Three roots below a+b. Put t = a+b and ρ = sqrt(a)sqrt(b)sqrt(c), so ρ² = abc. In original support order 3,12,13,23, the principal block of S is [[ab+a+b,−ρ],[−ρ,c]] direct-sum (b) direct-sum (a); its selector in stored coordinates is [2,5,4,3]. The two-dimensional block has characteristic polynomial Q(x) = x²−(ab+a+b+c)x+c(a+b), and Q(t) = −ab t < 0. Its shifted form can also be read directly as

ab u²−2ρuv+(c−t)v² = ab(u−ρv/(ab))²−t v².

Since ab > 0 and t > 0, this invertible change of two coordinates gives one positive and one negative square. The two scalar shifts are b−t = −a and a−t = −b. Thus the four-dimensional block has exactly three eigenvalues below t, and its three negative directions give three positive directions for tI−S by the real inertia supplier. Hence N(a+b) ≥ 3, or λ₃ < a+b. Since c > 0, also a+b < s.

Two roots above s away from the boundary. On singleton supports 1,2, the principal block of S−sI is [[bc−a,−sqrt(a)sqrt(b)],[−sqrt(a)sqrt(b),ac−b]]. Its first pivot d = bc−a is at least a(a−1) > 0. Its determinant is cΔ, where Δ = abc−a²−b² = ab(c−b)+(a−1)(b−a)(b+a)+(a−2)a². All three summands are nonnegative. If Δ = 0, the last forces a = 2, the middle forces b = a, and the first forces c = b. Conversely Δ = 0 at (2,2,2). Off that point Δ > 0; multiplying this block's form by d completes it to (du−sqrt(a)sqrt(b)v)²+cΔv². The block is positive definite and the real inertia bound gives at least two λᵢ > s, so λ₅ > s.

The determinant fixes the remaining position. Set p = ab+ac+bc and r = abc, as actual functions of the same parameters. Substituting x = s in the division-free identity and using s > 0 yields h_C(s) = −rs V, where V = r(s+3)−sp = a²(bc−b−c)+b²(ac−a−c)+c²(ab−a−b). For example bc−b−c = (b−2)(c−1)+(c−2) ≥ 0, with equality exactly when b = c = 2; the other brackets have the same property. Since the square coefficients are positive, V vanishes exactly at the all-two triple. Away from that point χ_C(s) = −rs²V < 0 and no λᵢ equals s. The bounds just proved give 3 ≤ N(s) ≤ 4. Its determinant sign forces N(s) odd, hence N(s) = 3 and λ₄ > s.

At (a,b,c) = (2,2,2), apply the existing balanced_sharp_threshold at m = 2, whose hypothesis is only m ≥ 1. It gives χ_C(X) = X(X−6)(X²−12X+12)². The ascending root multiset is 0, 6−2sqrt(6), 6−2sqrt(6), 6, 6+2sqrt(6), 6+2sqrt(6). Here 0 < 6−2sqrt(6) < 4 and s = 6. This proves the entire global ordering, including all multiplicities, and both directions of λ₄ = s if and only if the triple is all two.

Endpoint comparison. Assume h_C(1) = 0. Keep q = b+c and z = bc tied to the ordered parameters, and put K = 4a²−2a+1 and Q = 2a²−2a+1. Expansion of the same literal determinant at x = 1 gives

h_C(1) = (q−K)z²−a(a−1)(q+2a−1)z+P_a(q), where P_a(q) = (a²−1)q³+(a³−a²−3a+3)q²−3(a−1)²q−(a−1)³.

Define E_a(q,z) to be this displayed expression, only as local notation. Let z₀ = a(q−a). Ordering gives z−z₀ = (b−a)(c−a) ≥ 0, q ≥ 2a and z₀ ≥ a² > 0. If q ≤ Q, then q−K ≤ −2a² < 0, and

E_a(q,z)−E_a(q,z₀) = (z−z₀)[(q−K)(z+z₀)−a(a−1)(q+2a−1)] ≤ 0.

The bracket is strictly negative, because z+z₀ > 0 and q+2a−1 > 0. Thus equality in this comparison occurs exactly when z = z₀. For t = q−a ≥ a, direct factorization gives E_a(q,z₀) = [(a−1)(2a−1)−t]B(a,t) = (Q−q)B(a,t), where B(a,t) = a³−2a²t²+a²t+a²+3at−3a+t²−2t+1.

Its sign follows from a complete positive decomposition. Write t = a+u with u ≥ 0. Then −B(a,a+u) = (2a²−1)u²+[(a−2)(4a²+7a+9)+20]u+(a−2)[2a³+a(2a−1)+3]+5. Each term is nonnegative for a ≥ 2, and the constant term is at least five. Hence B(a,t) < 0 on the whole real domain, including a = 2. If q < Q, the last factorization and comparison would give h_C(1) < 0, a contradiction. Therefore b+c ≥ Q.

If q = Q on the endpoint surface, E_a(q,z₀) = 0, so h_C(1) = 0 forces z = z₀. Then (b−a)(c−a) = 0 and a ≤ b ≤ c force b = a; consequently c = Q−a = (a−1)(2a−1). Conversely, for every real a ≥ 2, these parameters satisfy c−a = 2a(a−2)+1 ≥ 1 and hence are ordered. They have q = Q and z = z₀, so the same actual determinant factorization gives h_C(1) = 0 and equality. This proves the full equality iff without an independent cubic or a positivity assumption.

Isolation above the cutoff. Suppose additionally a > κ = 2+sqrt(3). Then a²−4a+1 = (a−2)²−3 > 0. The endpoint sum bound yields b+c−(a²+2a) ≥ a²−4a+1 > 0. Evaluating the actual determinant identity at x = a gives h_C(a) = −a²b²c²(a²+2a−b−c) > 0, and χ_C(a) = a h_C(a) > 0. Thus no λᵢ equals a.

In stored coordinates let E be the three-dimensional subspace with zero singleton coordinates. The form of aI−S on E is (a−a)u²+(a−b)v²+(a−c)w² ≤ 0. Its positive spectral subspace is disjoint from E, so the upper count mechanism gives N(a) ≤ 3, including all repeated-parameter cases. Zero and at least one occurrence of one lie below a, hence N(a) ≥ 2. The positive determinant forces even N(a), so N(a) = 2. Since zero is already simple, there is exactly one occurrence of one and no other positive root below a. Thus λ₂ = 1 is simple and smallest positive, while λ₃,…,λ₆ > a.

For the upper residual endpoint, S−cI has form (a−c)u²+(b−c)v² on that same pair subspace, so at most three full roots exceed c. Equivalently λ₃ ≤ c. Actual determinant evaluation gives h_C(c) = −a²b²c²(c²+2c−a−b) < 0, since a+b ≤ 2c and c > 0. No characteristic root equals c, so λ₃ < c. The global gap gives λ₃ < a+b and λ₄ > s; its exceptional all-two case is excluded here. Exact division now identifies the ordered multiset of R_C with (λ₃,λ₄,λ₅,λ₆), proving a < μ₁ < min{c,a+b} and s < μ₂ ≤ μ₃ ≤ μ₄.

Sharpness for every real parameter. On b = a and c = (a−1)(2a−1), already shown ordered and on h_C(1) = 0 for every a ≥ 2, the same evaluation specializes to h_C(a) = a⁴(a−1)²(2a−1)²(a²−4a+1). At a = κ the final factor is zero, while a differs from zero and one. Therefore a survives both exact polynomial divisions as an actual residual root. The global gap is strict for this family, with λ₄ > s > a; the distinct roots 0,1,a must fill the three earlier positions. Hence λ₂ = 1 and λ₃ = a, each simple, and the smallest residual root equals a.

For every real 2 ≤ a < κ, the displayed prefactor is positive and a²−4a+1 = (a−2)²−3 < 0. Thus χ_C(a) < 0 and no root equals a. The same weak-sign pair subspace still gives 2 ≤ N(a) ≤ 3, because zero and one are below a. Negative determinant forces odd N(a), so N(a) = 3 with multiplicity. Removing the unique zero and just one occurrence of one leaves at least one residual root below a. This establishes the universal sharpness claim without invoking the strict-cutoff isolation outside its hypotheses.

Supplier correspondence and limits. The actual geometry and balanced specialization come from SixSupportLaplacianLowRoot; the real positive-subspace and compression bounds from RHLinalg in Sylvester and Inertia, with the existing invertible-congruence inertia supplier for the spectral count transport. They are cited at repository revision 6b24b302e37ea2ead041655259d42ef4866d3249. The characteristic-root multiset, sorting, polynomial division and finite-dimensional disjointness suppliers are from Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; the source note gives direct locators. No complex-only Courant–Fischer specialization or extra third-party import is needed. Existing positive_real_low_eigenvalue supplies an actual low eigenpair but does not certify this sorted-spectrum application. The exact determinant at one is shared with the fixed-gap application below; that application's eventual fixed-gap analytic argument does not replace these all-real counts, equalities or the gap-zero sharpness family. Divisor windows, off-surface generic residual positivity, and equality-curve/genus remain outside this application. The separate equality-spectrum locus c = b(b+2)−a is supplied by the exact matrix-polynomial correspondence below; it does not add ordered-root, simplicity or positivity conclusions. Ideal-graph realization and full three-prime classification retain their separate obligations.

Fixed real gaps at endpoint one. The public proposition prop:fixed-gap-expansion in paper/sections/proof-structure.tex, with the coefficients in lem:endpoint-one-small-gaps in paper/sections/three-prime-classification.tex, concerns this same quotient. Both locators are at the public revision cited above. For every fixed real d ≥ 1, there exist real A_d ≥ 2 and K_d ≥ 0 such that, for every real a ≥ A_d and b = a+d, exactly one real c > b satisfies h_C(1) = 0, where h_C(x) = det(xI−C)/x. Write this root as c*. Its full expansion, with one bound valid for all these a, is

|c* − (2a² + (2d−3)a − (d+2)(2d−1)/2 + d²/(2a) + d²(d+1)(2d−3)/(4a²))| ≤ K_d/a³.

Here C is SixSupportLaplacianLowRoot.quotient a b c, with support order 1,2,3,12,13,23 and weights a,b,c,ab,ac,bc, exactly as displayed above. Disjoint supports interact with entry minus the target weight: the singleton triangle and the three complementary singleton/pair edges are all the off-diagonal interactions. The existing permutation [0,1,2,5,4,3] only reverses the pair coordinates. No symmetric surrogate replaces C in the endpoint calculation. This application is a readable consequence of existing results; it is not an additional Lean theorem certified by the Describe statements above.

The actual determinant. At x = 1 the defining division gives h_C(1) = det(I−C). The following identity holds for all real a,b,c. Set r = 1−a, s = 1−b, u = 1−c, k = 1−a−b−c, N_a = k+ab+ac−bc, N_b = k+ab+bc−ac, and N_c = k+ac+bc−ab. Expanding the determinant gives

det(I−C) = N_a N_b N_c − abrs N_c − acru N_b − bcsu N_a + 2abcrsu.

Indeed each pair vertex in a nonzero determinant permutation is either fixed or transposed with its sole singleton neighbor. Summing these alternatives when a singleton is otherwise fixed yields (1−a)(1−b−c−bc)−abc = N_a and its two cyclic versions. The three singleton transpositions contribute −abrs N_c, −acru N_b and −bcsu N_a. The two oriented singleton 3-cycles together contribute 2abcrsu. These exhaust the nonzero permutation terms. This is a division-free use of Matrix.det_apply (equivalently det_apply') over the commutative ring of real numbers, so it includes parameters equal to one.

For explicit coefficient extraction, put σ = a+b, p = ab, v = 1−σ, w = v+p = rs, z = v−p, m = 1−(a−b)², and L = σ³−4pσ+2p−σ. Then N_a = w+(a−b−1)c, N_b = w+(b−a−1)c, N_c = z−vc. The determinant becomes (z−vc)(wv−2wc+mc²) − c(1−c)(wσv+Lc). Consequently h_C(1) = Q(c) = Ac³+Bc²+Dc+E, where

A = L−vm = a²+b²−1.

B = zm+(σ+2)vw−L = a³−4a²b²+2a²b−a²+2ab²+ab−3a+b³−b²−3b+3.

D = w(2p−3v) = (a−1)(b−1)(2ab+3a+3b−3).

E = wvz = (a−1)(b−1)(a+b−1)(ab+a+b−1).

These are precisely the four public cubic coefficients. Their algebraic identity holds at arbitrary real b = a+d; it does not inherit the restriction d ∈ {1,2} of the separate small-gap bracket lemma. From now on fix an arbitrary real d ≥ 1 and write Q_{a,d} for this cubic at b = a+d.

Polynomial regularization and a real local branch. Define the following real polynomials, with d held fixed:

α(t) = 2+2dt+(d²−1)t².

β(t) = −4+(6−8d)t+(−4d²+9d−1)t²+(5d²−d−6)t³+(d³−d²−3d+3)t⁴.

γ(t) = 2+(4d+2)t+(2d²+3d−13)t²+(d²−13d+12)t³−3(d−1)²t⁴.

δ(t) = 2+(5d−1)t+(4d²−2d−8)t²+(d³−d²−12d+12)t³−6(d−1)²t⁴−(d−1)³t⁵.

Set F(t,y) = α(t)y³+β(t)y²+t²γ(t)y+t³δ(t). At a = 1/t and b = 1/t+d, the coefficient formulas give t²A = α(t), t⁴B = β(t), t⁴D = γ(t) and t⁵E = δ(t) whenever t ≠ 0. Hence F(t,y) = t⁸ Q_{1/t,d}(y/t²) for every real t ≠ 0 and every real y. The displayed polynomial defines F at zero without using an inverse there. It gives F(0,y) = 2y²(y−2), F(0,2) = 0 and F_y(0,2) = 8.

Use the pinned real implicit-function theorem for f : ℝ × ℝ → ℝ, f(t,y) = F(t,y), at (0,2). The polynomial is real analytic, hence C^ω, and the three spaces are complete normed real spaces. The dependent derivative is z ↦ 8z, an invertible continuous linear map with inverse z ↦ z/8. In Mathlib.Analysis.Calculus.ImplicitContDiff the statements ContDiffAt.implicitFunction, implicitFunction_apply_self, eventually_apply_implicitFunction and contDiffAt_implicitFunction apply with n = ω ≠ 0. They provide Y : ℝ → ℝ with Y(0) = 2, F(t,Y(t)) = 0 on a neighborhood of zero, and C^ω regularity at zero. ContDiffAt.analyticAt identifies that regularity with analyticity here; continuity already gives Y(t) → 2. This local supplier is used for existence and continuity, while uniqueness on all c > b is established below.

Coefficients and a common error constant. Use fresh local symbols u = 2d−3, v = −(d+2)(2d−1)/2, w = d²/2 and z = d²(d+1)(2d−3)/4, and let P(t) = 2+ut+vt²+wt³+zt⁴. The coefficients of F(t,P(t)) from degree zero through four vanish. More explicitly, with each successive coefficient using the previous choices, the degree-zero coefficient is 0 and the degree-one through degree-four coefficients are respectively 8u+24−16d, 8v+4(d+2)(2d−1), 8w−4d² and 8z−2d²(d+1)(2d−3). These triangular equations give every coefficient displayed in P.

One can verify these equations directly by writing F(t,2+s) = H(t)+J(t)s+M(t)s²+α(t)s³, where H = 8α+4β+2t²γ+t³δ, J = 12α+4β+t²γ and M = 6α+β. In increasing powers of t, the coefficients needed are H: (0, 24−16d, −8d²+36d−8, 20d²+4d−18, 4d³−d−15), J: (8, 24−8d, −4d²+36d−14, 20d²−22), and M: (8, 4d+6, 2d²+9d−7). Substitution of s = ut+vt²+wt³+zt⁴ yields the preceding triangular equations. Thus Polynomial.X_pow_dvd_iff supplies a real polynomial R_d, of degree at most nine, with the identity F(t,P(t)) = t⁵R_d(t) for every real t. This residual calculation does not assume any derivatives or Taylor coefficients of Y.

Define M_d = 1+|R_d(0)| = 1+|[t⁵]F(t,P(t))| > 0. By Polynomial.continuousAt and Metric.continuousAt_iff, with output tolerance one at zero, there is a positive radius on which |R_d(t)−R_d(0)| < 1. The triangle inequality gives the same bound |R_d(t)| ≤ M_d throughout that neighborhood, hence |F(t,P(t))| ≤ M_d|t|⁵. The constant depends only on the fixed d.

The polynomial F_y is jointly continuous and F_y(0,2) = 8. Continuity with tolerance four, followed by restriction to a smaller product rectangle, gives η > 0 such that |F_y(t,s)−8| ≤ 4 whenever |t| < η and s ∈ B = [2−η,2+η]. Choose η strictly smaller than the original continuity radius so that the closed endpoints are included. Continuity of Y and P, both equal to two at zero, then puts both Y(t) and P(t) in this same convex interval B on a sufficiently small common t-neighborhood.

Now apply D5.S3.Quantum.Tomography.CayleyCoverAnalysis.preconditioned_residual_controls_displacement with E = F = ℝ, the one-variable function f(s) = F(t,s), derivative J(s)(r) = F_y(t,s)r, preconditioner C(r) = r/8, q = 1/2, x = P(t) and y = Y(t). The letters C, J and F in this supplier instance are local to that instance; its preconditioner is not the six-support matrix. The derivative exists everywhere because f is a polynomial. The operator C.comp(J(s))−id is multiplication by (F_y(t,s)−8)/8, whose norm is at most 1/2 throughout B. Convexity and both membership hypotheses hold on the same neighborhood. The supplied inequality therefore gives

(1/2)|Y(t)−P(t)| ≤ (1/8)|F(t,Y(t))−F(t,P(t))| = (1/8)|F(t,P(t))|, hence |Y(t)−P(t)| ≤ (M_d/4)|t|⁵.

This verifies both uniform premises of the quantitative inference: one residual bound and one derivative margin hold for every t in a common neighborhood. No pointwise error, unspecified coefficient match, or unverified remainder assumption is needed.

Eventual signs and placement. Let U(t) = 1+dt and S_d(t) = tα(t)U(t)³+β(t)U(t)²+tγ(t)U(t)+tδ(t). The polynomial identities give F(t,t+dt²) = t²S_d(t) and S_d(0) = −4. Continuity with tolerance two makes S_d(t) < 0 on a neighborhood of zero. At t = 1/a > 0 the scaling identity therefore gives Q_{a,d}(a+d) = a⁶S_d(1/a) < 0 for all sufficiently large real a. In addition S_d(t) = −4+tT_d(t) for a polynomial T_d; its continuity yields the source estimate Q_{a,d}(a+d) = −4a⁶+O_d(a⁵). The sign used here follows directly from S_d(0), without assuming that estimate.

Choose one ε_d > 0, at most one, small enough for the branch equation, residual bound, derivative margin, both interval memberships, the sign of S_d and Y(t) > 1 whenever |t| < ε_d. Each holds on a neighborhood already obtained, so a finite intersection provides this one radius. Define A_d = max{2,d+2,2/ε_d} and K_d = M_d/4. For every real a ≥ A_d, t = 1/a satisfies 0 < t < ε_d. Set c* = a²Y(1/a). The scaling identity makes it a root of the actual endpoint equation. Also c* > a², and a ≥ d+2 gives b = a+d < 2a ≤ a². Thus c* > b.

Global uniqueness above b. At these same parameters a ≥ 2 and b ≥ 3, the coefficients A = a²+b²−1 and E = (a−1)(b−1)(a+b−1)(ab+a+b−1) are positive. Hence Q(0) > 0 > Q(b). The polynomial x ↦ Q(−x) has degree three and leading coefficient −A < 0; Polynomial.tendsto_atBot_of_leadingCoeff_nonpos makes it tend to minus infinity as x tends to plus infinity. Choose l < 0 with Q(l) < 0. The intermediate-value theorem on [l,0] and [0,b] supplies roots in the open intervals (l,0) and (0,b), since their endpoint signs are strict. Along with c* > b these are three distinct real roots. A nonzero polynomial of degree three has at most three distinct roots, by Polynomial.mem_roots and Polynomial.card_le_degree_of_subset_roots. Any other root anywhere in (b,∞) would yield a four-element set of roots, a contradiction. Thus the uniqueness conclusion is global on the required half-line.

Finally divide |Y(t)−P(t)| ≤ (M_d/4)|t|⁵ by t² > 0. Since a²P(1/a) is exactly 2a²+(2d−3)a−(d+2)(2d−1)/2+d²/(2a)+d²(d+1)(2d−3)/(4a²), this gives the stated bound K_d/a³ for every real a ≥ A_d. Equivalently Asymptotics.isBigO_iff expresses the remainder as O_d(a^(−3)) at plus infinity. The construction has the quantifier order: for every fixed real d ≥ 1, choose A_d and K_d once, then the existence, global uniqueness and bound hold for every real a above that threshold.

Supplier correspondence and scope. The quotient, weights and permutation are reused from the owning D5 module, and the quantitative inequality from CayleyCoverAnalysis, at repository revision 6b24b302e37ea2ead041655259d42ef4866d3249. The analytic, polynomial, continuity, intermediate-value and root-count statements used here are from Mathlib revision 56a005855ea17e0b0958f73ec801ae140b0a1679; the source note gives their direct locators. The proof uses only real parameters and establishes no uniformity for growing d. At d = 1 the full expansion is 2a²−a−3/2+1/(2a)−1/(2a²)+O(a^(−3)); the valid small-gap bracket anchor 2a²−a−2 is a different expression. At d = 2 it is 2a²+a−6+2/a+3/a²+O(a^(−3)). The application concerns the existing weighted quotient. Realization by an ideal graph and the whole graph classification require their separate hypotheses and arguments; this supplementary consequence supplies neither a classification nor a literature novelty claim.

## Exact actual matrix and characteristic-polynomial correspondence

The complete matrix correspondence is for the existing LowRoot carrier itself. In support order 1,2,3,12,13,23, C = SixSupportLaplacianLowRoot.quotient a b c is the literal six-by-six matrix with diagonal entries b+c+bc, a+c+ac, a+b+ab, c, b, a and off-diagonal entries −b, −c, −bc, −a, −ac, −ab in the displayed support positions. This is the D−A sign convention: each edge interaction is the negative of its target weight. Its support weights are a,b,c,ab,ac,bc. No symmetric surrogate is substituted for this carrier.

The same literal matrix is defined over every commutative ring R. The universal integer model uses Z[x₀,x₁,x₂] and the rational model uses Q[x₀,x₁,x₂]; coefficientwise specialization to any commutative ring, and to every Q-algebra for the rational model, returns the actual matrix. The maps commute with the matrix, its characteristic polynomial and exact divX operation. Thus the integer, rational and arbitrary-parameter readings are coefficient extensions of one matrix definition, not separate named matrices.

Write χ_C(X) for the characteristic polynomial and h_C(X) for χ_C.divX. The constant coefficient of χ_C is zero because the all-one vector is an exact kernel vector over every commutative ring. Polynomial X_mul_divX_add therefore gives the literal identity χ_C(X) = X h_C(X), with zero remainder; divX is exact polynomial division and does not mean pointwise division at X=0. Over a nontrivial coefficient ring the six-by-six characteristic polynomial has degree six and h_C has degree five. These degree statements are ring-theoretic and make no positivity, ordering or root-simplicity assumption.

For every parameter triple, evaluation at one is tied to the same carrier by h_C(1) = det(I−C). On the endpoint substitution c = t−a with t = b(b+2), put q = a(t−a), A = 3b−1, B = b(b²+4b−1), and C₀ = −(b²+2b−1)(b²+3b−1)(b³+3b²+3b−1). Define G(a,b) = A q² + B q + C₀. The literal determinant calculation over the universal ring, followed by coefficient extension, gives for all commutative-ring parameters h_C(a,b,t−a)(1) = −(b−1)G(a,b). The factor b−1 is retained; it is not canceled.

Regard G as a polynomial in a over Q[b]. Its a-degree is exactly four. Regard the same expression as a polynomial in independent a,b; its total degree is exactly seven and the coefficient of a⁰b⁷ is −1. These are coefficient identities for the actual endpoint polynomial, not degree estimates for a reduced or canceled expression.

For real a,b, the actual matrix spectrum has value one exactly when b = 1 or G(a,b) = 0: (1 ∈ spectrum ℝ (SixSupportLaplacianLowRoot.quotient a b (t−a))) ↔ (b = 1 ∨ G(a,b) = 0). The b = 1 component is a genuine component of the actual spectrum locus and remains present for every real a. This equivalence is algebraic and carries no ordered-root, simplicity, positivity, or endpoint-domain hypothesis.

Literal bridge to the quartic tower. The endpoint polynomial just defined is coefficientwise the actualQuartic used in the characteristic-zero tower. After mapping Q[b] into k[b] and then K = RatFunc k, the resulting polynomial in the fresh quartic parameter variable X, representing a, is the literal g(X) = A X⁴ − 2At X³ + (At²−B)X² + BtX + C₀. In the actual fields H = K(y) with y² = D and F = H(z) with z² = f, the chosen a = (t+z)/2 satisfies q = a(t−a), y = 2Aq+B and z = 2a−t. Those recovery identities prove that the endpoint polynomial evaluated at the tower generator is zero and that the tower generator is the same root of the literal g. The quartic quotient K[X]/(g) ≃ F and the coefficient extension are therefore bridges between the actual matrix endpoint expression and the actual field tower, rather than identifications made from declaration names.

Authority and limits. The matrix identities, universal/rational specializations, degree facts, endpoint factor, coefficient and spectrum assertions are supplied by the complete matrix proof source and its source-bound actual result. This section is readable application exposition; it adds no retained Lean, Reg, Describe, freeze or positive-certificate declaration. The existing real global spectral theorem and fixed-gap argument remain in force, while the separately owed smooth models, local branches, genus, Riemann–Hurwitz, geometric finiteness interfaces, graph realization and full classification remain outside this source preparation.

## The exact quartic algebra over characteristic-zero fields

The equality-curve remark rem:endpoint-one-equality-curve in paper/sections/endpoint-one-spectrum.tex at public revision b93becea662a746badeadba42fdc3d3eb3db9382 supplies the polynomial used here. Its linked curve note at revision 8ed4f9014f6142949e6af40fd16e18ca304f629a supplies the displayed discriminant and norm numerator. The polynomial and those parameters are attributed to that source. The following derivation is an application of existing integral-closure, quadratic-algebra, Kummer, minimal-polynomial and Gauss results, not a novelty claim. The existing Describe statements retain their stated quotient geometry, low-root and balanced scope; this application adds no Lean declaration or Describe theorem.

Let k be any field of characteristic zero, let b be an indeterminate, and put K = k(b), represented by RatFunc k. Map rational coefficients into k[b] and then into K; these maps are injective. We keep the same letters for the images. No algebraic-closedness assumption on k is needed for the field-tower argument. In this section C₀ is the scalar constant coefficient, distinct from the six-support matrix C; the next integer-finiteness section denotes this same scalar by C. Define the literal polynomials

$$
t = b \cdot \left(b + 2\right)
$$

$$
A = 3 \cdot b - 1
$$

$$
B = b \cdot \left(b^{2} + 4 \cdot b - 1\right)
$$

$$
C_{0} = -\left(\left(b^{2} + 2 \cdot b - 1\right) \cdot \left(b^{2} + 3 \cdot b - 1\right) \cdot \left(b^{3} + 3 \cdot b^{2} + 3 \cdot b - 1\right)\right)
$$

$$
D = 12 \cdot b^{8} + 92 \cdot b^{7} + 233 \cdot b^{6} + 172 \cdot b^{5} + -154 \cdot b^{4} + -172 \cdot b^{3} + 161 \cdot b^{2} + -44 \cdot b + 4
$$

$$
N = \left(b^{3} + 5 \cdot b^{2} + 6 \cdot b - 2\right) \cdot \left(3 \cdot b^{6} + 8 \cdot b^{5} + -6 \cdot b^{4} + -36 \cdot b^{3} + -28 \cdot b^{2} + 40 \cdot b + -8\right)
$$

For the plane variable a, write q = a(t−a). The polynomial is quartic in a, with coefficients in k[b]:

$$
\operatorname{G}\left(a, b\right) = A \cdot \left(a \cdot \left(t - a\right)\right)^{2} + B \cdot a \cdot \left(t - a\right) + C_{0}
$$

Exact polynomial identities and branch prerequisites. Polynomial normalization gives both identities below. The degrees of D and N are eight and nine; a prime denotes differentiation in b. Explicit rational Bézout identities for (D,D′), (N,N′) and (N,D) give their normalized gcds equal to one; mapping each Bézout equality into k[b] preserves coprimality. Thus D and N are squarefree, and their root sets are disjoint in an algebraic closure. These are exact identities for these polynomials, rather than assumed squarefreeness or norm certificates.

$$
B^{2} - 4 \cdot A \cdot C_{0} = D
$$

$$
A \cdot t^{4} + 4 \cdot B \cdot t^{2} + 16 \cdot C_{0} = N
$$

$$
\operatorname{gcd}\left(D, \operatorname{derivative}\left(D\right)\right) = 1
$$

$$
\operatorname{gcd}\left(N, \operatorname{derivative}\left(N\right)\right) = 1
$$

$$
\operatorname{gcd}\left(N, D\right) = 1
$$

For explicit Bézout witnesses, a coefficient list (c₀,…,cₘ) denotes the polynomial Σᵢ cᵢbⁱ, in ascending powers of b. The following rational coefficient lists satisfy U_D D+V_D D′ = 1, U_N N+V_N N′ = 1 and U_ND N+V_ND D = 1, respectively. These identities can be read as polynomial equalities before mapping to k[b].

U_D = (15077458503622003/12603918688, -54128905348874963/12603918688, -6246087705771407/3150979672, 117940112961877943/12603918688, 145006858328612117/12603918688, 30779539539563445/6301959344, 551481433980327/787744918).

V_D = (1370677759331121/12603918688, -19934798047738501/25207837376, 36019683710933693/25207837376, 8204653143188935/12603918688, -44366105575549787/25207837376, -47526676857220537/25207837376, -1093986370835811/1575489836, -551481433980327/6301959344).

U_N = (-1551720656793517/69254786592, 290115890479151/46169857728, 6813283610138383/92339715456, 34122483667637429/554038292736, 3370077294694969/2216153170944, -86652849207243331/4432306341888, -39894848329397747/4432306341888, -417181352926057/328318988288).

V_N = (-1551724985217679/554038292736, 13284078298392293/1108076585472, -27151801510553/123119620608, -13019587671423695/738717723648, -1608792935985931/130361951232, -192340276236565/492478482432, 2030298571254023/738717723648, 9931651975121645/8864612683776, 417181352926057/2954870894592).

U_ND = (-3559310030328403/471932176, 6462996085656055/117983044, -46657822536661549/471932176, -21303192533434097/471932176, 14356909865819141/117983044, 61549445215520121/471932176, 5667971824526075/117983044, 714366125043951/117983044).

V_ND = (889827514956041/29495761, -3793513481796410/29495761, 61458663986279/29495761, 22274907297181941/117983044, 15611438025308693/117983044, 249440883003581/58991522, -13899098543371799/471932176, -5667971824526075/471932176, -714366125043951/471932176).

At r = 1/3 the exact values are A(r) = 0, A′(r) = 3, B(r) = 4/27, D(r) = 16/729 and N(r) = 368/729. The nonzero rational values remain nonzero in every characteristic-zero k. The gcds and these values are prerequisites for the later branch analysis; they do not identify any local ring or ramification point on a model.

The first actual quadratic field. Coprimality with D′ makes D separable, hence squarefree, after coefficient extension. If x² = D in K, the integral-closure result IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow, applied to the polynomial ring k[b] and its fraction field K, supplies a polynomial w whose image is x. Injectivity then gives D = w² in k[b]. Squarefreeness forces w to be a unit, which would make D a unit of degree zero, contrary to degree eight. Thus D is nonsquare in K, with this premise proved for the displayed D.

The existing QuadraticAlgebra field instance therefore constructs the field H = QuadraticAlgebra K D 0, with generator y = omega satisfying y² = D. Its basis 1,y and finrank_eq_two give [H:K] = 2, and adjoin_omega_eq_top gives H = K(y). The prime-two instance of Polynomial.X_pow_sub_C_irreducible_iff_of_prime shows X²−D is irreducible; minpoly.eq_of_irreducible_of_monic identifies it as minpoly_K(y). The polynomial A has leading coefficient 3 ≠ 0, so its image in K and then H is nonzero and invertible. Define

$$
q = \frac{y - B}{2 \cdot A}
$$

$$
f = t^{2} - 4 \cdot q
$$

$$
f = t^{2} + \frac{2 \cdot B}{A} - \frac{2 \cdot y}{A}
$$

Using y² = D and B²−4AC₀ = D gives Aq²+Bq+C₀ = 0 and y = 2Aq+B. Here q is an actual element of H, and y = 2Aq+B puts its generator in K(q), so H = K(q). The first quadratic conjugation fixes K and sends y to −y. Its norm calculation is

$$
\operatorname{Norm}\left(H, K, f\right) = \left(t^{2} + \frac{2 \cdot B}{A}\right)^{2} - \frac{4 \cdot D}{A^{2}}
$$

$$
\operatorname{Norm}\left(H, K, f\right) = \frac{A \cdot t^{4} + 4 \cdot B \cdot t^{2} + 16 \cdot C_{0}}{A}
$$

$$
\operatorname{Norm}\left(H, K, f\right) = \frac{N}{A}
$$

QuadraticAlgebra.norm_def supplies the expression u²−Dv² for u+vy. QuadraticAlgebra.det_toLinearMap_eq_norm, together with Algebra.norm_apply, identifies that expression with the actual field norm Algebra.norm K on H. Therefore its multiplicativity is available for the nonsquare inference, rather than being an unproved norm interpretation.

A proved simple rational-field pole. Since A = 3(b−r) and N(r) ≠ 0, the reduced monic RatFunc denominator of N/A is exactly b−r, with root multiplicity one. The denominator-divisibility, cross-multiplication and monicity results for RatFunc give this reduced-denominator statement. N/A is nonsquare by a direct algebraic obstruction: if x² = N/A in K, then (Ax)² = AN. The same integral-closure supplier gives w in k[b] with w² = AN. Evaluation at r forces w(r) = 0. Differentiating the polynomial identity and evaluating at r would force 0 = A′(r)N(r) = 3·368/729, which is nonzero in characteristic zero. This proves the simple-pole nonsquare without assuming a valuation certificate. It concerns the rational base field; it does not yet prove orders at either of the two places of H over r.

The second actual quadratic field. If f were a square in H, multiplicativity of the actual field norm would make N/A a square in K. Thus f is nonsquare. The existing field instance now constructs F = QuadraticAlgebra H f 0 = H(z), with z = omega, z² = f, [F:H] = 2 and minpoly_H(z) = X²−f. The Kummer irreducibility and generation suppliers apply with the proved f-nonsquare premise, just as at the first step. Module.finrank_mul_finrank on the actual scalar tower gives [F:K] = 4. Both quadratic steps and F/K are finite separable extensions: all the fields have characteristic zero, and their finite algebraic extensions are separable. No smooth model or full constant-field assertion is used to obtain these field-level statements.

The actual quartic generator. In F choose a = (t+z)/2, using the embeddings K → H → F consistently. The sign of y is fixed by q = (y−B)/(2A). The equations z² = f and Aq²+Bq+C₀ = 0 give the recovery identities

$$
q = a \cdot \left(t - a\right)
$$

$$
y = 2 \cdot A \cdot a \cdot \left(t - a\right) + B
$$

$$
z = 2 \cdot a - t
$$

Every element of H is h₀+h₁y with h₀,h₁ in K, and every element of F is u+vz with u,v in H, by QuadraticAlgebra.re_smul_add_im_smul. The recovery formulas put y and z in K(a); these decompositions then put all of H and F in K(a). Hence F = K(a) = k(b,a), with a genuinely generating the field already constructed. Field.primitive_element_iff_minpoly_natDegree_eq gives degree four for minpoly_K(a).

To bind that generator to the literal polynomial, let X be a fresh polynomial variable and put g(X) = A[X(t−X)]²+B[X(t−X)]+C₀ in K[X]. Its expansion is

$$
\operatorname{g}\left(X\right) = A \cdot X^{4} + -2 \cdot A \cdot t \cdot X^{3} + \left(A \cdot t^{2} - B\right) \cdot X^{2} + B \cdot t \cdot X + C_{0}
$$

Thus g has degree four and leading coefficient A ≠ 0, and the actual a satisfies g(a) = 0. Its monic normalization A⁻¹g has the same degree and vanishes at a, so minpoly.unique_of_degree_le_degree_minpoly gives A⁻¹g = minpoly_K(a). Irreducibility of the minimal polynomial and multiplication by the nonzero constant A give irreducibility of g in K[X]. The argument uses this original g throughout.

The root-preserving polynomial quotient. Because g and A⁻¹g are associated, AdjoinRoot.algEquivOfAssociated identifies their quotients; AdjoinRoot.algEquivOfEq then uses A⁻¹g = minpoly_K(a). The existing minpoly.equivAdjoin and the proved generation identify the latter quotient with all of F. The composite is a K-algebra equivalence K[X]/(g) = AdjoinRoot(g) ≃ F, sending the residue root to the chosen a. The recovery formulas above identify y and z in its image as well. This supplies the actual quartic-polynomial/field correspondence, separately from the matrix/characteristic-polynomial correspondence.

Primitivity and absolute polynomial irreducibility. Work first in k[b][X], before passing to its fraction field in b. The polynomial A is a nonzero scalar multiple of b−1/3, while B(1/3) = 4/27 ≠ 0, so A and B are coprime in k[b]. A divisor common to all coefficients of G divides the coefficients A of X⁴ and At²−B of X²; it therefore divides B and is a unit. This proves that the literal quartic is primitive. Polynomial.IsPrimitive.irreducible_iff_irreducible_map_fraction_map now transfers the proved irreducibility in K[X] back to k[b][X].

For coefficient extension, let G_ℚ denote precisely A[X(t−X)]²+B[X(t−X)]+C₀ in ℚ[b][X]. The coefficientwise homomorphism pk : ℚ[b] → k[b], induced by ℚ → k, sends G_ℚ to exactly the plane polynomial just used; its further map to K[X] is g. Consequently the original rational polynomial remains irreducible after this coefficient extension for every characteristic-zero k. In particular, taking k = AlgebraicClosure ℚ proves irreducibility of map(pk)(G_ℚ) in (AlgebraicClosure ℚ)[b][X]. This is the actual absolute polynomial irreducibility statement, rather than only irreducibility over ℚ(b). It supplies no smooth projective model or genus computation.

Second conjugation and fixed elements. The involution of the second quadratic algebra fixes H and sends z to −z, so it sends a to t−a and fixes q = a(t−a) and y = 2Aq+B. For u = u₀+u₁z with u₀,u₁ in H, conjugation gives u₀−u₁z. Since 2 ≠ 0 and 1,z are independent, it fixes u exactly when u₁ = 0, exactly when u is in the image of H in F. This identifies the field fixed elements with H. It does not construct a quotient morphism between smooth models.

Supplier correspondence. The applications above use Mathlib revision 56a005855ea17e0b0958f73ec801ae140b0a1679: IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow for both nonsquare obstructions; QuadraticAlgebra's field instance, finrank_eq_two, omega_mul_omega_eq_algebraMap, re_smul_add_im_smul, adjoin_omega_eq_top, norm_def and det_toLinearMap_eq_norm for the actual fields, generators, degrees, norm and conjugation; Polynomial.X_pow_sub_C_irreducible_iff_of_prime and minpoly.eq_of_irreducible_of_monic for the two quadratic minimal polynomials; Module.finrank_mul_finrank and Field.primitive_element_iff_minpoly_natDegree_eq for the degree-four generator; minpoly.unique_of_degree_le_degree_minpoly, minpoly.equivAdjoin and AdjoinRoot.algEquivOfAssociated/algEquivOfEq for its minimal polynomial and quotient; and Polynomial.IsPrimitive.irreducible_iff_irreducible_map_fraction_map for Gauss transfer. The owning Library note gives direct public source locators. These are existing suppliers applied to the displayed parameters; this exposition retains no named transient checking wrappers or positive-instance declarations.

Remaining E3 boundary. The exact E3.00 universal six-support polynomial/characteristic-polynomial bridge, exact X division, substitution c = b(b+2)−a, identity h_C(1) = −(b−1)G, and faithful matrix correspondence are supplied in the “Exact actual matrix and characteristic-polynomial correspondence” section. The literal quartic quotient equivalence is separately tied to the bridge in that same section. The algebra portions of E3.01–E3.02 and E3.06–E3.08 are the discriminant, both actual fields, norm, nonsquares, degrees, separability, primitive generator and absolute polynomial irreducibility established above; their actual curve/model identifications remain separate.

E3.03 still requires actual smooth proper models, full constant fields, identification of their function fields and actual finite separable b-maps. E3.04 must identify the eight finite D-branch places and both infinity places with local rings, uniformizers, ramification and different hypotheses. E3.05 must apply Riemann–Hurwitz on that quotient model to obtain 2g(H)−2 = 2(−2)+8 = 4 and genus three. Squarefree degree eight alone is not that model-level proof.

E3.09 still requires nine actual simple f-zero places above roots of N, with regularity of both conjugate factors, a nonzero companion and order one. E3.10 must identify both H-places over 1/3, proving q and f have order −1 at one and that the other has q regular and f nonzero, with the local norm/order bridge. E3.11 must supply the two actual infinity points and coordinates giving ord(q) = −3 and ord(f) = −4 at each. E3.12 must exclude all other odd valuations, discharge local Kummer parity and tame different hypotheses, and prove exactly ten branches. The rational-field simple pole above is not a substitute for these local assertions.

E3.13 still requires the actual smooth projective normalization, its full constants and model morphism, and matched Riemann–Hurwitz with 2g(X)−2 = 2(2·3−2)+10 = 18, giving geometric genus ten. Arithmetic genus fifteen is not substituted. For E3.14 the elementary all-integer finiteness application in the following section already supplies finiteness of G(a,b) = 0, including A(b) ≠ 0 on integer b and finite a-fibers; this algebra section does not erase or reprove that result. The separate geometric route still owes an actual integer map to the constructed smooth affine quotient, its at-most-two fibers, and a Siegel or complete hyperelliptic finiteness theorem with all hypotheses matched. The F1–F3, G1–G5, E1–E4 and original 21+5 obligations are unchanged. No complete E3, effective point list, emptiness or graph classification follows from the algebra application alone.

## Integer points on the endpoint equality polynomial

The equality-curve remark in paper/sections/endpoint-one-spectrum.tex, label rem:endpoint-one-equality-curve, at the same public revision b93becea662a746badeadba42fdc3d3eb3db9382 supplies the polynomial below. The scalar C in this section denotes its constant term in q, distinct from the quotient matrix above. We give an elementary arithmetic derivation of finiteness by applying the existing facts that a nonzero polynomial over the integers has finitely many roots, a finite union of finite sets is finite, and a set with finite projection and finite fibers is finite. These are supplied by Polynomial.finite_setOfPred_isRoot, Set.Finite.biUnion and Set.Finite.of_finite_fibers. The parameter domain is all integer pairs (a,b), with no positivity or spectral-ordering assumption.

$$
t = b \cdot \left(b + 2\right)
$$

$$
q = a \cdot \left(t - a\right)
$$

$$
A = 3 \cdot b - 1
$$

$$
B = b \cdot \left(b^{2} + 4 \cdot b - 1\right)
$$

$$
C = -\left(\left(b^{2} + 2 \cdot b - 1\right) \cdot \left(b^{2} + 3 \cdot b - 1\right) \cdot \left(b^{3} + 3 \cdot b^{2} + 3 \cdot b - 1\right)\right)
$$

$$
\operatorname{G}\left(a, b\right) = A \cdot q^{2} + B \cdot q + C
$$

Let n=|b| be at least four. The triangle inequality gives |A|≥2n and |B|≤3n³. The three factors in |C| are bounded respectively by 2n², 2n² and 3n³, so |C|≤18n⁷. If G(a,b)=0 and x=|q|, then 2nx²≤3n³x+18n⁷. Were x>4n³, we would have 24n³x<6nx² and 144n⁷<9nx². Multiplying the preceding weak inequality by eight would then give 16nx²<15nx², a contradiction. Thus |q|≤4n³.

The involution a↦t−a preserves q and G. Choose u from a and t−a with |u|≤|t−u|, and put v=t−u. Since |b+2|≥n−2 and n≥4, n²≤2|t|≤2(|u|+|v|)≤4|v|. Multiplication by |u|, together with |uv|=|q|≤4n³, gives |u|n²≤16n³, hence |u|≤16n. The chosen pair (u,b) is still a solution. This choice preserves b and works for both signs of b; it is used only to bound the projection, so both original involution partners remain in the final set.

In the following identities write q=u(t−u). Define the auxiliary integer F and the following polynomials. All displayed polynomial identities hold over the integers without division.

$$
\operatorname{F}\left(u, b\right) = 9 \cdot u^{2} - 3 \cdot u - 3 \cdot b^{2} - 13 \cdot b
$$

$$
Q = \left(27 \cdot b - 9\right) \cdot u^{2} + \left(-54 \cdot b^{3} + -90 \cdot b^{2} + 45 \cdot b + -3\right) \cdot u + 27 \cdot b^{5} + 99 \cdot b^{4} + 54 \cdot b^{3} + -66 \cdot b^{2} + 11 \cdot b + -1
$$

$$
L_{0} = 3 \cdot \left(3 \cdot b^{2} + 6 \cdot b - 1\right) \cdot \left(-21 \cdot b^{2} + 8 \cdot b + 1\right)
$$

$$
M_{0} = -333 \cdot b^{5} + -1197 \cdot b^{4} + -258 \cdot b^{3} + 1436 \cdot b^{2} + -661 \cdot b + 81
$$

$$
81 \cdot \operatorname{G}\left(u, b\right) = \operatorname{F}\left(u, b\right) \cdot Q + u \cdot L_{0} + M_{0}
$$

For n≥1 and |u|≤16n, summing absolute monomials and using nʲ≤nᵏ for j≤k gives |Q−27b⁵|≤12519n⁴, |L₀|≤900n⁴ and |M₀|≤3966n⁵. The first constant is 36·256+192·16+231=12519; the second is 3·10·30=900; the third is 333+1197+258+1436+661+81=3966. For n≥1000, 12519n⁴≤26n⁵, and hence |Q|≥27n⁵−12519n⁴≥n⁵. On a solution the identity gives |F|n⁵≤|FQ|=|uL₀+M₀|≤(16·900+3966)n⁵=18366n⁵. Cancelling the positive n⁵ yields |F(u,b)|≤18366. Thus every solution with |b|≥1000 has a representative with the same b and an integer r=F(u,b) in [−18366,18366].

For each fixed integer r, define the following polynomials in b. Here A, B and C retain their definitions above.

$$
D_{0} = 3 \cdot b^{2} + 6 \cdot b - 1
$$

$$
T_{r} = 3 \cdot b^{2} + 13 \cdot b + r
$$

$$
L_{r} = 3 \cdot D_{0} \cdot \left(A \cdot D_{0} + -2 \cdot A \cdot T_{r} + 9 \cdot B\right)
$$

$$
M_{r} = A \cdot T_{r} \cdot \left(\left(D_{0}\right)^{2} + T_{r}\right) + -9 \cdot B \cdot T_{r} + 81 \cdot C
$$

When F(u,b)=r, the identities 9q=3uD₀−Tᵣ and 9u²=3u+Tᵣ reduce 81G(u,b) to uLᵣ+Mᵣ. For a solution Mᵣ=−uLᵣ, so the eliminant below vanishes. No division by Lᵣ occurs, including when Lᵣ=0.

$$
H_{r} = 9 \cdot \left(M_{r}\right)^{2} + 3 \cdot M_{r} \cdot L_{r} - T_{r} \cdot \left(L_{r}\right)^{2}
$$

$$
H_{r} = \left(9 \cdot u^{2} - 3 \cdot u - T_{r}\right) \cdot \left(L_{r}\right)^{2}
$$

The second equality holds under the two equations F(u,b)=r and G(u,b)=0; its right side is zero. Expanding the defining polynomials gives:

$$
L_{r} = -189 \cdot b^{4} + \left(-306 - 54 \cdot r\right) \cdot b^{3} + \left(216 - 90 \cdot r\right) \cdot b^{2} + \left(54 \cdot r - 6\right) \cdot b + -3 + -6 \cdot r
$$

$$
M_{r} = \left(27 \cdot r - 333\right) \cdot b^{5} + \left(99 \cdot r - 1197\right) \cdot b^{4} + \left(63 \cdot r - 258\right) \cdot b^{3} + \left(1436 - 30 \cdot r\right) \cdot b^{2} + \left(3 \cdot r^{2} + -2 \cdot r + -661\right) \cdot b + 81 + -r^{2} + -r
$$

These expansions show that Hᵣ has degree at most ten. Its coefficient of b¹⁰ is 9(27r−333)²−3·189²=729((3r−37)²−147). For any integer r, (3r−37)² is congruent to one modulo three, whereas 147 is congruent to zero. The coefficient is therefore nonzero. Hᵣ is a nonzero polynomial of degree exactly ten and has finitely many integer roots.

The b-projection of G(a,b)=0 is contained in [−999,999] together with the union of the root sets of Hᵣ for integers r in [−18366,18366]. Both intervals are finite, and each root set is finite, so the projection is finite. For every fixed integer b, the polynomial G(a,b) in a has quartic coefficient 3b−1. It is nonzero because 3b=1 has no integer solution; its integer root set, and hence each a-fiber, is finite. Applying finiteness from finite projection and finite fibers proves that the set of all (a,b) in ℤ² with G(a,b)=0 is finite. This includes zero and negative coordinates, every small-b fiber, and both involution partners.

This application establishes finiteness of the stated polynomial zero set. An effective list of points, emptiness and classification require further arguments. Relating the polynomial to admissible graph or matrix parameters is a separate mathematical step. The arithmetic argument does not establish geometric irreducibility, Kummer models, full constant fields or separability, local orders or ramification, or genus-three and genus-ten calculations. The public source's geometric discussion is separate from the polynomial and elementary finiteness argument given here.

## References

- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/SixSupportLaplacianLowRoot.balancedLow`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/SixSupportLaplacianLowRoot.balanced_sharp_threshold`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/SixSupportLaplacianLowRoot.positive_real_low_eigenvalue`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/SixSupportLaplacianLowRoot.quotient`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/SixSupportLaplacianLowRoot.quotient_geometry`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/SixSupportLaplacianLowRoot.rootWeights`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/SixSupportLaplacianLowRoot.small_second_negative_plane`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/SixSupportLaplacianLowRoot.supportPermutation`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/SixSupportLaplacianLowRoot.symmetric`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/SixSupportLaplacianLowRoot.toQuotientVector`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/SixSupportLaplacianLowRoot.weights`
