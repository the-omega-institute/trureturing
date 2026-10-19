# Six-support quotient and balanced threshold

## Abstract

The six-support weighted quotient, its symmetric representative, and the sharp balanced spectral threshold.

The support order for C is 1,2,3,12,13,23. The public source is paper/core/body.tex in the-omega-institute/ideal-intersection-laplacian at commit b93becea662a746badeadba42fdc3d3eb3db9382. Its quotient and energy occur on lines 574–600 and 774–784; its balanced sharpness proposition occurs on lines 114–145. The matrix model and balanced statement are attributed to that source. The Lean proofs and this exposition are independently authored; no novelty or graph-integrality classification is asserted.

**Definition 1.1 (The literal nonsymmetric quotient).**

$$\forall a \in \mathrm{Real},\; \forall b \in \mathrm{Real},\; \forall c \in \mathrm{Real},\; \operatorname{quotient}\left(a, b, c\right) = \begin{pmatrix}b + c + b \cdot c&-b&-c&0&0&-\left(b \cdot c\right)\\-a&a + c + a \cdot c&-c&0&-\left(a \cdot c\right)&0\\-a&-b&a + b + a \cdot b&-\left(a \cdot b\right)&0&0\\0&0&-c&c&0&0\\0&-b&0&0&b&0\\-a&0&0&0&0&a\end{pmatrix}$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/SixSupportLaplacianLowRoot.quotient` (`✓ std3`).

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient and uniform low root*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

Rows and columns have the stated original support order. Multiplying on the left by diag(a,b,c,ab,ac,bc) makes the matrix symmetric.

**Definition 1.2 (Support weights).**

$$\forall a \in \mathrm{Real},\; \forall b \in \mathrm{Real},\; \forall c \in \mathrm{Real},\; \operatorname{weights}\left(a, b, c\right) = [a,b,c,a \cdot b,a \cdot c,b \cdot c]$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/SixSupportLaplacianLowRoot.weights` (`✓ std3`).

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient and uniform low root*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

The final three weights are the pair-support class sizes.

**Definition 1.3 (Paired-coordinate reversal).**

$$\operatorname{supportPermutation} = \operatorname{permutation}\left([0,1,2,5,4,3]\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/SixSupportLaplacianLowRoot.supportPermutation` (`✓ std3`).

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient and uniform low root*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

This involution changes the support order to 1,2,3,23,13,12.

**Definition 1.4 (Square-root diagonal).**

$$\forall a \in \mathrm{Real},\; \forall b \in \mathrm{Real},\; \forall c \in \mathrm{Real},\; \operatorname{rootWeights}\left(a, b, c\right) = [\operatorname{sqrt}\left(a\right),\operatorname{sqrt}\left(b\right),\operatorname{sqrt}\left(c\right),\operatorname{sqrt}\left(b\right) \cdot \operatorname{sqrt}\left(c\right),\operatorname{sqrt}\left(a\right) \cdot \operatorname{sqrt}\left(c\right),\operatorname{sqrt}\left(a\right) \cdot \operatorname{sqrt}\left(b\right)]$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/SixSupportLaplacianLowRoot.rootWeights` (`✓ std3`).

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient and uniform low root*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

All six entries are positive when a,b,c are positive. Their squares are the reordered support weights.

**Definition 1.5 (The symmetric representative).**

$$\forall a \in \mathrm{Real},\; \forall b \in \mathrm{Real},\; \forall c \in \mathrm{Real},\; \operatorname{symmetric}\left(a, b, c\right) = \begin{pmatrix}b + c + b \cdot c&-\left(\operatorname{sqrt}\left(a\right) \cdot \operatorname{sqrt}\left(b\right)\right)&-\left(\operatorname{sqrt}\left(a\right) \cdot \operatorname{sqrt}\left(c\right)\right)&-\left(\operatorname{sqrt}\left(a\right) \cdot \operatorname{sqrt}\left(b\right) \cdot \operatorname{sqrt}\left(c\right)\right)&0&0\\-\left(\operatorname{sqrt}\left(a\right) \cdot \operatorname{sqrt}\left(b\right)\right)&a + c + a \cdot c&-\left(\operatorname{sqrt}\left(b\right) \cdot \operatorname{sqrt}\left(c\right)\right)&0&-\left(\operatorname{sqrt}\left(a\right) \cdot \operatorname{sqrt}\left(b\right) \cdot \operatorname{sqrt}\left(c\right)\right)&0\\-\left(\operatorname{sqrt}\left(a\right) \cdot \operatorname{sqrt}\left(c\right)\right)&-\left(\operatorname{sqrt}\left(b\right) \cdot \operatorname{sqrt}\left(c\right)\right)&a + b + a \cdot b&0&0&-\left(\operatorname{sqrt}\left(a\right) \cdot \operatorname{sqrt}\left(b\right) \cdot \operatorname{sqrt}\left(c\right)\right)\\-\left(\operatorname{sqrt}\left(a\right) \cdot \operatorname{sqrt}\left(b\right) \cdot \operatorname{sqrt}\left(c\right)\right)&0&0&a&0&0\\0&-\left(\operatorname{sqrt}\left(a\right) \cdot \operatorname{sqrt}\left(b\right) \cdot \operatorname{sqrt}\left(c\right)\right)&0&0&b&0\\0&0&-\left(\operatorname{sqrt}\left(a\right) \cdot \operatorname{sqrt}\left(b\right) \cdot \operatorname{sqrt}\left(c\right)\right)&0&0&c\end{pmatrix}$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/SixSupportLaplacianLowRoot.symmetric` (`✓ std3`).

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient and uniform low root*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

The paired diagonal is a,b,c; each singleton is coupled to its complementary pair by minus sqrt(a)sqrt(b)sqrt(c), equal to minus sqrt(abc) at positive parameters.

**Definition 1.6 (Return to the actual quotient).**

$$\forall a \in \mathrm{Real},\; \forall b \in \mathrm{Real},\; \forall c \in \mathrm{Real},\; \forall z \in \operatorname{Fin}\left(6\right) \to \mathrm{Real},\; \forall i \in \operatorname{Fin}\left(6\right),\; \operatorname{toQuotientVector}\left(a, b, c, z\right)\left(i\right) = \frac{z\left(\operatorname{inverse}\left(\operatorname{supportPermutation}, i\right)\right)}{\operatorname{rootWeights}\left(a, b, c\right)\left(\operatorname{inverse}\left(\operatorname{supportPermutation}, i\right)\right)}$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/SixSupportLaplacianLowRoot.toQuotientVector` (`✓ std3`).

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient and uniform low root*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

The inverse coordinate permutation and positive inverse diagonal preserve nonzero vectors and transport the same real eigenvalue to C.

**Theorem 1.7 (Weighted energy, kernel and similarity).**

$$\forall a \in \mathrm{Real},\; \forall b \in \mathrm{Real},\; \forall c \in \mathrm{Real},\; 0 < a \Rightarrow \left(0 < b \Rightarrow \left(0 < c \Rightarrow \left(\left(\left(\forall z \in \operatorname{Fin}\left(6\right) \to \mathrm{Real},\; \operatorname{dotProduct}\left(\lambda i : \operatorname{Fin}\left(6\right) \mapsto \operatorname{weights}\left(a, b, c\right)\left(i\right) \cdot z\left(i\right), \operatorname{mulVec}\left(\operatorname{quotient}\left(a, b, c\right), z\right)\right) = a \cdot b \cdot \left(z\left(0\right) - z\left(1\right)\right)^{2} + a \cdot c \cdot \left(z\left(0\right) - z\left(2\right)\right)^{2} + b \cdot c \cdot \left(z\left(1\right) - z\left(2\right)\right)^{2} + a \cdot b \cdot c \cdot \left(\left(z\left(0\right) - z\left(5\right)\right)^{2} + \left(z\left(1\right) - z\left(4\right)\right)^{2} + \left(z\left(2\right) - z\left(3\right)\right)^{2}\right)\right) \land \left(\left(\forall z \in \operatorname{Fin}\left(6\right) \to \mathrm{Real},\; \operatorname{mulVec}\left(\operatorname{quotient}\left(a, b, c\right), z\right) = 0 \Leftrightarrow \left(\exists t \in \mathrm{Real},\; z = \lambda i : \operatorname{Fin}\left(6\right) \mapsto t\right)\right) \land \left(\operatorname{mulVec}\left(\operatorname{quotient}\left(a, b, c\right), \lambda i : \operatorname{Fin}\left(6\right) \mapsto 1\right) = 0 \land \operatorname{vecMul}\left(\operatorname{weights}\left(a, b, c\right), \operatorname{quotient}\left(a, b, c\right)\right) = 0\right)\right)\right) \land \left(\operatorname{PosSemidef}\left(\operatorname{symmetric}\left(a, b, c\right)\right) \land \left(\operatorname{symmetric}\left(a, b, c\right) = \operatorname{diagonal}\left(\operatorname{rootWeights}\left(a, b, c\right)\right) \cdot \operatorname{submatrix}\left(\operatorname{quotient}\left(a, b, c\right), \operatorname{supportPermutation}, \operatorname{supportPermutation}\right) \cdot \operatorname{diagonal}\left(\lambda i : \operatorname{Fin}\left(6\right) \mapsto \operatorname{inverse}\left(\operatorname{rootWeights}\left(a, b, c\right)\left(i\right)\right)\right) \land \left(\forall e \in \mathrm{Real},\; \forall z \in \operatorname{Fin}\left(6\right) \to \mathrm{Real},\; z \ne 0 \Rightarrow \left(\operatorname{mulVec}\left(\operatorname{symmetric}\left(a, b, c\right), z\right) = e \cdot z \Rightarrow \left(\operatorname{toQuotientVector}\left(a, b, c, z\right) \ne 0 \land \operatorname{mulVec}\left(\operatorname{quotient}\left(a, b, c\right), \operatorname{toQuotientVector}\left(a, b, c, z\right)\right) = e \cdot \operatorname{toQuotientVector}\left(a, b, c, z\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/SixSupportLaplacianLowRoot.quotient_geometry` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient and uniform low root*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

The energy is a sum over the singleton triangle and the three complementary-pair edges. Positivity forces all six coordinates of a zero-kernel vector to agree. The symmetric form is also a sum of six real squares. The exact similarity and eigenvector transport concern C itself.

**Theorem 1.8 (A negative plane at a small second weight).**

$$\forall a \in \mathrm{Real},\; \forall b \in \mathrm{Real},\; \forall c \in \mathrm{Real},\; 0 < a \Rightarrow \left(0 < b \Rightarrow \left(0 < c \Rightarrow \left(a \le b \Rightarrow \left(b \le 3 \Rightarrow \left(\exists t \in \mathrm{Real},\; \operatorname{Injective}\left(\lambda u : \operatorname{Fin}\left(2\right) \to \mathrm{Real} \mapsto [u\left(0\right),u\left(1\right),0,t \cdot u\left(0\right),t \cdot u\left(1\right),0]\right) \land \left(\forall u \in \operatorname{Fin}\left(2\right) \to \mathrm{Real},\; u \ne 0 \Rightarrow \operatorname{dotProduct}\left([u\left(0\right),u\left(1\right),0,t \cdot u\left(0\right),t \cdot u\left(1\right),0], \operatorname{mulVec}\left(\operatorname{symmetric}\left(a, b, c\right) - 3 \cdot 1, [u\left(0\right),u\left(1\right),0,t \cdot u\left(0\right),t \cdot u\left(1\right),0]\right)\right) < 0\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/SixSupportLaplacianLowRoot.small_second_negative_plane` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient and uniform low root*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

For positive a,b,c with a at most b and b at most three, put p=sqrt(a)sqrt(b)sqrt(c), A=b+c+bc, B=a+c+ac, and t=(A+B+sqrt(a)sqrt(b)+1)/p. The plane consists of (u,v,0,tu,tv,0) in reordered coordinates. Its first two coordinates make the parametrization injective. The two paired diagonal contributions are nonpositive, and the singleton cross term is controlled by the square of u+v. The quadratic form of the symmetric matrix minus three times the identity is strictly negative on every nonzero vector of this plane. No division by a−3 or b−3 occurs, so their equality boundaries are included.

**Theorem 1.9 (Low eigenvalue for every positive real triple).**

$$\forall a \in \mathrm{Real},\; \forall b \in \mathrm{Real},\; \forall c \in \mathrm{Real},\; 0 < a \Rightarrow \left(a \le b \Rightarrow \left(b \le c \Rightarrow \left(\exists e \in \mathrm{Real},\; 0 < e \land \left(e < 3 \land \left(\exists z \in \operatorname{Fin}\left(6\right) \to \mathrm{Real},\; z \ne 0 \land \operatorname{mulVec}\left(\operatorname{quotient}\left(a, b, c\right), z\right) = e \cdot z\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/SixSupportLaplacianLowRoot.positive_real_low_eigenvalue` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient and uniform low root*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

For balanced weights at least one, the proof directly consumes the balanced threshold theorem and its actual quotient eigenpair. For the remaining triples it uses three explicit negative planes for the symmetric matrix shifted by three. When b is at most three, the small-second plane applies. When a is at most three but b is greater than three, the paired b and c coordinates are eliminated and the positive singleton diagonal completes a square; this includes a equal to three. When a is greater than three, the source comparison matrix is nonpositive on vectors (x,sqrt(b)y,sqrt(c)y): its form is minus (b+c)/2 times (x+2sqrt(a)y) squared minus 3/(2a) times (2bc-a(b+c))x squared. Ordering makes the latter coefficient nonnegative, including equal parameters. The positive Schur correction makes the lifted plane strictly negative. This explicit plane is a repository synthesis of the source geometry. A vector in each plane is chosen orthogonal to the simple zero kernel. The real Hermitian spectral expansion then forces a positive eigenvalue below three. The proved similarity transports its nonzero real eigenvector to the actual nonsymmetric quotient C. No ordered-eigenvalue convention or unproved inertia count is assumed.

**Definition 1.10 (The balanced smaller root).**

$$\forall m \in \mathrm{Real},\; \operatorname{balancedLow}\left(m\right) = \frac{m^{2} + 4 \cdot m - m \cdot \operatorname{sqrt}\left(\left(m + 4\right)^{2} - 12\right)}{2}$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/SixSupportLaplacianLowRoot.balancedLow` (`✓ std3`).

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient and uniform low root*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

The discriminant is strictly positive for m at least one.

**Theorem 1.11 (Balanced smallest positive eigenvalue and sharp threshold).**

$$\left(\forall m \in \mathrm{Real},\; 1 \le m \Rightarrow \left(\left(\exists z \in \operatorname{Fin}\left(6\right) \to \mathrm{Real},\; z \ne 0 \land \operatorname{mulVec}\left(\operatorname{quotient}\left(m, m, m\right), z\right) = \operatorname{balancedLow}\left(m\right) \cdot z\right) \land \left(0 < \operatorname{balancedLow}\left(m\right) \land \left(\operatorname{balancedLow}\left(m\right) < m \land \left(\frac{3 \cdot m}{m + 4} < \operatorname{balancedLow}\left(m\right) \land \left(\operatorname{balancedLow}\left(m\right) < 3 \land \left(\operatorname{balancedLow}\left(m\right) = \frac{6 \cdot m}{m + 4 + \operatorname{sqrt}\left(\left(m + 4\right)^{2} - 12\right)} \land \left(\left(\forall e \in \mathrm{Real},\; 0 < e \Rightarrow \left(\forall z \in \operatorname{Fin}\left(6\right) \to \mathrm{Real},\; z \ne 0 \Rightarrow \left(\operatorname{mulVec}\left(\operatorname{quotient}\left(m, m, m\right), z\right) = e \cdot z \Rightarrow \operatorname{balancedLow}\left(m\right) \le e\right)\right)\right) \land \left(\left(\forall x \in \mathrm{Real},\; \operatorname{det}\left(x \cdot 1 - \operatorname{quotient}\left(m, m, m\right)\right) = x \cdot \left(x - m^{2} - m\right) \cdot \left(x^{2} - \left(m^{2} + 4 \cdot m\right) \cdot x + 3 \cdot m^{2}\right)^{2}\right) \land \left(\operatorname{balancedLow}\left(m\right) < m^{2} + m \land m^{2} + m < \frac{m^{2} + 4 \cdot m + m \cdot \operatorname{sqrt}\left(\left(m + 4\right)^{2} - 12\right)}{2}\right)\right)\right)\right)\right)\right)\right)\right)\right)\right) \land \left(\operatorname{Tendsto}\left(\operatorname{balancedLow}, \operatorname{atTop}, \operatorname{nhds}\left(3\right)\right) \land \left(\operatorname{Tendsto}\left(\lambda n : \mathrm{Nat} \mapsto \operatorname{balancedLow}\left(\operatorname{realCast}\left(n\right)\right), \operatorname{atTop}, \operatorname{nhds}\left(3\right)\right) \land \left(\forall K \in \mathrm{Real},\; K < 3 \Rightarrow \left(\exists n \in \mathrm{Nat},\; 1 \le n \land \left(K < \operatorname{balancedLow}\left(\operatorname{realCast}\left(n\right)\right) \land \left(\exists z \in \operatorname{Fin}\left(6\right) \to \mathrm{Real},\; z \ne 0 \land \operatorname{mulVec}\left(\operatorname{quotient}\left(\operatorname{realCast}\left(n\right), \operatorname{realCast}\left(n\right), \operatorname{realCast}\left(n\right)\right), z\right) = \operatorname{balancedLow}\left(\operatorname{realCast}\left(n\right)\right) \cdot z\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/SixSupportLaplacianLowRoot.balanced_sharp_threshold` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient and uniform low root*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

The factorization gives zero, m squared plus m, and the two quadratic roots, each quadratic root counted twice. For q_m(x)=x squared minus (m squared plus 4m)x plus 3m squared, q_m(0)=3m squared is positive, q_m(m)=minus m cubed is negative, and q_m(3)=9−12m is negative when m is at least one. The smaller quadratic root lies between zero and m; the larger root exceeds m squared plus m. A nonzero real symmetric eigenvector is constructed and transported by the proved similarity to C. Rationalization gives the strict lower bound 3m/(m+4), while the upper bound is three. The lower bound tends to three, so squeezing proves the real limit and the positive-integer subsequence limit. For every K below three there is a positive integer m whose smallest positive quotient eigenvalue exceeds K; every other positive real quotient eigenvalue then also exceeds K. Thus no constant smaller than three bounds the smallest positive quotient eigenvalues uniformly. The positive-real theorem supplies the same uniform bound for unequal ordered weights; the integer consequence follows by specializing its parameters.

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
