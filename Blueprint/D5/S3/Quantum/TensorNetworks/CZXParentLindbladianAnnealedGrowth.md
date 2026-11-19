# Four-letter annealed row growth

## Abstract

Quantitative annealed Euclidean row growth for the four CZX transfer letters.

The rows are real two-dimensional Euclidean vectors. Each letter is chosen uniformly from two matrix types and two signs. Products retain their natural left-to-right order, and the empty product is the identity. The bound controls the first norm moment with a strict improvement over the square root of its second-moment multiplier.

**Definition 1.1 (Euclidean rows).**

$$\operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianAnnealedGrowth}.{Row} = \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(2\right)\right)$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianAnnealedGrowth.Row` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The carrier is the standard real Euclidean space on two coordinates.

**Definition 1.2 (The four-letter alphabet).**

$$\operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianAnnealedGrowth}.{Letter} = \operatorname{Prod}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right)\right)$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianAnnealedGrowth.Letter` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The first coordinate selects the matrix type. The second selects the signs +1 and -1.

**Definition 1.3 (The transfer matrices).**

$$\forall (rho: \mathbb{R}), \forall (c: \operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianAnnealedGrowth}.{Letter}), \operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianAnnealedGrowth}.{letter}\left(rho, c\right) = (\lambda (e: \mathbb{R}) \mapsto (\operatorname{ite}\left(\operatorname{Prod}.{fst}\left(c\right) = 0, \begin{pmatrix}(1) + (rho)&((2) \cdot (e)) \cdot (rho)\\0&(1) - (rho)\end{pmatrix}, \begin{pmatrix}(1) - (rho)&0\\((2) \cdot (e)) \cdot (rho)&(1) + (rho)\end{pmatrix}\right)))\left(\operatorname{ite}\left(\operatorname{Prod}.{snd}\left(c\right) = 0, 1, -1\right)\right)$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianAnnealedGrowth.letter` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For e=+1 or -1, the type-zero letter is [[1+rho,2e rho],[0,1-rho]], and the type-one letter is [[1-rho,0],[2e rho,1+rho]]. Both signs and both types have weight one quarter.

**Definition 1.4 (Right matrix action).**

$$\forall (v: \operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianAnnealedGrowth}.{Row}), \forall (M: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{R}\right)), \operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianAnnealedGrowth}.{rowAction}\left(v, M\right) = \operatorname{WithLp}.{toLp}\left(2, \operatorname{Matrix}.{vecMul}\left(\operatorname{WithLp}.{ofLp}\left(v\right), M\right)\right)$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianAnnealedGrowth.rowAction` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The ordinary row-matrix product is transported to the Euclidean carrier. Its norm is sqrt(a squared plus b squared), rather than the supremum norm on coordinate functions.

**Definition 1.5 (Ordered words).**

$$\forall (rho: \mathbb{R}), (\forall (w: (\operatorname{Fin}\left(0\right)) \to (\operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianAnnealedGrowth}.{Letter})), \operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianAnnealedGrowth}.{word}\left(rho, 0, w\right) = (1: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{R}\right))) \land (\forall (k: \mathbb{N}), \forall (w: (\operatorname{Fin}\left((k) + (1)\right)) \to (\operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianAnnealedGrowth}.{Letter})), \operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianAnnealedGrowth}.{word}\left(rho, (k) + (1), w\right) = (\operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianAnnealedGrowth}.{word}\left(rho, k, \operatorname{Fin}.{init}\left(w\right)\right)) \cdot (\operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianAnnealedGrowth}.{letter}\left(rho, w\left(\operatorname{Fin}.{last}\left(k\right)\right)\right)))$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianAnnealedGrowth.word` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A length k+1 word is its length k prefix followed by its last letter on the right. Consequently W_k=S(w_0)...S(w_(k-1)) in increasing index order, with W_0=I.

**Definition 1.6 (Normalized uniform average).**

$$\forall (rho: \mathbb{R}), \forall (k: \mathbb{N}), \forall (v: \operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianAnnealedGrowth}.{Row}), \operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianAnnealedGrowth}.{average}\left(rho, k, v\right) = ((\frac{1}{4})^{k}) \cdot (\sum_{w: (\operatorname{Fin}\left(k\right)) \to (\operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianAnnealedGrowth}.{Letter})} \operatorname{norm}\left(\operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianAnnealedGrowth}.{rowAction}\left(v, \operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianAnnealedGrowth}.{word}\left(rho, k, w\right)\right)\right))$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianAnnealedGrowth.average` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The normalization is 4 to the power minus k, and the sum ranges over every function from Fin k to the four-letter alphabet. This includes the unique empty word and every real row, including zero.

**Definition 1.7 (Explicit growth factor).**

$$\forall (rho: \mathbb{R}), \operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianAnnealedGrowth}.{growthFactor}\left(rho\right) = (\operatorname{Real}.{sqrt}\left((1) + ((3) \cdot ((rho)^{2}))\right)) - (\frac{((rho)^{2}) \cdot (((1) - (rho))^{2})}{(2) \cdot (((1) + ((3) \cdot (rho)))^{3})})$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianAnnealedGrowth.growthFactor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The factor q is sqrt(1+3 rho squared) minus rho squared times (1-rho) squared divided by 2(1+3rho) cubed.

**Theorem 1.8 (All-length Euclidean growth estimate).**

$$\forall (rho: \mathbb{R}), (0 < rho) \Rightarrow ((rho < 1) \Rightarrow (\forall (k: \mathbb{N}), \forall (v: \operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianAnnealedGrowth}.{Row}), (0 < \operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianAnnealedGrowth}.{growthFactor}\left(rho\right)) \land ((\operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianAnnealedGrowth}.{growthFactor}\left(rho\right) < \operatorname{Real}.{sqrt}\left((1) + ((3) \cdot ((rho)^{2}))\right)) \land ((\operatorname{Real}.{sqrt}\left((1) + ((3) \cdot ((rho)^{2}))\right) < 2) \land ((1 < \operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianAnnealedGrowth}.{growthFactor}\left(rho\right)) \land (\operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianAnnealedGrowth}.{average}\left(rho, k, v\right) \le ((\operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianAnnealedGrowth}.{growthFactor}\left(rho\right))^{k}) \cdot (\operatorname{norm}\left(v\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianAnnealedGrowth.annealed_growth` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every rho strictly between zero and one, every natural length k, and every real row v, the normalized average is at most q to the power k times the Euclidean norm of v. The factor satisfies 1<q<sqrt(1+3rho squared)<2, so this is a growth estimate.

Write s=a squared+b squared, d=a squared-b squared, mu=1+3rho squared, and K=1+3rho. The four squared output norms Y have mean mu s and variance 4rho squared(1-rho) squared s squared+16rho cubed d squared. Each lies between zero and K squared s. On a unit row, the quantitative inequality sqrt(y)<=sqrt(mu)+(y-mu)/(2sqrt(mu))-(y-mu) squared/(8K cubed) applies even at y=0. To see this, set u=sqrt(y), z=sqrt(mu). The remainder has numerator (u-z) squared times [4K cubed-z(u+z) squared], and the bracket equals 4K squared(K-z)+z(2K-u-z)(2K+u+z), which is nonnegative. Averaging cancels the linear term; the positive variance floor supplies the explicit subtraction in q. Positive homogeneity extends the estimate to arbitrary rows. Splitting a word into its prefix and final letter applies that estimate to the actual prefix row at every induction step.

At k=0 the bound is equality for every row, and at v=0 it is equality at every length. At rho=0 the formula gives q=1, and at rho=1 it gives q=2; the strict interior inequalities exclude these endpoints.

Prospective CZX trace-distance consequence.

The intended quantum application uses exactly the original even-window rate-one CZX evolution, n=2m>=4, t>0, rho=exp(-t), A0=4^(-m)(I+tensorX(n)), and sigma=4^(-m)(I+2^(1-m)czxUnitary(n)). For Delta=FiniteTraceDistance.traceNorm(evolution(n,t,A0)-sigma)/2, the intended consequence is Delta<=2sqrt(2)(q(rho)/2)^m. This quantum statement is not established by the present formal theorem.

The missing formal steps are the actual finite-time coefficient action and exponential product on the original even starts; the all-size cyclic pair bijection and variable-real ordered transfer contraction, retaining both ordered windows when m=2; the canonical trace-norm evaluation on U diag(f), with the exact normalization and stationary subtraction; and combination on those original quantum endpoints. A projective pressure operator and spectral-radius limit are separate questions. The improved exponential base comes with a larger prefactor than the older Hilbert-Schmidt asymptotic estimate, so it does not imply dominance at every finite size.

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianAnnealedGrowth.Letter`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianAnnealedGrowth.Row`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianAnnealedGrowth.annealed_growth`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianAnnealedGrowth.average`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianAnnealedGrowth.growthFactor`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianAnnealedGrowth.letter`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianAnnealedGrowth.rowAction`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianAnnealedGrowth.word`
