# A nonuniform fixed point on every even hypercube

## Abstract

For every even dimension d at least four, the all-plus spin-coupled Grover operator has a nonzero fixed vector with nonconstant position weights. A product of signed coordinate-pair indicators supplies an explicit vector on three adjacent Hamming layers.

**Definition 1.1 (The paired sign function).**

$$\forall m \in \mathbb{N},\; \forall s \in \operatorname{Finset}\left(\operatorname{Fin}\left(2 \cdot m\right)\right),\; \operatorname{f}\left(m, s\right) = \prod_{j: \operatorname{Fin}\left(m\right)} (\operatorname{Set}.\operatorname{indicator}\left((s: \operatorname{Set}\left(\operatorname{Fin}\left(2 \cdot m\right)\right)), (1: \operatorname{Fin}\left(2 \cdot m\right) \to \mathbb{C}), \operatorname{finProdFinEquiv}.\operatorname{trans}\left(\operatorname{finCongr}\left(\operatorname{Nat}.\operatorname{mul}_{comm}\left(m, 2\right)\right)\right)\left((j, 0)\right)\right) - \operatorname{Set}.\operatorname{indicator}\left((s: \operatorname{Set}\left(\operatorname{Fin}\left(2 \cdot m\right)\right)), (1: \operatorname{Fin}\left(2 \cdot m\right) \to \mathbb{C}), \operatorname{finProdFinEquiv}.\operatorname{trans}\left(\operatorname{finCongr}\left(\operatorname{Nat}.\operatorname{mul}_{comm}\left(m, 2\right)\right)\right)\left((j, 1)\right)\right))$$

*Formalization.* `D5/S3/Quantum/Dynamics/SpinCoupledEvenHypercubeGroverFixedPoint.f` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ce Wang (2026). *Spectral Criterion for Disorder-Free Localization of Quantum Walks on Hypercube: QBN Approach*. URL: <https://arxiv.org/abs/2609.07267v1>.

*Commentary.*

The equivalence finProdFinEquiv followed by finCongr (Nat.mul_comm m 2) sends (j, b) to coordinate 2j + b. Finsets are coerced to sets in Set.indicator. The function (1 : Fin (2*m) -> Complex) is the constant function one, so each factor is the indicator of coordinate 2j minus that of coordinate 2j+1. The product is zero unless the vertex contains exactly one coordinate from each pair.

**Definition 1.2 (The three-layer amplitudes).**

$$\forall m \in \mathbb{N},\; \forall z \in \mathbb{C},\; \forall c \in \mathbb{C},\; \forall s \in \operatorname{Finset}\left(\operatorname{Fin}\left(2 \cdot m\right)\right),\; \forall k \in \operatorname{Fin}\left(2 \cdot m\right),\; \operatorname{u}\left(m, z, c, s, k\right) = \operatorname{ite}\left((\operatorname{Finset}.\operatorname{card}\left(s\right) = m), \operatorname{ite}\left((k \in s), c \cdot \operatorname{f}\left(m, s\right), z \cdot c \cdot \operatorname{f}\left(m, s\right)\right), \operatorname{ite}\left(((\operatorname{Finset}.\operatorname{card}\left(s\right) = m - 1) \land (\neg (k \in s))), z^{m + 1} \cdot c \cdot \operatorname{f}\left(m, \operatorname{symmDiff}\left(s, \left\{k\right\}\right)\right), \operatorname{ite}\left(((\operatorname{Finset}.\operatorname{card}\left(s\right) = m + 1) \land (k \in s)), z^{m} \cdot c \cdot \operatorname{f}\left(m, \operatorname{symmDiff}\left(s, \left\{k\right\}\right)\right), 0\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Dynamics/SpinCoupledEvenHypercubeGroverFixedPoint.u` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ce Wang (2026). *Spectral Criterion for Disorder-Free Localization of Quantum Walks on Hypercube: QBN Approach*. URL: <https://arxiv.org/abs/2609.07267v1>.

*Commentary.*

The parameters z and c are arbitrary complex numbers in this definition. The operation ite is Lean's conditional; the first test has priority, followed by the lower and upper layer tests. Here m-1 is subtraction in the natural numbers, hence is truncated at zero. For m at least two and z^(2*m)=-1, m*(1+z)*c=1, the sum of the coin amplitudes at a vertex equals f, and the amplitudes satisfy the edge recurrence. The same z and c are used on every layer.

**Definition 1.3 (The amplitude coefficient).**

$$\forall m \in \mathbb{N},\; \operatorname{c}\left(m\right) = \frac{1}{(m: \mathbb{C}) \cdot (1 + \operatorname{PositivePauliClockOrder}.\operatorname{scalarPhase}\left(1, \frac{\operatorname{Real}.\operatorname{pi}}{(2 \cdot m: \mathbb{R})}, 1\right))}$$

*Formalization.* `D5/S3/Quantum/Dynamics/SpinCoupledEvenHypercubeGroverFixedPoint.c` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ce Wang (2026). *Spectral Criterion for Disorder-Free Localization of Quantum Walks on Hypercube: QBN Approach*. URL: <https://arxiv.org/abs/2609.07267v1>.

*Commentary.*

Here z is PositivePauliClockOrder.scalarPhase 1 (Real.pi/(2*m)) 1, the phase exp(-i*pi/(2*m)). For m at least two, the real part of this phase is cos(pi/(2*m)) and is positive. Thus 1+z is nonzero, and c(m) is nonzero and satisfies m*(1+z)*c(m)=1. All division here is division in Complex.

**Definition 1.4 (The all-plus reduced Grover operator).**

$$\forall d \in \mathbb{N},\; \forall v \in \operatorname{Finset}\left(\operatorname{Fin}\left(d\right)\right) \to \operatorname{Fin}\left(d\right) \to \mathbb{C},\; \forall t \in \operatorname{Finset}\left(\operatorname{Fin}\left(d\right)\right),\; \forall k \in \operatorname{Fin}\left(d\right),\; \operatorname{W}\left(d, v, t, k\right) = \operatorname{Complex}.\operatorname{exp}\left(-\frac{(\operatorname{Real}.\operatorname{pi}: \mathbb{C}) \cdot (\operatorname{Finset}.\operatorname{card}\left(\operatorname{symmDiff}\left(t, \left\{k\right\}\right)\right): \mathbb{C})}{(d: \mathbb{C})} \cdot \operatorname{Complex}.\operatorname{I}\right) \cdot (\frac{2}{(d: \mathbb{C})} \cdot (\sum_{j: \operatorname{Fin}\left(d\right)} v\left(\operatorname{symmDiff}\left(t, \left\{k\right\}\right), j\right)) - v\left(\operatorname{symmDiff}\left(t, \left\{k\right\}\right), k\right))$$

*Formalization.* `D5/S3/Quantum/Dynamics/SpinCoupledEvenHypercubeGroverFixedPoint.W` (`✓ std3`).

*Citation.* Ce Wang (2026). *Spectral Criterion for Disorder-Free Localization of Quantum Walks on Hypercube: QBN Approach*. URL: <https://arxiv.org/abs/2609.07267v1>.

*Commentary.*

Section 3, page 6, Proposition 3.4 defines the reduced evolution operator; Section 4, page 12, specifies C_k = (2/d) sum_j |e_k><e_j| - |e_k><e_k| and phi_sigma = |sigma|*pi/d. The all-plus restriction acts at output vertex t and coin coordinate k through predecessor symmDiff t {k}. The phase uses the predecessor's cardinality. The position carrier Finset (Fin d) enumerates all vertices and Fin d enumerates the d coin coordinates. The Grover coin contribution is (2/d) times the sum of all predecessor coin amplitudes, minus the kth predecessor amplitude. The casts to Complex and the anonymous summation index are shown explicitly.

**Definition 1.5 (Wang's conjecture).**

$$claim \Leftrightarrow (\forall d \in \mathbb{N},\; (\operatorname{Even}\left(d\right)) \Rightarrow ((4 \le d) \Rightarrow (\exists v \in \operatorname{Finset}\left(\operatorname{Fin}\left(d\right)\right) \to \operatorname{Fin}\left(d\right) \to \mathbb{C},\; (v \ne 0) \land ((\operatorname{W}\left(d, v\right) = v) \land (\exists s \in \operatorname{Finset}\left(\operatorname{Fin}\left(d\right)\right),\; \exists t \in \operatorname{Finset}\left(\operatorname{Fin}\left(d\right)\right),\; \sum_{k: \operatorname{Fin}\left(d\right)} \left\lVert v\left(s, k\right) \right\rVert^{2} \ne \sum_{k: \operatorname{Fin}\left(d\right)} \left\lVert v\left(t, k\right) \right\rVert^{2})))))$$

*Formalization.* `D5/S3/Quantum/Dynamics/SpinCoupledEvenHypercubeGroverFixedPoint.claim` (`✓ std3`).

*Citation.* Ce Wang (2026). *Spectral Criterion for Disorder-Free Localization of Quantum Walks on Hypercube: QBN Approach*. URL: <https://arxiv.org/abs/2609.07267v1>.

*Commentary.*

Page 13, Conjecture 4.1: "For every even $d \geq 4$, the spin-coupled Grover walk on the $d$-dimensional hypercube with coupling $\phi_{\sigma} = \lvert\sigma\rvert\pi/d$ and all $+1$ spin configuration exhibits disorder-free localization. Equivalently, the reduced evolution operator $\widetilde{W}_{\mathbf{s}}$ possesses a fixed point whose position distribution is non-uniform."

The predicate claim encodes the source's equivalent fixed-point clause. The letters v, s and t denote the coin-amplitude family and two vertices. Its position weight at s is the real sum of squared complex norms; dividing all weights by the total nonzero squared norm preserves their inequality. There is no extra hypothesis on the dimension or the vector.

**Theorem 1.6 (The fixed-point clause holds).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/SpinCoupledEvenHypercubeGroverFixedPoint.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ce Wang (2026). *Spectral Criterion for Disorder-Free Localization of Quantum Walks on Hypercube: QBN Approach*. URL: <https://arxiv.org/abs/2609.07267v1>.

*Commentary.*

Write d=2*m with m at least two, put z=PositivePauliClockOrder.scalarPhase 1 (Real.pi/(2*m)) 1, and take u(m, z, c(m)). Pair cancellation makes the sum of f over all one-coordinate neighbours zero, while f vanishes off the middle layer. These facts give sum_k u(s,k)=f(s). The middle, lower and upper layer branches satisfy z^|s|*((1/m)*f(s)-u(s,k))=u(symmDiff s {k},k); the remaining branches vanish. Since z^(2*m)=-1, this is exactly W u=u. At the vertex containing all even coordinates, f=1 and an even-coordinate amplitude is c(m), which is nonzero; all amplitudes at the empty vertex vanish. Hence the first position weight is strictly positive and the second is zero. Page 11, Corollary 4.4 (cor:fixed_point_DFL) then implies disorder-free localization by normalizing the fixed point. This last implication uses the paper's spectral criterion; the displayed Lean proposition is the equivalent fixed-point clause.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/SpinCoupledEvenHypercubeGroverFixedPoint.W`
- Truth anchor: `D5/S3/Quantum/Dynamics/SpinCoupledEvenHypercubeGroverFixedPoint.c`
- Truth anchor: `D5/S3/Quantum/Dynamics/SpinCoupledEvenHypercubeGroverFixedPoint.claim`
- Truth anchor: `D5/S3/Quantum/Dynamics/SpinCoupledEvenHypercubeGroverFixedPoint.f`
- Truth anchor: `D5/S3/Quantum/Dynamics/SpinCoupledEvenHypercubeGroverFixedPoint.result`
- Truth anchor: `D5/S3/Quantum/Dynamics/SpinCoupledEvenHypercubeGroverFixedPoint.u`
- Dependency: [D5/S3/Quantum/Dynamics/PositivePauliClockOrder](PositivePauliClockOrder.md)
