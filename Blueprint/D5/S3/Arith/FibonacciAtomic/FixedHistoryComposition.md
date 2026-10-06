# Fixed Composition in an Actual Clifford History Fiber

## Abstract

A positive natural composition and a single actual Clifford history are jointly realizable exactly when the rational quarter-counts are integral, all eight integer edge counts are nonnegative, and their undirected positive support is connected to the initial state 00.

Source is the native FreeMagma Bool: true denotes alpha, false beta. The source remains a nonempty ordered binary tree, with its brackets retained. Substitution sends alpha to beta and beta to the ordered pair (beta,alpha). Composition counts the leaves of each label.

The carrier is the actual real CliffordAlgebra for Q(a,b)=a*a+a*b-b*b. A and B are the canonical vector images. E multiplies their images in original leaf order; W3(t)=(E(t),E(rho(t)),E(rho(rho(t)))). S=B*A, D=A+B, g=(A,B,S), h=(B,S,D), and R00=1, R10=g, R01=h, R11=g*h. L(u,v,w)=((-1)^v*S^(2u),(-1)^w*S^(2v),(-1)^u*S^(2w)).

**Theorem 1.1 (Complete same-source criterion).**

$$\forall u \in \mathbb{Z},\; \forall v \in \mathbb{Z},\; \forall w \in \mathbb{Z},\; \forall p \in \left\{0, 1\right\},\; \forall q \in \left\{0, 1\right\},\; \forall ac \in \mathbb{N},\; \forall bc \in \mathbb{N},\; 1 \le ac + bc \Rightarrow \left(\left(\exists t \in Source,\; \left(W_{3}\right)\left(t\right) = \operatorname{L}\left(u, v, w\right) \cdot R_{(p, q)} \land \operatorname{c}\left(t\right) = (ac, bc)\right) \Leftrightarrow \left(\exists X \in \mathbb{Z},\; \exists Y \in \mathbb{Z},\; \left(\left(X = \frac{ac - p - 2 \cdot w + 2 \cdot u}{4} \land Y = \frac{bc - q - 2 \cdot u + 2 \cdot v}{4}\right) \land \left(\forall e \in (\left\{0, 1\right\} \times \left\{0, 1\right\}) \times \left\{0, 1\right\},\; 0 \le \operatorname{edgeCounts}\left(u, v, w, X, Y, p, q\right)\left(e\right)\right)\right) \land \left(\forall e \in (\left\{0, 1\right\} \times \left\{0, 1\right\}) \times \left\{0, 1\right\},\; 0 < \operatorname{edgeCounts}\left(u, v, w, X, Y, p, q\right)\left(e\right) \Rightarrow \left(\operatorname{Nonempty}\left(\operatorname{Path}\left(\operatorname{Symmetrify}\left(\operatorname{PositiveSupport}\left(\operatorname{edgeCounts}\left(u, v, w, X, Y, p, q\right)\right)\right), (0, 0), \operatorname{src}\left(e\right)\right)\right) \land \operatorname{Nonempty}\left(\operatorname{Path}\left(\operatorname{Symmetrify}\left(\operatorname{PositiveSupport}\left(\operatorname{edgeCounts}\left(u, v, w, X, Y, p, q\right)\right)\right), (0, 0), \operatorname{step}\left(\operatorname{src}\left(e\right), \operatorname{label}\left(e\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/FixedHistoryComposition.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All u,v,w are integers; p,q are Boolean bits interpreted as 0 or 1. All ac,bc are natural numbers with ac+bc>=1; either coordinate may be zero. Criterion means that the rational numbers X=(ac-p-2w+2u)/4 and Y=(bc-q-2u+2v)/4 have integer witnesses, all eight counts below are nonnegative, and every endpoint of every positive-count edge is connected to 00 in the undirected positive support. Unused ambient vertices impose no connectivity requirement.

The alpha counts at departures 00,10,01,11 are X+w-u+p, X+w, X, X-u. The beta counts at departures 00,01,10,11 are Y+u+q*(1-p), Y, Y-v+p*q, Y+u-v. Alpha toggles the first bit; beta toggles the second.

$\begin{aligned}x_{00} = \operatorname{edgeCounts}\left(u, v, w, X, Y, p, q\right)\left(((0, 0), 1)\right) = X + w - u + p\\x_{10} = \operatorname{edgeCounts}\left(u, v, w, X, Y, p, q\right)\left(((1, 0), 1)\right) = X + w\\x_{01} = \operatorname{edgeCounts}\left(u, v, w, X, Y, p, q\right)\left(((0, 1), 1)\right) = X\\x_{11} = \operatorname{edgeCounts}\left(u, v, w, X, Y, p, q\right)\left(((1, 1), 1)\right) = X - u\\y_{00} = \operatorname{edgeCounts}\left(u, v, w, X, Y, p, q\right)\left(((0, 0), 0)\right) = Y + u + q \cdot \left(1 - p\right)\\y_{01} = \operatorname{edgeCounts}\left(u, v, w, X, Y, p, q\right)\left(((0, 1), 0)\right) = Y\\y_{10} = \operatorname{edgeCounts}\left(u, v, w, X, Y, p, q\right)\left(((1, 0), 0)\right) = Y - v + p \cdot q\\y_{11} = \operatorname{edgeCounts}\left(u, v, w, X, Y, p, q\right)\left(((1, 1), 0)\right) = Y + u - v\end{aligned}$

In the displayed criterion, Kind=State times the Boolean leaf label, src and label are its two projections, and Path is the finite quiver path type. The label 1 denotes alpha and 0 denotes beta. Symmetrify allows each positive edge in either direction; a zero-length path retains the initial vertex 00. The positive support and its step function are specified by:

$\begin{aligned}State = \left\{0, 1\right\} \times \left\{0, 1\right\}\\Kind = (\left\{0, 1\right\} \times \left\{0, 1\right\}) \times \left\{0, 1\right\}\\\forall z \in \left\{0, 1\right\} \times \left\{0, 1\right\},\; \forall b \in \left\{0, 1\right\},\; \operatorname{src}\left((z, b)\right) = z \land \operatorname{label}\left((z, b)\right) = b\\\forall r \in \left\{0, 1\right\},\; \forall s \in \left\{0, 1\right\},\; \operatorname{step}\left((r, s), 1\right) = (1 - r, s) \land \operatorname{step}\left((r, s), 0\right) = (r, 1 - s)\\\forall m \in (\left\{0, 1\right\} \times \left\{0, 1\right\}) \times \left\{0, 1\right\} \to \mathbb{Z},\; \forall s \in \left\{0, 1\right\} \times \left\{0, 1\right\},\; \forall z \in \left\{0, 1\right\} \times \left\{0, 1\right\},\; \operatorname{Nonempty}\left(\operatorname{Hom}\left(\operatorname{PositiveSupport}\left(m\right), s, z\right)\right) \Leftrightarrow \left(\exists b \in \left\{0, 1\right\},\; \operatorname{step}\left(s, b\right) = z \land 0 < m\left((s, b)\right)\right)\end{aligned}$

The integer witness equations are ac=4X+2w-2u+p and bc=4Y+2u-2v+q, proved equivalent to the rational quotients. A maximum path whose edge counts are bounded by the capacities reaches the prescribed terminal by its residual divergence. Any remaining capacity is balanced. A boundary crossing in the original weak support supplies a visited splice vertex; a nonempty residual closed path would increase the maximum length. Residual connectivity is not assumed.

The same chronological path supplies the leaf word, all three actual Clifford coordinates and the composition. Necessity identifies parameters by actual Clifford reflection, and sufficiency brackets that same nonempty word into an actual Source. Parallel occurrences are retained by their exact chronological counts. Flow balance alone is insufficient: unit history at composition (4,0) gives two disconnected alpha cycles.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/FixedHistoryComposition.result`
- Dependency: [D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport](GenealogicalFiberTransport.md)
