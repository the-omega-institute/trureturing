# Finite-Path Coherence

## Abstract

Finite sequential qubit channels multiply coherence; its phase, attenuation, and closed-path gauge laws follow.

Let M be the complex two-by-two matrices and Q the completely positive, trace-preserving channels on them. Matrix action converts through CStarMatrix. The imaginary unit is I. The following notation fixes the Hermitian sector and edge coefficient.

$\operatorname{sourceMatrix}\left(a, b, d\right) = \begin{pmatrix}a&b\\\overline{b}&d\end{pmatrix} \land \operatorname{coefficient}\left(v, theta\right) = \operatorname{ofReal}\left(v\right) \cdot \operatorname{exp}\left(\operatorname{ofReal}\left(theta\right) \cdot I\right)$

A quiver has an arbitrary vertex type V and arbitrary arrow types Hom(x,y). Family(T) below means an assignment in T to every arrow, with its endpoints implicit. Path(i,j) contains every finite directed path, including the empty path. Weight is the ordered product of edge values, with empty product one; addWeight is the sum, with empty sum zero. The path channel applies each edge after the preceding path; its empty case is edgeChannel(1,0).

Sequential application is licensed by independently prepared auxiliary resources, or by a factorization already established in the physical model. Correlated resource reuse does not by itself supply this factorization.

**Theorem 1.1 (Canonical Edge Action).**

$$\forall v \in \mathbb{R},\; \forall theta \in \mathbb{R},\; \left(0 < v \land v \le 1\right) \Rightarrow \left(\forall rho \in M,\; \operatorname{matrixAction}\left(\operatorname{edgeChannel}\left(v, theta\right), rho\right) = \begin{pmatrix}rho_{0,0}&\operatorname{coefficient}\left(v, theta\right) \cdot rho_{0,1}\\\overline{\operatorname{coefficient}\left(v, theta\right)} \cdot rho_{1,0}&rho_{1,1}\end{pmatrix}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Decoherence/FinitePathCoherence.edgeChannel_action` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The channel is supplied by the finite Kraus construction. Its two Kraus matrices are diagonal, with diagonals (coefficient(v,theta),1) and (sqrt(1-v squared),0). Normalization and the displayed action hold for every admissible visibility and every real phase.

**Theorem 1.2 (Sequential Path Action).**

$$\forall V \in Type,\; \forall H \in \operatorname{Quiver}\left(V\right),\; \forall C \in \operatorname{Family}\left(Q\right),\; \forall z \in \operatorname{Family}\left(\mathbb{C}\right),\; \left(\forall x \in V,\; \forall y \in V,\; \forall e \in \operatorname{Hom}\left(x, y\right),\; \forall a \in \mathbb{R},\; \forall d \in \mathbb{R},\; \forall b \in \mathbb{C},\; \operatorname{matrixAction}\left(\operatorname{C}\left(e\right), \operatorname{sourceMatrix}\left(a, b, d\right)\right) = \operatorname{sourceMatrix}\left(a, \operatorname{z}\left(e\right) \cdot b, d\right)\right) \Rightarrow \left(\forall i \in V,\; \forall j \in V,\; \forall p \in \operatorname{Path}\left(i, j\right),\; \forall a \in \mathbb{R},\; \forall d \in \mathbb{R},\; \forall b \in \mathbb{C},\; \operatorname{matrixAction}\left(\operatorname{pathChannel}\left(C, p\right), \operatorname{sourceMatrix}\left(a, b, d\right)\right) = \operatorname{sourceMatrix}\left(a, \operatorname{weight}\left(z, p\right) \cdot b, d\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Decoherence/FinitePathCoherence.path_channel_action` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The edge premise specifies the whole Hermitian matrix action. Channel composition preserves both diagonal entries and multiplies the upper coherence by the path product; the lower entry is its conjugate.

**Theorem 1.3 (Polar Coordinates and Vertex Gauge).**

$$\forall V \in Type,\; \forall H \in \operatorname{Quiver}\left(V\right),\; \forall C \in \operatorname{Family}\left(Q\right),\; \forall v \in \operatorname{Family}\left(\mathbb{R}\right),\; \forall theta \in \operatorname{Family}\left(\mathbb{R}\right),\; \left(\left(\forall x \in V,\; \forall y \in V,\; \forall e \in \operatorname{Hom}\left(x, y\right),\; 0 < \operatorname{v}\left(e\right) \land \operatorname{v}\left(e\right) \le 1\right) \land \left(\forall x \in V,\; \forall y \in V,\; \forall e \in \operatorname{Hom}\left(x, y\right),\; \forall a \in \mathbb{R},\; \forall d \in \mathbb{R},\; \forall b \in \mathbb{C},\; \operatorname{matrixAction}\left(\operatorname{C}\left(e\right), \operatorname{sourceMatrix}\left(a, b, d\right)\right) = \operatorname{sourceMatrix}\left(a, \operatorname{coefficient}\left(\operatorname{v}\left(e\right), \operatorname{theta}\left(e\right)\right) \cdot b, d\right)\right)\right) \Rightarrow \left(\forall i \in V,\; \forall j \in V,\; \forall p \in \operatorname{Path}\left(i, j\right),\; \forall a \in \mathbb{R},\; \forall d \in \mathbb{R},\; \forall b \in \mathbb{C},\; \operatorname{let} \left(\forall x \in V,\; \forall y \in V,\; \forall e \in \operatorname{Hom}\left(x, y\right),\; \operatorname{z}\left(e\right) = \operatorname{coefficient}\left(\operatorname{v}\left(e\right), \operatorname{theta}\left(e\right)\right)\right) \land zP = \operatorname{weight}\left(z, p\right); \operatorname{matrixAction}\left(\operatorname{pathChannel}\left(C, p\right), \operatorname{sourceMatrix}\left(a, b, d\right)\right) = \operatorname{sourceMatrix}\left(a, zP \cdot b, d\right) \land \left(zP \ne 0 \land \left(\left\lVert zP \right\rVert = \operatorname{weight}\left(v, p\right) \land \left(\left(0 < \left\lVert zP \right\rVert \land \left\lVert zP \right\rVert \le 1\right) \land \left(\operatorname{angle}\left(\operatorname{arg}\left(zP\right)\right) = \operatorname{angle}\left(\operatorname{addWeight}\left(theta, p\right)\right) \land \left(-\operatorname{log}\left(\left\lVert zP \right\rVert\right) = \operatorname{addWeight}\left((e\mapsto-\operatorname{log}\left(\operatorname{v}\left(e\right)\right)), p\right) \land \left(zP = \operatorname{ofReal}\left(\left\lVert zP \right\rVert\right) \cdot \operatorname{exp}\left(\operatorname{ofReal}\left(\operatorname{arg}\left(zP\right)\right) \cdot I\right) \land \left(\forall alpha \in V\to\mathbb{R},\; \operatorname{let} \left(\forall x \in V,\; \forall y \in V,\; \forall e \in \operatorname{Hom}\left(x, y\right),\; \operatorname{zg}\left(e\right) = \operatorname{exp}\left(\operatorname{ofReal}\left(\operatorname{alpha}\left(y\right) - \operatorname{alpha}\left(x\right)\right) \cdot I\right) \cdot \operatorname{z}\left(e\right)\right) \land \left(\left(\forall x \in V,\; \forall y \in V,\; \forall e \in \operatorname{Hom}\left(x, y\right),\; \operatorname{Cg}\left(e\right) = \operatorname{edgeChannel}\left(\operatorname{v}\left(e\right), \operatorname{theta}\left(e\right) + \operatorname{alpha}\left(y\right) - \operatorname{alpha}\left(x\right)\right)\right) \land zgP = \operatorname{weight}\left(zg, p\right)\right); zgP = \operatorname{exp}\left(\operatorname{ofReal}\left(\operatorname{alpha}\left(j\right) - \operatorname{alpha}\left(i\right)\right) \cdot I\right) \cdot zP \land \left(\left(i = j \Rightarrow zgP = zP\right) \land \left(\left(i = j \Rightarrow (\operatorname{angle}\left(\operatorname{arg}\left(zgP\right)\right), \left\lVert zgP \right\rVert) = (\operatorname{angle}\left(\operatorname{arg}\left(zP\right)\right), \left\lVert zP \right\rVert)\right) \land \left(i = j \Rightarrow \operatorname{matrixAction}\left(\operatorname{pathChannel}\left(Cg, p\right), \operatorname{sourceMatrix}\left(a, b, d\right)\right) = \operatorname{matrixAction}\left(\operatorname{pathChannel}\left(C, p\right), \operatorname{sourceMatrix}\left(a, b, d\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Decoherence/FinitePathCoherence.source_path_coherence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The map angle is the quotient from real phases to Real.Angle, so phase equality is modulo two pi. The principal argument is used only for the polar reconstruction. The norm and its negative logarithm retain attenuation. For each real vertex reference alpha, the transformed channels are canonical edge channels with phase theta(e)+alpha(y)-alpha(x). On a closed path their complex multiplier, phase-norm pair, and actual Hermitian matrix action agree exactly.

## References

- Truth anchor: `D5/S3/Quantum/Decoherence/FinitePathCoherence.edgeChannel_action`
- Truth anchor: `D5/S3/Quantum/Decoherence/FinitePathCoherence.path_channel_action`
- Truth anchor: `D5/S3/Quantum/Decoherence/FinitePathCoherence.source_path_coherence`
- Dependency: [D5/S3/Quantum/Foundation/FiniteKrausChannel](../Foundation/FiniteKrausChannel.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteTraceDistance](../Foundation/FiniteTraceDistance.md)
