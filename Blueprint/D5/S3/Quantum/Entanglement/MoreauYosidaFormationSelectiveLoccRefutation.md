# Selective LOCC can increase the Moreau-Yosida entanglement of formation

## Abstract

Shirokov's Moreau-Yosida approximation of the entanglement of formation can increase on average under a local projective measurement. The input value is at most 1/7 and the output average is at least 3/20, for lambda = 7/2 on C^5 tensor C^3.

**Definition 1.1 (Pure-vector coefficients).**

$$\forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \operatorname{Coeff}\left(a, b\right) = \operatorname{Matrix}\left(\operatorname{Fin}\left(a\right), \operatorname{Fin}\left(b\right), \mathbb{C}\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/MoreauYosidaFormationSelectiveLoccRefutation.Coeff` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Coeff(a,b) is the complex a by b coefficient matrix of a vector in C^a tensor C^b. Fin(a) labels Alice's basis and Fin(b) labels Bob's basis.

**Definition 1.2 (Squared vector norm).**

$$\forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \forall M \in \operatorname{Coeff}\left(a, b\right),\; \operatorname{mass}\left(M\right) = \sum_{i : \operatorname{Fin}\left(a\right)} \sum_{j : \operatorname{Fin}\left(b\right)} \operatorname{normSq}\left(M\left(i, j\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/MoreauYosidaFormationSelectiveLoccRefutation.mass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The mass of M is the sum of the squared complex norms of all its entries. normSq(z) = |z|^2.

**Definition 1.3 (Normalized pure vectors).**

$$\forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \operatorname{Pure}\left(a, b\right) = \{M : \operatorname{Coeff}\left(a, b\right) \mid \operatorname{mass}\left(M\right) = 1\}$$

*Formalization.* `D5/S3/Quantum/Entanglement/MoreauYosidaFormationSelectiveLoccRefutation.Pure` (`✓ std3`).

*Citation.* M. E. Shirokov (2026). *The Moreau-Yosida approximation of the EoF: basic properties and accuracy estimates*. URL: <https://arxiv.org/abs/2609.30246v1>.

*Commentary.*

Pure(a,b) consists of coefficient matrices with mass one. Every normalized joint pure vector is represented, without a restriction to either selected block.

**Definition 1.4 (All finite pure ensembles).**

$$\forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \forall n \in \mathbb{N},\; \forall r \in \operatorname{DensityState}\left((\operatorname{Fin}\left(a\right) \times \operatorname{Fin}\left(b\right))\right),\; \operatorname{Ensemble}\left(n, r\right) = \{(p, q) : ((\operatorname{Fin}\left(n\right) \to \mathbb{R}) \times (\operatorname{Fin}\left(n\right) \to \operatorname{Pure}\left(a, b\right))) \mid (\forall i \in \operatorname{Fin}\left(n\right),\; 0 \le p\left(i\right)) \land ((\sum_{i : \operatorname{Fin}\left(n\right)} p\left(i\right) = 1) \land (\sum_{i : \operatorname{Fin}\left(n\right)} \operatorname{Complex}\left(p\left(i\right)\right) \cdot \operatorname{rankOneDensity}\left(\lambda x : (\operatorname{Fin}\left(a\right) \times \operatorname{Fin}\left(b\right)), \operatorname{val}\left(q\left(i\right)\right)\left(\operatorname{fst}\left(x\right), \operatorname{snd}\left(x\right)\right)\right) = \operatorname{CStarMatrix.ofMatrix.symm}\left(\operatorname{val}\left(r\right)\right)))\}$$

*Formalization.* `D5/S3/Quantum/Entanglement/MoreauYosidaFormationSelectiveLoccRefutation.Ensemble` (`✓ std3`).

*Citation.* M. E. Shirokov (2026). *The Moreau-Yosida approximation of the EoF: basic properties and accuracy estimates*. URL: <https://arxiv.org/abs/2609.30246v1>.

*Commentary.*

Equation (EF-d), equation (1), p. 2: "where the infimum is taken over all finite ensembles {pₖ, ϱₖ} of pure states in 𝔖($\mathcal{H}_{AB}$) having $\rho$ as their average state". rankOneDensity is the existing outer product of a vector with itself; the displayed lambda uncurries each coefficient matrix. An Ensemble(n,r) is a pair (p,q) of probabilities and normalized pure vectors satisfying every displayed condition. DensityState(Fin(a) times Fin(b)) is the canonical CStarMatrix density-state carrier, with nonnegative matrix and trace one. CStarMatrix.ofMatrix.symm returns the underlying joint matrix. No upper bound is imposed on n; the convex roof below ranges over all n.

**Definition 1.5 (Average pure-state entropy).**

$$\forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \forall n \in \mathbb{N},\; \forall r \in \operatorname{DensityState}\left((\operatorname{Fin}\left(a\right) \times \operatorname{Fin}\left(b\right))\right),\; \forall e \in \operatorname{Ensemble}\left(n, r\right),\; \operatorname{cost}\left(e\right) = \sum_{i : \operatorname{Fin}\left(n\right)} \operatorname{p}\left(e\right)\left(i\right) \cdot \operatorname{vonNeumannEntropy}\left(\operatorname{marginalRight}\left(\operatorname{pureDensityState}\left(\lambda x : (\operatorname{Fin}\left(a\right) \times \operatorname{Fin}\left(b\right)), \operatorname{val}\left(\psi\left(e\right)\left(i\right)\right)\left(\operatorname{fst}\left(x\right), \operatorname{snd}\left(x\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/MoreauYosidaFormationSelectiveLoccRefutation.cost` (`✓ std3`).

*Citation.* M. E. Shirokov (2026). *The Moreau-Yosida approximation of the EoF: basic properties and accuracy estimates*. URL: <https://arxiv.org/abs/2609.30246v1>.

*Commentary.*

The average entropy is the probability-weighted vonNeumannEntropy of marginalRight of each pureDensityState. The unit-norm proof argument to pureDensityState is suppressed in the display and supplied by mass(val(ψ(e)(i))) = 1. pureDensityState is the existing density-state constructor with underlying matrix rankOneDensity, the outer product |ψ><ψ|. marginalRight traces out Bob and retains Alice. vonNeumannEntropy is the existing -Re Tr(rho log rho), using natural logarithms and zero contribution at a zero eigenvalue. The projections p(e) and ψ(e) are its probabilities and pure vectors, respectively.

**Definition 1.6 (Entanglement of formation).**

$$\forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \forall r \in \operatorname{DensityState}\left((\operatorname{Fin}\left(a\right) \times \operatorname{Fin}\left(b\right))\right),\; \left(E_{F}\right)\left(r\right) = \operatorname{inf}_{n : \mathbb{N}} (\operatorname{inf}_{e : \operatorname{Ensemble}\left(n, r\right)} (\operatorname{ofReal}\left(\operatorname{cost}\left(e\right)\right)))$$

*Formalization.* `D5/S3/Quantum/Entanglement/MoreauYosidaFormationSelectiveLoccRefutation.E_F` (`✓ std3`).

*Citation.* M. E. Shirokov (2026). *The Moreau-Yosida approximation of the EoF: basic properties and accuracy estimates*. URL: <https://arxiv.org/abs/2609.30246v1>.

*Commentary.*

Equation (EF-d), equation (1), p. 2, is E_F(rho) = inf_{sum_k p_k varrho_k = rho} sum_k p_k S([varrho_k]_A). The formula uses all finite ensembles as in the quoted sentence above. The displayed full name E with subscript F denotes the Lean definition E_F. The value type is the extended nonnegative reals; ofReal(x) is max(x,0) in that type. For normalized pure states every entropy term is nonnegative.

**Definition 1.7 (The unsquared trace-norm Moreau envelope).**

$$\forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \forall t \in \mathbb{R},\; \forall r \in \operatorname{DensityState}\left((\operatorname{Fin}\left(a\right) \times \operatorname{Fin}\left(b\right))\right),\; \left(E_{F_{my}}\right)\left(t, r\right) = \operatorname{inf}_{s : \operatorname{DensityState}\left((\operatorname{Fin}\left(a\right) \times \operatorname{Fin}\left(b\right))\right)} (\left(E_{F}\right)\left(s\right) + \operatorname{ofReal}\left(\frac{\operatorname{traceNorm}\left(\operatorname{CStarMatrix.ofMatrix.symm}\left(\operatorname{val}\left(r\right)\right) - \operatorname{CStarMatrix.ofMatrix.symm}\left(\operatorname{val}\left(s\right)\right)\right)}{2 \cdot t}\right))$$

*Formalization.* `D5/S3/Quantum/Entanglement/MoreauYosidaFormationSelectiveLoccRefutation.E_F_my` (`✓ std3`).

*Citation.* M. E. Shirokov (2026). *The Moreau-Yosida approximation of the EoF: basic properties and accuracy estimates*. URL: <https://arxiv.org/abs/2609.30246v1>.

*Commentary.*

Equation (EFA), equation (13), p. 6, defines E_F^lambda(rho) = inf_sigma { E_F(sigma) + $\Vert \rho - \sigma \Vert_{1}$/(2 lambda) }. The footnote on p. 7 states: "It is essential that we use $\Vert \rho - \sigma \Vert_{1}$ instead of $\Vert \rho - \sigma \Vert^{2}_{1}$ in (13)." The displayed full name E with nested subscript F and my denotes the Lean definition E_F_my; t denotes lambda. The infimum ranges over every density state on the same space. traceNorm is the existing matrix trace norm, and the penalty has no square. The selective claim requires t > 0.

**Definition 1.8 (Local instruments with classical outcomes).**

$$\forall d \in \mathbb{N},\; \operatorname{LocalInstrument}\left(d\right) = \{(o, k, K) : \Sigma (o : \mathbb{N}), \Sigma (k : (\operatorname{Fin}\left(o\right) \to \mathbb{N})), \forall i \in \operatorname{Fin}\left(o\right),\; (\operatorname{Fin}\left(k\left(i\right)\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)) \mid \sum_{i : \operatorname{Fin}\left(o\right)} \sum_{j : \operatorname{Fin}\left(k\left(i\right)\right)} \operatorname{conjTranspose}\left(K\left(i, j\right)\right) \cdot K\left(i, j\right) = 1\}$$

*Formalization.* `D5/S3/Quantum/Entanglement/MoreauYosidaFormationSelectiveLoccRefutation.LocalInstrument` (`✓ std3`).

*Citation.* M. E. Shirokov (2026). *The Moreau-Yosida approximation of the EoF: basic properties and accuracy estimates*. URL: <https://arxiv.org/abs/2609.30246v1>.

*Commentary.*

A local instrument on dimension d has o classical outcomes, k(i) Kraus operators for outcome i, and operators K(i,j) with the displayed completeness equation. conjTranspose is Matrix.conjTranspose. All sums are finite. Multiple Kraus operators for one classical outcome represent a general completely positive outcome map on the fixed local space.

**Definition 1.9 (Finite-round LOCC with recorded outcomes).**

$$\forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \operatorname{Protocol}\left(a, b\right) : Type; done : \operatorname{Protocol}\left(a, b\right); alice : \forall I \in \operatorname{LocalInstrument}\left(a\right),\; ((\operatorname{Fin}\left(\operatorname{outcomes}\left(I\right)\right) \to \operatorname{Protocol}\left(a, b\right)) \to \operatorname{Protocol}\left(a, b\right)); bob : \forall I \in \operatorname{LocalInstrument}\left(b\right),\; ((\operatorname{Fin}\left(\operatorname{outcomes}\left(I\right)\right) \to \operatorname{Protocol}\left(a, b\right)) \to \operatorname{Protocol}\left(a, b\right))$$

*Formalization.* `D5/S3/Quantum/Entanglement/MoreauYosidaFormationSelectiveLoccRefutation.Protocol` (`✓ std3`).

*Citation.* M. E. Shirokov (2026). *The Moreau-Yosida approximation of the EoF: basic properties and accuracy estimates*. URL: <https://arxiv.org/abs/2609.30246v1>.

*Commentary.*

Protocol(a,b) is the inductive type with constructors done, alice and bob. The two local constructors take an instrument and a continuation for each classical outcome. Finite trees retain the complete classical outcome history. This class has finite outcomes and rounds and fixed local spaces. It contains one-round local projective measurements, hence the counterexample also refutes selective monotonicity for every larger LOCC class containing these operations.

**Definition 1.10 (Unnormalized terminal branches).**

$$\forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \forall r \in \operatorname{CompositeMatrix}\left(a, b\right),\; (\operatorname{branchList}\left(\operatorname{done}\left(a, b\right), r\right) = [r]) \land ((\forall I \in \operatorname{LocalInstrument}\left(a\right),\; \forall k \in (\operatorname{Fin}\left(\operatorname{outcomes}\left(I\right)\right) \to \operatorname{Protocol}\left(a, b\right)),\; \operatorname{branchList}\left(\operatorname{alice}\left(I, k\right), r\right) = \operatorname{flatMap}\left(\lambda i : \operatorname{Fin}\left(\operatorname{outcomes}\left(I\right)\right), \operatorname{branchList}\left(k\left(i\right), \sum_{j : \operatorname{Fin}\left(\operatorname{krausCount}\left(I\right)\left(i\right)\right)} \operatorname{kronecker}\left(\operatorname{K}\left(I\right)\left(i, j\right), (1 : \operatorname{Matrix}\left(\operatorname{Fin}\left(b\right), \operatorname{Fin}\left(b\right), \mathbb{C}\right))\right) \cdot r \cdot \operatorname{conjTranspose}\left(\operatorname{kronecker}\left(\operatorname{K}\left(I\right)\left(i, j\right), (1 : \operatorname{Matrix}\left(\operatorname{Fin}\left(b\right), \operatorname{Fin}\left(b\right), \mathbb{C}\right))\right)\right)\right), \operatorname{finRange}\left(\operatorname{outcomes}\left(I\right)\right)\right)) \land (\forall I \in \operatorname{LocalInstrument}\left(b\right),\; \forall k \in (\operatorname{Fin}\left(\operatorname{outcomes}\left(I\right)\right) \to \operatorname{Protocol}\left(a, b\right)),\; \operatorname{branchList}\left(\operatorname{bob}\left(I, k\right), r\right) = \operatorname{flatMap}\left(\lambda i : \operatorname{Fin}\left(\operatorname{outcomes}\left(I\right)\right), \operatorname{branchList}\left(k\left(i\right), \sum_{j : \operatorname{Fin}\left(\operatorname{krausCount}\left(I\right)\left(i\right)\right)} \operatorname{kronecker}\left((1 : \operatorname{Matrix}\left(\operatorname{Fin}\left(a\right), \operatorname{Fin}\left(a\right), \mathbb{C}\right)), \operatorname{K}\left(I\right)\left(i, j\right)\right) \cdot r \cdot \operatorname{conjTranspose}\left(\operatorname{kronecker}\left((1 : \operatorname{Matrix}\left(\operatorname{Fin}\left(a\right), \operatorname{Fin}\left(a\right), \mathbb{C}\right)), \operatorname{K}\left(I\right)\left(i, j\right)\right)\right)\right), \operatorname{finRange}\left(\operatorname{outcomes}\left(I\right)\right)\right)))$$

*Formalization.* `D5/S3/Quantum/Entanglement/MoreauYosidaFormationSelectiveLoccRefutation.branchList` (`✓ std3`).

*Citation.* M. E. Shirokov (2026). *The Moreau-Yosida approximation of the EoF: basic properties and accuracy estimates*. URL: <https://arxiv.org/abs/2609.30246v1>.

*Commentary.*

The recursive equations evaluate the complete protocol on a joint matrix r. At an Alice node each local Kraus operator is tensored with Bob's identity, and at a Bob node Alice's identity is tensored with the local Kraus operator. flatMap concatenates the terminal branch lists over the classical outcomes. The typed matrix numerals 1 are the identity matrices; conjTranspose is Matrix.conjTranspose. These are unnormalized branches. A terminal probability and normalized output are linked by the exact matrix equation in claim.

**Definition 1.11 (Shirokov's selective-monotonicity conjecture).**

$$claim \Leftrightarrow (\forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; (0 < a) \Rightarrow \left((0 < b) \Rightarrow \left(\forall t \in \mathbb{R},\; (0 < t) \Rightarrow \left(\forall r \in \operatorname{DensityState}\left((\operatorname{Fin}\left(a\right) \times \operatorname{Fin}\left(b\right))\right),\; \forall T \in \operatorname{Protocol}\left(a, b\right),\; \forall n \in \mathbb{N},\; \forall p \in (\operatorname{Fin}\left(n\right) \to \mathbb{R}),\; \forall out \in (\operatorname{Fin}\left(n\right) \to \operatorname{DensityState}\left((\operatorname{Fin}\left(a\right) \times \operatorname{Fin}\left(b\right))\right)),\; (\forall i \in \operatorname{Fin}\left(n\right),\; 0 \le p\left(i\right)) \Rightarrow \left((\sum_{i : \operatorname{Fin}\left(n\right)} p\left(i\right) = 1) \Rightarrow \left((\operatorname{branchList}\left(T, \operatorname{CStarMatrix.ofMatrix.symm}\left(\operatorname{val}\left(r\right)\right)\right) = \operatorname{map}\left(\lambda i : \operatorname{Fin}\left(n\right), \operatorname{Complex}\left(p\left(i\right)\right) \cdot \operatorname{CStarMatrix.ofMatrix.symm}\left(\operatorname{val}\left(out\left(i\right)\right)\right), \operatorname{finRange}\left(n\right)\right)) \Rightarrow \sum_{i : \operatorname{Fin}\left(n\right)} \operatorname{ofReal}\left(p\left(i\right)\right) \cdot \left(E_{F_{my}}\right)\left(t, out\left(i\right)\right) \le \left(E_{F_{my}}\right)\left(t, r\right)\right)\right)\right)\right)\right))$$

*Formalization.* `D5/S3/Quantum/Entanglement/MoreauYosidaFormationSelectiveLoccRefutation.claim` (`✓ std3`).

*Citation.* M. E. Shirokov (2026). *The Moreau-Yosida approximation of the EoF: basic properties and accuracy estimates*. URL: <https://arxiv.org/abs/2609.30246v1>.

*Commentary.*

Section 7, p. 20: "So, we may conjecture, at the moment, that the function $E^{\lambda}_{F}$ does not increase under selective LOCC-operations as well." The section's heading is "Open question: can the function $E^{\lambda}_{F}$ increase under selective LOCC-operations?" The formal inequality is the standard selective convention: the probability-weighted average of the normalized terminal values is at most the input value. Dimensions a,b are positive, t is lambda > 0, T is a finite-round local-instrument protocol, p is nonnegative and sums to one, and out assigns normalized density states. finRange(n) is the ordered list of all elements of Fin(n); its map lists p(i) times CStarMatrix.ofMatrix.symm(val(out(i))) in the same order as the terminal branches. Complex(p(i)) denotes the real-to-complex coercion, and ofReal(p(i)) denotes the extended-nonnegative weight. Zero-probability branches may have any normalized out(i).

**Theorem 1.12 (A local projective measurement increases the output average).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/MoreauYosidaFormationSelectiveLoccRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/shirokov-2026-moreau-yosida-eof-selective-locc-refutation` (refuted) by `D5/S3/Quantum/Entanglement/MoreauYosidaFormationSelectiveLoccRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"shirokov-2026-moreau-yosida-eof-selective-locc-refutation","declaration_gid":"D5/S3/Quantum/Entanglement/MoreauYosidaFormationSelectiveLoccRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* M. E. Shirokov (2026). *The Moreau-Yosida approximation of the EoF: basic properties and accuracy estimates*. URL: <https://arxiv.org/abs/2609.30246v1>.

*Commentary.*

Let v_2 = e_00 + e_11 and v_3 = e_20 + e_31 + e_42 on C^5 tensor C^3, let Phi_2 = v_2 v_2^*/2 and Phi_3 = v_3 v_3^*/3, and omega = (Phi_2 + Phi_3)/2. At t = 7/2 Alice measures the projections diag(1,1,0,0,0) and its complement. The two branches have probabilities 1/2 and outputs Phi_2 and Phi_3. For every normalized ambient 5 by 3 pure coefficient matrix, entropy is at least 1 - Tr((M M^*)^2), equal to twice the sum of the squared absolute 2 by 2 minors. Pair and triple norm estimates give affine entropy bounds with slope 3/10 and fidelity offsets 11/20 and 2/5. Nonnegativity lowers the slope to 2/7; linearity extends the bounds to every finite ensemble. The unitary reflection 2P-I gives traceNorm(P-sigma) >= 2(1-Tr(P sigma)) for a trace-one projector P. Thus E_F_my(7/2,Phi_2) >= 9/70 and E_F_my(7/2,Phi_3) >= 6/35, and their average is at least 3/20. The state sigma = (|00><00| + |11><11|)/2 has an explicit product-state ensemble of entropy zero, and traceNorm(omega-sigma) <= 1, so E_F_my(7/2,omega) <= 1/7. Since 3/20 - 1/7 = 1/140 > 0, the selective inequality fails.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/MoreauYosidaFormationSelectiveLoccRefutation.Coeff`
- Truth anchor: `D5/S3/Quantum/Entanglement/MoreauYosidaFormationSelectiveLoccRefutation.E_F`
- Truth anchor: `D5/S3/Quantum/Entanglement/MoreauYosidaFormationSelectiveLoccRefutation.E_F_my`
- Truth anchor: `D5/S3/Quantum/Entanglement/MoreauYosidaFormationSelectiveLoccRefutation.Ensemble`
- Truth anchor: `D5/S3/Quantum/Entanglement/MoreauYosidaFormationSelectiveLoccRefutation.LocalInstrument`
- Truth anchor: `D5/S3/Quantum/Entanglement/MoreauYosidaFormationSelectiveLoccRefutation.Protocol`
- Truth anchor: `D5/S3/Quantum/Entanglement/MoreauYosidaFormationSelectiveLoccRefutation.Pure`
- Truth anchor: `D5/S3/Quantum/Entanglement/MoreauYosidaFormationSelectiveLoccRefutation.branchList`
- Truth anchor: `D5/S3/Quantum/Entanglement/MoreauYosidaFormationSelectiveLoccRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Entanglement/MoreauYosidaFormationSelectiveLoccRefutation.cost`
- Truth anchor: `D5/S3/Quantum/Entanglement/MoreauYosidaFormationSelectiveLoccRefutation.mass`
- Truth anchor: `D5/S3/Quantum/Entanglement/MoreauYosidaFormationSelectiveLoccRefutation.result`
- Dependency: [D5/S3/Entropy/MaxEntropy](../../Entropy/MaxEntropy.md)
- Dependency: [D5/S3/Quantum/Divergence/VonNeumannEntropyPinching](../Divergence/VonNeumannEntropyPinching.md)
- Dependency: [D5/S3/Quantum/Dynamics/EnergyEigenstateStationarity](../Dynamics/EnergyEigenstateStationarity.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteStateChannel](../Foundation/FiniteStateChannel.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteTraceDistance](../Foundation/FiniteTraceDistance.md)
- Dependency: [D5/S3/Quantum/Information/InputInformationBalance](../Information/InputInformationBalance.md)
- Dependency: [D5/S3/Quantum/Information/PartialTraceMutualInformation](../Information/PartialTraceMutualInformation.md)
- Dependency: [D5/S3/Quantum/PureState/PureStateHandshake](../PureState/PureStateHandshake.md)
- Dependency: [D5/S3/Quantum/Reduction/IsometricCompression](../Reduction/IsometricCompression.md)
