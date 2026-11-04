# Order-three Renyi information combining

## Abstract

Both branches of the binary quantum information-combining expression are equalities at Renyi order three, in arbitrary finite dimensions including singular marginals.

**Theorem 1.1 (A basis projector is positive semidefinite).**

$$\forall i \in \operatorname{Fin}\left(2\right),\; \operatorname{Matrix.PosSemidef}\left((\operatorname{Matrix.single}\left(i, i, 1\right) : \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/RenyiInformationCombiningOrderThree.unit_psd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Christoph Hirche; Xinyue Guan; Marco Tomamichel (2023). *Chain Rules for Rényi Information Combining*. DOI: [10.1109/ISIT54713.2023.10206941](https://doi.org/10.1109/ISIT54713.2023.10206941). URL: <https://arxiv.org/abs/2305.02589v1>.

*Commentary.*

For each of the two basis indices, Matrix.single i i 1 is positive semidefinite. Its Kronecker products give the two positive blocks in blk_psd. The channel time-reversal argument also uses the basis projector at index zero.

**Theorem 1.2 (Functional calculus of a unitarily conjugated real diagonal matrix).**

$$\forall n \in \operatorname{Type},\; [\operatorname{Fintype}\left(n\right)] [\operatorname{DecidableEq}\left(n\right)] \forall U \in \operatorname{Matrix.unitaryGroup}\left(n, \mathbb{C}\right),\; \forall d \in n \to \mathbb{R},\; \forall f \in \mathbb{R} \to \mathbb{R},\; \operatorname{cfc}\left(f, (U : \operatorname{Matrix}\left(n, n, \mathbb{C}\right)) \cdot \operatorname{Matrix.diagonal}\left((fun (i : n) \mapsto (d\left(i\right) : \mathbb{C}))\right) \cdot \operatorname{star}\left((U : \operatorname{Matrix}\left(n, n, \mathbb{C}\right))\right)\right) = (U : \operatorname{Matrix}\left(n, n, \mathbb{C}\right)) \cdot \operatorname{Matrix.diagonal}\left((fun (i : n) \mapsto (f\left(d\left(i\right)\right) : \mathbb{C}))\right) \cdot \operatorname{star}\left((U : \operatorname{Matrix}\left(n, n, \mathbb{C}\right))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/RenyiInformationCombiningOrderThree.cfc_unitary_diagonal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Christoph Hirche; Xinyue Guan; Marco Tomamichel (2023). *Chain Rules for Rényi Information Combining*. DOI: [10.1109/ISIT54713.2023.10206941](https://doi.org/10.1109/ISIT54713.2023.10206941). URL: <https://arxiv.org/abs/2305.02589v1>.

*Commentary.*

Real continuous functional calculus commutes with unitary conjugation and applies the scalar function to each real diagonal entry. No continuity assumption on f is needed because the matrix spectrum is finite. Its internal kronecker_rpow consumer lies on the xor_sandwiches proof path. The dependent-family escape audit remains unfinished; the result audit remains unfinished.

**Definition 1.3 (Sandwiched conditional Renyi entropy).**

$$\forall a \in \operatorname{Type},\; [\operatorname{Fintype}\left(a\right)] [\operatorname{DecidableEq}\left(a\right)] \forall b \in \operatorname{Type},\; [\operatorname{Fintype}\left(b\right)] [\operatorname{DecidableEq}\left(b\right)] \forall alpha \in \mathbb{R},\; \forall rho \in \operatorname{Matrix}\left((a \times b), (a \times b), \mathbb{C}\right),\; \operatorname{let} M : \operatorname{Matrix}\left((a \times b), (a \times b), \mathbb{C}\right) = \operatorname{Matrix.kronecker}\left((1 : \operatorname{Matrix}\left(a, a, \mathbb{C}\right)), (\operatorname{PartialTraceMutualInformation.partialTraceLeft}\left(rho\right)^{\frac{1 - alpha}{2 \cdot alpha}})\right); \operatorname{condRenyiDown}\left(alpha, rho\right) = \frac{1}{1 - alpha} \cdot \operatorname{Real.log}\left(\operatorname{RCLike.re}\left(\operatorname{Matrix.trace}\left(\left(M \cdot rho \cdot M\right)^{alpha}\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Information/RenyiInformationCombiningOrderThree.condRenyiDown` (`✓ std3`).

*Citation.* Christoph Hirche; Xinyue Guan; Marco Tomamichel (2023). *Chain Rules for Rényi Information Combining*. DOI: [10.1109/ISIT54713.2023.10206941](https://doi.org/10.1109/ISIT54713.2023.10206941). URL: <https://arxiv.org/abs/2305.02589v1>.

*Commentary.*

Section IV, p. 4, defines the sandwiched conditional Renyi entropy by the trace of the alpha power of the sandwiched state. The identity on A is explicit here; partialTraceLeft is the B marginal. Matrix real powers are continuous-functional-calculus powers, with inverse powers taken on the support. Real.log uses natural logarithms. The real part of the trace is explicit. The equation applies to all matrices; its entropy interpretation is for density matrices and admissible alpha.

**Definition 1.4 (Equiprobable classical-quantum input).**

$$\forall n \in \operatorname{Type},\; \forall s0 \in \operatorname{Matrix}\left(n, n, \mathbb{C}\right),\; \forall s1 \in \operatorname{Matrix}\left(n, n, \mathbb{C}\right),\; \operatorname{cqState}\left(s0, s1\right) = \operatorname{HSMul.hSMul}\left((\frac{1}{2} : \mathbb{C}), \operatorname{Matrix.kronecker}\left(\operatorname{Matrix.single}\left(0, 0, 1\right), s0\right)\right) + \operatorname{HSMul.hSMul}\left((\frac{1}{2} : \mathbb{C}), \operatorname{Matrix.kronecker}\left(\operatorname{Matrix.single}\left(1, 1, 1\right), s1\right)\right)$$

*Formalization.* `D5/S3/Quantum/Information/RenyiInformationCombiningOrderThree.cqState` (`✓ std3`).

*Citation.* Christoph Hirche; Xinyue Guan; Marco Tomamichel (2023). *Chain Rules for Rényi Information Combining*. DOI: [10.1109/ISIT54713.2023.10206941](https://doi.org/10.1109/ISIT54713.2023.10206941). URL: <https://arxiv.org/abs/2305.02589v1>.

*Commentary.*

Section V, p. 5: the two classical labels are equiprobable. Matrix.single is the matrix unit representing each classical basis projector. The two quantum blocks have the same finite-dimensional carrier.

**Definition 1.5 (The CNOT state).**

$$\forall n1 \in \operatorname{Type},\; \forall n2 \in \operatorname{Type},\; \forall s1 \in \operatorname{Fin}\left(2\right) \to \operatorname{Matrix}\left(n1, n1, \mathbb{C}\right),\; \forall s2 \in \operatorname{Fin}\left(2\right) \to \operatorname{Matrix}\left(n2, n2, \mathbb{C}\right),\; \operatorname{tau}\left(s1, s2\right) = \sum_{z:\operatorname{Fin}\left(2\right)} \sum_{x2:\operatorname{Fin}\left(2\right)} \operatorname{HSMul.hSMul}\left((\frac{1}{4} : \mathbb{C}), \operatorname{Matrix.kronecker}\left(\operatorname{Matrix.single}\left((z + x2, x2), (z + x2, x2), 1\right), \operatorname{Matrix.kronecker}\left(s1\left(z\right), s2\left(x2\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Information/RenyiInformationCombiningOrderThree.tau` (`✓ std3`).

*Citation.* Christoph Hirche; Xinyue Guan; Marco Tomamichel (2023). *Chain Rules for Rényi Information Combining*. DOI: [10.1109/ISIT54713.2023.10206941](https://doi.org/10.1109/ISIT54713.2023.10206941). URL: <https://arxiv.org/abs/2305.02589v1>.

*Commentary.*

Section V, p. 5, states verbatim: "After applying a CNOT gate to the classical systems we have the joint state". Its displayed sum is encoded below. Addition in Fin 2 is XOR, and the index order is ((X1 + X2, X2), (B1, B2)). The quantum inputs are independent; each of the four classical pairs has weight one quarter.

**Definition 1.6 (Discarding the second classical register).**

$$\forall b \in \operatorname{Type},\; \forall t \in \operatorname{Matrix}\left(((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)) \times b), ((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)) \times b), \mathbb{C}\right),\; \forall z \in \operatorname{Fin}\left(2\right),\; \forall j \in b,\; \forall w \in \operatorname{Fin}\left(2\right),\; \forall k \in b,\; \operatorname{traceOutX2}\left(t\right)\left((z, j), (w, k)\right) = \sum_{x2:\operatorname{Fin}\left(2\right)} t\left(((z, x2), j), ((w, x2), k)\right)$$

*Formalization.* `D5/S3/Quantum/Information/RenyiInformationCombiningOrderThree.traceOutX2` (`✓ std3`).

*Citation.* Christoph Hirche; Xinyue Guan; Marco Tomamichel (2023). *Chain Rules for Rényi Information Combining*. DOI: [10.1109/ISIT54713.2023.10206941](https://doi.org/10.1109/ISIT54713.2023.10206941). URL: <https://arxiv.org/abs/2305.02589v1>.

*Commentary.*

The B carrier here may itself be a product. The partial trace sums over the diagonal X2 index, leaving X1 + X2 and B. This is the marginal used on the left of Conjecture V.5.

**Definition 1.7 (The binary-entropy inverse branch).**

$$\forall alpha \in \mathbb{R},\; \operatorname{hRenyiInv}\left(alpha\right) = \operatorname{Function.invFunOn}\left(\operatorname{hRenyi}\left(alpha\right), \operatorname{Set.Icc}\left(0, \frac{1}{2}\right)\right)$$

*Formalization.* `D5/S3/Quantum/Information/RenyiInformationCombiningOrderThree.hRenyiInv` (`✓ std3`).

*Citation.* Christoph Hirche; Xinyue Guan; Marco Tomamichel (2023). *Chain Rules for Rényi Information Combining*. DOI: [10.1109/ISIT54713.2023.10206941](https://doi.org/10.1109/ISIT54713.2023.10206941). URL: <https://arxiv.org/abs/2305.02589v1>.

*Commentary.*

Function.invFunOn restricts the probability input to the closed interval [0, 1/2]. At alpha = 3, hRenyi maps this interval bijectively to [0, Real.log 2]. Consequently the entropy arguments of this inverse belong to [0, Real.log 2], and its returned probabilities lie in [0, 1/2].

**Definition 1.8 (The order-three equality clause).**

$$\operatorname{claim} \Leftrightarrow (\forall n1 \in \mathbb{N},\; \forall n2 \in \mathbb{N},\; \forall s1 \in \operatorname{Fin}\left(2\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(n1\right), \operatorname{Fin}\left(n1\right), \mathbb{C}\right),\; \forall s2 \in \operatorname{Fin}\left(2\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(n2\right), \operatorname{Fin}\left(n2\right), \mathbb{C}\right),\; (\forall x \in \operatorname{Fin}\left(2\right),\; \operatorname{SLDSpectralEnergy.IsDensity}\left(s1\left(x\right)\right)) \Rightarrow ((\forall x \in \operatorname{Fin}\left(2\right),\; \operatorname{SLDSpectralEnergy.IsDensity}\left(s2\left(x\right)\right)) \Rightarrow (\operatorname{let} H1 : \mathbb{R} = \operatorname{condRenyiDown}\left(3, \operatorname{cqState}\left(s1\left(0\right), s1\left(1\right)\right)\right); \operatorname{let} H2 : \mathbb{R} = \operatorname{condRenyiDown}\left(3, \operatorname{cqState}\left(s2\left(0\right), s2\left(1\right)\right)\right); \operatorname{let} Hout : \mathbb{R} = \operatorname{condRenyiDown}\left(3, \operatorname{traceOutX2}\left(\operatorname{tau}\left(s1, s2\right)\right)\right); ((H1 + H2 \le \operatorname{Real.log}\left(2\right)) \Rightarrow (Hout = \operatorname{hRenyi}\left(3, \operatorname{bconv}\left(\operatorname{hRenyiInv}\left(3, H1\right), \operatorname{hRenyiInv}\left(3, H2\right)\right)\right))) \land ((\operatorname{Real.log}\left(2\right) \le H1 + H2) \Rightarrow (Hout = H1 + H2 - \operatorname{Real.log}\left(2\right) + \operatorname{hRenyi}\left(3, \operatorname{bconv}\left(\operatorname{hRenyiInv}\left(3, \operatorname{Real.log}\left(2\right) - H1\right), \operatorname{hRenyiInv}\left(3, \operatorname{Real.log}\left(2\right) - H2\right)\right)\right))))))$$

*Formalization.* `D5/S3/Quantum/Information/RenyiInformationCombiningOrderThree.claim` (`✓ std3`).

*Citation.* Christoph Hirche; Xinyue Guan; Marco Tomamichel (2023). *Chain Rules for Rényi Information Combining*. DOI: [10.1109/ISIT54713.2023.10206941](https://doi.org/10.1109/ISIT54713.2023.10206941). URL: <https://arxiv.org/abs/2305.02589v1>.

*Commentary.*

Conjecture V.5, Section V, p. 7, states verbatim: "For α ∈ [2, 3] the same holds with ≥ exchanged by ≤ and for α ∈ {2, 3} the above holds with equality." The specialization alpha = 3 quantifies over all dimensions n1 and n2 and all four density matrices. The two displayed guards match the two source branches, including their common boundary. IsDensity is the existing predicate for a positive semidefinite complex matrix of trace one.

**Theorem 1.9 (Both order-three branches hold).**

$$\forall n1 \in \mathbb{N},\; \forall n2 \in \mathbb{N},\; \forall s1 \in \operatorname{Fin}\left(2\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(n1\right), \operatorname{Fin}\left(n1\right), \mathbb{C}\right),\; \forall s2 \in \operatorname{Fin}\left(2\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(n2\right), \operatorname{Fin}\left(n2\right), \mathbb{C}\right),\; (\forall x \in \operatorname{Fin}\left(2\right),\; \operatorname{SLDSpectralEnergy.IsDensity}\left(s1\left(x\right)\right)) \Rightarrow ((\forall x \in \operatorname{Fin}\left(2\right),\; \operatorname{SLDSpectralEnergy.IsDensity}\left(s2\left(x\right)\right)) \Rightarrow (\operatorname{let} H1 : \mathbb{R} = \operatorname{condRenyiDown}\left(3, \operatorname{cqState}\left(s1\left(0\right), s1\left(1\right)\right)\right); \operatorname{let} H2 : \mathbb{R} = \operatorname{condRenyiDown}\left(3, \operatorname{cqState}\left(s2\left(0\right), s2\left(1\right)\right)\right); \operatorname{let} Hout : \mathbb{R} = \operatorname{condRenyiDown}\left(3, \operatorname{traceOutX2}\left(\operatorname{tau}\left(s1, s2\right)\right)\right); ((H1 + H2 \le \operatorname{Real.log}\left(2\right)) \Rightarrow (Hout = \operatorname{hRenyi}\left(3, \operatorname{bconv}\left(\operatorname{hRenyiInv}\left(3, H1\right), \operatorname{hRenyiInv}\left(3, H2\right)\right)\right))) \land ((\operatorname{Real.log}\left(2\right) \le H1 + H2) \Rightarrow (Hout = H1 + H2 - \operatorname{Real.log}\left(2\right) + \operatorname{hRenyi}\left(3, \operatorname{bconv}\left(\operatorname{hRenyiInv}\left(3, \operatorname{Real.log}\left(2\right) - H1\right), \operatorname{hRenyiInv}\left(3, \operatorname{Real.log}\left(2\right) - H2\right)\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/RenyiInformationCombiningOrderThree.result` (`✓ std3`). ∎

*Resolves.* `Problems/hirche-guan-tomamichel-2023-renyi-order-three-equality` (proved) by `D5/S3/Quantum/Information/RenyiInformationCombiningOrderThree.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hirche-guan-tomamichel-2023-renyi-order-three-equality","declaration_gid":"D5/S3/Quantum/Information/RenyiInformationCombiningOrderThree.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Christoph Hirche; Xinyue Guan; Marco Tomamichel (2023). *Chain Rules for Rényi Information Combining*. DOI: [10.1109/ISIT54713.2023.10206941](https://doi.org/10.1109/ISIT54713.2023.10206941). URL: <https://arxiv.org/abs/2305.02589v1>.

*Commentary.*

At order three the sandwich exponent is -1/3. Write the two sandwiched blocks as A and B, and set S = A + B and D = A - B. Their cubic trace equals (1 + 3 trace(S D D))/4. The XOR moment factorizes as the product of the input moments, because the quantum marginals are tensor products and their functional-calculus powers factorize. Positivity bounds each input entropy between zero and Real.log 2. Binary convolution multiplies the biases, yielding both expressions in claim. Singular marginals and noncommuting input matrices are included. The source's order-two equality (V.13) is cited, not formalized here. Other-order inequality clauses remain open.

## References

- Truth anchor: `D5/S3/Quantum/Information/RenyiInformationCombiningOrderThree.cfc_unitary_diagonal`
- Truth anchor: `D5/S3/Quantum/Information/RenyiInformationCombiningOrderThree.claim`
- Truth anchor: `D5/S3/Quantum/Information/RenyiInformationCombiningOrderThree.condRenyiDown`
- Truth anchor: `D5/S3/Quantum/Information/RenyiInformationCombiningOrderThree.cqState`
- Truth anchor: `D5/S3/Quantum/Information/RenyiInformationCombiningOrderThree.hRenyiInv`
- Truth anchor: `D5/S3/Quantum/Information/RenyiInformationCombiningOrderThree.result`
- Truth anchor: `D5/S3/Quantum/Information/RenyiInformationCombiningOrderThree.tau`
- Truth anchor: `D5/S3/Quantum/Information/RenyiInformationCombiningOrderThree.traceOutX2`
- Truth anchor: `D5/S3/Quantum/Information/RenyiInformationCombiningOrderThree.unit_psd`
- Dependency: [D5/S3/Entropy/RenyiCombining/BinaryRenyiCombining](../../Entropy/RenyiCombining/BinaryRenyiCombining.md)
- Dependency: [D5/S3/Quantum/Dynamics/EntropyProductionCoherenceDeletionIdentity](../Dynamics/EntropyProductionCoherenceDeletionIdentity.md)
- Dependency: [D5/S3/Quantum/Dynamics/ProjectionProbabilityFlow](../Dynamics/ProjectionProbabilityFlow.md)
- Dependency: [D5/S3/Quantum/Entanglement/GHZMeasureBiseparableBound](../Entanglement/GHZMeasureBiseparableBound.md)
- Dependency: [D5/S3/Quantum/Information/PartialTraceMutualInformation](PartialTraceMutualInformation.md)
- Dependency: [D5/S3/Quantum/Information/SLDSpectralEnergy](SLDSpectralEnergy.md)
