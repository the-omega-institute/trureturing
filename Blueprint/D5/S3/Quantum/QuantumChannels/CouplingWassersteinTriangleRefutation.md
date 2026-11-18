# An order-one coupling Wasserstein distance violates the triangle inequality

## Abstract

For pure-state transport plans with the trace-distance ground metric, an order-one coupling distance in dimension three has a long side at least 96/625 and two short sides totaling at most 3/20.

**Definition 1.1 (Unit amplitude vectors).**

$$\forall n: \mathbb{N}, \operatorname{UnitVector}\left(n\right) = \{v: \operatorname{Fin}\left(n\right) \to \mathbb{C} | \sum_{i\in \operatorname{Fin}\left(n\right)} \operatorname{normSq}\left(v\left(i\right)\right) = 1\}$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/CouplingWassersteinTriangleRefutation.UnitVector` (`✓ std3`).

*Citation.* E. Beatty; D. Stilck França (2025). *Order p quantum Wasserstein distances from couplings*. DOI: [10.1007/s00023-025-01557-z](https://doi.org/10.1007/s00023-025-01557-z). URL: <https://arxiv.org/abs/2402.16477v2>.

*Commentary.*

A vector is a function from Fin n to the complex numbers, with the sum of squared coordinate moduli equal to one. normSq is Complex.normSq, so it is the real squared complex modulus. Vectors differing by a unit complex phase represent the same pure projector. The existing rankOneDensity sends v to the matrix with entries v i times the conjugate of v j. This is the unit-vector presentation of the pure states in Definition 8.

**Definition 1.2 (The trace distance between pure states).**

$$\forall n: \mathbb{N}, \forall u: \operatorname{UnitVector}\left(n\right), \forall v: \operatorname{UnitVector}\left(n\right), \operatorname{ground}\left(u, v\right) = \operatorname{sqrt}\left(1 - \operatorname{normSq}\left(\sum_{i\in \operatorname{Fin}\left(n\right)} (\operatorname{conj}\left(u\left(i\right)\right)) \cdot (v\left(i\right))\right)\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/CouplingWassersteinTriangleRefutation.ground` (`✓ std3`).

*Citation.* E. Beatty; D. Stilck França (2025). *Order p quantum Wasserstein distances from couplings*. DOI: [10.1007/s00023-025-01557-z](https://doi.org/10.1007/s00023-025-01557-z). URL: <https://arxiv.org/abs/2402.16477v2>.

*Commentary.*

Section V.2, equation (81), gives this square-root expression for half the trace norm of the difference of the two unit-vector projectors. The complex inner product is the sum of conjugate u i times v i. The formula uses the real nonnegative square root; it depends only on the projectors and includes arbitrary complex amplitudes.

**Definition 1.3 (Countable pure-state transport plans).**

$$\forall n: \mathbb{N}, \forall \rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), \forall \sigma: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), \operatorname{Plan}\left(\rho, \sigma\right) = \{(q, u, v): (\mathbb{N} \to \mathbb{R}) \times ((\mathbb{N} \to \operatorname{UnitVector}\left(n\right)) \times (\mathbb{N} \to \operatorname{UnitVector}\left(n\right))) | (\forall j: \mathbb{N}, 0 \le q\left(j\right)) \land ((\operatorname{HasSum}\left(\lambda j: \mathbb{N} \mapsto ((q\left(j\right)) \cdot (\operatorname{rankOneDensity}\left(u\left(j\right)\right))), \rho\right)) \land ((\operatorname{HasSum}\left(\lambda j: \mathbb{N} \mapsto ((q\left(j\right)) \cdot (\operatorname{rankOneDensity}\left(v\left(j\right)\right))), \sigma\right)) \land (\operatorname{HasSum}\left(q, 1\right))))\}$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/CouplingWassersteinTriangleRefutation.Plan` (`✓ std3`).

*Citation.* E. Beatty; D. Stilck França (2025). *Order p quantum Wasserstein distances from couplings*. DOI: [10.1007/s00023-025-01557-z](https://doi.org/10.1007/s00023-025-01557-z). URL: <https://arxiv.org/abs/2402.16477v2>.

*Commentary.*

Definition 8 and equations (11) and (12) require the two weighted projector sums to be the indicated marginals. The displayed triple contains a real weight sequence and two sequences of unit vectors. HasSum denotes convergence of the unordered finite partial sums, and the real scalar action multiplies every matrix entry by the real weight. The explicit mass equation HasSum q 1 follows from either density marginal by taking the trace, since each unit projector has trace one. It is retained as a redundant normalization field.

Natural-number indices with nonnegative weights represent the same plans as the source's countable index sets with strictly positive weights. Remove zero-weight terms in one direction; enumerate the positive terms and pad with zeros in the other. Both operations preserve the marginals and cost. Finite plans are included by zero padding. This correspondence is an explanation of the representation; no additional equivalence theorem is asserted.

**Definition 1.4 (The order-one cost).**

$$\forall n: \mathbb{N}, \forall \rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), \forall \sigma: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), \forall Q: \operatorname{Plan}\left(\rho, \sigma\right), \operatorname{cost}\left(Q\right) = \operatorname{tsum}\left(\lambda j: \mathbb{N} \mapsto ((\operatorname{weight}\left(Q\right)\left(j\right)) \cdot (\operatorname{ground}\left(\operatorname{source}\left(Q\right)\left(j\right), \operatorname{target}\left(Q\right)\left(j\right)\right)))\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/CouplingWassersteinTriangleRefutation.cost` (`✓ std3`).

*Citation.* E. Beatty; D. Stilck França (2025). *Order p quantum Wasserstein distances from couplings*. DOI: [10.1007/s00023-025-01557-z](https://doi.org/10.1007/s00023-025-01557-z). URL: <https://arxiv.org/abs/2402.16477v2>.

*Commentary.*

Definition 9, equation (15), specialized to order one. Every ground cost is nonnegative because the real square root is nonnegative, and is at most one because the squared complex modulus is nonnegative and Real.sqrt_le_one applies. Thus the nonnegative weighted cost is bounded termwise by the weight sequence, whose sum is one, so the real tsum is convergent and agrees with the ordinary plan cost. A zero-weight term contributes zero.

**Definition 1.5 (The coupling infimum).**

$$\forall n: \mathbb{N}, \forall \rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), \forall \sigma: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), \operatorname{wasserstein}\left(\rho, \sigma\right) = \operatorname{sInf}\left(\{r: \mathbb{R} | \exists Q: \operatorname{Plan}\left(\rho, \sigma\right), r = \operatorname{cost}\left(Q\right)\}\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/CouplingWassersteinTriangleRefutation.wasserstein` (`✓ std3`).

*Citation.* E. Beatty; D. Stilck França (2025). *Order p quantum Wasserstein distances from couplings*. DOI: [10.1007/s00023-025-01557-z](https://doi.org/10.1007/s00023-025-01557-z). URL: <https://arxiv.org/abs/2402.16477v2>.

*Commentary.*

Definition 9, equation (16), specialized to order one: the outer power 1/p is then one. The infimum is over all countable plans, with no restriction to a chosen finite family. The real sInf convention is total on arbitrary sets; the estimates in the counterexample use nonempty cost sets bounded below by zero, so they use the ordinary real infimum.

**Definition 1.6 (The universal order-one triangle assertion).**

$$(\operatorname{claim}\left(\right)) \Leftrightarrow (\forall n: \mathbb{N}, \forall \rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), \forall T: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), \forall \sigma: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), (\operatorname{IsDensity}\left(\rho\right)) \Rightarrow ((\operatorname{IsDensity}\left(T\right)) \Rightarrow ((\operatorname{IsDensity}\left(\sigma\right)) \Rightarrow (\operatorname{wasserstein}\left(\rho, \sigma\right) \le \operatorname{wasserstein}\left(\rho, T\right) + \operatorname{wasserstein}\left(T, \sigma\right)))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/CouplingWassersteinTriangleRefutation.claim` (`✓ std3`).

*Citation.* E. Beatty; D. Stilck França (2025). *Order p quantum Wasserstein distances from couplings*. DOI: [10.1007/s00023-025-01557-z](https://doi.org/10.1007/s00023-025-01557-z). URL: <https://arxiv.org/abs/2402.16477v2>.

*Commentary.*

The introduction states: “Although many desirable properties of these W_p^d are proven in Sec. IV, establishing a triangle inequality remains a difficult open problem.” Appendix C states: “the triangle inequality eludes us.” Here the triangle assertion ranges over every natural dimension and three arbitrary density matrices, meaning positive semidefinite matrices with trace one. The ground distance is exactly the trace-distance choice in equation (81), and the transport order is one. Pure and singular density matrices are included. The empty-dimensional case is retained literally; it supplies no trace-one states.

**Theorem 1.7 (A three-dimensional counterexample).**

$$\neg \operatorname{claim}\left(\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/CouplingWassersteinTriangleRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/beatty-stilck-franca-2024-coupling-wasserstein-triangle` (refuted) by `D5/S3/Quantum/QuantumChannels/CouplingWassersteinTriangleRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"beatty-stilck-franca-2024-coupling-wasserstein-triangle","declaration_gid":"D5/S3/Quantum/QuantumChannels/CouplingWassersteinTriangleRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* E. Beatty; D. Stilck França (2025). *Order p quantum Wasserstein distances from couplings*. DOI: [10.1007/s00023-025-01557-z](https://doi.org/10.1007/s00023-025-01557-z). URL: <https://arxiv.org/abs/2402.16477v2>.

*Commentary.*

Use coordinates numbered zero, one and two. Put p=(4/5,3/5,0), q=(3/5,4/5,0), P=|p⟩⟨p|, Q=|q⟩⟨q|, R=(P+Q)/2 and s=1/100. Let E k be the kth coordinate projector, B=R−s E 0 and σ=B+s E 2. In the first two coordinates B has matrix [[49/100,12/25],[12/25,1/2]]. The unit vector u=(119/169,120/169,0) gives B=(28561/29750)|u⟩⟨u|+(7/500)E 0+(19/1190)E 1. These positive coefficients sum to 99/100. This decomposition also establishes positivity of B and σ.

The plan with weight 1/2 on (p,p) and 1/2 on (p,q) has marginals P and R and cost 7/50, since the ground distances are zero and 7/25. Match the three displayed components of B to themselves, then put weight s on (e 0,e 2). This plan has marginals R and σ and cost 1/100. Hence the two short sides total at most 3/20.

Consider an arbitrary countable plan with source P and denote its source vectors by ψ j. Apply the source marginal to the quadratic forms normSq(3 ψ j 0−4 ψ j 1) and normSq(ψ j 2). Their nonnegative weighted sums are both zero because p=(4/5,3/5,0). Hence each positive-weight source term satisfies 3 ψ j 0=4 ψ j 1 and ψ j 2=0. Unit normalization then forces its projector to equal P. Its ground cost to any target v therefore equals the ground cost from p to v; zero-weight terms contribute nothing.

For the pointwise estimate take a complex unit vector v, and locally write z=v 0, w=v 1, q=|z|²+|w|², t=|v 2|², r=|−3z/5+4w/5|² and L=−9|z|²/25+16|w|²/25. Unit normalization gives q+t=1, and the orthogonal change of coordinates gives 1−|⟨p,v⟩|²=r+t. The exact algebraic certificate q r−L²=((12/25)q−Re(z conj(w)))²+Im(z conj(w))² is nonnegative, so L≤sqrt(q r). Furthermore sqrt(r+t)≥sqrt(q r)+t: after squaring, the difference of the squared sides is t(r+q−2 sqrt(q r)), which is nonnegative by the arithmetic–geometric mean inequality. Thus the ground distance is at least L+t. Equivalently it is at least (7/50)q−(|z|²−|w|²)/2+t. These identities retain the imaginary part explicitly and apply to all complex amplitudes.

Summation against the target marginal replaces the three coordinate masses by 49/100, 1/2 and 1/100. Every plan from P to σ therefore has cost at least −(9/25)(49/100)+(16/25)(1/2)+1/100=96/625. An explicit plan from P to σ uses the four target components of σ with constant source p, so this cost set is nonempty. Its infimum is at least 96/625. Since 96/625>3/20, the long side strictly exceeds the sum of the two short sides. The counterexample and the estimates are the construction here; the plans and distances are from the cited definitions.

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/CouplingWassersteinTriangleRefutation.Plan`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/CouplingWassersteinTriangleRefutation.UnitVector`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/CouplingWassersteinTriangleRefutation.claim`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/CouplingWassersteinTriangleRefutation.cost`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/CouplingWassersteinTriangleRefutation.ground`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/CouplingWassersteinTriangleRefutation.result`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/CouplingWassersteinTriangleRefutation.wasserstein`
- Dependency: [D5/S3/Quantum/Dynamics/EnergyEigenstateStationarity](../Dynamics/EnergyEigenstateStationarity.md)
- Dependency: [D5/S3/Quantum/PureState/PureStateHandshake](../PureState/PureStateHandshake.md)
- Dependency: [D5/S3/QuantumStates/DensitySpan](../../QuantumStates/DensitySpan.md)
