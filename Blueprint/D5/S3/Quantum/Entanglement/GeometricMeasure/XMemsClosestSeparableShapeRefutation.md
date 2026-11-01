# A closest separable state need not have the proposed X-MEMS shape

## Abstract

A fully separable three-qubit state is closer to an X-MEMS than every fully separable state of the proposed shape.

**Definition 1.1 (The low-branch X-MEMS matrix).**

$$\forall (n: \mathbb{N}), (\forall (\gamma: \mathbb{C}), ((\operatorname{D5.S3.Quantum.Entanglement.GeometricMeasure.XMemsClosestSeparableShapeRefutation.xmems}\left(n, \gamma\right): \operatorname{Matrix}\left((\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right)), \mathbb{C}\right)) = \lambda (x: (\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right))) \mapsto (\lambda (y: (\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right))) \mapsto (\operatorname{ite}\left(x = y, \operatorname{ite}\left((x = \operatorname{Function.const}\left(\operatorname{Fin}\left(n\right), (1: \operatorname{Fin}\left(2\right))\right)) \lor (\exists (k: \operatorname{Fin}\left(n\right)), ((\operatorname{Fin.val}\left(k\right) = (0: \mathbb{N})) \land (x\left(k\right) = (0: \operatorname{Fin}\left(2\right))))), \frac{(1: \mathbb{C})}{((2: \mathbb{C}))^{n - (1: \mathbb{N})} + (1: \mathbb{C})}, (0: \mathbb{C})\right), \operatorname{ite}\left((x = \operatorname{Function.const}\left(\operatorname{Fin}\left(n\right), (0: \operatorname{Fin}\left(2\right))\right)) \land (y = \operatorname{Function.const}\left(\operatorname{Fin}\left(n\right), (1: \operatorname{Fin}\left(2\right))\right)), \gamma, \operatorname{ite}\left((x = \operatorname{Function.const}\left(\operatorname{Fin}\left(n\right), (1: \operatorname{Fin}\left(2\right))\right)) \land (y = \operatorname{Function.const}\left(\operatorname{Fin}\left(n\right), (0: \operatorname{Fin}\left(2\right))\right)), \operatorname{Star.star}\left(\gamma\right), (0: \mathbb{C})\right)\right)\right)))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/GeometricMeasure/XMemsClosestSeparableShapeRefutation.xmems` (`✓ std3`).

*Citation.* Mirko Consiglio; Tony J. G. Apollaro; Marcin Wieśniak (2022). *Variational approach to the quantum separability problem*. DOI: [10.1103/PhysRevA.106.062413](https://doi.org/10.1103/PhysRevA.106.062413). URL: <https://arxiv.org/abs/2209.01430v2>.

*Commentary.*

The computational basis consists of functions from Fin n to Fin 2, with coordinate zero the most significant bit. The diagonal is 1/(2^(n-1)+1) at every word whose first bit is zero and at the all-one word, and zero elsewhere. The two opposite corners are gamma and its complex conjugate. This is the low branch of the matrix in PRA_v2.tex, lines 341-373, where f and g both equal 1/(N+1). The definition gives a matrix for every natural n and complex gamma; the low-branch bound and n at least two occur in claim. Subtraction n-1 is natural subtraction. Function.const denotes each constant bit string.

**Definition 1.2 (The proposed matrix shape).**

$$\forall (n: \mathbb{N}), (\forall (a: \mathbb{R}), (\forall (b: \mathbb{R}), (\forall (d: \mathbb{C}), ((\operatorname{D5.S3.Quantum.Entanglement.GeometricMeasure.XMemsClosestSeparableShapeRefutation.cssShape}\left(n, a, b, d\right): \operatorname{Matrix}\left((\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right)), \mathbb{C}\right)) = \lambda (x: (\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right))) \mapsto (\lambda (y: (\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right))) \mapsto (\operatorname{ite}\left(x = y, \operatorname{ite}\left((x = \operatorname{Function.const}\left(\operatorname{Fin}\left(n\right), (0: \operatorname{Fin}\left(2\right))\right)) \lor (x = \operatorname{Function.const}\left(\operatorname{Fin}\left(n\right), (1: \operatorname{Fin}\left(2\right))\right)), \operatorname{Complex.ofReal}\left(\frac{a}{(2: \mathbb{R})}\right), \operatorname{ite}\left(\exists (k: \operatorname{Fin}\left(n\right)), ((\operatorname{Fin.val}\left(k\right) = (0: \mathbb{N})) \land (x\left(k\right) = (0: \operatorname{Fin}\left(2\right)))), \operatorname{Complex.ofReal}\left(\frac{b}{((2: \mathbb{R}))^{n - (1: \mathbb{N})} - (1: \mathbb{R})}\right), \operatorname{Complex.ofReal}\left(\frac{(1: \mathbb{R}) - a - b}{((2: \mathbb{R}))^{n - (1: \mathbb{N})} - (1: \mathbb{R})}\right)\right)\right), \operatorname{ite}\left((x = \operatorname{Function.const}\left(\operatorname{Fin}\left(n\right), (0: \operatorname{Fin}\left(2\right))\right)) \land (y = \operatorname{Function.const}\left(\operatorname{Fin}\left(n\right), (1: \operatorname{Fin}\left(2\right))\right)), d, \operatorname{ite}\left((x = \operatorname{Function.const}\left(\operatorname{Fin}\left(n\right), (1: \operatorname{Fin}\left(2\right))\right)) \land (y = \operatorname{Function.const}\left(\operatorname{Fin}\left(n\right), (0: \operatorname{Fin}\left(2\right))\right)), \operatorname{Star.star}\left(d\right), (0: \mathbb{C})\right)\right)\right)))))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/GeometricMeasure/XMemsClosestSeparableShapeRefutation.cssShape` (`✓ std3`).

*Citation.* Mirko Consiglio; Tony J. G. Apollaro; Marcin Wieśniak (2022). *Variational approach to the quantum separability problem*. DOI: [10.1103/PhysRevA.106.062413](https://doi.org/10.1103/PhysRevA.106.062413). URL: <https://arxiv.org/abs/2209.01430v2>.

*Commentary.*

The all-zero and all-one diagonal entries are a/2. The other first-bit-zero entries are b/(2^(n-1)-1), and the remaining diagonal entries are (1-a-b)/(2^(n-1)-1). The opposite corners are d and its complex conjugate, and every other entry is zero. This is equation (A11), PRA_v2.tex, lines 459-474. Each real diagonal expression is included in the complex scalars by Complex.ofReal. The matrix is defined without restrictions on its parameters; IsCssShape supplies the stated restrictions.

**Definition 1.3 (The parameter restrictions).**

$$\forall (n: \mathbb{N}), (\forall (\sigma: \operatorname{Matrix}\left((\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right)), \mathbb{C}\right)), ((\operatorname{D5.S3.Quantum.Entanglement.GeometricMeasure.XMemsClosestSeparableShapeRefutation.IsCssShape}\left(\sigma\right): \operatorname{Prop}) = (\exists (a: \mathbb{R}), (\exists (b: \mathbb{R}), (\exists (d: \mathbb{C}), (((0: \mathbb{R}) \le a) \land ((a \le (1: \mathbb{R})) \land (((0: \mathbb{R}) \le b) \land ((b \le (1: \mathbb{R})) \land ((a + b \le (1: \mathbb{R})) \land ((\left\lVert d \right\rVert \le \frac{a}{(2: \mathbb{R})}) \land (\sigma = \operatorname{D5.S3.Quantum.Entanglement.GeometricMeasure.XMemsClosestSeparableShapeRefutation.cssShape}\left(n, a, b, d\right)))))))))))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/GeometricMeasure/XMemsClosestSeparableShapeRefutation.IsCssShape` (`✓ std3`).

*Citation.* Mirko Consiglio; Tony J. G. Apollaro; Marcin Wieśniak (2022). *Variational approach to the quantum separability problem*. DOI: [10.1103/PhysRevA.106.062413](https://doi.org/10.1103/PhysRevA.106.062413). URL: <https://arxiv.org/abs/2209.01430v2>.

*Commentary.*

A matrix has the proposed shape if it equals cssShape n a b d for real a and b in the unit interval with a+b at most one, and complex d with norm at most a/2. These are exactly the restrictions following equation (A11), PRA_v2.tex, line 474. Full separability is a separate requirement.

**Definition 1.4 (Squared Hilbert-Schmidt distance).**

$$\forall (n: \mathbb{N}), (\forall (\rho: \operatorname{Matrix}\left((\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right)), \mathbb{C}\right)), (\forall (\sigma: \operatorname{Matrix}\left((\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right)), \mathbb{C}\right)), ((\operatorname{D5.S3.Quantum.Entanglement.GeometricMeasure.XMemsClosestSeparableShapeRefutation.hsSq}\left(\rho, \sigma\right): \mathbb{R}) = \operatorname{D5.S3.Quantum.Tomography.RankOneContextCommutator.hilbertSchmidtSquare}\left(\rho - \sigma\right))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/GeometricMeasure/XMemsClosestSeparableShapeRefutation.hsSq` (`✓ std3`).

*Citation.* Mirko Consiglio; Tony J. G. Apollaro; Marcin Wieśniak (2022). *Variational approach to the quantum separability problem*. DOI: [10.1103/PhysRevA.106.062413](https://doi.org/10.1103/PhysRevA.106.062413). URL: <https://arxiv.org/abs/2209.01430v2>.

*Commentary.*

Apply the frozen D5.S3.Quantum.Tomography.RankOneContextCommutator.hilbertSchmidtSquare to the matrix difference. Unfolding it gives the real part of the trace of that difference conjugate-transpose multiplied by the difference. For density matrices this is the squared Hilbert-Schmidt distance called D_HS in PRA_v2.tex, lines 70-84. The formula also applies to arbitrary matrices, without a Hermitian hypothesis.

**Definition 1.5 (A closest fully separable state of the proposed shape).**

$$(\operatorname{D5.S3.Quantum.Entanglement.GeometricMeasure.XMemsClosestSeparableShapeRefutation.claim}: \operatorname{Prop}) = (\forall (n: \mathbb{N}), (((2: \mathbb{N}) \le n) \to (\forall (\gamma: \mathbb{C}), ((\left\lVert \gamma \right\rVert \le \frac{(1: \mathbb{R})}{((2: \mathbb{R}))^{n - (1: \mathbb{N})} + (1: \mathbb{R})}) \to (\exists (\sigma: \operatorname{Matrix}\left((\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right)), \mathbb{C}\right)), ((\operatorname{D5.S3.Quantum.Entanglement.FullySeparableExchangeObstruction.IsFullySeparableLocal}\left(\sigma\right)) \land ((\operatorname{D5.S3.Quantum.Entanglement.GeometricMeasure.XMemsClosestSeparableShapeRefutation.IsCssShape}\left(\sigma\right)) \land (\forall (\tau: \operatorname{Matrix}\left((\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right)), \mathbb{C}\right)), ((\operatorname{D5.S3.Quantum.Entanglement.FullySeparableExchangeObstruction.IsFullySeparableLocal}\left(\tau\right)) \to (\operatorname{D5.S3.Quantum.Entanglement.GeometricMeasure.XMemsClosestSeparableShapeRefutation.hsSq}\left(\operatorname{D5.S3.Quantum.Entanglement.GeometricMeasure.XMemsClosestSeparableShapeRefutation.xmems}\left(n, \gamma\right), \sigma\right) \le \operatorname{D5.S3.Quantum.Entanglement.GeometricMeasure.XMemsClosestSeparableShapeRefutation.hsSq}\left(\operatorname{D5.S3.Quantum.Entanglement.GeometricMeasure.XMemsClosestSeparableShapeRefutation.xmems}\left(n, \gamma\right), \tau\right)))))))))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/GeometricMeasure/XMemsClosestSeparableShapeRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mirko Consiglio; Tony J. G. Apollaro; Marcin Wieśniak (2022). *Variational approach to the quantum separability problem*. DOI: [10.1103/PhysRevA.106.062413](https://doi.org/10.1103/PhysRevA.106.062413). URL: <https://arxiv.org/abs/2209.01430v2>.

*Commentary.*

For every n at least two and every complex gamma of norm at most 1/(2^(n-1)+1), some fully separable matrix has the proposed shape and minimizes the squared Hilbert-Schmidt distance to xmems n gamma among all fully separable matrices. Full separability uses the frozen finite-mixture predicate D5.S3.Quantum.Entanglement.FullySeparableExchangeObstruction.IsFullySeparableLocal, applied to each matrix: it admits a finite mixture of products of local density states with nonnegative real weights summing to one. Each local density state is positive semidefinite with trace one. This is the low-branch reading of the conjecture in PRA_v2.tex, lines 459-474, using the closest-state definition at lines 80-93. It asserts attainment as well as comparison with every fully separable matrix, and it places no further restriction on the phase of gamma.

**Theorem 1.6 (The three-qubit obstruction at gamma equal to 11/112).**

$$\neg (\operatorname{D5.S3.Quantum.Entanglement.GeometricMeasure.XMemsClosestSeparableShapeRefutation.claim})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/GeometricMeasure/XMemsClosestSeparableShapeRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/consiglio-apollaro-wiesniak-2022-xmems-css-shape` (refuted) by `D5/S3/Quantum/Entanglement/GeometricMeasure/XMemsClosestSeparableShapeRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"consiglio-apollaro-wiesniak-2022-xmems-css-shape","declaration_gid":"D5/S3/Quantum/Entanglement/GeometricMeasure/XMemsClosestSeparableShapeRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Mirko Consiglio; Tony J. G. Apollaro; Marcin Wieśniak (2022). *Variational approach to the quantum separability problem*. DOI: [10.1103/PhysRevA.106.062413](https://doi.org/10.1103/PhysRevA.106.062413). URL: <https://arxiv.org/abs/2209.01430v2>.

*Commentary.*

First, the trace expression for hsSq equals the sum of the squared complex moduli of all entry differences. For three qubits, enumerate the eight binary words in order 000,001,010,011,100,101,110,111, denoted by indices 0 through 7 in the following calculations.

Consider a product P of three one-qubit density matrices. Put A_k equal to the real 00 diagonal entry of its kth factor and B_k equal to the real 11 entry. These numbers are nonnegative, and positivity bounds the squared modulus of each local 01 entry by A_k B_k. Consequently Re(P_07) is at most sqrt(product of A_k B_k). For nonnegative u,v, the arithmetic-geometric mean inequality is supplied by the frozen D5.S3.Geometry.Hyperideal.GramDomainContraction.twice_sqrt_product_le_add. It gives sqrt(uv) at most (u+v)/2; applying it to u/3 and 3v also gives sqrt(uv) at most u/6+3v/2.

Group the product under the square root as (A_0 A_1 B_2)(B_0 B_1 A_2). The weighted inequality then gives Re(P_07) at most P_11/6+3P_66/2. For a second bound, split the square root into sqrt(A_0 B_0) times sqrt(A_1 B_1 A_2 B_2). Bound the first factor by A_0/6+3B_0/2. For the term multiplied by A_0/6, bound the second factor by (A_1 A_2+B_1 B_2)/2; for the term multiplied by 3B_0/2, bound it by (A_1 B_2+B_1 A_2)/2. This yields Re(P_07) at most P_00/12+P_33/12+3P_55/4+3P_66/4. All displayed diagonal entries of P are real.

Combine the first bound with weight 1/5 and the second with weight 4/5. The resulting inequality defines a convex half-space because real parts of matrix entries are real-linear. It contains every product of density matrices and therefore their real convex hull. The proof identifies this convex hull with the frozen finite-mixture full-separability predicate. For a fully separable matrix cssShape 3 a b d, write s=a/2, B=b/3, C=(1-a-b)/3, r=Re(d) and t=Im(d). Substitution gives r at most s/15+B/10+3C/2.

Set rho=xmems 3 (11/112). Expanding its squared distance to cssShape 3 a b d gives 2(1/5-s)^2+3(1/5-B)^2+3C^2+2((11/112-r)^2+t^2). Since 2s+3B+3C=1, this equals 109/23520 plus 2(s-3/16)^2+3(B-3/16)^2+3(C-1/48)^2+2(r-1/16)^2+2t^2 plus (s/15+B/10+3C/2-r)/7. Every additional term is nonnegative for a fully separable matrix of this shape. Its squared distance is therefore at least 109/23520.

To construct a closer state, use the standard additive character chi of ZMod 3. For 0 at most u at most 1 and c in ZMod 3, use the frozen D5.S3.Quantum.Information.BargmannImaginaryMaximizers.Latitude.latitude at parameters 1-u and chi(c). Its coordinates are sqrt(u) and sqrt(1-u) chi(c). Its outer product with its conjugate is positive semidefinite; the frozen latitude_dot identity and star(chi(c)) chi(c)=1 give trace one. For a,b in ZMod 3, form the tensor product of these local densities at parameters (9/10,a), (199/400,b), and (199/400,-a-b).

Let m(x) be the product of the three nonnegative coordinate magnitudes at a binary word x. The x,y entry of the preceding tensor product is m(x)m(y) chi(a u+b v), where u=x(0)-y(0)-x(2)+y(2) and v=x(1)-y(1)-x(2)+y(2), with each bit included in ZMod 3. Character orthogonality makes the sum over a,b equal to 9m(x)m(y) when u=v=0, and zero otherwise. Among binary words, u=v=0 holds exactly on the diagonal and at the two opposite corners. The diagonal magnitudes squared are products of 9/10 or 1/10 and two factors 199/400 or 201/400; the opposite-corner magnitude product is 119997/1600000.

Define a matrix T with diagonal (356409,359991,359991,363609,39601,39999,39999,360401)/1920000, opposite corners 119997/1920000, and all other entries zero. The character sum shows that T equals 5/54 times the sum of the nine product densities just constructed, plus 1/6 times the projector onto 111. The latter is the product of the three local densities with u=0,c=0. Each row-average over b and then the average over a is fully separable by convexity. Taking weights 5/6 and 1/6 for that double average and the 111 projector proves that T is fully separable.

Entrywise evaluation gives hsSq rho T = 417965512477/90316800000000, strictly below 109/23520. Finally, claim at n=3 and gamma=11/112, whose norm is at most 1/5, would supply a fully separable matrix sigma of the proposed shape with hsSq rho sigma at most hsSq rho T. The lower bound on every such sigma contradicts this strict inequality. This excludes the proposed shape for a closest fully separable state in this instance; it does not identify the actual closest state or address the high branch.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/GeometricMeasure/XMemsClosestSeparableShapeRefutation.IsCssShape`
- Truth anchor: `D5/S3/Quantum/Entanglement/GeometricMeasure/XMemsClosestSeparableShapeRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Entanglement/GeometricMeasure/XMemsClosestSeparableShapeRefutation.cssShape`
- Truth anchor: `D5/S3/Quantum/Entanglement/GeometricMeasure/XMemsClosestSeparableShapeRefutation.hsSq`
- Truth anchor: `D5/S3/Quantum/Entanglement/GeometricMeasure/XMemsClosestSeparableShapeRefutation.result`
- Truth anchor: `D5/S3/Quantum/Entanglement/GeometricMeasure/XMemsClosestSeparableShapeRefutation.xmems`
- Dependency: [D5/S3/Geometry/Hyperideal/GramDomainContraction](../../../Geometry/Hyperideal/GramDomainContraction.md)
- Dependency: [D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums](../../Dynamics/CycleUniformMixing/OrbitIndexedSums.md)
- Dependency: [D5/S3/Quantum/Entanglement/FullySeparableExchangeObstruction](../FullySeparableExchangeObstruction.md)
- Dependency: [D5/S3/Quantum/Foundation/HilbertSchmidtTraceStability](../../Foundation/HilbertSchmidtTraceStability.md)
- Dependency: [D5/S3/Quantum/Information/BargmannImaginaryMaximizers](../../Information/BargmannImaginaryMaximizers.md)
- Dependency: [D5/S3/Quantum/Information/SLDSpectralEnergy](../../Information/SLDSpectralEnergy.md)
- Dependency: [D5/S3/Quantum/Magic/StabilizerAsymmetryShannonBoundRefutation](../../Magic/StabilizerAsymmetryShannonBoundRefutation.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/TwirlingPhaseRetrievabilityCounterexample](../../QuantumChannels/TwirlingPhaseRetrievabilityCounterexample.md)
