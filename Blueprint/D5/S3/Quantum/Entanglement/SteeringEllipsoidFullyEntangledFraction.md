# The fully entangled fraction and the steering-ellipsoid centre

## Abstract

Every two-qubit density matrix rho satisfies rho <= (2 - |c|)(1 tensor rho_B), where c is the centre of Alice's steering ellipsoid and rho_B is Bob's reduced state; hence its fully entangled fraction is at most 1 - |c|/2, and every value |c| = t in [0, 1] is attained by a state whose fully entangled fraction equals 1 - t/2. This proves Conjecture 2 of A. Milne, D. Jennings, S. Jevtic and T. Rudolph (arXiv:1404.3951).

**Definition 1.1 (The Pauli matrices).**

$$(\operatorname{pauli}\left(0\right) = \operatorname{pauliMatrix}\left(\operatorname{X}\right)) \land ((\operatorname{pauli}\left(1\right) = \operatorname{pauliMatrix}\left(\operatorname{Y}\right)) \land (\operatorname{pauli}\left(2\right) = \operatorname{pauliMatrix}\left(\operatorname{Z}\right)))$$

*Formalization.* `D5/S3/Quantum/Entanglement/SteeringEllipsoidFullyEntangledFraction.pauli` (`✓ std3`).

*Citation.* Antony Milne; David Jennings; Sania Jevtic; Terry Rudolph (2014). *Quantum correlations of two-qubit states with one maximally mixed marginal*. DOI: [10.1103/PhysRevA.90.024302](https://doi.org/10.1103/PhysRevA.90.024302). URL: <https://arxiv.org/abs/1404.3951v2>.

*Commentary.*

The three Pauli matrices sigma_x, sigma_y, sigma_z indexed by Fin 3. They are the Pauli matrices pauliMatrix of StabilizerPairLocalUnitaryInequivalence at the labels X, Y, Z: pauliMatrix X = qubitX = [[0, 1], [1, 0]], pauliMatrix Y = i qubitX qubitZ = [[0, -i], [i, 0]] and pauliMatrix Z = qubitZ = [[1, 0], [0, -1]]. Since Fin 3 has exactly the elements 0, 1, 2, the three displayed equations are the whole definition.

**Definition 1.2 (Alice's Bloch vector).**

$$\forall rho \in \operatorname{Matrix}\left((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right),\; \forall i \in \operatorname{Fin}\left(3\right),\; \operatorname{blochA}\left(rho, i\right) = \operatorname{re}\left(\operatorname{trace}\left(rho \cdot \operatorname{kronecker}\left(\operatorname{pauli}\left(i\right), 1\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/SteeringEllipsoidFullyEntangledFraction.blochA` (`✓ std3`).

*Citation.* Antony Milne; David Jennings; Sania Jevtic; Terry Rudolph (2014). *Quantum correlations of two-qubit states with one maximally mixed marginal*. DOI: [10.1103/PhysRevA.90.024302](https://doi.org/10.1103/PhysRevA.90.024302). URL: <https://arxiv.org/abs/1404.3951v2>.

*Commentary.*

A two-qubit operator is a complex matrix indexed by pairs of qubit indices, the first entry of the pair belonging to Alice and the second to Bob. Following the companion paper, Theta_{mu nu} = tr(rho sigma_mu tensor sigma_nu): Alice's Bloch vector has components a_i = Re tr(rho (sigma_i tensor 1)), where kronecker is the Kronecker product and 1 the two-by-two identity.

**Definition 1.3 (Bob's Bloch vector).**

$$\forall rho \in \operatorname{Matrix}\left((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right),\; \forall j \in \operatorname{Fin}\left(3\right),\; \operatorname{blochB}\left(rho, j\right) = \operatorname{re}\left(\operatorname{trace}\left(rho \cdot \operatorname{kronecker}\left(1, \operatorname{pauli}\left(j\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/SteeringEllipsoidFullyEntangledFraction.blochB` (`✓ std3`).

*Citation.* Antony Milne; David Jennings; Sania Jevtic; Terry Rudolph (2014). *Quantum correlations of two-qubit states with one maximally mixed marginal*. DOI: [10.1103/PhysRevA.90.024302](https://doi.org/10.1103/PhysRevA.90.024302). URL: <https://arxiv.org/abs/1404.3951v2>.

*Commentary.*

Bob's Bloch vector has components b_j = Re tr(rho (1 tensor sigma_j)).

**Definition 1.4 (The correlation matrix).**

$$\forall rho \in \operatorname{Matrix}\left((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right),\; \forall i \in \operatorname{Fin}\left(3\right),\; \forall j \in \operatorname{Fin}\left(3\right),\; \operatorname{corr}\left(rho, i, j\right) = \operatorname{re}\left(\operatorname{trace}\left(rho \cdot \operatorname{kronecker}\left(\operatorname{pauli}\left(i\right), \operatorname{pauli}\left(j\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/SteeringEllipsoidFullyEntangledFraction.corr` (`✓ std3`).

*Citation.* Antony Milne; David Jennings; Sania Jevtic; Terry Rudolph (2014). *Quantum correlations of two-qubit states with one maximally mixed marginal*. DOI: [10.1103/PhysRevA.90.024302](https://doi.org/10.1103/PhysRevA.90.024302). URL: <https://arxiv.org/abs/1404.3951v2>.

*Commentary.*

The correlation matrix has entries T_ij = Re tr(rho (sigma_i tensor sigma_j)), first index Alice.

**Definition 1.5 (Euclidean length).**

$$\forall v \in \operatorname{Fin}\left(3\right) \to \mathbb{R},\; \operatorname{vlen}\left(v\right) = \sqrt{\sum_{i:\operatorname{Fin}\left(3\right)} (v\left(i\right)^{2})}$$

*Formalization.* `D5/S3/Quantum/Entanglement/SteeringEllipsoidFullyEntangledFraction.vlen` (`✓ std3`).

*Citation.* Antony Milne; David Jennings; Sania Jevtic; Terry Rudolph (2014). *Quantum correlations of two-qubit states with one maximally mixed marginal*. DOI: [10.1103/PhysRevA.90.024302](https://doi.org/10.1103/PhysRevA.90.024302). URL: <https://arxiv.org/abs/1404.3951v2>.

*Commentary.*

The Euclidean length of a real three-vector, the square root of the sum of the squares of its components. The scalar c of the conjecture is the length of the centre vector: the paper writes “For c = (0, 0, c)” and plots against “the magnitude of the steering ellipsoid centre”.

**Definition 1.6 (The centre of the steering ellipsoid).**

$$\forall rho \in \operatorname{Matrix}\left((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right),\; \forall i \in \operatorname{Fin}\left(3\right),\; \operatorname{centre}\left(rho\right)\left(i\right) = \operatorname{ite}\left(\operatorname{vlen}\left(\operatorname{blochB}\left(rho\right)\right) = 1, \operatorname{blochA}\left(rho, i\right), \frac{\operatorname{blochA}\left(rho, i\right) - \sum_{j:\operatorname{Fin}\left(3\right)} (\operatorname{corr}\left(rho, i, j\right) \cdot \operatorname{blochB}\left(rho, j\right))}{1 - \operatorname{vlen}\left(\operatorname{blochB}\left(rho\right)\right)^{2}}\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/SteeringEllipsoidFullyEntangledFraction.centre` (`✓ std3`).

*Citation.* Antony Milne; David Jennings; Sania Jevtic; Terry Rudolph (2014). *Quantum correlations of two-qubit states with one maximally mixed marginal*. DOI: [10.1103/PhysRevA.90.024302](https://doi.org/10.1103/PhysRevA.90.024302). URL: <https://arxiv.org/abs/1404.3951v2>.

*Commentary.*

Section I of the paper: “Given all possible measurements by Bob, the set of Bloch vectors to which Alice can be steered forms her steering ellipsoid E inside the Bloch sphere. E is described by its centre c and a real, symmetric 3 x 3 matrix Q.” The companion paper of Jevtic, Pusey, Jennings and Rudolph (PRL 113, 020402) gives the centre: “This gives a steering ellipsoid centred at c_A = (a - T b)/(1 - b^2)”, and “If b = 1 then rho is a product state in which case there is no steering and the steering ellipsoid is the single point a.” The definition takes c = (a - T b)/(1 - |b|^2) when |b| is not 1 and c = a when |b| = 1; the display states it coordinate by coordinate, with (T b)_i the sum over j of T_ij b_j.

**Definition 1.7 (Maximally entangled vectors).**

$$\forall e \in (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)) \to \mathbb{C},\; \operatorname{IsMaxEntangled}\left(e\right) \Leftrightarrow ((\sum_{k:(\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right))} (\left\lVert e\left(k\right) \right\rVert^{2}) = 1) \land ((\operatorname{partialTraceRight}\left(\operatorname{vecMulVec}\left(e, \operatorname{star}\left(e\right)\right)\right) = \frac{1}{2} \cdot 1) \land (\operatorname{partialTraceLeft}\left(\operatorname{vecMulVec}\left(e, \operatorname{star}\left(e\right)\right)\right) = \frac{1}{2} \cdot 1)))$$

*Formalization.* `D5/S3/Quantum/Entanglement/SteeringEllipsoidFullyEntangledFraction.IsMaxEntangled` (`✓ std3`).

*Citation.* Antony Milne; David Jennings; Sania Jevtic; Terry Rudolph (2014). *Quantum correlations of two-qubit states with one maximally mixed marginal*. DOI: [10.1103/PhysRevA.90.024302](https://doi.org/10.1103/PhysRevA.90.024302). URL: <https://arxiv.org/abs/1404.3951v2>.

*Commentary.*

A two-qubit vector e is maximally entangled when it is a unit vector and both of its reduced states are half the identity: partialTraceRight traces out Bob and partialTraceLeft traces out Alice from the rank-one operator vecMulVec e (star e) = |e><e|, and (1/2) 1 is the scalar multiple of the identity. For two qubits these are exactly the vectors (U tensor V)(|00> + |11>)/sqrt 2 with U, V unitary.

**Definition 1.8 (The fully entangled fraction).**

$$\forall rho \in \operatorname{Matrix}\left((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right),\; \operatorname{fef}\left(rho\right) = \operatorname{sSup}\left(\{f \mid \exists e \in (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)) \to \mathbb{C},\; (\operatorname{IsMaxEntangled}\left(e\right)) \land (f = \operatorname{re}\left(\operatorname{dotProduct}\left(\operatorname{star}\left(e\right), \operatorname{mulVec}\left(rho, e\right)\right)\right))\}\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/SteeringEllipsoidFullyEntangledFraction.fef` (`✓ std3`).

*Citation.* Antony Milne; David Jennings; Sania Jevtic; Terry Rudolph (2014). *Quantum correlations of two-qubit states with one maximally mixed marginal*. DOI: [10.1103/PhysRevA.90.024302](https://doi.org/10.1103/PhysRevA.90.024302). URL: <https://arxiv.org/abs/1404.3951v2>.

*Commentary.*

Section III of the paper: “The fully entangled fraction of a bipartite state rho is defined by f(rho) = max_phi <phi| rho |phi>, where the maximum is taken over all maximally entangled states |phi>.” The definition takes the supremum of the real expectation Re <e| rho |e> = RealPart(star e . (rho e)) over all maximally entangled e; for a density matrix the set is non-empty and bounded, and attainment of the maximum is not used.

**Definition 1.9 (Conjecture 2).**

$$claim \Leftrightarrow ((\forall rho \in \operatorname{Matrix}\left((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right),\; (\operatorname{PosSemidef}\left(rho\right)) \Rightarrow \left((\operatorname{trace}\left(rho\right) = 1) \Rightarrow \operatorname{fef}\left(rho\right) \le 1 - \frac{\operatorname{vlen}\left(\operatorname{centre}\left(rho\right)\right)}{2}\right)) \land (\forall t \in \mathbb{R},\; (0 \le t) \Rightarrow \left((t \le 1) \Rightarrow \left(\exists rho \in \operatorname{Matrix}\left((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right),\; (\operatorname{PosSemidef}\left(rho\right)) \land ((\operatorname{trace}\left(rho\right) = 1) \land ((\operatorname{vlen}\left(\operatorname{centre}\left(rho\right)\right) = t) \land (\operatorname{fef}\left(rho\right) = 1 - \frac{t}{2})))\right)\right)))$$

*Formalization.* `D5/S3/Quantum/Entanglement/SteeringEllipsoidFullyEntangledFraction.claim` (`✓ std3`).

*Citation.* Antony Milne; David Jennings; Sania Jevtic; Terry Rudolph (2014). *Quantum correlations of two-qubit states with one maximally mixed marginal*. DOI: [10.1103/PhysRevA.90.024302](https://doi.org/10.1103/PhysRevA.90.024302). URL: <https://arxiv.org/abs/1404.3951v2>.

*Commentary.*

Section V, Conjecture 2: “Let rho be a general two-qubit state with E centred at c. The fully entangled fraction is tightly bounded as f(rho) <= 1 - c/2.” A two-qubit state is a positive semidefinite complex 4 x 4 matrix of trace 1. The first conjunct is the bound for every state; the second makes “tightly” precise: for every t in [0, 1] there is a state with |c| = t and fully entangled fraction exactly 1 - t/2.

**Theorem 1.10 (States with a maximally mixed Bob marginal).**

$$\forall sigma \in \operatorname{Matrix}\left((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right),\; (\operatorname{PosSemidef}\left(sigma\right)) \Rightarrow \left((\operatorname{partialTraceLeft}\left(sigma\right) = \frac{1}{2} \cdot 1) \Rightarrow \left(\forall phi \in (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)) \to \mathbb{C},\; \operatorname{re}\left(\operatorname{dotProduct}\left(\operatorname{star}\left(phi\right), \operatorname{mulVec}\left(sigma, phi\right)\right)\right) \le (1 - \frac{\operatorname{vlen}\left(\operatorname{blochA}\left(sigma\right)\right)}{2}) \cdot \operatorname{re}\left(\operatorname{dotProduct}\left(\operatorname{star}\left(phi\right), phi\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SteeringEllipsoidFullyEntangledFraction.canonical_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Antony Milne; David Jennings; Sania Jevtic; Terry Rudolph (2014). *Quantum correlations of two-qubit states with one maximally mixed marginal*. DOI: [10.1103/PhysRevA.90.024302](https://doi.org/10.1103/PhysRevA.90.024302). URL: <https://arxiv.org/abs/1404.3951v2>.

*Commentary.*

Let sigma be positive semidefinite with Bob marginal sigma_B = 1/2 (so its trace is 1), let a be the Bloch vector of its Alice marginal sigma_A, and let phi be a vector with t = <phi| sigma |phi> > 0. Put w = sigma phi. The Cauchy-Schwarz inequality for the positive form of sigma gives sigma >= w w^H / t and t^2 <= |phi|^2 |w|^2. For a two-by-two Hermitian X let rad X be the length of its Bloch vector, the difference of its eigenvalues; it is a seminorm, rad(sigma_A) = |a|, and rad Z <= tr Z for positive semidefinite Z because det Z >= 0. Taking Bob's marginal of sigma - w w^H / t gives 1/2 - tr_A(w w^H)/t >= 0, hence rad(tr_A w w^H)/t <= 1 - |w|^2/t. The two marginals of the rank-one operator w w^H have the same trace |w|^2 and the same determinant |det W|^2, W the coefficient matrix of w, so they have the same rad. Taking Alice's marginal, sigma_A = tr_B(w w^H)/t + Z with Z >= 0 and tr Z = 1 - |w|^2/t, so |a| <= rad(tr_B w w^H)/t + tr Z <= 2 - 2|w|^2/t <= 2 - 2t/|phi|^2. This is the bound; for t = 0 it follows from |a| <= 1.

**Theorem 1.11 (The operator inequality).**

$$\forall rho \in \operatorname{Matrix}\left((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right),\; (\operatorname{PosSemidef}\left(rho\right)) \Rightarrow \left((\operatorname{trace}\left(rho\right) = 1) \Rightarrow \left(\forall x \in (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)) \to \mathbb{C},\; \operatorname{re}\left(\operatorname{dotProduct}\left(\operatorname{star}\left(x\right), \operatorname{mulVec}\left(rho, x\right)\right)\right) \le (2 - \operatorname{vlen}\left(\operatorname{centre}\left(rho\right)\right)) \cdot \operatorname{re}\left(\operatorname{dotProduct}\left(\operatorname{star}\left(x\right), \operatorname{mulVec}\left(\operatorname{kronecker}\left(1, \operatorname{partialTraceLeft}\left(rho\right)\right), x\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SteeringEllipsoidFullyEntangledFraction.operator_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Antony Milne; David Jennings; Sania Jevtic; Terry Rudolph (2014). *Quantum correlations of two-qubit states with one maximally mixed marginal*. DOI: [10.1103/PhysRevA.90.024302](https://doi.org/10.1103/PhysRevA.90.024302). URL: <https://arxiv.org/abs/1404.3951v2>.

*Commentary.*

Let rho be a two-qubit density matrix with Bob marginal rho_B = [[p, q], [conj q, r]] and Bloch vector b, so that 1 - |b|^2 = 4d with d = pr - |q|^2 = det rho_B. If |b| < 1 then d > 0 and p > 0; with u = sqrt d the filters H = [[u, 0], [-conj q, p]] and G = [[p, 0], [conj q, u]] satisfy H rho_B H^H = p d 1, G H = p u 1, G G^H = p rho_B and H^H H = p (1 - rho_B). The filtered operator sigma = (1 tensor H) rho (1 tensor H)^H / (2 p d) is positive semidefinite with Bob marginal 1/2, and since 2(1 - rho_B) = 1 - b . sigma its Alice Bloch vector is (a - T b)/(1 - |b|^2) = c. Moreover rho = (2/p)(1 tensor G) sigma (1 tensor G)^H, so for y = (1 tensor G)^H x the bound for sigma gives Re <x| rho |x> = (2/p) Re <y| sigma |y> <= (2/p)(1 - |c|/2) p <x| 1 tensor rho_B |x>. If |b| = 1 then c = a and |a| <= 1, and it suffices to show Re <x| rho |x> <= <x| 1 tensor rho_B |x>: with t = <x| rho |x> > 0 and w = rho x, the Cauchy-Schwarz bound rho >= w w^H / t gives rho_B >= tr_A(w w^H)/t, and rad(rho_B) = tr rho_B = 1 forces rad = tr for tr_A(w w^H), so det W = 0. Then A = W conj(X)^T is a rank-one two-by-two matrix with tr A = <x|w> = t, and |tr A|^2 <= sum |A_ik|^2 = tr(tr_A(w w^H) tr_A(x x^H)) <= t tr(rho_B tr_A(x x^H)) = t <x| 1 tensor rho_B |x>.

**Theorem 1.12 (Proof of the conjecture).**

$$(\forall rho \in \operatorname{Matrix}\left((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right),\; (\operatorname{PosSemidef}\left(rho\right)) \Rightarrow \left((\operatorname{trace}\left(rho\right) = 1) \Rightarrow \operatorname{fef}\left(rho\right) \le 1 - \frac{\operatorname{vlen}\left(\operatorname{centre}\left(rho\right)\right)}{2}\right)) \land (\forall t \in \mathbb{R},\; (0 \le t) \Rightarrow \left((t \le 1) \Rightarrow \left(\exists rho \in \operatorname{Matrix}\left((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right),\; (\operatorname{PosSemidef}\left(rho\right)) \land ((\operatorname{trace}\left(rho\right) = 1) \land ((\operatorname{vlen}\left(\operatorname{centre}\left(rho\right)\right) = t) \land (\operatorname{fef}\left(rho\right) = 1 - \frac{t}{2})))\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SteeringEllipsoidFullyEntangledFraction.result` (`✓ std3`). ∎

*Resolves.* `Problems/milne-jennings-jevtic-rudolph-2014-fully-entangled-fraction` (proved) by `D5/S3/Quantum/Entanglement/SteeringEllipsoidFullyEntangledFraction.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"milne-jennings-jevtic-rudolph-2014-fully-entangled-fraction","declaration_gid":"D5/S3/Quantum/Entanglement/SteeringEllipsoidFullyEntangledFraction.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Antony Milne; David Jennings; Sania Jevtic; Terry Rudolph (2014). *Quantum correlations of two-qubit states with one maximally mixed marginal*. DOI: [10.1103/PhysRevA.90.024302](https://doi.org/10.1103/PhysRevA.90.024302). URL: <https://arxiv.org/abs/1404.3951v2>.

*Commentary.*

For a maximally entangled e the reduced state tr_A(e e^H) is 1/2, so <e| 1 tensor rho_B |e> = tr(rho_B)/2 = 1/2, and the operator inequality gives Re <e| rho |e> <= (2 - |c|)/2 = 1 - |c|/2; the vector ((1 + i)/2)(|00> + |11>), a phase multiple of (|00> + |11>)/sqrt 2, is maximally entangled, so the supremum is at most 1 - |c|/2. For tightness let 0 <= t <= 1, chi = |00> + (1 - t)|11> and rho_t = (|chi><chi| + t(1 - t)|01><01|)/(2 - t), a density matrix. Its Bloch data are a = (0, 0, t(3 - 2t)/(2 - t)), b = (0, 0, t/(2 - t)), T_xz = T_yz = 0 and T_zz = (2 - 3t + 2t^2)/(2 - t). For t < 1 one has |b| < 1 and c = (a - T b)/(1 - |b|^2) = (0, 0, t); for t = 1 the state is |00><00|, |b| = 1 and c = a = (0, 0, 1). In both cases |c| = t, and the phase multiple of (|00> + |11>)/sqrt 2 gives Re <e| rho_t |e> = (1 + 2(1 - t) + (1 - t)^2)/(2(2 - t)) = 1 - t/2, which together with the bound fixes the supremum.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/SteeringEllipsoidFullyEntangledFraction.IsMaxEntangled`
- Truth anchor: `D5/S3/Quantum/Entanglement/SteeringEllipsoidFullyEntangledFraction.blochA`
- Truth anchor: `D5/S3/Quantum/Entanglement/SteeringEllipsoidFullyEntangledFraction.blochB`
- Truth anchor: `D5/S3/Quantum/Entanglement/SteeringEllipsoidFullyEntangledFraction.canonical_bound`
- Truth anchor: `D5/S3/Quantum/Entanglement/SteeringEllipsoidFullyEntangledFraction.centre`
- Truth anchor: `D5/S3/Quantum/Entanglement/SteeringEllipsoidFullyEntangledFraction.claim`
- Truth anchor: `D5/S3/Quantum/Entanglement/SteeringEllipsoidFullyEntangledFraction.corr`
- Truth anchor: `D5/S3/Quantum/Entanglement/SteeringEllipsoidFullyEntangledFraction.fef`
- Truth anchor: `D5/S3/Quantum/Entanglement/SteeringEllipsoidFullyEntangledFraction.operator_bound`
- Truth anchor: `D5/S3/Quantum/Entanglement/SteeringEllipsoidFullyEntangledFraction.pauli`
- Truth anchor: `D5/S3/Quantum/Entanglement/SteeringEllipsoidFullyEntangledFraction.result`
- Truth anchor: `D5/S3/Quantum/Entanglement/SteeringEllipsoidFullyEntangledFraction.vlen`
- Dependency: [D5/S3/Quantum/FiniteDimensional](../FiniteDimensional.md)
- Dependency: [D5/S3/Quantum/Information/PartialTraceMutualInformation](../Information/PartialTraceMutualInformation.md)
- Dependency: [D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence](../Information/StabilizerPairLocalUnitaryInequivalence.md)
