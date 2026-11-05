# One measurement does not force noncontextuality

## Abstract

One four-outcome qubit POVM generates a contextual subtheory that admits one-copy pseudo-broadcasting.

**Definition 1.1 (Convex quantum subtheories).**

$$\forall \left(d: \mathbb{N}\right), \left(\forall \left(t: \operatorname{Set}\left(\operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right)\right), \left(\forall \left(a: \operatorname{Set}\left(\operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right)\right), \left(\left(\operatorname{D5.S3.QuantumContext.SingleMeasurementPseudobroadcastingRefutation.Subtheory}\left(t, a\right)\right) \Leftrightarrow \left(\left(\operatorname{Convex}\left(\mathbb{R}, t\right)\right) \land \left(\left(\forall \left(\rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right), \left(\left(\rho \in t\right) \Rightarrow \left(\operatorname{D5.S3.QuantumChannels.CoPRelativeQuantumnessRefutation.IsDensity}\left(\rho\right)\right)\right)\right) \land \left(\left(\operatorname{Convex}\left(\mathbb{R}, a\right)\right) \land \left(\left(\forall \left(e: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right), \left(\left(e \in a\right) \Rightarrow \left(\left(\operatorname{Matrix.PosSemidef}\left(e\right)\right) \land \left(\operatorname{Matrix.PosSemidef}\left(\left(\left(1: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right)\right) - \left(e\right)\right)\right)\right)\right)\right) \land \left(\left(\left(1: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right) \in a\right) \land \left(\forall \left(e: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right), \left(\left(e \in a\right) \Rightarrow \left(\left(\left(1: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right)\right) - \left(e\right) \in a\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/QuantumContext/SingleMeasurementPseudobroadcastingRefutation.Subtheory` (`✓ std3`).

*Citation.* Pauli Jokinen; Mirjam Weilenmann; Martin Plávala; Juha-Pekka Pellonpää; Jukka Kiukas; Roope Uola (2024). *No-Broadcasting Characterizes Operational Contextuality*. DOI: [10.1103/PhysRevLett.133.240201](https://doi.org/10.1103/PhysRevLett.133.240201). URL: <https://arxiv.org/abs/2406.07305v1>.

*Commentary.*

The allowed states t form a convex set of density matrices. The allowed operators a form a convex set of effects: both e and 1 − e are positive semidefinite, the identity belongs to a, and a is closed under complements. This is the subtheory of arXiv:2406.07305v1, Arxiv.tex, line 321. The dimension d is arbitrary, including zero, and no nonemptiness condition is imposed on t.

**Definition 1.2 (Binary classical post-processings).**

$$\forall \left(d: \mathbb{N}\right), \left(\forall \left(m: \mathbb{N}\right), \left(\forall \left(p: \left(\operatorname{Fin}\left(m\right)\right) \to \left(\operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right)\right), \left(\operatorname{D5.S3.QuantumContext.SingleMeasurementPseudobroadcastingRefutation.postprocessings}\left(p\right) = \{e: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right) \mid \exists \left(c: \left(\operatorname{Fin}\left(m\right)\right) \to \left(\mathbb{R}\right)\right), \left(\left(\forall \left(o: \operatorname{Fin}\left(m\right)\right), \left(\left(\left(0: \mathbb{R}\right) \le c\left(o\right)\right) \land \left(c\left(o\right) \le \left(1: \mathbb{R}\right)\right)\right)\right) \land \left(e = \sum_{o: \operatorname{Fin}\left(m\right)} \left(\left(\operatorname{Complex.ofReal}\left(c\left(o\right)\right)\right) \cdot \left(p\left(o\right)\right)\right)\right)\right)\}\right)\right)\right)$$

*Formalization.* `D5/S3/QuantumContext/SingleMeasurementPseudobroadcastingRefutation.postprocessings` (`✓ std3`).

*Citation.* Pauli Jokinen; Mirjam Weilenmann; Martin Plávala; Juha-Pekka Pellonpää; Jukka Kiukas; Roope Uola (2024). *No-Broadcasting Characterizes Operational Contextuality*. DOI: [10.1103/PhysRevLett.133.240201](https://doi.org/10.1103/PhysRevLett.133.240201). URL: <https://arxiv.org/abs/2406.07305v1>.

*Commentary.*

For a finite family p of matrices, choose one real coefficient c o in the unit interval for each outcome o, and sum the matrices with these coefficients. Each coefficient is explicitly included in the complex scalars. For a POVM this is one effect of a binary classical post-processing, with the other effect obtained from the coefficients 1 − c o. The source defines classical post-processing in Arxiv.tex, line 275. The definition also applies to families that are not POVMs.

**Definition 1.3 (Generation by k finite POVMs).**

$$\forall \left(d: \mathbb{N}\right), \left(\forall \left(a: \operatorname{Set}\left(\operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right)\right), \left(\forall \left(k: \mathbb{N}\right), \left(\left(\operatorname{D5.S3.QuantumContext.SingleMeasurementPseudobroadcastingRefutation.GeneratedBy}\left(a, k\right)\right) \Leftrightarrow \left(\exists \left(m: \left(\operatorname{Fin}\left(k\right)\right) \to \left(\mathbb{N}\right)\right), \left(\exists \left(p: \left(j: \operatorname{Fin}\left(k\right)\right) \to \left(\left(\operatorname{Fin}\left(m\left(j\right)\right)\right) \to \left(\operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right)\right)\right), \left(\left(\forall \left(j: \operatorname{Fin}\left(k\right)\right), \left(\operatorname{D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation.IsPOVM}\left(p\left(j\right)\right)\right)\right) \land \left(a = \operatorname{convexHull}\left(\mathbb{R}, \cup_{j: \operatorname{Fin}\left(k\right)} \left(\operatorname{D5.S3.QuantumContext.SingleMeasurementPseudobroadcastingRefutation.postprocessings}\left(p\left(j\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/QuantumContext/SingleMeasurementPseudobroadcastingRefutation.GeneratedBy` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Pauli Jokinen; Mirjam Weilenmann; Martin Plávala; Juha-Pekka Pellonpää; Jukka Kiukas; Roope Uola (2024). *No-Broadcasting Characterizes Operational Contextuality*. DOI: [10.1103/PhysRevLett.133.240201](https://doi.org/10.1103/PhysRevLett.133.240201). URL: <https://arxiv.org/abs/2406.07305v1>.

*Commentary.*

For each j in Fin k, choose a natural outcome count m j and a POVM p j. The set a is exactly the real convex hull of the union of their binary classical post-processings. This specifies the meaning of generation used here for the question in Arxiv.tex, lines 348 and 482. The generators need not be independent or distinct, and k need not be positive.

**Definition 1.4 (Keeping one tensor coordinate).**

$$\forall \left(d: \mathbb{N}\right), \left(\forall \left(n: \mathbb{N}\right), \left(\forall \left(i: \operatorname{Fin}\left(n\right)\right), \left(\forall \left(x: \operatorname{Matrix}\left(\left(\operatorname{Fin}\left(n\right)\right) \to \left(\operatorname{Fin}\left(d\right)\right), \left(\operatorname{Fin}\left(n\right)\right) \to \left(\operatorname{Fin}\left(d\right)\right), \mathbb{C}\right)\right), \left(\left(\operatorname{D5.S3.QuantumContext.SingleMeasurementPseudobroadcastingRefutation.partialTraceKeep}\left(i, x\right): \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right) = \operatorname{D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight}\left(\operatorname{Matrix.submatrix}\left(x, \lambda \left(z: \operatorname{Prod}\left(\operatorname{Fin}\left(d\right), \left(\operatorname{Subtype}\left(\lambda \left(j: \operatorname{Fin}\left(n\right)\right) \mapsto \left(j \ne i\right)\right)\right) \to \left(\operatorname{Fin}\left(d\right)\right)\right)\right) \mapsto \left(\lambda \left(j: \operatorname{Fin}\left(n\right)\right) \mapsto \left(\operatorname{dite}\left(j = i, \operatorname{Function.const}\left(j = i, \operatorname{Prod.fst}\left(z\right)\right), \lambda \left(h: \neg \left(j = i\right)\right) \mapsto \left(\operatorname{Prod.snd}\left(z\right)\left(\operatorname{Subtype.mk}\left(j, h\right)\right)\right)\right)\right)\right), \lambda \left(z: \operatorname{Prod}\left(\operatorname{Fin}\left(d\right), \left(\operatorname{Subtype}\left(\lambda \left(j: \operatorname{Fin}\left(n\right)\right) \mapsto \left(j \ne i\right)\right)\right) \to \left(\operatorname{Fin}\left(d\right)\right)\right)\right) \mapsto \left(\lambda \left(j: \operatorname{Fin}\left(n\right)\right) \mapsto \left(\operatorname{dite}\left(j = i, \operatorname{Function.const}\left(j = i, \operatorname{Prod.fst}\left(z\right)\right), \lambda \left(h: \neg \left(j = i\right)\right) \mapsto \left(\operatorname{Prod.snd}\left(z\right)\left(\operatorname{Subtype.mk}\left(j, h\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/QuantumContext/SingleMeasurementPseudobroadcastingRefutation.partialTraceKeep` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Pauli Jokinen; Mirjam Weilenmann; Martin Plávala; Juha-Pekka Pellonpää; Jukka Kiukas; Roope Uola (2024). *No-Broadcasting Characterizes Operational Contextuality*. DOI: [10.1103/PhysRevLett.133.240201](https://doi.org/10.1103/PhysRevLett.133.240201). URL: <https://arxiv.org/abs/2406.07305v1>.

*Commentary.*

A tensor basis label is a function from Fin n to Fin d. Split it into its coordinate at i and its function on the remaining coordinates. Reindex both matrix indices by this splitting and trace out the second factor. In the displayed dependent conditional, the equal branch is constant on proofs of j = i; the unequal branch uses its proof h to form an index of the remaining coordinates.

**Definition 1.5 (Pseudo-broadcasting to n copies).**

$$\forall \left(d: \mathbb{N}\right), \left(\forall \left(t: \operatorname{Set}\left(\operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right)\right), \left(\forall \left(a: \operatorname{Set}\left(\operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right)\right), \left(\forall \left(n: \mathbb{N}\right), \left(\left(\operatorname{D5.S3.QuantumContext.SingleMeasurementPseudobroadcastingRefutation.PseudoBroadcastable}\left(t, a, n\right)\right) \Leftrightarrow \left(\exists \left(\xi: \operatorname{LinearMap}\left(\mathbb{C}, \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right), \operatorname{Matrix}\left(\left(\operatorname{Fin}\left(n\right)\right) \to \left(\operatorname{Fin}\left(d\right)\right), \left(\operatorname{Fin}\left(n\right)\right) \to \left(\operatorname{Fin}\left(d\right)\right), \mathbb{C}\right)\right)\right), \left(\left(\forall \left(x: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right), \left(\operatorname{Matrix.trace}\left(\xi\left(x\right)\right) = \operatorname{Matrix.trace}\left(x\right)\right)\right) \land \left(\left(\forall \left(i: \operatorname{Fin}\left(n\right)\right), \left(\forall \left(\rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right), \left(\left(\rho \in t\right) \Rightarrow \left(\forall \left(e: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right), \left(\left(e \in a\right) \Rightarrow \left(\operatorname{Matrix.trace}\left(\left(e\right) \cdot \left(\operatorname{D5.S3.QuantumContext.SingleMeasurementPseudobroadcastingRefutation.partialTraceKeep}\left(i, \xi\left(\rho\right)\right)\right)\right) = \operatorname{Matrix.trace}\left(\left(e\right) \cdot \left(\rho\right)\right)\right)\right)\right)\right)\right)\right) \land \left(\forall \left(\rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right), \left(\left(\rho \in t\right) \Rightarrow \left(\forall \left(e: \left(\operatorname{Fin}\left(n\right)\right) \to \left(\operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right)\right), \left(\left(\forall \left(i: \operatorname{Fin}\left(n\right)\right), \left(e\left(i\right) \in a\right)\right) \Rightarrow \left(\left(0: \mathbb{C}\right) \le \operatorname{Matrix.trace}\left(\left(\xi\left(\rho\right)\right) \cdot \left(\operatorname{D5.S3.Quantum.Recovery.ProductPrefixRigidity.productMap}\left(\operatorname{Function.const}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(d\right)\right), e\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/QuantumContext/SingleMeasurementPseudobroadcastingRefutation.PseudoBroadcastable` (`✓ std3`).

*Citation.* Pauli Jokinen; Mirjam Weilenmann; Martin Plávala; Juha-Pekka Pellonpää; Jukka Kiukas; Roope Uola (2024). *No-Broadcasting Characterizes Operational Contextuality*. DOI: [10.1103/PhysRevLett.133.240201](https://doi.org/10.1103/PhysRevLett.133.240201). URL: <https://arxiv.org/abs/2406.07305v1>.

*Commentary.*

There is a complex linear map ξ into the n-fold tensor matrix space. It preserves the trace of every input matrix, preserves every allowed one-coordinate expectation, and gives nonnegative expectations for every product of allowed effects. Complete positivity is not required. This is the common-effect-set case of Arxiv.tex, lines 328–333. The constant family Function.const takes domain Fin n and value Fin d. All traces and their zero bounds are complex; the order on complex numbers requires a nonnegative real part and zero imaginary part.

**Definition 1.6 (A preparation and measurement noncontextual model).**

$$\forall \left(d: \mathbb{N}\right), \left(\forall \left(t: \operatorname{Set}\left(\operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right)\right), \left(\forall \left(a: \operatorname{Set}\left(\operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right)\right), \left(\left(\operatorname{D5.S3.QuantumContext.SingleMeasurementPseudobroadcastingRefutation.Noncontextual}\left(t, a\right)\right) \Leftrightarrow \left(\exists \left(\iota: \operatorname{Type}\right), \left(\exists \left(g: \left(\iota\right) \to \left(\operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right)\right), \left(\exists \left(s: \left(\iota\right) \to \left(\operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right)\right), \left(\left(\forall \left(l: \iota\right), \left(\forall \left(\rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right), \left(\left(\rho \in t\right) \Rightarrow \left(\left(0: \mathbb{C}\right) \le \operatorname{Matrix.trace}\left(\left(\rho\right) \cdot \left(g\left(l\right)\right)\right)\right)\right)\right)\right) \land \left(\left(\forall \left(\rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right), \left(\left(\rho \in t\right) \Rightarrow \left(\operatorname{HasSum}\left(\lambda \left(l: \iota\right) \mapsto \left(\operatorname{Matrix.trace}\left(\left(\rho\right) \cdot \left(g\left(l\right)\right)\right)\right), \left(1: \mathbb{C}\right)\right)\right)\right)\right) \land \left(\left(\forall \left(l: \iota\right), \left(\forall \left(e: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right), \left(\left(e \in a\right) \Rightarrow \left(\left(0: \mathbb{C}\right) \le \operatorname{Matrix.trace}\left(\left(s\left(l\right)\right) \cdot \left(e\right)\right)\right)\right)\right)\right) \land \left(\left(\forall \left(l: \iota\right), \left(\operatorname{Matrix.trace}\left(s\left(l\right)\right) = \left(1: \mathbb{C}\right)\right)\right) \land \left(\forall \left(\rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right), \left(\left(\rho \in t\right) \Rightarrow \left(\forall \left(e: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right), \left(\left(e \in a\right) \Rightarrow \left(\operatorname{HasSum}\left(\lambda \left(l: \iota\right) \mapsto \left(\left(\operatorname{Matrix.trace}\left(\left(\rho\right) \cdot \left(g\left(l\right)\right)\right)\right) \cdot \left(\operatorname{Matrix.trace}\left(\left(s\left(l\right)\right) \cdot \left(e\right)\right)\right)\right), \operatorname{Matrix.trace}\left(\left(\rho\right) \cdot \left(e\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/QuantumContext/SingleMeasurementPseudobroadcastingRefutation.Noncontextual` (`✓ std3`).

*Citation.* Pauli Jokinen; Mirjam Weilenmann; Martin Plávala; Juha-Pekka Pellonpää; Jukka Kiukas; Roope Uola (2024). *No-Broadcasting Characterizes Operational Contextuality*. DOI: [10.1103/PhysRevLett.133.240201](https://doi.org/10.1103/PhysRevLett.133.240201). URL: <https://arxiv.org/abs/2406.07305v1>.

*Commentary.*

Choose any type ι of hidden labels and two matrix families g and s. For every allowed state, its traces against g are nonnegative and sum to one. Each s l has trace one and gives nonnegative responses on the allowed effects. The sum of preparation weight times response reproduces every allowed Born probability. HasSum expresses convergence over arbitrary finite subsets of ι; neither a finite label set nor global positivity of g and s is required. These are the restricted positivity and normalization requirements of Arxiv.tex, lines 321–326.

**Definition 1.7 (The equivalence for k generating measurements).**

$$\left(\operatorname{D5.S3.QuantumContext.SingleMeasurementPseudobroadcastingRefutation.claim}\right) \Leftrightarrow \left(\forall \left(d: \mathbb{N}\right), \left(\forall \left(k: \mathbb{N}\right), \left(\forall \left(t: \operatorname{Set}\left(\operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right)\right), \left(\forall \left(a: \operatorname{Set}\left(\operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right)\right), \left(\left(\operatorname{D5.S3.QuantumContext.SingleMeasurementPseudobroadcastingRefutation.Subtheory}\left(t, a\right)\right) \Rightarrow \left(\left(\operatorname{D5.S3.QuantumContext.SingleMeasurementPseudobroadcastingRefutation.GeneratedBy}\left(a, k\right)\right) \Rightarrow \left(\left(\operatorname{D5.S3.QuantumContext.SingleMeasurementPseudobroadcastingRefutation.PseudoBroadcastable}\left(t, a, k\right)\right) \Leftrightarrow \left(\operatorname{D5.S3.QuantumContext.SingleMeasurementPseudobroadcastingRefutation.Noncontextual}\left(t, a\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/QuantumContext/SingleMeasurementPseudobroadcastingRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Pauli Jokinen; Mirjam Weilenmann; Martin Plávala; Juha-Pekka Pellonpää; Jukka Kiukas; Roope Uola (2024). *No-Broadcasting Characterizes Operational Contextuality*. DOI: [10.1103/PhysRevLett.133.240201](https://doi.org/10.1103/PhysRevLett.133.240201). URL: <https://arxiv.org/abs/2406.07305v1>.

*Commentary.*

For all natural dimensions d and all natural k, a subtheory generated by k finite POVMs admits k-copy pseudo-broadcasting if and only if it has a preparation and measurement noncontextual model. The source asks for this equivalence in Arxiv.tex, lines 348 and 482. The displayed statement uses the precise generation condition above and includes k = 0; its failure will occur at the positive value k = 1.

**Theorem 1.8 (A qubit counterexample at k equal to one).**

$$\neg \left(\operatorname{D5.S3.QuantumContext.SingleMeasurementPseudobroadcastingRefutation.claim}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumContext/SingleMeasurementPseudobroadcastingRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/jokinen-et-al-2024-k-measurement-pseudobroadcasting` (refuted) by `D5/S3/QuantumContext/SingleMeasurementPseudobroadcastingRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"jokinen-et-al-2024-k-measurement-pseudobroadcasting","declaration_gid":"D5/S3/QuantumContext/SingleMeasurementPseudobroadcastingRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Pauli Jokinen; Mirjam Weilenmann; Martin Plávala; Juha-Pekka Pellonpää; Jukka Kiukas; Roope Uola (2024). *No-Broadcasting Characterizes Operational Contextuality*. DOI: [10.1103/PhysRevLett.133.240201](https://doi.org/10.1103/PhysRevLett.133.240201). URL: <https://arxiv.org/abs/2406.07305v1>.

*Commentary.*

Take four complex column vectors v₀ = (3,1), v₁ = (1,3), v₂ = (3,−1), v₃ = (1,−3), and the states ρⱼ = vⱼvⱼ*/10. Take four vectors w₀ = (1,1), w₁ = (1,−1), w₂ = (1,0), w₃ = (0,1), and operators M₀ = w₀w₀*/4, M₁ = w₁w₁*/4, M₂ = w₂w₂*/2, M₃ = w₃w₃*/2. Outer-product positivity and the squared norms of the vⱼ show that each ρⱼ is a density matrix. The Mₒ are positive semidefinite and their sum is the identity, so they form a POVM.

The binary post-processings of any finite matrix family form the linear image of a real unit cube and are therefore convex. For a POVM, replacing each coefficient c o by 1 − c o gives the complement of the corresponding effect. Nonnegative coefficients give positive semidefinite operators. Each Mₒ belongs to this set by choosing its coordinate indicator. Let T be the convex hull of the four ρⱼ and A the convex hull of the post-processings of M. Convexity makes A equal to the post-processing set itself. Convexity of the density matrices gives the state condition for T; positivity of an effect and its complement gives the effect condition for A. Choosing every coefficient equal to one gives the identity. Thus T and A form a subtheory, and the single generator M proves GeneratedBy A 1.

Every subtheory admits one-copy pseudo-broadcasting. Identify the functions Fin 1 → Fin d with Fin d by evaluation at the unique coordinate, and let ξ be the induced complex linear reindexing of matrices. Reindexing preserves the trace. For the one-coordinate partial trace, the type of remaining coordinates is empty, so its function space has one element; the partial trace is consequently the original matrix. A product over Fin 1 is its sole factor. The remaining nonnegativity condition follows from the nonnegative trace of the product of a density matrix and a positive semidefinite effect.

For the numerical bound, let u,v,w,z be nonnegative real numbers with u + z = v + w, and let 0 ≤ x,y ≤ 1/2. Then [u(x+y) + v(x+1/2−y) + w(1/2−x+y) + z(1−x−y)]/4 ≤ 3(u+z)/8. To prove it, split according to the signs of u + v − w − z and u + w − v − z. In each of the four cases the bounds on x and y bound their respective affine contributions; the relation u + z = v + w gives the stated right side.

Direct matrix arithmetic gives ρ₀ + ρ₃ = ρ₁ + ρ₂ = 1 and M₀ + M₁ = M₂ + M₃ = 1/2 times the identity. Let ix = (0,0,1,1) and iz = (2,3,2,3), indexed by Fin 4. For every j, the two Born probabilities have sum tr(ρⱼ Mᵢₓⱼ) + tr(ρⱼ Mᵢ𝓏ⱼ) = 17/20.

Suppose a noncontextual model with label type ι and families g,s exists. Set μ j l = tr(ρⱼ g l) and r o l = tr(s l Mₒ). All four states and all four operators are allowed. Hence the μ and r are nonnegative complex numbers, each family μ j has sum one, and the products μ j l · r o l sum to tr(ρⱼ Mₒ). Linearity and the two state decompositions give μ 0 l + μ 3 l = μ 1 l + μ 2 l. Linearity, the two effect decompositions and tr(s l) = 1 give r 0 l + r 1 l = r 2 l + r 3 l = 1/2.

Apply the affine bound with u,v,w,z the real parts of μ 0 l, μ 1 l, μ 2 l, μ 3 l, and x,y the real parts of r 0 l,r 2 l. Nonnegativity supplies zero imaginary parts for the μ, and the response sums put x,y in the required half-interval. It follows pointwise that one quarter of the sum over j of Re[μ j l · (r (ix j) l + r (iz j) l)] is at most (3/8)·[Re(μ 0 l) + Re(μ 3 l)]. The latter two real weight families together have sum 2. For each j, adding the two reproduction identities and taking real parts shows that the corresponding score family has sum 17/20. Summing the four score families and dividing by four keeps this sum equal to 17/20. Monotonicity of these convergent sums would therefore give 17/20 ≤ (3/8)·2 = 3/4, a contradiction.

Finally, apply the asserted equivalence with d = 2, k = 1, t = T and a = A. The subtheory and single-generator properties supply its hypotheses, and the one-copy map supplies its pseudo-broadcasting side. Its noncontextual side contradicts the bound just proved. Thus the equivalence fails already for one finite qubit POVM.

## References

- Truth anchor: `D5/S3/QuantumContext/SingleMeasurementPseudobroadcastingRefutation.GeneratedBy`
- Truth anchor: `D5/S3/QuantumContext/SingleMeasurementPseudobroadcastingRefutation.Noncontextual`
- Truth anchor: `D5/S3/QuantumContext/SingleMeasurementPseudobroadcastingRefutation.PseudoBroadcastable`
- Truth anchor: `D5/S3/QuantumContext/SingleMeasurementPseudobroadcastingRefutation.Subtheory`
- Truth anchor: `D5/S3/QuantumContext/SingleMeasurementPseudobroadcastingRefutation.claim`
- Truth anchor: `D5/S3/QuantumContext/SingleMeasurementPseudobroadcastingRefutation.partialTraceKeep`
- Truth anchor: `D5/S3/QuantumContext/SingleMeasurementPseudobroadcastingRefutation.postprocessings`
- Truth anchor: `D5/S3/QuantumContext/SingleMeasurementPseudobroadcastingRefutation.result`
- Dependency: [D5/S3/Quantum/Information/PartialTraceMutualInformation](../Quantum/Information/PartialTraceMutualInformation.md)
- Dependency: [D5/S3/Quantum/Measurements/VisibleStateSpaceDimension](../Quantum/Measurements/VisibleStateSpaceDimension.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/ConcealmentKernelNecessityRefutation](../Quantum/QuantumChannels/ConcealmentKernelNecessityRefutation.md)
- Dependency: [D5/S3/Quantum/Recovery/PurifiedLocalPath](../Quantum/Recovery/PurifiedLocalPath.md)
