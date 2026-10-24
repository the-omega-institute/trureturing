# A quaternary refutation of the length-five extension expectation

## Abstract

The quaternary quantum extension property already fails at lengths one and three, so length five is not minimal.

**Definition 1.1 (The trace map on the quaternary field).**

$$\forall (x: \operatorname{K}\left(1\right)), (\operatorname{tr}\left(x\right) = (x) + (x^{2}))$$

*Formalization.* `D5/S3/Quantum/Codes/StabilizerExtensionQuaternaryMinimalLength.tr` (`✓ std3`).

*Citation.* Ali Assem Mahmoud (2026). *Minimal Counterexamples of the MacWilliams Extension Theorem for Stabilizer Codes*. DOI: [10.48550/arXiv.2607.26214](https://doi.org/10.48550/arXiv.2607.26214). URL: <https://arxiv.org/abs/2607.26214v1>.

*Commentary.*

The carrier K 1 is the four-element field 𝔽₄, and tr x = x + x squared is its trace to the binary subfield. The label alphabet HilbertPhase (K 1) is A₄ = 𝔽₄² in the source's notation (MzWi_Ext_Th.tex, lines 211–217).

**Definition 1.2 (The trace-symplectic pairing).**

$$\forall (n: \mathbb{N}), (\forall (u: \operatorname{Fin}\left(n\right) \to \operatorname{HilbertPhase}\left(\operatorname{K}\left(1\right)\right)), (\forall (v: \operatorname{Fin}\left(n\right) \to \operatorname{HilbertPhase}\left(\operatorname{K}\left(1\right)\right)), (\operatorname{symp}\left(u, v\right) = \operatorname{tr}\left(\sum_{(i: \operatorname{Fin}\left(n\right))} (((u\left(i\right).1) \cdot (v\left(i\right).2)) - ((v\left(i\right).1) \cdot (u\left(i\right).2)))\right))))$$

*Formalization.* `D5/S3/Quantum/Codes/StabilizerExtensionQuaternaryMinimalLength.symp` (`✓ std3`).

*Citation.* Ali Assem Mahmoud (2026). *Minimal Counterexamples of the MacWilliams Extension Theorem for Stabilizer Codes*. DOI: [10.48550/arXiv.2607.26214](https://doi.org/10.48550/arXiv.2607.26214). URL: <https://arxiv.org/abs/2607.26214v1>.

*Commentary.*

For two vectors u and v of labels, sum the determinant-like terms u_i.1 v_i.2 − v_i.1 u_i.2 and apply tr. The carrier HilbertPhase (K 1) is the label alphabet 𝔽₄², and the expression is the coordinate form of the trace-symplectic pairing in the source (MzWi_Ext_Th.tex, lines 211–215).

**Definition 1.3 (Trace-symplectic self-orthogonality).**

$$\forall (n: \mathbb{N}), (\forall (C: \operatorname{AddSubgroup}\left(\operatorname{Fin}\left(n\right) \to \operatorname{HilbertPhase}\left(\operatorname{K}\left(1\right)\right)\right)), ((\operatorname{selfOrthogonal}\left(C\right)) \Leftrightarrow (\forall (u: \operatorname{Fin}\left(n\right) \to \operatorname{HilbertPhase}\left(\operatorname{K}\left(1\right)\right)), ((u \in C) \Rightarrow (\forall (v: \operatorname{Fin}\left(n\right) \to \operatorname{HilbertPhase}\left(\operatorname{K}\left(1\right)\right)), ((v \in C) \Rightarrow (\operatorname{symp}\left(u, v\right) = (0: \operatorname{K}\left(1\right)))))))))$$

*Formalization.* `D5/S3/Quantum/Codes/StabilizerExtensionQuaternaryMinimalLength.selfOrthogonal` (`✓ std3`).

*Citation.* Ali Assem Mahmoud (2026). *Minimal Counterexamples of the MacWilliams Extension Theorem for Stabilizer Codes*. DOI: [10.48550/arXiv.2607.26214](https://doi.org/10.48550/arXiv.2607.26214). URL: <https://arxiv.org/abs/2607.26214v1>.

*Commentary.*

An additive subgroup C is self-orthogonal when the trace-symplectic pairing of every two of its elements is zero. This is the self-orthogonality condition imposed on additive stabilizer codes in the source (MzWi_Ext_Th.tex, lines 217 and 237–239).

**Definition 1.4 (A monomial extension witness).**

$$\forall (n: \mathbb{N}), (\forall (C: \operatorname{AddSubgroup}\left(\operatorname{Fin}\left(n\right) \to \operatorname{HilbertPhase}\left(\operatorname{K}\left(1\right)\right)\right)), (\forall (D: \operatorname{AddSubgroup}\left(\operatorname{Fin}\left(n\right) \to \operatorname{HilbertPhase}\left(\operatorname{K}\left(1\right)\right)\right)), (\forall (f: \operatorname{AddEquiv}\left(\operatorname{Subtype}\left(C\right), \operatorname{Subtype}\left(D\right)\right)), (\forall (\pi: \operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(n\right)\right)), (\forall (\tau: \operatorname{Fin}\left(n\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \operatorname{K}\left(1\right)\right)), ((\operatorname{qepWitness}\left(f, \pi, \tau\right)) \Leftrightarrow ((\forall (i: \operatorname{Fin}\left(n\right)), (\operatorname{Matrix.det}\left(\tau\left(i\right)\right) = (1: \operatorname{K}\left(1\right)))) \land (\forall (u: \operatorname{Subtype}\left(C\right)), (\forall (i: \operatorname{Fin}\left(n\right)), (\operatorname{coe}\left(f\left(u\right)\right)\left(i\right) = (\tau\left(i\right)) \cdot (\operatorname{coe}\left(u\right)\left(\operatorname{Equiv.symm}\left(\pi\right)\left(i\right)\right))))))))))))$$

*Formalization.* `D5/S3/Quantum/Codes/StabilizerExtensionQuaternaryMinimalLength.qepWitness` (`✓ std3`).

*Citation.* Ali Assem Mahmoud (2026). *Minimal Counterexamples of the MacWilliams Extension Theorem for Stabilizer Codes*. DOI: [10.48550/arXiv.2607.26214](https://doi.org/10.48550/arXiv.2607.26214). URL: <https://arxiv.org/abs/2607.26214v1>.

*Commentary.*

A permutation π of the coordinates and a determinant-one two-by-two matrix τ_i at each coordinate witness an extension when f u at coordinate i equals τ_i applied to u at the coordinate π⁻¹(i). The determinant-one condition is the concrete symplectic condition for the quaternary label alphabet, matching the monomial transformation in Definition 2.1 (MzWi_Ext_Th.tex, lines 221–223).

**Definition 1.5 (The quaternary quantum extension property).**

$$\forall (n: \mathbb{N}), ((\operatorname{QEP}\left(n\right)) \Leftrightarrow (\forall (C: \operatorname{AddSubgroup}\left(\operatorname{Fin}\left(n\right) \to \operatorname{HilbertPhase}\left(\operatorname{K}\left(1\right)\right)\right)), (\forall (D: \operatorname{AddSubgroup}\left(\operatorname{Fin}\left(n\right) \to \operatorname{HilbertPhase}\left(\operatorname{K}\left(1\right)\right)\right)), ((\operatorname{selfOrthogonal}\left(C\right)) \Rightarrow ((\operatorname{selfOrthogonal}\left(D\right)) \Rightarrow (\forall (f: \operatorname{AddEquiv}\left(\operatorname{Subtype}\left(C\right), \operatorname{Subtype}\left(D\right)\right)), ((\forall (u: \operatorname{Subtype}\left(C\right)), (\operatorname{hammingNorm}\left(\operatorname{coe}\left(f\left(u\right)\right)\right) = \operatorname{hammingNorm}\left(\operatorname{coe}\left(u\right)\right))) \Rightarrow (\exists (\pi: \operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(n\right)\right)), (\exists (\tau: \operatorname{Fin}\left(n\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \operatorname{K}\left(1\right)\right)), (\operatorname{qepWitness}\left(f, \pi, \tau\right)))))))))))$$

*Formalization.* `D5/S3/Quantum/Codes/StabilizerExtensionQuaternaryMinimalLength.QEP` (`✓ std3`).

*Citation.* Ali Assem Mahmoud (2026). *Minimal Counterexamples of the MacWilliams Extension Theorem for Stabilizer Codes*. DOI: [10.48550/arXiv.2607.26214](https://doi.org/10.48550/arXiv.2607.26214). URL: <https://arxiv.org/abs/2607.26214v1>.

*Commentary.*

QEP n asserts that every pair of self-orthogonal additive subgroups of the label alphabet at length n, together with every additive bijection preserving Hamming weight, has a witness of the preceding monomial form. This is the source's Definition 2.3 specialized to q = 4 (MzWi_Ext_Th.tex, lines 237–239).

**Definition 1.6 (The extension property for coordinate additive automorphisms).**

$$\forall (n: \mathbb{N}), ((\operatorname{QEPAdd}\left(n\right)) \Leftrightarrow (\forall (C: \operatorname{AddSubgroup}\left(\operatorname{Fin}\left(n\right) \to \operatorname{HilbertPhase}\left(\operatorname{K}\left(1\right)\right)\right)), (\forall (D: \operatorname{AddSubgroup}\left(\operatorname{Fin}\left(n\right) \to \operatorname{HilbertPhase}\left(\operatorname{K}\left(1\right)\right)\right)), ((\operatorname{selfOrthogonal}\left(C\right)) \Rightarrow ((\operatorname{selfOrthogonal}\left(D\right)) \Rightarrow (\forall (f: \operatorname{AddEquiv}\left(\operatorname{Subtype}\left(C\right), \operatorname{Subtype}\left(D\right)\right)), ((\forall (u: \operatorname{Subtype}\left(C\right)), (\operatorname{hammingNorm}\left(\operatorname{coe}\left(f\left(u\right)\right)\right) = \operatorname{hammingNorm}\left(\operatorname{coe}\left(u\right)\right))) \Rightarrow (\exists (\pi: \operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(n\right)\right)), (\exists (\tau: \operatorname{Fin}\left(n\right) \to \operatorname{AddEquiv}\left(\operatorname{HilbertPhase}\left(\operatorname{K}\left(1\right)\right), \operatorname{HilbertPhase}\left(\operatorname{K}\left(1\right)\right)\right)), (\forall (u: \operatorname{Subtype}\left(C\right)), (\forall (i: \operatorname{Fin}\left(n\right)), (\operatorname{coe}\left(f\left(u\right)\right)\left(i\right) = \tau\left(i\right)\left(\operatorname{coe}\left(u\right)\left(\operatorname{Equiv.symm}\left(\pi\right)\left(i\right)\right)\right)))))))))))))$$

*Formalization.* `D5/S3/Quantum/Codes/StabilizerExtensionQuaternaryMinimalLength.QEPAdd` (`✓ std3`).

*Citation.* Ali Assem Mahmoud (2026). *Minimal Counterexamples of the MacWilliams Extension Theorem for Stabilizer Codes*. DOI: [10.48550/arXiv.2607.26214](https://doi.org/10.48550/arXiv.2607.26214). URL: <https://arxiv.org/abs/2607.26214v1>.

*Commentary.*

QEPAdd n has the same hypotheses as QEP n, but permits an arbitrary additive equivalence of the label alphabet at each coordinate in the extension equation. For K 1 = 𝔽₄, this is the full coordinatewise additive-automorphism version described alongside the symplectic group in Definition 2.1 (MzWi_Ext_Th.tex, lines 221–223).

**Definition 1.7 (The expected minimal length five).**

$$(\operatorname{IsLeast}\left(\{n : \mathbb{N} \mid ((1: \mathbb{N}) \le n) \land (\neg (\operatorname{QEP}\left(n\right)))\}, (5: \mathbb{N})\right)) \lor (\operatorname{IsLeast}\left(\{n : \mathbb{N} \mid ((1: \mathbb{N}) \le n) \land (\neg (\operatorname{QEPAdd}\left(n\right)))\}, (5: \mathbb{N})\right))$$

*Formalization.* `D5/S3/Quantum/Codes/StabilizerExtensionQuaternaryMinimalLength.claim` (`✓ std3`).

*Citation.* Ali Assem Mahmoud (2026). *Minimal Counterexamples of the MacWilliams Extension Theorem for Stabilizer Codes*. DOI: [10.48550/arXiv.2607.26214](https://doi.org/10.48550/arXiv.2607.26214). URL: <https://arxiv.org/abs/2607.26214v1>.

*Commentary.*

The claim is the disjunction of two leastness assertions: either 5 is the least positive length where QEP fails, or 5 is the least positive length where QEPAdd fails. It is the q = 4 instance of the expectation that the minimal counterexample length is q + 1 (MzWi_Ext_Th.tex, lines 427–430).

**Theorem 1.8 (Lengths one and three refute the length-five claim).**

$$\neg ((\operatorname{IsLeast}\left(\{n : \mathbb{N} \mid ((1: \mathbb{N}) \le n) \land (\neg (\operatorname{QEP}\left(n\right)))\}, (5: \mathbb{N})\right)) \lor (\operatorname{IsLeast}\left(\{n : \mathbb{N} \mid ((1: \mathbb{N}) \le n) \land (\neg (\operatorname{QEPAdd}\left(n\right)))\}, (5: \mathbb{N})\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Codes/StabilizerExtensionQuaternaryMinimalLength.result` (`✓ std3`). ∎

*Resolves.* `Problems/mahmoud-2026-quaternary-extension-minimal-length-refutation` (refuted) by `D5/S3/Quantum/Codes/StabilizerExtensionQuaternaryMinimalLength.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"mahmoud-2026-quaternary-extension-minimal-length-refutation","declaration_gid":"D5/S3/Quantum/Codes/StabilizerExtensionQuaternaryMinimalLength.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Ali Assem Mahmoud (2026). *Minimal Counterexamples of the MacWilliams Extension Theorem for Stabilizer Codes*. DOI: [10.48550/arXiv.2607.26214](https://doi.org/10.48550/arXiv.2607.26214). URL: <https://arxiv.org/abs/2607.26214v1>.

*Commentary.*

Choose an element w of the four-element field with w different from 0 and 1. For length one, use the additive maps (a,b) ↦ (a + b w, 0) and (a,b) ↦ (a,b) from the binary pair space into the one-coordinate label alphabet. Their images are self-orthogonal, the induced additive equivalence preserves Hamming weight, and the only coordinate permutation is the identity. If a determinant-one matrix extended this equivalence, the image of (1,0) would force its lower-left entry to be zero; its action on the source label (w,0), corresponding to the binary parameter (0,1), would then force 1 = 0 times w, a contradiction. Thus QEP 1 fails.

For length three, use the additive maps (a,b) ↦ ((a,b w),(a,b w),(0,0)) and (a,b) ↦ ((a+b,0),(a,0),(b,0)). Their images are self-orthogonal and the induced equivalence preserves Hamming weight. If a coordinatewise additive extension existed, let j be the image of coordinate 2 under its permutation. Every vector in the first image is zero at coordinate 2, so every image under the extension is zero at j. Additive surjectivity would then make every element of the second image zero at j, but explicit elements of that image are nonzero at each of the three coordinates. This contradiction proves QEPAdd 3 fails.

The first leastness assertion in the claim cannot hold because 1 is a positive member of its failure set, and the second cannot hold because 3 is a positive member of its failure set. The two smaller counterexample lengths contradict the asserted least value 5.

## References

- Truth anchor: `D5/S3/Quantum/Codes/StabilizerExtensionQuaternaryMinimalLength.QEP`
- Truth anchor: `D5/S3/Quantum/Codes/StabilizerExtensionQuaternaryMinimalLength.QEPAdd`
- Truth anchor: `D5/S3/Quantum/Codes/StabilizerExtensionQuaternaryMinimalLength.claim`
- Truth anchor: `D5/S3/Quantum/Codes/StabilizerExtensionQuaternaryMinimalLength.qepWitness`
- Truth anchor: `D5/S3/Quantum/Codes/StabilizerExtensionQuaternaryMinimalLength.result`
- Truth anchor: `D5/S3/Quantum/Codes/StabilizerExtensionQuaternaryMinimalLength.selfOrthogonal`
- Truth anchor: `D5/S3/Quantum/Codes/StabilizerExtensionQuaternaryMinimalLength.symp`
- Truth anchor: `D5/S3/Quantum/Codes/StabilizerExtensionQuaternaryMinimalLength.tr`
- Dependency: [D5/S1/Recurrence/Residue/ExponentialSquareWeightCatalanParity](../../../S1/Recurrence/Residue/ExponentialSquareWeightCatalanParity.md)
- Dependency: [D5/S3/Observer/HilbertGeometry/GoldenAntiIsometry](../../Observer/HilbertGeometry/GoldenAntiIsometry.md)
- Dependency: [D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/FirstWindowBoundaryAttainment](../../ObserverMemory/Algorithms/KBonacciAcquisition/FirstWindowBoundaryAttainment.md)
- Dependency: [D5/S3/Quantum/Information/SingerQuadricQubitDistanceCeiling](../Information/SingerQuadricQubitDistanceCeiling.md)
