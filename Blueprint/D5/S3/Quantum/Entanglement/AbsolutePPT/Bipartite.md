# Generic matrix and cyclic-sector primitives

## Abstract

Shared partial transpose, universal APPT, and finite cyclic Fourier sectors.

Second-factor partial transpose acts on matrices indexed by a product of local types. APPT requires positivity after every global unitary conjugation. These definitions enter the dimension-general contraction decomposition and the five-row attaining family.

**Definition 1.1 (Second-factor partial transpose).**

$$\forall (A:Type), \forall (B:Type), \forall (M:Matrix\left((A\times B), (A\times B), \mathbb{C}\right)), \forall (p:(A\times B)), \forall (q:(A\times B)), partialTranspose\left(M, p, q\right)=M\left(Prod.mk\left(Prod.fst\left(p\right), Prod.snd\left(q\right)\right), Prod.mk\left(Prod.fst\left(q\right), Prod.snd\left(p\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/Bipartite.partialTranspose` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For arbitrary local index types A and B, the output entry at ((a,b),(c,d)) is the input entry at ((a,d),(c,b)). No finiteness, decidable equality, equal-cardinality, Hermitian or positivity assumption is imposed. The operation is definitionally equal to KickedIsingNegativityRefutation.partialTranspose over the same Type-star telescope.

**Definition 1.2 (All-unitary partial-transpose positivity).**

$$\forall (A:Type), \forall (B:Type), [Fintype\left(A\right)] [Fintype\left(B\right)] [DecidableEq\left(A\right)] [DecidableEq\left(B\right)] \forall (M:Matrix\left((A\times B), (A\times B), \mathbb{C}\right)), APPT\left(M\right)\iff \forall (U:unitaryGroup\left((A\times B), \mathbb{C}\right)), Matrix.PosSemidef\left(partialTranspose\left(((val\left(U\right)\cdot M)\cdot Matrix.conjTranspose\left(val\left(U\right)\right))\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/Bipartite.APPT` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every pair of finite local types with Fintype and DecidableEq instances, APPT M says that the second-factor partial transpose of U M U-adjoint is positive semidefinite for every global unitary on A times B. Empty and unequal local dimensions remain admitted. The Type-star telescope and full unitary group are exactly those of QutritPerturbationAttainment.APPT, which is definitionally equal to this predicate. ContractionAttainment.contraction_appt and five_row_attainment use this predicate.

**Definition 1.3 (The points of a cyclic sector).**

$$\forall (n:\mathbb{N}), \forall (d:\mathbb{N}), \forall (t:ZMod\left(d\right)), \forall (r:(Fin\left(n\right)) \to (ZMod\left(d\right))), \forall (k:Fin\left(n\right)), sectorPoint\left(t, r, k\right)=(t) + (r\left(k\right))$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/Bipartite.sectorPoint` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For natural n and d, a residue t and a string r of residues indexed by Fin n, sectorPoint t r is the string with kth entry t+r(k). Neither dimension is required to be nonzero.

**Definition 1.4 (The sector label of a string).**

$$\forall (n:\mathbb{N}), \forall (d:\mathbb{N}), (n \ne 0) \Rightarrow (\forall (i:(Fin\left(n\right)) \to (ZMod\left(d\right))), \forall (k:Fin\left(n\right)), sectorCoordinate\left(i, k\right)=(i\left(k\right)) - (i\left(0\right)))$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/Bipartite.sectorCoordinate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For nonzero n, subtract the zeroth coordinate from every coordinate. The resulting label has zeroth coordinate zero; d may be zero.

**Definition 1.5 (A normalized Fourier vector on a sector).**

$$\forall (n:\mathbb{N}), \forall (d:\mathbb{N}), (n \ne 0) \Rightarrow ((d \ne 0) \Rightarrow (\forall (a:ZMod\left(d\right)), \forall (r:(Fin\left(n\right)) \to (ZMod\left(d\right))), \forall (i:(Fin\left(n\right)) \to (ZMod\left(d\right))), fourierVector\left(a, r, i\right)=ite\left((i=sectorPoint\left(i\left(0\right), r\right)), (((Real.sqrt\left((d: \mathbb{R})\right): \mathbb{C})^{-1}\cdot ZMod.stdAddChar\left((a\cdot i\left(0\right))\right))), ((0: \mathbb{C}))\right)))$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/Bipartite.fourierVector` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For nonzero n and d, frequency a and label r, the coefficient at i is the inverse complex coercion of sqrt d times the standard additive character of a times i(0), when i equals sectorPoint i(0) r, and zero otherwise. Normalization and orthogonality are asserted for labels with zeroth coordinate zero by sector_basis.

**Theorem 1.6 (Recovering a string from its sector coordinates).**

$$\forall (n:\mathbb{N}), \forall (d:\mathbb{N}), (n \ne 0) \Rightarrow (\forall (i:(Fin\left(n\right)) \to (ZMod\left(d\right))), (sectorCoordinate\left(i, 0\right)=0) \land (sectorPoint\left(i\left(0\right), sectorCoordinate\left(i\right)\right)=i))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/Bipartite.sector_coordinates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For nonzero n and arbitrary d, the sector label of i vanishes at zero, and translating it by i(0) recovers i. This decomposes every string into its first coordinate and its normalized sector label.

**Theorem 1.7 (Uniqueness of normalized sector coordinates).**

$$\forall (n:\mathbb{N}), \forall (d:\mathbb{N}), (n \ne 0) \Rightarrow (\forall (r:(Fin\left(n\right)) \to (ZMod\left(d\right))), \forall (s:(Fin\left(n\right)) \to (ZMod\left(d\right))), (r\left(0\right)=0) \Rightarrow ((s\left(0\right)=0) \Rightarrow (\forall (t:ZMod\left(d\right)), \forall (u:ZMod\left(d\right)), (sectorPoint\left(t, r\right)=sectorPoint\left(u, s\right)) \Rightarrow ((t=u) \land (r=s)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/Bipartite.sectorPoint_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For nonzero n, normalized labels r and s and residues t and u, equality of sectorPoint t r and sectorPoint u s forces both t=u and r=s. Evaluation at zero identifies the translating residues, and cancellation identifies all label coordinates. No positivity assumption on d is needed.

**Theorem 1.8 (A Fourier coefficient at a sector point).**

$$\forall (n:\mathbb{N}), \forall (d:\mathbb{N}), (n \ne 0) \Rightarrow ((d \ne 0) \Rightarrow (\forall (a:ZMod\left(d\right)), \forall (t:ZMod\left(d\right)), \forall (r:(Fin\left(n\right)) \to (ZMod\left(d\right))), (r\left(0\right)=0) \Rightarrow (fourierVector\left(a, r, sectorPoint\left(t, r\right)\right)=((Real.sqrt\left((d: \mathbb{R})\right): \mathbb{C})^{-1}\cdot ZMod.stdAddChar\left((a\cdot t)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/Bipartite.fourier_at_point` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For nonzero n and d and a label r vanishing at zero, the Fourier coefficient at sectorPoint t r is exactly the inverse complex coercion of sqrt d times the standard character at a times t.

**Theorem 1.9 (Fourier coefficients vanish off their sector).**

$$\forall (n:\mathbb{N}), \forall (d:\mathbb{N}), (n \ne 0) \Rightarrow ((d \ne 0) \Rightarrow (\forall (a:ZMod\left(d\right)), \forall (r:(Fin\left(n\right)) \to (ZMod\left(d\right))), \forall (i:(Fin\left(n\right)) \to (ZMod\left(d\right))), (i \ne sectorPoint\left(i\left(0\right), r\right)) \Rightarrow (fourierVector\left(a, r, i\right)=(0: \mathbb{C}))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/Bipartite.fourier_off_sector` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For nonzero n and d, if i differs from sectorPoint i(0) r, the coefficient of fourierVector a r at i is zero. The label need not be normalized for this implication.

**Theorem 1.10 (Orthonormal Fourier vectors across cyclic sectors).**

$$\forall (n:\mathbb{N}), \forall (d:\mathbb{N}), (n \ne 0) \Rightarrow ((d \ne 0) \Rightarrow ((2 \le n) \Rightarrow ((2 \le d) \Rightarrow (\forall (a:ZMod\left(d\right)), \forall (c:ZMod\left(d\right)), \forall (r:(Fin\left(n\right)) \to (ZMod\left(d\right))), \forall (s:(Fin\left(n\right)) \to (ZMod\left(d\right))), (r\left(0\right)=0) \Rightarrow ((s\left(0\right)=0) \Rightarrow (\sum_{(i: (Fin\left(n\right)) \to (ZMod\left(d\right)))} ((star\left(fourierVector\left(a, r, i\right)\right)\cdot fourierVector\left(c, s, i\right)))=ite\left(((a=c) \land (r=s)), ((1: \mathbb{C})), ((0: \mathbb{C}))\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/Bipartite.sector_basis` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For n and d at least two, frequencies a and c and labels r and s vanishing at zero, the conjugate dot product of their Fourier vectors is one exactly when both frequencies and both labels agree, and zero otherwise. Distinct normalized sectors have disjoint support. In a fixed sector, summing the character at t times (c-a) gives d at equal frequencies and zero otherwise; the square-root normalization gives unit length. The hypotheses retain the stated bounds on both dimensions.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/Bipartite.APPT`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/Bipartite.fourierVector`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/Bipartite.fourier_at_point`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/Bipartite.fourier_off_sector`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/Bipartite.partialTranspose`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/Bipartite.sectorCoordinate`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/Bipartite.sectorPoint`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/Bipartite.sectorPoint_injective`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/Bipartite.sector_basis`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/Bipartite.sector_coordinates`
