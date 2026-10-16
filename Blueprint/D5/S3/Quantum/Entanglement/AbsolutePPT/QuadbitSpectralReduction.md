# Four-by-four APPT spectral reduction

## Abstract

Literal four-by-four APPT density matrices satisfy the two qutrit corner constraints on their largest three and smallest six spectral values.

**Definition 1.1 (The nine boundary values in dimension sixteen).**

$$\forall (l:Fin\left(16\right)\to \mathbb{R}), \forall (q:Fin\left(9\right)), boundaryValues16\left(l, q\right)=l\left((if val\left(q\right)<3 then val\left(q\right) else 7+val\left(q\right):Fin\left(16\right))\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitSpectralReduction.boundaryValues16` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Indices are zero-based. The boundary selector retains spectrum entries 0, 1, 2, 10, 11, 12, 13, 14, 15, and omits the seven middle values. The packing equivalence uses all sixteen coordinates; it does not change the physical local tensor factors.

**Theorem 1.2 (Four-by-four density-to-spectrum reduction).**

$$\forall (rho:Matrix\left((Fin\left(4\right)\times Fin\left(4\right)), (Fin\left(4\right)\times Fin\left(4\right)), \mathbb{C}\right)), ((Matrix.PosSemidef\left(rho\right))\land (Matrix.trace\left(rho\right)=1)\land (APPT\left(rho\right)))\Rightarrow \exists (l:Fin\left(16\right)\to \mathbb{R}), (Antitone\left(l\right))\land (\forall (i:Fin\left(16\right)), 0\leq l\left(i\right))\land (\sum_{i:Fin\left(16\right)} l\left(i\right)=1)\land (Matrix.PosSemidef\left(K1\left(boundaryValues16\left(l\right)\right)\right))\land (Matrix.PosSemidef\left(K2\left(boundaryValues16\left(l\right)\right)\right))\land (Complex.re\left(Matrix.trace\left(rho\cdot rho\right)\right)=\sum_{i:Fin\left(16\right)} (l\left(i\right))^{2})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitSpectralReduction.spectral_reduction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every positive semidefinite trace-one matrix on Fin 4 × Fin 4 that remains positive under partial transpose after every global unitary conjugation has an antitone nonnegative sixteen-coordinate spectrum of mass one. Its selected largest three and smallest six values satisfy both real qutrit boundary LMIs, and its real trace-square equals the sum of spectral squares. The proof reuses the existing ordered spectral diagonalization and the existing Bell calculation. It embeds that calculation into the genuine local Fin 3 × Fin 3 corner, extends each unitary by the identity on the seven complementary product positions, and compresses partial transpose only along product coordinates. An arbitrary global coordinate equivalence is used as a unitary packing, never as an asserted symmetry of partial transpose. These two constraints are necessary; this theorem does not assert that they characterize four-by-four APPT states. No statement about physical preparation or experimental observability is included. The bridge is consumed by the exact dimension-sixteen purity bound.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitSpectralReduction.boundaryValues16`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitSpectralReduction.spectral_reduction`
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/QutritHildebrandSufficiency](QutritHildebrandSufficiency.md)
