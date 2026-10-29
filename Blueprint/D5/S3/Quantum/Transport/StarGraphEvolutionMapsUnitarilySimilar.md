# Unitary similarity of the two star-graph evolution maps

## Abstract

The two evolution maps of every quantum star graph are unitarily similar.

**Definition 1.1 (The star-graph scattering matrix).**

$$\forall (n: \mathbb{N}), (\forall (r: (\operatorname{Fin}\left((n) - (1)\right)) \to (\mathbb{C})), (\forall (r1: \mathbb{C}), (\forall (t1: \mathbb{C}), (\forall (p: \operatorname{Prod}\left(\operatorname{Fin}\left((n) - (1)\right), \operatorname{Fin}\left(2\right)\right)), (\forall (q: \operatorname{Prod}\left(\operatorname{Fin}\left((n) - (1)\right), \operatorname{Fin}\left(2\right)\right)), ((\operatorname{D5.S3.Quantum.Transport.StarGraphEvolutionMapsUnitarilySimilar.scatteringMatrix}\left(r, r1, t1, p, q\right): \mathbb{C}) = \operatorname{ite}\left(\operatorname{Prod.snd}\left(p\right) = (0: \operatorname{Fin}\left(2\right)), \operatorname{ite}\left((\operatorname{Prod.fst}\left(q\right) = \operatorname{Prod.fst}\left(p\right)) \land (\operatorname{Prod.snd}\left(q\right) = (1: \operatorname{Fin}\left(2\right))), r\left(\operatorname{Prod.fst}\left(p\right)\right), (0: \mathbb{C})\right), \operatorname{ite}\left(\operatorname{Prod.snd}\left(q\right) = (1: \operatorname{Fin}\left(2\right)), (0: \mathbb{C}), \operatorname{ite}\left(\operatorname{Prod.fst}\left(q\right) = \operatorname{Prod.fst}\left(p\right), r1, t1\right)\right)\right)))))))$$

*Formalization.* `D5/S3/Quantum/Transport/StarGraphEvolutionMapsUnitarilySimilar.scatteringMatrix` (`✓ std3`).

*Citation.* Fabiano M. Andrade; Simone Severini (2018). *Unitary equivalence between the Green's function and Schrödinger approaches for quantum graphs*. DOI: [10.1103/PhysRevA.98.062107](https://doi.org/10.1103/PhysRevA.98.062107). URL: <https://arxiv.org/abs/1808.01154v2>.

*Commentary.*

For a star with n vertices, the amplitude index is a pair consisting of an edge in Fin (n − 1) and a direction in Fin 2. A direction-zero row p has r(p.1) only in the same-edge direction-one column. A direction-one row has zero in direction-one columns, r1 in the same-edge direction-zero column, and t1 in every other direction-zero column. This is the matrix displayed for Sₙ in the source at TeX lines 383–405.

**Definition 1.2 (The diagonal propagation matrix).**

$$\forall (n: \mathbb{N}), (\forall (k: \mathbb{R}), (\forall (\ell: (\operatorname{Fin}\left((n) - (1)\right)) \to (\mathbb{R})), ((\operatorname{D5.S3.Quantum.Transport.StarGraphEvolutionMapsUnitarilySimilar.propagationMatrix}\left(k, \ell\right): \operatorname{Matrix}\left(\operatorname{Prod}\left(\operatorname{Fin}\left((n) - (1)\right), \operatorname{Fin}\left(2\right)\right), \operatorname{Prod}\left(\operatorname{Fin}\left((n) - (1)\right), \operatorname{Fin}\left(2\right)\right), \mathbb{C}\right)) = \operatorname{Matrix.diagonal}\left(\lambda (p: \operatorname{Prod}\left(\operatorname{Fin}\left((n) - (1)\right), \operatorname{Fin}\left(2\right)\right)) \mapsto (\operatorname{Complex.exp}\left(((\operatorname{Complex.I}) \cdot (\operatorname{Complex.ofReal}\left(k\right))) \cdot (\operatorname{Complex.ofReal}\left(\ell\left(\operatorname{Prod.fst}\left(p\right)\right)\right))\right))\right))))$$

*Formalization.* `D5/S3/Quantum/Transport/StarGraphEvolutionMapsUnitarilySimilar.propagationMatrix` (`✓ std3`).

*Citation.* Fabiano M. Andrade; Simone Severini (2018). *Unitary equivalence between the Green's function and Schrödinger approaches for quantum graphs*. DOI: [10.1103/PhysRevA.98.062107](https://doi.org/10.1103/PhysRevA.98.062107). URL: <https://arxiv.org/abs/1808.01154v2>.

*Commentary.*

Every amplitude on the edge indexed by p is multiplied by the same phase exp(I k ℓ(p.1)). The real wave number k and edge length ℓ(p.1) enter the complex exponential through Complex.ofReal. Thus the diagonal entries are the edge factors zᵢⱼ = exp(i k ℓᵢⱼ) described at TeX line 298 and in the star-graph construction at lines 383–405.

**Definition 1.3 (The universal unitary-similarity claim).**

$$\operatorname{D5.S3.Quantum.Transport.StarGraphEvolutionMapsUnitarilySimilar.claim}\left(\right) = \forall (n: \mathbb{N}), (((2: \mathbb{N}) \le n) \Rightarrow (\forall (r: (\operatorname{Fin}\left((n) - (1)\right)) \to (\mathbb{C})), (\forall (r1: \mathbb{C}), (\forall (t1: \mathbb{C}), (\forall (k: \mathbb{R}), (\forall (\ell: (\operatorname{Fin}\left((n) - (1)\right)) \to (\mathbb{R})), (\exists (w: \operatorname{Matrix}\left(\operatorname{Prod}\left(\operatorname{Fin}\left((n) - (1)\right), \operatorname{Fin}\left(2\right)\right), \operatorname{Prod}\left(\operatorname{Fin}\left((n) - (1)\right), \operatorname{Fin}\left(2\right)\right), \mathbb{C}\right)), ((w \in \operatorname{Matrix.unitaryGroup}\left(\operatorname{Prod}\left(\operatorname{Fin}\left((n) - (1)\right), \operatorname{Fin}\left(2\right)\right), \mathbb{C}\right)) \land (((w) \cdot ((\operatorname{D5.S3.Quantum.Transport.StarGraphEvolutionMapsUnitarilySimilar.scatteringMatrix}\left(r, r1, t1\right)) \cdot (\operatorname{D5.S3.Quantum.Transport.StarGraphEvolutionMapsUnitarilySimilar.propagationMatrix}\left(k, \ell\right)))) \cdot (\operatorname{star}\left(w\right)) = (\operatorname{D5.S3.Quantum.Transport.StarGraphEvolutionMapsUnitarilySimilar.propagationMatrix}\left(k, \ell\right)) \cdot (\operatorname{D5.S3.Quantum.Transport.StarGraphEvolutionMapsUnitarilySimilar.scatteringMatrix}\left(r, r1, t1\right)))))))))))$$

*Formalization.* `D5/S3/Quantum/Transport/StarGraphEvolutionMapsUnitarilySimilar.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Fabiano M. Andrade; Simone Severini (2018). *Unitary equivalence between the Green's function and Schrödinger approaches for quantum graphs*. DOI: [10.1103/PhysRevA.98.062107](https://doi.org/10.1103/PhysRevA.98.062107). URL: <https://arxiv.org/abs/1808.01154v2>.

*Commentary.*

For every star size n at least two, every complex collection of edge reflection amplitudes, every pair of complex central amplitudes, every real wave number and every real edge-length function, there is a unitary matrix w that conjugates scatteringMatrix times propagationMatrix to propagationMatrix times scatteringMatrix. This is the repository's formal reading of Claim 1, which the source states at TeX lines 522–530.

**Theorem 1.4 (The propagation matrix is the conjugating unitary).**

$$\operatorname{D5.S3.Quantum.Transport.StarGraphEvolutionMapsUnitarilySimilar.claim}\left(\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Transport/StarGraphEvolutionMapsUnitarilySimilar.result` (`✓ std3`). ∎

*Resolves.* `Problems/andrade-severini-2018-star-graph-unitary-similarity` (proved) by `D5/S3/Quantum/Transport/StarGraphEvolutionMapsUnitarilySimilar.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"andrade-severini-2018-star-graph-unitary-similarity","declaration_gid":"D5/S3/Quantum/Transport/StarGraphEvolutionMapsUnitarilySimilar.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Fabiano M. Andrade; Simone Severini (2018). *Unitary equivalence between the Green's function and Schrödinger approaches for quantum graphs*. DOI: [10.1103/PhysRevA.98.062107](https://doi.org/10.1103/PhysRevA.98.062107). URL: <https://arxiv.org/abs/1808.01154v2>.

*Commentary.*

Fix n, the amplitudes, the wave number and the edge lengths in the quantified claim. Write D for propagationMatrix k ℓ and S for scatteringMatrix r r1 t1. Each diagonal entry of D has norm one: the real exponential phase calculation gives ‖exp(I k ℓ(p.1))‖ = 1.

The diagonal-unitary criterion then proves that D belongs to the unitary group. Regard D as a unit in the matrix ring. Its inverse is its star, so multiplying the identity D D⁻¹ = 1 on the right of D S gives D (S D) star(D) = D S.

Choose w = D. The preceding unitary membership and conjugation identity supply the two witnesses required by the existential statement, which proves the claim for every n and all the quantified data.

## References

- Truth anchor: `D5/S3/Quantum/Transport/StarGraphEvolutionMapsUnitarilySimilar.claim`
- Truth anchor: `D5/S3/Quantum/Transport/StarGraphEvolutionMapsUnitarilySimilar.propagationMatrix`
- Truth anchor: `D5/S3/Quantum/Transport/StarGraphEvolutionMapsUnitarilySimilar.result`
- Truth anchor: `D5/S3/Quantum/Transport/StarGraphEvolutionMapsUnitarilySimilar.scatteringMatrix`
