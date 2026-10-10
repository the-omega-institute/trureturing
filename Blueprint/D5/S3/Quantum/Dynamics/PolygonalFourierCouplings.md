# Polygonal couplings and the discrete Fourier transform

## Abstract

The polygonal coupling model uses real symmetric circulant matrices with zero diagonal. Diagonal phase shifts act before and after the Hamiltonian evolution.

**Definition 1.1 (The Fourier matrix).**

$$\forall N \in \mathbb{N},\; \forall j \in \operatorname{Fin}\left(N\right),\; \forall k \in \operatorname{Fin}\left(N\right),\; (\operatorname{fourier}\left(N\right))_{j, k} = \frac{\operatorname{exp}\left(\frac{-(((((2) \cdot (\pi)) \cdot (i)) \cdot (j)) \cdot (k))}{N}\right)}{\operatorname{sqrt}\left(N\right)}$$

*Formalization.* `D5/S3/Quantum/Dynamics/PolygonalFourierCouplings.fourier` (`✓ std3`).

*Citation.* Edgar Barriga et al. (2026). *N-dimensional discrete Fourier transform via bosonic Hamiltonian*. URL: <https://arxiv.org/abs/2609.05644>.

*Commentary.*

The indices are the residues represented by 0 through N - 1. The Fourier matrix uses the negative exponential convention and the normalization by the square root of N.

**Definition 1.2 (Diagonal phase shifts).**

$$\forall N \in \mathbb{N},\; \forall Phi \in \operatorname{Matrix}\left(\operatorname{Fin}\left(N\right), \operatorname{Fin}\left(N\right), \mathbb{C}\right),\; \operatorname{IsUnimodularDiagonal}\left(Phi\right) \Leftrightarrow (\exists z \in (\operatorname{Fin}\left(N\right) \to \mathbb{C}),\; (\forall x \in \operatorname{Fin}\left(N\right),\; \operatorname{norm}\left(z\left(x\right)\right) = 1) \land (Phi = \operatorname{diagonal}\left(z\right)))$$

*Formalization.* `D5/S3/Quantum/Dynamics/PolygonalFourierCouplings.IsUnimodularDiagonal` (`✓ std3`).

*Citation.* Edgar Barriga et al. (2026). *N-dimensional discrete Fourier transform via bosonic Hamiltonian*. URL: <https://arxiv.org/abs/2609.05644>.

*Commentary.*

A diagonal phase matrix has an entry of modulus one at every index.

**Definition 1.3 (Polygonal coupling matrices).**

$$\forall N \in \mathbb{N},\; (\neg (N = 0)) \Rightarrow (\forall C \in \operatorname{Matrix}\left(\operatorname{Fin}\left(N\right), \operatorname{Fin}\left(N\right), \mathbb{R}\right),\; \operatorname{IsPolygonalCoupling}\left(C\right) \Leftrightarrow (\exists c \in (\operatorname{Fin}\left(N\right) \to \mathbb{R}),\; (c\left(0\right) = 0) \land ((\forall l \in \operatorname{Fin}\left(N\right),\; c\left(-(l)\right) = c\left(l\right)) \land (\forall i \in \operatorname{Fin}\left(N\right),\; \forall j \in \operatorname{Fin}\left(N\right),\; (C)_{i, j} = c\left((j) - (i)\right)))))$$

*Formalization.* `D5/S3/Quantum/Dynamics/PolygonalFourierCouplings.IsPolygonalCoupling` (`✓ std3`).

*Citation.* Edgar Barriga et al. (2026). *N-dimensional discrete Fourier transform via bosonic Hamiltonian*. URL: <https://arxiv.org/abs/2609.05644>.

*Commentary.*

The coupling between i and j depends on j - i modulo N. Reversing this residue preserves the coupling, and the zero residue has zero coupling.

**Definition 1.4 (The polygonal Fourier question).**

$$claim \Leftrightarrow (\forall N \in \mathbb{N},\; (\neg (N = 0)) \Rightarrow (\exists C \in \operatorname{Matrix}\left(\operatorname{Fin}\left(N\right), \operatorname{Fin}\left(N\right), \mathbb{R}\right),\; (\operatorname{IsPolygonalCoupling}\left(C\right)) \land ((\forall i \in \operatorname{Fin}\left(N\right),\; \forall j \in \operatorname{Fin}\left(N\right),\; (\neg (i = j)) \Rightarrow (0 < (C)_{i, j})) \land (\exists Phiout \in \operatorname{Matrix}\left(\operatorname{Fin}\left(N\right), \operatorname{Fin}\left(N\right), \mathbb{C}\right),\; \exists Phiin \in \operatorname{Matrix}\left(\operatorname{Fin}\left(N\right), \operatorname{Fin}\left(N\right), \mathbb{C}\right),\; (\operatorname{IsUnimodularDiagonal}\left(Phiout\right)) \land ((\operatorname{IsUnimodularDiagonal}\left(Phiin\right)) \land (((Phiout) \cdot (\operatorname{hamiltonianPropagator}\left(\operatorname{map}\left(C, \operatorname{ofReal}\right), 1\right))) \cdot (Phiin) = \operatorname{fourier}\left(N\right)))))))$$

*Formalization.* `D5/S3/Quantum/Dynamics/PolygonalFourierCouplings.claim` (`✓ std3`).

*Citation.* Edgar Barriga et al. (2026). *N-dimensional discrete Fourier transform via bosonic Hamiltonian*. URL: <https://arxiv.org/abs/2609.05644>.

*Commentary.*

For every positive dimension, the question asks for strictly positive off-diagonal couplings and two diagonal phase matrices whose product with the propagator at time one equals the Fourier matrix exactly.

**Theorem 1.5 (Positive couplings in every dimension).**

$$\forall N \in \mathbb{N},\; (\neg (N = 0)) \Rightarrow (\exists C \in \operatorname{Matrix}\left(\operatorname{Fin}\left(N\right), \operatorname{Fin}\left(N\right), \mathbb{R}\right),\; (\operatorname{IsPolygonalCoupling}\left(C\right)) \land ((\forall i \in \operatorname{Fin}\left(N\right),\; \forall j \in \operatorname{Fin}\left(N\right),\; (\neg (i = j)) \Rightarrow (0 < (C)_{i, j})) \land (\exists Phiout \in \operatorname{Matrix}\left(\operatorname{Fin}\left(N\right), \operatorname{Fin}\left(N\right), \mathbb{C}\right),\; \exists Phiin \in \operatorname{Matrix}\left(\operatorname{Fin}\left(N\right), \operatorname{Fin}\left(N\right), \mathbb{C}\right),\; (\operatorname{IsUnimodularDiagonal}\left(Phiout\right)) \land ((\operatorname{IsUnimodularDiagonal}\left(Phiin\right)) \land (((Phiout) \cdot (\operatorname{hamiltonianPropagator}\left(\operatorname{map}\left(C, \operatorname{ofReal}\right), 1\right))) \cdot (Phiin) = \operatorname{fourier}\left(N\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/PolygonalFourierCouplings.result` (`✓ std3`). ∎

*Resolves.* `Problems/barriga-2026-polygonal-fourier-couplings` (proved) by `D5/S3/Quantum/Dynamics/PolygonalFourierCouplings.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"barriga-2026-polygonal-fourier-couplings","declaration_gid":"D5/S3/Quantum/Dynamics/PolygonalFourierCouplings.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Edgar Barriga et al. (2026). *N-dimensional discrete Fourier transform via bosonic Hamiltonian*. URL: <https://arxiv.org/abs/2609.05644>.

*Commentary.*

A periodic quadratic phase on the residues factors a symmetric circulant unitary as a diagonal phase, the Fourier matrix, and the same diagonal phase. Character orthogonality makes the normalized Fourier matrix unitary. Fourier conjugation diagonalizes the circulant: its eigenvalue vector is the discrete Fourier transform of its first column. The negatives of its eigenvalue arguments are real spectral angles of absolute value at most pi, and they agree at opposite residues. Their inverse Fourier kernel is therefore real and symmetric. Subtracting the mean of the angles removes the diagonal. Adding 2 pi times the quantity N minus one on the constant Fourier mode and subtracting 2 pi on every other mode preserves the exponential and raises every off-diagonal coupling by 2 pi. The original kernel has modulus at most pi, so every resulting off-diagonal coupling is strictly positive. The common phase from subtracting the mean is absorbed into the input diagonal phase.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/PolygonalFourierCouplings.IsPolygonalCoupling`
- Truth anchor: `D5/S3/Quantum/Dynamics/PolygonalFourierCouplings.IsUnimodularDiagonal`
- Truth anchor: `D5/S3/Quantum/Dynamics/PolygonalFourierCouplings.claim`
- Truth anchor: `D5/S3/Quantum/Dynamics/PolygonalFourierCouplings.fourier`
- Truth anchor: `D5/S3/Quantum/Dynamics/PolygonalFourierCouplings.result`
- Dependency: [D5/S3/Quantum/Dynamics/ProjectionProbabilityFlow](ProjectionProbabilityFlow.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/TomiyamaDiagonalKPositivity](../QuantumChannels/TomiyamaDiagonalKPositivity.md)
