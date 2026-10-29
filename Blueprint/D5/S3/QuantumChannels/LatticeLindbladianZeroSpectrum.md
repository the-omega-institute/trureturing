# Spectral zero for a lattice Lindblad generator

## Abstract

Finite-range translation-invariant lattice Lindblad matrices define a bounded operator with spectral zero.

**Definition 1.1 (Finite matrix range).**

$$\forall \left(r: \mathbb{N}\right), \left(\forall \left(h: \mathbb{Z} \to \left(\mathbb{Z} \to \mathbb{C}\right)\right), \left(\forall \left(\ell: \mathbb{Z} \to \left(\mathbb{Z} \to \left(\mathbb{Z} \to \mathbb{C}\right)\right)\right), \left(\operatorname{D5.S3.QuantumChannels.LatticeLindbladianZeroSpectrum.IsFiniteRange}\left(r, h, \ell\right) = \left(\left(\forall \left(x: \mathbb{Z}\right), \left(\forall \left(y: \mathbb{Z}\right), \left(\left(\left(\operatorname{Nat.cast}\left(r\right): \mathbb{Z}\right) < \left|x - y\right|\right) \Rightarrow \left(h\left(x, y\right) = \left(0: \mathbb{C}\right)\right)\right)\right)\right) \land \left(\forall \left(k: \mathbb{Z}\right), \left(\forall \left(x: \mathbb{Z}\right), \left(\forall \left(y: \mathbb{Z}\right), \left(\left(\left(\operatorname{Nat.cast}\left(r\right): \mathbb{Z}\right) < \operatorname{Max.max}\left(\left|x - k\right|, \left|y - k\right|\right)\right) \Rightarrow \left(\ell\left(k, x, y\right) = \left(0: \mathbb{C}\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/QuantumChannels/LatticeLindbladianZeroSpectrum.IsFiniteRange` (`✓ std3`).

*Citation.* Frederik Ravn Klausen (2025). *Spectra of generators of Markovian evolution in the thermodynamic limit: From non-Hermitian to full evolution via tridiagonal Laurent matrices*. DOI: [10.48550/arXiv.2206.09879](https://doi.org/10.48550/arXiv.2206.09879). URL: <https://arxiv.org/abs/2206.09879v3>.

*Commentary.*

The Hamiltonian matrix h vanishes beyond distance r from its diagonal. The jump matrix indexed by k vanishes unless both its row and column lie within distance r of k. The radius is a natural number, included in the integers before comparison with distances. These are the matrix support conditions associated with (Finite Range) in section02.tex, line 41. The Hamiltonian condition is expressed using the distance between its own two indices; it has no jump index k. No symmetry or rank condition is part of this predicate.

**Definition 1.2 (Translation of matrix indices).**

$$\forall \left(h: \mathbb{Z} \to \left(\mathbb{Z} \to \mathbb{C}\right)\right), \left(\forall \left(\ell: \mathbb{Z} \to \left(\mathbb{Z} \to \left(\mathbb{Z} \to \mathbb{C}\right)\right)\right), \left(\operatorname{D5.S3.QuantumChannels.LatticeLindbladianZeroSpectrum.IsTranslationInvariant}\left(h, \ell\right) = \left(\left(\forall \left(x: \mathbb{Z}\right), \left(\forall \left(y: \mathbb{Z}\right), \left(h\left(x + 1, y + 1\right) = h\left(x, y\right)\right)\right)\right) \land \left(\forall \left(k: \mathbb{Z}\right), \left(\forall \left(x: \mathbb{Z}\right), \left(\forall \left(y: \mathbb{Z}\right), \left(\ell\left(k + 1, x + 1, y + 1\right) = \ell\left(k, x, y\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/QuantumChannels/LatticeLindbladianZeroSpectrum.IsTranslationInvariant` (`✓ std3`).

*Citation.* Frederik Ravn Klausen (2025). *Spectra of generators of Markovian evolution in the thermodynamic limit: From non-Hermitian to full evolution via tridiagonal Laurent matrices*. DOI: [10.48550/arXiv.2206.09879](https://doi.org/10.48550/arXiv.2206.09879). URL: <https://arxiv.org/abs/2206.09879v3>.

*Commentary.*

Translating both indices of h by one leaves its entries unchanged. Translating the jump index and both matrix indices by one likewise leaves the jump entries unchanged. This is the matrix form of (TransInv) in section02.tex, line 42; iteration gives the corresponding identities for every integer translation.

**Definition 1.3 (The generator in matrix elements).**

$$\forall \left(g: \mathbb{R}\right), \left(\forall \left(h: \mathbb{Z} \to \left(\mathbb{Z} \to \mathbb{C}\right)\right), \left(\forall \left(\ell: \mathbb{Z} \to \left(\mathbb{Z} \to \left(\mathbb{Z} \to \mathbb{C}\right)\right)\right), \left(\forall \left(\rho: \left(\mathbb{Z} \times \mathbb{Z}\right) \to \mathbb{C}\right), \left(\forall \left(x: \mathbb{Z}\right), \left(\forall \left(y: \mathbb{Z}\right), \left(\left(\operatorname{D5.S3.QuantumChannels.LatticeLindbladianZeroSpectrum.lindbladEntry}\left(g, h, \ell, \rho, x, y\right): \mathbb{C}\right) = \left(-\operatorname{Complex.I}\right) \cdot \left(\sum'_{z: \mathbb{Z}} \left(\left(h\left(x, z\right)\right) \cdot \left(\rho\left(\left(z, y\right)\right)\right)\right) - \sum'_{z: \mathbb{Z}} \left(\left(\rho\left(\left(x, z\right)\right)\right) \cdot \left(h\left(z, y\right)\right)\right)\right) + \left(\operatorname{Complex.ofReal}\left(g\right)\right) \cdot \left(\sum'_{k: \mathbb{Z}} \left(\sum'_{u: \mathbb{Z}} \left(\sum'_{v: \mathbb{Z}} \left(\left(\left(\ell\left(k, x, u\right)\right) \cdot \left(\rho\left(\left(u, v\right)\right)\right)\right) \cdot \left(\operatorname{Star.star}\left(\ell\left(k, y, v\right)\right)\right)\right)\right) - \left(\frac{\left(1: \mathbb{C}\right)}{\left(2: \mathbb{C}\right)}\right) \cdot \left(\sum'_{z: \mathbb{Z}} \left(\left(\sum'_{w: \mathbb{Z}} \left(\left(\operatorname{Star.star}\left(\ell\left(k, w, x\right)\right)\right) \cdot \left(\ell\left(k, w, z\right)\right)\right)\right) \cdot \left(\rho\left(\left(z, y\right)\right)\right)\right)\right) - \left(\frac{\left(1: \mathbb{C}\right)}{\left(2: \mathbb{C}\right)}\right) \cdot \left(\sum'_{z: \mathbb{Z}} \left(\left(\rho\left(\left(x, z\right)\right)\right) \cdot \left(\sum'_{w: \mathbb{Z}} \left(\left(\operatorname{Star.star}\left(\ell\left(k, w, z\right)\right)\right) \cdot \left(\ell\left(k, w, y\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/QuantumChannels/LatticeLindbladianZeroSpectrum.lindbladEntry` (`✓ std3`).

*Citation.* Frederik Ravn Klausen (2025). *Spectra of generators of Markovian evolution in the thermodynamic limit: From non-Hermitian to full evolution via tridiagonal Laurent matrices*. DOI: [10.48550/arXiv.2206.09879](https://doi.org/10.48550/arXiv.2206.09879). URL: <https://arxiv.org/abs/2206.09879v3>.

*Commentary.*

For an arbitrary complex kernel ρ, this expression is the (x,y) entry of the commutator term and the jump gain minus the two half anticommutator terms. The operation star on a complex entry is complex conjugation. Every sum is an unconditional sum over the integers; finite range makes the relevant sums finite. The real parameter g is included in the complex numbers and multiplies the entire dissipative term. The Lindblad expression appears in section02.tex, lines 6–13; the effective Hamiltonian there at line 22 and its use in section03.tex, lines 179–182, specify the placement of the coupling constant. The definition allows every real g and does not impose positivity or self-adjointness.

**Theorem 1.4 (A bounded generator with zero in its spectrum).**

$$\forall \left(r: \mathbb{N}\right), \left(\forall \left(g: \mathbb{R}\right), \left(\forall \left(h: \mathbb{Z} \to \left(\mathbb{Z} \to \mathbb{C}\right)\right), \left(\forall \left(\ell: \mathbb{Z} \to \left(\mathbb{Z} \to \left(\mathbb{Z} \to \mathbb{C}\right)\right)\right), \left(\left(\operatorname{D5.S3.QuantumChannels.LatticeLindbladianZeroSpectrum.IsFiniteRange}\left(r, h, \ell\right)\right) \Rightarrow \left(\left(\operatorname{D5.S3.QuantumChannels.LatticeLindbladianZeroSpectrum.IsTranslationInvariant}\left(h, \ell\right)\right) \Rightarrow \left(\exists \left(t: \operatorname{CoeSort.coe}\left(\operatorname{D5.S3.Observer.Approximation.ReadoutUpdateCommutatorFactorization.ObserverHilbertSpace}\left(\left(\mathbb{Z} \times \mathbb{Z}\right)\right)\right) \to_{L}[\mathbb{C}] \operatorname{CoeSort.coe}\left(\operatorname{D5.S3.Observer.Approximation.ReadoutUpdateCommutatorFactorization.ObserverHilbertSpace}\left(\left(\mathbb{Z} \times \mathbb{Z}\right)\right)\right)\right), \left(\left(\forall \left(\rho: \operatorname{CoeSort.coe}\left(\operatorname{D5.S3.Observer.Approximation.ReadoutUpdateCommutatorFactorization.ObserverHilbertSpace}\left(\left(\mathbb{Z} \times \mathbb{Z}\right)\right)\right)\right), \left(\forall \left(x: \mathbb{Z}\right), \left(\forall \left(y: \mathbb{Z}\right), \left(\operatorname{Subtype.val}\left(\operatorname{DFunLike.coe}\left(t\right)\left(\rho\right)\right)\left(\left(x, y\right)\right) = \operatorname{D5.S3.QuantumChannels.LatticeLindbladianZeroSpectrum.lindbladEntry}\left(g, h, \ell, \operatorname{Subtype.val}\left(\rho\right), x, y\right)\right)\right)\right)\right) \land \left(\left(0: \mathbb{C}\right) \in \operatorname{spectrum}\left(\mathbb{C}, t\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/LatticeLindbladianZeroSpectrum.result` (`✓ std3`). ∎

*Resolves.* `Problems/klausen-2025-lattice-lindbladian-zero-spectrum` (proved) by `D5/S3/QuantumChannels/LatticeLindbladianZeroSpectrum.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"klausen-2025-lattice-lindbladian-zero-spectrum","declaration_gid":"D5/S3/QuantumChannels/LatticeLindbladianZeroSpectrum.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Frederik Ravn Klausen (2025). *Spectra of generators of Markovian evolution in the thermodynamic limit: From non-Hermitian to full evolution via tridiagonal Laurent matrices*. DOI: [10.48550/arXiv.2206.09879](https://doi.org/10.48550/arXiv.2206.09879). URL: <https://arxiv.org/abs/2206.09879v3>.

*Commentary.*

The space ObserverHilbertSpace on the integer pairs is the complex square-summable kernel space. The vectorization in section03.tex, lines 162–165, identifies this space with the Hilbert–Schmidt operators on the square-summable sequences on the integers. The spectrum here is the complex spectrum in the unital algebra of continuous complex linear endomorphisms. The question in section04.tex, line 574, asks for spectral zero under finite range, translation invariance and rank one. The statement holds for every real g, without a rank or self-adjointness assumption.

First, translation invariance writes h(x,y) as h(0,y−x) and ℓ(k,x,y) as ℓ(0,x−k,y−k). Only finitely many differences survive the support conditions, so all matrix entries have a common norm bound. Replacing the unconditional sums by sums on the corresponding finite integer intervals makes each output entry a linear function of ρ. It depends only on ρ(u,v) with |u−x| and |v−y| at most 2r. Expanding this finite rectangle in its matrix units gives a finite sum over displacements w in [−2r,2r]²: each summand multiplies the translated value ρ(p+w) by the generator's entry on the matrix unit at p+w, evaluated at p. The entrywise bounds give a common nonnegative real bound m for these multiplying functions. Each translated multiplication operator is bounded: translation is an isometry and multiplication has norm at most m. Their finite sum is therefore a continuous complex linear operator t with exactly the required entries.

Next let Pₙ be the kernel equal to one on (x,x) for −n ≤ x ≤ n and zero elsewhere. Its inner product with ρ is the sum of the diagonal entries of ρ on that interval, and its squared norm is 2n+1. For a matrix unit at q=(u,v), locality confines the output to |u−x| ≤ 2r and |v−y| ≤ 2r. The full sum of its diagonal output entries is zero. Indeed, the two commutator contributions cancel; for each jump index, the gain sum equals the sum of the conjugate product, while each loss contributes half of that same sum. All exchanges of sums are finite, with diagonal indices in [min(u,v)−2r,max(u,v)+2r] and jump indices in [u−r,u+r] union [v−r,v+r].

For a fixed n, denote by κ(q) the sum of the diagonal output of the matrix unit at q over [−n,n]. At most 4r+1 diagonal entries contribute, so |κ(q)| ≤ (4r+1)m. Moreover κ(q) vanishes unless u lies in [n−2r,n+2r] union [−n−2r,−n+2r] and |v−u| ≤ 4r. If the two input indices are farther apart, locality gives zero; if u is outside the enlarged interval, there is no contribution; if u is strictly inside away from its ends, the restricted diagonal sum is the full zero sum. The remaining pairs number at most c=2(4r+1)(8r+1), independently of n. Expand an arbitrary ρ on the finite square [−n−2r,n+2r]² and exchange the finite sums. Only these boundary pairs remain. Since each |ρ(q)| is at most its square-summable norm, the triangle inequality gives |⟨Pₙ,tρ⟩| ≤ k‖ρ‖ with k=c(4r+1)m, uniformly in n.

Finally suppose t is a unit, and let s be its bounded inverse. Choose a natural n greater than (k‖s‖)² and apply the preceding estimate to ρ=sPₙ. Since t(sPₙ)=Pₙ, it gives ‖Pₙ‖² ≤ k‖sPₙ‖ ≤ k‖s‖‖Pₙ‖. The norm of Pₙ is positive, so ‖Pₙ‖ ≤ k‖s‖. Squaring contradicts ‖Pₙ‖²=2n+1 and the choice of n. Thus t is not a unit. The equivalence between noninvertibility and membership of zero in the spectrum proves the conclusion.

## References

- Truth anchor: `D5/S3/QuantumChannels/LatticeLindbladianZeroSpectrum.IsFiniteRange`
- Truth anchor: `D5/S3/QuantumChannels/LatticeLindbladianZeroSpectrum.IsTranslationInvariant`
- Truth anchor: `D5/S3/QuantumChannels/LatticeLindbladianZeroSpectrum.lindbladEntry`
- Truth anchor: `D5/S3/QuantumChannels/LatticeLindbladianZeroSpectrum.result`
- Dependency: [D5/S3/Observer/Approximation/ReadoutUpdateCommutatorFactorization](../Observer/Approximation/ReadoutUpdateCommutatorFactorization.md)
