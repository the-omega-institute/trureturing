# Directed support obstructions for nSSP

## Abstract

Real centralizers and directed cycle spaces constrain exact nSSP supports.

**Definition 1.1 (The non-symmetric strong spectral property).**

$$\forall n \in \operatorname{Nat},\; \forall A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \operatorname{Real}\right),\; \operatorname{HasNSSP}\left(A\right) \Leftrightarrow \left(\forall X \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \operatorname{Real}\right),\; \left(\forall i \in \operatorname{Fin}\left(n\right),\; \forall j \in \operatorname{Fin}\left(n\right),\; A\left(i, j\right) \cdot X\left(i, j\right) = 0\right) \Rightarrow \left(A \cdot \operatorname{transpose}\left(X\right) - \operatorname{transpose}\left(X\right) \cdot A = 0 \Rightarrow X = 0\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/KoljancicOblakMinimumArcs.HasNSSP` (`✓ std3`).

*Citation.* Sara Koljančić; Polona Oblak (2026). *Combinatorial aspects of the nonsymmetric strong spectral property for graphs*. DOI: [10.13001/ela.2026.10523](https://doi.org/10.13001/ela.2026.10523). URL: <https://arxiv.org/abs/2604.21552v1>.

*Commentary.*

Every real obstruction matrix X is tested. Hadamard annihilation uses the same ordered entries, and the commutator uses X transposed. There is no extra identity-Hadamard or trace condition.

**Definition 1.2 (Exact directed support).**

$$\forall n \in \operatorname{Nat},\; \forall E \in \operatorname{Finset}\left(\operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(n\right)\right),\; \forall A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \operatorname{Real}\right),\; \operatorname{ExactSupport}\left(E, A\right) \Leftrightarrow \left(\forall i \in \operatorname{Fin}\left(n\right),\; \forall j \in \operatorname{Fin}\left(n\right),\; A\left(i, j\right) \ne 0 \Leftrightarrow (i, j) \in E\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/KoljancicOblakMinimumArcs.ExactSupport` (`✓ std3`).

*Citation.* Sara Koljančić; Polona Oblak (2026). *Combinatorial aspects of the nonsymmetric strong spectral property for graphs*. DOI: [10.13001/ela.2026.10523](https://doi.org/10.13001/ela.2026.10523). URL: <https://arxiv.org/abs/2604.21552v1>.

*Commentary.*

The support is a finite set of ordered pairs on Fin n. Nonzero entries are equivalent to membership, so all prescribed arc weights are nonzero and all other entries vanish. Loops are counted once.

**Definition 1.3 (A support requiring nSSP).**

$$\forall n \in \operatorname{Nat},\; \forall E \in \operatorname{Finset}\left(\operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(n\right)\right),\; \operatorname{Requires}\left(E\right) \Leftrightarrow \left(\forall A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \operatorname{Real}\right),\; \operatorname{ExactSupport}\left(E, A\right) \Rightarrow \operatorname{HasNSSP}\left(A\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/KoljancicOblakMinimumArcs.Requires` (`✓ std3`).

*Citation.* Sara Koljančić; Polona Oblak (2026). *Combinatorial aspects of the nonsymmetric strong spectral property for graphs*. DOI: [10.13001/ela.2026.10523](https://doi.org/10.13001/ela.2026.10523). URL: <https://arxiv.org/abs/2604.21552v1>.

*Commentary.*

The quantifier ranges over every real matrix with precisely this support, including all assignments of nonzero weights of either sign.

**Definition 1.4 (The minimum-arcs assertion).**

$$\operatorname{MinimumArcs}\left(\right) \Leftrightarrow \left(\forall n \in \operatorname{Nat},\; 1 \le n \Rightarrow \left(\left(\forall E \in \operatorname{Finset}\left(\operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(n\right)\right),\; \operatorname{Requires}\left(E\right) \Rightarrow 2 \cdot n - 1 \le \operatorname{card}\left(E\right)\right) \land \left(\exists E \in \operatorname{Finset}\left(\operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(n\right)\right),\; \operatorname{Requires}\left(E\right) \land \operatorname{card}\left(E\right) = 2 \cdot n - 1\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/KoljancicOblakMinimumArcs.MinimumArcs` (`✓ std3`).

*Citation.* Sara Koljančić; Polona Oblak (2026). *Combinatorial aspects of the nonsymmetric strong spectral property for graphs*. DOI: [10.13001/ela.2026.10523](https://doi.org/10.13001/ela.2026.10523). URL: <https://arxiv.org/abs/2604.21552v1>.

*Commentary.*

For each positive order, the assertion contains both the lower bound for every requiring support and existence of a requiring support attaining equality. The two clauses use the same order n.

**Definition 1.5 (The real signed incidence matrix).**

$$\forall n \in \operatorname{Nat},\; \forall E \in \operatorname{Finset}\left(\operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(n\right)\right),\; \forall i \in \operatorname{Fin}\left(n\right),\; \forall u \in E,\; \operatorname{incidence}\left(E\right)\left(i, u\right) = (\operatorname{if} (i = \operatorname{snd}\left(u\right)) \operatorname{then} 1 \operatorname{else} 0) - (\operatorname{if} (i = \operatorname{fst}\left(u\right)) \operatorname{then} 1 \operatorname{else} 0)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/KoljancicOblakMinimumArcs.incidence` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sara Koljančić; Polona Oblak (2026). *Combinatorial aspects of the nonsymmetric strong spectral property for graphs*. DOI: [10.13001/ela.2026.10523](https://doi.org/10.13001/ela.2026.10523). URL: <https://arxiv.org/abs/2604.21552v1>.

*Commentary.*

Each arc column is the target coordinate vector minus the source coordinate vector. This is the real cast of the integer signed incidence matrix. A loop column is zero; opposite arcs are separate columns.

**Definition 1.6 (Constancy along every arc).**

$$\forall n \in \operatorname{Nat},\; \forall E \in \operatorname{Finset}\left(\operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(n\right)\right),\; \operatorname{ConnectedSupport}\left(E\right) \Leftrightarrow \left(\forall p \in \operatorname{Fin}\left(n\right) \to \operatorname{Real},\; \left(\forall u \in E,\; p\left(\operatorname{fst}\left(u\right)\right) = p\left(\operatorname{snd}\left(u\right)\right)\right) \Rightarrow \left(\forall i \in \operatorname{Fin}\left(n\right),\; \forall j \in \operatorname{Fin}\left(n\right),\; p\left(i\right) = p\left(j\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/KoljancicOblakMinimumArcs.ConnectedSupport` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sara Koljančić; Polona Oblak (2026). *Combinatorial aspects of the nonsymmetric strong spectral property for graphs*. DOI: [10.13001/ela.2026.10523](https://doi.org/10.13001/ela.2026.10523). URL: <https://arxiv.org/abs/2604.21552v1>.

*Commentary.*

A real function equal at the endpoints of every directed arc must be constant on all vertices. This is the algebraic connectivity condition used in the incidence-rank estimate.

**Theorem 1.7 (The centralizer injects into the cycle space).**

$$\forall n \in \operatorname{Nat},\; \forall E \in \operatorname{Finset}\left(\operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(n\right)\right),\; \forall A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \operatorname{Real}\right),\; \operatorname{ExactSupport}\left(E, A\right) \Rightarrow \left(\operatorname{HasNSSP}\left(A\right) \Rightarrow n + \operatorname{rank}\left(\operatorname{incidence}\left(E\right)\right) \le \operatorname{card}\left(E\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/KoljancicOblakMinimumArcs.nssp_centralizer_cycle_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sara Koljančić; Polona Oblak (2026). *Combinatorial aspects of the nonsymmetric strong spectral property for graphs*. DOI: [10.13001/ela.2026.10523](https://doi.org/10.13001/ela.2026.10523). URL: <https://arxiv.org/abs/2604.21552v1>.

*Commentary.*

View A as a linear operator over the reals and use its polynomial module. The classical PID structure theorem gives a finite product of cyclic quotient rings. Conjugated coordinatewise multiplication is injective and commutes with A, giving centralizer dimension at least n. The map F ↦ (A_ij F_ji) over the actual arc set lies in the signed incidence kernel because its boundary is the diagonal of FA−AF. If this map vanishes, nSSP applied to F transposed gives F=0. Rank-nullity therefore bounds n plus the incidence rank by the number of arcs. No positivity, diagonalizability or irreducibility is used.

**Theorem 1.8 (The connected-support lower bound).**

$$\forall n \in \operatorname{Nat},\; 1 \le n \Rightarrow \left(\forall E \in \operatorname{Finset}\left(\operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(n\right)\right),\; \operatorname{ConnectedSupport}\left(E\right) \Rightarrow \left(\forall A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \operatorname{Real}\right),\; \operatorname{ExactSupport}\left(E, A\right) \Rightarrow \left(\operatorname{HasNSSP}\left(A\right) \Rightarrow 2 \cdot n - 1 \le \operatorname{card}\left(E\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/KoljancicOblakMinimumArcs.nssp_arc_bound_of_connected` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sara Koljančić; Polona Oblak (2026). *Combinatorial aspects of the nonsymmetric strong spectral property for graphs*. DOI: [10.13001/ela.2026.10523](https://doi.org/10.13001/ela.2026.10523). URL: <https://arxiv.org/abs/2604.21552v1>.

*Commentary.*

The kernel of the transposed incidence matrix consists of functions constant along every arc. Under ConnectedSupport, evaluation at any one vertex is injective on that kernel, so its dimension is at most one. Transpose invariance of rank and rank-nullity give incidence rank at least n−1. Combining this with the centralizer-cycle bound gives 2n−1 arcs. Connectivity is an explicit hypothesis of this theorem.

**Definition 1.9 (The endpoint-looped double path).**

$$\forall n \in \operatorname{Nat},\; \forall i \in \operatorname{Fin}\left(n\right),\; \forall j \in \operatorname{Fin}\left(n\right),\; (i, j) \in \operatorname{endpointSupport}\left(n\right) \Leftrightarrow \left(\left(\operatorname{val}\left(i\right) = 0 \land \operatorname{val}\left(j\right) = 0\right) \lor \left(\operatorname{val}\left(i\right) + 1 = \operatorname{val}\left(j\right) \lor \operatorname{val}\left(j\right) + 1 = \operatorname{val}\left(i\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/KoljancicOblakMinimumArcs.endpointSupport` (`✓ std3`).

*Citation.* Sara Koljančić; Polona Oblak (2026). *Combinatorial aspects of the nonsymmetric strong spectral property for graphs*. DOI: [10.13001/ela.2026.10523](https://doi.org/10.13001/ela.2026.10523). URL: <https://arxiv.org/abs/2604.21552v1>.

*Commentary.*

At positive order there is one loop at vertex zero and two opposite arcs between consecutive vertices. All other ordered pairs are absent.

**Theorem 1.10 (Universal real attainment construction).**

$$\forall n \in \operatorname{Nat},\; 1 \le n \Rightarrow \operatorname{Requires}\left(\operatorname{endpointSupport}\left(n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/KoljancicOblakMinimumArcs.endpoint_requires` (`✓ std3`). ∎

*Citation.* Sara Koljančić; Polona Oblak (2026). *Combinatorial aspects of the nonsymmetric strong spectral property for graphs*. DOI: [10.13001/ela.2026.10523](https://doi.org/10.13001/ela.2026.10523). URL: <https://arxiv.org/abs/2604.21552v1>.

*Commentary.*

Let F be the transpose of an obstruction. Its entries at the loop and both neighbouring diagonals vanish. Commutation along each odd offset, read from the terminal end of the path, forces that entire offset to vanish. Apply the same argument to the transposed matrices for the lower odd offsets. The endpoint loop then forces the remaining entries in the first column to vanish. Commutation propagates the zero column successively along every nonzero path arc. Thus F, and hence the obstruction, is zero. This is the construction of Theorem 5.5 of Koljančić and Oblak, formalized for arbitrary nonzero real weights.

**Theorem 1.11 (Exactly 2n−1 arcs).**

$$\forall n \in \operatorname{Nat},\; 1 \le n \Rightarrow \left(\exists E \in \operatorname{Finset}\left(\operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(n\right)\right),\; \operatorname{Requires}\left(E\right) \land \operatorname{card}\left(E\right) = 2 \cdot n - 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/KoljancicOblakMinimumArcs.endpoint_attainment` (`✓ std3`). ∎

*Citation.* Sara Koljančić; Polona Oblak (2026). *Combinatorial aspects of the nonsymmetric strong spectral property for graphs*. DOI: [10.13001/ela.2026.10523](https://doi.org/10.13001/ela.2026.10523). URL: <https://arxiv.org/abs/2604.21552v1>.

*Commentary.*

The support is in bijection with one loop together with two copies of Fin(n−1). Its cardinality is 1+2(n−1)=2n−1 at every positive order. Combining this count with the universal real path argument gives the upper clause of the minimum-arcs assertion.

**Theorem 1.12 (A loop in every constant level).**

$$\forall n \in \operatorname{Nat},\; \forall E \in \operatorname{Finset}\left(\operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(n\right)\right),\; \operatorname{Requires}\left(E\right) \Rightarrow \left(\forall p \in \operatorname{Fin}\left(n\right) \to \operatorname{Real},\; \left(\forall u \in E,\; p\left(\operatorname{fst}\left(u\right)\right) = p\left(\operatorname{snd}\left(u\right)\right)\right) \Rightarrow \left(\forall r \in \operatorname{Fin}\left(n\right),\; \exists i \in \operatorname{Fin}\left(n\right),\; p\left(i\right) = p\left(r\right) \land (i, i) \in E\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/KoljancicOblakMinimumArcs.requires_level_has_loop` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sara Koljančić; Polona Oblak (2026). *Combinatorial aspects of the nonsymmetric strong spectral property for graphs*. DOI: [10.13001/ela.2026.10523](https://doi.org/10.13001/ela.2026.10523). URL: <https://arxiv.org/abs/2604.21552v1>.

*Commentary.*

Take the diagonal indicator of any nonempty level of a function constant along every arc. It commutes with a matrix of that exact support because no arc crosses the level. If that level contained no loop, its diagonal indicator would also satisfy Hadamard annihilation, contradicting nSSP. In particular a component without a loop cannot occur in a requiring support.

**Theorem 1.13 (A loop permits a real eigenvalue).**

$$\forall n \in \operatorname{Nat},\; \forall E \in \operatorname{Finset}\left(\operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(n\right)\right),\; \forall r \in \operatorname{Fin}\left(n\right),\; (r, r) \in E \Rightarrow \left(\exists A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \operatorname{Real}\right),\; \operatorname{ExactSupport}\left(E, A\right) \land \operatorname{det}\left(1 - A\right) = 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/KoljancicOblakMinimumArcs.loop_support_eigenvalue_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sara Koljančić; Polona Oblak (2026). *Combinatorial aspects of the nonsymmetric strong spectral property for graphs*. DOI: [10.13001/ela.2026.10523](https://doi.org/10.13001/ela.2026.10523). URL: <https://arxiv.org/abs/2604.21552v1>.

*Commentary.*

Give all prescribed entries other than a selected loop the same small nonzero real weight t. Write N(t)=I−tB, with the selected loop removed from B. Both det N(t) and the determinant obtained by replacing its selected row by the corresponding unit row equal one at t=0. Continuity makes both nonzero for some nonzero t. Choose the loop weight as their ratio. Multilinearity in that row then gives det(I−A)=0, while every prescribed entry remains nonzero. This supplies a real eigenvalue-one realization without any sign or genericity condition in the requiring property.

**Theorem 1.14 (A requiring support is connected).**

$$\forall n \in \operatorname{Nat},\; \forall E \in \operatorname{Finset}\left(\operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(n\right)\right),\; \operatorname{Requires}\left(E\right) \Rightarrow \operatorname{ConnectedSupport}\left(E\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/KoljancicOblakMinimumArcs.requires_connected` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sara Koljančić; Polona Oblak (2026). *Combinatorial aspects of the nonsymmetric strong spectral property for graphs*. DOI: [10.13001/ela.2026.10523](https://doi.org/10.13001/ela.2026.10523). URL: <https://arxiv.org/abs/2604.21552v1>.

*Commentary.*

Suppose a function is constant along every arc but has two different vertex values. Its corresponding level and its complement have no arcs between them. The diagonal obstruction gives a loop in each part. Realize eigenvalue one on each restricted support, and choose a nonzero right eigenvector on the first part and a nonzero left eigenvector on the second. Their outer product is a nonzero matrix in an off-diagonal block that commutes with the block diagonal support matrix. Its transpose is Hadamard-annihilated by that support matrix. This contradicts the requirement that every exact-support matrix have nSSP, so the vertex function must be constant.

**Theorem 1.15 (The all-positive-order minimum).**

$$\forall n \in \operatorname{Nat},\; 1 \le n \Rightarrow \left(\left(\forall E \in \operatorname{Finset}\left(\operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(n\right)\right),\; \operatorname{Requires}\left(E\right) \Rightarrow 2 \cdot n - 1 \le \operatorname{card}\left(E\right)\right) \land \left(\exists E \in \operatorname{Finset}\left(\operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(n\right)\right),\; \operatorname{Requires}\left(E\right) \land \operatorname{card}\left(E\right) = 2 \cdot n - 1\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/KoljancicOblakMinimumArcs.result` (`✓ std3`). ∎

*Resolves.* `Problems/koljancic-oblak-2026-nssp-minimum-arcs-problem-1-8` (proved) by `D5/S3/Combinatorics/SpectralGraph/KoljancicOblakMinimumArcs.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"koljancic-oblak-2026-nssp-minimum-arcs-problem-1-8","declaration_gid":"D5/S3/Combinatorics/SpectralGraph/KoljancicOblakMinimumArcs.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Sara Koljančić; Polona Oblak (2026). *Combinatorial aspects of the nonsymmetric strong spectral property for graphs*. DOI: [10.13001/ela.2026.10523](https://doi.org/10.13001/ela.2026.10523). URL: <https://arxiv.org/abs/2604.21552v1>.

*Commentary.*

Every requiring support is connected. Apply the centralizer and incidence lower bound to its matrix with every prescribed entry equal to one. This gives at least 2n−1 arcs. The endpoint-looped double path has exactly that many arcs and requires nSSP for every exact real weighting. Both conclusions hold at each positive order, including order one.

## References

- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/KoljancicOblakMinimumArcs.ConnectedSupport`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/KoljancicOblakMinimumArcs.ExactSupport`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/KoljancicOblakMinimumArcs.HasNSSP`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/KoljancicOblakMinimumArcs.MinimumArcs`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/KoljancicOblakMinimumArcs.Requires`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/KoljancicOblakMinimumArcs.endpointSupport`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/KoljancicOblakMinimumArcs.endpoint_attainment`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/KoljancicOblakMinimumArcs.endpoint_requires`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/KoljancicOblakMinimumArcs.incidence`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/KoljancicOblakMinimumArcs.loop_support_eigenvalue_one`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/KoljancicOblakMinimumArcs.nssp_arc_bound_of_connected`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/KoljancicOblakMinimumArcs.nssp_centralizer_cycle_bound`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/KoljancicOblakMinimumArcs.requires_connected`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/KoljancicOblakMinimumArcs.requires_level_has_loop`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/KoljancicOblakMinimumArcs.result`
- Dependency: [D5/S3/Fourier/CharacterSelection/SignedIncidenceTotalUnimodularity](../../Fourier/CharacterSelection/SignedIncidenceTotalUnimodularity.md)
