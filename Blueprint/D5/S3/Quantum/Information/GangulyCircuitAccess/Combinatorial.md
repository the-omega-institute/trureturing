# Circuit access and dealer labels for the seven-vertex graph

## Abstract

An exact binary certificate gives a nonempty pairwise intersecting circuit family and a proper dealer image for a member of that family.

**Definition 1.1 (Binary configurations).**

Lean statement: `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.Bits`

*Formalization.* `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.Bits` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sayantan Ganguly (2026). *Symplectic Matroids, Stabilizer Codes, and Quantum Secret-Sharing*. DOI: [10.48550/arXiv.2611.27300](https://doi.org/10.48550/arXiv.2611.27300). URL: <https://arxiv.org/abs/2611.27300v2>.

*Commentary.*

Bits(n) is the type of functions from Fin(n) to the field ZMod(2). Vertices are numbered from zero.

**Definition 1.2 (Circuit-induced authorization).**

Lean statement: `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.circuitAuthorized`

*Formalization.* `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.circuitAuthorized` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sayantan Ganguly (2026). *Symplectic Matroids, Stabilizer Codes, and Quantum Secret-Sharing*. DOI: [10.48550/arXiv.2611.27300](https://doi.org/10.48550/arXiv.2611.27300). URL: <https://arxiv.org/abs/2611.27300v2>.

*Commentary.*

A is circuit-authorized when d is outside A and some dealer circuit has its unsigned player support contained in A. Binary column relations in [I | M] have coefficient pairs (Mx, x). A circuit is a minimal nonempty relation support with at most one signed column per vertex. The player support forgets the signs and omits the dealer.

**Definition 1.3 (Quantum access antecedent).**

Lean statement: `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.quantumAccess`

*Formalization.* `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.quantumAccess` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sayantan Ganguly (2026). *Symplectic Matroids, Stabilizer Codes, and Quantum Secret-Sharing*. DOI: [10.48550/arXiv.2611.27300](https://doi.org/10.48550/arXiv.2611.27300). URL: <https://arxiv.org/abs/2611.27300v2>.

*Commentary.*

At least one player set is circuit-authorized, and every two circuit-authorized sets have nonempty intersection, including when the sets are equal. Upward closure is built into circuit authorization.

**Definition 1.4 (Attainable dealer labels).**

Lean statement: `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.dealerImage`

*Formalization.* `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.dealerImage` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sayantan Ganguly (2026). *Symplectic Matroids, Stabilizer Codes, and Quantum Secret-Sharing*. DOI: [10.48550/arXiv.2611.27300](https://doi.org/10.48550/arXiv.2611.27300). URL: <https://arxiv.org/abs/2611.27300v2>.

*Commentary.*

Take the set of pairs (x(d), (Mx)(d)) as x ranges over binary configurations for which both x and Mx vanish outside A together with d.

**Definition 1.5 (The simple witness graph).**

Lean statement: `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.witnessGraph`

*Formalization.* `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.witnessGraph` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sayantan Ganguly (2026). *Symplectic Matroids, Stabilizer Codes, and Quantum Secret-Sharing*. DOI: [10.48550/arXiv.2611.27300](https://doi.org/10.48550/arXiv.2611.27300). URL: <https://arxiv.org/abs/2611.27300v2>.

*Commentary.*

The vertex set is Fin(7). The unordered edges are 01, 02, 04, 06, 12, 13, 16, 23, 25, 45, 46 and 56.

**Definition 1.6 (The dealer).**

Lean statement: `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.witnessDealer`

*Formalization.* `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.witnessDealer` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sayantan Ganguly (2026). *Symplectic Matroids, Stabilizer Codes, and Quantum Secret-Sharing*. DOI: [10.48550/arXiv.2611.27300](https://doi.org/10.48550/arXiv.2611.27300). URL: <https://arxiv.org/abs/2611.27300v2>.

*Commentary.*

The dealer is vertex 4.

**Definition 1.7 (The retained players).**

Lean statement: `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.witnessPlayers`

*Formalization.* `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.witnessPlayers` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sayantan Ganguly (2026). *Symplectic Matroids, Stabilizer Codes, and Quantum Secret-Sharing*. DOI: [10.48550/arXiv.2611.27300](https://doi.org/10.48550/arXiv.2611.27300). URL: <https://arxiv.org/abs/2611.27300v2>.

*Commentary.*

The retained set A consists of vertices 2, 5 and 6.

**Definition 1.8 (Binary adjacency matrix).**

Lean statement: `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.witnessMatrix`

*Formalization.* `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.witnessMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sayantan Ganguly (2026). *Symplectic Matroids, Stabilizer Codes, and Quantum Secret-Sharing*. DOI: [10.48550/arXiv.2611.27300](https://doi.org/10.48550/arXiv.2611.27300). URL: <https://arxiv.org/abs/2611.27300v2>.

*Commentary.*

The matrix M is the adjacency matrix of the witness graph over ZMod(2).

**Theorem 1.9 (Circuit authorization for the retained players).**

Lean statement: `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.witness_authorized`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.witness_authorized` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sayantan Ganguly (2026). *Symplectic Matroids, Stabilizer Codes, and Quantum Secret-Sharing*. DOI: [10.48550/arXiv.2611.27300](https://doi.org/10.48550/arXiv.2611.27300). URL: <https://arxiv.org/abs/2611.27300v2>.

*Commentary.*

The relation vector with a single one at vertex 5 gives the signed circuit {2, 4, 5*, 6}. Its minimality is checked against all 128 binary relation vectors. Its player support is A.

**Theorem 1.10 (A proper dealer image).**

Lean statement: `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.witness_dealer_image`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.witness_dealer_image` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sayantan Ganguly (2026). *Symplectic Matroids, Stabilizer Codes, and Quantum Secret-Sharing*. DOI: [10.48550/arXiv.2611.27300](https://doi.org/10.48550/arXiv.2611.27300). URL: <https://arxiv.org/abs/2611.27300v2>.

*Commentary.*

The image on the retained set is exactly {(0, 0), (0, 1)}. Setting x(0), x(1) and x(3) to zero and requiring the same rows of Mx to vanish leaves x(5) free and forces x(2), x(4) and x(6) to zero.

**Theorem 1.11 (Quantum access for the circuit family).**

Lean statement: `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.witness_quantum_access`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.witness_quantum_access` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sayantan Ganguly (2026). *Symplectic Matroids, Stabilizer Codes, and Quantum Secret-Sharing*. DOI: [10.48550/arXiv.2611.27300](https://doi.org/10.48550/arXiv.2611.27300). URL: <https://arxiv.org/abs/2611.27300v2>.

*Commentary.*

The witness matrix and dealer satisfy the quantum access antecedent. Every admissible nonempty dealer relation contains one of the ten listed supports 026, 036, 056, 236, 256, 356, 0123, 0125, 0135 and 1235. Each pair of these supports intersects. A common vertex of the two generator supports also belongs to both authorized supersets.

**Definition 1.12 (Discarded players).**

Lean statement: `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.discarded`

*Formalization.* `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.discarded` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sayantan Ganguly (2026). *Symplectic Matroids, Stabilizer Codes, and Quantum Secret-Sharing*. DOI: [10.48550/arXiv.2611.27300](https://doi.org/10.48550/arXiv.2611.27300). URL: <https://arxiv.org/abs/2611.27300v2>.

*Commentary.*

Remove the dealer and all retained vertices from Fin(n). For the witness the discarded vertices are {0, 1, 3}.

**Definition 1.13 (Configuration on a player register).**

Lean statement: `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.Config`

*Formalization.* `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.Config` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sayantan Ganguly (2026). *Symplectic Matroids, Stabilizer Codes, and Quantum Secret-Sharing*. DOI: [10.48550/arXiv.2611.27300](https://doi.org/10.48550/arXiv.2611.27300). URL: <https://arxiv.org/abs/2611.27300v2>.

*Commentary.*

A configuration on a vertex set assigns an element of Fin(2) to each vertex in that set.

**Definition 1.14 (Joint configuration with dealer).**

Lean statement: `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.fullConfig`

*Formalization.* `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.fullConfig` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sayantan Ganguly (2026). *Symplectic Matroids, Stabilizer Codes, and Quantum Secret-Sharing*. DOI: [10.48550/arXiv.2611.27300](https://doi.org/10.48550/arXiv.2611.27300). URL: <https://arxiv.org/abs/2611.27300v2>.

*Commentary.*

For a discarded and retained configuration pair and a dealer bit s, use s at d, the retained coordinate at vertices of A other than d, and the discarded coordinate at every remaining vertex.

**Definition 1.15 (Quadratic graph phase).**

Lean statement: `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.graphPhase`

*Formalization.* `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.graphPhase` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sayantan Ganguly (2026). *Symplectic Matroids, Stabilizer Codes, and Quantum Secret-Sharing*. DOI: [10.48550/arXiv.2611.27300](https://doi.org/10.48550/arXiv.2611.27300). URL: <https://arxiv.org/abs/2611.27300v2>.

*Commentary.*

For a matrix M and bit string z, sum M(i,j) z(i) z(j) over i < j in ZMod(2).

**Definition 1.16 (Integer graph sign).**

Lean statement: `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.signedGraphEntry`

*Formalization.* `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.signedGraphEntry` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sayantan Ganguly (2026). *Symplectic Matroids, Stabilizer Codes, and Quantum Secret-Sharing*. DOI: [10.48550/arXiv.2611.27300](https://doi.org/10.48550/arXiv.2611.27300). URL: <https://arxiv.org/abs/2611.27300v2>.

*Commentary.*

Raise minus one to the natural representative zero or one of the quadratic graph phase.

**Theorem 1.17 (Vanishing mixed-column sums).**

Lean statement: `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.witness_signed_cross_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.witness_signed_cross_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sayantan Ganguly (2026). *Symplectic Matroids, Stabilizer Codes, and Quantum Secret-Sharing*. DOI: [10.48550/arXiv.2611.27300](https://doi.org/10.48550/arXiv.2611.27300). URL: <https://arxiv.org/abs/2611.27300v2>.

*Commentary.*

For every two retained configurations a and b, sum the product of the integer graph signs at (c,a,0) and (c,b,1) over all discarded configurations c. Each of the 64 sums, with eight terms each, equals zero.

**Theorem 1.18 (The integer Gram matrix).**

Lean statement: `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.witness_signed_gram`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.witness_signed_gram` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sayantan Ganguly (2026). *Symplectic Matroids, Stabilizer Codes, and Quantum Secret-Sharing*. DOI: [10.48550/arXiv.2611.27300](https://doi.org/10.48550/arXiv.2611.27300). URL: <https://arxiv.org/abs/2611.27300v2>.

*Commentary.*

For each pair of dealer bits s and t, sum the product of their two signs over all pairs of discarded and retained configurations. The sum is 64 when s = t and zero otherwise.

**Theorem 1.19 (All labels on the dealer before restricting support).**

Lean statement: `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.witness_dealer_surjective`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.witness_dealer_surjective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sayantan Ganguly (2026). *Symplectic Matroids, Stabilizer Codes, and Quantum Secret-Sharing*. DOI: [10.48550/arXiv.2611.27300](https://doi.org/10.48550/arXiv.2611.27300). URL: <https://arxiv.org/abs/2611.27300v2>.

*Commentary.*

The map from all binary configurations to their dealer pair (x(4), (Mx)(4)) is surjective.

## References

- Truth anchor: `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.Bits`
- Truth anchor: `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.Config`
- Truth anchor: `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.circuitAuthorized`
- Truth anchor: `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.dealerImage`
- Truth anchor: `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.discarded`
- Truth anchor: `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.fullConfig`
- Truth anchor: `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.graphPhase`
- Truth anchor: `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.quantumAccess`
- Truth anchor: `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.signedGraphEntry`
- Truth anchor: `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.witnessDealer`
- Truth anchor: `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.witnessGraph`
- Truth anchor: `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.witnessMatrix`
- Truth anchor: `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.witnessPlayers`
- Truth anchor: `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.witness_authorized`
- Truth anchor: `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.witness_dealer_image`
- Truth anchor: `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.witness_dealer_surjective`
- Truth anchor: `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.witness_quantum_access`
- Truth anchor: `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.witness_signed_cross_zero`
- Truth anchor: `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.witness_signed_gram`
