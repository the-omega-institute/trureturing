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

**Definition 1.2 (Binary column-relation support).**

Lean statement: `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.relationSupport`

*Formalization.* `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.relationSupport` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sayantan Ganguly (2026). *Symplectic Matroids, Stabilizer Codes, and Quantum Secret-Sharing*. DOI: [10.48550/arXiv.2611.27300](https://doi.org/10.48550/arXiv.2611.27300). URL: <https://arxiv.org/abs/2611.27300v2>.

*Commentary.*

For an n by n binary matrix M and x in Bits(n), take the support of (Mx, x). An unstarred column belongs to the support when the corresponding coordinate of Mx is nonzero, and a starred column belongs when the corresponding coordinate of x is nonzero. For [I | M], the relation equation is Mx + Mx = 0 in characteristic two.

**Definition 1.3 (Admissible supports).**

Lean statement: `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.admissible`

*Formalization.* `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.admissible` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sayantan Ganguly (2026). *Symplectic Matroids, Stabilizer Codes, and Quantum Secret-Sharing*. DOI: [10.48550/arXiv.2611.27300](https://doi.org/10.48550/arXiv.2611.27300). URL: <https://arxiv.org/abs/2611.27300v2>.

*Commentary.*

A signed vertex set is admissible when it contains at most one of the two signed columns at each vertex.

**Definition 1.4 (Minimal nonempty relation supports).**

Lean statement: `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.isCircuit`

*Formalization.* `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.isCircuit` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sayantan Ganguly (2026). *Symplectic Matroids, Stabilizer Codes, and Quantum Secret-Sharing*. DOI: [10.48550/arXiv.2611.27300](https://doi.org/10.48550/arXiv.2611.27300). URL: <https://arxiv.org/abs/2611.27300v2>.

*Commentary.*

The support of x is a circuit when it is nonempty and admissible and no nonempty relation support, over all y in Bits(n), is a strict subset of it.

**Definition 1.5 (Supports meeting the dealer).**

Lean statement: `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.meetsDealer`

*Formalization.* `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.meetsDealer` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sayantan Ganguly (2026). *Symplectic Matroids, Stabilizer Codes, and Quantum Secret-Sharing*. DOI: [10.48550/arXiv.2611.27300](https://doi.org/10.48550/arXiv.2611.27300). URL: <https://arxiv.org/abs/2611.27300v2>.

*Commentary.*

A signed set meets the dealer d if it contains d or its starred copy.

**Definition 1.6 (Unsigned player support).**

Lean statement: `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.playerSupport`

*Formalization.* `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.playerSupport` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sayantan Ganguly (2026). *Symplectic Matroids, Stabilizer Codes, and Quantum Secret-Sharing*. DOI: [10.48550/arXiv.2611.27300](https://doi.org/10.48550/arXiv.2611.27300). URL: <https://arxiv.org/abs/2611.27300v2>.

*Commentary.*

Project a signed support to its vertex set and remove the dealer d.

**Definition 1.7 (Dealer circuits).**

Lean statement: `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.dealerCircuit`

*Formalization.* `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.dealerCircuit` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sayantan Ganguly (2026). *Symplectic Matroids, Stabilizer Codes, and Quantum Secret-Sharing*. DOI: [10.48550/arXiv.2611.27300](https://doi.org/10.48550/arXiv.2611.27300). URL: <https://arxiv.org/abs/2611.27300v2>.

*Commentary.*

A dealer circuit is a circuit whose signed support meets d.

**Definition 1.8 (Circuit-induced authorization).**

Lean statement: `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.circuitAuthorized`

*Formalization.* `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.circuitAuthorized` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sayantan Ganguly (2026). *Symplectic Matroids, Stabilizer Codes, and Quantum Secret-Sharing*. DOI: [10.48550/arXiv.2611.27300](https://doi.org/10.48550/arXiv.2611.27300). URL: <https://arxiv.org/abs/2611.27300v2>.

*Commentary.*

A is circuit-authorized when d is outside A and some dealer circuit has its unsigned player support contained in A. The finite upward closure of the full generator family equals that of its inclusion-minimal members, as in Definition 3 and Lemma 9.

**Definition 1.9 (Quantum access antecedent).**

Lean statement: `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.quantumAccess`

*Formalization.* `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.quantumAccess` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sayantan Ganguly (2026). *Symplectic Matroids, Stabilizer Codes, and Quantum Secret-Sharing*. DOI: [10.48550/arXiv.2611.27300](https://doi.org/10.48550/arXiv.2611.27300). URL: <https://arxiv.org/abs/2611.27300v2>.

*Commentary.*

At least one player set is circuit-authorized, and every two circuit-authorized sets have nonempty intersection, including when the sets are equal. Upward closure is built into circuit authorization.

**Theorem 1.10 (Upward closure on the players).**

Lean statement: `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.circuitAuthorized_mono`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.circuitAuthorized_mono` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sayantan Ganguly (2026). *Symplectic Matroids, Stabilizer Codes, and Quantum Secret-Sharing*. DOI: [10.48550/arXiv.2611.27300](https://doi.org/10.48550/arXiv.2611.27300). URL: <https://arxiv.org/abs/2611.27300v2>.

*Commentary.*

For any binary matrix M and dealer d, if A is circuit-authorized, A is contained in B and d is outside B, then B is circuit-authorized.

**Theorem 1.11 (Checking access on generators).**

Lean statement: `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.quantumAccess_of_generators`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.quantumAccess_of_generators` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sayantan Ganguly (2026). *Symplectic Matroids, Stabilizer Codes, and Quantum Secret-Sharing*. DOI: [10.48550/arXiv.2611.27300](https://doi.org/10.48550/arXiv.2611.27300). URL: <https://arxiv.org/abs/2611.27300v2>.

*Commentary.*

For any binary matrix M and dealer d, assume a dealer circuit exists and the player supports of every pair of dealer circuits intersect. Then the circuit-induced family satisfies the quantum access antecedent.

**Definition 1.12 (Labels supported on players and dealer).**

Lean statement: `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.supportedAt`

*Formalization.* `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.supportedAt` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sayantan Ganguly (2026). *Symplectic Matroids, Stabilizer Codes, and Quantum Secret-Sharing*. DOI: [10.48550/arXiv.2611.27300](https://doi.org/10.48550/arXiv.2611.27300). URL: <https://arxiv.org/abs/2611.27300v2>.

*Commentary.*

The pair (x, Mx) is supported on A together with d when both coordinates vanish at every vertex outside the union.

**Definition 1.13 (Attainable dealer labels).**

Lean statement: `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.dealerImage`

*Formalization.* `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.dealerImage` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sayantan Ganguly (2026). *Symplectic Matroids, Stabilizer Codes, and Quantum Secret-Sharing*. DOI: [10.48550/arXiv.2611.27300](https://doi.org/10.48550/arXiv.2611.27300). URL: <https://arxiv.org/abs/2611.27300v2>.

*Commentary.*

Take the set of pairs (x(d), (Mx)(d)) as x ranges over binary configurations with both label components supported on A together with d.

**Definition 1.14 (Edges of the witness).**

Lean statement: `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.witnessEdges`

*Formalization.* `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.witnessEdges` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sayantan Ganguly (2026). *Symplectic Matroids, Stabilizer Codes, and Quantum Secret-Sharing*. DOI: [10.48550/arXiv.2611.27300](https://doi.org/10.48550/arXiv.2611.27300). URL: <https://arxiv.org/abs/2611.27300v2>.

*Commentary.*

The unordered edges are 01, 02, 04, 06, 12, 13, 16, 23, 25, 45, 46 and 56. Each edge is stored as its smaller vertex followed by its larger vertex.

**Definition 1.15 (The simple witness graph).**

Lean statement: `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.witnessGraph`

*Formalization.* `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.witnessGraph` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sayantan Ganguly (2026). *Symplectic Matroids, Stabilizer Codes, and Quantum Secret-Sharing*. DOI: [10.48550/arXiv.2611.27300](https://doi.org/10.48550/arXiv.2611.27300). URL: <https://arxiv.org/abs/2611.27300v2>.

*Commentary.*

The vertex set is Fin(7). Two vertices are adjacent when their ordered pair or its reversal is in the displayed edge set.

**Definition 1.16 (The dealer).**

Lean statement: `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.witnessDealer`

*Formalization.* `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.witnessDealer` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sayantan Ganguly (2026). *Symplectic Matroids, Stabilizer Codes, and Quantum Secret-Sharing*. DOI: [10.48550/arXiv.2611.27300](https://doi.org/10.48550/arXiv.2611.27300). URL: <https://arxiv.org/abs/2611.27300v2>.

*Commentary.*

The dealer is vertex 4.

**Definition 1.17 (The retained players).**

Lean statement: `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.witnessPlayers`

*Formalization.* `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.witnessPlayers` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sayantan Ganguly (2026). *Symplectic Matroids, Stabilizer Codes, and Quantum Secret-Sharing*. DOI: [10.48550/arXiv.2611.27300](https://doi.org/10.48550/arXiv.2611.27300). URL: <https://arxiv.org/abs/2611.27300v2>.

*Commentary.*

The retained set A consists of vertices 2, 5 and 6.

**Definition 1.18 (Binary adjacency matrix).**

Lean statement: `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.witnessMatrix`

*Formalization.* `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.witnessMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sayantan Ganguly (2026). *Symplectic Matroids, Stabilizer Codes, and Quantum Secret-Sharing*. DOI: [10.48550/arXiv.2611.27300](https://doi.org/10.48550/arXiv.2611.27300). URL: <https://arxiv.org/abs/2611.27300v2>.

*Commentary.*

The matrix M is the adjacency matrix of the witness graph over ZMod(2).

**Definition 1.19 (The circuit relation vector).**

Lean statement: `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.witnessRelation`

*Formalization.* `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.witnessRelation` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sayantan Ganguly (2026). *Symplectic Matroids, Stabilizer Codes, and Quantum Secret-Sharing*. DOI: [10.48550/arXiv.2611.27300](https://doi.org/10.48550/arXiv.2611.27300). URL: <https://arxiv.org/abs/2611.27300v2>.

*Commentary.*

The vector x has value one at vertex 5 and zero at every other vertex.

**Theorem 1.20 (A dealer circuit).**

Lean statement: `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.witness_circuit`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.witness_circuit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sayantan Ganguly (2026). *Symplectic Matroids, Stabilizer Codes, and Quantum Secret-Sharing*. DOI: [10.48550/arXiv.2611.27300](https://doi.org/10.48550/arXiv.2611.27300). URL: <https://arxiv.org/abs/2611.27300v2>.

*Commentary.*

The displayed vector is a dealer circuit for the witness matrix and dealer. Its signed support is {2, 4, 5*, 6}. Minimality is checked against all 128 binary relation vectors.

**Theorem 1.21 (Circuit authorization for the retained players).**

Lean statement: `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.witness_authorized`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.witness_authorized` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sayantan Ganguly (2026). *Symplectic Matroids, Stabilizer Codes, and Quantum Secret-Sharing*. DOI: [10.48550/arXiv.2611.27300](https://doi.org/10.48550/arXiv.2611.27300). URL: <https://arxiv.org/abs/2611.27300v2>.

*Commentary.*

The witness relation gives a circuit meeting dealer 4 whose other vertices belong to A.

**Theorem 1.22 (A proper dealer image).**

Lean statement: `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.witness_dealer_image`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.witness_dealer_image` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sayantan Ganguly (2026). *Symplectic Matroids, Stabilizer Codes, and Quantum Secret-Sharing*. DOI: [10.48550/arXiv.2611.27300](https://doi.org/10.48550/arXiv.2611.27300). URL: <https://arxiv.org/abs/2611.27300v2>.

*Commentary.*

The image on the retained set is exactly {(0, 0), (0, 1)}. Setting x(0), x(1) and x(3) to zero and requiring the same rows of Mx to vanish leaves x(5) free and forces x(2), x(4) and x(6) to zero.

**Theorem 1.23 (Quantum access for the circuit family).**

Lean statement: `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.witness_quantum_access`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.witness_quantum_access` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sayantan Ganguly (2026). *Symplectic Matroids, Stabilizer Codes, and Quantum Secret-Sharing*. DOI: [10.48550/arXiv.2611.27300](https://doi.org/10.48550/arXiv.2611.27300). URL: <https://arxiv.org/abs/2611.27300v2>.

*Commentary.*

The witness matrix and dealer satisfy the quantum access antecedent. Every admissible nonempty dealer relation contains one of the ten listed supports 026, 036, 056, 236, 256, 356, 0123, 0125, 0135 and 1235. Each pair of these supports intersects.

**Definition 1.24 (Universal full dealer image under circuit access).**

Lean statement: `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.dealerImageClaim`

*Formalization.* `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.dealerImageClaim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sayantan Ganguly (2026). *Symplectic Matroids, Stabilizer Codes, and Quantum Secret-Sharing*. DOI: [10.48550/arXiv.2611.27300](https://doi.org/10.48550/arXiv.2611.27300). URL: <https://arxiv.org/abs/2611.27300v2>.

*Commentary.*

For every finite simple graph with decidable adjacency and every dealer, assume the quantum access antecedent for the binary adjacency matrix. The claim asks that every circuit-authorized set have the full two-coordinate dealer image.

**Theorem 1.25 (Refutation of the full dealer image claim).**

Lean statement: `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.witness_dealer_image_refutation`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.witness_dealer_image_refutation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sayantan Ganguly (2026). *Symplectic Matroids, Stabilizer Codes, and Quantum Secret-Sharing*. DOI: [10.48550/arXiv.2611.27300](https://doi.org/10.48550/arXiv.2611.27300). URL: <https://arxiv.org/abs/2611.27300v2>.

*Commentary.*

The universal full dealer image claim is false. The witness image omits (1, 0).

**Definition 1.26 (Discarded players).**

Lean statement: `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.discarded`

*Formalization.* `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.discarded` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sayantan Ganguly (2026). *Symplectic Matroids, Stabilizer Codes, and Quantum Secret-Sharing*. DOI: [10.48550/arXiv.2611.27300](https://doi.org/10.48550/arXiv.2611.27300). URL: <https://arxiv.org/abs/2611.27300v2>.

*Commentary.*

Remove the dealer and all retained vertices from Fin(n). For the witness the discarded vertices are {0, 1, 3}.

**Definition 1.27 (Configuration on a player register).**

Lean statement: `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.Config`

*Formalization.* `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.Config` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sayantan Ganguly (2026). *Symplectic Matroids, Stabilizer Codes, and Quantum Secret-Sharing*. DOI: [10.48550/arXiv.2611.27300](https://doi.org/10.48550/arXiv.2611.27300). URL: <https://arxiv.org/abs/2611.27300v2>.

*Commentary.*

A configuration on a vertex set assigns an element of Fin(2) to each vertex in that set.

**Definition 1.28 (Joint configuration with dealer).**

Lean statement: `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.fullConfig`

*Formalization.* `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.fullConfig` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sayantan Ganguly (2026). *Symplectic Matroids, Stabilizer Codes, and Quantum Secret-Sharing*. DOI: [10.48550/arXiv.2611.27300](https://doi.org/10.48550/arXiv.2611.27300). URL: <https://arxiv.org/abs/2611.27300v2>.

*Commentary.*

For a discarded and retained configuration pair and a dealer bit s, use s at d, the retained coordinate at vertices of A other than d, and the discarded coordinate at every remaining vertex.

**Definition 1.29 (Quadratic graph phase).**

Lean statement: `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.graphPhase`

*Formalization.* `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.graphPhase` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sayantan Ganguly (2026). *Symplectic Matroids, Stabilizer Codes, and Quantum Secret-Sharing*. DOI: [10.48550/arXiv.2611.27300](https://doi.org/10.48550/arXiv.2611.27300). URL: <https://arxiv.org/abs/2611.27300v2>.

*Commentary.*

For a matrix M and bit string z, sum M(i,j) z(i) z(j) over i < j in ZMod(2).

**Definition 1.30 (Integer graph sign).**

Lean statement: `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.signedGraphEntry`

*Formalization.* `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.signedGraphEntry` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sayantan Ganguly (2026). *Symplectic Matroids, Stabilizer Codes, and Quantum Secret-Sharing*. DOI: [10.48550/arXiv.2611.27300](https://doi.org/10.48550/arXiv.2611.27300). URL: <https://arxiv.org/abs/2611.27300v2>.

*Commentary.*

Raise minus one to the natural representative zero or one of the quadratic graph phase.

**Theorem 1.31 (Vanishing mixed-column sums).**

Lean statement: `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.witness_signed_cross_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.witness_signed_cross_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sayantan Ganguly (2026). *Symplectic Matroids, Stabilizer Codes, and Quantum Secret-Sharing*. DOI: [10.48550/arXiv.2611.27300](https://doi.org/10.48550/arXiv.2611.27300). URL: <https://arxiv.org/abs/2611.27300v2>.

*Commentary.*

For every two retained configurations a and b, sum the product of the integer graph signs at (c,a,0) and (c,b,1) over all discarded configurations c. Each of the 64 sums, with eight terms each, equals zero.

**Theorem 1.32 (The integer Gram matrix).**

Lean statement: `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.witness_signed_gram`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.witness_signed_gram` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sayantan Ganguly (2026). *Symplectic Matroids, Stabilizer Codes, and Quantum Secret-Sharing*. DOI: [10.48550/arXiv.2611.27300](https://doi.org/10.48550/arXiv.2611.27300). URL: <https://arxiv.org/abs/2611.27300v2>.

*Commentary.*

For each pair of dealer bits s and t, sum the product of their two signs over all pairs of discarded and retained configurations. The sum is 64 when s = t and zero otherwise.

**Theorem 1.33 (All labels on the dealer before restricting support).**

Lean statement: `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.witness_dealer_surjective`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.witness_dealer_surjective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sayantan Ganguly (2026). *Symplectic Matroids, Stabilizer Codes, and Quantum Secret-Sharing*. DOI: [10.48550/arXiv.2611.27300](https://doi.org/10.48550/arXiv.2611.27300). URL: <https://arxiv.org/abs/2611.27300v2>.

*Commentary.*

The map from all binary configurations to their dealer pair (x(4), (Mx)(4)) is surjective.

## References

- Truth anchor: `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.Bits`
- Truth anchor: `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.Config`
- Truth anchor: `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.admissible`
- Truth anchor: `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.circuitAuthorized`
- Truth anchor: `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.circuitAuthorized_mono`
- Truth anchor: `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.dealerCircuit`
- Truth anchor: `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.dealerImage`
- Truth anchor: `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.dealerImageClaim`
- Truth anchor: `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.discarded`
- Truth anchor: `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.fullConfig`
- Truth anchor: `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.graphPhase`
- Truth anchor: `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.isCircuit`
- Truth anchor: `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.meetsDealer`
- Truth anchor: `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.playerSupport`
- Truth anchor: `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.quantumAccess`
- Truth anchor: `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.quantumAccess_of_generators`
- Truth anchor: `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.relationSupport`
- Truth anchor: `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.signedGraphEntry`
- Truth anchor: `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.supportedAt`
- Truth anchor: `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.witnessDealer`
- Truth anchor: `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.witnessEdges`
- Truth anchor: `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.witnessGraph`
- Truth anchor: `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.witnessMatrix`
- Truth anchor: `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.witnessPlayers`
- Truth anchor: `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.witnessRelation`
- Truth anchor: `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.witness_authorized`
- Truth anchor: `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.witness_circuit`
- Truth anchor: `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.witness_dealer_image`
- Truth anchor: `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.witness_dealer_image_refutation`
- Truth anchor: `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.witness_dealer_surjective`
- Truth anchor: `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.witness_quantum_access`
- Truth anchor: `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.witness_signed_cross_zero`
- Truth anchor: `D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.witness_signed_gram`
