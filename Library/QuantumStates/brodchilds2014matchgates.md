---
bibkey: brodchilds2014matchgates
authors: Daniel J. Brod; Andrew M. Childs
year: 2014
title: "The computational power of matchgates and the XY interaction on arbitrary graphs"
doi: 10.26421/QIC14.11-12
url: https://arxiv.org/abs/1308.1463v1
claim: "Equation (4) gives the fermionic swap G(Z,X), which swaps 01 and 10, fixes 00 and negates 11; equation (6) shows that it swaps a zero auxiliary without the double-occupation sign. Theorem 1 establishes encoded circuit simulation on connected graphs other than paths and cycles under arbitrary adjacent matchgate access."
strata_touched: []
license: citation-only
triage: anchor
---

# Matchgate routing and its exact statistics boundary

Daniel J. Brod and Andrew M. Childs, *The computational power of matchgates
and the XY interaction on arbitrary graphs*, Quantum Information and
Computation **14**, 901–916 (2014),
[DOI 10.26421/QIC14.11-12](https://doi.org/10.26421/QIC14.11-12),
[arXiv:1308.1463v1](https://arxiv.org/abs/1308.1463v1).

Section II.A, equations (3)–(4), uses

$$
\operatorname{CZ}=\operatorname{fSWAP}\operatorname{SWAP},\qquad
\operatorname{fSWAP}=G(Z,X)=
\begin{pmatrix}
1&0&0&0\\
0&0&1&0\\
0&1&0&0\\
0&0&0&-1
\end{pmatrix}
$$

in the basis $00,01,10,11$. The ordinary SWAP is not a matchgate.
Section II.B, equation (6), states
$\operatorname{fSWAP}|0\rangle|\psi\rangle=|\psi\rangle|0\rangle$.
The same section routes encoded states through branching vertices with
zero auxiliaries. Theorem 1 concerns arbitrary matchgates on the edges of
a connected graph other than a path or cycle, and simulation of circuits
on $\Omega(\sqrt n)$ encoded qubits with polynomial operation overhead.
The XY-only construction is treated separately in Section IV and Theorem 3.

[FIB continuation Theorem 61.7](../../docs/develop/theory/FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION.md#61-source-owned-hard-core-green-interactions-and-population-uniform-renewal-retention)
consumes the exact matrix in equation (4), the zero-auxiliary routing
principle and the branching-wire setting. Its particular P/B product,
seven-swap controlled sign and 89-block density-phase word are established
there by their full local matrices. The paper's universality theorem is
not used as a replacement for that word or its private source coefficients.

Arbitrary-graph matchgate access is an additional circuit premise.
It does not make physical qubit hops into an exterior-power representation
in a fixed global ordering, supply a density-phase oracle, price coefficient
arithmetic, or calibrate gates and clocks. The FIB word's non-seam wires,
auxiliary retention and finite signed-dyadic approximation have their own
explicit premises and prices. The real-angle fSWAP identity does not assert
that $\pi/2$ is a dyadic angle or that a finite approximation leaves every
auxiliary exactly zero.
