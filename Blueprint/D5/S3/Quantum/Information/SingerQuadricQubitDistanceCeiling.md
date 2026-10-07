# The q = 2 Singer-quadric qubit codes have minimum distance 2 for every d >= 2

## Abstract

Kulhandjian and Hanzo (arXiv:2610.02392) build qubit stabilizer codes Q(2,d) from a Singer difference set and the quadric Tr(z^3) = 0 in PG(d,2), prove numerically for d <= 6 that the cross-correlation u = M_Q tau_H is the all-ones vector, and conjecture (Conjecture 24) that this and the resulting minimum distance 2 hold for every d >= 2. For every d >= 2 and every primitive element of GF(2^(d+1)), u is all-ones, every Z_i Z_j with i != j lies in the centralizer and not in the stabilizer row space, and no element of the centralizer outside the stabilizers has weight below 2.

**Definition 1.1 (The field).**

$$\forall d : \mathbb{N}, \operatorname{K}\left(d\right) = \operatorname{GaloisField}\left(2, d + 1\right)$$

*Formalization.* `D5/S3/Quantum/Information/SingerQuadricQubitDistanceCeiling.K` (`✓ std3`).

*Citation.* M. Kulhandjian; L. Hanzo (2026). *Singer-Difference-Set Qudit Stabilizer Codes from Non-Degenerate Quadrics in PG(d,q): Construction, Structural Theorems, and Monte-Carlo Performance*. DOI: [10.48550/arXiv.2610.02392](https://doi.org/10.48550/arXiv.2610.02392). URL: <https://arxiv.org/abs/2610.02392v1>.

*Commentary.*

K(d) is the Galois field GF(2^(d+1)), the field K of the paper at q = 2.

**Definition 1.2 (The code length).**

$$\forall d : \mathbb{N}, \operatorname{n}\left(d\right) = 2^{d + 1} - 1$$

*Formalization.* `D5/S3/Quantum/Information/SingerQuadricQubitDistanceCeiling.n` (`✓ std3`).

*Citation.* M. Kulhandjian; L. Hanzo (2026). *Singer-Difference-Set Qudit Stabilizer Codes from Non-Degenerate Quadrics in PG(d,q): Construction, Structural Theorems, and Monte-Carlo Performance*. DOI: [10.48550/arXiv.2610.02392](https://doi.org/10.48550/arXiv.2610.02392). URL: <https://arxiv.org/abs/2610.02392v1>.

*Commentary.*

The number of qubits n = (q^(d+1) - 1)/(q - 1) of the paper at q = 2, which is 2^(d+1) - 1, the order of the multiplicative group of K(d).

**Definition 1.3 (The absolute trace).**

$$\forall d : \mathbb{N}, \forall x : \operatorname{K}\left(d\right), \operatorname{tr}\left(x\right) = \operatorname{trace}\left(\operatorname{ZMod}\left(2\right), \operatorname{K}\left(d\right), x\right)$$

*Formalization.* `D5/S3/Quantum/Information/SingerQuadricQubitDistanceCeiling.tr` (`✓ std3`).

*Citation.* M. Kulhandjian; L. Hanzo (2026). *Singer-Difference-Set Qudit Stabilizer Codes from Non-Degenerate Quadrics in PG(d,q): Construction, Structural Theorems, and Monte-Carlo Performance*. DOI: [10.48550/arXiv.2610.02392](https://doi.org/10.48550/arXiv.2610.02392). URL: <https://arxiv.org/abs/2610.02392v1>.

*Commentary.*

The trace of K(d) over its prime field ZMod 2, the trace Tr from K to F of the paper.

**Definition 1.4 (The hyperplane indicator).**

$$\forall d : \mathbb{N}, \forall \alpha : \operatorname{K}\left(d\right), \forall i : \operatorname{Fin}\left(\operatorname{n}\left(d\right)\right), \operatorname{tauH}\left(\alpha\right)\left(i\right) = \operatorname{ite}\left(\operatorname{tr}\left(\alpha^{i}\right) = 0, 1, 0\right)$$

*Formalization.* `D5/S3/Quantum/Information/SingerQuadricQubitDistanceCeiling.tauH` (`✓ std3`).

*Citation.* M. Kulhandjian; L. Hanzo (2026). *Singer-Difference-Set Qudit Stabilizer Codes from Non-Degenerate Quadrics in PG(d,q): Construction, Structural Theorems, and Monte-Carlo Performance*. DOI: [10.48550/arXiv.2610.02392](https://doi.org/10.48550/arXiv.2610.02392). URL: <https://arxiv.org/abs/2610.02392v1>.

*Commentary.*

Appendix A, Step 2: the i-th entry is 1 when the trace of alpha^i vanishes and 0 otherwise, for i in Fin(n(d)). Here ite(c, a, b) is a if c holds and b otherwise.

**Definition 1.5 (The quadric indicator).**

$$\forall d : \mathbb{N}, \forall \alpha : \operatorname{K}\left(d\right), \forall i : \operatorname{Fin}\left(\operatorname{n}\left(d\right)\right), \operatorname{tauQ}\left(\alpha\right)\left(i\right) = \operatorname{ite}\left(\operatorname{tr}\left(\alpha^{3 \cdot i}\right) = 0, 1, 0\right)$$

*Formalization.* `D5/S3/Quantum/Information/SingerQuadricQubitDistanceCeiling.tauQ` (`✓ std3`).

*Citation.* M. Kulhandjian; L. Hanzo (2026). *Singer-Difference-Set Qudit Stabilizer Codes from Non-Degenerate Quadrics in PG(d,q): Construction, Structural Theorems, and Monte-Carlo Performance*. DOI: [10.48550/arXiv.2610.02392](https://doi.org/10.48550/arXiv.2610.02392). URL: <https://arxiv.org/abs/2610.02392v1>.

*Commentary.*

Appendix A, Step 3 with xi = q + 1 = 3: the i-th entry is 1 when the trace of alpha^(3i) vanishes and 0 otherwise.

**Definition 1.6 (The Z block).**

$$\forall d : \mathbb{N}, \forall \alpha : \operatorname{K}\left(d\right), \operatorname{Hz}\left(\alpha\right) = \operatorname{circulant}\left(\operatorname{tauH}\left(\alpha\right)\right)$$

*Formalization.* `D5/S3/Quantum/Information/SingerQuadricQubitDistanceCeiling.Hz` (`✓ std3`).

*Citation.* M. Kulhandjian; L. Hanzo (2026). *Singer-Difference-Set Qudit Stabilizer Codes from Non-Degenerate Quadrics in PG(d,q): Construction, Structural Theorems, and Monte-Carlo Performance*. DOI: [10.48550/arXiv.2610.02392](https://doi.org/10.48550/arXiv.2610.02392). URL: <https://arxiv.org/abs/2610.02392v1>.

*Commentary.*

H_z = A is the Singer incidence matrix circ(tau_H). Mathlib's circulant(v) has entries v(i - j), with subtraction in Fin(n(d)), the paper's (M)_{i,j} = v_{(i-j) mod n}.

**Definition 1.7 (The X block).**

$$\forall d : \mathbb{N}, \forall \alpha : \operatorname{K}\left(d\right), \operatorname{Hx}\left(\alpha\right) = \operatorname{circulant}\left(\operatorname{tauQ}\left(\alpha\right)\right) \cdot \operatorname{circulant}\left(\operatorname{tauH}\left(\alpha\right)\right)$$

*Formalization.* `D5/S3/Quantum/Information/SingerQuadricQubitDistanceCeiling.Hx` (`✓ std3`).

*Citation.* M. Kulhandjian; L. Hanzo (2026). *Singer-Difference-Set Qudit Stabilizer Codes from Non-Degenerate Quadrics in PG(d,q): Construction, Structural Theorems, and Monte-Carlo Performance*. DOI: [10.48550/arXiv.2610.02392](https://doi.org/10.48550/arXiv.2610.02392). URL: <https://arxiv.org/abs/2610.02392v1>.

*Commentary.*

H_x = M_Q A, the product of the quadric circulant M_Q = circ(tau_Q) and A, with matrix multiplication over ZMod 2.

**Definition 1.8 (The centralizer).**

$$\forall d : \mathbb{N}, \forall \alpha : \operatorname{K}\left(d\right), \forall a : \operatorname{Fin}\left(\operatorname{n}\left(d\right)\right) \to \operatorname{ZMod}\left(2\right), \forall b : \operatorname{Fin}\left(\operatorname{n}\left(d\right)\right) \to \operatorname{ZMod}\left(2\right), (a, b) \in \operatorname{centralizer}\left(\alpha\right) \Leftrightarrow (\operatorname{vecMul}\left(a, \operatorname{transpose}\left(\operatorname{Hx}\left(\alpha\right)\right)\right) = \operatorname{vecMul}\left(b, \operatorname{transpose}\left(\operatorname{Hz}\left(\alpha\right)\right)\right))$$

*Formalization.* `D5/S3/Quantum/Information/SingerQuadricQubitDistanceCeiling.centralizer` (`✓ std3`).

*Citation.* M. Kulhandjian; L. Hanzo (2026). *Singer-Difference-Set Qudit Stabilizer Codes from Non-Degenerate Quadrics in PG(d,q): Construction, Structural Theorems, and Monte-Carlo Performance*. DOI: [10.48550/arXiv.2610.02392](https://doi.org/10.48550/arXiv.2610.02392). URL: <https://arxiv.org/abs/2610.02392v1>.

*Commentary.*

The paper's centralizer: pairs (a, b) of vectors over ZMod 2 indexed by Fin(n(d)) with a H_x^T = b H_z^T, where a is the Z part and b the X part and vecMul(c, M) is the row vector c times M.

**Definition 1.9 (The stabilizer row space).**

$$\forall d : \mathbb{N}, \forall \alpha : \operatorname{K}\left(d\right), \forall a : \operatorname{Fin}\left(\operatorname{n}\left(d\right)\right) \to \operatorname{ZMod}\left(2\right), \forall b : \operatorname{Fin}\left(\operatorname{n}\left(d\right)\right) \to \operatorname{ZMod}\left(2\right), (a, b) \in \operatorname{stabilizers}\left(\alpha\right) \Leftrightarrow (\exists c : \operatorname{Fin}\left(\operatorname{n}\left(d\right)\right) \to \operatorname{ZMod}\left(2\right), (a = \operatorname{vecMul}\left(c, \operatorname{Hz}\left(\alpha\right)\right)) \land (b = \operatorname{vecMul}\left(c, \operatorname{Hx}\left(\alpha\right)\right)))$$

*Formalization.* `D5/S3/Quantum/Information/SingerQuadricQubitDistanceCeiling.stabilizers` (`✓ std3`).

*Citation.* M. Kulhandjian; L. Hanzo (2026). *Singer-Difference-Set Qudit Stabilizer Codes from Non-Degenerate Quadrics in PG(d,q): Construction, Structural Theorems, and Monte-Carlo Performance*. DOI: [10.48550/arXiv.2610.02392](https://doi.org/10.48550/arXiv.2610.02392). URL: <https://arxiv.org/abs/2610.02392v1>.

*Commentary.*

The row space of H = (H_z | H_x): the pairs (c H_z, c H_x) for all row vectors c over ZMod 2.

**Definition 1.10 (The symplectic weight).**

$$\forall d : \mathbb{N}, \forall a : \operatorname{Fin}\left(\operatorname{n}\left(d\right)\right) \to \operatorname{ZMod}\left(2\right), \forall b : \operatorname{Fin}\left(\operatorname{n}\left(d\right)\right) \to \operatorname{ZMod}\left(2\right), \operatorname{wt}\left((a, b)\right) = \operatorname{card}\left(\operatorname{filter}\left(i \mapsto (a\left(i\right) \ne 0) \lor (b\left(i\right) \ne 0), \operatorname{univ}\left(\operatorname{Fin}\left(\operatorname{n}\left(d\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Information/SingerQuadricQubitDistanceCeiling.wt` (`✓ std3`).

*Citation.* M. Kulhandjian; L. Hanzo (2026). *Singer-Difference-Set Qudit Stabilizer Codes from Non-Degenerate Quadrics in PG(d,q): Construction, Structural Theorems, and Monte-Carlo Performance*. DOI: [10.48550/arXiv.2610.02392](https://doi.org/10.48550/arXiv.2610.02392). URL: <https://arxiv.org/abs/2610.02392v1>.

*Commentary.*

The number of positions i at which (a_i, b_i) is not (0, 0), the weight of a Pauli operator. For the weight-two witness it equals the Hamming weight of (a, b), and every lower bound for it is a lower bound for that Hamming weight.

**Definition 1.11 (Conjecture 24).**

$$claim \Leftrightarrow (\forall d : \mathbb{N}, (2 \le d) \Rightarrow (\forall \alpha : \operatorname{K}\left(d\right), (\operatorname{orderOf}\left(\alpha\right) = \operatorname{n}\left(d\right)) \Rightarrow ((\operatorname{mulVec}\left(\operatorname{circulant}\left(\operatorname{tauQ}\left(\alpha\right)\right), \operatorname{tauH}\left(\alpha\right)\right) = 1) \land ((\forall i : \operatorname{Fin}\left(\operatorname{n}\left(d\right)\right), \forall j : \operatorname{Fin}\left(\operatorname{n}\left(d\right)\right), (i \ne j) \Rightarrow (((\operatorname{single}\left(i, 1\right) + \operatorname{single}\left(j, 1\right), 0) \in \operatorname{centralizer}\left(\alpha\right)) \land (\neg ((\operatorname{single}\left(i, 1\right) + \operatorname{single}\left(j, 1\right), 0) \in \operatorname{stabilizers}\left(\alpha\right))))) \land (\forall v : (\operatorname{Fin}\left(\operatorname{n}\left(d\right)\right) \to \operatorname{ZMod}\left(2\right)) \times (\operatorname{Fin}\left(\operatorname{n}\left(d\right)\right) \to \operatorname{ZMod}\left(2\right)), (v \in \operatorname{centralizer}\left(\alpha\right)) \Rightarrow ((\neg (v \in \operatorname{stabilizers}\left(\alpha\right))) \Rightarrow (2 \le \operatorname{wt}\left(v\right))))))))$$

*Formalization.* `D5/S3/Quantum/Information/SingerQuadricQubitDistanceCeiling.claim` (`✓ std3`).

*Citation.* M. Kulhandjian; L. Hanzo (2026). *Singer-Difference-Set Qudit Stabilizer Codes from Non-Degenerate Quadrics in PG(d,q): Construction, Structural Theorems, and Monte-Carlo Performance*. DOI: [10.48550/arXiv.2610.02392](https://doi.org/10.48550/arXiv.2610.02392). URL: <https://arxiv.org/abs/2610.02392v1>.

*Commentary.*

Proposition 23 for every d >= 2 and every primitive element alpha (an element of order n(d)): u = M_Q tau_H is the all-ones vector; for every pair of distinct positions i, j the operator Z_i Z_j, written (e_i + e_j, 0), lies in the centralizer and not in the stabilizer row space; and every element of the centralizer outside the stabilizers has weight at least 2. Together these give d_min = 2.

**Theorem 1.12 (The q = 2 distance ceiling holds for every d >= 2).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/SingerQuadricQubitDistanceCeiling.result` (`✓ std3`). ∎

*Resolves.* `Problems/kulhandjian-hanzo-2026-q2-distance-ceiling` (proved) by `D5/S3/Quantum/Information/SingerQuadricQubitDistanceCeiling.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"kulhandjian-hanzo-2026-q2-distance-ceiling","declaration_gid":"D5/S3/Quantum/Information/SingerQuadricQubitDistanceCeiling.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* M. Kulhandjian; L. Hanzo (2026). *Singer-Difference-Set Qudit Stabilizer Codes from Non-Degenerate Quadrics in PG(d,q): Construction, Structural Theorems, and Monte-Carlo Performance*. DOI: [10.48550/arXiv.2610.02392](https://doi.org/10.48550/arXiv.2610.02392). URL: <https://arxiv.org/abs/2610.02392v1>.

*Commentary.*

Put m = d + 1 >= 3 and n = 2^m - 1 >= 7. Power sums over the units of K(d) vanish except when n divides the exponent, and no exponent 2^r, 3 2^s or 3 2^s - 2^r with r, s < m is divisible by n: the last would give 2^t = 3 modulo n with t < m. Writing the trace as the sum of the Frobenius powers x^(2^i), the entry u_k is the sum over x in the units of (1 + Tr(x))(1 + Tr(alpha^(3k) x^(-3))); every non-constant term is a multiple of a vanishing power sum and the constant term is n = 1 in ZMod 2, so u is all-ones and H_x is the all-ones matrix. For b != 0, x -> Tr(b x) is a nonzero linear functional, so each of its fibers has 2^(m-1) elements. Every vector in the row space of A has entries c + Tr(b alpha^(-j)), so its weight is 0, n, 2^(m-1) or 2^(m-1) - 1, never 2; hence Z_i Z_j is not a stabilizer, while H_x = J puts it in the centralizer. A centralizer element of weight 1 would make the all-ones vector, a column of A, or its complement zero, but every column of A has weight 2^(m-1) - 1, strictly between 0 and n.

## References

- Truth anchor: `D5/S3/Quantum/Information/SingerQuadricQubitDistanceCeiling.Hx`
- Truth anchor: `D5/S3/Quantum/Information/SingerQuadricQubitDistanceCeiling.Hz`
- Truth anchor: `D5/S3/Quantum/Information/SingerQuadricQubitDistanceCeiling.K`
- Truth anchor: `D5/S3/Quantum/Information/SingerQuadricQubitDistanceCeiling.centralizer`
- Truth anchor: `D5/S3/Quantum/Information/SingerQuadricQubitDistanceCeiling.claim`
- Truth anchor: `D5/S3/Quantum/Information/SingerQuadricQubitDistanceCeiling.n`
- Truth anchor: `D5/S3/Quantum/Information/SingerQuadricQubitDistanceCeiling.result`
- Truth anchor: `D5/S3/Quantum/Information/SingerQuadricQubitDistanceCeiling.stabilizers`
- Truth anchor: `D5/S3/Quantum/Information/SingerQuadricQubitDistanceCeiling.tauH`
- Truth anchor: `D5/S3/Quantum/Information/SingerQuadricQubitDistanceCeiling.tauQ`
- Truth anchor: `D5/S3/Quantum/Information/SingerQuadricQubitDistanceCeiling.tr`
- Truth anchor: `D5/S3/Quantum/Information/SingerQuadricQubitDistanceCeiling.wt`
