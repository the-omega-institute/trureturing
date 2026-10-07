# Kulhandjian-Hanzo Conjecture 25: the odd-prime distance bound

## Abstract

For every odd prime p and every primitive element of GaloisField p 3, the Singer-quadric stabilizer code has a non-stabilizer centralizer vector of Pauli weight at most p+1. A translated trace-plane indicator gives a centralizer vector. A right-kernel separator and two correlation moments ensure that at least one translated vector lies outside the stabilizer row space.

**Definition 1.1 (The trace-plane indicator).**

$$\forall p : \mathbb{N}, [\operatorname{Fact}\left(\operatorname{Nat}.\operatorname{Prime}\left(p\right)\right)], \forall \alpha : \operatorname{GaloisField}\left(p, 3\right), \forall i : \operatorname{Fin}\left(p^{2} + p + 1\right), \operatorname{tauH}\left(\alpha\right)\left(i\right) = \operatorname{ite}\left(\operatorname{Algebra}.\operatorname{trace}\left(\operatorname{ZMod}\left(p\right), \operatorname{GaloisField}\left(p, 3\right), \alpha^{\operatorname{val}\left(i\right)}\right) = 0, 1, 0\right)$$

*Formalization.* `D5/S3/Quantum/Information/SingerQuadricQuditDistanceBound.tauH` (`✓ std3`).

*Citation.* M. Kulhandjian; L. Hanzo (2026). *Singer-Difference-Set Qudit Stabilizer Codes from Non-Degenerate Quadrics in PG(d,q): Construction, Structural Theorems, and Monte-Carlo Performance*. DOI: [10.48550/arXiv.2610.02392](https://doi.org/10.48550/arXiv.2610.02392). URL: <https://arxiv.org/abs/2610.02392v1>.

*Commentary.*

Page 7, Section III: “Its first column $\mathbf{\tau_{H}}$ has $(\mathbf{\tau_{H}})_{i} = 1$ iff $\operatorname{Tr}_{K/F}(\alpha^{i}) = 0$.”

At q=p and d=2, the carrier is GaloisField p 3 and the positions are Fin(p^2+p+1). The entry is 0 when the trace is nonzero.

**Definition 1.2 (The quadric indicator).**

$$\forall p : \mathbb{N}, [\operatorname{Fact}\left(\operatorname{Nat}.\operatorname{Prime}\left(p\right)\right)], \forall \alpha : \operatorname{GaloisField}\left(p, 3\right), \forall i : \operatorname{Fin}\left(p^{2} + p + 1\right), \operatorname{tauQ}\left(\alpha\right)\left(i\right) = \operatorname{ite}\left(\operatorname{Algebra}.\operatorname{trace}\left(\operatorname{ZMod}\left(p\right), \operatorname{GaloisField}\left(p, 3\right), \alpha^{2 \cdot \operatorname{val}\left(i\right)}\right) = 0, 1, 0\right)$$

*Formalization.* `D5/S3/Quantum/Information/SingerQuadricQuditDistanceBound.tauQ` (`✓ std3`).

*Citation.* M. Kulhandjian; L. Hanzo (2026). *Singer-Difference-Set Qudit Stabilizer Codes from Non-Degenerate Quadrics in PG(d,q): Construction, Structural Theorems, and Monte-Carlo Performance*. DOI: [10.48550/arXiv.2610.02392](https://doi.org/10.48550/arXiv.2610.02392). URL: <https://arxiv.org/abs/2610.02392v1>.

*Commentary.*

Page 27, Appendix A, Step 3: “Set $\xi = q + 1$ if $q$ is even, $\xi = 2$ if $q$ is odd. Define $\mathbf{\tau_{Q}} \in \left(\mathbb{F}_{q}\right)^{n}$ by $(\mathbf{\tau_{Q}})_{i} = 1$ if $T[(\xi \cdot i) \operatorname{mod} (q^{d + 1} - 1)] = 0$, else $0$.”

For odd p the exponent is 2*val(i), with trace zero giving entry 1 and nonzero trace giving entry 0. Primitive powers have period p^3-1, so the source's exponent reduction modulo p^3-1 gives the same entry.

**Definition 1.3 (The Singer circulant).**

$$\forall p : \mathbb{N}, [\operatorname{Fact}\left(\operatorname{Nat}.\operatorname{Prime}\left(p\right)\right)], \forall \alpha : \operatorname{GaloisField}\left(p, 3\right), \operatorname{A}\left(\alpha\right) = \operatorname{Matrix}.\operatorname{circulant}\left(\operatorname{tauH}\left(\alpha\right)\right)$$

*Formalization.* `D5/S3/Quantum/Information/SingerQuadricQuditDistanceBound.A` (`✓ std3`).

*Citation.* M. Kulhandjian; L. Hanzo (2026). *Singer-Difference-Set Qudit Stabilizer Codes from Non-Degenerate Quadrics in PG(d,q): Construction, Structural Theorems, and Monte-Carlo Performance*. DOI: [10.48550/arXiv.2610.02392](https://doi.org/10.48550/arXiv.2610.02392). URL: <https://arxiv.org/abs/2610.02392v1>.

*Commentary.*

A=circ(tau_H), with entry tauH(alpha)(i-j) and cyclic subtraction in Fin(p^2+p+1).

**Definition 1.4 (The quadric circulant).**

$$\forall p : \mathbb{N}, [\operatorname{Fact}\left(\operatorname{Nat}.\operatorname{Prime}\left(p\right)\right)], \forall \alpha : \operatorname{GaloisField}\left(p, 3\right), \operatorname{MQ}\left(\alpha\right) = \operatorname{Matrix}.\operatorname{circulant}\left(\operatorname{tauQ}\left(\alpha\right)\right)$$

*Formalization.* `D5/S3/Quantum/Information/SingerQuadricQuditDistanceBound.MQ` (`✓ std3`).

*Citation.* M. Kulhandjian; L. Hanzo (2026). *Singer-Difference-Set Qudit Stabilizer Codes from Non-Degenerate Quadrics in PG(d,q): Construction, Structural Theorems, and Monte-Carlo Performance*. DOI: [10.48550/arXiv.2610.02392](https://doi.org/10.48550/arXiv.2610.02392). URL: <https://arxiv.org/abs/2610.02392v1>.

*Commentary.*

M_Q=circ(tau_Q), using the same first-column circulant convention as A.

**Definition 1.5 (The second check block).**

$$\forall p : \mathbb{N}, [\operatorname{Fact}\left(\operatorname{Nat}.\operatorname{Prime}\left(p\right)\right)], \forall \alpha : \operatorname{GaloisField}\left(p, 3\right), \operatorname{B}\left(\alpha\right) = \operatorname{MQ}\left(\alpha\right) \cdot \operatorname{A}\left(\alpha\right)$$

*Formalization.* `D5/S3/Quantum/Information/SingerQuadricQuditDistanceBound.B` (`✓ std3`).

*Citation.* M. Kulhandjian; L. Hanzo (2026). *Singer-Difference-Set Qudit Stabilizer Codes from Non-Degenerate Quadrics in PG(d,q): Construction, Structural Theorems, and Monte-Carlo Performance*. DOI: [10.48550/arXiv.2610.02392](https://doi.org/10.48550/arXiv.2610.02392). URL: <https://arxiv.org/abs/2610.02392v1>.

*Commentary.*

The X block is M_Q*A over ZMod p.

**Definition 1.6 (The stabilizer check matrix).**

$$\forall p : \mathbb{N}, [\operatorname{Fact}\left(\operatorname{Nat}.\operatorname{Prime}\left(p\right)\right)], \forall \alpha : \operatorname{GaloisField}\left(p, 3\right), \forall i : \operatorname{Fin}\left(p^{2} + p + 1\right), \forall j : \operatorname{Sum}\left(\operatorname{Fin}\left(p^{2} + p + 1\right), \operatorname{Fin}\left(p^{2} + p + 1\right)\right), \operatorname{H}\left(\alpha\right)\left(i, j\right) = \operatorname{Sum}.\operatorname{elim}\left(\operatorname{A}\left(\alpha\right)\left(i\right), \operatorname{B}\left(\alpha\right)\left(i\right), j\right)$$

*Formalization.* `D5/S3/Quantum/Information/SingerQuadricQuditDistanceBound.H` (`✓ std3`).

*Citation.* M. Kulhandjian; L. Hanzo (2026). *Singer-Difference-Set Qudit Stabilizer Codes from Non-Degenerate Quadrics in PG(d,q): Construction, Structural Theorems, and Monte-Carlo Performance*. DOI: [10.48550/arXiv.2610.02392](https://doi.org/10.48550/arXiv.2610.02392). URL: <https://arxiv.org/abs/2610.02392v1>.

*Commentary.*

Page 11, Section V: H=(H_z | H_x):=(A | M_Q A). Sum.elim concatenates the two row functions, so H has columns indexed by Fin(p^2+p+1) summed with Fin(p^2+p+1).

**Definition 1.7 (The symplectic pairing).**

$$\forall p : \mathbb{N}, \forall v : \operatorname{Prod}\left((\operatorname{Fin}\left(p^{2} + p + 1\right) \to \operatorname{ZMod}\left(p\right)), (\operatorname{Fin}\left(p^{2} + p + 1\right) \to \operatorname{ZMod}\left(p\right))\right), \forall w : \operatorname{Prod}\left((\operatorname{Fin}\left(p^{2} + p + 1\right) \to \operatorname{ZMod}\left(p\right)), (\operatorname{Fin}\left(p^{2} + p + 1\right) \to \operatorname{ZMod}\left(p\right))\right), \operatorname{symp}\left(v, w\right) = \operatorname{dotProduct}\left(v.1, w.2\right) - \operatorname{dotProduct}\left(v.2, w.1\right)$$

*Formalization.* `D5/S3/Quantum/Information/SingerQuadricQuditDistanceBound.symp` (`✓ std3`).

*Citation.* M. Kulhandjian; L. Hanzo (2026). *Singer-Difference-Set Qudit Stabilizer Codes from Non-Degenerate Quadrics in PG(d,q): Construction, Structural Theorems, and Monte-Carlo Performance*. DOI: [10.48550/arXiv.2610.02392](https://doi.org/10.48550/arXiv.2610.02392). URL: <https://arxiv.org/abs/2610.02392v1>.

*Commentary.*

The first component is the Z part, and the second the X part. The signed form is z dot x' minus x dot z'; its vanishing expresses symplectic commutation.

**Definition 1.8 (The stabilizer row space).**

$$\forall p : \mathbb{N}, [\operatorname{Fact}\left(\operatorname{Nat}.\operatorname{Prime}\left(p\right)\right)], \forall \alpha : \operatorname{GaloisField}\left(p, 3\right), \forall v : \operatorname{Prod}\left((\operatorname{Fin}\left(p^{2} + p + 1\right) \to \operatorname{ZMod}\left(p\right)), (\operatorname{Fin}\left(p^{2} + p + 1\right) \to \operatorname{ZMod}\left(p\right))\right), (v \in \operatorname{stabilizers}\left(\alpha\right)) \Leftrightarrow (\exists c : (\operatorname{Fin}\left(p^{2} + p + 1\right) \to \operatorname{ZMod}\left(p\right)), v = (\operatorname{Matrix}.\operatorname{vecMul}\left(c, \operatorname{A}\left(\alpha\right)\right), \operatorname{Matrix}.\operatorname{vecMul}\left(c, \operatorname{B}\left(\alpha\right)\right)))$$

*Formalization.* `D5/S3/Quantum/Information/SingerQuadricQuditDistanceBound.stabilizers` (`✓ std3`).

*Citation.* M. Kulhandjian; L. Hanzo (2026). *Singer-Difference-Set Qudit Stabilizer Codes from Non-Degenerate Quadrics in PG(d,q): Construction, Structural Theorems, and Monte-Carlo Performance*. DOI: [10.48550/arXiv.2610.02392](https://doi.org/10.48550/arXiv.2610.02392). URL: <https://arxiv.org/abs/2610.02392v1>.

*Commentary.*

The pairs (c*A,c*B) for all row coefficient vectors c are exactly rowspan(H), with H=(A | B).

**Definition 1.9 (The symplectic centralizer).**

$$\forall p : \mathbb{N}, [\operatorname{Fact}\left(\operatorname{Nat}.\operatorname{Prime}\left(p\right)\right)], \forall \alpha : \operatorname{GaloisField}\left(p, 3\right), \forall v : \operatorname{Prod}\left((\operatorname{Fin}\left(p^{2} + p + 1\right) \to \operatorname{ZMod}\left(p\right)), (\operatorname{Fin}\left(p^{2} + p + 1\right) \to \operatorname{ZMod}\left(p\right))\right), (v \in \operatorname{centralizer}\left(\alpha\right)) \Leftrightarrow (\forall w : \operatorname{Prod}\left((\operatorname{Fin}\left(p^{2} + p + 1\right) \to \operatorname{ZMod}\left(p\right)), (\operatorname{Fin}\left(p^{2} + p + 1\right) \to \operatorname{ZMod}\left(p\right))\right), (w \in \operatorname{stabilizers}\left(\alpha\right)) \Rightarrow (\operatorname{symp}\left(v, w\right) = 0))$$

*Formalization.* `D5/S3/Quantum/Information/SingerQuadricQuditDistanceBound.centralizer` (`✓ std3`).

*Citation.* M. Kulhandjian; L. Hanzo (2026). *Singer-Difference-Set Qudit Stabilizer Codes from Non-Degenerate Quadrics in PG(d,q): Construction, Structural Theorems, and Monte-Carlo Performance*. DOI: [10.48550/arXiv.2610.02392](https://doi.org/10.48550/arXiv.2610.02392). URL: <https://arxiv.org/abs/2610.02392v1>.

*Commentary.*

The vectors pairing to zero with every element of the stabilizer row space.

**Definition 1.10 (The Pauli weight).**

$$\forall p : \mathbb{N}, \forall v : \operatorname{Prod}\left((\operatorname{Fin}\left(p^{2} + p + 1\right) \to \operatorname{ZMod}\left(p\right)), (\operatorname{Fin}\left(p^{2} + p + 1\right) \to \operatorname{ZMod}\left(p\right))\right), \operatorname{wt}\left(v\right) = \operatorname{Finset}.\operatorname{card}\left(\operatorname{Finset}.\operatorname{filter}\left((i: \operatorname{Fin}\left(p^{2} + p + 1\right)) \mapsto (v.1\left(i\right) \ne 0) \lor (v.2\left(i\right) \ne 0), \operatorname{Finset}.\operatorname{univ}\left(\operatorname{Fin}\left(p^{2} + p + 1\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Information/SingerQuadricQuditDistanceBound.wt` (`✓ std3`).

*Citation.* M. Kulhandjian; L. Hanzo (2026). *Singer-Difference-Set Qudit Stabilizer Codes from Non-Degenerate Quadrics in PG(d,q): Construction, Structural Theorems, and Monte-Carlo Performance*. DOI: [10.48550/arXiv.2610.02392](https://doi.org/10.48550/arXiv.2610.02392). URL: <https://arxiv.org/abs/2610.02392v1>.

*Commentary.*

Weight counts positions where either component is nonzero, counting a position only once when both are nonzero.

**Definition 1.11 (Conjecture 25).**

$$(claim) \Leftrightarrow (\forall p : \mathbb{N}, (\operatorname{Nat}.\operatorname{Prime}\left(p\right)) \Rightarrow ((2 < p) \Rightarrow (\forall \alpha : \operatorname{GaloisField}\left(p, 3\right), (\operatorname{orderOf}\left(\alpha\right) = p^{3} - 1) \Rightarrow (\exists v : \operatorname{Prod}\left((\operatorname{Fin}\left(p^{2} + p + 1\right) \to \operatorname{ZMod}\left(p\right)), (\operatorname{Fin}\left(p^{2} + p + 1\right) \to \operatorname{ZMod}\left(p\right))\right), (v \in \operatorname{centralizer}\left(\alpha\right)) \land ((\neg (v \in \operatorname{stabilizers}\left(\alpha\right))) \land (\operatorname{wt}\left(v\right) \le p + 1))))))$$

*Formalization.* `D5/S3/Quantum/Information/SingerQuadricQuditDistanceBound.claim` (`✓ std3`).

*Citation.* M. Kulhandjian; L. Hanzo (2026). *Singer-Difference-Set Qudit Stabilizer Codes from Non-Degenerate Quadrics in PG(d,q): Construction, Structural Theorems, and Monte-Carlo Performance*. DOI: [10.48550/arXiv.2610.02392](https://doi.org/10.48550/arXiv.2610.02392). URL: <https://arxiv.org/abs/2610.02392v1>.

*Commentary.*

Page 19, Section VII, Conjecture 25 (Flagship distance, original): “For prime $p$ odd, $d_{\min}(\mathcal{Q}\left(p, 2\right)) \le p + 1$.”

The encoding quantifies over every prime p>2 and every alpha of multiplicative order p^3-1. It asserts a vector in the symplectic centralizer, outside rowspan(H), of Pauli weight at most p+1.

**Theorem 1.12 (The conjectured distance bound holds).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/SingerQuadricQuditDistanceBound.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* M. Kulhandjian; L. Hanzo (2026). *Singer-Difference-Set Qudit Stabilizer Codes from Non-Degenerate Quadrics in PG(d,q): Construction, Structural Theorems, and Monte-Carlo Performance*. DOI: [10.48550/arXiv.2610.02392](https://doi.org/10.48550/arXiv.2610.02392). URL: <https://arxiv.org/abs/2610.02392v1>.

*Commentary.*

Let D and Q be the trace-plane and trace-square supports. Both have size p+1, and D has nonzero difference multiplicities one. A translated reversed indicator s has A*s=1, while MQ*1=1, so (s,s) centralizes the row space. The vector (tauQ,-e_0) is in the ordinary right kernel of H. Its pairing with (s,s) is m_t-delta_t, where m_t counts (t-D) intersect Q and delta_t indicates membership in D. The moment identities sum(m_t)=(p+1)^2 and sum(m_t^2)=(p+1)^2+p^2+p contradict m_t congruent to delta_t modulo p for every t: their forced lower bound exceeds the second moment by p*(p-2)*(p+1)>0. A nonzero pairing excludes stabilizer membership. The support of (s,s) has p+1 positions.

## References

- Truth anchor: `D5/S3/Quantum/Information/SingerQuadricQuditDistanceBound.A`
- Truth anchor: `D5/S3/Quantum/Information/SingerQuadricQuditDistanceBound.B`
- Truth anchor: `D5/S3/Quantum/Information/SingerQuadricQuditDistanceBound.H`
- Truth anchor: `D5/S3/Quantum/Information/SingerQuadricQuditDistanceBound.MQ`
- Truth anchor: `D5/S3/Quantum/Information/SingerQuadricQuditDistanceBound.centralizer`
- Truth anchor: `D5/S3/Quantum/Information/SingerQuadricQuditDistanceBound.claim`
- Truth anchor: `D5/S3/Quantum/Information/SingerQuadricQuditDistanceBound.result`
- Truth anchor: `D5/S3/Quantum/Information/SingerQuadricQuditDistanceBound.stabilizers`
- Truth anchor: `D5/S3/Quantum/Information/SingerQuadricQuditDistanceBound.symp`
- Truth anchor: `D5/S3/Quantum/Information/SingerQuadricQuditDistanceBound.tauH`
- Truth anchor: `D5/S3/Quantum/Information/SingerQuadricQuditDistanceBound.tauQ`
- Truth anchor: `D5/S3/Quantum/Information/SingerQuadricQuditDistanceBound.wt`
- Dependency: [D5/S3/Geometry/FiniteGeometry/SingerTracePlane](../../Geometry/FiniteGeometry/SingerTracePlane.md)
