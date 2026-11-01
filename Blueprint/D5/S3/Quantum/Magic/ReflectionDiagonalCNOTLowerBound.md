# The worst-case CNOT lower bound for reflection symmetry

## Abstract

Every positive even number of wires admits a reflection-symmetric diagonal unitary forcing the exponential CNOT lower bound.

**Definition 1.1 (Ancilla-free CNOT and real z rotations).**

$$\forall \left(m: \mathbb{N}\right), \operatorname{gate}\left(m\right) = \operatorname{Sum}\left(\operatorname{Subtype}\left(\left(\lambda \left(p: \left(\operatorname{Fin}\left(m\right)\right) \times \left(\operatorname{Fin}\left(m\right)\right)\right) \mapsto \left(\operatorname{Prod.fst}\left(p\right) \ne \operatorname{Prod.snd}\left(p\right)\right)\right)\right), \left(\operatorname{Fin}\left(m\right)\right) \times \left(\mathbb{R}\right)\right)$$

*Formalization.* `D5/S3/Quantum/Magic/ReflectionDiagonalCNOTLowerBound.gate` (`✓ std3`).

*Citation.* Xinchi Huang, Taichi Kosugi, Hirofumi Nishi and Yu-ichiro Matsushita (2024). *Optimized Synthesis of Circuits for Diagonal Unitary Matrices with Reflection Symmetry*. DOI: [10.7566/JPSJ.93.054002](https://doi.org/10.7566/JPSJ.93.054002). URL: <https://arxiv.org/abs/2310.06676v2>.

*Commentary.*

A gate is either an ordered pair of distinct target and control wires, or a wire together with a real rotation angle. The two alternatives form a disjoint sum. All wire indices belong to Fin m, so there are no ancillary wires. This is the gate set in main_arXiv2.tex, lines 170 and 194; the absence of ancillas is also stated at line 1225.

**Definition 1.2 (The complex matrix of a gate).**

$$\forall \left(m: \mathbb{N}\right), \left(\forall \left(p: \operatorname{Subtype}\left(\left(\lambda \left(p: \left(\operatorname{Fin}\left(m\right)\right) \times \left(\operatorname{Fin}\left(m\right)\right)\right) \mapsto \left(\operatorname{Prod.fst}\left(p\right) \ne \operatorname{Prod.snd}\left(p\right)\right)\right)\right)\right), \operatorname{gateMatrix}\left(\operatorname{Sum.inl}\left(p\right)\right) = \operatorname{Matrix.submatrix}\left(\left(1: \operatorname{Matrix}\left(\operatorname{Qubits}\left(m\right), \operatorname{Qubits}\left(m\right), \mathbb{C}\right)\right), \operatorname{id}, \left(\lambda \left(y: \operatorname{Qubits}\left(m\right)\right) \mapsto \left(\operatorname{Function.update}\left(y, \operatorname{Prod.fst}\left(\operatorname{Subtype.val}\left(p\right)\right), \operatorname{Bool.xor}\left(y\left(\operatorname{Prod.fst}\left(\operatorname{Subtype.val}\left(p\right)\right)\right), y\left(\operatorname{Prod.snd}\left(\operatorname{Subtype.val}\left(p\right)\right)\right)\right)\right)\right)\right)\right)\right) \land \left(\forall \left(p: \left(\operatorname{Fin}\left(m\right)\right) \times \left(\mathbb{R}\right)\right), \operatorname{gateMatrix}\left(\operatorname{Sum.inr}\left(p\right)\right) = \operatorname{Matrix.diagonal}\left(\left(\lambda \left(x: \operatorname{Qubits}\left(m\right)\right) \mapsto \left(\operatorname{ite}\left(x\left(\operatorname{Prod.fst}\left(p\right)\right) = \operatorname{Bool.false}, \operatorname{Complex.exp}\left(\left(\operatorname{Complex.ofReal}\left(\left(\frac{-\operatorname{Prod.snd}\left(p\right)}{\left(2: \mathbb{R}\right)}: \mathbb{R}\right)\right)\right) \cdot \left(\operatorname{Complex.I}\right)\right), \operatorname{Complex.exp}\left(\left(\operatorname{Complex.ofReal}\left(\left(\frac{\operatorname{Prod.snd}\left(p\right)}{\left(2: \mathbb{R}\right)}: \mathbb{R}\right)\right)\right) \cdot \left(\operatorname{Complex.I}\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Magic/ReflectionDiagonalCNOTLowerBound.gateMatrix` (`✓ std3`).

*Citation.* Xinchi Huang, Taichi Kosugi, Hirofumi Nishi and Yu-ichiro Matsushita (2024). *Optimized Synthesis of Circuits for Diagonal Unitary Matrices with Reflection Symmetry*. DOI: [10.7566/JPSJ.93.054002](https://doi.org/10.7566/JPSJ.93.054002). URL: <https://arxiv.org/abs/2310.06676v2>.

*Commentary.*

Qubits m denotes the Boolean functions on Fin m, as in D5.S3.Quantum.Entanglement.RandomizedGraphNegativityRefutation.Qubits. Sum.elim selects the CNOT or rotation matrix from the gate's disjoint-sum tag. The CNOT matrix reindexes the columns of the identity by replacing the target bit with its exclusive-or with the control bit. Subtype.val explicitly extracts the ordered wire pair. The rotation matrix is diagonal: a false bit receives the exponential of minus half the angle times the imaginary unit, and a true bit receives the positive half-angle exponential. Complex.ofReal explicitly includes each real half-angle into the complex numbers. These are the CNOT and z-rotation gates used by the source's circuit model at lines 170 and 194.

**Definition 1.3 (The ordered product of gate matrices).**

$$\forall \left(m: \mathbb{N}\right), \forall \left(circuit: \operatorname{List}\left(\operatorname{gate}\left(m\right)\right)\right), \operatorname{circuitMatrix}\left(circuit\right) = \operatorname{List.foldr}\left(\left(\lambda \left(g: \operatorname{gate}\left(m\right)\right) \mapsto \left(\left(\lambda \left(acc: \operatorname{Matrix}\left(\operatorname{Qubits}\left(m\right), \operatorname{Qubits}\left(m\right), \mathbb{C}\right)\right) \mapsto \left(\left(\operatorname{gateMatrix}\left(g\right)\right) \cdot \left(acc\right)\right)\right)\right)\right), \left(1: \operatorname{Matrix}\left(\operatorname{Qubits}\left(m\right), \operatorname{Qubits}\left(m\right), \mathbb{C}\right)\right), circuit\right)$$

*Formalization.* `D5/S3/Quantum/Magic/ReflectionDiagonalCNOTLowerBound.circuitMatrix` (`✓ std3`).

*Citation.* Xinchi Huang, Taichi Kosugi, Hirofumi Nishi and Yu-ichiro Matsushita (2024). *Optimized Synthesis of Circuits for Diagonal Unitary Matrices with Reflection Symmetry*. DOI: [10.7566/JPSJ.93.054002](https://doi.org/10.7566/JPSJ.93.054002). URL: <https://arxiv.org/abs/2310.06676v2>.

*Commentary.*

The matrix of a finite circuit is the right fold of its gate matrices under multiplication, starting from the identity. Thus the first list entry is the leftmost matrix factor, and the empty circuit has the identity matrix. This expresses the finite circuits over the source's gate set, with realization up to a global phase as at lines 429–445.

**Definition 1.4 (Counting only CNOT gates).**

$$\forall \left(m: \mathbb{N}\right), \forall \left(circuit: \operatorname{List}\left(\operatorname{gate}\left(m\right)\right)\right), \operatorname{cnotCount}\left(circuit\right) = \operatorname{List.length}\left(\operatorname{List.filter}\left(\left(\lambda \left(g: \operatorname{gate}\left(m\right)\right) \mapsto \left(\operatorname{Sum.elim}\left(\operatorname{Function.const}\left(\operatorname{Subtype}\left(\left(\lambda \left(p: \left(\operatorname{Fin}\left(m\right)\right) \times \left(\operatorname{Fin}\left(m\right)\right)\right) \mapsto \left(\operatorname{Prod.fst}\left(p\right) \ne \operatorname{Prod.snd}\left(p\right)\right)\right)\right), \operatorname{Bool.true}\right), \operatorname{Function.const}\left(\left(\operatorname{Fin}\left(m\right)\right) \times \left(\mathbb{R}\right), \operatorname{Bool.false}\right), g\right)\right)\right), circuit\right)\right)$$

*Formalization.* `D5/S3/Quantum/Magic/ReflectionDiagonalCNOTLowerBound.cnotCount` (`✓ std3`).

*Citation.* Xinchi Huang, Taichi Kosugi, Hirofumi Nishi and Yu-ichiro Matsushita (2024). *Optimized Synthesis of Circuits for Diagonal Unitary Matrices with Reflection Symmetry*. DOI: [10.7566/JPSJ.93.054002](https://doi.org/10.7566/JPSJ.93.054002). URL: <https://arxiv.org/abs/2310.06676v2>.

*Commentary.*

Filter the circuit with Sum.elim on its disjoint-sum tag and take the length of the retained list. The predicate is constantly true on CNOT pairs and constantly false on rotations; Function.const displays both constant branches. This is the CNOT gate count used at lines 229 and 434, independently of the number of rotations.

**Definition 1.5 (A hard reflection-symmetric phase function in every even dimension).**

$$\operatorname{claim} = \left(\forall \left(n: \mathbb{N}\right), \left(1 \le n\right) \Rightarrow \left(\exists \left(\theta: \operatorname{Qubits}\left(\left(2\right) \cdot \left(n\right)\right) \to \mathbb{R}\right), \left(\forall \left(x: \operatorname{Qubits}\left(\left(2\right) \cdot \left(n\right)\right)\right), \theta\left(\left(\lambda \left(j: \operatorname{Fin}\left(\left(2\right) \cdot \left(n\right)\right)\right) \mapsto \left(\operatorname{Bool.not}\left(x\left(j\right)\right)\right)\right)\right) = \theta\left(x\right)\right) \land \left(\forall \left(circuit: \operatorname{List}\left(\operatorname{gate}\left(\left(2\right) \cdot \left(n\right)\right)\right)\right), \forall \left(c: \mathbb{C}\right), \left(\operatorname{circuitMatrix}\left(circuit\right) = \operatorname{HSMul.hSMul}\left(c, \operatorname{Matrix.diagonal}\left(\left(\lambda \left(x: \operatorname{Qubits}\left(\left(2\right) \cdot \left(n\right)\right)\right) \mapsto \left(\operatorname{Complex.exp}\left(\left(\operatorname{Complex.ofReal}\left(\left(\theta\left(x\right): \mathbb{R}\right)\right)\right) \cdot \left(\operatorname{Complex.I}\right)\right)\right)\right)\right)\right)\right) \Rightarrow \left(2^{\left(2\right) \cdot \left(n\right) - 1} + \left(2\right) \cdot \left(n\right) - 2 \le \operatorname{cnotCount}\left(circuit\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Magic/ReflectionDiagonalCNOTLowerBound.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Xinchi Huang, Taichi Kosugi, Hirofumi Nishi and Yu-ichiro Matsushita (2024). *Optimized Synthesis of Circuits for Diagonal Unitary Matrices with Reflection Symmetry*. DOI: [10.7566/JPSJ.93.054002](https://doi.org/10.7566/JPSJ.93.054002). URL: <https://arxiv.org/abs/2310.06676v2>.

*Commentary.*

For every positive natural n, there is a real phase function on twice n Boolean wires that is unchanged by complementing every bit. Every circuit whose matrix is a complex scalar multiple of its diagonal exponential has the stated natural-number CNOT lower bound. The scalar c is arbitrary in the statement; the matrix equality itself will force it to be nonzero. This gives the worst-case lower-bound reading of the conjecture at main_arXiv2.tex, line 847, for the symmetry defined at lines 207–227 and the global-phase convention at lines 429–445. The matching upper bound supplied by Algorithm 1 at lines 229 and 434 is separate from this assertion.

**Theorem 1.6 (The reflection-symmetric CNOT lower bound).**

$$\forall \left(n: \mathbb{N}\right), \left(1 \le n\right) \Rightarrow \left(\exists \left(\theta: \operatorname{Qubits}\left(\left(2\right) \cdot \left(n\right)\right) \to \mathbb{R}\right), \left(\forall \left(x: \operatorname{Qubits}\left(\left(2\right) \cdot \left(n\right)\right)\right), \theta\left(\left(\lambda \left(j: \operatorname{Fin}\left(\left(2\right) \cdot \left(n\right)\right)\right) \mapsto \left(\operatorname{Bool.not}\left(x\left(j\right)\right)\right)\right)\right) = \theta\left(x\right)\right) \land \left(\forall \left(circuit: \operatorname{List}\left(\operatorname{gate}\left(\left(2\right) \cdot \left(n\right)\right)\right)\right), \forall \left(c: \mathbb{C}\right), \left(\operatorname{circuitMatrix}\left(circuit\right) = \operatorname{HSMul.hSMul}\left(c, \operatorname{Matrix.diagonal}\left(\left(\lambda \left(x: \operatorname{Qubits}\left(\left(2\right) \cdot \left(n\right)\right)\right) \mapsto \left(\operatorname{Complex.exp}\left(\left(\operatorname{Complex.ofReal}\left(\left(\theta\left(x\right): \mathbb{R}\right)\right)\right) \cdot \left(\operatorname{Complex.I}\right)\right)\right)\right)\right)\right)\right) \Rightarrow \left(2^{\left(2\right) \cdot \left(n\right) - 1} + \left(2\right) \cdot \left(n\right) - 2 \le \operatorname{cnotCount}\left(circuit\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/ReflectionDiagonalCNOTLowerBound.result` (`✓ std3`). ∎

*Resolves.* `Problems/huang-kosugi-nishi-matsushita-2024-reflection-diagonal-cnot-lower-bound` (proved) by `D5/S3/Quantum/Magic/ReflectionDiagonalCNOTLowerBound.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"huang-kosugi-nishi-matsushita-2024-reflection-diagonal-cnot-lower-bound","declaration_gid":"D5/S3/Quantum/Magic/ReflectionDiagonalCNOTLowerBound.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Xinchi Huang, Taichi Kosugi, Hirofumi Nishi and Yu-ichiro Matsushita (2024). *Optimized Synthesis of Circuits for Diagonal Unitary Matrices with Reflection Symmetry*. DOI: [10.7566/JPSJ.93.054002](https://doi.org/10.7566/JPSJ.93.054002). URL: <https://arxiv.org/abs/2310.06676v2>.

*Commentary.*

Fix n at least one and put m equal to twice n. Choose the phase to be pi divided by two at the all-false and all-true inputs and zero elsewhere. The two inputs are distinct because m is positive. Complementing every bit exchanges them and preserves the remaining inputs, so the phase has reflection symmetry. Its diagonal exponential is the imaginary unit at those two inputs and one elsewhere.

Track a Boolean row vector on each wire, starting with the rows of the identity matrix. A CNOT replaces its target row by the sum of its target and control rows; a rotation leaves all rows unchanged. Boolean addition is exclusive-or. Evaluating the rows on an input commutes with a CNOT update. The corresponding bit toggle is an involution when target and control differ, so these updates preserve bijectivity of the linear map. An induction over the gate list expresses each matrix row as a nonzero product of rotation factors at the column selected by the final linear map, with all other entries zero. If the circuit matrix is diagonal, that selected column must be the original input. Equality of the linear maps on every input then makes the final row matrix the identity.

For a Boolean vector v and a nowhere-zero complex function f, form a multiplicative invariant by multiplying f(x) when the Boolean dot product of v and x is false and multiplying its inverse when that dot product is true. The invariant is multiplicative in f. If a translation by u preserves f and has dot product true with v, pair each x with x plus u: the two exponents are opposite and their factors cancel. For nonzero v a coordinate vector supplies such a translation for every nonzero constant function, so a global scalar contributes one. For distinct nonzero vectors v and w, one coordinate vector or a sum of two coordinate vectors has dot product true with v and false with w. Consequently every nowhere-zero factor depending only on the dot product with w also contributes one.

Induct over the circuit again. Bijectivity ensures that every current wire row is nonzero. If a fixed nonzero v never occurs on a rotated wire, the preceding cancellation applies to each rotation factor, and the invariant of their product is one. For an even Boolean vector v, however, its dot products with the all-false and all-true inputs are both false. On the chosen diagonal the invariant is therefore the product of two imaginary units, namely minus one; every other input contributes one. The diagonal equality and the final identity row matrix identify the product of rotation factors with c times this diagonal function. Nonvanishing at any input forces c to be nonzero. Multiplicativity and cancellation of c contradict the value one whenever a nonzero even v is absent. Thus every nonzero even vector occurs on a rotated wire.

Remove the rotations from the list, retaining the ordered CNOT pairs. This preserves the final row matrix and makes the length of the remaining list equal to the CNOT count. Induction shows that a row used by a rotation is either an initial row or an earlier CNOT output. Every initial identity row is odd, so each required nonzero even vector must occur as a CNOT output. The final identity rows are odd as well. Apply D5.S3.Quantum.Magic.ReflectionDiagonalParityCounting.count_bound to this list and the initial identity rows: the required even outputs number half of all Boolean vectors less one, and at least m minus one further updates are needed to restore odd rows. Substitution of m equal to twice n into that bound proves the assertion.

## References

- Truth anchor: `D5/S3/Quantum/Magic/ReflectionDiagonalCNOTLowerBound.circuitMatrix`
- Truth anchor: `D5/S3/Quantum/Magic/ReflectionDiagonalCNOTLowerBound.claim`
- Truth anchor: `D5/S3/Quantum/Magic/ReflectionDiagonalCNOTLowerBound.cnotCount`
- Truth anchor: `D5/S3/Quantum/Magic/ReflectionDiagonalCNOTLowerBound.gate`
- Truth anchor: `D5/S3/Quantum/Magic/ReflectionDiagonalCNOTLowerBound.gateMatrix`
- Truth anchor: `D5/S3/Quantum/Magic/ReflectionDiagonalCNOTLowerBound.result`
- Dependency: [D5/S3/Quantum/Entanglement/RandomizedGraphNegativityRefutation](../Entanglement/RandomizedGraphNegativityRefutation.md)
- Dependency: [D5/S3/Quantum/Magic/ReflectionDiagonalParityCounting](ReflectionDiagonalParityCounting.md)
