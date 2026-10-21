# Strength three of the Mariot–Manzoni array

## Abstract

Every three distinct columns in the binary array of mutually orthogonal bipermutive cellular automata contain each binary triple equally often.

**Definition 1.1 (The no-boundary cellular automaton).**

$$\forall b \in \mathbb{N},\; \forall f \in ((\operatorname{Fin}\left(b + 1\right)) \to \operatorname{ZMod}\left(2\right)) \to \operatorname{ZMod}\left(2\right),\; \forall x \in (\operatorname{Fin}\left(b + b\right)) \to \operatorname{ZMod}\left(2\right),\; \operatorname{ca}\left(b, f, x\right) = (\operatorname{fun} (j: \operatorname{Fin}\left(b\right)) \mapsto f\left(\operatorname{fun} (t: \operatorname{Fin}\left(b + 1\right)) \mapsto x\left(\langle \operatorname{val}\left(j\right) + \operatorname{val}\left(t\right), \operatorname{by} \operatorname{omega} \rangle\right)\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/CellularAutomata/MariotManzoniMOCAStrength.ca` (`✓ std3`).

*Citation.* Luca Mariot and Luca Manzoni (2022). *Building Correlation Immune Functions from Sets of Mutually Orthogonal Cellular Automata*. DOI: [10.48550/arXiv.2207.08280](https://doi.org/10.48550/arXiv.2207.08280). URL: <https://arxiv.org/abs/2207.08280v1>.

*Commentary.*

Definition 1, p. 6: “Let n, d ∈ ℕ with d ≤ n, and let f : F₂ᵈ → F₂ be a d-variable Boolean function. A cellular automaton of length n, diameter d and local rule f is a mapping F : F₂ⁿ → F₂ⁿ⁻ᵈ⁺¹ defined for all x ∈ F₂ⁿ as: F(x₁, · · · , xₙ) = (f(x₁, · · · , x_d), f(x₂, · · · , x_{d+1}), · · · , f(x_{n−d+1}, · · · , xₙ)).” Here n = 2b and d = b + 1; Fin indices start at zero. Addition in ZMod 2 is XOR. Each Fin constructor carries the displayed value and its arithmetic bound proof.

**Definition 1.2 (Bipermutive local rules).**

$$\forall b \in \mathbb{N},\; \forall f \in ((\operatorname{Fin}\left(b + 1\right)) \to \operatorname{ZMod}\left(2\right)) \to \operatorname{ZMod}\left(2\right),\; \operatorname{IsBipermutive}\left(b, f\right) \Leftrightarrow (\exists phi \in ((\operatorname{Fin}\left(b - 1\right)) \to \operatorname{ZMod}\left(2\right)) \to \operatorname{ZMod}\left(2\right),\; \forall y \in (\operatorname{Fin}\left(b + 1\right)) \to \operatorname{ZMod}\left(2\right),\; f\left(y\right) = y\left(\langle 0, \operatorname{by} \operatorname{omega} \rangle\right) + phi\left(\operatorname{fun} (t: \operatorname{Fin}\left(b - 1\right)) \mapsto y\left(\langle \operatorname{val}\left(t\right) + 1, \operatorname{by} \operatorname{omega} \rangle\right)\right) + y\left(\langle b, \operatorname{by} \operatorname{omega} \rangle\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/CellularAutomata/MariotManzoniMOCAStrength.IsBipermutive` (`✓ std3`).

*Citation.* Luca Mariot and Luca Manzoni (2022). *Building Correlation Immune Functions from Sets of Mutually Orthogonal Cellular Automata*. DOI: [10.48550/arXiv.2207.08280](https://doi.org/10.48550/arXiv.2207.08280). URL: <https://arxiv.org/abs/2207.08280v1>.

*Commentary.*

Page 7: “Formally, a local rule f : F₂ᵈ → F₂ is called bipermutive if it is defined as f(x₁, · · · , x_d) = x₁ ⊕ ϕ(x₂, · · · , x_{d−1}) ⊕ x_d for all x ∈ F₂ᵈ, where ϕ : F₂ᵈ⁻² → F₂ is any function of the d−2 central variables.” The parameter b is d − 1, and b − 1 is natural subtraction.

**Definition 1.3 (Orthogonality of two automata).**

$$\forall b \in \mathbb{N},\; \forall f \in ((\operatorname{Fin}\left(b + 1\right)) \to \operatorname{ZMod}\left(2\right)) \to \operatorname{ZMod}\left(2\right),\; \forall g \in ((\operatorname{Fin}\left(b + 1\right)) \to \operatorname{ZMod}\left(2\right)) \to \operatorname{ZMod}\left(2\right),\; \operatorname{AreOrthogonal}\left(b, f, g\right) \Leftrightarrow (\forall r \in (\operatorname{Fin}\left(b\right)) \to \operatorname{ZMod}\left(2\right),\; \forall c \in (\operatorname{Fin}\left(b\right)) \to \operatorname{ZMod}\left(2\right),\; \forall u \in (\operatorname{Fin}\left(b\right)) \to \operatorname{ZMod}\left(2\right),\; \forall v \in (\operatorname{Fin}\left(b\right)) \to \operatorname{ZMod}\left(2\right),\; ((r, c) \ne (u, v)) \Rightarrow ((\operatorname{ca}\left(b, f, \operatorname{Fin}.\operatorname{append}\left(r, c\right)\right), \operatorname{ca}\left(b, g, \operatorname{Fin}.\operatorname{append}\left(r, c\right)\right)) \ne (\operatorname{ca}\left(b, f, \operatorname{Fin}.\operatorname{append}\left(u, v\right)\right), \operatorname{ca}\left(b, g, \operatorname{Fin}.\operatorname{append}\left(u, v\right)\right))))$$

*Formalization.* `D5/S3/StatisticalMechanics/CellularAutomata/MariotManzoniMOCAStrength.AreOrthogonal` (`✓ std3`).

*Citation.* Luca Mariot and Luca Manzoni (2022). *Building Correlation Immune Functions from Sets of Mutually Orthogonal Cellular Automata*. DOI: [10.48550/arXiv.2207.08280](https://doi.org/10.48550/arXiv.2207.08280). URL: <https://arxiv.org/abs/2207.08280v1>.

*Commentary.*

Page 7: “we define two bipermutive CA F₁, F₂ : F₂²⁽ᵈ⁻¹⁾ → F₂ᵈ⁻¹ to be orthogonal (or equivalently they are OCA) if the corresponding Latin squares are orthogonal.” Equation (6), p. 6, requires unequal superposed pairs at distinct cells. The left half indexes rows and the right half indexes columns; Fin.append joins those halves.

**Definition 1.4 (Mutually orthogonal cellular automata).**

$$\forall b \in \mathbb{N},\; \forall k \in \mathbb{N},\; \forall f \in (\operatorname{Fin}\left(k\right)) \to ((\operatorname{Fin}\left(b + 1\right)) \to \operatorname{ZMod}\left(2\right)) \to \operatorname{ZMod}\left(2\right),\; \operatorname{IsMOCA}\left(b, k, f\right) \Leftrightarrow ((\forall i \in \operatorname{Fin}\left(k\right),\; \operatorname{IsBipermutive}\left(b, f\left(i\right)\right)) \land (\forall i \in \operatorname{Fin}\left(k\right),\; \forall h \in \operatorname{Fin}\left(k\right),\; (i \ne h) \Rightarrow (\operatorname{AreOrthogonal}\left(b, f\left(i\right), f\left(h\right)\right))))$$

*Formalization.* `D5/S3/StatisticalMechanics/CellularAutomata/MariotManzoniMOCAStrength.IsMOCA` (`✓ std3`).

*Citation.* Luca Mariot and Luca Manzoni (2022). *Building Correlation Immune Functions from Sets of Mutually Orthogonal Cellular Automata*. DOI: [10.48550/arXiv.2207.08280](https://doi.org/10.48550/arXiv.2207.08280). URL: <https://arxiv.org/abs/2207.08280v1>.

*Commentary.*

Page 7: “Accordingly, a family of k pairwise orthogonal bipermutive CA F₁, · · · , F_k will be called a set of k-MOCA (mutually orthogonal cellular automata).” The index set is Fin k.

**Definition 1.5 (The juxtaposed binary array).**

$$\forall b \in \mathbb{N},\; \forall k \in \mathbb{N},\; \forall f \in (\operatorname{Fin}\left(k\right)) \to ((\operatorname{Fin}\left(b + 1\right)) \to \operatorname{ZMod}\left(2\right)) \to \operatorname{ZMod}\left(2\right),\; \operatorname{mocaArray}\left(b, k, f\right) = (\operatorname{fun} (x: (\operatorname{Fin}\left(b + b\right)) \to \operatorname{ZMod}\left(2\right)) \mapsto \operatorname{fun} (c: \operatorname{Fin}\left(k\right) \times \operatorname{Fin}\left(b\right)) \mapsto \operatorname{ca}\left(b, f\left(c.1\right), x, c.2\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/CellularAutomata/MariotManzoniMOCAStrength.mocaArray` (`✓ std3`).

*Citation.* Luca Mariot and Luca Manzoni (2022). *Building Correlation Immune Functions from Sets of Mutually Orthogonal Cellular Automata*. DOI: [10.48550/arXiv.2207.08280](https://doi.org/10.48550/arXiv.2207.08280). URL: <https://arxiv.org/abs/2207.08280v1>.

*Commentary.*

Equation (7), p. 8: “the row of A indexed by (x, y) is equal to: A(x, y) = (F₁(x, y), F₂(x, y), · · · , F_k(x, y)).” Rows are functions Fin (b + b) → ZMod 2; columns are pairs in Fin k × Fin b. Thus there are 2^(2b) rows and kb columns.

**Definition 1.6 (Binary orthogonal arrays).**

$$\forall R \in \operatorname{Type},\; \forall C \in \operatorname{Type},\; [\operatorname{Fintype}\left(R\right)]\forall A \in (R) \to (C) \to \operatorname{ZMod}\left(2\right),\; \forall t \in \mathbb{N},\; \operatorname{IsOrthogonalArray}\left(A, t\right) \Leftrightarrow (\forall cols \in (\operatorname{Fin}\left(t\right)) \to C,\; (\operatorname{Function}.\operatorname{Injective}\left(cols\right)) \Rightarrow (\forall v \in (\operatorname{Fin}\left(t\right)) \to \operatorname{ZMod}\left(2\right),\; \operatorname{Fintype}.\operatorname{card}\left(\{ r: R // (\forall s \in \operatorname{Fin}\left(t\right),\; A\left(r, cols\left(s\right)\right) = v\left(s\right)) \}\right) = \operatorname{Nat}.\operatorname{div}\left(\operatorname{Fintype}.\operatorname{card}\left(R\right), 2^{t}\right)))$$

*Formalization.* `D5/S3/StatisticalMechanics/CellularAutomata/MariotManzoniMOCAStrength.IsOrthogonalArray` (`✓ std3`).

*Citation.* Luca Mariot and Luca Manzoni (2022). *Building Correlation Immune Functions from Sets of Mutually Orthogonal Cellular Automata*. DOI: [10.48550/arXiv.2207.08280](https://doi.org/10.48550/arXiv.2207.08280). URL: <https://arxiv.org/abs/2207.08280v1>.

*Commentary.*

Page 6: “is a N × n array with entries from a set S with s elements such that, for any N × t subarray, each t-uple of Sᵗ occurs exactly λ = N/sᵗ times”. Here s = 2. An injective map selects t distinct columns; Fintype.card counts the rows of each pattern fiber. Nat.div denotes natural integer division. If there are fewer than t columns, there is no such selection.

**Definition 1.7 (The strength question).**

$$\operatorname{claim} \Leftrightarrow (\forall b \in \mathbb{N},\; \forall k \in \mathbb{N},\; \forall f \in (\operatorname{Fin}\left(k\right)) \to ((\operatorname{Fin}\left(b + 1\right)) \to \operatorname{ZMod}\left(2\right)) \to \operatorname{ZMod}\left(2\right),\; (\operatorname{IsMOCA}\left(b, k, f\right)) \Rightarrow (\operatorname{IsOrthogonalArray}\left(\operatorname{mocaArray}\left(b, k, f\right), 3\right)))$$

*Formalization.* `D5/S3/StatisticalMechanics/CellularAutomata/MariotManzoniMOCAStrength.claim` (`✓ std3`).

*Citation.* Luca Mariot and Luca Manzoni (2022). *Building Correlation Immune Functions from Sets of Mutually Orthogonal Cellular Automata*. DOI: [10.48550/arXiv.2207.08280](https://doi.org/10.48550/arXiv.2207.08280). URL: <https://arxiv.org/abs/2207.08280v1>.

*Commentary.*

Section 5, p. 12: “The most natural open question remains whether our Theorem 1 is really a tight lower bound on the correlation immunity of the Boolean functions constructed through k-MOCA. If further experiments show that the lowest correlation immunity order is always at least 3, then it would be interesting to try refining Lemma 3, and prove that the binary OA obtained from a set of k-MOCA has always at least strength 3.” The proposition quantifies over every b, k and family of local rules, and asserts strength three for the array in Equation (7).

**Theorem 1.8 (Every MOCA array has strength three).**

$$\forall b \in \mathbb{N},\; \forall k \in \mathbb{N},\; \forall f \in (\operatorname{Fin}\left(k\right)) \to ((\operatorname{Fin}\left(b + 1\right)) \to \operatorname{ZMod}\left(2\right)) \to \operatorname{ZMod}\left(2\right),\; (\operatorname{IsMOCA}\left(b, k, f\right)) \Rightarrow (\operatorname{IsOrthogonalArray}\left(\operatorname{mocaArray}\left(b, k, f\right), 3\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/CellularAutomata/MariotManzoniMOCAStrength.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Luca Mariot and Luca Manzoni (2022). *Building Correlation Immune Functions from Sets of Mutually Orthogonal Cellular Automata*. DOI: [10.48550/arXiv.2207.08280](https://doi.org/10.48550/arXiv.2207.08280). URL: <https://arxiv.org/abs/2207.08280v1>.

*Commentary.*

Flip one input bit. A single column changes under its left endpoint flip. For three columns ordered by starting position, use the first left endpoint when the first two starts differ, the last right endpoint when only the last start differs, and the common left endpoint when all starts coincide. These flips reverse the triple XOR, even when columns repeat, without requiring orthogonality. For two distinct columns with different starts, the earlier left endpoint suffices. At equal starts, orthogonality makes the pair of complete output vectors a bijection, so summation can be reindexed and one output bit flipped. The seven nonconstant integer character sums of a three-column array therefore vanish. Expanding the three-bit indicator gives eight times each fiber cardinality equal to the number of rows, which yields the asserted natural quotient. The theorem asserts strength three; sharpness and the corresponding Boolean-function statement are outside its conclusion.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/MariotManzoniMOCAStrength.AreOrthogonal`
- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/MariotManzoniMOCAStrength.IsBipermutive`
- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/MariotManzoniMOCAStrength.IsMOCA`
- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/MariotManzoniMOCAStrength.IsOrthogonalArray`
- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/MariotManzoniMOCAStrength.ca`
- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/MariotManzoniMOCAStrength.claim`
- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/MariotManzoniMOCAStrength.mocaArray`
- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/MariotManzoniMOCAStrength.result`
