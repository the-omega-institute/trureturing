# Entropy constancy on quantum correlation lines fails

## Abstract

The entropy minimum under an exact mean energy constraint is not constant on fixed-difference correlation lines.

**Definition 1.1 (The minimum state overlap).**

$$\forall (e: \mathbb{R}), (\operatorname{gamma}\left(e\right) = \operatorname{if} (e < \frac{\operatorname{Real}.\operatorname{pi}}{2}) \operatorname{then} \operatorname{Real}.\operatorname{cos}\left(e\right) \operatorname{else} 0)$$

*Formalization.* `D5/S3/Quantum/JonesAloyEntropyConstancy.gamma` (`✓ std3`).

*Citation.* Caroline L. Jones; Albert Aloy; Gerard Higgins; Markus P. Müller (2026). *Certified randomness from quantum speed limits*. DOI: [10.1103/bnrq-sp5w](https://doi.org/10.1103/bnrq-sp5w). URL: <https://arxiv.org/abs/2506.14526v3>.

*Commentary.*

Equation (9), p. 4, defines the smallest possible overlap by the cosine below pi/2 and zero otherwise, in units with time separation and Planck's constant equal to one. Energy labels range over all nonnegative real numbers.

**Definition 1.2 (The correlation overlap expression).**

$$\forall (C: \mathbb{R}\times\mathbb{R}), (\operatorname{fidelityExpression}\left(C\right) = \frac{\operatorname{Real}.\operatorname{sqrt}\left(1 + C.1\right) \cdot \operatorname{Real}.\operatorname{sqrt}\left(1 + C.2\right) + \operatorname{Real}.\operatorname{sqrt}\left(1 - C.1\right) \cdot \operatorname{Real}.\operatorname{sqrt}\left(1 - C.2\right)}{2})$$

*Formalization.* `D5/S3/Quantum/JonesAloyEntropyConstancy.fidelityExpression` (`✓ std3`).

*Citation.* Caroline L. Jones; Albert Aloy; Gerard Higgins; Markus P. Müller (2026). *Certified randomness from quantum speed limits*. DOI: [10.1103/bnrq-sp5w](https://doi.org/10.1103/bnrq-sp5w). URL: <https://arxiv.org/abs/2506.14526v3>.

*Commentary.*

Equation (8), p. 4, gives one half of the sum of the two products of square roots. Each square root is taken separately.

**Definition 1.3 (The quantum correlation domain).**

$$\forall (e: \mathbb{R}), (\operatorname{quantumSet}\left(e\right) = \{C:\mathbb{R}\times\mathbb{R} | (-(1) \le C.1) \land ((C.1 \le 1) \land ((-(1) \le C.2) \land ((C.2 \le 1) \land (\operatorname{gamma}\left(e\right) \le \operatorname{fidelityExpression}\left(C\right)))))\})$$

*Formalization.* `D5/S3/Quantum/JonesAloyEntropyConstancy.quantumSet` (`✓ std3`).

*Citation.* Caroline L. Jones; Albert Aloy; Gerard Higgins; Markus P. Müller (2026). *Certified randomness from quantum speed limits*. DOI: [10.1103/bnrq-sp5w](https://doi.org/10.1103/bnrq-sp5w). URL: <https://arxiv.org/abs/2506.14526v3>.

*Commentary.*

Equations (7)–(9), p. 4, characterize the correlations by the overlap inequality inside the square [-1,1] squared. The displayed set uses that characterization.

**Definition 1.4 (The entropy of a correlation pair).**

$$\forall (C: \mathbb{R}\times\mathbb{R}), (\operatorname{entropy}\left(C\right) = \frac{\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{CloningMachine}.\operatorname{binaryEntropyBits}\left(\frac{1 + C.1}{2}\right) + \operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{CloningMachine}.\operatorname{binaryEntropyBits}\left(\frac{1 + C.2}{2}\right)}{2})$$

*Formalization.* `D5/S3/Quantum/JonesAloyEntropyConstancy.entropy` (`✓ std3`).

*Citation.* Caroline L. Jones; Albert Aloy; Gerard Higgins; Markus P. Müller (2026). *Certified randomness from quantum speed limits*. DOI: [10.1103/bnrq-sp5w](https://doi.org/10.1103/bnrq-sp5w). URL: <https://arxiv.org/abs/2506.14526v3>.

*Commentary.*

Equation (27), p. 14: “Here we assume p(x)=1/2 for both x, i.e. there is equal a priori probability for both inputs.” The displayed expression uses CloningMachine.binaryEntropyBits at (1+C.1)/2 and (1+C.2)/2, including its endpoint values.

**Definition 1.5 (Finite hidden-variable ensembles).**

$$\forall (n: \mathbb{N}), (\forall (A: \operatorname{Ensemble}\left(n\right)), (A.\operatorname{weight}:\operatorname{Fin}\left(n\right) \to \mathbb{R}; A.\operatorname{corr}:\operatorname{Fin}\left(n\right) \to (\mathbb{R}\times\mathbb{R}); A.\operatorname{energy}:\operatorname{Fin}\left(n\right) \to \mathbb{R}))$$

*Formalization.* `D5/S3/Quantum/JonesAloyEntropyConstancy.Ensemble` (`✓ std3`).

*Citation.* Caroline L. Jones; Albert Aloy; Gerard Higgins; Markus P. Müller (2026). *Certified randomness from quantum speed limits*. DOI: [10.1103/bnrq-sp5w](https://doi.org/10.1103/bnrq-sp5w). URL: <https://arxiv.org/abs/2506.14526v3>.

*Commentary.*

The source describes the ensemble {p(lambda),(C^lambda,E^lambda)}. An Ensemble n stores its real weights, correlation pairs and real energy labels at indices in Fin n. The optimization ranges over every natural number n.

**Definition 1.6 (The exact optimization constraints).**

$$\forall (n: \mathbb{N}), (\forall (A: \operatorname{Ensemble}\left(n\right)), (\forall (C: \mathbb{R}\times\mathbb{R}), (\forall (E: \mathbb{R}), ((\operatorname{Feasible}\left(A, C, E\right)) \Leftrightarrow ((\forall (i: \operatorname{Fin}\left(n\right)), (0 \le A.\operatorname{weight}\left(i\right))) \land ((\sum_{i:\operatorname{Fin}\left(n\right)} (A.\operatorname{weight}\left(i\right)) = 1) \land ((\forall (i: \operatorname{Fin}\left(n\right)), (0 \le A.\operatorname{energy}\left(i\right))) \land ((\forall (i: \operatorname{Fin}\left(n\right)), (A.\operatorname{corr}\left(i\right) \in \operatorname{quantumSet}\left(A.\operatorname{energy}\left(i\right)\right))) \land ((\sum_{i:\operatorname{Fin}\left(n\right)} (A.\operatorname{weight}\left(i\right) \cdot (A.\operatorname{corr}\left(i\right)).1) = C.1) \land ((\sum_{i:\operatorname{Fin}\left(n\right)} (A.\operatorname{weight}\left(i\right) \cdot (A.\operatorname{corr}\left(i\right)).2) = C.2) \land (\sum_{i:\operatorname{Fin}\left(n\right)} (A.\operatorname{weight}\left(i\right) \cdot A.\operatorname{energy}\left(i\right)) = E)))))))))))$$

*Formalization.* `D5/S3/Quantum/JonesAloyEntropyConstancy.Feasible` (`✓ std3`).

*Citation.* Caroline L. Jones; Albert Aloy; Gerard Higgins; Markus P. Müller (2026). *Certified randomness from quantum speed limits*. DOI: [10.1103/bnrq-sp5w](https://doi.org/10.1103/bnrq-sp5w). URL: <https://arxiv.org/abs/2506.14526v3>.

*Commentary.*

Equation (27), p. 14, imposes the two correlation means, the exact mean energy and quantum-domain membership of every component. Probability weights are nonnegative and sum to one; energy labels are nonnegative without a componentwise upper bound.

**Definition 1.7 (The attainable entropy values).**

$$\forall (C: \mathbb{R}\times\mathbb{R}), (\forall (E: \mathbb{R}), (\operatorname{entropyValues}\left(C, E\right) = \{z:\mathbb{R} | \exists (n: \mathbb{N}), (\exists (A: \operatorname{Ensemble}\left(n\right)), ((\operatorname{Feasible}\left(A, C, E\right)) \land (z = \sum_{i:\operatorname{Fin}\left(n\right)} (A.\operatorname{weight}\left(i\right) \cdot \operatorname{entropy}\left(A.\operatorname{corr}\left(i\right)\right)))))\}))$$

*Formalization.* `D5/S3/Quantum/JonesAloyEntropyConstancy.entropyValues` (`✓ std3`).

*Citation.* Caroline L. Jones; Albert Aloy; Gerard Higgins; Markus P. Müller (2026). *Certified randomness from quantum speed limits*. DOI: [10.1103/bnrq-sp5w](https://doi.org/10.1103/bnrq-sp5w). URL: <https://arxiv.org/abs/2506.14526v3>.

*Commentary.*

Equation (27), p. 14, minimizes the weighted sum of branch entropies over hidden-variable decompositions. This set collects those sums over every finite size, with all constraints retained.

**Definition 1.8 (The attained-minimum specification).**

$$\forall (HStar: (\mathbb{R}\times\mathbb{R}) \to \mathbb{R} \to \mathbb{R}), ((\operatorname{IsSourceRoof}\left(HStar\right)) \Leftrightarrow (\forall (E: \mathbb{R}), ((0 \le E) \Rightarrow (\forall (C: \mathbb{R}\times\mathbb{R}), ((C \in \operatorname{quantumSet}\left(E\right)) \Rightarrow (\operatorname{IsLeast}\left(\operatorname{entropyValues}\left(C, E\right), HStar\left(C, E\right)\right)))))))$$

*Formalization.* `D5/S3/Quantum/JonesAloyEntropyConstancy.IsSourceRoof` (`✓ std3`).

*Citation.* Caroline L. Jones; Albert Aloy; Gerard Higgins; Markus P. Müller (2026). *Certified randomness from quantum speed limits*. DOI: [10.1103/bnrq-sp5w](https://doi.org/10.1103/bnrq-sp5w). URL: <https://arxiv.org/abs/2506.14526v3>.

*Commentary.*

The minimum in Equation (27), p. 14, is expressed by IsLeast on the attainable values, at every nonnegative energy and every correlation in its domain. It specifies attainment as well as the lower-bound property.

**Definition 1.9 (The line-constancy conjecture).**

$$(claim) \Leftrightarrow ((\exists (HStar: (\mathbb{R}\times\mathbb{R}) \to \mathbb{R} \to \mathbb{R}), (\operatorname{IsSourceRoof}\left(HStar\right))) \land (\forall (HStar: (\mathbb{R}\times\mathbb{R}) \to \mathbb{R} \to \mathbb{R}), ((\operatorname{IsSourceRoof}\left(HStar\right)) \Rightarrow (\forall (E: \mathbb{R}), ((0 \le E) \Rightarrow ((E \le \frac{\operatorname{Real}.\operatorname{pi}}{2}) \Rightarrow (\forall (C: \mathbb{R}\times\mathbb{R}), ((C \in \operatorname{quantumSet}\left(E\right)) \Rightarrow (HStar\left(C, E\right) = HStar\left((\frac{C.1 - C.2}{2}, \frac{-(C.1 - C.2)}{2}), E\right))))))))))$$

*Formalization.* `D5/S3/Quantum/JonesAloyEntropyConstancy.claim` (`✓ std3`).

*Citation.* Caroline L. Jones; Albert Aloy; Gerard Higgins; Markus P. Müller (2026). *Certified randomness from quantum speed limits*. DOI: [10.1103/bnrq-sp5w](https://doi.org/10.1103/bnrq-sp5w). URL: <https://arxiv.org/abs/2506.14526v3>.

*Commentary.*

Appendix E(ii), p. 16, after Lemma 3: “Indeed, we conjecture – and the numerics suggest – that H⋆ is constant on those lines, i.e. that we have equality in Lemma 3. However, we have not managed to prove this.” The coordinates are the two real components of C. The center of its fixed-difference line is ((C.1-C.2)/2,-(C.1-C.2)/2). The statement includes existence of a function attaining every minimum, then asks every such function to have equal values at C and its center for energies in [0,pi/2].

**Theorem 1.10 (Refutation of line constancy).**

$$\neg((\exists (HStar: (\mathbb{R}\times\mathbb{R}) \to \mathbb{R} \to \mathbb{R}), (\operatorname{IsSourceRoof}\left(HStar\right))) \land (\forall (HStar: (\mathbb{R}\times\mathbb{R}) \to \mathbb{R} \to \mathbb{R}), ((\operatorname{IsSourceRoof}\left(HStar\right)) \Rightarrow (\forall (E: \mathbb{R}), ((0 \le E) \Rightarrow ((E \le \frac{\operatorname{Real}.\operatorname{pi}}{2}) \Rightarrow (\forall (C: \mathbb{R}\times\mathbb{R}), ((C \in \operatorname{quantumSet}\left(E\right)) \Rightarrow (HStar\left(C, E\right) = HStar\left((\frac{C.1 - C.2}{2}, \frac{-(C.1 - C.2)}{2}), E\right))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/JonesAloyEntropyConstancy.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Caroline L. Jones; Albert Aloy; Gerard Higgins; Markus P. Müller (2026). *Certified randomness from quantum speed limits*. DOI: [10.1103/bnrq-sp5w](https://doi.org/10.1103/bnrq-sp5w). URL: <https://arxiv.org/abs/2506.14526v3>.

*Commentary.*

For every 24/25 <= s < 1 and every function HStar satisfying IsSourceRoof, its value at (s squared,-s squared) and energy Real.arcsin(s), plus 7((1-s)/2) squared, is strictly smaller than its value at (1,1-2s squared) at the same energy. An extremal first coordinate forces every positive-weight branch onto the boundary. A strict supporting tangent and the exact energy mean then force all these branches to have the same correlation. At the midpoint, the correlations (s,-s), (1,1) and (-1,-1) with weights s, (1-s)/2 and (1-s)/2 give a cheaper ensemble. Taking s=24/25 contradicts the displayed conjecture. Global existence of the minimum function, persistence into the interior and operator realizations are not proved here.

## References

- Truth anchor: `D5/S3/Quantum/JonesAloyEntropyConstancy.Ensemble`
- Truth anchor: `D5/S3/Quantum/JonesAloyEntropyConstancy.Feasible`
- Truth anchor: `D5/S3/Quantum/JonesAloyEntropyConstancy.IsSourceRoof`
- Truth anchor: `D5/S3/Quantum/JonesAloyEntropyConstancy.claim`
- Truth anchor: `D5/S3/Quantum/JonesAloyEntropyConstancy.entropy`
- Truth anchor: `D5/S3/Quantum/JonesAloyEntropyConstancy.entropyValues`
- Truth anchor: `D5/S3/Quantum/JonesAloyEntropyConstancy.fidelityExpression`
- Truth anchor: `D5/S3/Quantum/JonesAloyEntropyConstancy.gamma`
- Truth anchor: `D5/S3/Quantum/JonesAloyEntropyConstancy.quantumSet`
- Truth anchor: `D5/S3/Quantum/JonesAloyEntropyConstancy.result`
- Dependency: [D5/S3/Quantum/CloningMachine](CloningMachine.md)
