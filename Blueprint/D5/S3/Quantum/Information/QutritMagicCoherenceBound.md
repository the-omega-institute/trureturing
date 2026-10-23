# A lower bound on qutrit magic from coherence

## Abstract

For every normalized pure qutrit state, the sum negativity is at least (C/2) sqrt(1 - C/2), where C is its l1 coherence.

Use the computational basis with indices 0, 1 and 2. Fin(3) is this index set. The rows and columns of every displayed array are ordered 0, 1, 2. Complex absolute values denote moduli, and Re and Im denote real and imaginary parts.

**Definition 1.1 (The nine Wigner entries).**

$$\forall (\rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{C}\right)), (\operatorname{wigner}\left(\rho\right) = \frac{1}{3} \cdot \begin{pmatrix}\operatorname{Re}\left(\rho_{0,0}\right) + 2 \cdot \operatorname{Re}\left(\rho_{1,2}\right)&\operatorname{Re}\left(\rho_{1,1}\right) + 2 \cdot \operatorname{Re}\left(\rho_{0,2}\right)&\operatorname{Re}\left(\rho_{2,2}\right) + 2 \cdot \operatorname{Re}\left(\rho_{0,1}\right)\\\operatorname{Re}\left(\rho_{0,0}\right) - \operatorname{Re}\left(\rho_{1,2}\right) - \sqrt{3} \cdot \operatorname{Im}\left(\rho_{1,2}\right)&\operatorname{Re}\left(\rho_{1,1}\right) - \operatorname{Re}\left(\rho_{0,2}\right) + \sqrt{3} \cdot \operatorname{Im}\left(\rho_{0,2}\right)&\operatorname{Re}\left(\rho_{2,2}\right) - \operatorname{Re}\left(\rho_{0,1}\right) - \sqrt{3} \cdot \operatorname{Im}\left(\rho_{0,1}\right)\\\operatorname{Re}\left(\rho_{0,0}\right) - \operatorname{Re}\left(\rho_{1,2}\right) + \sqrt{3} \cdot \operatorname{Im}\left(\rho_{1,2}\right)&\operatorname{Re}\left(\rho_{1,1}\right) - \operatorname{Re}\left(\rho_{0,2}\right) - \sqrt{3} \cdot \operatorname{Im}\left(\rho_{0,2}\right)&\operatorname{Re}\left(\rho_{2,2}\right) - \operatorname{Re}\left(\rho_{0,1}\right) + \sqrt{3} \cdot \operatorname{Im}\left(\rho_{0,1}\right)\end{pmatrix})$$

*Formalization.* `D5/S3/Quantum/Information/QutritMagicCoherenceBound.wigner` (`✓ std3`).

*Citation.* Chiranjib Mukhopadhyay; Sk Sazim; Arun Kumar Pati (2018). *Coherence makes quantum systems 'magical'*. DOI: [10.1088/1751-8121/aac8e8](https://doi.org/10.1088/1751-8121/aac8e8). URL: <https://arxiv.org/abs/1801.04807v3>.

*Commentary.*

The array defines wigner for every complex 3 by 3 matrix, using the real parts of its diagonal entries. For density matrices it is the discrete Wigner function of Eq. (12), with both phase-space indices shifted from 1, 2, 3 to 0, 1, 2. In particular, the imaginary part of the 02 entry has the opposite sign pattern to those of the 01 and 12 entries.

**Definition 1.2 (The sum negativity).**

$$\forall (\rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{C}\right)), (\operatorname{sumNegativity}\left(\rho\right) = \sum_{(p: \operatorname{Fin}\left(3\right))} (\sum_{(q: \operatorname{Fin}\left(3\right))} (\left|\operatorname{wigner}\left(\rho, p, q\right)\right|)) - 1)$$

*Formalization.* `D5/S3/Quantum/Information/QutritMagicCoherenceBound.sumNegativity` (`✓ std3`).

*Citation.* Chiranjib Mukhopadhyay; Sk Sazim; Arun Kumar Pati (2018). *Coherence makes quantum systems 'magical'*. DOI: [10.1088/1751-8121/aac8e8](https://doi.org/10.1088/1751-8121/aac8e8). URL: <https://arxiv.org/abs/1801.04807v3>.

*Commentary.*

The sum negativity is the sum of the absolute values of the nine Wigner entries, minus one, as in Eq. (13). The definition applies to every complex 3 by 3 matrix without additional assumptions.

**Definition 1.3 (The pure-qutrit coherence bound).**

$$\operatorname{claim} \Leftrightarrow (\forall (x: (\operatorname{Fin}\left(3\right) \to \mathbb{C})), ((\sum_{(i: \operatorname{Fin}\left(3\right))} (\left|x\left(i\right)\right|^{2}) = 1) \Rightarrow (\frac{\operatorname{l1Coherence}\left(\operatorname{rankOneDensity}\left(x\right)\right)}{2} \cdot \sqrt{1 - \frac{\operatorname{l1Coherence}\left(\operatorname{rankOneDensity}\left(x\right)\right)}{2}} \le \operatorname{sumNegativity}\left(\operatorname{rankOneDensity}\left(x\right)\right))))$$

*Formalization.* `D5/S3/Quantum/Information/QutritMagicCoherenceBound.claim` (`✓ std3`).

*Citation.* Chiranjib Mukhopadhyay; Sk Sazim; Arun Kumar Pati (2018). *Coherence makes quantum systems 'magical'*. DOI: [10.1088/1751-8121/aac8e8](https://doi.org/10.1088/1751-8121/aac8e8). URL: <https://arxiv.org/abs/1801.04807v3>.

*Commentary.*

Equation (18) asserts the bound for every normalized vector x in C cubed. Write rho = x x† = rankOneDensity(x), so rho has entry x(i) times the complex conjugate of x(j). Write C = l1Coherence(rho), the sum of the moduli of all ordered off-diagonal entries, hence:

$$
\forall (x: (\operatorname{Fin}\left(3\right) \to \mathbb{C})), (\operatorname{l1Coherence}\left(\operatorname{rankOneDensity}\left(x\right)\right) = \sum_{(i: \operatorname{Fin}\left(3\right))} (\sum_{(j: \operatorname{Fin}\left(3\right)), i \ne j} (\left|x\left(i\right) \cdot \overline{x\left(j\right)}\right|)))
$$

The normalization is the sum of squared moduli. The proposition requires no restriction on the phases.

**Theorem 1.4 (The lower bound holds for every pure qutrit).**

$$\operatorname{claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/QutritMagicCoherenceBound.result` (`✓ std3`). ∎

*Resolves.* `Problems/mukhopadhyay-sazim-pati-2018-qutrit-magic-coherence-bound` (proved) by `D5/S3/Quantum/Information/QutritMagicCoherenceBound.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"mukhopadhyay-sazim-pati-2018-qutrit-magic-coherence-bound","declaration_gid":"D5/S3/Quantum/Information/QutritMagicCoherenceBound.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Chiranjib Mukhopadhyay; Sk Sazim; Arun Kumar Pati (2018). *Coherence makes quantum systems 'magical'*. DOI: [10.1088/1751-8121/aac8e8](https://doi.org/10.1088/1751-8121/aac8e8). URL: <https://arxiv.org/abs/1801.04807v3>.

*Commentary.*

Let r(i) be the modulus of x(i). In column i of 3W, put A = r(i)² and R = r(j)r(k), where i, j, k are distinct. The three entries have sum 3A and second moment 3A² + 6R². For any three real numbers with positive mass P and negative mass N, the sum of their squares is at most P² + N². Applied to a column, this gives 3R² ≤ 3A² + 3AN + N² ≤ (√3 A + N)², so its negative mass is at least √3 max(R − A, 0).

Set s = r(0)r(1) + r(0)r(2) + r(1)r(2) = C/2 and v = 1 − s. Normalization gives s ≥ 0 and v ≥ 0. The amplitude defects δ(i) = r(i)² − r(j)r(k) satisfy Σδ = v and Σδ² = 1 − s². Their negative mass D = Σ max(−δ(i), 0) therefore obeys 1 − s² ≤ (v + D)² + D², which is D² + vD ≥ sv.

Put T = (√3/2)s√v. The square identity sv − (T² + vT) = (sv/4)(√3√v − 1)² shows T² + vT ≤ sv ≤ D² + vD. Since T, D and v are nonnegative, D ≥ T. Finally, let N be the total negative mass of 3W. The column bounds give N ≥ √3 D. Since the entries of 3W sum to 3, M = sumNegativity(rho) = (2/3)N ≥ (2/√3)D ≥ s√v. Substituting s = C/2 and v = 1 − s gives the asserted bound.

## References

- Truth anchor: `D5/S3/Quantum/Information/QutritMagicCoherenceBound.claim`
- Truth anchor: `D5/S3/Quantum/Information/QutritMagicCoherenceBound.result`
- Truth anchor: `D5/S3/Quantum/Information/QutritMagicCoherenceBound.sumNegativity`
- Truth anchor: `D5/S3/Quantum/Information/QutritMagicCoherenceBound.wigner`
- Dependency: [D5/S3/Quantum/Information/CorrelatedCoherenceMonogamyRefutation](CorrelatedCoherenceMonogamyRefutation.md)
- Dependency: [D5/S3/Quantum/PureState/PureStateHandshake](../PureState/PureStateHandshake.md)
