# Finite preparations certify nonclassical measurements

## Abstract

Every nonclassical finite-outcome quantum measurement has a finite preparation experiment with a strictly violated noncontextuality inequality.

**Definition 1.1 (Responses preserving all effect identities).**

$$\forall \left(d: \mathbb{N}\right), \left(\forall \left(m: \mathbb{N}\right), \left(\forall \left(M: \left(\operatorname{Fin}\left(m\right)\right) \to \left(\operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right)\right), \left(\operatorname{D5.S3.QuantumContext.FinitePreparationCertification.responsePolytope}\left(M\right) = \{r: \left(\operatorname{Fin}\left(m\right)\right) \to \left(\mathbb{R}\right) \mid \left(\forall \left(b: \operatorname{Fin}\left(m\right)\right), \left(0 \le r\left(b\right)\right)\right) \land \left(\left(\sum_{b: \operatorname{Fin}\left(m\right)} \left(r\left(b\right)\right) = 1\right) \land \left(\forall \left(\beta: \left(\operatorname{Fin}\left(m\right)\right) \to \left(\mathbb{R}\right)\right), \left(\left(\sum_{b: \operatorname{Fin}\left(m\right)} \left(\left(\left(\beta\left(b\right): \mathbb{C}\right)\right) \cdot \left(M\left(b\right)\right)\right) = 0\right) \Rightarrow \left(\sum_{b: \operatorname{Fin}\left(m\right)} \left(\left(\beta\left(b\right)\right) \cdot \left(r\left(b\right)\right)\right) = 0\right)\right)\right)\right)\}\right)\right)\right)$$

*Formalization.* `D5/S3/QuantumContext/FinitePreparationCertification.responsePolytope` (`✓ std3`).

*Citation.* Yujie Zhang, Yìlè Yīng, David Schmid (2026). *Quantifiers and witnesses for the nonclassicality of measurements and of states*. DOI: [10.22331/q-2026-07-30-2180](https://doi.org/10.22331/q-2026-07-30-2180). URL: <https://arxiv.org/abs/2504.02944v3>.

*Commentary.*

Definition 3, PDF page 4: “The noncontextual measurement-assignment polytope ℙ_M associated with a multi-measurement M = {{Mᵦ|ᵧ}ᵦ}ᵧ is the set of points {p(b|y)}ᵦ,ᵧ that satisfy the following constraints:” The constraints are nonnegativity, normalization for each measurement setting, and every linear effect identity. Here there is one setting, d is the finite Hilbert dimension, m is the number of outcomes, and β has real coefficients. The coefficients acting on complex matrices are included in ℂ.

**Definition 1.2 (Noncontextual tables on arbitrary preparation families).**

$$\forall \left(d: \mathbb{N}\right), \left(\forall \left(m: \mathbb{N}\right), \left(\forall \left(\iota: \operatorname{Type}\right), \left(\forall \left(\rho: \left(\iota\right) \to \left(\operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right)\right), \left(\forall \left(M: \left(\operatorname{Fin}\left(m\right)\right) \to \left(\operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right)\right), \left(\forall \left(p: \left(\iota\right) \to \left(\left(\operatorname{Fin}\left(m\right)\right) \to \left(\mathbb{R}\right)\right)\right), \left(\left(\operatorname{D5.S3.QuantumContext.FinitePreparationCertification.NoncontextualTable}\left(\rho, M, p\right)\right) \Leftrightarrow \left(\exists \left(\Lambda: \operatorname{Type}\right), \left(\exists \left(\mu: \left(\iota\right) \to \left(\left(\Lambda\right) \to \left(\mathbb{R}\right)\right)\right), \left(\exists \left(\xi: \left(\Lambda\right) \to \left(\left(\operatorname{Fin}\left(m\right)\right) \to \left(\mathbb{R}\right)\right)\right), \left(\left(\forall \left(a: \iota\right), \left(\forall \left(l: \Lambda\right), \left(0 \le \mu\left(a, l\right)\right)\right)\right) \land \left(\left(\forall \left(a: \iota\right), \left(\operatorname{HasSum}\left(\mu\left(a\right), 1\right)\right)\right) \land \left(\left(\forall \left(l: \Lambda\right), \left(\xi\left(l\right) \in \operatorname{D5.S3.QuantumContext.FinitePreparationCertification.responsePolytope}\left(M\right)\right)\right) \land \left(\left(\forall \left(l: \Lambda\right), \left(\forall \left(s: \operatorname{Finset}\left(\iota\right)\right), \left(\forall \left(\alpha: \left(\iota\right) \to \left(\mathbb{R}\right)\right), \left(\left(\sum_{a \in s} \left(\left(\left(\alpha\left(a\right): \mathbb{C}\right)\right) \cdot \left(\rho\left(a\right)\right)\right) = 0\right) \Rightarrow \left(\sum_{a \in s} \left(\left(\alpha\left(a\right)\right) \cdot \left(\mu\left(a, l\right)\right)\right) = 0\right)\right)\right)\right)\right) \land \left(\forall \left(a: \iota\right), \left(\forall \left(b: \operatorname{Fin}\left(m\right)\right), \left(\operatorname{HasSum}\left(\lambda \left(l: \Lambda\right) \mapsto \left(\left(\xi\left(l, b\right)\right) \cdot \left(\mu\left(a, l\right)\right)\right), p\left(a, b\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/QuantumContext/FinitePreparationCertification.NoncontextualTable` (`✓ std3`).

*Citation.* Yujie Zhang, Yìlè Yīng, David Schmid (2026). *Quantifiers and witnesses for the nonclassicality of measurements and of states*. DOI: [10.22331/q-2026-07-30-2180](https://doi.org/10.22331/q-2026-07-30-2180). URL: <https://arxiv.org/abs/2504.02944v3>.

*Commentary.*

Definition 1, PDF page 3: “A prepare-and-measure experiment with a quantum multi-source P = {{p(a|x)ρₐ|ₓ}ₐ}ₓ and a quantum multi-measurement M = {{Mᵦ|ᵧ}ᵦ}ᵧ is classically explainable if and only if there exists an ontological model with ontic state space Λ, preparation assignments p(a, λ|x), and response functions p(b|y, λ) such that Eqs. (3), (5a), and (5b) are satisfied.” Each preparation setting here has one certain normalized output. The index type ι and discrete ontic type Λ are arbitrary. HasSum expresses the ontic sums, including infinite summable families. Every finitely supported real preparation identity holds at every ontic state. The response vectors satisfy every effect identity, and their weighted sums reproduce the entire table p.

**Definition 1.3 (A common model for all density matrices).**

$$\forall \left(d: \mathbb{N}\right), \left(\forall \left(m: \mathbb{N}\right), \left(\forall \left(M: \left(\operatorname{Fin}\left(m\right)\right) \to \left(\operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right)\right), \left(\left(\operatorname{D5.S3.QuantumContext.FinitePreparationCertification.Classical}\left(M\right)\right) \Leftrightarrow \left(\operatorname{D5.S3.QuantumContext.FinitePreparationCertification.NoncontextualTable}\left(\lambda \left(\rho: \{\rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right) // \operatorname{D5.S3.QuantumChannels.CoPRelativeQuantumnessRefutation.IsDensity}\left(\rho\right)\}\right) \mapsto \left(\operatorname{val}\left(\rho\right)\right), M, \lambda \left(\rho: \{\rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right) // \operatorname{D5.S3.QuantumChannels.CoPRelativeQuantumnessRefutation.IsDensity}\left(\rho\right)\}\right) \mapsto \left(\lambda \left(b: \operatorname{Fin}\left(m\right)\right) \mapsto \left(\operatorname{Complex.re}\left(\operatorname{D5.S3.Quantum.FiniteDimensional.bornProbability}\left(\operatorname{val}\left(\rho\right), M\left(b\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/QuantumContext/FinitePreparationCertification.Classical` (`✓ std3`).

*Citation.* Yujie Zhang, Yìlè Yīng, David Schmid (2026). *Quantifiers and witnesses for the nonclassicality of measurements and of states*. DOI: [10.22331/q-2026-07-30-2180](https://doi.org/10.22331/q-2026-07-30-2180). URL: <https://arxiv.org/abs/2504.02944v3>.

*Commentary.*

Definition 2, PDF page 3: “A multi-measurement is classical if and only if the statistics generated by the set of circuits where it is contracted with any state (i.e., where the set ranges over all states) are classically explainable in the sense of Def. 1.” The preparation family is the subtype of all density matrices. A single ontological model must reproduce all their real Born probabilities. The function val is subtype projection.

**Definition 1.4 (Conjecture 1).**

$$\left(\operatorname{D5.S3.QuantumContext.FinitePreparationCertification.claim}\right) \Leftrightarrow \left(\forall \left(d: \mathbb{N}\right), \left(\left(0 < d\right) \Rightarrow \left(\forall \left(m: \mathbb{N}\right), \left(\left(0 < m\right) \Rightarrow \left(\forall \left(M: \left(\operatorname{Fin}\left(m\right)\right) \to \left(\operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right)\right), \left(\left(\operatorname{D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation.IsPOVM}\left(M\right)\right) \Rightarrow \left(\left(\neg \left(\operatorname{D5.S3.QuantumContext.FinitePreparationCertification.Classical}\left(M\right)\right)\right) \Rightarrow \left(\exists \left(n: \mathbb{N}\right), \left(\exists \left(\rho: \left(\operatorname{Fin}\left(n\right)\right) \to \left(\operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right)\right), \left(\exists \left(w: \left(\operatorname{Fin}\left(n\right)\right) \to \left(\left(\operatorname{Fin}\left(m\right)\right) \to \left(\mathbb{R}\right)\right)\right), \left(\exists \left(c: \mathbb{R}\right), \left(\left(\forall \left(a: \operatorname{Fin}\left(n\right)\right), \left(\operatorname{D5.S3.QuantumChannels.CoPRelativeQuantumnessRefutation.IsDensity}\left(\rho\left(a\right)\right)\right)\right) \land \left(\left(\forall \left(p: \left(\operatorname{Fin}\left(n\right)\right) \to \left(\left(\operatorname{Fin}\left(m\right)\right) \to \left(\mathbb{R}\right)\right)\right), \left(\left(\operatorname{D5.S3.QuantumContext.FinitePreparationCertification.NoncontextualTable}\left(\rho, M, p\right)\right) \Rightarrow \left(\sum_{a: \operatorname{Fin}\left(n\right)} \left(\sum_{b: \operatorname{Fin}\left(m\right)} \left(\left(w\left(a, b\right)\right) \cdot \left(p\left(a, b\right)\right)\right)\right) \le c\right)\right)\right) \land \left(c < \sum_{a: \operatorname{Fin}\left(n\right)} \left(\sum_{b: \operatorname{Fin}\left(m\right)} \left(\left(w\left(a, b\right)\right) \cdot \left(\operatorname{Complex.re}\left(\operatorname{D5.S3.Quantum.FiniteDimensional.bornProbability}\left(\rho\left(a\right), M\left(b\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/QuantumContext/FinitePreparationCertification.claim` (`✓ std3`).

*Citation.* Yujie Zhang, Yìlè Yīng, David Schmid (2026). *Quantifiers and witnesses for the nonclassicality of measurements and of states*. DOI: [10.22331/q-2026-07-30-2180](https://doi.org/10.22331/q-2026-07-30-2180). URL: <https://arxiv.org/abs/2504.02944v3>.

*Commentary.*

Conjecture 1, Section 4.3, PDF page 10: “A finite number of preparations is sufficient for the theory-independent certification of any nonclassical measurement with a finite number of outcomes (through the violation of some noncontextual inequality).” The dimension d and outcome count m are positive. For each POVM M without a common model, the preparations ρ, coefficients w, and bound c may depend on M. The inequality holds for every noncontextual table on those preparations, and the real Born table strictly violates it. No uniform preparation count or noise bound is asserted.

**Theorem 1.5 (A finite operational inequality).**

$$\forall \left(d: \mathbb{N}\right), \left(\left(0 < d\right) \Rightarrow \left(\forall \left(m: \mathbb{N}\right), \left(\left(0 < m\right) \Rightarrow \left(\forall \left(M: \left(\operatorname{Fin}\left(m\right)\right) \to \left(\operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right)\right), \left(\left(\operatorname{D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation.IsPOVM}\left(M\right)\right) \Rightarrow \left(\left(\neg \left(\operatorname{D5.S3.QuantumContext.FinitePreparationCertification.Classical}\left(M\right)\right)\right) \Rightarrow \left(\exists \left(n: \mathbb{N}\right), \left(\exists \left(\rho: \left(\operatorname{Fin}\left(n\right)\right) \to \left(\operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right)\right), \left(\exists \left(w: \left(\operatorname{Fin}\left(n\right)\right) \to \left(\left(\operatorname{Fin}\left(m\right)\right) \to \left(\mathbb{R}\right)\right)\right), \left(\exists \left(c: \mathbb{R}\right), \left(\left(\forall \left(a: \operatorname{Fin}\left(n\right)\right), \left(\operatorname{D5.S3.QuantumChannels.CoPRelativeQuantumnessRefutation.IsDensity}\left(\rho\left(a\right)\right)\right)\right) \land \left(\left(\forall \left(p: \left(\operatorname{Fin}\left(n\right)\right) \to \left(\left(\operatorname{Fin}\left(m\right)\right) \to \left(\mathbb{R}\right)\right)\right), \left(\left(\operatorname{D5.S3.QuantumContext.FinitePreparationCertification.NoncontextualTable}\left(\rho, M, p\right)\right) \Rightarrow \left(\sum_{a: \operatorname{Fin}\left(n\right)} \left(\sum_{b: \operatorname{Fin}\left(m\right)} \left(\left(w\left(a, b\right)\right) \cdot \left(p\left(a, b\right)\right)\right)\right) \le c\right)\right)\right) \land \left(c < \sum_{a: \operatorname{Fin}\left(n\right)} \left(\sum_{b: \operatorname{Fin}\left(m\right)} \left(\left(w\left(a, b\right)\right) \cdot \left(\operatorname{Complex.re}\left(\operatorname{D5.S3.Quantum.FiniteDimensional.bornProbability}\left(\rho\left(a\right), M\left(b\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumContext/FinitePreparationCertification.result` (`✓ std3`). ∎

*Resolves.* `Problems/zhang-ying-schmid` (proved) by `D5/S3/QuantumContext/FinitePreparationCertification.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"zhang-ying-schmid","declaration_gid":"D5/S3/QuantumContext/FinitePreparationCertification.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Yujie Zhang, Yìlè Yīng, David Schmid (2026). *Quantifiers and witnesses for the nonclassicality of measurements and of states*. DOI: [10.22331/q-2026-07-30-2180](https://doi.org/10.22331/q-2026-07-30-2180). URL: <https://arxiv.org/abs/2504.02944v3>.

*Commentary.*

The effect-identity constraints cut out a linear slice of the finite probability simplex. The finite-simplex-fiber theorem gives a finite set of response vectors spanning that slice. Decompose each response into these vectors and sum its preparation weights against the decomposition coefficients. Nonnegative domination gives summability, and interchange of finite sums with these sums preserves every preparation identity and every table entry.

For a fixed response carrier, preparation assignments belong to a product of finite simplexes. The Born equations and the finitely supported preparation relations are closed conditions. Models for all finite preparation families satisfy the finite-intersection property after extension by a fixed probability vector. Compactness therefore supplies one model for all density matrices. Its contrapositive gives a finite family without a model.

For a finite preparation family, the noncontextual tables are exactly the linear image of the compact convex set of nonnegative normalized weights preserving all preparation relations. Strict separation from the Born table gives a continuous linear functional and a real bound. Expansion in coordinate singletons expresses that functional as the displayed double sum.

The compactness argument allows arbitrary preparation index types and target tables. The conjecture keeps the POVM and positive finite-dimension assumptions of the source. The ontic sums are discrete; continuous measurable ontic models and quantitative bounds on preparations, noise or samples are outside this statement.

## References

- Truth anchor: `D5/S3/QuantumContext/FinitePreparationCertification.Classical`
- Truth anchor: `D5/S3/QuantumContext/FinitePreparationCertification.NoncontextualTable`
- Truth anchor: `D5/S3/QuantumContext/FinitePreparationCertification.claim`
- Truth anchor: `D5/S3/QuantumContext/FinitePreparationCertification.responsePolytope`
- Truth anchor: `D5/S3/QuantumContext/FinitePreparationCertification.result`
- Dependency: [D5/S3/Estimation/DataProcessing/FiniteSimplexFiberPolytope](../Estimation/DataProcessing/FiniteSimplexFiberPolytope.md)
- Dependency: [D5/S3/Estimation/DecisionRisk/FiniteBayesRiskDominanceCriterion](../Estimation/DecisionRisk/FiniteBayesRiskDominanceCriterion.md)
- Dependency: [D5/S3/Quantum/FiniteDimensional](../Quantum/FiniteDimensional.md)
- Dependency: [D5/S3/Quantum/Matrix/CartesianVariance](../Quantum/Matrix/CartesianVariance.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/ConcealmentKernelNecessityRefutation](../Quantum/QuantumChannels/ConcealmentKernelNecessityRefutation.md)
- Dependency: [D5/S3/QuantumChannels/CoPRelativeQuantumnessRefutation](../QuantumChannels/CoPRelativeQuantumnessRefutation.md)
