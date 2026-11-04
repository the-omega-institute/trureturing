# Signalling-game value equality

## Abstract

The signalling game has classical, quantum and no-signalling value 1/max(m,n).

**Definition 1.1 (No-signalling conditional probabilities).**

$$\forall (m: \mathbb{N}), (\forall (n: \mathbb{N}), (\forall (p: \operatorname{Fin}\left(n\right) \to \left(\operatorname{Fin}\left(m\right) \to \left(\operatorname{Fin}\left(m\right) \to \left(\operatorname{Fin}\left(n\right) \to \mathbb{R}\right)\right)\right)), ((\operatorname{IsNoSignalling}\left(p\right)) \Leftrightarrow ((\forall (a: \operatorname{Fin}\left(n\right)), (\forall (b: \operatorname{Fin}\left(m\right)), (\forall (x: \operatorname{Fin}\left(m\right)), (\forall (y: \operatorname{Fin}\left(n\right)), ((0: \mathbb{R}) \le p\left(a, b, x, y\right)))))) \land ((\forall (x: \operatorname{Fin}\left(m\right)), (\forall (y: \operatorname{Fin}\left(n\right)), (\sum_{a: \operatorname{Fin}\left(n\right)} (\sum_{b: \operatorname{Fin}\left(m\right)} (p\left(a, b, x, y\right))) = (1: \mathbb{R})))) \land ((\forall (a: \operatorname{Fin}\left(n\right)), (\forall (x: \operatorname{Fin}\left(m\right)), (\forall (y: \operatorname{Fin}\left(n\right)), (\forall (z: \operatorname{Fin}\left(n\right)), (\sum_{b: \operatorname{Fin}\left(m\right)} (p\left(a, b, x, y\right)) = \sum_{b: \operatorname{Fin}\left(m\right)} (p\left(a, b, x, z\right))))))) \land (\forall (b: \operatorname{Fin}\left(m\right)), (\forall (x: \operatorname{Fin}\left(m\right)), (\forall (z: \operatorname{Fin}\left(m\right)), (\forall (y: \operatorname{Fin}\left(n\right)), (\sum_{a: \operatorname{Fin}\left(n\right)} (p\left(a, b, x, y\right)) = \sum_{a: \operatorname{Fin}\left(n\right)} (p\left(a, b, z, y\right)))))))))))))$$

*Formalization.* `D5/S3/Quantum/Information/SignallingGameValueEquality.IsNoSignalling` (`✓ std3`).

*Citation.* Akshay Seshadri; Felix Leditzky; Vikesh Siddhu; Graeme Smith (2023). *On the separation of correlation-assisted sum capacities of multiple access channels*. DOI: [10.1109/TIT.2023.3274434](https://doi.org/10.1109/TIT.2023.3274434). URL: <https://arxiv.org/abs/2205.13538v3>.

*Commentary.*

For questions x and y and answers a and b, IsNoSignalling requires nonnegative probabilities, normalization for each question pair, and independence of Alice's marginal from Bob's question and of Bob's marginal from Alice's question.

**Definition 1.2 (Uniform winning probability).**

$$\forall (m: \mathbb{N}), (\forall (n: \mathbb{N}), (\forall (p: \operatorname{Fin}\left(n\right) \to \left(\operatorname{Fin}\left(m\right) \to \left(\operatorname{Fin}\left(m\right) \to \left(\operatorname{Fin}\left(n\right) \to \mathbb{R}\right)\right)\right)), ((\operatorname{winProb}\left(p\right): \mathbb{R}) = \frac{1}{((m: \mathbb{R}) \cdot (n: \mathbb{R}))} \cdot \sum_{x: \operatorname{Fin}\left(m\right)} (\sum_{y: \operatorname{Fin}\left(n\right)} (p\left(y, x, x, y\right))))))$$

*Formalization.* `D5/S3/Quantum/Information/SignallingGameValueEquality.winProb` (`✓ std3`).

*Citation.* Akshay Seshadri; Felix Leditzky; Vikesh Siddhu; Graeme Smith (2023). *On the separation of correlation-assisted sum capacities of multiple access channels*. DOI: [10.1109/TIT.2023.3274434](https://doi.org/10.1109/TIT.2023.3274434). URL: <https://arxiv.org/abs/2205.13538v3>.

*Commentary.*

The questions are uniform on Fin m and Fin n. The winning event is that the first answer equals the second question and the second answer equals the first question, so winProb averages p y x x y over all question pairs and divides by the product of the two cardinalities.

**Definition 1.3 (A deterministic local box).**

$$\forall (m: \mathbb{N}), (\forall (n: \mathbb{N}), (\forall (fa: \operatorname{Fin}\left(m\right) \to \operatorname{Fin}\left(n\right)), (\forall (fb: \operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(m\right)), (\forall (a: \operatorname{Fin}\left(n\right)), (\forall (b: \operatorname{Fin}\left(m\right)), (\forall (x: \operatorname{Fin}\left(m\right)), (\forall (y: \operatorname{Fin}\left(n\right)), ((\operatorname{deterministicBox}\left(fa, fb, a, b, x, y\right): \mathbb{R}) = \operatorname{labelKernel}\left(fa, x, a\right) \cdot \operatorname{labelKernel}\left(fb, y, b\right)))))))))$$

*Formalization.* `D5/S3/Quantum/Information/SignallingGameValueEquality.deterministicBox` (`✓ std3`).

*Citation.* Akshay Seshadri; Felix Leditzky; Vikesh Siddhu; Graeme Smith (2023). *On the separation of correlation-assisted sum capacities of multiple access channels*. DOI: [10.1109/TIT.2023.3274434](https://doi.org/10.1109/TIT.2023.3274434). URL: <https://arxiv.org/abs/2205.13538v3>.

*Commentary.*

Given local response functions fa from Fin m to Fin n and fb from Fin n to Fin m, deterministicBox is the product of the two indicator kernels for the selected answers and questions.

**Definition 1.4 (Classical deterministic values).**

$$\forall (m: \mathbb{N}), (\forall (n: \mathbb{N}), (\operatorname{classicalValues}\left(m, n\right) = \{(v: \mathbb{R}) \mid \exists (fa: \operatorname{Fin}\left(m\right) \to \operatorname{Fin}\left(n\right)), (\exists (fb: \operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(m\right)), (\operatorname{winProb}\left(\operatorname{deterministicBox}\left(fa, fb\right)\right) = v))\}))$$

*Formalization.* `D5/S3/Quantum/Information/SignallingGameValueEquality.classicalValues` (`✓ std3`).

*Citation.* Akshay Seshadri; Felix Leditzky; Vikesh Siddhu; Graeme Smith (2023). *On the separation of correlation-assisted sum capacities of multiple access channels*. DOI: [10.1109/TIT.2023.3274434](https://doi.org/10.1109/TIT.2023.3274434). URL: <https://arxiv.org/abs/2205.13538v3>.

*Commentary.*

classicalValues m n is the set of real winning probabilities obtained from pairs of deterministic local response functions.

**Definition 1.5 (Finite-dimensional quantum strategies).**

$$\forall (m: \mathbb{N}), (\forall (n: \mathbb{N}), (\forall (da: \mathbb{N}), (\forall (db: \mathbb{N}), (\forall (rho: \operatorname{Matrix}\left((\operatorname{Fin}\left(da\right)\times \operatorname{Fin}\left(db\right)), (\operatorname{Fin}\left(da\right)\times \operatorname{Fin}\left(db\right)), \mathbb{C}\right)), (\forall (a: \operatorname{Fin}\left(m\right) \to \left(\operatorname{Fin}\left(n\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(da\right), \operatorname{Fin}\left(da\right), \mathbb{C}\right)\right)), (\forall (b: \operatorname{Fin}\left(n\right) \to \left(\operatorname{Fin}\left(m\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(db\right), \operatorname{Fin}\left(db\right), \mathbb{C}\right)\right)), ((\operatorname{IsQuantumStrategy}\left(rho, a, b\right)) \Leftrightarrow ((\operatorname{IsDensity}\left(rho\right)) \land ((\forall (x: \operatorname{Fin}\left(m\right)), (\operatorname{IsPOVM}\left(a\left(x\right)\right))) \land (\forall (y: \operatorname{Fin}\left(n\right)), (\operatorname{IsPOVM}\left(b\left(y\right)\right))))))))))))$$

*Formalization.* `D5/S3/Quantum/Information/SignallingGameValueEquality.IsQuantumStrategy` (`✓ std3`).

*Citation.* Akshay Seshadri; Felix Leditzky; Vikesh Siddhu; Graeme Smith (2023). *On the separation of correlation-assisted sum capacities of multiple access channels*. DOI: [10.1109/TIT.2023.3274434](https://doi.org/10.1109/TIT.2023.3274434). URL: <https://arxiv.org/abs/2205.13538v3>.

*Commentary.*

A quantum strategy consists of a bipartite complex density matrix rho and a POVM for every question on each side. Alice's measurements act on the first local dimension and Bob's on the second.

**Definition 1.6 (The Born-rule correlation box).**

$$\forall (m: \mathbb{N}), (\forall (n: \mathbb{N}), (\forall (da: \mathbb{N}), (\forall (db: \mathbb{N}), (\forall (rho: \operatorname{Matrix}\left((\operatorname{Fin}\left(da\right)\times \operatorname{Fin}\left(db\right)), (\operatorname{Fin}\left(da\right)\times \operatorname{Fin}\left(db\right)), \mathbb{C}\right)), (\forall (a: \operatorname{Fin}\left(m\right) \to \left(\operatorname{Fin}\left(n\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(da\right), \operatorname{Fin}\left(da\right), \mathbb{C}\right)\right)), (\forall (b: \operatorname{Fin}\left(n\right) \to \left(\operatorname{Fin}\left(m\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(db\right), \operatorname{Fin}\left(db\right), \mathbb{C}\right)\right)), (\forall (u: \operatorname{Fin}\left(n\right)), (\forall (v: \operatorname{Fin}\left(m\right)), (\forall (x: \operatorname{Fin}\left(m\right)), (\forall (y: \operatorname{Fin}\left(n\right)), ((\operatorname{quantumBox}\left(rho, a, b, u, v, x, y\right): \mathbb{R}) = \operatorname{Complex.re}\left(\operatorname{bornProbability}\left(rho, \operatorname{Matrix.kroneckerMap}\left(fun x1 x2 \mapsto x1 \cdot x2, a\left(x, u\right), b\left(y, v\right)\right)\right)\right))))))))))))$$

*Formalization.* `D5/S3/Quantum/Information/SignallingGameValueEquality.quantumBox` (`✓ std3`).

*Citation.* Akshay Seshadri; Felix Leditzky; Vikesh Siddhu; Graeme Smith (2023). *On the separation of correlation-assisted sum capacities of multiple access channels*. DOI: [10.1109/TIT.2023.3274434](https://doi.org/10.1109/TIT.2023.3274434). URL: <https://arxiv.org/abs/2205.13538v3>.

*Commentary.*

quantumBox is the real part of Born's probability for the tensor product of Alice's effect for answer u and Bob's effect for answer v, evaluated at questions x and y.

**Definition 1.7 (Quantum strategy values).**

$$\forall (m: \mathbb{N}), (\forall (n: \mathbb{N}), (\operatorname{quantumValues}\left(m, n\right) = \{(v: \mathbb{R}) \mid \exists (da: \mathbb{N}), (\exists (db: \mathbb{N}), (\exists (rho: \operatorname{Matrix}\left((\operatorname{Fin}\left(da\right)\times \operatorname{Fin}\left(db\right)), (\operatorname{Fin}\left(da\right)\times \operatorname{Fin}\left(db\right)), \mathbb{C}\right)), (\exists (a: \operatorname{Fin}\left(m\right) \to \left(\operatorname{Fin}\left(n\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(da\right), \operatorname{Fin}\left(da\right), \mathbb{C}\right)\right)), (\exists (b: \operatorname{Fin}\left(n\right) \to \left(\operatorname{Fin}\left(m\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(db\right), \operatorname{Fin}\left(db\right), \mathbb{C}\right)\right)), ((\operatorname{IsQuantumStrategy}\left(rho, a, b\right)) \land (\operatorname{winProb}\left(\operatorname{quantumBox}\left(rho, a, b\right)\right) = v))))))\}))$$

*Formalization.* `D5/S3/Quantum/Information/SignallingGameValueEquality.quantumValues` (`✓ std3`).

*Citation.* Akshay Seshadri; Felix Leditzky; Vikesh Siddhu; Graeme Smith (2023). *On the separation of correlation-assisted sum capacities of multiple access channels*. DOI: [10.1109/TIT.2023.3274434](https://doi.org/10.1109/TIT.2023.3274434). URL: <https://arxiv.org/abs/2205.13538v3>.

*Commentary.*

quantumValues m n contains exactly the winning probabilities of all finite local dimensions, bipartite density matrices, and local POVM families satisfying IsQuantumStrategy.

**Definition 1.8 (No-signalling strategy values).**

$$\forall (m: \mathbb{N}), (\forall (n: \mathbb{N}), (\operatorname{noSignallingValues}\left(m, n\right) = \{(v: \mathbb{R}) \mid \exists (p: \operatorname{Fin}\left(n\right) \to \left(\operatorname{Fin}\left(m\right) \to \left(\operatorname{Fin}\left(m\right) \to \left(\operatorname{Fin}\left(n\right) \to \mathbb{R}\right)\right)\right)), ((\operatorname{IsNoSignalling}\left(p\right)) \land (\operatorname{winProb}\left(p\right) = v))\}))$$

*Formalization.* `D5/S3/Quantum/Information/SignallingGameValueEquality.noSignallingValues` (`✓ std3`).

*Citation.* Akshay Seshadri; Felix Leditzky; Vikesh Siddhu; Graeme Smith (2023). *On the separation of correlation-assisted sum capacities of multiple access channels*. DOI: [10.1109/TIT.2023.3274434](https://doi.org/10.1109/TIT.2023.3274434). URL: <https://arxiv.org/abs/2205.13538v3>.

*Commentary.*

noSignallingValues m n contains the winning probabilities of all normalized nonnegative boxes satisfying IsNoSignalling.

**Definition 1.9 (The common sharp value).**

$$(\operatorname{claim}: Prop) = (\forall (m: \mathbb{N}), (\forall (n: \mathbb{N}), ((1 \le m) \Rightarrow ((1 \le n) \Rightarrow ((\operatorname{IsGreatest}\left(\operatorname{noSignallingValues}\left(m, n\right), \frac{1}{\operatorname{max}\left((m: \mathbb{R}), (n: \mathbb{R})\right)}\right)) \land ((\operatorname{IsGreatest}\left(\operatorname{quantumValues}\left(m, n\right), \frac{1}{\operatorname{max}\left((m: \mathbb{R}), (n: \mathbb{R})\right)}\right)) \land (\operatorname{IsGreatest}\left(\operatorname{classicalValues}\left(m, n\right), \frac{1}{\operatorname{max}\left((m: \mathbb{R}), (n: \mathbb{R})\right)}\right))))))))$$

*Formalization.* `D5/S3/Quantum/Information/SignallingGameValueEquality.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Akshay Seshadri; Felix Leditzky; Vikesh Siddhu; Graeme Smith (2023). *On the separation of correlation-assisted sum capacities of multiple access channels*. DOI: [10.1109/TIT.2023.3274434](https://doi.org/10.1109/TIT.2023.3274434). URL: <https://arxiv.org/abs/2205.13538v3>.

*Commentary.*

For every pair of nonempty finite question sets, the greatest no-signalling, quantum, and classical deterministic winning probabilities are all 1/max(m,n).

**Theorem 1.10 (The signalling-game equality is proved).**

$$\forall (m: \mathbb{N}), (\forall (n: \mathbb{N}), ((1 \le m) \Rightarrow ((1 \le n) \Rightarrow ((\operatorname{IsGreatest}\left(\operatorname{noSignallingValues}\left(m, n\right), \frac{1}{\operatorname{max}\left((m: \mathbb{R}), (n: \mathbb{R})\right)}\right)) \land ((\operatorname{IsGreatest}\left(\operatorname{quantumValues}\left(m, n\right), \frac{1}{\operatorname{max}\left((m: \mathbb{R}), (n: \mathbb{R})\right)}\right)) \land (\operatorname{IsGreatest}\left(\operatorname{classicalValues}\left(m, n\right), \frac{1}{\operatorname{max}\left((m: \mathbb{R}), (n: \mathbb{R})\right)}\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/SignallingGameValueEquality.result` (`✓ std3`). ∎

*Resolves.* `Problems/seshadri-leditzky-siddhu-smith-2023-signalling-game-values` (proved) by `D5/S3/Quantum/Information/SignallingGameValueEquality.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"seshadri-leditzky-siddhu-smith-2023-signalling-game-values","declaration_gid":"D5/S3/Quantum/Information/SignallingGameValueEquality.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Akshay Seshadri; Felix Leditzky; Vikesh Siddhu; Graeme Smith (2023). *On the separation of correlation-assisted sum capacities of multiple access channels*. DOI: [10.1109/TIT.2023.3274434](https://doi.org/10.1109/TIT.2023.3274434). URL: <https://arxiv.org/abs/2205.13538v3>.

*Commentary.*

Choose response functions fa and fb that reduce indices modulo their respective target dimensions: fa sends x to x mod n and fb sends y to y mod m. If m is at most n, fb composed with fa is the identity on Fin m; if n is at most m, fa composed with fb is the identity on Fin n. In either case the deterministic box wins on exactly the smaller question set, so its uniform winning probability is 1/max(m,n).

Realize this deterministic box as a one-dimensional quantum strategy. Take the one-by-one density matrix and diagonal one-by-one POVM effects whose entries are the local indicator kernels. The POVMs sum to the identity, and direct evaluation of Born's rule gives quantumBox equal to deterministicBox.

Every quantum strategy induces a no-signalling box. Summing Bob's POVM over his answers replaces it by the identity on Bob's space, and summing Alice's POVM does the same on Alice's space. Positivity follows from positivity of the state and the two effects; normalization follows from trace one. The resulting marginal sums are independent of the other question.

For any no-signalling box, the winning sum is bounded by m using Alice's marginal and by n using Bob's marginal: each winning term is bounded by the corresponding marginal term, and the relevant normalized marginal sums equal one. Splitting into m at most n or n at most m turns these bounds into winProb at most 1/max(m,n).

The deterministic construction supplies an element attaining the bound in every class. The no-signalling upper bound applies directly to noSignallingValues and, through the quantum-to-no-signalling construction, to quantumValues. For a classical value, embed each deterministic box into a one-dimensional quantum strategy and apply the same bound. The three IsGreatest statements follow.

## References

- Truth anchor: `D5/S3/Quantum/Information/SignallingGameValueEquality.IsNoSignalling`
- Truth anchor: `D5/S3/Quantum/Information/SignallingGameValueEquality.IsQuantumStrategy`
- Truth anchor: `D5/S3/Quantum/Information/SignallingGameValueEquality.claim`
- Truth anchor: `D5/S3/Quantum/Information/SignallingGameValueEquality.classicalValues`
- Truth anchor: `D5/S3/Quantum/Information/SignallingGameValueEquality.deterministicBox`
- Truth anchor: `D5/S3/Quantum/Information/SignallingGameValueEquality.noSignallingValues`
- Truth anchor: `D5/S3/Quantum/Information/SignallingGameValueEquality.quantumBox`
- Truth anchor: `D5/S3/Quantum/Information/SignallingGameValueEquality.quantumValues`
- Truth anchor: `D5/S3/Quantum/Information/SignallingGameValueEquality.result`
- Truth anchor: `D5/S3/Quantum/Information/SignallingGameValueEquality.winProb`
- Dependency: [D5/S3/Quantum/Information/SLDSpectralEnergy](SLDSpectralEnergy.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/ConcealmentKernelNecessityRefutation](../QuantumChannels/ConcealmentKernelNecessityRefutation.md)
- Dependency: [D5/S3/TotalVariation/Equality/FiberwiseEqualDistanceLift](../../TotalVariation/Equality/FiberwiseEqualDistanceLift.md)
