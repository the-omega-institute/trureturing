# DetectorSensorDickeOptimality

## Abstract

Balanced Dicke states maximize the success of equal-prior detector-sensor identification.

**Definition 1.1 (fire).**

$$\forall (n : \mathbb{N}) , \forall (theta : \mathbb{R}) , \forall (i : Fin\left(n\right)) , \forall (psi : \left(Fin\left(n\right) \to Bool\right) \to \mathbb{C}) , fire\left(theta, i, psi\right) = (fun x : Fin\left(n\right) \to Bool \mapsto \operatorname{Complex}.\operatorname{exp}\left((if x\left(i\right) then 1 else -1) \cdot (theta : \mathbb{C}) \cdot \operatorname{Complex}.\operatorname{I}\right) \cdot psi\left(x\right))$$

*Formalization.* `D5/S3/Quantum/Measurement/DetectorSensorDickeOptimality.fire` (`✓ std3`).

*Citation.* C. Zhan, H. Gupta, M. Hillery (2024). *Optimizing Initial State of Detector Sensors in Quantum Sensor Networks*. DOI: [10.1145/3655028](https://doi.org/10.1145/3655028). URL: <https://arxiv.org/abs/2306.17401v6>.

*Commentary.*

Section 2, pages 2–3: “Let |𝜙ᵢ⟩ = (𝐼^{⊗𝑖} ⊗ 𝑈 ⊗ 𝐼^{⊗(𝑛−𝑖−1)})|𝜓⟩.” A Boolean word labels the tensor eigenbasis; true is u₊ and false is u₋. Angles are in radians.

**Definition 1.2 (isoSuccess).**

$$\forall (n : \mathbb{N}) , \forall (theta : \mathbb{R}) , \forall (psi : \left(Fin\left(n\right) \to Bool\right) \to \mathbb{C}) , \forall (M : LocalPOVM\left(Fin\left(n\right) \to Bool, Fin\left(n\right)\right)) , isoSuccess\left(theta, psi, M\right) = (1) / ((n : \mathbb{R})) \cdot \sum i : Fin\left(n\right) , \operatorname{Complex}.\operatorname{re}\left((star\left(fire\left(theta, i, psi\right)\right) \cdot_{v} (\operatorname{LocalPOVM}.\operatorname{effect}\left(M, i\right) \times_{v} fire\left(theta, i, psi\right)))\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/DetectorSensorDickeOptimality.isoSuccess` (`✓ std3`).

*Citation.* C. Zhan, H. Gupta, M. Hillery (2024). *Optimizing Initial State of Detector Sensors in Quantum Sensor Networks*. DOI: [10.1145/3655028](https://doi.org/10.1145/3655028). URL: <https://arxiv.org/abs/2306.17401v6>.

*Commentary.*

Section 2, page 3: “these final states have an equal prior probability”. The success is the mean of the Born probabilities for the correct outcomes. LocalPOVM is the existing finite family of positive semidefinite effects summing to the identity.

**Definition 1.3 (rCount).**

$$\forall (n : \mathbb{N}) , \forall (i : Fin\left(n\right)) , \forall (j : Fin\left(n\right)) , \forall (k : \mathbb{N}) , rCount\left(n, i, j, k\right) = \operatorname{Finset}.\operatorname{card}\left(\operatorname{Finset}.\operatorname{filter}\left((fun x : Fin\left(n\right) \to Bool \mapsto ((\operatorname{Finset}.\operatorname{card}\left(\operatorname{Finset}.\operatorname{filter}\left((fun j : Fin\left(n\right) \mapsto x\left(j\right) = true), (\operatorname{Finset}.\operatorname{univ} : Finset\left(Fin\left(n\right)\right))\right)\right) = k) \land (x\left(i\right) = x\left(j\right)))), (\operatorname{Finset}.\operatorname{univ} : Finset\left(Fin\left(n\right) \to Bool\right))\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/DetectorSensorDickeOptimality.rCount` (`✓ std3`).

*Citation.* C. Zhan, H. Gupta, M. Hillery (2024). *Optimizing Initial State of Detector Sensors in Quantum Sensor Networks*. DOI: [10.1145/3655028](https://doi.org/10.1145/3655028). URL: <https://arxiv.org/abs/2306.17401v6>.

*Commentary.*

Section 4, page 7: “For each 0 ≤ 𝑘 ≤ 𝑛, let 𝑅𝑘 be the number of coefficient-squares from 𝑆𝑘 in the RHS of a Real equation”. Observation 1 places a word on this side exactly when its two selected bits agree. The inner cardinality counts the true bits.

**Definition 1.4 (lCount).**

$$\forall (n : \mathbb{N}) , \forall (i : Fin\left(n\right)) , \forall (j : Fin\left(n\right)) , \forall (k : \mathbb{N}) , lCount\left(n, i, j, k\right) = \operatorname{Finset}.\operatorname{card}\left(\operatorname{Finset}.\operatorname{filter}\left((fun x : Fin\left(n\right) \to Bool \mapsto ((\operatorname{Finset}.\operatorname{card}\left(\operatorname{Finset}.\operatorname{filter}\left((fun j : Fin\left(n\right) \mapsto x\left(j\right) = true), (\operatorname{Finset}.\operatorname{univ} : Finset\left(Fin\left(n\right)\right))\right)\right) = k) \land (x\left(i\right) \neq x\left(j\right)))), (\operatorname{Finset}.\operatorname{univ} : Finset\left(Fin\left(n\right) \to Bool\right))\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/DetectorSensorDickeOptimality.lCount` (`✓ std3`).

*Citation.* C. Zhan, H. Gupta, M. Hillery (2024). *Optimizing Initial State of Detector Sensors in Quantum Sensor Networks*. DOI: [10.1145/3655028](https://doi.org/10.1145/3655028). URL: <https://arxiv.org/abs/2306.17401v6>.

*Commentary.*

Section 4, page 7: “𝐿𝑘 be the number of coefficient-squares from 𝑆𝑙 in the LHS of Real equation.” Observation 1 places a word on this side exactly when its two selected bits differ. The source’s Sl in this sentence denotes the selected weight partition.

**Definition 1.5 (T).**

$$\forall (n : \mathbb{N}) , T\left(n\right) = let q : \mathbb{N} = \operatorname{Nat}.\operatorname{div}\left((n + 1), 2\right) in (\operatorname{Real}.\operatorname{arccos}\left(-(((q : \mathbb{R}) - 1) / ((q : \mathbb{R})))\right)) / (2)$$

*Formalization.* `D5/S3/Quantum/Measurement/DetectorSensorDickeOptimality.T` (`✓ std3`).

*Citation.* C. Zhan, H. Gupta, M. Hillery (2024). *Optimizing Initial State of Detector Sensors in Quantum Sensor Networks*. DOI: [10.1145/3655028](https://doi.org/10.1145/3655028). URL: <https://arxiv.org/abs/2306.17401v6>.

*Commentary.*

Theorem 2, pages 6–7, defines T = ½ arccos(−(⌈n/2⌉ − 1)/⌈n/2⌉). Nat.div is integer division, so Nat.div (n + 1) 2 is the ceiling of n/2. The outer division is in ℝ.

**Definition 1.6 (claim).**

$$claim = \forall (n : \mathbb{N}) , (3 \leq n) \to (\forall (theta : \mathbb{R}) , (((0 < theta) \land (theta \leq T\left(n\right))) \lor ((\operatorname{Real}.\operatorname{pi} - T\left(n\right) \leq theta) \land (theta < \operatorname{Real}.\operatorname{pi}))) \to (\forall (l : \mathbb{N}) , (l \leq n) \to ((IsMinOn\left((fun k : \mathbb{N} \mapsto ((rCount\left(n, \langle0\rangle, \langle1\rangle, k\right) : \mathbb{R}) + \operatorname{Real}.\operatorname{cos}\left(2 \cdot theta\right) \cdot (lCount\left(n, \langle0\rangle, \langle1\rangle, k\right) : \mathbb{R})) / ((rCount\left(n, \langle0\rangle, \langle1\rangle, k\right) : \mathbb{R}) + (lCount\left(n, \langle0\rangle, \langle1\rangle, k\right) : \mathbb{R}))), \operatorname{Set}.\operatorname{Iic}\left(n\right), l\right)) \to (\forall (phi : \left(Fin\left(n\right) \to Bool\right) \to \mathbb{C}) , (\forall (x : Fin\left(n\right) \to Bool) , \operatorname{Complex}.\operatorname{normSq}\left(phi\left(x\right)\right) = if \operatorname{Finset}.\operatorname{card}\left(\operatorname{Finset}.\operatorname{filter}\left((fun j : Fin\left(n\right) \mapsto x\left(j\right) = true), (\operatorname{Finset}.\operatorname{univ} : Finset\left(Fin\left(n\right)\right))\right)\right) = l then (1) / ((\operatorname{Nat}.\operatorname{choose}\left(n, l\right) : \mathbb{R})) else 0) \to (\forall (psi : \left(Fin\left(n\right) \to Bool\right) \to \mathbb{C}) , (\sum x : Fin\left(n\right) \to Bool , \operatorname{Complex}.\operatorname{normSq}\left(psi\left(x\right)\right) = 1) \to (\forall (M : LocalPOVM\left(Fin\left(n\right) \to Bool, Fin\left(n\right)\right)) , \exists (Mp : LocalPOVM\left(Fin\left(n\right) \to Bool, Fin\left(n\right)\right)) , isoSuccess\left(theta, psi, M\right) \leq isoSuccess\left(theta, phi, Mp\right)))))))$$

*Formalization.* `D5/S3/Quantum/Measurement/DetectorSensorDickeOptimality.claim` (`✓ std3`).

*Citation.* C. Zhan, H. Gupta, M. Hillery (2024). *Optimizing Initial State of Detector Sensors in Quantum Sensor Networks*. DOI: [10.1145/3655028](https://doi.org/10.1145/3655028). URL: <https://arxiv.org/abs/2306.17401v6>.

*Commentary.*

Section 5, Conjecture 1, page 10: “Consider the ISO problem, with the unitary operator 𝑈, initial state |𝜓⟩, and final states {|𝜙ᵢ⟩} as defined therein. Recall that the eigenvalues of 𝑈 are {𝑒^{+𝑖𝜃}, 𝑒^{−𝑖𝜃}}. Let 𝑛 ≥ 3 be the number of sensors. For a given 𝜃 ∈ (0,𝑇] ∪ [180 − 𝑇, 180), degrees, where 𝑇 is from Theorem 2, the optimal initial state |𝜓⟩ for the ISO problem is as follows. Let 𝑆ₗ be the partition that minimizes (𝑅ₗ + cos(2𝜃)𝐿ₗ)/(𝑅ₗ + 𝐿ₗ), where 𝑅ₗ and 𝐿ₗ are as defined in the previous section. The coefficients of the optimal solution are such that their coefficient-squares are given by: |𝜓ⱼ|² = 1/|𝑆ₗ| ∀ |𝜓ⱼ|² ∈ 𝑆ₗ  |𝜓ⱼ|² = 0 ∀ |𝜓ⱼ|² ∉ 𝑆ₗ” The formula uses radians, φ for the proposed state and ψ for a competitor. Each minimizing l and every assignment of coefficient phases are allowed. The words of weight l number Nat.choose n l. The two Fin n indices have values 0 and 1; their proof fields are omitted.

**Theorem 1.7 (result).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/DetectorSensorDickeOptimality.result` (`✓ std3`). ∎

*Resolves.* `Problems/zhan-gupta-hillery-2024-detector-sensor-dicke-optimality` (proved) by `D5/S3/Quantum/Measurement/DetectorSensorDickeOptimality.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"zhan-gupta-hillery-2024-detector-sensor-dicke-optimality","declaration_gid":"D5/S3/Quantum/Measurement/DetectorSensorDickeOptimality.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* C. Zhan, H. Gupta, M. Hillery (2024). *Optimizing Initial State of Detector Sensors in Quantum Sensor Networks*. DOI: [10.1145/3655028](https://doi.org/10.1145/3655028). URL: <https://arxiv.org/abs/2306.17401v6>.

*Commentary.*

Averaging a feasible Gram decomposition over sensor permutations preserves its objective and produces a real constant overlap. A positive semidefinite trace certificate bounds the objective by the squared diagonal of the Gram square root. This diagonal decreases with the overlap on the stated angle range. Every minimizing weight class reaches the smallest overlap, and a complete square-root measurement attains the bound. The argument allows arbitrary phases and every global POVM; it does not require the source’s stronger strict-averaging Conjecture 2.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/DetectorSensorDickeOptimality.T`
- Truth anchor: `D5/S3/Quantum/Measurement/DetectorSensorDickeOptimality.claim`
- Truth anchor: `D5/S3/Quantum/Measurement/DetectorSensorDickeOptimality.fire`
- Truth anchor: `D5/S3/Quantum/Measurement/DetectorSensorDickeOptimality.isoSuccess`
- Truth anchor: `D5/S3/Quantum/Measurement/DetectorSensorDickeOptimality.lCount`
- Truth anchor: `D5/S3/Quantum/Measurement/DetectorSensorDickeOptimality.rCount`
- Truth anchor: `D5/S3/Quantum/Measurement/DetectorSensorDickeOptimality.result`
- Dependency: [D5/S3/Quantum/Entanglement/TriangleIndependentSourceNoise](../Entanglement/TriangleIndependentSourceNoise.md)
- Dependency: [D5/S3/Quantum/Measurement/AntidistinguishabilityGram](AntidistinguishabilityGram.md)
- Dependency: [D5/S3/Quantum/Recovery/PurifiedLocalPath](../Recovery/PurifiedLocalPath.md)
- Dependency: [D5/S3/Quantum/Reduction/IsometricCompression](../Reduction/IsometricCompression.md)
