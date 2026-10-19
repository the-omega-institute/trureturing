# The exact three-coherence Ramsey threshold

## Abstract

The greatest third-moment Ramsey ratio for finite mixtures of unit vectors with at most three nonzero coordinates, over all finite dimensions, integer spectra and unit measurement vectors, is an attained algebraic value.

**Definition 1.1 (The pure Ramsey signal).**

$$\forall d \in \mathbb{N},\; \forall n \in \operatorname{Fin}\left(d\right) \to \mathbb{Z},\; \forall chi \in \operatorname{Fin}\left(d\right) \to \mathbb{C},\; \forall psi \in \operatorname{Fin}\left(d\right) \to \mathbb{C},\; \forall t \in \mathbb{R},\; \operatorname{signal}\left(n, chi, psi, t\right) = (\left|\sum_{j : \operatorname{Fin}\left(d\right)} (\overline{chi\left(j\right)} \cdot \exp\left(-\left((\operatorname{val}\left(n\left(j\right)\right): \mathbb{C}) \cdot (\operatorname{val}\left(t\right): \mathbb{C}) \cdot \operatorname{i}\right)\right) \cdot psi\left(j\right))\right|)^{2}$$

*Formalization.* `D5/S3/Quantum/Measurement/ThreeCoherenceRamseyThreshold.signal` (`✓ std3`).

*Citation.* Benjamin Dive; Nikolaos Koukoulekidis; Stefanos Mousafeiris; Florian Mintert (2020). *Characterisation of multi-level quantum coherence without ideal measurements*. DOI: [10.1103/PhysRevResearch.2.013220](https://doi.org/10.1103/PhysRevResearch.2.013220). URL: <https://arxiv.org/abs/1901.08599v3>.

*Commentary.*

For integer energy labels n and complex amplitude vectors chi and psi, the signal is p(t) = |Σ_j χ̄_j exp(−i n_j t) ψ_j|². Here chi denotes χ, psi denotes ψ, and i is the imaginary unit. The expressions val(n(j)) : ℂ and val(t) : ℂ are the canonical embeddings ℤ → ℂ and ℝ → ℂ, respectively. With unit vectors this is the probability of the rank-one measurement onto χ after the evolution of ψ. The expression itself is defined for arbitrary vectors. This is the pure-state interference pattern of page 2 with the Hamiltonian of Eq. (1).

**Definition 1.2 (Finite mixtures of pure signals).**

$$\forall d \in \mathbb{N},\; \forall L \in \mathbb{N},\; \forall n \in \operatorname{Fin}\left(d\right) \to \mathbb{Z},\; \forall chi \in \operatorname{Fin}\left(d\right) \to \mathbb{C},\; \forall psi \in \operatorname{Fin}\left(L\right) \to \left(\operatorname{Fin}\left(d\right) \to \mathbb{C}\right),\; \forall w \in \operatorname{Fin}\left(L\right) \to \mathbb{R},\; \forall t \in \mathbb{R},\; \operatorname{mixedSignal}\left(n, chi, psi, w, t\right) = \sum_{l : \operatorname{Fin}\left(L\right)} (w\left(l\right) \cdot \operatorname{signal}\left(n, chi, psi\left(l\right), t\right))$$

*Formalization.* `D5/S3/Quantum/Measurement/ThreeCoherenceRamseyThreshold.mixedSignal` (`✓ std3`).

*Citation.* Benjamin Dive; Nikolaos Koukoulekidis; Stefanos Mousafeiris; Florian Mintert (2020). *Characterisation of multi-level quantum coherence without ideal measurements*. DOI: [10.1103/PhysRevResearch.2.013220](https://doi.org/10.1103/PhysRevResearch.2.013220). URL: <https://arxiv.org/abs/1901.08599v3>.

*Commentary.*

The function is the finite sum Σ_l w_l p_l(t), where p_l(t) = signal n chi (psi l) t. For nonnegative weights summing to one it is the interference pattern of the state Σ_l w_l |ψ_l⟩⟨ψ_l| with the same χ and Hamiltonian throughout. The definition also permits arbitrary real weights. This restates the mixed-state signal in Eq. (2).

**Definition 1.3 (Moments over one period).**

$$\forall q \in \mathbb{N},\; \forall p \in \mathbb{R} \to \mathbb{R},\; \operatorname{moment}\left(q, p\right) = \frac{1}{2 \cdot \pi} \cdot \int_{0}^{2 \cdot \pi} (p\left(t\right))^{q} \mathrm{d}t$$

*Formalization.* `D5/S3/Quantum/Measurement/ThreeCoherenceRamseyThreshold.moment` (`✓ std3`).

*Citation.* Benjamin Dive; Nikolaos Koukoulekidis; Stefanos Mousafeiris; Florian Mintert (2020). *Characterisation of multi-level quantum coherence without ideal measurements*. DOI: [10.1103/PhysRevResearch.2.013220](https://doi.org/10.1103/PhysRevResearch.2.013220). URL: <https://arxiv.org/abs/1901.08599v3>.

*Commentary.*

Write M_q(p) = moment q p. Eq. (2) defines M_q(p) = (1/(2π))∫₀^{2π} p(t)^q dt. The definition has a natural exponent and an arbitrary real function; continuity and positivity are properties of the Ramsey signals used below, rather than assumptions of this definition.

**Definition 1.4 (The third-moment ratio).**

$$\forall p \in \mathbb{R} \to \mathbb{R},\; \operatorname{ratio3}\left(p\right) = \frac{\operatorname{moment}\left(3, p\right)}{(\operatorname{moment}\left(1, p\right))^{2}}$$

*Formalization.* `D5/S3/Quantum/Measurement/ThreeCoherenceRamseyThreshold.ratio3` (`✓ std3`).

*Citation.* Benjamin Dive; Nikolaos Koukoulekidis; Stefanos Mousafeiris; Florian Mintert (2020). *Characterisation of multi-level quantum coherence without ideal measurements*. DOI: [10.1103/PhysRevResearch.2.013220](https://doi.org/10.1103/PhysRevResearch.2.013220). URL: <https://arxiv.org/abs/1901.08599v3>.

*Commentary.*

Write R₃(p) = ratio3 p. This is M₃(p)/M₁(p)², the case n = 3 of Eq. (3). The quotient is defined for every real function. Only signals with M₁ > 0 enter the set of values to be maximized.

**Definition 1.5 (At most three occupied coordinates).**

$$\forall d \in \mathbb{N},\; \forall psi \in \operatorname{Fin}\left(d\right) \to \mathbb{C},\; (\operatorname{IsThreeSparse}\left(psi\right)) \Leftrightarrow (\left|\{j : \operatorname{Fin}\left(d\right) \mid psi\left(j\right) \ne 0\}\right| \le 3)$$

*Formalization.* `D5/S3/Quantum/Measurement/ThreeCoherenceRamseyThreshold.IsThreeSparse` (`✓ std3`).

*Citation.* Benjamin Dive; Nikolaos Koukoulekidis; Stefanos Mousafeiris; Florian Mintert (2020). *Characterisation of multi-level quantum coherence without ideal measurements*. DOI: [10.1103/PhysRevResearch.2.013220](https://doi.org/10.1103/PhysRevResearch.2.013220). URL: <https://arxiv.org/abs/1901.08599v3>.

*Commentary.*

The vertical bars on the finite set denote its cardinality. At most three coordinates of ψ are nonzero. By the page-1 definition of k-coherence, mixtures of such vectors are the states that are not four-coherent, as used in the k = 3 row of Table I.

**Definition 1.6 (Unit amplitude vectors).**

$$\forall d \in \mathbb{N},\; \forall psi \in \operatorname{Fin}\left(d\right) \to \mathbb{C},\; (\operatorname{IsUnitVector}\left(psi\right)) \Leftrightarrow (\sum_{j : \operatorname{Fin}\left(d\right)} ((\left|psi\left(j\right)\right|)^{2}) = 1)$$

*Formalization.* `D5/S3/Quantum/Measurement/ThreeCoherenceRamseyThreshold.IsUnitVector` (`✓ std3`).

*Citation.* Benjamin Dive; Nikolaos Koukoulekidis; Stefanos Mousafeiris; Florian Mintert (2020). *Characterisation of multi-level quantum coherence without ideal measurements*. DOI: [10.1103/PhysRevResearch.2.013220](https://doi.org/10.1103/PhysRevResearch.2.013220). URL: <https://arxiv.org/abs/1901.08599v3>.

*Commentary.*

The squared complex moduli sum to one. This is the normalization of the state and measurement vectors in the interference pattern of Eqs. (1)–(3).

**Definition 1.7 (All admissible third-moment ratios).**

$$\operatorname{admissibleValues} = \{v : \mathbb{R} \mid \exists d \in \mathbb{N},\; \exists L \in \mathbb{N},\; \exists n \in \operatorname{Fin}\left(d\right) \to \mathbb{Z},\; \exists chi \in \operatorname{Fin}\left(d\right) \to \mathbb{C},\; \exists psi \in \operatorname{Fin}\left(L\right) \to \left(\operatorname{Fin}\left(d\right) \to \mathbb{C}\right),\; \exists w \in \operatorname{Fin}\left(L\right) \to \mathbb{R},\; (\operatorname{IsUnitVector}\left(chi\right)) \land ((\forall l \in \operatorname{Fin}\left(L\right),\; (\operatorname{IsUnitVector}\left(psi\left(l\right)\right)) \land (\operatorname{IsThreeSparse}\left(psi\left(l\right)\right))) \land ((\forall l \in \operatorname{Fin}\left(L\right),\; 0 \le w\left(l\right)) \land ((\sum_{l : \operatorname{Fin}\left(L\right)} (w\left(l\right)) = 1) \land ((0 < \operatorname{moment}\left(1, \operatorname{mixedSignal}\left(n, chi, psi, w\right)\right)) \land (v = \operatorname{ratio3}\left(\operatorname{mixedSignal}\left(n, chi, psi, w\right)\right))))))\}$$

*Formalization.* `D5/S3/Quantum/Measurement/ThreeCoherenceRamseyThreshold.admissibleValues` (`✓ std3`).

*Citation.* Benjamin Dive; Nikolaos Koukoulekidis; Stefanos Mousafeiris; Florian Mintert (2020). *Characterisation of multi-level quantum coherence without ideal measurements*. DOI: [10.1103/PhysRevResearch.2.013220](https://doi.org/10.1103/PhysRevResearch.2.013220). URL: <https://arxiv.org/abs/1901.08599v3>.

*Commentary.*

The set ranges over every finite dimension d, every finite mixture size L, every integer energy assignment n, every unit measurement vector χ, and every mixture of unit vectors with at most three nonzero coordinates. Its weights are nonnegative and sum to one, and its first moment is positive. Repeated energy labels are allowed. This is the optimization in the k = 3 row of Table I, using Eqs. (1)–(3) and the page-1 definition of coherence. In that table the row k concerns states that are not (k + 1)-coherent.

**Definition 1.8 (The numerator polynomial).**

$$\forall r \in \mathbb{R},\; \operatorname{thresholdN}\left(r\right) = (r)^{6} + 30 \cdot (r)^{4} + 90 \cdot (r)^{2} + 20$$

*Formalization.* `D5/S3/Quantum/Measurement/ThreeCoherenceRamseyThreshold.thresholdN` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Benjamin Dive; Nikolaos Koukoulekidis; Stefanos Mousafeiris; Florian Mintert (2020). *Characterisation of multi-level quantum coherence without ideal measurements*. DOI: [10.1103/PhysRevResearch.2.013220](https://doi.org/10.1103/PhysRevResearch.2.013220). URL: <https://arxiv.org/abs/1901.08599v3>.

*Commentary.*

Write N(r) = thresholdN r. This polynomial is the numerator of the ratio for the equally spaced, symmetric three-level family, extending the optimization of Table I.

**Definition 1.9 (The denominator polynomial).**

$$\forall r \in \mathbb{R},\; \operatorname{thresholdD}\left(r\right) = (r + 2)^{2} \cdot ((r)^{2} + 2)^{2}$$

*Formalization.* `D5/S3/Quantum/Measurement/ThreeCoherenceRamseyThreshold.thresholdD` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Benjamin Dive; Nikolaos Koukoulekidis; Stefanos Mousafeiris; Florian Mintert (2020). *Characterisation of multi-level quantum coherence without ideal measurements*. DOI: [10.1103/PhysRevResearch.2.013220](https://doi.org/10.1103/PhysRevResearch.2.013220). URL: <https://arxiv.org/abs/1901.08599v3>.

*Commentary.*

Write D(r) = thresholdD r. It is positive for r ≥ 0 and is the denominator of the symmetric family's third-moment ratio.

**Definition 1.10 (The stationary-point polynomial).**

$$\forall r \in \mathbb{R},\; \operatorname{thresholdP}\left(r\right) = (r)^{7} - 13 \cdot (r)^{6} + 6 \cdot (r)^{5} - 60 \cdot (r)^{4} + 30 \cdot (r)^{3} - 30 \cdot (r)^{2} + 140 \cdot r - 20$$

*Formalization.* `D5/S3/Quantum/Measurement/ThreeCoherenceRamseyThreshold.thresholdP` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Benjamin Dive; Nikolaos Koukoulekidis; Stefanos Mousafeiris; Florian Mintert (2020). *Characterisation of multi-level quantum coherence without ideal measurements*. DOI: [10.1103/PhysRevResearch.2.013220](https://doi.org/10.1103/PhysRevResearch.2.013220). URL: <https://arxiv.org/abs/1901.08599v3>.

*Commentary.*

Write P(r) = thresholdP r. For r ≥ 0, differentiation gives (N/D)′(r) = 4P(r)/((r + 2)³(r² + 2)³). Its root in the stated rational interval determines the exact maximum sought in Table I.

**Definition 1.11 (The attained algebraic maximum).**

$$(\operatorname{claim}) \Leftrightarrow (\exists alpha \in \mathbb{R},\; (\frac{6169}{5000} < alpha) \land ((alpha < \frac{12339}{10000}) \land ((\operatorname{thresholdP}\left(alpha\right) = 0) \land (\operatorname{IsGreatest}\left(\operatorname{admissibleValues}, \frac{\operatorname{thresholdN}\left(alpha\right)}{\operatorname{thresholdD}\left(alpha\right)}\right)))))$$

*Formalization.* `D5/S3/Quantum/Measurement/ThreeCoherenceRamseyThreshold.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Benjamin Dive; Nikolaos Koukoulekidis; Stefanos Mousafeiris; Florian Mintert (2020). *Characterisation of multi-level quantum coherence without ideal measurements*. DOI: [10.1103/PhysRevResearch.2.013220](https://doi.org/10.1103/PhysRevResearch.2.013220). URL: <https://arxiv.org/abs/1901.08599v3>.

*Commentary.*

There is an α in (6169/5000, 12339/10000) with P(α) = 0 such that N(α)/D(α) is the greatest element of admissibleValues. Being greatest includes both membership and an upper bound for every member. Table I gives the analytic upper bound 179/96 and a numerical value 1.77 for this row; the present value specifies the attained maximum exactly.

**Theorem 1.12 (The sharp threshold is attained).**

$$\operatorname{claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/ThreeCoherenceRamseyThreshold.result` (`✓ std3`). ∎

*Resolves.* `Problems/dive-koukoulekidis-mousafeiris-mintert-2020-three-coherence-ramsey-threshold` (proved) by `D5/S3/Quantum/Measurement/ThreeCoherenceRamseyThreshold.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"dive-koukoulekidis-mousafeiris-mintert-2020-three-coherence-ramsey-threshold","declaration_gid":"D5/S3/Quantum/Measurement/ThreeCoherenceRamseyThreshold.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Benjamin Dive; Nikolaos Koukoulekidis; Stefanos Mousafeiris; Florian Mintert (2020). *Characterisation of multi-level quantum coherence without ideal measurements*. DOI: [10.1103/PhysRevResearch.2.013220](https://doi.org/10.1103/PhysRevResearch.2.013220). URL: <https://arxiv.org/abs/1901.08599v3>.

*Commentary.*

Convexity of x ↦ x³ reduces the mixture bound to pure inputs. Weighting by the first moments gives the bound M₃ ≤ T M₁² for a mixture whenever it holds for each pure signal. Replacing each first moment by M₁ + ε and taking ε down to zero includes components whose first moment vanishes.

For a pure input put z_j = χ̄_j ψ_j, and combine equal energies into Z_e = Σ_{j:n_j=e} z_j. Cauchy–Schwarz and the unit-vector assumptions give Σ_e |Z_e| ≤ Σ_j |z_j| ≤ 1, with at most three nonzero grouped coefficients. Fourier orthogonality gives M₁ = Σ_e |Z_e|² and M₃ = Σ_h |Σ_{e₁+e₂+e₃=h} Z_{e₁}Z_{e₂}Z_{e₃}|². Taking absolute values and normalizing their sum to one can only increase the ratio; a zero sum gives the zero signal. Thus consider a, b, c ≥ 0 with a + b + c = 1.

For three distinct ordered energies with gaps x and z, collisions between different cubic monomials occur only when x = z, x = 2z or z = 2x. The inequalities 3a² + 2b² + 3c² ≥ ab and 3a² + 2b² + 3c² ≥ bc show that the equal-spacing case bounds both other collision cases and the case with no extra collision. One or two distinct energies give a ratio at most 5/4.

At equal spacing put u = a² + b² + c², X = b(a + c) and Y = ac. The ratio is u + 6(X² + Y²)/u + 6X²Y/u². At fixed b, set A = (1 − b)² + b² and B = b²(1 − b)². The same expression is (5/2)u − 3A + (3/2)(A² + 2B)/u + 3AB/u², convex for u > 0. Its feasible interval has endpoints u = b² + (1 − b)²/2 and u = A. The first has a = c; the second has ac = 0 and ratio at most 5/4. In the symmetric case a = c = 1/(r + 2), b = r/(r + 2), the ratio is N(r)/D(r). The case b = 1 has ratio one.

The intermediate value theorem supplies α in the stated interval with P(α) = 0. Put T = N(α)/D(α). Rational estimates give T > 177/100 > 5/4 and the identity T D(r) − N(r) = (r − α)²Q(r), where Q(r) = (T − 1)r⁴ + (4T + 2α(T − 1))r³ + (8T − 30 + 8αT + 3α²(T − 1))r² + (16T + 16αT − 60α + 12α²T + 4α³(T − 1))r + 20T − 90 + 32αT + (24T − 90)α² + 16Tα³ + 5(T − 1)α⁴. The bounds 123/100 < α < 31/25 and T > 177/100 make all five coefficients positive. Hence Q(r) > 0 for r ≥ 0 and N(r)/D(r) ≤ T.

For attainment take the energies 0, 1, 2 and ψ = χ with populations (1, α, 1)/(α + 2), namely amplitudes (√(1/(α + 2)), √(α/(α + 2)), √(1/(α + 2))). A single pure component of weight one has positive first moment and ratio T. Thus T belongs to admissibleValues and bounds every admissible value above.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/ThreeCoherenceRamseyThreshold.IsThreeSparse`
- Truth anchor: `D5/S3/Quantum/Measurement/ThreeCoherenceRamseyThreshold.IsUnitVector`
- Truth anchor: `D5/S3/Quantum/Measurement/ThreeCoherenceRamseyThreshold.admissibleValues`
- Truth anchor: `D5/S3/Quantum/Measurement/ThreeCoherenceRamseyThreshold.claim`
- Truth anchor: `D5/S3/Quantum/Measurement/ThreeCoherenceRamseyThreshold.mixedSignal`
- Truth anchor: `D5/S3/Quantum/Measurement/ThreeCoherenceRamseyThreshold.moment`
- Truth anchor: `D5/S3/Quantum/Measurement/ThreeCoherenceRamseyThreshold.ratio3`
- Truth anchor: `D5/S3/Quantum/Measurement/ThreeCoherenceRamseyThreshold.result`
- Truth anchor: `D5/S3/Quantum/Measurement/ThreeCoherenceRamseyThreshold.signal`
- Truth anchor: `D5/S3/Quantum/Measurement/ThreeCoherenceRamseyThreshold.thresholdD`
- Truth anchor: `D5/S3/Quantum/Measurement/ThreeCoherenceRamseyThreshold.thresholdN`
- Truth anchor: `D5/S3/Quantum/Measurement/ThreeCoherenceRamseyThreshold.thresholdP`
- Dependency: [D5/S3/Quantum/Measurements/IQP/LidarRestrictedAnticoncentrationRefutation](../Measurements/IQP/LidarRestrictedAnticoncentrationRefutation.md)
