# Tightness of the higher-order EPR bound

## Abstract

The zero higher-order EPR bound is tight for both signs at every positive order.

**Definition 1.1 (Squared occupation-basis norm).**

$$\forall \left(\psi: \operatorname{Finsupp}\left(\left(\mathbb{N} \times \mathbb{N}\right), \mathbb{C}\right)\right), \left(\left(\operatorname{D5.S3.Quantum.FockSpace.HigherOrderEPRTightness.normSq}\left(\psi\right): \mathbb{R}\right) = \operatorname{Finsupp.sum}\left(\psi, \operatorname{Function.const}\left(\mathbb{N} \times \mathbb{N}, \left(\lambda \left(z: \mathbb{C}\right) \mapsto \left(\left\lVert z \right\rVert^{2}\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/FockSpace/HigherOrderEPRTightness.normSq` (`✓ std3`).

*Citation.* E. Shchukin and P. van Loock (2016). *Higher-order Einstein-Podolsky-Rosen correlations and inseparability conditions for continuous variables*. DOI: [10.1103/PhysRevA.93.032114](https://doi.org/10.1103/PhysRevA.93.032114). URL: <https://arxiv.org/abs/1511.08444v1>.

*Commentary.*

A finitely supported complex function on pairs of natural occupation numbers represents a two-mode state. Its squared norm is the finite sum of the squared absolute values of its amplitudes. This is the usual occupation-basis norm used in the source's normalization equation in bip-ent2.tex, lines 925–934, restricted here to finite support.

**Definition 1.2 (Annihilation in the first mode).**

$$\forall \left(n: \mathbb{N}\right), \left(\operatorname{D5.S3.Quantum.FockSpace.HigherOrderEPRTightness.annihilateA}\left(n\right) = \operatorname{Finsupp.linearCombination}\left(\mathbb{C}, \left(\lambda \left(p: \mathbb{N} \times \mathbb{N}\right) \mapsto \left(\operatorname{ite}\left(n \le \operatorname{Prod.fst}\left(p\right), \operatorname{Finsupp.single}\left(\left(\operatorname{Prod.fst}\left(p\right) - n, \operatorname{Prod.snd}\left(p\right)\right), \operatorname{Complex.ofReal}\left(\operatorname{Real.sqrt}\left(\frac{\left(\operatorname{Nat.cast}\left(\operatorname{Nat.factorial}\left(\operatorname{Prod.fst}\left(p\right)\right)\right): \mathbb{R}\right)}{\left(\operatorname{Nat.cast}\left(\operatorname{Nat.factorial}\left(\operatorname{Prod.fst}\left(p\right) - n\right)\right): \mathbb{R}\right)}\right)\right)\right), \left(0: \operatorname{Finsupp}\left(\left(\mathbb{N} \times \mathbb{N}\right), \mathbb{C}\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/FockSpace/HigherOrderEPRTightness.annihilateA` (`✓ std3`).

*Citation.* E. Shchukin and P. van Loock (2016). *Higher-order Einstein-Podolsky-Rosen correlations and inseparability conditions for continuous variables*. DOI: [10.1103/PhysRevA.93.032114](https://doi.org/10.1103/PhysRevA.93.032114). URL: <https://arxiv.org/abs/1511.08444v1>.

*Commentary.*

The nth power of first-mode annihilation sends the basis state at p to the state with n fewer first-mode quanta, multiplied by the square root of the falling factorial. It vanishes when the first occupation is less than n. Finsupp.linearCombination extends this basis action complex linearly. These are the annihilation powers in the source's higher-order expression, bip-ent2.tex, lines 914–922. Both factorials are cast from natural to real numbers before division, and the real square root is then included in the complex numbers.

**Definition 1.3 (Creation in the second mode).**

$$\forall \left(n: \mathbb{N}\right), \left(\operatorname{D5.S3.Quantum.FockSpace.HigherOrderEPRTightness.createB}\left(n\right) = \operatorname{Finsupp.linearCombination}\left(\mathbb{C}, \left(\lambda \left(p: \mathbb{N} \times \mathbb{N}\right) \mapsto \left(\operatorname{Finsupp.single}\left(\left(\operatorname{Prod.fst}\left(p\right), \operatorname{Prod.snd}\left(p\right) + n\right), \operatorname{Complex.ofReal}\left(\operatorname{Real.sqrt}\left(\frac{\left(\operatorname{Nat.cast}\left(\operatorname{Nat.factorial}\left(\operatorname{Prod.snd}\left(p\right) + n\right)\right): \mathbb{R}\right)}{\left(\operatorname{Nat.cast}\left(\operatorname{Nat.factorial}\left(\operatorname{Prod.snd}\left(p\right)\right)\right): \mathbb{R}\right)}\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/FockSpace/HigherOrderEPRTightness.createB` (`✓ std3`).

*Citation.* E. Shchukin and P. van Loock (2016). *Higher-order Einstein-Podolsky-Rosen correlations and inseparability conditions for continuous variables*. DOI: [10.1103/PhysRevA.93.032114](https://doi.org/10.1103/PhysRevA.93.032114). URL: <https://arxiv.org/abs/1511.08444v1>.

*Commentary.*

The nth power of second-mode creation adds n to the second occupation and multiplies the amplitude by the square root of the rising factorial. Its complex linear extension acts on all finitely supported states. This is the creation power in bip-ent2.tex, lines 914–922. As for annihilation, the factorial ratio is real and its square root is explicitly included in the complex numbers.

**Definition 1.4 (Tightness for every positive order).**

$$\operatorname{D5.S3.Quantum.FockSpace.HigherOrderEPRTightness.claim} \Leftrightarrow \left(\forall \left(n: \mathbb{N}\right), \left(\left(\left(1: \mathbb{N}\right) \le n\right) \to \left(\forall \left(\sigma: \mathbb{C}\right), \left(\left(\sigma = \left(1: \mathbb{C}\right) \lor \sigma = -\left(1: \mathbb{C}\right)\right) \to \left(\forall \left(\varepsilon: \mathbb{R}\right), \left(\left(\left(0: \mathbb{R}\right) < \varepsilon\right) \to \left(\exists \left(\psi: \operatorname{Finsupp}\left(\left(\mathbb{N} \times \mathbb{N}\right), \mathbb{C}\right)\right), \left(\operatorname{D5.S3.Quantum.FockSpace.HigherOrderEPRTightness.normSq}\left(\psi\right) = \left(1: \mathbb{R}\right) \land \operatorname{D5.S3.Quantum.FockSpace.HigherOrderEPRTightness.normSq}\left(\operatorname{D5.S3.Quantum.FockSpace.HigherOrderEPRTightness.annihilateA}\left(n, \psi\right) + \operatorname{HSMul.hSMul}\left(\sigma, \operatorname{D5.S3.Quantum.FockSpace.HigherOrderEPRTightness.createB}\left(n, \psi\right)\right)\right) < \varepsilon\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/FockSpace/HigherOrderEPRTightness.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* E. Shchukin and P. van Loock (2016). *Higher-order Einstein-Podolsky-Rosen correlations and inseparability conditions for continuous variables*. DOI: [10.1103/PhysRevA.93.032114](https://doi.org/10.1103/PhysRevA.93.032114). URL: <https://arxiv.org/abs/1511.08444v1>.

*Commentary.*

For every positive natural order n, either complex sign σ, and every positive real ε, there is a finitely supported state ψ of squared norm one whose image under the signed sum of the two operator powers has squared norm below ε. The source states the nonnegative bound in bip-ent2.tex, lines 914–924, and asks for its tightness at lines 961–963. The formula expresses that question using finite occupation-basis states and a squared norm. It makes no assertion about Gaussian states or about whether zero can be attained.

**Theorem 1.5 (Normalized finite states approach zero).**

$$\forall \left(n: \mathbb{N}\right), \left(\left(\left(1: \mathbb{N}\right) \le n\right) \to \left(\forall \left(\sigma: \mathbb{C}\right), \left(\left(\sigma = \left(1: \mathbb{C}\right) \lor \sigma = -\left(1: \mathbb{C}\right)\right) \to \left(\forall \left(\varepsilon: \mathbb{R}\right), \left(\left(\left(0: \mathbb{R}\right) < \varepsilon\right) \to \left(\exists \left(\psi: \operatorname{Finsupp}\left(\left(\mathbb{N} \times \mathbb{N}\right), \mathbb{C}\right)\right), \left(\operatorname{D5.S3.Quantum.FockSpace.HigherOrderEPRTightness.normSq}\left(\psi\right) = \left(1: \mathbb{R}\right) \land \operatorname{D5.S3.Quantum.FockSpace.HigherOrderEPRTightness.normSq}\left(\operatorname{D5.S3.Quantum.FockSpace.HigherOrderEPRTightness.annihilateA}\left(n, \psi\right) + \operatorname{HSMul.hSMul}\left(\sigma, \operatorname{D5.S3.Quantum.FockSpace.HigherOrderEPRTightness.createB}\left(n, \psi\right)\right)\right) < \varepsilon\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FockSpace/HigherOrderEPRTightness.result` (`✓ std3`). ∎

*Resolves.* `Problems/shchukin-van-loock-2016-higher-order-epr-tightness` (proved) by `D5/S3/Quantum/FockSpace/HigherOrderEPRTightness.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"shchukin-van-loock-2016-higher-order-epr-tightness","declaration_gid":"D5/S3/Quantum/FockSpace/HigherOrderEPRTightness.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* E. Shchukin and P. van Loock (2016). *Higher-order Einstein-Podolsky-Rosen correlations and inseparability conditions for continuous variables*. DOI: [10.1103/PhysRevA.93.032114](https://doi.org/10.1103/PhysRevA.93.032114). URL: <https://arxiv.org/abs/1511.08444v1>.

*Commentary.*

Multiplication of a state by a complex scalar multiplies its squared norm by the squared absolute value of that scalar. For a finite sum of single-site states at distinct occupation pairs, the squared norm is the sum of the squared absolute values of their amplitudes.

Write Hₖ for the kth harmonic number, regarded as real. For a positive natural m set fₖ = 1 − Hₖ/Hₘ and cₖ = √((nk)!/(nk+n−1)!). Let v be the finite sum, for 0 ≤ k ≤ m, of the basis states at (nk+n−1,nk) with complex amplitudes (−σ)ᵏfₖcₖ. For positive r the factorial identity r! = r(r−1)! gives √(t!/(r−1)!) √(r!/t!) = √r. Applying this identity to the two operator actions shows that annihilation of the term at k+1 and creation of the term at k both reach (n(k+1)−1,n(k+1)), with the same factorial factor √(n(k+1)).

Annihilation kills the initial term because its first occupation is n−1, and fₘ = 0 removes the final creation term. Thus annihilateA n v + σ • createB n v is the sum, for 0 ≤ k < m, of single-site states at (n(k+1)−1,n(k+1)) with amplitudes (−σ)ᵏ⁺¹√(n(k+1))(fₖ₊₁−fₖ). The harmonic recurrence gives fₖ₊₁−fₖ = −1/((k+1)Hₘ). Squaring the real factors and summing gives ∑ₖ₌₀ᵐ⁻¹ n(k+1)(fₖ₊₁−fₖ)² = (n/Hₘ²)∑ₖ₌₀ᵐ⁻¹ 1/(k+1) = n/Hₘ.

Because n is positive, the occupation pairs of v are distinct. The k = 0 term has squared amplitude 1/(n−1)!, so Z = normSq v is at least 1/(n−1)! and is strictly positive. The output occupation pairs are also distinct. For σ equal to 1 or −1, the factors (−σ)ᵏ⁺¹ have absolute value one. The preceding sum therefore proves that the squared norm of the unnormalized output is exactly n/Hₘ.

The harmonic numbers are unbounded: the partial sums of 1/(k+1) tend to positive infinity. Hence for every real b there is a natural m at least one with Hₘ > b. For any state v with positive squared norm Z, multiplication by the real scalar 1/√Z, included in the complex numbers, produces a state ψ of squared norm one. Linearity of both operators and the squared-norm scaling identity show that the squared norm of its output is the squared norm of the output of v divided by Z.

Now fix n ≥ 1, σ equal to either sign, and ε > 0. Choose m ≥ 1 with Hₘ > n!/ε and form the finite state v above. Its lower norm bound permits normalization. The resulting ψ has squared norm one and output squared norm n/(HₘZ). Using Z ≥ 1/(n−1)! and n! = n(n−1)! gives n/(HₘZ) ≤ n!/Hₘ < ε. This establishes the stated approximation for every order and both signs.

## References

- Truth anchor: `D5/S3/Quantum/FockSpace/HigherOrderEPRTightness.annihilateA`
- Truth anchor: `D5/S3/Quantum/FockSpace/HigherOrderEPRTightness.claim`
- Truth anchor: `D5/S3/Quantum/FockSpace/HigherOrderEPRTightness.createB`
- Truth anchor: `D5/S3/Quantum/FockSpace/HigherOrderEPRTightness.normSq`
- Truth anchor: `D5/S3/Quantum/FockSpace/HigherOrderEPRTightness.result`
