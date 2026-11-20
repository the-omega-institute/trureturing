# The entropy dichotomy fails for finite-monoid cellular automata

## Abstract

A Boolean OR automaton refutes the finite-monoid entropy dichotomy.

Castronuovo, Dennunzio, Kari and Margara ask in arXiv:2611.16746v1, §9, second research direction, printed p. 32. “It would be interesting to understand whether the dichotomy extends to cellular automata over finite monoids, and more generally which algebraic constraints force it.” The settling proposition is the first clause, with both alternatives of Theorem 6 (p. 21) retained.

**Definition 1.1 (The finite-monoid extension of Theorem 6).**

$$\begin{aligned}\forall D: \mathbb{N}, 2 \le D \Rightarrow \forall A: Type, [\operatorname{Fintype} A] [\operatorname{Monoid} A],\\\operatorname{letI} : \operatorname{UniformSpace} A := \perp;\\\forall F: ((\operatorname{Fin} D \to \mathbb{Z}) \to A) \to^{*} ((\operatorname{Fin} D \to \mathbb{Z}) \to A),\\(\exists W: \operatorname{Finset} (\operatorname{Fin} D \to \mathbb{Z}), rule: (W \to A) \to A, F = \operatorname{localMap} W rule) \Rightarrow\\\operatorname{Continuous} F \Rightarrow\\(\forall u: (\operatorname{Fin} D \to \mathbb{Z}), \forall x: ((\operatorname{Fin} D \to \mathbb{Z}) \to A), F (\operatorname{shift} u x) = \operatorname{shift} u (F x)) \Rightarrow\\(\operatorname{UniformEquicontinuous} (\operatorname{fun} k: \mathbb{N} \mapsto F^{[k]}) \land \operatorname{coverEntropy} F \operatorname{Set}.\operatorname{univ} = 0) \lor\\(\operatorname{sensitive} F \land \operatorname{coverEntropy} F \operatorname{Set}.\operatorname{univ} = \infty)\end{aligned}$$

*Formalization.* `D5/S1/Dynamics/Symbolic/MonoidCADichotomyRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Niccolò Castronuovo and Alberto Dennunzio and Jarkko Kari and Luciano Margara (2026). *Topological Entropy of Group Cellular Automata is Effectively Computable*. URL: <https://arxiv.org/abs/2611.16746v1>.

*Commentary.*

A ranges over Type with Fintype and Monoid instances. The alphabet carries the discrete uniformity, the bottom UniformSpace instance, and the configuration space carries its product uniformity. The domain contains every function from Fin D → ℤ to A. The bundled MonoidHom preserves pointwise multiplication and the constant-one configuration. A finite set W supplies the offsets, and localMap reads rule on the translated window. Shift uses z ↦ z + u. Continuity and commutation with every shift are stated separately.

For each natural radius r, the source distance is strictly below 2⁻ʳ exactly when the two configurations agree on the centered box [−r,r] in each coordinate. The boxes contain every finite window at some radius, so their agreement relations are cofinal entourages. This identifies uniform equicontinuity of the natural iterates and sensitivity with the source quantifiers, including the strict input bound and the weak separation bound. The time index starts at zero.

At a box scale and time length n, the dynamical entourage is equality of box traces at times 0 through n − 1. A minimum spanning cover takes one representative per realized trace. A maximum separated set also takes one per trace, using the source's weak separation inequality at the same scale. Taking the normalized logarithmic upper limits and the supremum over the cofinal box scales identifies coverEntropy on Set.univ with the source entropy. A source trace that ends at time t has length n = t + 1. The infinite value in the display is Top.top in EReal.

**Theorem 1.2 (The Boolean OR counterexample).**

$$\neg \left(\begin{aligned}\forall D: \mathbb{N}, 2 \le D \Rightarrow \forall A: Type, [\operatorname{Fintype} A] [\operatorname{Monoid} A],\\\operatorname{letI} : \operatorname{UniformSpace} A := \perp;\\\forall F: ((\operatorname{Fin} D \to \mathbb{Z}) \to A) \to^{*} ((\operatorname{Fin} D \to \mathbb{Z}) \to A),\\(\exists W: \operatorname{Finset} (\operatorname{Fin} D \to \mathbb{Z}), rule: (W \to A) \to A, F = \operatorname{localMap} W rule) \Rightarrow\\\operatorname{Continuous} F \Rightarrow\\(\forall u: (\operatorname{Fin} D \to \mathbb{Z}), \forall x: ((\operatorname{Fin} D \to \mathbb{Z}) \to A), F (\operatorname{shift} u x) = \operatorname{shift} u (F x)) \Rightarrow\\(\operatorname{UniformEquicontinuous} (\operatorname{fun} k: \mathbb{N} \mapsto F^{[k]}) \land \operatorname{coverEntropy} F \operatorname{Set}.\operatorname{univ} = 0) \lor\\(\operatorname{sensitive} F \land \operatorname{coverEntropy} F \operatorname{Set}.\operatorname{univ} = \infty)\end{aligned}\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/MonoidCADichotomyRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Niccolò Castronuovo and Alberto Dennunzio and Jarkko Kari and Luciano Margara (2026). *Topological Entropy of Group Cellular Automata is Effectively Computable*. URL: <https://arxiv.org/abs/2611.16746v1>.

*Commentary.*

The Lean theorem has the literal type ¬ claim. Take D = 2 and Bool with Bool.or as multiplication and false as its unit. At z the map takes the OR of x(z), x(z + e₁) and x(z + e₂). The local lift is continuous, commutes with every shift, and preserves the unit and multiplication. Each of e₁ and e₂ is essential. Flipping the corresponding site alone in the all-false configuration changes the output at the origin.

For any input box of radius r, a single true at (r + 1)e₁ agrees with the all-false configuration throughout that box. It reaches the origin after r + 1 steps, while the all-false configuration stays fixed. This contradicts equicontinuity. Independently, true persists at each site, and the all-true configuration is fixed. Agreement with it on any fixed box therefore persists at every time, which rules out sensitivity.

In a trace of length n each Boolean coordinate has at most one transition from false to true. Its first true time, with n for a trace that stays false, gives at most n + 1 choices. The number of traces on W is at most (n + 1) to the power |W|. Its normalized logarithm goes to zero for each fixed W. The cover-entropy supremum over boxes is zero. Propagation excludes the equicontinuous alternative, and zero entropy excludes the infinite-entropy alternative. Zero entropy and the same failure of equicontinuity also contradict the zero-entropy entry of Table 2 (p. 31). The possible finite positive entropy values and the classification of algebraic constraints remain open here.

## References

- Truth anchor: `D5/S1/Dynamics/Symbolic/MonoidCADichotomyRefutation.claim`
- Truth anchor: `D5/S1/Dynamics/Symbolic/MonoidCADichotomyRefutation.result`
- Dependency: [D5/S1/Dynamics/Symbolic/LatticeGardenOfEden](LatticeGardenOfEden.md)
