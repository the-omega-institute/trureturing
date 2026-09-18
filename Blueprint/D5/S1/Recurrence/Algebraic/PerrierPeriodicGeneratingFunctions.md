# Perrier's Period-One Generating Functions

## Abstract

Perrier's period-one recurrences have the two stated shifted generating functions.

Let K be any field and d any natural number, including zero. Set k=d+1. The source uses coordinates 1,...,k; here they are Fin(d+1). Thus r(n,j) denotes the source coordinate j+1 at time n-1, and m(j), a(j) denote its parameters with index j+1. The maps succ and castSucc send j in Fin(d) to coordinates j+1 and j in Fin(d+1); last(d) is coordinate d. All series lie in K[[X]], C embeds a field element as a constant series, and val(j) is the natural value of a finite index. Subtraction in an exponent is natural subtraction, truncated at zero. Every finite sum below ranges over all j in Fin(d), so it is empty at d=0.

**Definition 1.1 (The period-one recurrence).**

$$\forall K: \operatorname{Type}, \operatorname{Field}\left(K\right) \implies \forall d: \mathbb{N}, \forall m: \operatorname{Fin}\left(d\right) \to K, \forall a: \operatorname{Fin}\left(d\right) \to K, \forall r: \mathbb{N} \to \left(\operatorname{Fin}\left(d + 1\right) \to K\right), \operatorname{Recurrence}\left(m, a, r\right) \iff (\operatorname{r}\left(0, 0\right) = 1) \land ((\forall j: \operatorname{Fin}\left(d\right), \operatorname{r}\left(0, \operatorname{succ}\left(j\right)\right) = \operatorname{a}\left(j\right)) \land ((\forall n: \mathbb{N}, \operatorname{r}\left(n + 1, 0\right) = \operatorname{r}\left(n, \operatorname{last}\left(d\right)\right)) \land (\forall n: \mathbb{N}, \forall j: \operatorname{Fin}\left(d\right), \operatorname{r}\left(n + 1, \operatorname{succ}\left(j\right)\right) = \operatorname{r}\left(n, \operatorname{castSucc}\left(j\right)\right) + \operatorname{m}\left(j\right) \cdot \operatorname{r}\left(n, \operatorname{last}\left(d\right)\right))))$$

*Formalization.* `D5/S1/Recurrence/Algebraic/PerrierPeriodicGeneratingFunctions.Recurrence` (`✓ std3`).

*Citation.* Rachel Perrier (2026). *Multidimensional Continued Fractions and Riordan Arrays*. DOI: [10.54550/ECA2026V6S4R33](https://doi.org/10.54550/ECA2026V6S4R33). URL: <https://ecajournal.haifa.ac.il/Volume2026/ECA2026_S4R33.pdf>.

*Commentary.*

Perrier, printed p. 14: "The same method extends to higher dimensions." The next paragraph states: "Assume period 1, so mⱼ,ᵢ = mⱼ for 1 ≤ j ≤ k − 1 and i ≥ 0." The initial values are r₁⁽⁻¹⁾ = 1, r₂⁽⁻¹⁾ = a₁, ..., rₖ⁽⁻¹⁾ = aₖ₋₁. On printed p. 15 the recurrences are r₁⁽ⁿ⁺¹⁾ = rₖ⁽ⁿ⁾ and rⱼ₊₁⁽ⁿ⁺¹⁾ = rⱼ⁽ⁿ⁾ + mⱼrₖ⁽ⁿ⁾, 1 ≤ j ≤ k − 1. The four conjuncts above retain these initial values and both equations as a predicate on an arbitrary sequence. For every m and a, the initial vector and the next-vector rule recursively determine one and only one sequence, so the predicate has a solution.

**Definition 1.2 (The shifted generating function).**

$$\forall K: \operatorname{Type}, \operatorname{Field}\left(K\right) \implies \forall d: \mathbb{N}, \forall r: \mathbb{N} \to \left(\operatorname{Fin}\left(d + 1\right) \to K\right), \forall j: \operatorname{Fin}\left(d + 1\right), \operatorname{R}\left(r, j\right) = \operatorname{mk}\left(n \mapsto \operatorname{r}\left(n, j\right)\right)$$

*Formalization.* `D5/S1/Recurrence/Algebraic/PerrierPeriodicGeneratingFunctions.R` (`✓ std3`).

*Citation.* Rachel Perrier (2026). *Multidimensional Continued Fractions and Riordan Arrays*. DOI: [10.54550/ECA2026V6S4R33](https://doi.org/10.54550/ECA2026V6S4R33). URL: <https://ecajournal.haifa.ac.il/Volume2026/ECA2026_S4R33.pdf>.

*Commentary.*

Perrier, printed p. 8: "To retain the stated initial values, define the shifted generating functions" R₁(t) = ∑ₙ≥₀ r₁⁽ⁿ⁻¹⁾tⁿ, R₂(t) = ∑ₙ≥₀ r₂⁽ⁿ⁻¹⁾tⁿ. Printed p. 12 states: "Define the shifted generating functions" Rᵢ(t) = ∑ₙ≥₀ rᵢ⁽ⁿ⁻¹⁾tⁿ, i = 1, 2, 3. The coefficient function n ↦ r(n,j) implements that shift literally. Section 5 does not repeat this definition for general k; its opening sentence, "The same method extends to higher dimensions.", is read as retaining the preceding shifted convention.

**Definition 1.3 (The common denominator).**

$$\forall K: \operatorname{Type}, \operatorname{Field}\left(K\right) \implies \forall d: \mathbb{N}, \forall m: \operatorname{Fin}\left(d\right) \to K, \operatorname{D}\left(m\right) = 1 - \sum_{j \in \operatorname{Fin}\left(d\right)} (\operatorname{C}\left(\operatorname{m}\left(j\right)\right) \cdot X^{d - \operatorname{val}\left(j\right)}) - X^{d + 1}$$

*Formalization.* `D5/S1/Recurrence/Algebraic/PerrierPeriodicGeneratingFunctions.D` (`✓ std3`).

*Citation.* Rachel Perrier (2026). *Multidimensional Continued Fractions and Riordan Arrays*. DOI: [10.54550/ECA2026V6S4R33](https://doi.org/10.54550/ECA2026V6S4R33). URL: <https://ecajournal.haifa.ac.il/Volume2026/ECA2026_S4R33.pdf>.

*Commentary.*

This is the denominator printed on p. 15, with m₁ attached to t^(k-1) and mₖ₋₁ attached to t. The sum writes the same terms in the opposite order. Each exponent d-val(j) is positive, so D(m) has constant coefficient one and is invertible as a formal power series.

**Definition 1.4 (The first-coordinate numerator).**

$$\forall K: \operatorname{Type}, \operatorname{Field}\left(K\right) \implies \forall d: \mathbb{N}, \forall m: \operatorname{Fin}\left(d\right) \to K, \forall a: \operatorname{Fin}\left(d\right) \to K, \operatorname{P}\left(m, a\right) = 1 + \sum_{j \in \operatorname{Fin}\left(d\right)} (\operatorname{C}\left(\operatorname{a}\left(j\right) - \operatorname{m}\left(j\right)\right) \cdot X^{d - \operatorname{val}\left(j\right)})$$

*Formalization.* `D5/S1/Recurrence/Algebraic/PerrierPeriodicGeneratingFunctions.P` (`✓ std3`).

*Citation.* Rachel Perrier (2026). *Multidimensional Continued Fractions and Riordan Arrays*. DOI: [10.54550/ECA2026V6S4R33](https://doi.org/10.54550/ECA2026V6S4R33). URL: <https://ecajournal.haifa.ac.il/Volume2026/ECA2026_S4R33.pdf>.

*Commentary.*

This is the numerator of R₁ on printed p. 15. The source difference aⱼ-mⱼ becomes C(a(j)-m(j)) at exponent d-val(j), and the remaining constant term is one.

**Definition 1.5 (The last-coordinate numerator).**

$$\forall K: \operatorname{Type}, \operatorname{Field}\left(K\right) \implies \forall d: \mathbb{N}, \forall a: \operatorname{Fin}\left(d\right) \to K, \operatorname{Q}\left(a\right) = X^{d} + \sum_{j \in \operatorname{Fin}\left(d\right)} (\operatorname{C}\left(\operatorname{a}\left(j\right)\right) \cdot X^{d - 1 - \operatorname{val}\left(j\right)})$$

*Formalization.* `D5/S1/Recurrence/Algebraic/PerrierPeriodicGeneratingFunctions.Q` (`✓ std3`).

*Citation.* Rachel Perrier (2026). *Multidimensional Continued Fractions and Riordan Arrays*. DOI: [10.54550/ECA2026V6S4R33](https://doi.org/10.54550/ECA2026V6S4R33). URL: <https://ecajournal.haifa.ac.il/Volume2026/ECA2026_S4R33.pdf>.

*Commentary.*

This is the numerator of Rₖ on printed p. 15. Its leading term is X^d, and parameter a(j) has exponent d-1-val(j). For d=0 the finite sum is empty and X^d is one.

**Theorem 1.6 (The two rational generating functions).**

$$\forall K: \operatorname{Type}, \operatorname{Field}\left(K\right) \implies \forall d: \mathbb{N}, \forall m: \operatorname{Fin}\left(d\right) \to K, \forall a: \operatorname{Fin}\left(d\right) \to K, \forall r: \mathbb{N} \to \left(\operatorname{Fin}\left(d + 1\right) \to K\right), \operatorname{Recurrence}\left(m, a, r\right) \implies (\operatorname{R}\left(r, 0\right) = \operatorname{P}\left(m, a\right) \cdot \operatorname{D}\left(m\right)^{-1}) \land (\operatorname{R}\left(r, \operatorname{last}\left(d\right)\right) = \operatorname{Q}\left(a\right) \cdot \operatorname{D}\left(m\right)^{-1})$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/PerrierPeriodicGeneratingFunctions.result` (`✓ std3`). ∎

*Citation.* Rachel Perrier (2026). *Multidimensional Continued Fractions and Riordan Arrays*. DOI: [10.54550/ECA2026V6S4R33](https://doi.org/10.54550/ECA2026V6S4R33). URL: <https://ecajournal.haifa.ac.il/Volume2026/ECA2026_S4R33.pdf>.

*Commentary.*

Perrier, Section 5, printed p. 15: "We conjecture that solving these recurrences yields" the displayed formulas for R₁(t) and Rₖ(t). In the notation above these are P(m,a) times the inverse of D(m), and Q(a) times the same inverse. Both identities hold for every sequence satisfying Recurrence(m,a,r), over every field and every d. Multiplying the successor-coordinate equations by X^(d-1-val(j)) and summing cancels all intermediate coordinates. This gives R(r,last(d))D(m)=Q(a); the first-coordinate equation gives R(r,0)D(m)=P(m,a). The constant coefficient one permits division. The subsequent sentence about equation (7) is a separate conjecture.

The two formulas quoted from printed p. 15, in the source notation, are:

$$
\begin{aligned}\left(R_{1}\right)\left(t\right) = \frac{(a_{1} - m_{1}) \cdot t^{k - 1} + (a_{2} - m_{2}) \cdot t^{k - 2} + \cdot\cdot\cdot + (a_{k - 1} - m_{k - 1}) \cdot t + 1}{1 - m_{k - 1} \cdot t - m_{k - 2} \cdot t^{2} - \cdot\cdot\cdot - m_{1} \cdot t^{k - 1} - t^{k}}\\\left(R_{k}\right)\left(t\right) = \frac{t^{k - 1} + a_{1} \cdot t^{k - 2} + \cdot\cdot\cdot + a_{k - 2} \cdot t + a_{k - 1}}{1 - m_{k - 1} \cdot t - m_{k - 2} \cdot t^{2} - \cdot\cdot\cdot - m_{1} \cdot t^{k - 1} - t^{k}}\end{aligned}
$$

## References

- Truth anchor: `D5/S1/Recurrence/Algebraic/PerrierPeriodicGeneratingFunctions.D`
- Truth anchor: `D5/S1/Recurrence/Algebraic/PerrierPeriodicGeneratingFunctions.P`
- Truth anchor: `D5/S1/Recurrence/Algebraic/PerrierPeriodicGeneratingFunctions.Q`
- Truth anchor: `D5/S1/Recurrence/Algebraic/PerrierPeriodicGeneratingFunctions.R`
- Truth anchor: `D5/S1/Recurrence/Algebraic/PerrierPeriodicGeneratingFunctions.Recurrence`
- Truth anchor: `D5/S1/Recurrence/Algebraic/PerrierPeriodicGeneratingFunctions.result`
