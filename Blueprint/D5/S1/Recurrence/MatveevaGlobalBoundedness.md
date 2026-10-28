# Matveeva's Literal Global Boundedness Claim

## Abstract

A rational linear solution contradicts the literal nonzero-parameter assertion about global boundedness.

**Definition 1.1 (Integral scaling of positive coefficients).**

$$\forall s:\mathbb{N}\to\mathbb{Q}, \operatorname{integralScaling}\left(s\right)\iff\left(\exists C:\mathbb{Z}, C\neq 0 \land \left(\forall n:\mathbb{N}, 1\le n\implies \exists k:\mathbb{Z}, \left(C:\mathbb{Q}\right)^{n}\cdot s\left(n\right)=\left(k:\mathbb{Q}\right)\right)\right)$$

*Formalization.* `D5/S1/Recurrence/MatveevaGlobalBoundedness.integralScaling` (`✓ std3`).

*Citation.* Anastasia Matveeva (2025). *On the integrality of some P-recursive sequences*. URL: <https://arxiv.org/abs/2511.02121v1>.

*Commentary.*

A single nonzero integer C clears all positive-index coefficients after scaling the variable. The integer k may depend on n. No integrality condition is imposed on the constant coefficient. This is Definition 1.4.

**Definition 1.2 (Summability on a positive complex disk).**

$$\forall s:\mathbb{N}\to\mathbb{Q}, \operatorname{positiveComplexRadius}\left(s\right)\iff\left(\exists R:\mathbb{R}, 0<R \land \left(\forall z:\mathbb{C}, \Vert z\Vert <R\implies \operatorname{Summable}\left(\left(n:\mathbb{N}\mapsto\left(s\left(n\right):\mathbb{C}\right)\cdot z^{n}\right)\right)\right)\right)$$

*Formalization.* `D5/S1/Recurrence/MatveevaGlobalBoundedness.positiveComplexRadius` (`✓ std3`).

*Citation.* Anastasia Matveeva (2025). *On the integrality of some P-recursive sequences*. URL: <https://arxiv.org/abs/2511.02121v1>.

*Commentary.*

A positive real R gives summability of the entire complex series at every z of norm less than R. The natural summation index includes zero. This expresses the convergence clause of Definition 1.5.

**Definition 1.3 (The two clauses of global boundedness).**

$$\forall s:\mathbb{N}\to\mathbb{Q}, \operatorname{globallyBounded}\left(s\right)\iff\left(\operatorname{integralScaling}\left(s\right) \land \operatorname{positiveComplexRadius}\left(s\right)\right)$$

*Formalization.* `D5/S1/Recurrence/MatveevaGlobalBoundedness.globallyBounded` (`✓ std3`).

*Citation.* Anastasia Matveeva (2025). *On the integrality of some P-recursive sequences*. URL: <https://arxiv.org/abs/2511.02121v1>.

*Commentary.*

Global boundedness is the conjunction of integral scaling and a positive complex radius, as in Definition 1.5.

**Definition 1.4 (The full rational-parameter assertion).**

$$\operatorname{claim}\iff\left(\forall a_{1} a_{2} b_{0} b_{1} b_{2}:\mathbb{Q}, a_{1}\neq 0\implies a_{2}\neq 0\implies \left(\forall n:\mathbb{N}, 2\le n\implies b_{0}\neq -\left(n:\mathbb{Q}\right)\right)\implies \forall s:\mathbb{N}\to\mathbb{Q}, \left(\forall n:\mathbb{N}, 2\le n\implies \left(\left(n:\mathbb{Q}\right)+b_{0}\right)\cdot s\left(n\right)+\left(a_{1}\cdot \left(n:\mathbb{Q}\right)+b_{1}\right)\cdot s\left(n-1\right)+\left(a_{2}\cdot \left(n:\mathbb{Q}\right)+b_{2}\right)\cdot s\left(n-2\right)=0\right)\implies a_{1}\cdot a_{2}\cdot b_{0}+a_{1}\cdot b_{2}-2\cdot a_{2}\cdot b_{1}\neq 0\implies \neg \operatorname{globallyBounded}\left(s\right)\right)$$

*Formalization.* `D5/S1/Recurrence/MatveevaGlobalBoundedness.claim` (`✓ std3`).

*Citation.* Anastasia Matveeva (2025). *On the integrality of some P-recursive sequences*. URL: <https://arxiv.org/abs/2511.02121v1>.

*Commentary.*

All five parameters are rational, a1 and a2 are nonzero, and b0 excludes every negative integer at most minus two. Every rational sequence is allowed, with arbitrary rational initial pair. The recurrence holds at every natural n at least two. The only further hypothesis is that a1*a2*b0 + a1*b2 - 2*a2*b1 is nonzero. Section 4.2 and the explicit inequality in Section 7 give this literal parameter reading. No minimal order, nonrationality, normalized initial values, or persistence of an exponential after simplification is required. Subtraction in sequence indices is natural subtraction.

**Definition 1.5 (The rational sequence n plus one).**

$$\forall n:\mathbb{N}, \operatorname{witness}\left(n\right)=\left(n:\mathbb{Q}\right)+1$$

*Formalization.* `D5/S1/Recurrence/MatveevaGlobalBoundedness.witness` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Anastasia Matveeva (2025). *On the integrality of some P-recursive sequences*. URL: <https://arxiv.org/abs/2511.02121v1>.

*Commentary.*

At natural index n the rational coefficient is n plus one. Its initial values are one and two.

**Theorem 1.6 (Negation of the entire literal claim).**

$$\neg \operatorname{claim}$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/MatveevaGlobalBoundedness.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Anastasia Matveeva (2025). *On the integrality of some P-recursive sequences*. URL: <https://arxiv.org/abs/2511.02121v1>.

*Commentary.*

Take (b0, a1, b1, a2, b2) = (1, -3, -1, 2, 1) and s(n) = n + 1. The recurrence becomes (n+1)^2 + (-3*n-1)*n + (2*n+1)*(n-1) = 0 for every n at least two. The parameter expression is minus five. Integral scaling uses C = 1 and integer coefficient n + 1 at every positive index. The complex series is summable for every z of norm less than R = 1, by the k = 1 complex instance of summable_choose_mul_geometric_of_norm_lt_one. These facts contradict the universally quantified conclusion. The result concerns the literal parameter condition; Conjecture 4.1 is a separate assertion. A requirement that an exponential survive simplification would define a different claim.

## References

- Truth anchor: `D5/S1/Recurrence/MatveevaGlobalBoundedness.claim`
- Truth anchor: `D5/S1/Recurrence/MatveevaGlobalBoundedness.globallyBounded`
- Truth anchor: `D5/S1/Recurrence/MatveevaGlobalBoundedness.integralScaling`
- Truth anchor: `D5/S1/Recurrence/MatveevaGlobalBoundedness.positiveComplexRadius`
- Truth anchor: `D5/S1/Recurrence/MatveevaGlobalBoundedness.result`
- Truth anchor: `D5/S1/Recurrence/MatveevaGlobalBoundedness.witness`
