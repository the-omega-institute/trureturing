# Actual Shape Masses and Fixed Shift Ratios

## Abstract

Critical actual-shape masses and every fixed-shift count ratio retain the singleton conventions.

U(n) consists of actual permutations of Fin(n) avoiding 2413 and 3142. It includes the genuine empty and singleton permutations. Write rho=(sqrt(2)-1)^2. Subtraction in a natural index is truncated at zero.

U(n) is the class of literal permutations avoiding 2413 and 3142. J(s,n) is its subclass with no proper cut of sign s. Put b=sqrt(2)-1, rho=b^2, a=1-b, and ceiling=a/2. The weight shapeWeight(n) is rho^(n+1)*card(U(n+1)); thus every shape counted has positive length. The kernelWeight adds rho/2 at n=0 and adds zero at other indices.

**Theorem 1.1 (Critical masses and the singleton correction).**

$$\operatorname{Summable}\left(shapeWeight\right) \land \operatorname{sum}\left(shapeWeight\right)=b \land \operatorname{Summable}\left(kernelWeight\right) \land \operatorname{sum}\left(kernelWeight\right)=\frac{1}{2} \land \operatorname{Summable}\left(jWeight\right) \land \operatorname{sum}\left(jWeight\right)=ceiling \land (\forall n\in \mathbb{N}, \operatorname{jWeight}\left(n\right)=\frac{\operatorname{kernelWeight}\left(n\right)+\frac{rho}{2}\cdot\operatorname{indicatorZero}\left(n\right)}{2})$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Patterns/Separable/ActualCountRatios.critical_shape_masses` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All three real series in the display are summable. Here jWeight(n) is rho^(n+1)*card(J(false,n+1)), and indicatorZero(n) is one at n=0 and zero otherwise. In addition, for every natural n, jWeight(n)=(kernelWeight(n)+(if n=0 then rho/2 else 0))/2. At positive length one both signed indecomposable classes contain one shape; the sign-half relation starts only at length two.

The actual cardinality recurrence bounds the partial sums of shapeWeight by b. Its Cauchy product equation identifies the sum with the double root b. The actual signed counts then give the remaining two sums and the displayed pointwise correction.

**Theorem 1.2 (Full sequence ratio for every fixed shift).**

$$\forall d\in\mathbb{N}, \lim_{n\to\infty}\frac{\operatorname{card}\left(\operatorname{U}\left(n-d\right)\right)}{\operatorname{card}\left(\operatorname{U}\left(n\right)\right)}=rho^d$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Patterns/Separable/ActualCountRatios.actual_fixed_shift_ratio` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The limit is along all natural sizes. No ratio limit, recurrence asymptotic, positivity assumption or subsequence is supplied as a hypothesis. The actual enumeration identifies positive-length counts with largeSchroder(n-1), and an actual identity or reversal permutation supplies the required nonempty finite carriers.

Differentiating the formal Schroder generating function yields (n+3)*S(n+2)=(6*n+9)*S(n+1)-n*S(n). The adjacent ratios S(n+1)/S(n) increase from 2 and stay below 3+2*sqrt(2). Their limit satisfies L=6-1/L and is therefore 3+2*sqrt(2). Finite products, reciprocals and shifts give the stated actual ratio.

## References

- Truth anchor: `D5/S1/Words/Patterns/Separable/ActualCountRatios.actual_fixed_shift_ratio`
- Truth anchor: `D5/S1/Words/Patterns/Separable/ActualCountRatios.critical_shape_masses`
- Dependency: [D5/S1/Words/Patterns/Separable/ActualCardinality](ActualCardinality.md)
