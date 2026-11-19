# Exponential coefficients of marked assemblies

## Abstract

Arbitrary marker arity gives an exact signed exponential formula and full Sylow-order cancellation of compatible strict-prefix residuals.

**Theorem 1.1 (The signed exponential formula).**

$$\forall d: \mathbb{N}, \forall V: \operatorname{FiniteTypes}, \forall C: \operatorname{FiniteTypes}, \forall allowed: \operatorname{Predicate}\left(\mathbb{N}, C\right), \forall S: \operatorname{Finset}\left(V\right), \forall T: \operatorname{Finset}\left(V\right), \forall sign: \operatorname{Function}\left(C, \mathbb{Z}\right), \operatorname{castQ}\left(\operatorname{assemblySum}\left(d, allowed, S, T, sign\right)\right) = \operatorname{factorial}\left(\operatorname{card}\left(S\right)\right) \cdot \operatorname{coeff}\left(\operatorname{card}\left(S\right), \operatorname{exp}\left((\operatorname{castQ}\left(\operatorname{card}\left(T\right)\right))^{d} \cdot \operatorname{colorSeries}\left(allowed, sign\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/MarkedAssemblyCoefficients.assembly_sum_coefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any natural arity d, finite V and C, arbitrary admissibility predicate and integer color weights, the signed sum over the actual d-marker assemblies is |S|! times the ordinary degree-|S| coefficient of exp(|T|^d P). Here P has zero constant coefficient and positive degree-j coefficient equal to the signed sum of allowed colors at size j. All marker coordinates range independently over T, including repetition, even when the vertex support shrinks. The proof groups the root block by support, order, color and marker function. Its factors are the support binomial coefficient, the support-size factorial, the color sum and |T|^d. Strong induction identifies this exact block-removal recurrence with the formal exponential derivative recurrence. The empty assembly gives the constant term. The Orders, support sums, colorSeries and signed prefix palettes are defined in MarkedAssemblyCoefficients and are independent of marker arity.

**Theorem 1.2 (The compatible-prefix local residual).**

$$\forall d: \mathbb{N}, \forall N: \mathbb{N}, \forall a: \operatorname{Function}\left(\mathbb{N}, \mathbb{Z}\right), \forall p: \mathbb{N}, (1 \le N \land \left(\operatorname{Prime}\left(p\right) \land \left(\neg \operatorname{Dvd}\left(p, N\right) \land \forall f: \mathbb{N}, (1 \le f) \implies ((f < N) \implies (\operatorname{coeff}\left(f, \operatorname{exp}\left((\operatorname{castQ}\left(f\right))^{d} \cdot \operatorname{prefixSeries}\left(N, a\right)\right)\right) = (\operatorname{castQ}\left(f\right))^{d} \cdot \operatorname{coeff}\left(f - 1, \operatorname{exp}\left((\operatorname{castQ}\left(f\right))^{d} \cdot \operatorname{prefixSeries}\left(N, a\right)\right)\right)))\right)\right)) \implies (\operatorname{IsRIntegralRat}\left(p, \operatorname{coeff}\left(N, \operatorname{exp}\left((\operatorname{castQ}\left(N\right))^{d} \cdot \operatorname{prefixSeries}\left(N, a\right)\right)\right) - (\operatorname{castQ}\left(N\right))^{d} \cdot \operatorname{coeff}\left(N - 1, \operatorname{exp}\left((\operatorname{castQ}\left(N\right))^{d} \cdot \operatorname{prefixSeries}\left(N, a\right)\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/MarkedAssemblyCoefficients.signed_prefix_residual_local_integral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural d and N>=1, integer sequence a, and prime p not dividing N, let P have ordinary coefficient a(j) for 0<j<N and zero otherwise. Assume precisely the displayed lower degree-f equations for 1<=f<N. The degree-N residual then has rational denominator coprime to p. No restriction on d, coefficient signs, or the next source coefficient is imposed. The finite palette realizes P, and each color has sign one or minus one independently of marker arity. Full assemblies and rooted assemblies carry the actual simultaneous permutation actions. A rooted object has one distinguished vertex and d independent markers; its remaining assembly retains the whole ambient marker set, including the removed vertex. For a permutation with f>=1 fixed vertices and moved-part signed sum M, the fixed-object subtraction equals M f! times the degree-f residual with scalar f^d. Fixed blocks restrict every marker to the fixed vertices; moved blocks keep the original ambient set. Signed Burnside splits the action into its positive and negative weight fibers. A Sylow p-subgroup of the symmetric group has full order p^v_p(N!). Every element fixes a vertex since p does not divide N; a nonidentity element fixes fewer than N vertices. Its residual therefore vanishes by the actual lower equations. The identity moved part is uniquely empty. The resulting integer divisibility cancels the entire factorial valuation. The zero residual and trivial Sylow group are included. Taking d=3 supplies the cubic arithmetic step.

## References

- Truth anchor: `D5/S1/Recurrence/Algebraic/MarkedAssemblyCoefficients.assembly_sum_coefficient`
- Truth anchor: `D5/S1/Recurrence/Algebraic/MarkedAssemblyCoefficients.signed_prefix_residual_local_integral`
- Dependency: [D5/S1/Recurrence/Algebraic/DoldExponentialIntegrality](DoldExponentialIntegrality.md)
- Dependency: [D5/S1/Recurrence/Algebraic/MarkedAssemblyFixedPoints](MarkedAssemblyFixedPoints.md)
