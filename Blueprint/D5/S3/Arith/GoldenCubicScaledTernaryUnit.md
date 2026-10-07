# Native Scaled Ternary Lucas Units

## Abstract

Native ternary Lucas layers have exact three-adic valuations and alternating scaled units.

Let phi be the golden integer with phi squared equal to phi plus one. The integer L_n is goldenLucas n, the trace of phi^n. For every natural j, put A_j=L_(3^j)^2+2. The symbol v_3 denotes padicValInt 3 on these positive integers. Powers have natural exponents.

$$
L_n=\operatorname{Tr}(\varphi^n),\quad A_{j}=L_{3^{j}}^2+2
$$

**Theorem 1.1 (Exact depth and signed integer quotient).**

$$\forall j \in \mathbb{N},\; (1 \le j) \Rightarrow ((\left(v_{3}\right)\left(A_{j}\right) = j + 1) \land (\frac{A_{j}}{3^{j + 1}} \equiv (-1)^{j} (\operatorname{mod} 3)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenCubicScaledTernaryUnit.golden_cubic_scaled_ternary_unit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural j at least one, A_j has three-adic valuation j+1. The displayed fraction is exact integer division in Z: 3^(j+1) divides A_j, and the resulting integer has residue (-1)^j modulo three.

The native cubic Lucas identity gives A_(k+1)=A_k(A_k^2-3), starting from A_0=3. Induction constructs an integer u_k with A_k=3^(k+1)u_k and u_k congruent to (-1)^k modulo three. The successor is u_(k+1)=u_k(3(3^k)^2u_k^2-1), so its residue is the negative of the preceding residue. Exact division by the positive power 3^(j+1) recovers this same u_j.

For the valuation, Fibonacci and Lucas doubling give F_(4*3^j)=F_(3^j)L_(3^j)A_j. The first two factors are nonzero and indivisible by three. The Fibonacci valuation at index 4*3^j is j+1, hence the valuation of A_j is j+1 as well.

## References

- Truth anchor: `D5/S3/Arith/GoldenCubicScaledTernaryUnit.golden_cubic_scaled_ternary_unit`
- Dependency: [D5/S1/Scale/GoldenCubicBlockCongruences](../../S1/Scale/GoldenCubicBlockCongruences.md)
- Dependency: [D5/S3/Arith/CloitreFibFourThreeAdicValuationSigma](CloitreFibFourThreeAdicValuationSigma.md)
