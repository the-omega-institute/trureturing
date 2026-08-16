# Tribonacci Perron Root

## Abstract

Tribonacci number and name-count ratios converge to the unique real Perron root.

The existing Tribonacci constant remains the unique source for the base. Factoring its cubic from the count recurrence leaves a stable quadratic error whose positive energy contracts exactly by the inverse base.

**Theorem 1.1 (Exact Tribonacci-root characterization).**

$$\forall x \in R,\; x = t \Leftrightarrow \left(1 < x \land \left(x < 2 \land \operatorname{pow}\left(x, 3\right) = \operatorname{pow}\left(x, 2\right) + x + 1\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/Tribonacci/PerronRoot.eq_tribonacciConstant_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Subtracting two cubic equations factors out their root difference. The remaining factor is strictly positive above one, proving uniqueness while the frozen Values module supplies both bounds.

**Theorem 1.2 (Tribonacci-number ratio Perron limit).**

$$\operatorname{limitAtTop}\left(\left(\frac{\operatorname{T}\left(n + 1\right)}{\operatorname{T}\left(n\right)}\right)_{n \in N}\right) = t$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/Tribonacci/PerronRoot.tribonacci_ratio_tendsto` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For e(n)=T(n+1)-tT(n), cubic factorization gives a second-order recurrence. Its positive quadratic energy is multiplied by t^-1 at each step, so e(n) tends to zero and division by positive T(n) yields the ratio limit.

**Theorem 1.3 (Tribonacci-name count ratio Perron limit).**

$$\operatorname{limitAtTop}\left(\left(\frac{\operatorname{card}\left(\operatorname{TribonacciName}\left(Q + 1\right)\right)}{\operatorname{card}\left(\operatorname{TribonacciName}\left(Q\right)\right)}\right)_{Q \in N}\right) = t$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/Tribonacci/PerronRoot.tribonacci_name_card_ratio_tendsto` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The frozen cardinality theorem rewrites each length-Q name count as T(Q+2). Shifting the already proved number-ratio limit by two then gives the exact name-count statement.

## References

- Truth anchor: `D5/S0/Tower/Tribonacci/PerronRoot.eq_tribonacciConstant_iff`
- Truth anchor: `D5/S0/Tower/Tribonacci/PerronRoot.tribonacci_name_card_ratio_tendsto`
- Truth anchor: `D5/S0/Tower/Tribonacci/PerronRoot.tribonacci_ratio_tendsto`
- Dependency: [D5/S0/Tower/Tribonacci/Values](Values.md)
