# A physical order gap for four marked heat ports

## Abstract

The full heat kernel of a complete four-port network has linear order seven and physical order eight.

**Theorem 1.1 (Four columns are necessary under the cycle bounds).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/FourPortHeatRealization.cycle_gram_width`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/FourPortHeatRealization.cycle_gram_width` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let A have four rows in cyclic order, m columns and nonnegative real entries. Suppose AAᵀ has diagonal entries at most 4, cyclic entries Q₀₁, Q₁₂, Q₂₃ and Q₃₀ at least 1, and opposite entries Q₀₂ and Q₁₃ strictly below 1/36. Then m is at least four.

With at most three columns, each cyclic entry has a contributing column whose endpoint product is at least 1/3. The diagonal cap bounds each factor entry by 2, so both endpoints in the chosen column have entries at least 1/6. Two edges choose the same column, and their endpoint union contains an opposite pair. That column contributes at least 1/36 to the opposite entry.

For the unperturbed incidence Gram matrix the triangle-free support argument is classical. See Naomi Shaked-Monderer, Bounding the CP-rank by graph parameters, Electronic Journal of Linear Algebra 28 (2015), DOI 10.13001/1081-3810.3009. The bound here also permits positive opposite entries.

**Theorem 1.2 (The complete example has physical order eight and linear order seven).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/FourPortHeatRealization.cycle_heat_order_gap`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/FourPortHeatRealization.cycle_heat_order_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There are four labeled ports and four hidden vertices, all with unit mass. The cross conductance matrix is the unsigned cycle incidence matrix plus the all-ones matrix divided by 1000. The incidence rows are (1,0,0,1), (1,1,0,0), (0,1,1,0), and (0,0,1,1). Each distinct pair on the same side has conductance 1/1000. The symmetric generator S has zero row sums and strictly negative off-diagonal entries.

For a physical candidate write z for the vector of positive square roots of the masses with value one at each port. Its mass-normalized generator S is symmetric, annihilates z and has nonpositive off-diagonal entries. These conditions give the conductance Laplacian diag(z) S diag(z). The port insertion E gives moments Uⱼ = Eᵀ Sʲ E and heat kernel Eᵀ exp(−tS) E.

Block multiplication identifies the defect Q = U₂ − U₁² with AAᵀ for the nonnegative cross block A = −S_PH. For the stated network Q has values 2+q on the diagonal, 1+q on cycle edges and q on opposite pairs, where q = 1001/250000. Every physical candidate within entrywise defect error 1/250 obeys the cycle bounds and therefore has at least eight vertices. The same lower bound applies to exact heat data because the first and second derivatives at zero determine U₁ and U₂.

The hidden hyperplane x₀ − x₁ + x₂ − x₃ = 0, together with the port space, is invariant under S. Restricting to it preserves all port moments and the entire matrix exponential readout. For the converse, take the four port columns of E and the first three columns of SE. They have rank seven by a nonzero minor. Their Gram matrix is the corresponding principal section of the two-step moment Hankel matrix. For any linear realization with the same heat curve this section factors through the state space, so its dimension is at least seven.

The dimension includes the stationary mode. The perturbation statement concerns physical order in a band on the first-two-moment defect. Its hypothesis is at the calibrated heat-moment level.

## References

- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/FourPortHeatRealization.cycle_gram_width`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/FourPortHeatRealization.cycle_heat_order_gap`
