# Residual Zero-Star Cardinality

For a configuration `z` with the marked label at the final position, the residual zero-star is the independently defined set of configurations whose deletion is the residual circle of `z` in either orientation. The coordinate bijection separates the orientation bit, the global rotation, and the rotation of the first `m` positions.

There are `m` choices for the first-position rotation, `m+1` choices for the global rotation, and two choices for the residual orientation. Hence the exact vertex count is `2m(m+1)`, which is the finite layer cardinality used by the native Hamilton construction.

## Exact Residual Star Cardinality

Describe: `star-cardinality`

$$\forall m \in \mathbb{N},\; (3 \le m) \Rightarrow \forall z \in \mathrm{Configuration}(m),\; \mathrm{Fintype.card}\left\{v \mid \mathrm{Star}\left(z(\mathrm{last}(m)),\;\mathrm{residualList}(z),\;v\right)\right\} = m\cdot((m+1)\cdot 2)$$

For every `m` at least three and every configuration `z`, the finite subtype of the residual zero-star has cardinality `m` times `m+1` times `2`.
