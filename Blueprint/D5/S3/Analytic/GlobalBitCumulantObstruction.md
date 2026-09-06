# A Global-Bit Obstruction for Shift-Dependent Cumulants

## Abstract

A single radial tensor-power parameter cannot encode every shift-dependent cumulant.

**Theorem 1.1 (One radial tensor square misses an explicit shift pattern).**

$$\begin{gathered}R_{ij}(c, \delta) = c \delta_{i} \delta_{j},\\{}K_{01} = K_{12} = 1, K_{02} = 0,\\{}(R_{01} \neq 0 \land R_{12} \neq 0) \Rightarrow R_{02} \neq 0,\\{}\neg \exists c, \delta, R(c, \delta) = K.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GlobalBitCumulantObstruction.one_global_bit_cannot_encode_all_pair_cumulants` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A one-bit radial model produces pair cumulants of the form scale times delta_i delta_j. Such a rank-one family has a load-bearing nonzero closure law: nonzero correlations on pairs 01 and 12 force the correlation on pair 02 to be nonzero.

The explicit symmetric three-shift target instead has adjacent values K_01=K_12=1 and distance-two value K_02=0. It therefore has no representation by one displacement vector and one global scale.

A separate public control theorem represents the constant-one pair family, showing that the obstruction is caused by shift structure rather than an empty radial model class.

## References

- Truth anchor: `D5/S3/Analytic/GlobalBitCumulantObstruction.one_global_bit_cannot_encode_all_pair_cumulants`
