# Generic Finite Reciprocal-Product Sector Calculus

## Abstract

Generic finite reciprocal-product sector calculus

**Theorem 1.1 (Strict decrease in the height parameter).**

$$\forall N \in \mathbb{N},\; \forall c \in \operatorname{Fin}\left(N\right) \to \mathbb{R},\; \forall p \in \mathbb{R},\; 0 < N \Rightarrow \left(\left(\forall j \in \operatorname{Fin}\left(N\right),\; 0 \le \operatorname{c}\left(j\right)\right) \Rightarrow \left(0 \le p \Rightarrow \left(p \le \frac{1}{4} \Rightarrow \operatorname{StrictAntiOn}\left(((u:\mathbb{R}) \mapsto \operatorname{weight}\left(c, u, p\right)), \operatorname{Ioi}\left(\operatorname{threshold}\left(N\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZeroData/ActualHeightFourteenSector.strictAntiOn_weight_u` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive finite index size, every nonnegative shift family, and every p in the closed interval [0,1/4], the real part of the reciprocal product is strictly decreasing in u above the explicit threshold 4*(N+1)^2/pi^2. The proof supplies the reusable polar-angle positivity, u- and p-derivative signs, the endpoint continuity argument, and the signed-imaginary-part reduction. No six-pole constants or zeta data occur in this generic source.

## References

- Truth anchor: `D5/S3/Weil/ZeroData/ActualHeightFourteenSector.strictAntiOn_weight_u`
