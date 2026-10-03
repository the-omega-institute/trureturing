# Auxiliary Twisted Octonion Norm

## Abstract

The explicit signed Cayley-Dickson table has a multiplicative Euclidean norm.

**Theorem 1.1 (The signed multiplication has a composition norm).**

$$\forall x, y, \operatorname{normSq}(mul(x, y))= \operatorname{normSq}(x)\times\operatorname{normSq}(y).$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/MonsterTwistedOctonionNorm.norm_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Lean definition is the explicit eight-coordinate signed Cayley-Dickson table. The proof expands every coordinate and normalizes the resulting polynomial identity over the reals.

The companion unit lemmas are checked from the same table. This is an auxiliary twisted group-algebra model and does not assert a VOA or Monster OPE construction.

## References

- Truth anchor: `D5/S3/VertexAlgebra/MonsterTwistedOctonionNorm.norm_mul`
