# Auxiliary Twisted Octonion Norm

## Abstract

The explicit signed Cayley-Dickson table used for the finite `F₂³` sign model has a multiplicative Euclidean norm.

**Theorem 1.1 (Multiplicative norm).**

$$
\forall x,y\in\mathbb R^8,\qquad
\operatorname{normSq}(x\,y)=\operatorname{normSq}(x)\operatorname{normSq}(y).
$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/MonsterTwistedOctonionNorm.norm_mul` (`✓ std3`). The proof expands the eight signed coordinates and closes the polynomial identity over `ℝ`; `one_mul` and `mul_one` check the unit independently. ∎

*Source.* Repository-derived formalization of the auxiliary table.

*Commentary.*

The multiplication is a fixed signed representative of the admissible `F₂³` twisted group algebra. This theorem proves the all-real-vector composition law, rather than checking only basis products. It formalizes the norm statement in §32.1 of `MONSTER_LOCAL_COMPLETION_AND_CUBIC_RESPONSE.md`.

The result concerns the auxiliary eight-dimensional algebra. It does not construct the Monster VOA, an intertwiner, a Griess product, or an OPE. The literature identification with the real octonions remains the cited Hurwitz classification input.

## References

- Truth anchor: `D5/S3/VertexAlgebra/MonsterTwistedOctonionNorm.norm_mul`
- Unit anchors: `D5/S3/VertexAlgebra/MonsterTwistedOctonionNorm.one_mul`, `D5/S3/VertexAlgebra/MonsterTwistedOctonionNorm.mul_one`
- Theory owner: `docs/develop/theory/MONSTER_LOCAL_COMPLETION_AND_CUBIC_RESPONSE.md`, §32.1
- [Ba17] T. Basak, *The octonions as a twisted group algebra*, arXiv:1702.05705, Theorem 1 and §§5–6. See `Library/VertexAlgebra/basak2017monstercharactercarry.md`.
- [B02] J. C. Baez, *The Octonions*, Bull. Amer. Math. Soc. 39 (2002), arXiv:math/0105155. See `Library/VertexAlgebra/vanekeren2020atomicmonstercompletion.md`.
