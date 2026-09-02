# Full-Rank Inertia Pullback

## Abstract

Hermitian pullback cannot increase negative index, and an explicit right inverse preserves the full positive-negative inertia pair exactly.

**Theorem 1.1 (Negative index cannot increase under pullback).**

Lean statement: `D5/S3/Weil/ZetaLinear/FullRankInertiaPullback.negIndex_conj_le`

$$\operatorname{negIndex}(\operatorname{pullback}(B,Q))\le\operatorname{negIndex}(Q).$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaLinear/FullRankInertiaPullback.negIndex_conj_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The repository already owns the positive-index pullback inequality. The new theorem proves the negative companion through the frozen Hermitian negative-part calculus and the same finite-dimensional image argument.

**Theorem 1.2 (A right inverse preserves positive index).**

Lean statement: `D5/S3/Weil/ZetaLinear/FullRankInertiaPullback.posIndex_conj_eq_of_rightInverse`

$$BR=I\Rightarrow\operatorname{posIndex}(\operatorname{pullback}(B,Q))=\operatorname{posIndex}(Q).$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaLinear/FullRankInertiaPullback.posIndex_conj_eq_of_rightInverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The forward inequality is the frozen pullback theorem. The explicit right inverse pulls the pulled-back form back to the original form and supplies the reverse inequality.

**Theorem 1.3 (A right inverse preserves negative index).**

Lean statement: `D5/S3/Weil/ZetaLinear/FullRankInertiaPullback.negIndex_conj_eq_of_rightInverse`

$$BR=I\Rightarrow\operatorname{negIndex}(\operatorname{pullback}(B,Q))=\operatorname{negIndex}(Q).$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaLinear/FullRankInertiaPullback.negIndex_conj_eq_of_rightInverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same two-sided pullback argument preserves the number of strictly negative eigenvalues exactly.

**Theorem 1.4 (A right inverse preserves the full inertia pair).**

Lean statement: `D5/S3/Weil/ZetaLinear/FullRankInertiaPullback.inertia_conj_eq_of_rightInverse`

$$BR=I\Rightarrow\left(\operatorname{posIndex}(\operatorname{pullback}(B,Q))=\operatorname{posIndex}(Q)\land\operatorname{negIndex}(\operatorname{pullback}(B,Q))=\operatorname{negIndex}(Q)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaLinear/FullRankInertiaPullback.inertia_conj_eq_of_rightInverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The result packages positive- and negative-index preservation. It is the reusable algebraic certificate required by rectangular full-rank Cauchy and Vandermonde feature maps.

## References

- Dependency: `D5/S3/Weil/ZetaLinear/Inertia`
- Truth anchor: `D5/S3/Weil/ZetaLinear/FullRankInertiaPullback.negIndex_conj_le`
- Truth anchor: `D5/S3/Weil/ZetaLinear/FullRankInertiaPullback.posIndex_conj_eq_of_rightInverse`
- Truth anchor: `D5/S3/Weil/ZetaLinear/FullRankInertiaPullback.negIndex_conj_eq_of_rightInverse`
- Truth anchor: `D5/S3/Weil/ZetaLinear/FullRankInertiaPullback.inertia_conj_eq_of_rightInverse`
