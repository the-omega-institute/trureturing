# Original even exterior projection

## Abstract

Identification of the closed cosine tail with the original even exterior and its actual orthogonal projection.

All spaces and maps use complex L2 for Lebesgue measure restricted to Ioc(-a,a]. originalEven is the independently defined AE-even zero-extension sector. exteriorSpace(a,M) is the existing closed span of cosine modes M+j+1 for natural j, and exteriorProjection has that subspace as its codomain. The identifications below require a>0 and natural M; there is no terminal upper tail cutoff.

**Definition 1.1 (The finite head consists of modes zero through M).**

Lean statement: `D5/S3/Weil/ZetaBridge/OriginalEvenExterior.finiteHead`

*Formalization.* `D5/S3/Weil/ZetaBridge/OriginalEvenExterior.finiteHead` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The complex span is indexed by Fin(M+1), so the constant mode and the mode M are both included. It is finite dimensional and therefore supports its orthogonal projection. The finite head and the closed tail both lie in originalEven; for a>0 their mutual orthogonality follows from the existing physical cosine orthonormality.

**Theorem 1.2 (The closed tail is the original even head complement).**

Lean statement: `D5/S3/Weil/ZetaBridge/OriginalEvenExterior.exteriorSpace_eq_even_inf_head_orthogonal`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/OriginalEvenExterior.exteriorSpace_eq_even_inf_head_orthogonal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a>0 and every natural M, exteriorSpace(a,M) equals originalEven(a) intersected with the orthogonal complement of finiteHead(a,M), with both subspaces in the full window carrier. For the reverse inclusion, subtract the projection onto the existing tail. The residual remains originally even and orthogonal to the head and tail. Splitting each natural cosine index at M then gives zero inner product with every mode, so original even cosine injectivity kills the residual. The full even identification is proved here using completeness, rather than built into the definition of the tail.

**Definition 1.3 (Projection onto the original even sector).**

Lean statement: `D5/S3/Weil/ZetaBridge/OriginalEvenExterior.evenProjection`

*Formalization.* `D5/S3/Weil/ZetaBridge/OriginalEvenExterior.evenProjection` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the original even subspace's starProjection, regarded as a continuous complex linear endomorphism of WindowL2(a). It is defined for arbitrary real a.

**Definition 1.4 (Projection onto the finite cosine head).**

Lean statement: `D5/S3/Weil/ZetaBridge/OriginalEvenExterior.headProjection`

*Formalization.* `D5/S3/Weil/ZetaBridge/OriginalEvenExterior.headProjection` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This starProjection is also an endomorphism of WindowL2(a), for arbitrary real a and natural M. Its codomain convention differs from the subspace-valued exteriorProjection; the following identity explicitly includes the latter's subtype inclusion.

**Theorem 1.5 (The actual exterior projection on the full window carrier).**

Lean statement: `D5/S3/Weil/ZetaBridge/OriginalEvenExterior.exteriorProjection_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/OriginalEvenExterior.exteriorProjection_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a>0 and natural M, inclusion composed with exteriorProjection(a,M) equals (id-headProjection(a,M)) composed with evenProjection(a). The equality is between continuous complex linear maps on all WindowL2(a), including inputs that are not even. If e is the even projection of u and h is the head projection of e, then e-h lies in the identified tail and u-(e-h) is orthogonal to it. Uniqueness of orthogonal projection proves the equality. Omitting the even projection on an arbitrary input is not part of this statement.

**Theorem 1.6 (Head subtraction for the actual symmetric prime image).**

Lean statement: `D5/S3/Weil/ZetaBridge/OriginalEvenExterior.exteriorProjection_prime`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/OriginalEvenExterior.exteriorProjection_prime` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a>0, arbitrary natural M and N and arbitrary complex v, the included projection of primeHeadL2(a,N,v) equals that image minus its headProjection at M. No N<M separation is required for this identity. The even projection disappears because the exact prime image was proved to lie in originalEven, retaining every von Mangoldt prime-power term up to primeCutoff(a)=floor(exp(2*a)) and both signed compressed shifts.

This is a standard closed-subspace and orthogonal-projection argument applied to the original analytic objects. It supplies no canonical full Weil arithmetic/operator identification, signed positivity, literature novelty or Riemann-hypothesis conclusion.

## References

- Truth anchor: `D5/S3/Weil/ZetaBridge/OriginalEvenExterior.evenProjection`
- Truth anchor: `D5/S3/Weil/ZetaBridge/OriginalEvenExterior.exteriorProjection_identity`
- Truth anchor: `D5/S3/Weil/ZetaBridge/OriginalEvenExterior.exteriorProjection_prime`
- Truth anchor: `D5/S3/Weil/ZetaBridge/OriginalEvenExterior.exteriorSpace_eq_even_inf_head_orthogonal`
- Truth anchor: `D5/S3/Weil/ZetaBridge/OriginalEvenExterior.finiteHead`
- Truth anchor: `D5/S3/Weil/ZetaBridge/OriginalEvenExterior.headProjection`
- Dependency: [D5/S3/Weil/ZetaBridge/OriginalEvenCosineComplete](OriginalEvenCosineComplete.md)
