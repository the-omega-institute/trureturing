# OriginalWorld

## Abstract

OriginalWorld stores (r,b,d,c₀,c₁,c₂,c₃) with the ordinary coefficients of one polynomial g=Polynomial

OriginalWorld stores (r,b,d,c₀,c₁,c₂,c₃) with the ordinary coefficients of one polynomial g=Polynomial.ofFn 4 c. Its readings use the literal source matrix P(r,b), chronological left products and d+g(i)tr(QᵢP). OriginalParent includes every original history row and requires only the strict source and a nonzero whole polynomial.

The coefficient vector of samples a is [a₀,-11a₀/6+3a₁-3a₂/2+a₃/3,a₀-5a₁/2+2a₂-a₃/2,-a₀/6+a₁/2-a₂/2+a₃/6]. It represents precisely the same polynomial. Decoding evaluates that entire polynomial at the original four nodes. Mathlib’s interpolation uniqueness and coefficient-vector reconstruction supply both inverses for all polynomials of degree at most three.

The original parent and the full parent coordinates correspond in both directions, including the unchanged gain, drift and chronological response. The coefficient transform is linear and continuous; the inverse parent coordinates are (r,b,d-24). Positivity of b,j,n,T makes reconstruction continuous at every strict source. Hence originalParentHomeomorph is a homeomorphism for the original ordinary coefficient topology.

The source matrix parametrization also preserves topology: r=P₀₀ and b=P₀₁ recover its coordinates continuously, while P(r,b) is continuous on b>0. This gives the same source topology if worlds are written as (P,g,d). No source normalization or quotient is taken.

For encoded_parent the complete telescope is C=(r,b,e) in Coordinates=Real times Real times Real and hC:StrictParent C. These hypotheses are exactly 0<r, r<1, 0<b and e parentLambda(r,b)+(24/5)(b-1/8)parentB(b)=0. parentWorld C uses d=24+e and the single sample vector [-24-e,-e/sourceJ(r,b),(27/5-e)/(1+b),-e/sourceN(r,b)]. encodeWorld converts this vector to the ordinary coefficients of the same cubic. The conclusion is OriginalParent(encodeWorld(parentWorld C)), including every literal history row; no regularity or nonzero-sample hypothesis is added.

For encoded_response the sole parameter is C:Coordinates; StrictParent C is not required. Its equality is originalResponse(encodeWorld(parentWorld C))=response C, with both sides the ordered pair of actual fifth and sixth responses. The encoding preserves the entire polynomial, so this identity does not fit a new gain to either reading. The regular analytic chart applies both statements to C=(t b,b,regularError(t b,b)).

The bounded-response estimate is for the actual drift d and all four ordinary coefficients, not only for gain samples. The fixed coefficient transform gives the explicit bound 10 max(G,0) from a bound G on the samples, while |d|≤24+max(D,0) follows from |ε|≤D. The map includes zero drift, zero gain samples, lower degrees and repeated roots; only the identically zero gain is excluded by the literal history.

**Theorem 1.1 (originalParentHomeomorph).**

Lean statement: `D5/S3/Observer/CubicGain/OriginalWorld.originalParentHomeomorph`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/CubicGain/OriginalWorld.originalParentHomeomorph` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The map originalParentHomeomorph is a homeomorphism from ParentOverOpen to OriginalOverOpen in ordinary polynomial coefficient topology. It preserves the source, drift, whole polynomial and actual response in both directions.

**Theorem 1.2 (original coordinates).**

Lean statement: `D5/S3/Observer/CubicGain/OriginalWorld.original_coordinates`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/CubicGain/OriginalWorld.original_coordinates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original parent W, decoding gives strict parent coordinates, encoding their reconstructed parent world returns W, and their response equals originalResponse W.

**Theorem 1.3 (encoded strict parent).**

Lean statement: `D5/S3/Observer/CubicGain/OriginalWorld.encoded_parent`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/CubicGain/OriginalWorld.encoded_parent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every strict parent coordinate triple C, encoding parentWorld C produces an OriginalParent with the literal original history rows.

**Theorem 1.4 (encoded actual response).**

Lean statement: `D5/S3/Observer/CubicGain/OriginalWorld.encoded_response`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/CubicGain/OriginalWorld.encoded_response` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every coordinate triple C, the actual original response of encodeWorld (parentWorld C) equals the response computed from C.

**Theorem 1.5 (bounded response coefficients).**

Lean statement: `D5/S3/Observer/CubicGain/OriginalWorld.bounded_response_coefficients`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/CubicGain/OriginalWorld.bounded_response_coefficients` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real M there are bounds D,G such that every original parent with |P₅|≤M has |d|≤D and all four ordinary polynomial coefficients bounded in absolute value by G.

## References

- Truth anchor: `D5/S3/Observer/CubicGain/OriginalWorld.bounded_response_coefficients`
- Truth anchor: `D5/S3/Observer/CubicGain/OriginalWorld.encoded_parent`
- Truth anchor: `D5/S3/Observer/CubicGain/OriginalWorld.encoded_response`
- Truth anchor: `D5/S3/Observer/CubicGain/OriginalWorld.originalParentHomeomorph`
- Truth anchor: `D5/S3/Observer/CubicGain/OriginalWorld.original_coordinates`
- Dependency: [D5/S3/Observer/CubicGain/ResponseProper](ResponseProper.md)
