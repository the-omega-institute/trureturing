# Exact EJM Gram probabilities and independent-source noise

## Abstract

The finite exact interface for the triangle-network theory supplement defines the regular-tetrahedron Gram expression for the EJM distribution and the independent-source visibility map. It proves the exact output classes (25/256), (1/256), and (5/256), normalization of the finite table, and the eight-term multi-affine source-noise expansion. These are probability identities and typed finite interfaces. They do not prove EJM triangle locality or nonlocality and do not provide an inflation certificate.

**Definition 1.1 (Regular tetrahedron Gram entry).**

[
operatorname{tetrahedralGram}(i,j)=
egin{cases}
1&i=j,\\
-1/3&i\ne j.
end{cases}
]

*Formalization.* `D5/S3/Quantum/Entanglement/TriangleEJMGramInterface.tetrahedralGram` (`✓ std3`).

*Commentary.*

The four outcomes are represented by the vertices of a regular tetrahedron. The off-diagonal inner product is (-1/3).

**Definition 1.2 (EJM Gram probability).**

[
P(a,b,c)=rac{4+S+6R}{256},
]
where (S=d_{ab}+d_{bc}+d_{ca}) and (R=d_{ab}d_{bc}+d_{bc}d_{ca}+d_{ca}d_{ab}).

*Formalization.* `D5/S3/Quantum/Entanglement/TriangleEJMGramInterface.ejmGramProbability` (`✓ std3`).

**Theorem 1.3 (Exact EJM probability table).**

[
P(a,b,c)=
egin{cases}
25/256& a=b=c,\\
1/256& 	ext{exactly two of }a,b,c	ext{ are equal},\\
5/256& a,b,c	ext{ are all distinct}.
end{cases}
]

*Proof.* Machine-checked by finite case analysis in Lean as `D5/S3/Quantum/Entanglement/TriangleEJMGramInterface.ejmGramProbability_table` (`✓ std3`). The accompanying `ejmGramProbability_nonnegative` and `ejmGramProbability_mass` prove nonnegativity and total mass one. ∎

**Definition 1.4 (Finite EJM law).**

The exact table is packaged as a rational finite probability law over the three-party outcome type.

*Formalization.* `D5/S3/Quantum/Entanglement/TriangleEJMGramInterface.ejmFiniteLaw` (`✓ std3`).

**Definition 1.5 (Independent-source visibility weights).**

For ((w_\alpha,w_\beta,w_\gamma)), the eight coefficients are
[
(1-w_\alpha)^{1-s_\alpha}w_\alpha^{s_\alpha}
(1-w_\beta)^{1-s_\beta}w_\beta^{s_\beta}
(1-w_\gamma)^{1-s_\gamma}w_\gamma^{s_\gamma},
]
enumerated as (000,100,010,110,001,101,011,111).

*Formalization.* `D5/S3/Quantum/Entanglement/TriangleEJMGramInterface.sourceNoiseWeight` (`✓ std3`).

**Definition 1.6 (Independent-source noise map).**

Given eight component tables (P_i), the noisy table is
[
P_{\mathbf w}(a,b,c)=
sum_{i=0}^{7} q_i(w_\alpha,w_\beta,w_\gamma)P_i(a,b,c).
]

*Formalization.* `D5/S3/Quantum/Entanglement/TriangleEJMGramInterface.independentSourceNoise` (`✓ std3`).

**Theorem 1.7 (Eight-term expansion and coefficient normalization).**

The finite map expands to the eight terms in equation (6.2) of the theory supplement. The eight coefficients sum to one, and the map is affine in each edge visibility.

*Proof.* Machine-checked as `independentSourceNoise_eight_terms`, `sourceNoiseWeight_mass`, and `independentSourceNoise_affine_alpha` (`✓ std3`). ∎

## Scope boundary

The component tables in this finite interface are typed placeholders for the eight ideal or maximally mixed source choices. The file does not formalize the Born-rule construction of those tables. It also does not prove (P_{\mathrm{EJM}}\in\mathcal L_\triangle), prove (P_{\mathrm{EJM}}\notin\mathcal L_\triangle), or instantiate an inflation certificate. The imported `IsTriangleLocal` definition remains the classical source-product anchor for the later soundness theorem.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/TriangleEJMGramInterface.ejmGramProbability_table`
- Truth anchor: `D5/S3/Quantum/Entanglement/TriangleEJMGramInterface.independentSourceNoise_eight_terms`
- Existing classical anchor: `D5/S3/Quantum/Entanglement/TriangleSymmetricLocalRefutation.IsTriangleLocal`
