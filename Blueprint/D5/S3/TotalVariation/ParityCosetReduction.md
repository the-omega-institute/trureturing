# Total variation on cosets of the noise image

## Abstract

Uniform additive noise gives exact quotient laws and preserves total variation under projection.

**Theorem 1.1 (Quotienting the uniform noise image).**

$$\begin{aligned}\forall (F: \operatorname{Type})(A: \operatorname{Type})(B: \operatorname{Type})(Z: \operatorname{Type}),\\{}[\operatorname{AddCommGroup}(F)][\operatorname{AddCommGroup}(A)][\operatorname{Fintype}(F)][\operatorname{Fintype}(A)][\operatorname{Fintype}(B)][\operatorname{Fintype}(Z)],\\(f: \operatorname{AddMonoidHom}(F,A))(a: Z \to A)(b: Z \to B)(w: Z \to \mathbb{R})(r: B \to \mathbb{R}),\\\operatorname{let} Q:=A/\operatorname{im}(f),\\\operatorname{let} p(x: A \times B):=([x.1],x.2),\\\operatorname{let} \mu(x: A \times B):=\sum_{(z,u) \in Z \times F: (a(z)+f(u),b(z))=x}\frac{w(z)}{\left|F\right|},\\\operatorname{let} \nu(x: A \times B):=\frac{r(x.2)}{\left|A\right|},\\(\forall (q: Q \times B),p_{*}(\mu)(q)=\sum_{z \in Z: p(a(z),b(z))=q}w(z)) \land\\(\forall (q: Q \times B),p_{*}(\nu)(q)=\frac{r(q.2)}{\left|Q\right|}) \land\\\operatorname{TV}(\mu,\nu)=\operatorname{TV}(p_{*}(\mu),p_{*}(\nu))\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/ParityCosetReduction.total_variation_noise_image_quotient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let F and A be finite abelian groups, let B and Z be finite types, and let f be an additive homomorphism from F to A. The shift a and the second readout b depend on the state z. The mass of each source pair (z,u) is w(z) divided by the cardinality of F. Its output is (a(z)+f(u),b(z)). The reference is uniform on A against the second-coordinate mass function r. The formulas allow arbitrary real weights and apply to probability laws when w and r are nonnegative and sum to one.

Write Q for the quotient of A by the image of f, and project the first coordinate to its coset while preserving the second coordinate. The projected joint law is the pushforward of w by the projected pair of readouts. The projected reference is uniform on Q against r. Translating the uniform source by a preimage of a coset displacement proves that the joint mass is constant inside each fiber. The reference mass is likewise constant there, so projection preserves total variation.

For the affine binary parity outputs of section 35.6.8 in Quantum Geometry, take F to be the binary vector space of fair input assignments and Z to be the assignments of the biased bits with their product mass w. Let A and B be the binary vector spaces on the output indices that meet a fair input and those that use biased inputs only, respectively. The fair-input coefficient map is f. The shifts a and the outputs b include the biased contributions and the affine offsets. Each row in A has a nonzero fair coefficient. Flipping that fair bit exchanges the two values of the row while preserving input mass, giving a fair marginal. Thus the product of all output marginals is uniform on A times r, where r is the product of the marginal masses of the outputs in B.

## References

- Truth anchor: `D5/S3/TotalVariation/ParityCosetReduction.total_variation_noise_image_quotient`
- Dependency: [D5/S3/TotalVariation/Equality/FiberwiseEqualDistanceLift](Equality/FiberwiseEqualDistanceLift.md)
