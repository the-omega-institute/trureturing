# Isolating a coordinate in a matching

## Abstract

Each matching uses the chosen coordinate once, so its polynomial is at most linear in that coordinate.

**Definition 1.1 (Remaining coordinates).**

Lean statement: `D5/S3/Geometry/KozakiKakeiAffine.Rest`

*Formalization.* `D5/S3/Geometry/KozakiKakeiAffine.Rest` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The remaining coordinate set omits the distinguished index.

**Definition 1.2 (Coefficient ring).**

Lean statement: `D5/S3/Geometry/KozakiKakeiAffine.Coeff`

*Formalization.* `D5/S3/Geometry/KozakiKakeiAffine.Coeff` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Coefficients are complex multivariate polynomials in the remaining coordinates.

**Definition 1.3 (Single-variable presentation).**

Lean statement: `D5/S3/Geometry/KozakiKakeiAffine.isolate`

*Formalization.* `D5/S3/Geometry/KozakiKakeiAffine.isolate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The chosen variable is extracted as the outer polynomial variable via the option-type decomposition.

**Theorem 1.4 (The distinguished variable).**

$$\forall V : \operatorname{Type}, [\operatorname{DecidableEq}(V)], \forall w : V, \operatorname{isolate}(w,X(w)) = \operatorname{PolynomialX}$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/KozakiKakeiAffine.isolate_X_self` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The variable at the chosen index becomes the outer indeterminate.

**Theorem 1.5 (A remaining variable).**

$$\forall V : \operatorname{Type}, [\operatorname{DecidableEq}(V)], \forall w,j : V, \forall h : j \neq w, \operatorname{isolate}\left(w, \operatorname{X}\left(j\right)\right) = \operatorname{Polynomial}.\operatorname{C}\left(\operatorname{X}\left(\langle j, h \rangle\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/KozakiKakeiAffine.isolate_X_other` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a proof h of j ≠ w, the pair ⟨j, h⟩ indexes a variable in Rest(w), so its variable belongs to Coeff(w). Polynomial.C embeds that coefficient as a constant outer polynomial.

**Theorem 1.6 (Evaluation after isolation).**

$$\forall V : \operatorname{Type}, [\operatorname{DecidableEq}(V)], \forall w : V, p : \operatorname{MvPolynomial}(V,\mathbb{C}), t : \operatorname{Rest}(w) \to \mathbb{C}, z : \mathbb{C}, \operatorname{MvPolynomial}.\operatorname{eval}\left(i \mapsto \operatorname{Option}.\operatorname{elim}\left((\operatorname{Equiv}.\operatorname{optionSubtypeNe}\left(w\right))^{-1}(i), z, t\right), p\right) = \operatorname{Polynomial}.\operatorname{eval}\left(z, \operatorname{Polynomial}.\operatorname{map}\left(\operatorname{MvPolynomial}.\operatorname{eval}\left(t\right), \operatorname{isolate}\left(w, p\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/KozakiKakeiAffine.eval_isolate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The inverse of Equiv.optionSubtypeNe(w) sends w to none and each other index i to some ⟨i, h⟩ in the option type on Rest(w). Option.elim assigns z on none and uses t on the remaining index. Polynomial.map evaluates the coefficients by the ring homomorphism MvPolynomial.eval(t), and Polynomial.eval then evaluates the outer variable at z.

**Theorem 1.7 (Prime coordinate differences).**

$$\forall V : \operatorname{Type}, \forall i,j : V, i \neq j \implies \operatorname{Prime}(\operatorname{diff}(i,j))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/KozakiKakeiAffine.diff_prime` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An oriented difference of two distinct variables is prime. Isolate the second variable to turn the factor into a monic linear polynomial.

**Theorem 1.8 (Different unordered pairs give independent factors).**

$$\forall V : \operatorname{Type}, \forall i,j,a,b : V, a \neq b \implies \neg((a=i \land b=j) \lor (a=j \land b=i)) \implies \neg(\operatorname{diff}(i,j) \mid \operatorname{diff}(a,b))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/KozakiKakeiAffine.diff_not_dvd_of_edges_ne` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Collapse the two coordinates of the divisor to one value and keep the coordinates of the other edge apart. The divisor vanishes but the other factor does not.

**Definition 1.9 (Vertices away from an edge).**

Lean statement: `D5/S3/Geometry/KozakiKakeiAffine.remainingVertex`

*Formalization.* `D5/S3/Geometry/KozakiKakeiAffine.remainingVertex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each endpoint of a different matching edge survives removal of the distinguished vertex.

**Definition 1.10 (Product off the distinguished edge).**

Lean statement: `D5/S3/Geometry/KozakiKakeiAffine.remainingProduct`

*Formalization.* `D5/S3/Geometry/KozakiKakeiAffine.remainingProduct` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The product uses precisely the edges other than the distinguished edge.

**Theorem 1.11 (Isolation at the first endpoint).**

$$\forall m : \mathbb{N}, \forall M : \operatorname{Matching}(m), e : \operatorname{Fin}(m), \forall h : \operatorname{M}\left(e, \operatorname{true}\right) \neq \operatorname{M}\left(e, \operatorname{false}\right), \operatorname{isolate}(M(e,\operatorname{false}),\operatorname{matchingPolynomial}(M)) = \operatorname{Polynomial}.\operatorname{C}(-\operatorname{remainingProduct}(M,e,\operatorname{false})) \cdot \operatorname{Polynomial}.\operatorname{X} + \operatorname{Polynomial}.\operatorname{C}(\operatorname{X}\left(\langle \operatorname{M}\left(e, \operatorname{true}\right), h \rangle\right) \cdot \operatorname{remainingProduct}(M,e,\operatorname{false}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/KozakiKakeiAffine.matching_isolate_left` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let h prove M(e, true) ≠ M(e, false) by injectivity of M. The second endpoint is indexed by ⟨M(e, true), h⟩ in Rest(M(e, false)). The linear coefficient is the negative of the remaining product. The constant coefficient is the second endpoint variable times that product.

**Theorem 1.12 (Isolation at the second endpoint).**

$$\forall m : \mathbb{N}, \forall M : \operatorname{Matching}(m), e : \operatorname{Fin}(m), \forall h : \operatorname{M}\left(e, \operatorname{false}\right) \neq \operatorname{M}\left(e, \operatorname{true}\right), \operatorname{isolate}(M(e,\operatorname{true}),\operatorname{matchingPolynomial}(M)) = \operatorname{Polynomial}.\operatorname{C}(\operatorname{remainingProduct}(M,e,\operatorname{true})) \cdot \operatorname{Polynomial}.\operatorname{X} + \operatorname{Polynomial}.\operatorname{C}(-(\operatorname{X}\left(\langle \operatorname{M}\left(e, \operatorname{false}\right), h \rangle\right) \cdot \operatorname{remainingProduct}(M,e,\operatorname{true})))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/KozakiKakeiAffine.matching_isolate_right` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let h prove M(e, false) ≠ M(e, true) by injectivity of M. The first endpoint is indexed by ⟨M(e, false), h⟩ in Rest(M(e, true)). The linear coefficient is the remaining product. The constant coefficient is the negative of the product of the first endpoint variable and the remaining product.

**Theorem 1.13 (Linearity in every coordinate).**

$$\forall m : \mathbb{N}, \forall M : \operatorname{Matching}(m), w : \operatorname{Col}(m), \exists A,B : \operatorname{Coeff}(w), \operatorname{isolate}(w,\operatorname{matchingPolynomial}(M)) = \operatorname{PolynomialC}(A) \cdot \operatorname{PolynomialX} + \operatorname{PolynomialC}(B)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/KozakiKakeiAffine.matching_exists_linear` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Find the matching edge and endpoint containing the chosen coordinate and apply its ordered isolation formula.

**Theorem 1.14 (Transport of matching factors).**

$$\forall m : \mathbb{N}, \forall s : \operatorname{Perm}(\operatorname{Col}(m)), M : \operatorname{Matching}(m), \operatorname{rename}(s,\operatorname{matchingPolynomial}(M)) = \operatorname{matchingPolynomial}(s \circ M)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/KozakiKakeiAffine.rename_matchingPolynomial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Renaming the polynomial variables composes the endpoint labeling with the permutation.

**Theorem 1.15 (Linearity after a permutation).**

$$\forall m : \mathbb{N}, \forall s : \operatorname{Perm}(\operatorname{Col}(m)), w : \operatorname{Col}(m), \exists A,B : \operatorname{Coeff}(w), \operatorname{isolate}(w,\operatorname{rename}(s,F(m))) = \operatorname{PolynomialC}(A) \cdot \operatorname{PolynomialX} + \operatorname{PolynomialC}(B)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/KozakiKakeiAffine.rename_F_exists_linear` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The difference of the two transported matching products is at most linear in the chosen coordinate.

## References

- Truth anchor: `D5/S3/Geometry/KozakiKakeiAffine.Coeff`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiAffine.Rest`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiAffine.diff_not_dvd_of_edges_ne`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiAffine.diff_prime`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiAffine.eval_isolate`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiAffine.isolate`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiAffine.isolate_X_other`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiAffine.isolate_X_self`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiAffine.matching_exists_linear`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiAffine.matching_isolate_left`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiAffine.matching_isolate_right`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiAffine.remainingProduct`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiAffine.remainingVertex`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiAffine.rename_F_exists_linear`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiAffine.rename_matchingPolynomial`
- Dependency: [D5/S3/Geometry/KozakiKakeiMatching](KozakiKakeiMatching.md)
