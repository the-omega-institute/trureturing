# Width saturation of symmetric block couplings

## Abstract

A rank-one coupling is bounded by the node width, with an exact equality criterion at a root of width greater than one.

Take a finite family of finite-dimensional real symmetric child blocks A(i) and a direction u in their Euclidean product. Let L be the set of nonleaves, w(i) the child widths, k(i) the child nullities, and k the nullity of the rank-one coupling of the block sum. The node width W is the maximum of one and the sum of w over L.

Leaf nullities are zero. A nonleaf nullity is at most its width, and equality for a nonleaf gives a kernel vector pairing nontrivially with its component of u. These hypotheses are the numerical and state inputs from cotree induction.

In the distance-spectrum application, the direction is the all-ones vector and its pairing is the coordinate sum. The root rule addresses equality in the distance multiplicity bound from Manna, Mandal and Tura, The Spectral Theory of Cographs, Theorem 6.4 and Open Problem 14.2(ii), arXiv:2611.06981v1.

The graph decomposition uses Seinsche's theorem in SimpleGraph.IsP4Free.not_preconnected_or_compl, the Apache-2.0 Lean Pool adaptation by Juan Pablo Traverso Gianini. The node widths use the vicinal chain-cover number, defined by inclusion of the open neighborhood of one vertex in the closed neighborhood of another.

**Theorem 1.1 (The width bound and saturation state).**

$$k \leq W \land (k=W \Rightarrow \operatorname{Flag}\left(U, u\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/SymmetricRankOneWidth.update_block_width` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any nonzero real coupling t, k is bounded by W and equality gives a nonzero kernel pairing. When W > 1, equality holds exactly when L is a singleton {i}, k(i) + 1 = w(i), every block has scalar response g(j), and 1 + t times the sum of g(j) is zero. A flagged child lowers the summed nullity by one. In the scalar branch every nonleaf has a positive deficit, and resonance adds just one to the sum.

**Theorem 1.2 (The one-nonleaf root criterion).**

$$k=W \iff \exists i, L=\{i\} \land 0 < \ell \land \operatorname{k}\left(i\right)+1=\operatorname{w}\left(i\right) \land (\exists g, \operatorname{Response}\left(\operatorname{A}\left(i\right), \operatorname{u}\left(i\right), g\right) \land 1+g-\frac{\ell}{x+1}=0)$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/SymmetricRankOneWidth.update_block_root_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use coupling one, at least two children, W > 1, and a common real shift x. Each leaf has nullity zero and response −1/(x + 1), and the nonleaf hypotheses are as above. Here ell is the number of leaves. Having only one nonleaf makes ell positive, and summing all child responses gives g − ell/(x + 1). In the distance application the shift is eligible when it differs from −1 and −2.

## References

- Truth anchor: `D5/S3/QuadraticForms/SymmetricRankOneWidth.update_block_root_iff`
- Truth anchor: `D5/S3/QuadraticForms/SymmetricRankOneWidth.update_block_width`
- Dependency: [D5/S3/QuadraticForms/SymmetricRankOneKernel](SymmetricRankOneKernel.md)
