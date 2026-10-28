# Affine suborbits of the order-nine BCCB family

## Abstract

Every nonconstant affine dephasing of the order-nine BCCB sum-one locus lies in the cancelling-pair or equilateral-triple family.

Use zero-based matrix indices 0 through 8 and parameter positions 0 through 3. Fin(n) denotes the index set from 0 to n minus one. The parameter space Fin(p) to R is R to the power p. LinearMap(R,V,R) denotes real linear maps from V to R. Write i for the imaginary unit and omega for the positive cubic root in `D5/S3/Observer/WindowRegister.windowRoot`:

$$
\omega = \operatorname{windowRoot}\left(3\right) = e^{\frac{2 \cdot \pi \cdot i}{3}}
$$

**Definition 1.1 (The symmetric block-circulant matrix).**

$$\forall (x: \mathbb{C}), (\forall (y: \mathbb{C}), (\forall (u: \mathbb{C}), (\forall (w: \mathbb{C}), (\operatorname{bccb}\left(x, y, u, w\right) = \begin{pmatrix}1&x&x&y&u&w&y&w&u\\x&1&x&w&y&u&u&y&w\\x&x&1&u&w&y&w&u&y\\y&w&u&1&x&x&y&u&w\\u&y&w&x&1&x&w&y&u\\w&u&y&x&x&1&u&w&y\\y&u&w&y&w&u&1&x&x\\w&y&u&u&y&w&x&1&x\\u&w&y&w&u&y&x&x&1\end{pmatrix}))))$$

*Formalization.* `D5/S3/Quantum/Tomography/MUB/BCCBOrderNineAffineSuborbits.bccb` (`✓ std3`).

*Citation.* Bengt R. Karlsson (2016). *BCCB complex Hadamard matrices of order 9, and MUBs*. DOI: [10.1016/j.laa.2016.04.012](https://doi.org/10.1016/j.laa.2016.04.012). URL: <https://arxiv.org/abs/1604.03770v1>.

*Commentary.*

The rows and columns of this array are ordered 0 through 8. It is the matrix of Section 4, Eq. (4.1). Its definition allows arbitrary complex x, y, u and w; unimodularity and the sum-one condition enter the classification below.

**Definition 1.2 (Canonical dephasing).**

$$\forall (H: \operatorname{Matrix}\left(\operatorname{Fin}\left(9\right), \operatorname{Fin}\left(9\right), \mathbb{C}\right)), (\forall (a: \operatorname{Fin}\left(9\right)), (\forall (b: \operatorname{Fin}\left(9\right)), (\operatorname{dephase}\left(H\right)_{a,b} = \frac{H_{a,b}}{(H_{a,0} \cdot H_{0,b})})))$$

*Formalization.* `D5/S3/Quantum/Tomography/MUB/BCCBOrderNineAffineSuborbits.dephase` (`✓ std3`).

*Citation.* Bengt R. Karlsson (2016). *BCCB complex Hadamard matrices of order 9, and MUBs*. DOI: [10.1016/j.laa.2016.04.012](https://doi.org/10.1016/j.laa.2016.04.012). URL: <https://arxiv.org/abs/1604.03770v1>.

*Commentary.*

Divide entry ab by the product of entry a0 and entry 0b. On matrices with nonzero first row and column and entry 00 equal to one, this makes the first row and column equal to one. The definition itself is total, using complex division also when a denominator is zero.

**Definition 1.3 (The four parameter functions).**

$$\forall (p: \mathbb{N}), (\forall (x: ((\operatorname{Fin}\left(p\right) \to \mathbb{R}) \to \mathbb{C})), (\forall (y: ((\operatorname{Fin}\left(p\right) \to \mathbb{R}) \to \mathbb{C})), (\forall (u: ((\operatorname{Fin}\left(p\right) \to \mathbb{R}) \to \mathbb{C})), (\forall (w: ((\operatorname{Fin}\left(p\right) \to \mathbb{R}) \to \mathbb{C})), (\forall (t: (\operatorname{Fin}\left(p\right) \to \mathbb{R})), (\operatorname{params}\left(x, y, u, w, t\right) = [x\left(t\right), y\left(t\right), u\left(t\right), w\left(t\right)]))))))$$

*Formalization.* `D5/S3/Quantum/Tomography/MUB/BCCBOrderNineAffineSuborbits.params` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Bengt R. Karlsson (2016). *BCCB complex Hadamard matrices of order 9, and MUBs*. DOI: [10.1016/j.laa.2016.04.012](https://doi.org/10.1016/j.laa.2016.04.012). URL: <https://arxiv.org/abs/1604.03770v1>.

*Commentary.*

The ordered tuple retains the parameter positions x, y, u, w. Each function is defined on the whole real parameter space; later equalities are required only on U.

**Definition 1.4 (Affine phases on a set).**

$$\forall (p: \mathbb{N}), (\forall (U: \operatorname{Set}\left((\operatorname{Fin}\left(p\right) \to \mathbb{R})\right)), (\forall (F: ((\operatorname{Fin}\left(p\right) \to \mathbb{R}) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(9\right), \operatorname{Fin}\left(9\right), \mathbb{C}\right))), ((\operatorname{IsAffineOn}\left(U, F\right)) \Leftrightarrow (\forall (a: \operatorname{Fin}\left(9\right)), (\forall (b: \operatorname{Fin}\left(9\right)), (\exists (c_{a,b}: \mathbb{C}), (\exists (L_{a,b}: \operatorname{LinearMap}\left(\mathbb{R}, (\operatorname{Fin}\left(p\right) \to \mathbb{R}), \mathbb{R}\right)), (\forall (t: (\operatorname{Fin}\left(p\right) \to \mathbb{R})), ((t \in U) \Rightarrow (F\left(t\right)_{a,b} = c_{a,b} \cdot \operatorname{exp}\left(\operatorname{ofReal}\left(\left(L_{a,b}\right)\left(t\right)\right) \cdot i\right)))))))))))$$

*Formalization.* `D5/S3/Quantum/Tomography/MUB/BCCBOrderNineAffineSuborbits.IsAffineOn` (`✓ std3`).

*Citation.* Bengt R. Karlsson (2016). *BCCB complex Hadamard matrices of order 9, and MUBs*. DOI: [10.1016/j.laa.2016.04.012](https://doi.org/10.1016/j.laa.2016.04.012). URL: <https://arxiv.org/abs/1604.03770v1>.

*Commentary.*

For each matrix entry ab, choose its own complex coefficient c(ab) and real linear form L(ab). The entry is c(ab) times exp(i L(ab)(t)) throughout U. The coefficient includes a constant phase. This predicate alone imposes no openness, nonemptiness, continuity or unit-modulus assumption.

**Definition 1.5 (The affine-suborbit classification).**

$$(\operatorname{claim}) \Leftrightarrow (\forall (p: \mathbb{N}), (\forall (U: \operatorname{Set}\left((\operatorname{Fin}\left(p\right) \to \mathbb{R})\right)), ((\operatorname{IsOpen}\left(U\right)) \Rightarrow ((\operatorname{Nonempty}\left(U\right)) \Rightarrow (\forall (x: ((\operatorname{Fin}\left(p\right) \to \mathbb{R}) \to \mathbb{C})), (\forall (y: ((\operatorname{Fin}\left(p\right) \to \mathbb{R}) \to \mathbb{C})), (\forall (u: ((\operatorname{Fin}\left(p\right) \to \mathbb{R}) \to \mathbb{C})), (\forall (w: ((\operatorname{Fin}\left(p\right) \to \mathbb{R}) \to \mathbb{C})), ((\forall (t: (\operatorname{Fin}\left(p\right) \to \mathbb{R})), ((t \in U) \Rightarrow ((\left|x\left(t\right)\right| = 1) \land ((\left|y\left(t\right)\right| = 1) \land ((\left|u\left(t\right)\right| = 1) \land ((\left|w\left(t\right)\right| = 1) \land (x\left(t\right) + y\left(t\right) + u\left(t\right) + w\left(t\right) = 1))))))) \Rightarrow ((\operatorname{IsAffineOn}\left(U, (t \mapsto \operatorname{dephase}\left(\operatorname{bccb}\left(x\left(t\right), y\left(t\right), u\left(t\right), w\left(t\right)\right)\right))\right)) \Rightarrow ((\exists (t_{1}: (\operatorname{Fin}\left(p\right) \to \mathbb{R})), ((t_{1} \in U) \land (\exists (t_{2}: (\operatorname{Fin}\left(p\right) \to \mathbb{R})), ((t_{2} \in U) \land (\operatorname{params}\left(x, y, u, w, t_{1}\right) \ne \operatorname{params}\left(x, y, u, w, t_{2}\right)))))) \Rightarrow (\exists (\pi: \operatorname{Perm}\left(\operatorname{Fin}\left(4\right)\right)), ((\exists (\mu: ((\operatorname{Fin}\left(p\right) \to \mathbb{R}) \to \mathbb{C})), (\forall (t: (\operatorname{Fin}\left(p\right) \to \mathbb{R})), ((t \in U) \Rightarrow ((\operatorname{params}\left(x, y, u, w, t\right) \circ \pi) = [\mu\left(t\right), -(\mu\left(t\right)), -(\omega), -(\omega^{2})])))) \lor (\exists (\xi: ((\operatorname{Fin}\left(p\right) \to \mathbb{R}) \to \mathbb{C})), (\forall (t: (\operatorname{Fin}\left(p\right) \to \mathbb{R})), ((t \in U) \Rightarrow ((\operatorname{params}\left(x, y, u, w, t\right) \circ \pi) = [1, \xi\left(t\right), \omega \cdot \xi\left(t\right), \omega^{2} \cdot \xi\left(t\right)])))))))))))))))))$$

*Formalization.* `D5/S3/Quantum/Tomography/MUB/BCCBOrderNineAffineSuborbits.claim` (`✓ std3`).

*Citation.* Bengt R. Karlsson (2016). *BCCB complex Hadamard matrices of order 9, and MUBs*. DOI: [10.1016/j.laa.2016.04.012](https://doi.org/10.1016/j.laa.2016.04.012). URL: <https://arxiv.org/abs/1604.03770v1>.

*Commentary.*

This is the parameter-space formulation of Karlsson's Conjecture 3. The set U is any nonempty open subset of a finite-dimensional real space. On U the four parameters have modulus one, sum to one, and give an affine dephasing. Nonconstancy means that two points of U have different ordered parameter tuples. A single permutation, independent of t, then puts every tuple into one of the two displayed families from Sections 8.1 and 8.2. No connectedness assumption or positive-dimension hypothesis is added; nonconstancy excludes dimension zero. The functions mu and xi are defined on the whole parameter space. Their values on U have modulus one by the tuple identities and the hypotheses.

**Theorem 1.6 (Only the cancelling pair and equilateral triple occur).**

$$\operatorname{claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/MUB/BCCBOrderNineAffineSuborbits.result` (`✓ std3`). ∎

*Resolves.* `Problems/karlsson-2016-bccb-order-nine-affine-suborbits` (proved) by `D5/S3/Quantum/Tomography/MUB/BCCBOrderNineAffineSuborbits.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"karlsson-2016-bccb-order-nine-affine-suborbits","declaration_gid":"D5/S3/Quantum/Tomography/MUB/BCCBOrderNineAffineSuborbits.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Bengt R. Karlsson (2016). *BCCB complex Hadamard matrices of order 9, and MUBs*. DOI: [10.1016/j.laa.2016.04.012](https://doi.org/10.1016/j.laa.2016.04.012). URL: <https://arxiv.org/abs/1604.03770v1>.

*Commentary.*

Let D(t) be the dephasing of H(x(t), y(t), u(t), w(t)). Its entries at the zero-based positions (1,2), (3,6), (4,8) and (5,7) are respectively 1/x(t), 1/y(t), 1/u(t) and 1/w(t). Inverting their affine expressions writes each parameter as c(j) exp(i L(j)(t)), where every coefficient c(j) has modulus one.

The sum of these four exponential functions is real analytic on the whole parameter space. Since it equals one on a nonempty open set, analytic continuation makes the sum identity hold everywhere. The functions t maps to exp(i L(j)(t)) are characters of the additive parameter group. Linear independence of distinct characters forces the coefficients in the trivial-character class to sum to one, and those in each nontrivial class to sum to zero.

The trivial class is nonempty. Every nontrivial class that occurs contains at least two members, since its coefficients are nonzero and sum to zero. Nonconstancy supplies such a class. With only four positions, there is exactly one nontrivial class, of size two or three, and all remaining positions belong to the trivial class.

If the nontrivial class has size two, its coefficients are a and minus a. The two constant coefficients b and c have modulus one and satisfy b + c = 1. Thus b squared minus b plus one equals zero, and the constants are minus omega and minus omega squared in either order. Taking mu(t) to be a times the common character gives the cancelling-pair family.

If the nontrivial class has size three, the remaining constant is one. Its three unit coefficients a, b, c sum to zero. Dividing by a shows that b/a and c/a are omega and omega squared in either order. Taking xi(t) to be a times the common character gives the equilateral-triple family. In both cases a fixed permutation arranges the positions as in the claim.

## References

- Truth anchor: `D5/S3/Observer/WindowRegister.windowRoot`
- Truth anchor: `D5/S3/Quantum/Tomography/MUB/BCCBOrderNineAffineSuborbits.IsAffineOn`
- Truth anchor: `D5/S3/Quantum/Tomography/MUB/BCCBOrderNineAffineSuborbits.bccb`
- Truth anchor: `D5/S3/Quantum/Tomography/MUB/BCCBOrderNineAffineSuborbits.claim`
- Truth anchor: `D5/S3/Quantum/Tomography/MUB/BCCBOrderNineAffineSuborbits.dephase`
- Truth anchor: `D5/S3/Quantum/Tomography/MUB/BCCBOrderNineAffineSuborbits.params`
- Truth anchor: `D5/S3/Quantum/Tomography/MUB/BCCBOrderNineAffineSuborbits.result`
- Dependency: [D5/S3/Observer/WindowRegister](../../../Observer/WindowRegister.md)
