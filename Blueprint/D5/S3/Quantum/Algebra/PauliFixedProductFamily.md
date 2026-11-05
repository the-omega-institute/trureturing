# Fixed positive products and the complete actual Pauli family

## Abstract

Fixed spin products, the actual real Pauli action and complete unaveraged residual with exact local data.

Notation is shared by every display below. J is EuclideanSpace over the reals on Fin 4, identified with a scalar and a spatial vector in real three-space; V is its real Hilbert tensor product. T(a,b) denotes a tensor b. Coordinates a_i have i in Fin 4. All inner products and norms are the fixed Euclidean and positive tensor-product ones. Scalar juxtaposition denotes real scalar multiplication. The cross and dot operations are the usual real three-dimensional cross and dot products. An ordered pair (scalar, spatial triple) denotes its four-vector in J. The vectors e(i) are EuclideanSpace.single i 1; e(0) is the unit, e(1), e(2), e(3) are x, y, z. b is localBasis and B is jointBasis, the complete orthonormal bases. Every displayed parameter and vector is explicitly quantified.

$$
(J = \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(4\right)\right)) \land ((V = \operatorname{TensorProduct}\left(\mathbb{R}, J, J\right)) \land (\forall i \in \operatorname{Fin}\left(4\right),\; \operatorname{e}\left(i\right) = \operatorname{single}\left(i, 1\right)))
$$

$$
\forall a \in J,\; \forall b \in J,\; (\operatorname{S}\left(a, b\right) = (a_{0} \cdot b_{0} + \operatorname{dot}\left((a_{1}, a_{2}, a_{3}), (b_{1}, b_{2}, b_{3})\right), a_{0} \cdot (b_{1}, b_{2}, b_{3}) + b_{0} \cdot (a_{1}, a_{2}, a_{3}))) \land (\operatorname{C}\left(a, b\right) = (0, \operatorname{cross}\left((a_{1}, a_{2}, a_{3}), (b_{1}, b_{2}, b_{3})\right)))
$$

$$
\forall t \in \mathbb{R},\; \forall a \in J,\; \forall b \in J,\; \operatorname{D}\left(t, a, b\right) = (0, \operatorname{cross}\left((a_{1}, a_{2}, a_{3} + t \cdot a_{0}), (b_{1}, b_{2}, b_{3})\right))
$$

$$
\forall a \in J,\; \forall b \in J,\; \forall c \in J,\; \forall d \in J,\; \operatorname{M}\left(\operatorname{T}\left(a, b\right), \operatorname{T}\left(c, d\right)\right) = \operatorname{T}\left(\operatorname{S}\left(a, c\right), \operatorname{S}\left(b, d\right)\right) - \operatorname{T}\left(\operatorname{C}\left(a, c\right), \operatorname{C}\left(b, d\right)\right)
$$

$$
\forall t \in \mathbb{R},\; \forall a \in J,\; \forall b \in J,\; \forall c \in J,\; \forall d \in J,\; \operatorname{Gamma}\left(t, \operatorname{T}\left(a, b\right), \operatorname{T}\left(c, d\right)\right) = \operatorname{T}\left(\operatorname{D}\left(t, a, c\right), \operatorname{S}\left(b, d\right)\right) + \operatorname{T}\left(\operatorname{S}\left(a, c\right), \operatorname{D}\left(t, b, d\right)\right)
$$

S, C and D(t) denote the existing bilinear maps S, C, D t; M and Gamma(t) are the existing fixed joint product and actual joint action, extended linearly from pure tensors. E(t,H,X,Y) is E t H X Y. R(t) is reportSquared t, with all six basis indices summed independently. Each output norm includes every coordinate; there is no averaging.

$$
\forall t \in \mathbb{R},\; \forall H \in V,\; \forall X \in V,\; \forall Y \in V,\; \operatorname{E}\left(t, H, X, Y\right) = \operatorname{Gamma}\left(t, H, \operatorname{M}\left(X, Y\right)\right) - \operatorname{M}\left(\operatorname{Gamma}\left(t, H, X\right), Y\right) - \operatorname{M}\left(X, \operatorname{Gamma}\left(t, H, Y\right)\right)
$$

$$
\forall t \in \mathbb{R},\; \operatorname{R}\left(t\right) = \sum_{i,j,k,l,m,n: \operatorname{Fin}\left(4\right)}(\Vert \operatorname{E}\left(t, \operatorname{T}\left(\operatorname{e}\left(i\right), \operatorname{e}\left(j\right)\right), \operatorname{T}\left(\operatorname{e}\left(k\right), \operatorname{e}\left(l\right)\right), \operatorname{T}\left(\operatorname{e}\left(m\right), \operatorname{e}\left(n\right)\right)\right)\Vert)^{2}
$$

U(t) means unitOperator t, the continuous linear map b mapped to D(t,e(0),b); its norm with subscript op is the operator norm. G(t) means actionGram t, H(t) means labelGram t. Adjoint is taken for the same Euclidean inner product. W(t) means actionSupport t, the real span of all actual D(t,e(i),e(j)); Z(t) means commonFixed t, the intersection of the four action kernels. ker D(t) is the kernel of the label-linear map a mapped to D(t,a), whereas D(t,a)=0 is equality of linear operators. Orthogonal complement always uses the fixed Euclidean inner product.

$$
\forall t \in \mathbb{R},\; (\forall b \in J,\; \operatorname{U}\left(t, b\right) = \operatorname{D}\left(t, \operatorname{e}\left(0\right), b\right)) \land ((\operatorname{G}\left(t\right) = \sum_{i: \operatorname{Fin}\left(4\right)}\operatorname{compose}\left(\operatorname{adj}\left(\operatorname{D}\left(t, \operatorname{e}\left(i\right)\right)\right), \operatorname{D}\left(t, \operatorname{e}\left(i\right)\right)\right)) \land ((\operatorname{H}\left(t\right) = \sum_{i: \operatorname{Fin}\left(4\right)}\operatorname{compose}\left(\operatorname{adj}\left(\operatorname{flipD}\left(t, \operatorname{e}\left(i\right)\right)\right), \operatorname{flipD}\left(t, \operatorname{e}\left(i\right)\right)\right)) \land ((\forall a \in J,\; \forall b \in J,\; \operatorname{flipD}\left(t, b, a\right) = \operatorname{D}\left(t, a, b\right)) \land ((\operatorname{W}\left(t\right) = \operatorname{span}\left(\mathbb{R}, \{ v: J \mid \exists i \in \operatorname{Fin}\left(4\right),\; \exists j \in \operatorname{Fin}\left(4\right),\; v = \operatorname{D}\left(t, \operatorname{e}\left(i\right), \operatorname{e}\left(j\right)\right) \}\right)) \land (\operatorname{Z}\left(t\right) = \{ a: J \mid \forall i \in \operatorname{Fin}\left(4\right),\; \operatorname{D}\left(t, \operatorname{e}\left(i\right), a\right) = 0 \})))))
$$

Lambda(t) is positiveActionSpectrum t; sigma(t) is actionGap t, the square root of the infimum of that set. Membership and universal inequalities are both displayed for every greatest or least value below, so attainment and the full domain are retained. kappa(i,j,k) is curvature i j k on precisely the original finite basis, not a redefined unit-ball maximum.

$$
\forall t \in \mathbb{R},\; (\operatorname{Lambda}\left(t\right) = \{ lambda: \mathbb{R} \mid (0 < lambda) \land (\exists a \in J,\; (a \ne 0) \land (\operatorname{G}\left(t, a\right) = lambda \cdot a)) \}) \land (\operatorname{sigma}\left(t\right) = \sqrt{\operatorname{inf}\left(\operatorname{Lambda}\left(t\right)\right)})
$$

$$
\forall i \in \operatorname{Fin}\left(4\right),\; \forall j \in \operatorname{Fin}\left(4\right),\; \forall k \in \operatorname{Fin}\left(4\right),\; \operatorname{kappa}\left(i, j, k\right) = \operatorname{S}\left(\operatorname{e}\left(i\right), \operatorname{S}\left(\operatorname{e}\left(j\right), \operatorname{e}\left(k\right)\right)\right) - \operatorname{S}\left(\operatorname{e}\left(j\right), \operatorname{S}\left(\operatorname{e}\left(i\right), \operatorname{e}\left(k\right)\right)\right)
$$

**Theorem 1.1 (The actual residual scales on all joint inputs).**

$$\forall t \in \mathbb{R},\; \forall H \in V,\; \forall X \in V,\; \forall Y \in V,\; \operatorname{E}\left(t, H, X, Y\right) = t \cdot \operatorname{E}\left(1, H, X, Y\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/PauliFixedProductFamily.residual_scaling` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual action and residual are affine in the real parameter. The zero-parameter residual vanishes on the complete product basis, and multilinearity extends this equality through the basis span in every slot, including arbitrary sums of pure tensors.

**Theorem 1.2 (All ordered labels and every output coordinate).**

$$\forall t \in \mathbb{R},\; \operatorname{R}\left(t\right) = 288 \cdot (t)^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/PauliFixedProductFamily.full_report` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complete unaveraged report uses 4096 ordered triples of the sixteen-element joint basis. At parameter one, six complete first-label blocks contribute 48 each; the other ten blocks vanish. Each squared norm includes every output coordinate. All-input scaling gives the displayed identity for every real parameter.

**Theorem 1.3 (The complete fixed realization and all four original identities).**

$$\forall t \in \mathbb{R},\; (\operatorname{dim}\left(\mathbb{R}, J\right) = 4) \land ((\operatorname{dim}\left(\mathbb{R}, V\right) = 16) \land ((\forall i \in \operatorname{Fin}\left(4\right),\; \operatorname{b}\left(i\right) = \operatorname{e}\left(i\right)) \land ((\forall i \in \operatorname{Fin}\left(4\right),\; \forall j \in \operatorname{Fin}\left(4\right),\; \operatorname{B}\left(i, j\right) = \operatorname{T}\left(\operatorname{e}\left(i\right), \operatorname{e}\left(j\right)\right)) \land ((\forall a \in J,\; \forall b \in J,\; \operatorname{S}\left(a, b\right) = \operatorname{S}\left(b, a\right)) \land ((\forall a \in J,\; \operatorname{S}\left(\operatorname{e}\left(0\right), a\right) = a) \land ((\forall a \in J,\; \forall b \in J,\; \forall c \in J,\; \langle \operatorname{S}\left(a, b\right),c\rangle = \langle a,\operatorname{S}\left(b, c\right)\rangle) \land ((\forall a \in J,\; \forall b \in J,\; \forall c \in J,\; \operatorname{D}\left(t, a, \operatorname{S}\left(b, c\right)\right) = \operatorname{S}\left(\operatorname{D}\left(t, a, b\right), c\right) + \operatorname{S}\left(b, \operatorname{D}\left(t, a, c\right)\right)) \land ((\operatorname{D}\left(t, \operatorname{e}\left(1\right), \operatorname{e}\left(2\right)\right) = \operatorname{e}\left(3\right)) \land ((\forall X \in V,\; \forall Y \in V,\; \operatorname{M}\left(X, Y\right) = \operatorname{M}\left(Y, X\right)) \land ((\forall X \in V,\; \operatorname{M}\left(\operatorname{T}\left(\operatorname{e}\left(0\right), \operatorname{e}\left(0\right)\right), X\right) = X) \land ((\forall X \in V,\; \forall Y \in V,\; \forall Z \in V,\; \langle \operatorname{M}\left(X, Y\right),Z\rangle = \langle X,\operatorname{M}\left(Y, Z\right)\rangle) \land ((\forall X \in V,\; (0 \le \langle X,X\rangle) \land ((\langle X,X\rangle = 0) \Leftrightarrow (X = 0))) \land ((\forall a \in J,\; \forall b \in J,\; \forall c \in J,\; \forall d \in J,\; (\operatorname{M}\left(\operatorname{T}\left(a, \operatorname{e}\left(0\right)\right), \operatorname{T}\left(c, d\right)\right) = \operatorname{T}\left(\operatorname{S}\left(a, c\right), d\right)) \land ((\operatorname{M}\left(\operatorname{T}\left(\operatorname{e}\left(0\right), b\right), \operatorname{T}\left(c, d\right)\right) = \operatorname{T}\left(c, \operatorname{S}\left(b, d\right)\right)) \land ((\operatorname{Gamma}\left(t, \operatorname{T}\left(a, b\right), \operatorname{T}\left(c, \operatorname{e}\left(0\right)\right)\right) = \operatorname{T}\left(\operatorname{D}\left(t, a, c\right), b\right)) \land (\operatorname{Gamma}\left(t, \operatorname{T}\left(a, b\right), \operatorname{T}\left(\operatorname{e}\left(0\right), d\right)\right) = \operatorname{T}\left(a, \operatorname{D}\left(t, b, d\right)\right))))) \land (\operatorname{R}\left(t\right) = 288 \cdot (t)^{2}))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/PauliFixedProductFamily.family_contract` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

These are the complete fifteen conjuncts of the realization contract. The fixed products and positive inner products serve every parameter. No alternation, Jacobi, vanishing unit generator or global joint derivation law is assumed.

**Theorem 1.4 (Attained defects, all-input bounds and operator norm).**

$$\forall t \in \mathbb{R},\; ((\frac{\lvert t\rvert}{2} \in \{ s: \mathbb{R} \mid \exists a \in J,\; (\Vert a\Vert = 1) \land (s = \Vert \operatorname{D}\left(t, a, a\right)\Vert) \}) \land (\forall r \in \mathbb{R},\; (r \in \{ s: \mathbb{R} \mid \exists a \in J,\; (\Vert a\Vert = 1) \land (s = \Vert \operatorname{D}\left(t, a, a\right)\Vert) \}) \Rightarrow (r \le \frac{\lvert t\rvert}{2}))) \land (((\lvert t\rvert \in \{ s: \mathbb{R} \mid \exists b \in J,\; (\Vert b\Vert = 1) \land (s = \Vert \operatorname{D}\left(t, \operatorname{e}\left(0\right), b\right)\Vert) \}) \land (\forall r \in \mathbb{R},\; (r \in \{ s: \mathbb{R} \mid \exists b \in J,\; (\Vert b\Vert = 1) \land (s = \Vert \operatorname{D}\left(t, \operatorname{e}\left(0\right), b\right)\Vert) \}) \Rightarrow (r \le \lvert t\rvert))) \land ((\forall a \in J,\; \forall b \in J,\; \Vert \operatorname{S}\left(a, b\right)\Vert \le \sqrt{2} \cdot \Vert a\Vert \cdot \Vert b\Vert) \land ((\forall a \in J,\; \forall b \in J,\; \Vert \operatorname{D}\left(t, a, b\right)\Vert \le \sqrt{1 + (t)^{2}} \cdot \Vert a\Vert \cdot \Vert b\Vert) \land (\Vert \operatorname{U}\left(t\right)\Vert_{op} = \lvert t\rvert))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/PauliFixedProductFamily.exact_defects` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The diagonal maximum is attained at (e(0)+e(1))/sqrt(2); the unit-generator maximum is attained at e(1). The universal estimates follow from nonnegative square decompositions on arbitrary real coordinates, and the last conjunct is the norm of the actual continuous unit-generator operator.

**Theorem 1.5 (Every original local constant is sharp).**

$$\forall t \in \mathbb{R},\; (\Vert \operatorname{e}\left(0\right)\Vert = 1) \land (((\sqrt{2} \in \{ s: \mathbb{R} \mid \exists a \in J,\; \exists b \in J,\; (\Vert a\Vert = 1) \land ((\Vert b\Vert = 1) \land (s = \Vert \operatorname{S}\left(a, b\right)\Vert)) \}) \land (\forall r \in \mathbb{R},\; (r \in \{ s: \mathbb{R} \mid \exists a \in J,\; \exists b \in J,\; (\Vert a\Vert = 1) \land ((\Vert b\Vert = 1) \land (s = \Vert \operatorname{S}\left(a, b\right)\Vert)) \}) \Rightarrow (r \le \sqrt{2}))) \land (((\sqrt{1 + (t)^{2}} \in \{ s: \mathbb{R} \mid \exists a \in J,\; \exists b \in J,\; (\Vert a\Vert = 1) \land ((\Vert b\Vert = 1) \land (s = \Vert \operatorname{D}\left(t, a, b\right)\Vert)) \}) \land (\forall r \in \mathbb{R},\; (r \in \{ s: \mathbb{R} \mid \exists a \in J,\; \exists b \in J,\; (\Vert a\Vert = 1) \land ((\Vert b\Vert = 1) \land (s = \Vert \operatorname{D}\left(t, a, b\right)\Vert)) \}) \Rightarrow (r \le \sqrt{1 + (t)^{2}}))) \land ((1 \in \{ s: \mathbb{R} \mid \exists i \in \operatorname{Fin}\left(4\right),\; \exists j \in \operatorname{Fin}\left(4\right),\; \exists k \in \operatorname{Fin}\left(4\right),\; s = \Vert \operatorname{kappa}\left(i, j, k\right)\Vert \}) \land (\forall r \in \mathbb{R},\; (r \in \{ s: \mathbb{R} \mid \exists i \in \operatorname{Fin}\left(4\right),\; \exists j \in \operatorname{Fin}\left(4\right),\; \exists k \in \operatorname{Fin}\left(4\right),\; s = \Vert \operatorname{kappa}\left(i, j, k\right)\Vert \}) \Rightarrow (r \le 1)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/PauliFixedProductFamily.exact_constants` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The unit length is one. The spin bound is attained with both inputs (e(0)+e(1))/sqrt(2), and the action bound at (t e(0)+e(3))/sqrt(1+t squared) and e(1). For arbitrary local a,b,c, the spin commutator is minus C(C(a,b),c), by the general vector triple-product identity. Two applications of the all-input cross-channel bound, obtained from the existing action estimate at parameter zero, give commutator norm at most norm(a) norm(b) norm(c). Specialization to the original unit basis gives the curvature upper bound without enumerating its entries. The same identity and orthonormal normalization give kappa(1,2,2)=e(1), attaining one on the original finite domain. This calibration supplies no new report escape or numeric consumer.

**Theorem 1.6 (The full action Gram, both kernels, support and eigenvalues).**

$$\forall t \in \mathbb{R},\; (\forall a \in J,\; \operatorname{G}\left(t, a\right) = (0, \left(2 + (t)^{2}\right) \cdot a_{1}, \left(2 + (t)^{2}\right) \cdot a_{2}, 2 \cdot a_{3})) \land ((\forall a \in J,\; (\forall i \in \operatorname{Fin}\left(4\right),\; \operatorname{D}\left(t, \operatorname{e}\left(i\right), a\right) = 0) \Leftrightarrow (\exists r \in \mathbb{R},\; a = r \cdot \operatorname{e}\left(0\right))) \land ((\forall a \in J,\; (a \in \operatorname{W}\left(t\right)) \Leftrightarrow (a_{0} = 0)) \land ((\forall a \in J,\; (\operatorname{D}\left(t, a\right) = 0) \Leftrightarrow (\exists r \in \mathbb{R},\; a = r \cdot (\operatorname{e}\left(0\right) - t \cdot \operatorname{e}\left(3\right)))) \land (\forall lambda \in \mathbb{R},\; (\exists a \in J,\; (a \ne 0) \land (\operatorname{G}\left(t, a\right) = lambda \cdot a)) \Leftrightarrow ((lambda = 0) \lor ((lambda = 2 + (t)^{2}) \lor (lambda = 2)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/PauliFixedProductFamily.exact_action_data` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The coordinate identity holds on every vector. The label kernel and common fixed kernel are distinguished as actual operator statements. The exact coordinates retain eigenvalue multiplicities and their collision at zero parameter.

**Theorem 1.7 (The label Gram and attained positive action minimum).**

$$\forall t \in \mathbb{R},\; (\forall a \in J,\; \operatorname{H}\left(t, a\right) = (2 \cdot (t)^{2} \cdot a_{0} + 2 \cdot t \cdot a_{3}, 2 \cdot a_{1}, 2 \cdot a_{2}, 2 \cdot t \cdot a_{0} + 2 \cdot a_{3})) \land ((\forall lambda \in \mathbb{R},\; (\exists a \in J,\; (a \ne 0) \land (\operatorname{H}\left(t, a\right) = lambda \cdot a)) \Leftrightarrow ((lambda = 0) \lor ((lambda = 2) \lor (lambda = 2 \cdot (1 + (t)^{2}))))) \land (((2 \in \operatorname{Lambda}\left(t\right)) \land (\forall r \in \mathbb{R},\; (r \in \operatorname{Lambda}\left(t\right)) \Rightarrow (2 \le r))) \land (\operatorname{sigma}\left(t\right) = \sqrt{2})))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/PauliFixedProductFamily.exact_label_data` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

H is the label Gram, distinct from the action Gram G. The displayed eigenvalue equivalence includes all real eigenvalues, including collisions. The positive action eigenvalue minimum is attained at e(3), and its square-root gap is uniform.

**Theorem 1.8 (Complete support, uniform gap, activity and zero boundary).**

$$\forall t \in \mathbb{R},\; (\operatorname{W}\left(t\right) = (\operatorname{Z}\left(t\right))^{\perp}) \land ((\forall a \in J,\; (a \in \operatorname{W}\left(t\right)) \Rightarrow (2 \cdot (\Vert a\Vert)^{2} \le \langle a,\operatorname{G}\left(t, a\right)\rangle)) \land (((\operatorname{e}\left(3\right) \in \operatorname{W}\left(t\right)) \land ((\Vert \operatorname{e}\left(3\right)\Vert = 1) \land (\operatorname{G}\left(t, \operatorname{e}\left(3\right)\right) = 2 \cdot \operatorname{e}\left(3\right)))) \land ((\operatorname{D}\left(t\right) \ne 0) \land (((t \ne 0) \Rightarrow ((\exists a \in J,\; \operatorname{D}\left(t, a, a\right) \ne 0) \land ((\operatorname{D}\left(t, \operatorname{e}\left(0\right)\right) \ne 0) \land (\operatorname{ker}\left(\operatorname{D}\left(t\right)\right) \ne \operatorname{Z}\left(t\right))))) \land ((\forall a \in J,\; \operatorname{D}\left(0, a, a\right) = 0) \land (\operatorname{D}\left(0, \operatorname{e}\left(0\right)\right) = 0))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/PauliFixedProductFamily.exact_support_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every support and activity conjunct concerns the same actual maps. At parameter zero the diagonal and unit-generator defects vanish, while the spatial action remains nonzero and the positive support gap remains sqrt(2). These are algebraic conclusions for this realization; no physical acquisition or general reconstruction conclusion follows.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/PauliFixedProductFamily.exact_action_data`
- Truth anchor: `D5/S3/Quantum/Algebra/PauliFixedProductFamily.exact_constants`
- Truth anchor: `D5/S3/Quantum/Algebra/PauliFixedProductFamily.exact_defects`
- Truth anchor: `D5/S3/Quantum/Algebra/PauliFixedProductFamily.exact_label_data`
- Truth anchor: `D5/S3/Quantum/Algebra/PauliFixedProductFamily.exact_support_gap`
- Truth anchor: `D5/S3/Quantum/Algebra/PauliFixedProductFamily.family_contract`
- Truth anchor: `D5/S3/Quantum/Algebra/PauliFixedProductFamily.full_report`
- Truth anchor: `D5/S3/Quantum/Algebra/PauliFixedProductFamily.residual_scaling`
