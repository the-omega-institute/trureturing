# A strict certificate for the same fixed-product Pauli realization

## Abstract

The complete actual Pauli report gives strict improvement on the literal nonempty real interval.

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

All definitions above are the actual fixed-product family, reproduced here so that the existential realization statement is closed and complete. Cstar is PauliLinearCertificate.constant = 1+2sqrt(2). epsilon(t) is epsilon t, d(t) is localBound t, eta is smallEndpoint. L(t) means PauliLinearCertificate.linear (epsilon t) (localBound t); O(t) means PauliLinearCertificate.old at those same arguments. q(t) below is its original quadratic root; O retains the independent local cap. The computed report yields epsilon(t)=12sqrt(2)|t|, rather than a selected-block readout.

$$
(\operatorname{Cstar}\left(\right) = 1 + 2 \cdot \sqrt{2}) \land ((\operatorname{eta}\left(\right) = \frac{1}{192 \cdot \sqrt{2} \cdot (1 + 2 \cdot \sqrt{2})}) \land (\forall t \in \mathbb{R},\; (\operatorname{epsilon}\left(t\right) = \sqrt{\operatorname{R}\left(t\right)}) \land ((\operatorname{d}\left(t\right) = \sqrt{1 + (t)^{2}}) \land ((\operatorname{L}\left(t\right) = \frac{2 \cdot (1 + 2 \cdot \sqrt{2}) \cdot \sqrt{1 + (t)^{2}} \cdot \operatorname{epsilon}\left(t\right)}{\sqrt{2} - 2 \cdot (1 + 2 \cdot \sqrt{2}) \cdot \operatorname{epsilon}\left(t\right)}) \land ((\operatorname{q}\left(t\right) = \frac{(1 + 2 \cdot \sqrt{2}) \cdot \operatorname{epsilon}\left(t\right) + \sqrt{(1 + 2 \cdot \sqrt{2})^{2} \cdot (\operatorname{epsilon}\left(t\right))^{2} + 4 \cdot (1 + 2 \cdot \sqrt{2}) \cdot \sqrt{1 + (t)^{2}} \cdot \operatorname{epsilon}\left(t\right)}}{2}) \land (\operatorname{O}\left(t\right) = \operatorname{min}\left(\sqrt{1 + (t)^{2}}, \operatorname{q}\left(t\right)\right)))))))
$$

**Theorem 1.1 (The literal interval contains a nonzero real parameter).**

$$\exists t \in \mathbb{R},\; (0 < \lvert t\rvert) \land (\lvert t\rvert < \frac{1}{192 \cdot \sqrt{2} \cdot (1 + 2 \cdot \sqrt{2})})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/PauliFixedProductLinear.small_interval_nonempty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The endpoint is positive, and half of it is an explicit positive member. The ambient family still includes the zero parameter.

**Theorem 1.2 (The actual defect lies below both the original root and cap).**

$$\forall t \in \mathbb{R},\; ((0 < \lvert t\rvert) \land (\lvert t\rvert < \frac{1}{192 \cdot \sqrt{2} \cdot (1 + 2 \cdot \sqrt{2})})) \Rightarrow ((0 < \sqrt{2} - 2 \cdot (1 + 2 \cdot \sqrt{2}) \cdot \operatorname{epsilon}\left(t\right)) \land ((\exists a \in J,\; \operatorname{D}\left(t, a, a\right) \ne 0) \land ((\operatorname{D}\left(t, \operatorname{e}\left(0\right)\right) \ne 0) \land ((\forall a \in J,\; (\Vert a\Vert = 1) \Rightarrow (\Vert \operatorname{D}\left(t, a, a\right)\Vert \le \operatorname{L}\left(t\right))) \land ((\frac{\lvert t\rvert}{2} \le \operatorname{L}\left(t\right)) \land (\operatorname{L}\left(t\right) < \operatorname{O}\left(t\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/PauliFixedProductLinear.actual_strict_improvement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The six conjuncts include denominator positivity, both activity statements and domination for every unit vector. Since O(t) is the displayed minimum, strict inequality means strict improvement below both d(t) and q(t). The complete report gives epsilon in (0,1/(16 Cstar)); the literal interval also gives |t|<1 and hence 1<=d(t)<=sqrt(2). With x=Cstar epsilon, the linear certificate is at most 4x, strictly below sqrt(x), at most the quadratic root, and strictly below one and thus the cap. The exact attained diagonal defect gives domination. This proves the family-specific comparison; the general stability theorem for arbitrary products and actions is not asserted.

**Theorem 1.3 (One actual parameter realizes all data and strict improvement together).**

$$\exists t \in \mathbb{R},\; ((\operatorname{dim}\left(\mathbb{R}, J\right) = 4) \land ((\operatorname{dim}\left(\mathbb{R}, V\right) = 16) \land ((\forall i \in \operatorname{Fin}\left(4\right),\; \operatorname{b}\left(i\right) = \operatorname{e}\left(i\right)) \land ((\forall i \in \operatorname{Fin}\left(4\right),\; \forall j \in \operatorname{Fin}\left(4\right),\; \operatorname{B}\left(i, j\right) = \operatorname{T}\left(\operatorname{e}\left(i\right), \operatorname{e}\left(j\right)\right)) \land ((\forall a \in J,\; \forall b \in J,\; \operatorname{S}\left(a, b\right) = \operatorname{S}\left(b, a\right)) \land ((\forall a \in J,\; \operatorname{S}\left(\operatorname{e}\left(0\right), a\right) = a) \land ((\forall a \in J,\; \forall b \in J,\; \forall c \in J,\; \langle \operatorname{S}\left(a, b\right),c\rangle = \langle a,\operatorname{S}\left(b, c\right)\rangle) \land ((\forall a \in J,\; \forall b \in J,\; \forall c \in J,\; \operatorname{D}\left(t, a, \operatorname{S}\left(b, c\right)\right) = \operatorname{S}\left(\operatorname{D}\left(t, a, b\right), c\right) + \operatorname{S}\left(b, \operatorname{D}\left(t, a, c\right)\right)) \land ((\operatorname{D}\left(t, \operatorname{e}\left(1\right), \operatorname{e}\left(2\right)\right) = \operatorname{e}\left(3\right)) \land ((\forall X \in V,\; \forall Y \in V,\; \operatorname{M}\left(X, Y\right) = \operatorname{M}\left(Y, X\right)) \land ((\forall X \in V,\; \operatorname{M}\left(\operatorname{T}\left(\operatorname{e}\left(0\right), \operatorname{e}\left(0\right)\right), X\right) = X) \land ((\forall X \in V,\; \forall Y \in V,\; \forall Z \in V,\; \langle \operatorname{M}\left(X, Y\right),Z\rangle = \langle X,\operatorname{M}\left(Y, Z\right)\rangle) \land ((\forall X \in V,\; (0 \le \langle X,X\rangle) \land ((\langle X,X\rangle = 0) \Leftrightarrow (X = 0))) \land ((\forall a \in J,\; \forall b \in J,\; \forall c \in J,\; \forall d \in J,\; (\operatorname{M}\left(\operatorname{T}\left(a, \operatorname{e}\left(0\right)\right), \operatorname{T}\left(c, d\right)\right) = \operatorname{T}\left(\operatorname{S}\left(a, c\right), d\right)) \land ((\operatorname{M}\left(\operatorname{T}\left(\operatorname{e}\left(0\right), b\right), \operatorname{T}\left(c, d\right)\right) = \operatorname{T}\left(c, \operatorname{S}\left(b, d\right)\right)) \land ((\operatorname{Gamma}\left(t, \operatorname{T}\left(a, b\right), \operatorname{T}\left(c, \operatorname{e}\left(0\right)\right)\right) = \operatorname{T}\left(\operatorname{D}\left(t, a, c\right), b\right)) \land (\operatorname{Gamma}\left(t, \operatorname{T}\left(a, b\right), \operatorname{T}\left(\operatorname{e}\left(0\right), d\right)\right) = \operatorname{T}\left(a, \operatorname{D}\left(t, b, d\right)\right))))) \land (\operatorname{R}\left(t\right) = 288 \cdot (t)^{2}))))))))))))))) \land ((((\frac{\lvert t\rvert}{2} \in \{ s: \mathbb{R} \mid \exists a \in J,\; (\Vert a\Vert = 1) \land (s = \Vert \operatorname{D}\left(t, a, a\right)\Vert) \}) \land (\forall r \in \mathbb{R},\; (r \in \{ s: \mathbb{R} \mid \exists a \in J,\; (\Vert a\Vert = 1) \land (s = \Vert \operatorname{D}\left(t, a, a\right)\Vert) \}) \Rightarrow (r \le \frac{\lvert t\rvert}{2}))) \land (((\lvert t\rvert \in \{ s: \mathbb{R} \mid \exists b \in J,\; (\Vert b\Vert = 1) \land (s = \Vert \operatorname{D}\left(t, \operatorname{e}\left(0\right), b\right)\Vert) \}) \land (\forall r \in \mathbb{R},\; (r \in \{ s: \mathbb{R} \mid \exists b \in J,\; (\Vert b\Vert = 1) \land (s = \Vert \operatorname{D}\left(t, \operatorname{e}\left(0\right), b\right)\Vert) \}) \Rightarrow (r \le \lvert t\rvert))) \land ((\forall a \in J,\; \forall b \in J,\; \Vert \operatorname{S}\left(a, b\right)\Vert \le \sqrt{2} \cdot \Vert a\Vert \cdot \Vert b\Vert) \land ((\forall a \in J,\; \forall b \in J,\; \Vert \operatorname{D}\left(t, a, b\right)\Vert \le \sqrt{1 + (t)^{2}} \cdot \Vert a\Vert \cdot \Vert b\Vert) \land (\Vert \operatorname{U}\left(t\right)\Vert_{op} = \lvert t\rvert))))) \land (((\Vert \operatorname{e}\left(0\right)\Vert = 1) \land (((\sqrt{2} \in \{ s: \mathbb{R} \mid \exists a \in J,\; \exists b \in J,\; (\Vert a\Vert = 1) \land ((\Vert b\Vert = 1) \land (s = \Vert \operatorname{S}\left(a, b\right)\Vert)) \}) \land (\forall r \in \mathbb{R},\; (r \in \{ s: \mathbb{R} \mid \exists a \in J,\; \exists b \in J,\; (\Vert a\Vert = 1) \land ((\Vert b\Vert = 1) \land (s = \Vert \operatorname{S}\left(a, b\right)\Vert)) \}) \Rightarrow (r \le \sqrt{2}))) \land (((\sqrt{1 + (t)^{2}} \in \{ s: \mathbb{R} \mid \exists a \in J,\; \exists b \in J,\; (\Vert a\Vert = 1) \land ((\Vert b\Vert = 1) \land (s = \Vert \operatorname{D}\left(t, a, b\right)\Vert)) \}) \land (\forall r \in \mathbb{R},\; (r \in \{ s: \mathbb{R} \mid \exists a \in J,\; \exists b \in J,\; (\Vert a\Vert = 1) \land ((\Vert b\Vert = 1) \land (s = \Vert \operatorname{D}\left(t, a, b\right)\Vert)) \}) \Rightarrow (r \le \sqrt{1 + (t)^{2}}))) \land ((1 \in \{ s: \mathbb{R} \mid \exists i \in \operatorname{Fin}\left(4\right),\; \exists j \in \operatorname{Fin}\left(4\right),\; \exists k \in \operatorname{Fin}\left(4\right),\; s = \Vert \operatorname{kappa}\left(i, j, k\right)\Vert \}) \land (\forall r \in \mathbb{R},\; (r \in \{ s: \mathbb{R} \mid \exists i \in \operatorname{Fin}\left(4\right),\; \exists j \in \operatorname{Fin}\left(4\right),\; \exists k \in \operatorname{Fin}\left(4\right),\; s = \Vert \operatorname{kappa}\left(i, j, k\right)\Vert \}) \Rightarrow (r \le 1)))))) \land (((\forall a \in J,\; \operatorname{G}\left(t, a\right) = (0, \left(2 + (t)^{2}\right) \cdot a_{1}, \left(2 + (t)^{2}\right) \cdot a_{2}, 2 \cdot a_{3})) \land ((\forall a \in J,\; (\forall i \in \operatorname{Fin}\left(4\right),\; \operatorname{D}\left(t, \operatorname{e}\left(i\right), a\right) = 0) \Leftrightarrow (\exists r \in \mathbb{R},\; a = r \cdot \operatorname{e}\left(0\right))) \land ((\forall a \in J,\; (a \in \operatorname{W}\left(t\right)) \Leftrightarrow (a_{0} = 0)) \land ((\forall a \in J,\; (\operatorname{D}\left(t, a\right) = 0) \Leftrightarrow (\exists r \in \mathbb{R},\; a = r \cdot (\operatorname{e}\left(0\right) - t \cdot \operatorname{e}\left(3\right)))) \land (\forall lambda \in \mathbb{R},\; (\exists a \in J,\; (a \ne 0) \land (\operatorname{G}\left(t, a\right) = lambda \cdot a)) \Leftrightarrow ((lambda = 0) \lor ((lambda = 2 + (t)^{2}) \lor (lambda = 2)))))))) \land (((\forall a \in J,\; \operatorname{H}\left(t, a\right) = (2 \cdot (t)^{2} \cdot a_{0} + 2 \cdot t \cdot a_{3}, 2 \cdot a_{1}, 2 \cdot a_{2}, 2 \cdot t \cdot a_{0} + 2 \cdot a_{3})) \land ((\forall lambda \in \mathbb{R},\; (\exists a \in J,\; (a \ne 0) \land (\operatorname{H}\left(t, a\right) = lambda \cdot a)) \Leftrightarrow ((lambda = 0) \lor ((lambda = 2) \lor (lambda = 2 \cdot (1 + (t)^{2}))))) \land (((2 \in \operatorname{Lambda}\left(t\right)) \land (\forall r \in \mathbb{R},\; (r \in \operatorname{Lambda}\left(t\right)) \Rightarrow (2 \le r))) \land (\operatorname{sigma}\left(t\right) = \sqrt{2})))) \land (((\operatorname{W}\left(t\right) = (\operatorname{Z}\left(t\right))^{\perp}) \land ((\forall a \in J,\; (a \in \operatorname{W}\left(t\right)) \Rightarrow (2 \cdot (\Vert a\Vert)^{2} \le \langle a,\operatorname{G}\left(t, a\right)\rangle)) \land (((\operatorname{e}\left(3\right) \in \operatorname{W}\left(t\right)) \land ((\Vert \operatorname{e}\left(3\right)\Vert = 1) \land (\operatorname{G}\left(t, \operatorname{e}\left(3\right)\right) = 2 \cdot \operatorname{e}\left(3\right)))) \land ((\operatorname{D}\left(t\right) \ne 0) \land (((t \ne 0) \Rightarrow ((\exists a \in J,\; \operatorname{D}\left(t, a, a\right) \ne 0) \land ((\operatorname{D}\left(t, \operatorname{e}\left(0\right)\right) \ne 0) \land (\operatorname{ker}\left(\operatorname{D}\left(t\right)\right) \ne \operatorname{Z}\left(t\right))))) \land ((\forall a \in J,\; \operatorname{D}\left(0, a, a\right) = 0) \land (\operatorname{D}\left(0, \operatorname{e}\left(0\right)\right) = 0))))))) \land ((0 < \lvert t\rvert) \land ((\lvert t\rvert < \frac{1}{192 \cdot \sqrt{2} \cdot (1 + 2 \cdot \sqrt{2})}) \land ((\exists a \in J,\; \operatorname{D}\left(t, a, a\right) \ne 0) \land ((\operatorname{D}\left(t, \operatorname{e}\left(0\right)\right) \ne 0) \land ((\frac{\lvert t\rvert}{2} \le \operatorname{L}\left(t\right)) \land (\operatorname{L}\left(t\right) < \operatorname{O}\left(t\right))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/PauliFixedProductLinear.nonempty_improvement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The full six Family proposition bodies are displayed in this same-t existential conjunction, followed by the six interval, activity and comparison clauses. This particular declaration does not output denominator positivity or all-unit domination as additional conjuncts; those are outputs of actual_strict_improvement. The source realization, exact constants, both Gram operators, both kernels, spectra, support, uniform gap and zero-boundary data all belong to the same fixed-product family. No physical acquisition or general noisy-reconstruction conclusion is supplied.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/PauliFixedProductLinear.actual_strict_improvement`
- Truth anchor: `D5/S3/Quantum/Algebra/PauliFixedProductLinear.nonempty_improvement`
- Truth anchor: `D5/S3/Quantum/Algebra/PauliFixedProductLinear.small_interval_nonempty`
- Dependency: [D5/S3/Quantum/Algebra/PauliFixedProductFamily](PauliFixedProductFamily.md)
